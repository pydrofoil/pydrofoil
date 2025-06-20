# the following algorithms are partly adapted (and simplified) from networkx,
# covered by BSD 3-clause license
# https://github.com/networkx/networkx


def dfs_postorder_nodes(G, source=None):
    """Generate nodes in a depth-first-search post-ordering starting at source.

    Parameters
    ----------
    G : NetworkX graph

    source : node, optional
       Specify starting node for depth-first search.

    Returns
    -------
    nodes: generator
       A generator of nodes in a depth-first-search post-ordering.

    Examples
    --------
    >>> G = nx.path_graph(5)
    >>> list(nx.dfs_postorder_nodes(G, source=0))
    [4, 3, 2, 1, 0]

    Notes
    -----
    If a source is not specified then a source is chosen arbitrarily and
    repeatedly until all components in the graph are searched.

    The implementation of this function is adapted from David Eppstein's
    depth-first search function in `PADS`_, with modifications
    to allow depth limits based on the Wikipedia article
    "`Depth-limited search`_".

    .. _PADS: http://www.ics.uci.edu/~eppstein/PADS
    .. _Depth-limited search: https://en.wikipedia.org/wiki/Depth-limited_search

    See Also
    --------
    dfs_edges
    dfs_preorder_nodes
    dfs_labeled_edges
    edge_dfs
    bfs_tree
    """
    edges = dfs_labeled_edges(G, source=source)
    return (v for u, v, d in edges if d == "reverse")


def dfs_labeled_edges(G, source=None):
    """Iterate over edges in a depth-first-search (DFS) labeled by type.

    Parameters
    ----------
    G : NetworkX graph

    source : node, optional
       Specify starting node for depth-first search and return edges in
       the component reachable from source.

    Returns
    -------
    edges: generator
       A generator of triples of the form (*u*, *v*, *d*), where (*u*,
       *v*) is the edge being explored in the depth-first search and *d*
       is one of the strings 'forward', 'nontree', or 'reverse'.
       A 'forward' edge is one in which *u* has been visited but *v* has
       not. A 'nontree' edge is one in which both *u* and *v* have been
       visited but the edge is not in the DFS tree. A 'reverse' edge is
       one in which both *u* and *v* have been visited and the edge is in
       the DFS tree.

    Examples
    --------

    The labels reveal the complete transcript of the depth-first search
    algorithm in more detail than, for example, :func:`dfs_edges`::

        >>> from pprint import pprint
        >>>
        >>> G = nx.DiGraph([(0, 1), (1, 2), (2, 1)])
        >>> pprint(list(nx.dfs_labeled_edges(G, source=0)))
        [(0, 0, 'forward'),
         (0, 1, 'forward'),
         (1, 2, 'forward'),
         (2, 1, 'nontree'),
         (1, 2, 'reverse'),
         (0, 1, 'reverse'),
         (0, 0, 'reverse')]

    Notes
    -----
    If a source is not specified then a source is chosen arbitrarily and
    repeatedly until all components in the graph are searched.

    The implementation of this function is adapted from David Eppstein's
    depth-first search function in `PADS`_, with modifications
    to allow depth limits based on the Wikipedia article
    "`Depth-limited search`_".

    .. _PADS: http://www.ics.uci.edu/~eppstein/PADS
    .. _Depth-limited search: https://en.wikipedia.org/wiki/Depth-limited_search

    See Also
    --------
    dfs_edges
    dfs_preorder_nodes
    dfs_postorder_nodes
    """
    # Based on http://www.ics.uci.edu/~eppstein/PADS/DFS.py
    # by D. Eppstein, July 2004.
    if source is None:
        # edges for all components
        nodes = G
    else:
        # edges for components with source
        nodes = [source]

    visited = set()
    for start in nodes:
        if start in visited:
            continue
        yield start, start, "forward"
        visited.add(start)
        stack = [(start, iter(G[start]))]
        depth_now = 1
        while stack:
            parent, children = stack[-1]
            for child in children:
                if child in visited:
                    yield parent, child, "nontree"
                else:
                    yield parent, child, "forward"
                    visited.add(child)
                    stack.append((child, iter(G[child])))
                    depth_now += 1
                    break
            else:
                stack.pop()
                depth_now -= 1
                if stack:
                    yield stack[-1][0], parent, "reverse"
        yield start, start, "reverse"


def immediate_dominators(G, start, pred):
    """Returns the immediate dominators of all nodes of a directed graph.

    Parameters
    ----------
    G : a DiGraph or MultiDiGraph
        The graph where dominance is to be computed.

    start : node
        The start node of dominance computation.
    pred : dict keyed by nodes
        The predecessor relationship of the graph


    Returns
    -------
    idom : dict keyed by nodes
        A dict containing the immediate dominators of each node reachable from
        `start`.

    Notes
    -----
    Except for `start`, the immediate dominators are the parents of their
    corresponding nodes in the dominator tree.

    Examples
    --------
    >>> G = nx.DiGraph([(1, 2), (1, 3), (2, 5), (3, 4), (4, 5)])
    >>> sorted(nx.immediate_dominators(G, 1).items())
    [(1, 1), (2, 1), (3, 1), (4, 3), (5, 1)]

    References
    ----------
    .. [1] K. D. Cooper, T. J. Harvey, and K. Kennedy.
           A simple, fast dominance algorithm.
           Software Practice & Experience, 4:110, 2001.
    """
    assert start in G

    idom = {start: start}

    order = list(dfs_postorder_nodes(G, start))
    dfn = {u: i for i, u in enumerate(order)}
    order.pop()
    order.reverse()

    def intersect(u, v):
        while u != v:
            while dfn[u] < dfn[v]:
                u = idom[u]
            while dfn[u] > dfn[v]:
                v = idom[v]
        return u

    changed = True
    while changed:
        changed = False
        for u in order:
            new_idom = reduce(intersect, (v for v in pred[u] if v in idom))
            if u not in idom or idom[u] != new_idom:
                idom[u] = new_idom
                changed = True

    return idom

def compute_single_return_and_degree_two_phi_graph(G):
    """ Removes all but one return statement
        and splits up phi nodes so that any phi node has a in degree of two """
    G = compute_single_return_graph(G)
    return compute_max_phi_indeg_two_graph(G)


def compute_single_return_graph(G):
    """ Removes all but one return statement 
        by introducing a new phi node """
    
    from pydrofoil import ir
    first_return = None
    phi_block, phi_op = None, None

    for block in G.iterblocks():
        if block == phi_block: 
            continue
        if isinstance(block.next, ir.Return):
            if not first_return:
                # save the first block that has a Return as next for later
                first_return = block
                continue
            elif not phi_op:
                # we encountered the second block with a Return
                # create new block as 'merge point' for all blocks that return
                phi_block = ir.Block()
                # emit phi and put first_return block as first predecessor for phi block
                first_return_val = first_return.next.value
                phi_op = phi_block.emit_phi([first_return], [first_return_val], first_return_val.resolved_type)
                phi_block.next = ir.Return(phi_op)
                # set phi block as next for first_return block
                first_return.next = ir.Goto(phi_block, None)
            # append current block to phi predecessors
            phi_op.prevblocks.append(block)
            phi_op.prevvalues.append(block.next.value)
            # now set phi as next for the current block
            block.next = ir.Goto(phi_block, None)

    return G


def compute_max_phi_indeg_two_graph(G):
    """ Splits up phi nodes so that every phi has a maximum input degree of two """
    pass
    #current_block = G.startblock
    #import pdb; pdb.set_trace()
    #print(dir(current_block))
