from pydrofoil import parse
from collections import defaultdict

# optimize operation ASTs before generating code

def identify_replacements(blocks):
    decls, defs, uses = find_decl_defs_uses(blocks)
    replacements = {}
    for var, varuses in uses.iteritems():
        if len(varuses) != 1:
            continue
        vardefs = defs[var]
        if len(vardefs) != 1:
            continue
        [(useblock, useindex)] = varuses
        [(defblock, defindex)] = vardefs
        if var not in decls:
            continue
        declblock, declindex = decls[var]
        if not (declblock is defblock is useblock):
            continue
        defop = useblock[defindex]
        useop = useblock[useindex]
        if isinstance(defop, parse.Operation) and defop.name.startswith(('@', '$')):
            continue
        if any(len(defs[argvar]) != 1 for argvar in defop.find_used_vars()):
            continue
        replacements[var] = (useblock, declindex, defindex, useindex)
    return replacements

def do_replacements(replacements):
    repl_list = list(replacements.items())
    repl_list.sort(key=lambda element: (element[1][0], element[1][2]))
    for var, (block, declindex, defindex, useindex) in repl_list:
        declop = block[declindex]
        defop = block[defindex]
        useop = block[useindex]
        if isinstance(defop, parse.Operation):
            expr = parse.OperationExpr(defop.name, defop.args, declop.typ)
        else:
            assert isinstance(defop, parse.Assignment)
            expr = parse.CastExpr(defop.value, declop.typ)
        block[useindex] = newop = useop.replace_var(var, expr)
        assert newop != useop
        if type(block[-1]) is not set:
            block.append({defindex, declindex})
        else:
            block[-1].add(declindex)
            block[-1].add(defindex)
    for _, (block, _, _, _) in repl_list:
        if type(block[-1]) is not set:
            continue
        newblock = []
        delete_index = block.pop()
        for i, op in enumerate(block):
            if i in delete_index:
                continue
            newblock.append(op)
        block[:] = newblock


def optimize_blocks(blocks, codegen):
    do_replacements(identify_replacements(blocks.values()))

def find_decl_defs_uses(blocks):
    defs = defaultdict(list)
    uses = defaultdict(list)
    decls = {}
    for block in blocks:
        for i, op in enumerate(block):
            used_vars = op.find_used_vars()
            for var in used_vars:
                uses[var].append((block, i))
            if isinstance(op, (parse.Assignment, parse.Operation)):
                defs[op.result].append((block, i))
            elif isinstance(op, parse.LocalVarDeclaration):
                assert op.name not in decls
                decls[op.name] = (block, i)
    return decls, defs, uses

            
