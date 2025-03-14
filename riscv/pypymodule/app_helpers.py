def repr_struct(struct):
    fields = []
    for name, field in struct.sail_type.fields:
        fields.append(repr(getattr(struct, name)))
    fields = ", ".join(fields)
    return f"{struct.__class__.__name__}({fields})"

def repr_union(union):
    fields = [repr(x) for x in union]
    fields = ", ".join(fields)
    return f"{union.__class__.__name__}({fields})"
