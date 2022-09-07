CONCRETE_DOMAIN_KIND = 1
SYMBOLIC_DOMAIN_KIND = 2
SYMCRETE_DOMAIN_KIND = 3


def dom_is_concrete(v):
    return v.KIND == CONCRETE_DOMAIN_KIND

def dom_is_symbolic(v):
    return v.KIND == SYMBOLIC_DOMAIN_KIND

def dom_is_symcrete(v):
    return v.KIND == SYMCRETE_DOMAIN_KIND
