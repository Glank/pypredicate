import re
from copy import deepcopy
class KnowlegeBase:
    def __init__(self):
        pass

    def tell(self, sentence):
        pass

    def ask(self, question):
        pass

class Predicate:
    """A falsifiable claim."""
    def __init__(self, name, arity):
        """Predicate:
            Name is a string representing the predicate.
            Arity is the number of arguments for this predicate."""
        self.name = name
        self.arity = arity
    def __str__(self):
        return "%s/%d"%(self.name, self.arity)
    def __repr__(self):
        return str(self)

class Term:
    def __init__(self):
        pass
    def __repr__(self):
        return str(self)
    def clone(self):
        raise NotImplementedError()

class Function:
    def __init__(self, name, arity):
        """Function:
            Name is a string representing the function.
            Arity is the number of arguments for this function."""
        self.name = name
        self.arity = arity
    def __str__(self):
        return "%s/%d"%(self.name, self.arity)
    def __repr__(self):
        return str(self)

class Variable(Term):
    def __init__(self, name):
        self.name = name
    def __hash__(self):
        return hash(self.name)
    def __eq__(self, other):
        return self.name == other.name
    def __str__(self):
        return self.name
    def clone(self):
        return Variable(self.name)

class FunctionalTerm(Term):
    def __init__(self, function, terms):
        self.function = function
        self.terms = terms
        assert(len(terms)==function.arity)
    def __str__(self):
        if self.function.arity==0:
            return self.function.name
        return self.function.name+"("+", ".join(str(t) for t in self.terms)+")"
    def clone(self):
        return FunctionalTerm(self.function, [t.clone() for t in self.terms])

class WFF:
    """Well Formed Formula"""
    def __init__(self):
        pass
    def __repr__(self):
        return str(self)
    def clone(self):
        raise NotImplementedError()

class AtomicWFF(WFF):
    def __init__(self, predicate, terms):
        self.predicate = predicate
        self.terms = terms
        assert(len(terms)==predicate.arity)
    def __str__(self):
        if self.predicate.arity==0:
            return self.predicate.name
        return self.predicate.name+"("+", ".join(str(t) for t in self.terms)+")"
    def clone(self):
        return AtomicWFF(self.predicate, [t.clone() for t in self.terms])

class NotWFF(WFF):
    def __init__(self, child):
        self.child = child
    def to_cnf(self):
        return self.to_nnf()
    def __str__(self):
        return "~"+str(self.child)
    def clone(self):
        return NotWFF(self.child.clone())

class AndWFF(WFF):
    def __init__(self, children):
        self.children = children
    def __str__(self):
        return "("+" & ".join(str(c) for c in self.children)+")"
    def clone(self):
        return AndWFF([c.clone() for c in self.children])

class OrWFF(WFF):
    def __init__(self, children):
        self.children = children
    def __str__(self):
        return "("+" | ".join(str(c) for c in self.children)+")"
    def clone(self):
        return OrWFF([c.clone() for c in self.children])

class ForAllWFF(WFF):
    def __init__(self, bound, child):
        self.bound = bound
        self.child = child
    def __str__(self):
        left = "A "+",".join(str(v) for v in self.bound)
        right = "("+str(self.child)+")"
        return left + ":" + right
    def clone(self):
        return ForAllWFF([b.clone() for b in self.bound], self.child.clone())

class ThereExistsWFF(WFF):
    def __init__(self, bound, child):
        self.bound = bound
        self.child = child
    def __str__(self):
        left = "E "+",".join(str(v) for v in self.bound)
        right = "("+str(self.child)+")"
        return left + ":" + right
    def clone(self):
        return ThereExistsWFF([b.clone() for b in self.bound], self.child.clone())

def to_nnf(node):
    """To negation normal form"""
    if isinstance(node, AtomicWFF):
        return node
    elif isinstance(node, AndWFF):
        return AndWFF([to_nnf(c) for c in node.children])
    elif isinstance(node, OrWFF):
        return OrWFF([to_nnf(c) for c in node.children])
    elif isinstance(node, ForAllWFF):
        return ForAllWFF(node.bound, to_nnf(node.child))
    elif isinstance(node, ThereExistsWFF):
        return ThereExistsWFF(node.bound, to_nnf(node.child))
    elif isinstance(node, NotWFF):
        child = node.child
        if isinstance(child, NotWFF):
            return to_nnf(child.child)
        elif isinstance(child, AtomicWFF):
            return node
        elif isinstance(child, AndWFF):
            return OrWFF([to_nnf(NotWFF(c)) for c in child.children])
        elif isinstance(child, OrWFF):
            return AndWFF([to_nnf(NotWFF(c)) for c in child.children])
        elif isinstance(child, ForAllWFF):
            return ThereExistsWFF(child.bound, to_nnf(NotWFF(child.child)))
        elif isinstance(child, ThereExistsWFF):
            return ForAllWFF(child.bound, to_nnf(NotWFF(child.child)))
        else:
            raise Exception("NNF: Invalid type: %r"%type(child))
    else:
        raise Exception("NNF: Invalid type: %r"%type(node))

def to_svf(node):
    """To standardized variable form. Expects a nnf node."""
    node = node.clone()    
    def substitute_var(node, old_var, new_var_name):
        """Substitute all of old_var with the new_var binding recursively"""
        if isinstance(node, (ForAllWFF,ThereExistsWFF)):
            if old_var in node.bound:
                raise Exception("Recursive Binding on variable: %s"%str(node))
        if isinstance(node, (NotWFF,ForAllWFF,ThereExistsWFF)):
            substitute_var(node.child, old_var, new_var_name)
        elif isinstance(node, (AtomicWFF,FunctionalTerm)):
            for t in node.terms:
                substitute_var(t, old_var, new_var_name)
        elif isinstance(node, (AndWFF, OrWFF)):
            for c in node.children:
                substitute_var(c, old_var, new_var_name)
        elif isinstance(node, Variable) and node==old_var:
            node.name = new_var_name
    def bound_iter(node, bound=None):
        """Yields all the bound variables and their quantifiers."""
        if isinstance(node, (ForAllWFF, ThereExistsWFF)):
            for v in node.bound:
                yield v, node
        if isinstance(node, (NotWFF, ForAllWFF, ThereExistsWFF)):
            for v,q in bound_iter(node.child):
                yield v,q
            return
        elif isinstance(node, (AndWFF, OrWFF)):
            for c in node.children:
                for v,q in bound_iter(c):
                    yield v,q
    def increment(name):
        m = re.search(r"(.*?)(\d+)$", name)
        if not m:
            return name+"0"
        left, right = m.groups()
        return left+str(int(right)+1)
    already_bound = set()
    for v,q in bound_iter(node):
        name = v.name
        while name in already_bound:
            name = increment(name)
        substitute_var(q.child, v, name)
        v.name = name
        already_bound.add(name)
    return node

x,y,z = Variable('x'), Variable('y'), Variable('z')
p,q = Predicate('p',1), Predicate('q',1)
p_of_x = AtomicWFF(p, [x])
p_of_y = AtomicWFF(p, [y])
q_of_z = AtomicWFF(q, [z])
andwff = AndWFF([p_of_y, q_of_z])
orwff = OrWFF([p_of_x, andwff])
notwff = NotWFF(orwff)

print str(notwff)
print str(to_nnf(notwff))

q_of_x = AtomicWFF(q, [x])
not_pofy = NotWFF(p_of_y)
pofy_implies_qofx = OrWFF([not_pofy, q_of_x])
exists = ThereExistsWFF([x,y],pofy_implies_qofx)
for_all = ForAllWFF([x], p_of_x)
wff = OrWFF([NotWFF(for_all), exists])

print wff
wff = to_nnf(wff)
print wff
wff = to_svf(wff)
print wff
