import re

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
    def variables_iter(self):
        raise NotImplementedError()
    def __repr__(self):
        return str(self)

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
    def variables_iter(self):
        yield self
    def __hash__(self):
        return hash(self.name)
    def __eq__(self, other):
        return self.name == other.name
    def __str__(self):
        return self.name

def FunctionalTerm(Term):
    def __init__(self, function, terms):
        self.function = function
        self.terms = terms
        assert(len(terms)==function.arity)
    def variables_iter(self):
        for term in self.terms:
            for var in term.variables_iter():
                yield var
    def __str__(self):
        if self.function.arity==0:
            return self.function.name
        return self.function.name+"("+", ".join(str(t) for t in self.terms)+")"

class WFF:
    """Well Formed Formula"""
    def __init__(self):
        pass
    def to_cnf(self):
        """To conjunctive normal form"""
        raise NotImplementedError()
    def variables_iter(self):
        raise NotImplementedError()
    def sort_variables(self, bound_set, unbound_set):
        """Fills bound_set and unbound_set with the appropriate variables."""
        for var in self.variables_iter():
            if var in bound_set or var in unbound_set:
                continue
            if self.binds(var):
                bound_set.add(var)
            else:
                unbound_set.add(var)
    def binds(self, variable):
        return False
    def __repr__(self):
        return str(self)

class AtomicWFF(WFF):
    def __init__(self, predicate, terms):
        self.predicate = predicate
        self.terms = terms
        assert(len(terms)==predicate.arity)
    def to_cnf(self):
        return self
    def variables_iter(self):
        for term in self.terms:
            for var in term.variables_iter():
                yield var
    def __str__(self):
        if self.predicate.arity==0:
            return self.predicate.name
        return self.predicate.name+"("+", ".join(str(t) for t in self.terms)+")"

class NotWFF(WFF):
    def __init__(self, child):
        self.child = child
    def to_cnf(self):
        if isinstance(self.child, AtomicWFF):
            return self
        elif isinstance(self.child, NotWFF):
            return self.child.to_cnf()
        else:
            new_children = []
            for child in self.child.children:
                new_children.append(NotWFF(child))
            if isinstance(self.child, OrWFF):
                return AndWFF(new_children).to_cnf()
            elif isinstance(self.child, AndWFF):
                return OrWFF(new_children).to_cnf()
            elif isinstance(self.child, ForAllWFF):
                return ThereExistsWFF(new_children).to_cnf()
            elif isinstance(self.child, ThereExistsWFF):
                return ForAllWFF(new_children).to_cnf()
            else:
                raise Exception("Unknown WFF type.")
    def variables_iter(self):
        for var in self.child.variables_iter():
            yield var
    def __str__(self):
        return "~"+str(sefl.child)

def flatten(wff, clazz):
    #flatten
    diff_type = wff.children[:]
    same_type = []
    i = 0
    while i < len(diff_type):
        if isinstance(diff_type[i], clazz):
            same_type.append(diff_type.pop(i))
        else:
            i+=1
    #if needs flattening
    if same_type:
        new_children = diff_type
        for same in same_type:
            new_children+=same.children
        return clazz(new_children)
    #else
    return wff

class AndWFF(WFF):
    def __init__(self, children):
        self.children = children
    def to_cnf(self):
        children = [c.to_cnf() for c in self.children]
        return flatten(AndWFF(children), AndWFF)
    def variables_iter(self):
        for child in self.children:
            for var in child.variables_iter():
                yield var
    def __str__(self):
        return "("+" & ".join(str(c) for c in self.children)+")"

class OrWFF(WFF):
    def __init__(self, children):
        self.children = children
    def variables_iter(self):
        for child in self.children:
            for var in child.variables_iter():
                yield var
    def to_cnf(self):
        children = [c.to_cnf() for c in self.children]
        children = flatten(OrWFF(children), OrWFF).children
        for child in children:
            if isinstance(child, AndWFF)
    def __str__(self):
        return "("+" & ".join(str(c) for c in self.children)+")"

class ForAllWFF(WFF):
    def __init__(self, bound, child):
        self.bound = bound
        self.child = child
    def binds(self, variable):
        return variable in self.bound
    def variables_iter(self):
        for var in self.child.variables_iter():
            yield var
    def __str__(self):
        left = "A "+",".join(str(v) for v in self.bound)
        right = "("+str(self.child)+")"
        return left + ":" + right

class ThereExistsWFF(WFF):
    def __init__(self, bound, child):
        self.bound = bound
        self.child = child
    def binds(self, variable):
        return variable in self.bound
    def variables_iter(self):
        for var in self.child.variables_iter():
            yield var
    def __str__(self):
        left = "E "+",".join(str(v) for v in self.bound)
        right = "("+str(self.child)+")"
        return left + ":" + right

x,y,z = Variable('x'), Variable('y'), Variable('z')
p,q = Predicate('p',1), Predicate('q',1)
p_of_x = AtomicWFF(p, [x])
p_of_y = AtomicWFF(p, [y])
q_of_z = AtomicWFF(q, [z])
andwff = AndWFF([p_of_x, AndWFF([p_of_y, q_of_z])]) 

print str(andwff)
#(p(x) & (p(y) & q(z)))

allwff = ForAllWFF([x,y], andwff)
print str(allwff)

bound_set = set()
unbound_set = set()
allwff.sort_variables(bound_set, unbound_set)
print bound_set
print unbound_set
