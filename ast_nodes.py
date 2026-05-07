"""
AST node definitions for first-order logic formulas.
"""

from __future__ import annotations
from dataclasses import dataclass
from typing import Union


# --- Terms ---

@dataclass(frozen=True)
class Var:
    name: str

    def __str__(self):
        return self.name

    def free_vars(self):
        return {self.name}

    def subst(self, mapping):
        return mapping.get(self.name, self)


@dataclass(frozen=True)
class FuncApp:
    """Function application, e.g. f(x). Constants are 0-arg: FuncApp('a', ())"""
    name: str
    args: tuple

    def __str__(self):
        if not self.args:
            return self.name
        return f"{self.name}({', '.join(str(a) for a in self.args)})"

    def free_vars(self):
        fv = set()
        for a in self.args:
            fv |= a.free_vars()
        return fv

    def subst(self, mapping):
        return FuncApp(self.name, tuple(a.subst(mapping) for a in self.args))


def Const(name):
    return FuncApp(name, ())


# --- Formulas ---

@dataclass(frozen=True)
class Atom:
    pred: str
    args: tuple

    def __str__(self):
        if not self.args:
            return self.pred
        return f"{self.pred}({', '.join(str(a) for a in self.args)})"

    def free_vars(self):
        fv = set()
        for a in self.args:
            fv |= a.free_vars()
        return fv

    def subst(self, mapping):
        return Atom(self.pred, tuple(a.subst(mapping) for a in self.args))


@dataclass(frozen=True)
class Top:
    def __str__(self): return "⊤"
    def free_vars(self): return set()
    def subst(self, _): return self


@dataclass(frozen=True)
class Bot:
    def __str__(self): return "⊥"
    def free_vars(self): return set()
    def subst(self, _): return self


@dataclass(frozen=True)
class Neg:
    sub: object

    def __str__(self):
        return f"¬{self.sub}"

    def free_vars(self):
        return self.sub.free_vars()

    def subst(self, mapping):
        return Neg(self.sub.subst(mapping))


@dataclass(frozen=True)
class And:
    left: object
    right: object

    def __str__(self):
        return f"({self.left} ∧ {self.right})"

    def free_vars(self):
        return self.left.free_vars() | self.right.free_vars()

    def subst(self, mapping):
        return And(self.left.subst(mapping), self.right.subst(mapping))


@dataclass(frozen=True)
class Or:
    left: object
    right: object

    def __str__(self):
        return f"({self.left} ∨ {self.right})"

    def free_vars(self):
        return self.left.free_vars() | self.right.free_vars()

    def subst(self, mapping):
        return Or(self.left.subst(mapping), self.right.subst(mapping))


@dataclass(frozen=True)
class Implies:
    left: object
    right: object

    def __str__(self):
        return f"({self.left} → {self.right})"

    def free_vars(self):
        return self.left.free_vars() | self.right.free_vars()

    def subst(self, mapping):
        return Implies(self.left.subst(mapping), self.right.subst(mapping))


@dataclass(frozen=True)
class Forall:
    var: str
    body: object

    def __str__(self):
        return f"∀{self.var}.{self.body}"

    def free_vars(self):
        return self.body.free_vars() - {self.var}

    def subst(self, mapping):
        # don't substitute the bound variable
        m = {k: v for k, v in mapping.items() if k != self.var}
        return Forall(self.var, self.body.subst(m))


@dataclass(frozen=True)
class Exists:
    var: str
    body: object

    def __str__(self):
        return f"∃{self.var}.{self.body}"

    def free_vars(self):
        return self.body.free_vars() - {self.var}

    def subst(self, mapping):
        m = {k: v for k, v in mapping.items() if k != self.var}
        return Exists(self.var, self.body.subst(m))


Formula = Union[Atom, Top, Bot, Neg, And, Or, Implies, Forall, Exists]
