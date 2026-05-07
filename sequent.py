"""
Sequent data structure and LK' inference rule applications.

A sequent has the form  Γ ⊢ Δ  where Γ (left) and Δ (right) are lists of formulas.
Rules are applied *backwards* (from conclusion to premises) as required by Algorithm 2.
"""

from ast_nodes import (
    Var, FuncApp, Atom, Top, Bot,
    Neg, And, Or, Implies, Forall, Exists
)


class Sequent:
    def __init__(self, left, right):
        self.left = list(left)    # antecedent Γ
        self.right = list(right)  # succedent Δ

    def copy(self):
        return Sequent(self.left[:], self.right[:])

    def __repr__(self):
        L = ", ".join(str(f) for f in self.left) or "∅"
        R = ", ".join(str(f) for f in self.right) or "∅"
        return f"{L} ⊢ {R}"


# ---- Axiom check -------------------------------------------------------

def is_axiom(seq):
    """Return True if the sequent is closed by id, TR, or ⊥L."""
    # ⊥L: falsum on the left
    if any(isinstance(f, Bot) for f in seq.left):
        return True
    # TR: truth on the right
    if any(isinstance(f, Top) for f in seq.right):
        return True
    # id: same atomic formula on both sides
    left_atoms  = {f for f in seq.left  if isinstance(f, Atom)}
    right_atoms = {f for f in seq.right if isinstance(f, Atom)}
    return bool(left_atoms & right_atoms)


# ---- Term collection (used for quantifier instantiation) ---------------

def _terms_in_term(t, out):
    out.add(t)
    if isinstance(t, FuncApp):
        for a in t.args:
            _terms_in_term(a, out)

def _terms_in_formula(f, out):
    if isinstance(f, Atom):
        for a in f.args:
            _terms_in_term(a, out)
    elif isinstance(f, Neg):
        _terms_in_formula(f.sub, out)
    elif isinstance(f, (And, Or, Implies)):
        _terms_in_formula(f.left, out)
        _terms_in_formula(f.right, out)
    elif isinstance(f, (Forall, Exists)):
        _terms_in_formula(f.body, out)

def collect_terms(seq):
    """Return all terms appearing anywhere in the sequent."""
    out = set()
    for f in seq.left + seq.right:
        _terms_in_formula(f, out)
    return out


# ---- Rule applications -------------------------------------------------
# Each function returns None if no applicable rule is found.
# Non-branching rules return (rule_name, child_sequent).
# Branching rules return (rule_name, child1, child2).
# Quantifier rules return (rule_name, child_sequent, updated_used_insts).

def apply_nonbranching(seq, fresh_count):
    """
    Try: ¬L, ¬R, ∧L, ∨R, →R, ∀R (fresh), ∃L (fresh).
    Returns (rule, child) or None.
    """
    # ¬L: ¬A on left  →  remove ¬A, add A to right
    for i, f in enumerate(seq.left):
        if isinstance(f, Neg):
            c = seq.copy(); c.left.pop(i); c.right.append(f.sub)
            return "¬L", c

    # ¬R: ¬A on right  →  remove ¬A, add A to left
    for i, f in enumerate(seq.right):
        if isinstance(f, Neg):
            c = seq.copy(); c.right.pop(i); c.left.append(f.sub)
            return "¬R", c

    # ∧L: A∧B on left  →  replace with A, B
    for i, f in enumerate(seq.left):
        if isinstance(f, And):
            c = seq.copy(); c.left.pop(i); c.left += [f.left, f.right]
            return "∧L", c

    # ∨R: A∨B on right  →  replace with A, B
    for i, f in enumerate(seq.right):
        if isinstance(f, Or):
            c = seq.copy(); c.right.pop(i); c.right += [f.left, f.right]
            return "∨R", c

    # →R: A→B on right  →  remove A→B, add A to left, B to right
    for i, f in enumerate(seq.right):
        if isinstance(f, Implies):
            c = seq.copy(); c.right.pop(i)
            c.left.append(f.left); c.right.append(f.right)
            return "→R", c

    # ∀R: ∀x.A on right  →  remove ∀x.A, add A[x/c] to right (c fresh)
    for i, f in enumerate(seq.right):
        if isinstance(f, Forall):
            c_name = f"_c{fresh_count[0]}"; fresh_count[0] += 1
            c = FuncApp(c_name, ())
            child = seq.copy(); child.right.pop(i)
            child.right.append(f.body.subst({f.var: c}))
            return "∀R", child

    # ∃L: ∃x.A on left  →  remove ∃x.A, add A[x/c] to left (c fresh)
    for i, f in enumerate(seq.left):
        if isinstance(f, Exists):
            c_name = f"_c{fresh_count[0]}"; fresh_count[0] += 1
            c = FuncApp(c_name, ())
            child = seq.copy(); child.left.pop(i)
            child.left.append(f.body.subst({f.var: c}))
            return "∃L", child

    return None


def apply_branching(seq):
    """
    Try: ∧R, ∨L, →L.
    Returns (rule, child1, child2) or None.
    """
    # ∧R: A∧B on right  →  two children, one with A and one with B
    for i, f in enumerate(seq.right):
        if isinstance(f, And):
            c1 = seq.copy(); c1.right.pop(i); c1.right.append(f.left)
            c2 = seq.copy(); c2.right.pop(i); c2.right.append(f.right)
            return "∧R", c1, c2

    # ∨L: A∨B on left  →  two children, one with A and one with B
    for i, f in enumerate(seq.left):
        if isinstance(f, Or):
            c1 = seq.copy(); c1.left.pop(i); c1.left.append(f.left)
            c2 = seq.copy(); c2.left.pop(i); c2.left.append(f.right)
            return "∨L", c1, c2

    # →L: A→B on left  →  c1: prove premise (add A to right), c2: use conclusion (add B to left)
    for i, f in enumerate(seq.left):
        if isinstance(f, Implies):
            c1 = seq.copy(); c1.left.pop(i); c1.right.append(f.left)
            c2 = seq.copy(); c2.left.pop(i); c2.left.append(f.right)
            return "→L", c1, c2

    return None


def apply_quantifier(seq, used_insts, fresh_count):
    """
    Try ∀L or ∃R with term instantiation.
    Tries unused existing terms first; creates a fresh term if none left.
    Returns (rule, child, new_used_insts) or None.

    used_insts maps str(formula) -> set of str(term) already tried.
    The original ∀/∃ formula is kept in the sequent for re-use.
    """
    terms = collect_terms(seq)

    # ∀L: ∀x.A on left  →  keep ∀x.A, add A[x/t] to left
    for f in seq.left:
        if isinstance(f, Forall):
            key = str(f)
            used = used_insts.get(key, frozenset())
            unused = [t for t in terms if str(t) not in used]
            if unused:
                t = unused[0]
            else:
                c_name = f"_c{fresh_count[0]}"; fresh_count[0] += 1
                t = FuncApp(c_name, ())
            child = seq.copy()
            child.left.append(f.body.subst({f.var: t}))
            new_used = {**used_insts, key: used | {str(t)}}
            return "∀L", child, new_used

    # ∃R: ∃x.A on right  →  keep ∃x.A, add A[x/t] to right
    for f in seq.right:
        if isinstance(f, Exists):
            key = str(f)
            used = used_insts.get(key, frozenset())
            unused = [t for t in terms if str(t) not in used]
            if unused:
                t = unused[0]
            else:
                c_name = f"_c{fresh_count[0]}"; fresh_count[0] += 1
                t = FuncApp(c_name, ())
            child = seq.copy()
            child.right.append(f.body.subst({f.var: t}))
            new_used = {**used_insts, key: used | {str(t)}}
            return "∃R", child, new_used

    return None
