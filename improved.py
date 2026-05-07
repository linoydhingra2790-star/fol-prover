"""
Improved backward proof search for first-order logic using LK'.

Three improvements over Algorithm 2 (baseline):

  1. Loop detection
     Track visited sequents on the current branch. If the same sequent
     appears twice we are in a cycle and return False immediately.
     This prevents the algorithm from spinning forever on non-theorems.

  2. Redundancy elimination
     Before adding a formula to a sequent, check if it is already there.
     This stops quantifier rules from generating duplicate instantiations.

  3. Goal-directed, two-phase quantifier instantiation
     The baseline applies ∀L (with a fresh term) before ever trying ∃R,
     which causes it to miss proofs that require interleaving both rules.

     The improved strategy:
       Phase 1 — use existing terms, guided by the sequent sides:
                   ∀L prefers terms from the goal  (right side)
                   ∃R prefers terms from the facts (left side)
                 Both are tried before any fresh term is created.
       Phase 2 — if no existing term works, create a fresh constant.

     Example where baseline fails: ∀x.P(x) → ∃y.P(y)
       Baseline keeps applying ∀L with fresh terms until the depth
       limit is hit.  The improved prover applies ∀L once (fresh _c0),
       then immediately uses _c0 as the witness for ∃R, closing in 4
       steps.
"""

import time
from sequent import Sequent, is_axiom, apply_branching
from ast_nodes import Var, FuncApp, Atom, Neg, And, Or, Implies, Forall, Exists
from parser import parse

DEFAULT_MAX_DEPTH = 50


def prove_improved(formula, max_depth=DEFAULT_MAX_DEPTH):
    """
    Prove formula using the improved prover.
    Returns dict: proved (bool), time (float), steps (int).
    """
    start = time.time()
    steps = [0]
    fresh = [0]
    initial = Sequent([], [formula])
    proved = _search(initial, {}, frozenset(), 0, fresh, steps, max_depth)
    return {
        "proved": proved,
        "time":   time.time() - start,
        "steps":  steps[0],
    }


# ---- Helpers -----------------------------------------------------------

def _seq_key(seq):
    return (frozenset(str(f) for f in seq.left),
            frozenset(str(f) for f in seq.right))


def _add_if_new(lst, formula):
    """Improvement 2: only append if not already present."""
    if formula not in lst:
        lst.append(formula)


def _collect_side(formulas):
    """Collect all terms appearing in a list of formulas."""
    out = set()
    def from_term(t):
        out.add(t)
        if isinstance(t, FuncApp):
            for a in t.args: from_term(a)
    def from_formula(f):
        if isinstance(f, Atom):
            for a in f.args: from_term(a)
        elif isinstance(f, Neg): from_formula(f.sub)
        elif isinstance(f, (And, Or, Implies)):
            from_formula(f.left); from_formula(f.right)
        elif isinstance(f, (Forall, Exists)): from_formula(f.body)
    for f in formulas:
        from_formula(f)
    return out


# ---- Non-branching rules (with redundancy check) -----------------------

def _nonbranching(seq, fresh):
    for i, f in enumerate(seq.left):
        if isinstance(f, Neg):
            c = seq.copy(); c.left.pop(i); _add_if_new(c.right, f.sub)
            return "¬L", c
    for i, f in enumerate(seq.right):
        if isinstance(f, Neg):
            c = seq.copy(); c.right.pop(i); _add_if_new(c.left, f.sub)
            return "¬R", c
    for i, f in enumerate(seq.left):
        if isinstance(f, And):
            c = seq.copy(); c.left.pop(i)
            _add_if_new(c.left, f.left); _add_if_new(c.left, f.right)
            return "∧L", c
    for i, f in enumerate(seq.right):
        if isinstance(f, Or):
            c = seq.copy(); c.right.pop(i)
            _add_if_new(c.right, f.left); _add_if_new(c.right, f.right)
            return "∨R", c
    for i, f in enumerate(seq.right):
        if isinstance(f, Implies):
            c = seq.copy(); c.right.pop(i)
            _add_if_new(c.left, f.left); _add_if_new(c.right, f.right)
            return "→R", c
    for i, f in enumerate(seq.right):
        if isinstance(f, Forall):
            name = f"_c{fresh[0]}"; fresh[0] += 1
            c = seq.copy(); c.right.pop(i)
            _add_if_new(c.right, f.body.subst({f.var: FuncApp(name, ())}))
            return "∀R", c
    for i, f in enumerate(seq.left):
        if isinstance(f, Exists):
            name = f"_c{fresh[0]}"; fresh[0] += 1
            c = seq.copy(); c.left.pop(i)
            _add_if_new(c.left, f.body.subst({f.var: FuncApp(name, ())}))
            return "∃L", c
    return None


# ---- Quantifier instantiation (two-phase, goal-directed) ---------------

def _quantifier(seq, used_insts, fresh):
    """
    Improvement 3: two-phase quantifier strategy.
    Phase 1: try existing unused terms.
      ∀L uses right-side (goal) terms first.
      ∃R uses left-side (fact) terms first.
    Phase 2: fall back to a fresh constant if nothing else works.
    """
    right_terms = _collect_side(seq.right)
    left_terms  = _collect_side(seq.left)

    # goal-directed ordering: ∀L wants goal terms, ∃R wants fact terms
    def ordered_for_univ(all_terms):
        return list(right_terms & all_terms) + list((all_terms - right_terms))

    def ordered_for_exist(all_terms):
        return list(left_terms & all_terms) + list((all_terms - left_terms))

    all_terms = left_terms | right_terms

    # --- Phase 1: existing unused terms ---
    # ∃R is tried before ∀L: avoids the failure mode where ∀L keeps
    # creating fresh constants without ever trying available witnesses for ∃R.

    for f in seq.right:
        if isinstance(f, Exists):
            key  = str(f)
            used = used_insts.get(key, frozenset())
            candidates = [t for t in ordered_for_exist(all_terms) if str(t) not in used]
            if candidates:
                t = candidates[0]
                child = seq.copy()
                _add_if_new(child.right, f.body.subst({f.var: t}))
                return "∃R", child, {**used_insts, key: used | {str(t)}}

    for f in seq.left:
        if isinstance(f, Forall):
            key  = str(f)
            used = used_insts.get(key, frozenset())
            candidates = [t for t in ordered_for_univ(all_terms) if str(t) not in used]
            if candidates:
                t = candidates[0]
                child = seq.copy()
                _add_if_new(child.left, f.body.subst({f.var: t}))
                return "∀L", child, {**used_insts, key: used | {str(t)}}

    # --- Phase 2: fresh constant ---

    for f in seq.left:
        if isinstance(f, Forall):
            key  = str(f)
            used = used_insts.get(key, frozenset())
            name = f"_c{fresh[0]}"; fresh[0] += 1
            t = FuncApp(name, ())
            child = seq.copy()
            _add_if_new(child.left, f.body.subst({f.var: t}))
            return "∀L", child, {**used_insts, key: used | {str(t)}}

    for f in seq.right:
        if isinstance(f, Exists):
            key  = str(f)
            used = used_insts.get(key, frozenset())
            name = f"_c{fresh[0]}"; fresh[0] += 1
            t = FuncApp(name, ())
            child = seq.copy()
            _add_if_new(child.right, f.body.subst({f.var: t}))
            return "∃R", child, {**used_insts, key: used | {str(t)}}

    return None


# ---- Core search -------------------------------------------------------

def _search(seq, used_insts, visited, depth, fresh, steps, max_depth):
    steps[0] += 1

    if depth > max_depth:
        return False

    # Improvement 1: loop detection
    key = _seq_key(seq)
    if key in visited:
        return False
    visited = visited | {key}

    if is_axiom(seq):
        return True

    result = _nonbranching(seq, fresh)
    if result:
        _, child = result
        return _search(child, used_insts, visited, depth + 1, fresh, steps, max_depth)

    result = apply_branching(seq)
    if result:
        _, c1, c2 = result
        return (_search(c1, dict(used_insts), visited, depth + 1, fresh, steps, max_depth) and
                _search(c2, dict(used_insts), visited, depth + 1, fresh, steps, max_depth))

    result = _quantifier(seq, used_insts, fresh)
    if result:
        _, child, new_used = result
        return _search(child, new_used, visited, depth + 1, fresh, steps, max_depth)

    return False


# ---- Comparison test ---------------------------------------------------

if __name__ == "__main__":
    from baseline import prove as prove_baseline

    tests = [
        # (formula, expected)
        ("P -> P",                                                    True),
        ("P /\\ Q -> Q /\\ P",                                        True),
        ("(P -> Q) /\\ P -> Q",                                       True),
        ("(P -> Q) /\\ (Q -> R) -> P -> R",                          True),
        ("forall x. P(x) -> P(a)",                                   True),
        # baseline fails on this — needs interleaved ∀L and ∃R
        ("forall x. P(x) -> exists y. P(y)",                         True),
        # needs ∃ witness from the left side
        ("exists x. forall y. R(x,y) -> forall y. exists x. R(x,y)", True),
        ("exists x. P(x) -> exists x. P(x)",                         True),
        ("(P -> Q) /\\ (P -> ~Q) -> ~P",                             True),
        ("P /\\ ~P",                                                  False),
        ("P",                                                         False),
        ("exists x. P(x)",                                           False),
    ]

    print(f"{'Formula':<58} {'Exp':<6} {'Base':>8} {'Impr':>8}  "
          f"{'B-steps':>8} {'I-steps':>8}  {'B-ok':<5} {'I-ok':<5}")
    print("-" * 120)

    for src, expected in tests:
        f = parse(src)
        b = prove_baseline(f)
        m = prove_improved(f)
        b_ok = "OK" if b["proved"] == expected else "FAIL"
        i_ok = "OK" if m["proved"] == expected else "FAIL"
        print(f"{src:<58} {str(expected):<6} "
              f"{b['time']*1000:>6.2f}ms {m['time']*1000:>6.2f}ms  "
              f"{b['steps']:>8} {m['steps']:>8}  {b_ok:<5} {i_ok:<5}")
