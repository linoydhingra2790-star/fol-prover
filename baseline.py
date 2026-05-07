"""
Baseline prover: Algorithm 2 from Hou (2021).

Naive backward proof search for first-order logic using LK'.
The prover applies rules in the priority order described in the textbook:
  1. Axioms (id, TR, ⊥L)         -- close the branch
  2. Non-branching rules           -- ¬L, ¬R, ∧L, ∨R, →R, ∀R, ∃L
  3. Branching rules               -- ∧R, ∨L, →L
  4. Quantifier instantiation      -- ∀L, ∃R  (existing term first, then fresh)
  5. Stop if nothing applies
"""

import time
from sequent import Sequent, is_axiom, apply_nonbranching, apply_branching, apply_quantifier
from parser import parse

# Default depth limit to prevent infinite loops on non-theorems
DEFAULT_MAX_DEPTH = 50


def prove(formula, max_depth=DEFAULT_MAX_DEPTH):
    """
    Try to prove a formula using Algorithm 2.
    Returns a result dict with:
      proved  -- True if a closed proof tree was found
      time    -- wall-clock time in seconds
      steps   -- number of rule applications
    """
    start = time.time()
    steps = [0]
    fresh = [0]  # shared fresh-constant counter

    initial = Sequent([], [formula])
    proved = _search(initial, {}, 0, fresh, steps, max_depth)

    return {
        "proved": proved,
        "time":   time.time() - start,
        "steps":  steps[0],
    }


def _search(seq, used_insts, depth, fresh, steps, max_depth):
    """Recursive backward proof search (one open branch at a time)."""
    steps[0] += 1

    if depth > max_depth:
        return False

    # --- Priority 1: axioms ---
    if is_axiom(seq):
        return True

    # --- Priority 2: non-branching rule ---
    result = apply_nonbranching(seq, fresh)
    if result:
        _, child = result
        return _search(child, used_insts, depth + 1, fresh, steps, max_depth)

    # --- Priority 3: branching rule ---
    result = apply_branching(seq)
    if result:
        _, c1, c2 = result
        # both sub-goals must be provable
        return (_search(c1, dict(used_insts), depth + 1, fresh, steps, max_depth) and
                _search(c2, dict(used_insts), depth + 1, fresh, steps, max_depth))

    # --- Priority 4 & 5: quantifier instantiation (∀L / ∃R) ---
    result = apply_quantifier(seq, used_insts, fresh)
    if result:
        _, child, new_used = result
        return _search(child, new_used, depth + 1, fresh, steps, max_depth)

    # --- Priority 6: no rule applies ---
    return False


# ---- Quick test when run directly --------------------------------------

if __name__ == "__main__":
    tests = [
        # (formula_string, expected_result)
        ("P -> P",                                          True),
        ("P /\\ Q -> Q /\\ P",                              True),
        ("P -> P \\/ Q",                                    True),
        ("(P -> Q) /\\ P -> Q",                             True),   # modus ponens
        ("(P -> Q) /\\ (Q -> R) -> P -> R",                True),   # hypothetical syllogism
        ("forall x. P(x) -> P(a)",                         True),
        ("exists x. P(x) -> exists x. P(x)",               True),
        ("P /\\ ~P",                                        False),  # contradiction, not a theorem
        ("P",                                               False),  # not a tautology
    ]

    print(f"{'Formula':<50} {'Expected':<10} {'Got':<10} {'Steps':<8} {'Time(ms)'}")
    print("-" * 90)
    for formula_str, expected in tests:
        f = parse(formula_str)
        r = prove(f)
        got = r["proved"]
        status = "OK" if got == expected else "FAIL"
        print(f"{formula_str:<50} {str(expected):<10} {str(got):<10} "
              f"{r['steps']:<8} {r['time']*1000:.2f}ms  [{status}]")
