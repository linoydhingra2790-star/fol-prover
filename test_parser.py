"""
Quick tests for the FOL parser.
Run: python test_parser.py
"""

import sys
sys.path.insert(0, ".")

from parser import parse, ParseError, LexError
from ast_nodes import Var, FuncApp


def test(desc, src, expected):
    try:
        result = str(parse(src))
        status = "PASS" if result == expected else "FAIL"
        if status == "FAIL":
            print(f"[{status}] {desc}")
            print(f"       got:      {result}")
            print(f"       expected: {expected}")
        else:
            print(f"[{status}] {desc}")
        return status == "PASS"
    except Exception as e:
        print(f"[FAIL] {desc} -- exception: {e}")
        return False


def test_error(desc, src):
    try:
        parse(src)
        print(f"[FAIL] {desc} -- expected error but got none")
        return False
    except (ParseError, LexError):
        print(f"[PASS] {desc} -- correctly raised error")
        return True


passed = 0
total = 0

def run(fn, *args):
    global passed, total
    total += 1
    if fn(*args):
        passed += 1

# Basic atoms
run(test, "bare predicate",          "P",            "P")
run(test, "predicate with args",     "P(x,y)",       "P(x, y)")
run(test, "nested function",         "R(f(x),y)",    "R(f(x), y)")
run(test, "Top unicode",             "⊤",            "⊤")
run(test, "Bot unicode",             "⊥",            "⊥")
run(test, "Top keyword",             "True",         "⊤")

# Connectives
run(test, "negation",                "~P",           "¬P")
run(test, "conjunction",             "P /\\ Q",       "(P ∧ Q)")
run(test, "disjunction",             "P \\/ Q",       "(P ∨ Q)")
run(test, "implication",             "P -> Q",       "(P → Q)")

# Precedence
run(test, "¬ > ∧",                   "~P /\\ Q",      "(¬P ∧ Q)")
run(test, "∧ > ∨",                   "P /\\ Q \\/ R",  "((P ∧ Q) ∨ R)")
run(test, "∨ > →",                   "P \\/ Q -> R",  "((P ∨ Q) → R)")
run(test, "→ right-assoc",           "P -> Q -> R",  "(P → (Q → R))")
run(test, "parens override",         "(P -> Q) /\\ R","((P → Q) ∧ R)")

# Quantifiers
run(test, "forall",                  "forall x. P(x)",          "∀x.P(x)")
run(test, "exists",                  "exists x. P(x)",          "∃x.P(x)")
run(test, "nested quantifiers",      "forall x. exists y. R(x,y)", "∀x.∃y.R(x, y)")
run(test, "quantifier over impl",    "forall x. (P(x) -> Q(x))","∀x.(P(x) → Q(x))")

# Realistic examples
run(test, "modus ponens",
    "(P -> Q) /\\ P -> Q",
    "(((P → Q) ∧ P) → Q)")
run(test, "transitivity",
    "forall x. forall y. forall z. (R(x,y) /\\ R(y,z) -> R(x,z))",
    "∀x.∀y.∀z.((R(x, y) ∧ R(y, z)) → R(x, z))")

# subst / free_vars
f = parse("forall x. (P(x,y) /\\ Q(z))")
assert f.free_vars() == {"y", "z"}, f"free_vars failed: {f.free_vars()}"
print("[PASS] free_vars")
passed += 1; total += 1

f2 = parse("P(x) -> Q(x,y)")
f2s = f2.subst({"x": Var("a"), "y": FuncApp("g", (Var("b"),))})
assert str(f2s) == "(P(a) → Q(a, g(b)))", str(f2s)
print("[PASS] subst")
passed += 1; total += 1

# Errors
run(test_error, "empty input",          "")
run(test_error, "unmatched paren",      "(P -> Q")
run(test_error, "bad character",        "P @ Q")
run(test_error, "trailing junk",        "P Q")

print(f"\n{passed}/{total} passed")
