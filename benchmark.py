"""
benchmark.py  —  Run baseline and improved provers on all datasets.

Usage:
    python benchmark.py

Outputs a per-formula result table and a per-dataset summary.
The expected result is inferred from the dataset filename:
  non_theorems.txt  -> False
  everything else   -> True
"""

import os
import time
from parser import parse_file, ParseError
from baseline import prove as prove_baseline
from improved import prove_improved

DATA_DIR = os.path.join(os.path.dirname(__file__), "data")
MAX_DEPTH = 50


def load_dataset(path):
    """Load formulas from a .txt file. Returns list of (lineno, formula)."""
    try:
        return parse_file(path)
    except ParseError as e:
        print(f"  Parse error in {path}: {e}")
        return []


def run_dataset(name, path, expected):
    entries = load_dataset(path)
    if not entries:
        return []

    results = []
    for lineno, formula in entries:
        b = prove_baseline(formula, MAX_DEPTH)
        m = prove_improved(formula, MAX_DEPTH)
        results.append({
            "formula":  str(formula),
            "expected": expected,
            "b_proved": b["proved"],
            "b_steps":  b["steps"],
            "b_time":   b["time"],
            "m_proved": m["proved"],
            "m_steps":  m["steps"],
            "m_time":   m["time"],
        })
    return results


def print_table(name, results):
    W = 55
    print(f"\n{'='*100}")
    print(f"  Dataset: {name}  ({len(results)} formulas)")
    print(f"{'='*100}")
    print(f"  {'Formula':<{W}} {'Exp':<5}  "
          f"{'B-res':<6} {'B-steps':>7} {'B-ms':>7}  "
          f"{'I-res':<6} {'I-steps':>7} {'I-ms':>7}  {'Status'}")
    print(f"  {'-'*W} {'-'*5}  {'-'*6} {'-'*7} {'-'*7}  {'-'*6} {'-'*7} {'-'*7}  {'-'*6}")

    for r in results:
        f_str = r["formula"]
        if len(f_str) > W - 2:
            f_str = f_str[:W - 5] + "..."

        b_ok = r["b_proved"] == r["expected"]
        i_ok = r["m_proved"] == r["expected"]
        status = "OK" if (b_ok and i_ok) else ("B-FAIL" if not b_ok else "I-FAIL")

        print(f"  {f_str:<{W}} {str(r['expected']):<5}  "
              f"{'T' if r['b_proved'] else 'F':<6} {r['b_steps']:>7} {r['b_time']*1000:>7.2f}  "
              f"{'T' if r['m_proved'] else 'F':<6} {r['m_steps']:>7} {r['m_time']*1000:>7.2f}  "
              f"{status}")


def print_summary(name, results):
    b_correct = sum(1 for r in results if r["b_proved"] == r["expected"])
    m_correct = sum(1 for r in results if r["m_proved"] == r["expected"])
    n = len(results)

    proved = [r for r in results if r["expected"]]
    if proved:
        b_avg_steps = sum(r["b_steps"] for r in proved) / len(proved)
        m_avg_steps = sum(r["m_steps"] for r in proved) / len(proved)
        b_avg_ms    = sum(r["b_time"]  for r in proved) / len(proved) * 1000
        m_avg_ms    = sum(r["m_time"]  for r in proved) / len(proved) * 1000
        step_ratio  = b_avg_steps / m_avg_steps if m_avg_steps > 0 else float("inf")
    else:
        b_avg_steps = m_avg_steps = b_avg_ms = m_avg_ms = step_ratio = 0

    print(f"\n  Summary — {name}")
    print(f"    Correct:       baseline {b_correct}/{n}    improved {m_correct}/{n}")
    if proved:
        print(f"    Avg steps:     baseline {b_avg_steps:.1f}    improved {m_avg_steps:.1f}"
              f"    (speedup {step_ratio:.1f}x)")
        print(f"    Avg time (ms): baseline {b_avg_ms:.2f}    improved {m_avg_ms:.2f}")


def main():
    datasets = [
        ("Propositional (easy)",  "prop_easy.txt",    True),
        ("FOL (medium)",          "fol_medium.txt",   True),
        ("FOL (hard)",            "fol_hard.txt",     True),
        ("Non-theorems",          "non_theorems.txt", False),
    ]

    all_results = []

    for name, filename, expected in datasets:
        path = os.path.join(DATA_DIR, filename)
        if not os.path.exists(path):
            print(f"Missing: {path}")
            continue
        results = run_dataset(name, path, expected)
        print_table(name, results)
        print_summary(name, results)
        all_results.extend(results)

    # Overall summary
    if all_results:
        total = len(all_results)
        b_total = sum(1 for r in all_results if r["b_proved"] == r["expected"])
        m_total = sum(1 for r in all_results if r["m_proved"] == r["expected"])
        print(f"\n{'='*100}")
        print(f"  OVERALL: {total} formulas — "
              f"baseline {b_total}/{total} correct, "
              f"improved {m_total}/{total} correct")
        print(f"{'='*100}\n")


if __name__ == "__main__":
    main()
