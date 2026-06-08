# Formal Theory Quantum SymPy Companions

Lean source:

- `formal-theory-quantum.lean`
- `proofs/formal-theory-quantum.lean` is currently identical.

Run:

```bash
.venv-py312/bin/python tools/sympy/formal_theory_quantum/run_pipeline.py
```

The runner scans the Lean chapter stubs, requires one Python companion per
chapter, executes each companion, and writes:

```text
artifacts/sympy/formal_theory_quantum/results.json
```

The companions are finite computational shadows:

1. `chapter1_quantum_sl2.py` checks the fundamental `U_q(sl2)` representation.
2. `chapter2_quasitriangular.py` checks finite quasitriangular intertwining.
3. `chapter3_yang_baxter.py` checks `R12 R13 R23 = R23 R13 R12`.
4. `chapter4_braided_category.py` checks the braid operator relation.
5. `chapter5_roots_of_unity.py` checks root-of-unity quantum integer collapse.
6. `chapter6_fibonacci_mtc.py` checks the Fibonacci fusion ring shadow.
7. `chapter7_explicit_f_and_r.py` checks explicit `F` and `R` matrix facts.
8. `chapter8_hexagon.py` checks the finite Fibonacci Artin/Yang-Baxter matrix identity.

These files do not prove the Lean stubs.  They provide executable algebraic
evidence and regression tests for the finite matrix shadows that a later Lean
formalization can target.
