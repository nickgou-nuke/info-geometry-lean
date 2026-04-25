# SymPy -> Lean Handoff Notes (Local)

Use this checklist when moving symbolic results from SymPy into Lean-facing artifacts.

1. Prefer exact objects (`Rational`, symbolic constants, `sqrt`, `pi`) over floats.
2. Expand/factor/simplify only as needed to match target theorem shape.
3. Keep explicit assumption inventory (domains, positivity, nonzero constraints).
4. Provide one minimal numeric sanity check only as telemetry, not proof.
5. Treat Lean compile success as the final acceptance gate.
