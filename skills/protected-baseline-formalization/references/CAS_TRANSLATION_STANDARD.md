# Standard: Lean 4 ⇄ CAS (SymPy) Algebra Translation

Translation from Lean 4 to CAS algebras is paramount and MUST be standardized.
CAS (SymPy) provides speedup in development: identities, structure-constant
tables, sign conventions, and basis computations are verified symbolically in
seconds instead of being debugged through the Lean elaborator. This document is
the binding protocol for that handoff inside `protected-baseline-formalization`.

## Division of authority

| Stage | Authority |
|---|---|
| Symbolic verification, table generation, counterexample search | SymPy (fast, disposable) |
| Statement shaping (types, hypotheses, names) | negotiated here |
| Truth | Lean 4 kernel only |

A SymPy result is **never** final. It becomes truth only after re-expression as
a Lean theorem and successful kernel checking (`lake env lean <owner>.lean`).

## Mandatory pipeline (5 stages)

### Stage 1 — Fix the symbolic model in SymPy
- Basis order explicit and frozen (e.g. `(i, j)` pairs in lexicographic order).
- Exact arithmetic only: `Rational(1,2)`, `sqrt(n)`, symbolic parameters. No floats, ever.
- Every sign explicit; verify skew/symmetry, Jacobi, commutator, nilpotency identities that matter.
- Emit machine-readable artifacts (JSON/JSONL), not prose.

### Stage 2 — Normalize into an exchange artifact
Standard artifact shape (one JSON file per algebra object):

```json
{
  "object": "clifford_3",
  "basis": ["e1", "e2", "e3"],
  "ring": "Rational",
  "structure_constants": {"mul_table": "...", "skew": true, "jacobi_checked": true},
  "sympy_source": "scratch/cas/clifford_3.py",
  "artifact_hash": "<sha256>"
}
```

Rules:
- Store the generating `.py` under `scratch/cas/` and hash it.
- The artifact must be regenerable: rerunning the script reproduces it bit-for-bit.
- Record which identities SymPy actually checked — unchecked tables are marked `"checked": false` and may not be translated as if proven.

### Stage 3 — Translate statements (not proofs)
Translate the *statements* first: one Lean lemma per SymPy assertion, types and
hypotheses written by hand against the repo owner surface. Follow
`skills/sympy-to-lean-line-by-line/SKILL.md`: process assertions sequentially,
each Lean lemma compiles before the next is attempted, no `sorry` carried forward.

Naming convention: `<cas_object>_sym_<assertion>` so provenance is visible in
every downstream proof.

### Stage 4 — Prove against the owner surface
- Proofs target existing categorical owners (`Algebra/Grothendieck.lean`,
  `Canonical/TensorTowerColimit.lean`,
  `Categorical/FibonacciBraiding.lean`). Matrix-level CAS data is an
  *instance*, never a replacement for the categorical layer.
- Keep helper lemmas small, narrowly typed, reusable (repo size mandate).
- Respect the Finsupp/ExteriorAlgebra invariants from SKILL.md
  (typed `(1 : R)`, `noncomputable`, correct imports).

### Stage 5 — Kernel check + tracking
```bash
# Inspect running compiler processes first; never overlap verification commands.
lake env lean OwnerFile.lean   # targeted check only
git add -A                # immediately protect the work
```
Report exactly which commands passed/failed. Never claim a CAS-verified identity
is formalized until Stage 5 passes on the owner file.

## When NOT to route through CAS

- Statements already trivially provable in Lean directly (routing overhead > gain).
- Continuum/colimit claims — these go through the colimit owners only; CAS cannot
  certify them and analytic rhetoric is forbidden.
- Numerical approximation work (out of scope for this skill).

## Speedup discipline

Batch related identities into one SymPy script run before touching Lean. The
goal of the standardization is exactly this: one deterministic
script → artifact → statement batch → proof batch loop, instead of ad-hoc
per-theorem guessing in the elaborator.
