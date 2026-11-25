# Real single-mode Fermi/Kerr verification

The mathematical deliverable is the existing real CAR atom coupled to a
normalized two-state Gibbs matrix and native real Massieu/entropy calculus.
It specializes the occupation to `x = β * (E - Ω * m)` and proves an explicit
counterexample to identifying the Lorentz Cartan kernel with `x = 0`.

## Sources

| Module | Content |
|---|---|
| `InfoGeometry.Clifford.FermiDiracAnalytic` | Existing scalar Fermi API, relocated with names preserved; sharp threshold, calculus, susceptibility and entropy |
| `InfoGeometry.Lie.LorentzCartanKernel` | Explicit real six-coordinate matrix, skewness, kernel membership and coordinate pairing |
| `InfoGeometry.Canonical.KerrUnruhFermionicHorizonBridge` | Actual normalized real matrix state, expectation, particle–hole conjugation, temperature calibration and Kerr parameter specialization |
| `InfoGeometry.Canonical.KerrUnruhFermionicHorizonAudit` | All public definitions/theorems in the three owners, inspected with `#print axioms` |

The real CAR operators are reused from
`InfoGeometry.Krein.TomitaMatrixAtom`, including both projector idempotence
and orthogonality laws. `Real.binEntropy` is Mathlib's native binary entropy.

## Mathematical result

For the existing number/hole projectors `N` and `Ñ`,

\[
G(x)=e^{-x}N+\widetilde N,\quad Z(x)=\operatorname{tr}G(x)=1+e^{-x},
\quad\rho(x)=Z(x)^{-1}G(x).
\]

The density has trace one, is positive semidefinite, and obeys

\[
n(x)=\operatorname{tr}(N\rho(x))=\frac1{1+e^x},
\qquad J\rho(x)J=\rho(-x).
\]

The log trace is exactly the differentiated potential:

\[
\Psi=\log Z,\quad\Psi'=-n,\quad\Psi''=\chi=n(1-n),
\quad S=\operatorname{binEntropy}(n)=\Psi+xn,\quad S'=-x\chi.
\]

Both sharp bounds, `χ ≤ 1/4` and `S ≤ log 2`, have equality exactly at
`x = 0`. For `β > 0`, this is exactly `E = Ω*m`. The occupation lies below
or above one half according to the sign of `E-Ω*m`.

The separate coordinate calculation uses

\[
Q=(0,0,m,0,0,E),\qquad B=(0,0,-\beta\Omega,0,0,\beta).
\]

It proves both `Q · B = β(E-Ωm)` and `Π(Q)B=0`. For
`(β,Ω,E,m)=(1,0,1,0)`, kernel membership holds but `Q · B = 1` and
occupation is strictly below one half. This is the explicit obstruction to
equating the Poisson kernel with the scalar threshold.

## Reproducible focused checks

Run from the repository root:

```sh
python3 verification/kerr-unruh/check.py --validate
python3 verification/kerr-unruh/audit.py --log <captured-strict-output.log>
```

The wrapper acquires the repository's shared build lock and validates both
workspace roots. `--validate` builds the focused targets and then checks all
axiom queries in one serialized transaction. The focused library configuration
passes `-DwarningAsError=true` to every repository module in the build, so its
owners are compiled strictly in that pass. The audit is then elaborated again
to obtain fresh axiom output. The individual `build` and `--strict-sources`
commands remain available.
The focused package uses the root's unchanged Lean 4.34.1
and Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612` pins. Missing dependencies
must be prepared before interpreting any build result.

`audit.py` compares the current explicit declaration inventory with the Lean
audit output, rejects proof-hole/bypass syntax, verifies matching dependency
pins, and allows only `propext`, `Classical.choice`, and `Quot.sound` in the
reported transitive axiom dependencies. The three owners have no private
declarations, structures, or local custom axioms.

The log check must accompany a fresh successful compiler invocation and
unchanged source hashes. Parsing a previously saved log alone does not
establish acceptance of the current source tree. The inventory parser is
scoped to the explicit declaration forms used by these three owners; new
declaration forms require a corresponding inventory review.

## Scope and integration

The source contract is [THEOREM_CONTRACT.md](THEOREM_CONTRACT.md); intake
claims and the supplied 21-import inventory are preserved in
[INTAKE.md](INTAKE.md). Physical source context is the fermionic thermal
factor in [Düztaş, Eq. (1)](https://doi.org/10.1140/epjc/s10052-024-13540-9)
and the distinction between fermionic scattering and quantum emission in
[Casals et al.](https://arxiv.org/abs/1207.7089).

Theorems here concern a finite real matrix model and real analysis. The
thermal factor alone does not include a greybody factor or asymptotic flux.
The sign condition classifies mode energies; it is not a spacetime-location
theorem. The matrix swap is a particle–hole involution, not a constructed
spacetime CPT action.

The original thermal module imports the relocated Fermi owner, preserving
all 14 moved public declarations byte-for-byte. The new bridge and audit are
exposed from `InfoGeometry.All`. A focused build does not establish a build
of that large umbrella or all legacy consumers; their observed validation
status must be reported separately.

## Current evidence

The focused verification passed on 2026-11-25. The independent QA record is
[ACCEPTANCE.json](ACCEPTANCE.json), with source/configuration SHA-256 hashes
and the exact successful compiler output in [validation.log](validation.log).
The recorded Git HEAD precedes the final proof-script repairs; the record's
source hashes identify the actual tested worktree. All recorded inputs stayed
unchanged throughout the successful run.

- Independent A-A semantic/source review: PASS, including the explicit
  normalization, native derivatives, coordinate convention, and counterexample.
- Independent QA-A: focused strict build and fresh declaration audit passed.
  Its separate inventory matches all 85 public declarations (41 analytic,
  9 Lorentz, and 35 bridge). All nine focused dependency revisions match
  their root pins, and their tracked sources were clean.
- `python -u -B verification/kerr-unruh/check.py --validate`: exit 0.
  The strict build covers the three owners, the audit module, and the reused
  `FiniteSpinAlgebra` and `TomitaMatrixAtom` modules. The fresh audit contains
  exactly 85 unique declaration records.
- `python -B verification/kerr-unruh/audit.py --log validation.log`: exit 0
  (run with the captured log's full path). The observed axiom union is exactly
  `Classical.choice`, `Quot.sound`, and `propext`; no proof holes or custom
  axioms were accepted.
- Staged proof gate: passed after scalar coefficient proofs were separated
  from matrix proof goals.
- Strict OpenGauss source screen: zero violations in the three owners.
- Scoped semantic-content audit: three files, zero findings.
- An explicitly scoped QA invocation of the staged gate including
  `InfoGeometry.All` exceeded the operating system's Git argument-list limit.
  The plain staged invocation passed; the scoped failure is a tool limitation,
  not a theorem or kernel result.
- The focused result does not certify the large `InfoGeometry.All` umbrella,
  the legacy thermal owner's other dependencies, or the root push gate.
  Those integration checks are reported separately in the pull request.
