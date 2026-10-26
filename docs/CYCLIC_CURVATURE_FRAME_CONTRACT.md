# Cyclic curvature and discrete frame contract

Intake: `Pasted text(20261026-063320).txt`, supplied with the request to implement
a PR. Intake SHA-256:
`14edf6ad9e4d0e15ace14fab5ce7d53503076f3a48d4e3922d1376bafe8a72ac`.
Base: `2d3a6ed286fde7098d152b83c9c75580b98865d0`.

The implementation preserves the algebraic questions while correcting the
intake's stronger geometric claims.

## Exact statements and dependencies

1. For a commutative base ring R and an associative R-algebra A, take the
   R-module quotient of A by the **linear span** of commutators. Native
   `Matrix.trace` is cyclic after projection to this quotient. A diagonal
   curvature defect has an exact quotient-valued Chevalley–Eilenberg image
   when the matrix size is invertible in R. Use native `Submodule`, quotient,
   `TrivialLieModule`, and `LieModule.Cohomology.d₁₂`.
2. The supplied four-dimensional X and Z are involutions with XZ = -ZX.
   Their commutator word is -I. Nonidentity requires a characteristic
   assumption. Central real-unit rephasing leaves this commutator unchanged.
3. Reuse `AlbertCayleyDickson.SplitQuaternion.OpZornMatrix`, its existing
   minus-dot/skew-cross multiplication, and the first component of
   `zornRiccati_moving_frame_and_trifactor_fixed_point`:
   `corner = leftScale (X.a + dot q X.w) q - rightScale q X.b + X.v`.
   Characterize vanishing of this corner and exhibit the counterexample to
   its identification with the negative of the existing `opZornRiccati`.

`Canonical.ProjectiveRepresentationCocycle` already proves honest adjoint
composition for central multipliers. `Algebra.CyclicTraceStokes` proves trace
cyclicity for commutative coefficient rings; it does not supply the required
noncommutative coefficient quotient. `Geometry.RindlerCartanFrame` owns an
actual coordinate differential calculation and proves its Rindler connection
flat. These are separate statements.

## Scope corrections

- The cyclic quotient is a module, not the quotient ring by a commutator ideal.
  Quotient-valued exactness does not provide a central lift or a gauge change
  flattening the original A-valued connection.
- X and Z square to +I. Their signed subgroup has dihedral-type relations,
  not the quaternion-generator relations. No group-H² classification,
  fundamental group, or geometric holonomy is asserted by the matrix word.
- The intake's plus-dot Zorn product differs from the existing owner's product.
  Even under the intake convention, its claimed Riccati identity requires an
  ordering identity that fails for general noncommutative coefficients.
- A parenthesized algebraic sandwich contains neither a coframe nor an exterior
  derivative. It is not renamed Cartan torsion. An actual torsion theorem
  needs those additional structures and a proved identification.
- A logarithm of -I can exist. The obstruction discussed in the intake cannot
  be justified by claiming that no such logarithm exists.

## Validation boundary

[kernel_verified] All three new owner modules and
`Canonical.CyclicCurvatureFrameAudit` compiled with Lean 4.34.1 and mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`. The existing
`Algebra.FiniteSpinAlgebra` and `Canonical.AlbertCayleyDickson` dependencies
were also compiled. The latter reports pre-existing linter warnings; the new
modules report none.

The narrow check ran sequential `lean -o` invocations under the repository's
shared build lock, using the pinned, precompiled mathlib cache. This hosted
runtime required a process-path compatibility shim to locate Lean's executable;
no repository source or dependency pin was changed for that workaround.

The audit prints only `propext`, `Classical.choice`, and `Quot.sound` for the
listed theorems; `moving_corner_eq_zero_iff` uses only `propext`. No `sorryAx`,
custom axiom, `sorry`, `admit`, or `unsafe` was introduced. The staged proof-proxy
gate passes; the semantic-vacuity gate reports zero findings; the staged diff
passes `git diff --cached --check`. An independent source/semantic review
accepted the limited scope and did not claim an independent compiler run.

[accepted_limited_scope] The result is cyclic-module CE exactness and a signed
matrix commutator. [countermodel_found] The existing moving corner is not, in
general, the negative of the existing Riccati expression. Geometric holonomy,
Cartan torsion, and flattening of the original connection remain
[bucket_3_open_debt].

Normal provisioned-checkout reproduction target:

```sh
python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock \
  InfoGeometry.Canonical.CyclicCurvatureFrameAudit
```

The locked Lake target was also attempted. Dependency loading stopped before
compilation because `external_refs/atlas-lean` is absent in this checkout
(`Atlas: package directory not found`). The separate narrow kernel checks
passed using the pinned cache. They do not certify the full repository build
or its umbrella import graph.
