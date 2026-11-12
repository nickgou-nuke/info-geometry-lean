# Noncommutative holonomy and curvature: theorem contract

Source: user attachment `Pasted text(20261112-192446).txt`, received 2026-11-12.
Source SHA-256: `40a37834756be6116a66272bb03de7be2f95f4ffff0316fb48faac3734efecd6`.
Base: `a392af178af1fe2bcba2ba39eb405700c6ee103c`.

The attached Lean text stops after its first matrix multiplication lemma.
The mathematical specification is reconstructed against the existing owners.

## Carrier and owner decisions

| Stream | Carrier and assumptions | Existing owner | Addition |
| --- | --- | --- | --- |
| Quaternion factors | Any associative unital ring; invertible `2` for actual factor inverses | `Clifford.SplitAtomDoubling` | Nested negative generators, quaternion relations, factor conjugation and curvature realization |
| Quadratic BCH | Strictly upper triangular `3 × 3` matrices over `Ring A`; invertible `2` | Existing finite Heisenberg and square-zero Peirce owners have different carriers | Ring-valued class-two unipotent group, BCH group, exponential/logarithm equivalence |
| Discrete holonomy | Units of any ring, finite permutation indices | `LatticeGauge.FinitePlaquette` | Invertible weighted permutation matrices and multiplicative commutator realization |
| Connections | Native linear endomorphisms, Leibniz law, specified commuting directions | `Geometry.AssociativeGaugeConnection` | Reuse its regular-module connection and finite gauge covariance |
| Bianchi | `CommRing R`, `Ring A`, `Algebra R A`; native derivation Lie lane and Chevalley--Eilenberg forms | `OperatorAlgebra.DerivationDifferentialForms` | Reuse the general Bianchi theorem; preserve its Lie-direction correction |

## Canonical interfaces

The single import entry point is:

```lean
import InfoGeometry.Canonical.NoncommutativeHolonomyCurvature
```

| Owner under `InfoGeometry` | Principal interfaces |
| --- | --- |
| `Algebra.QuaternionCayley` | `factor_commutator`, `factor_sandwich`, `factors_commute_iff`, `factorUnit`, `factorUnit_conjugate` |
| `Algebra.UnitriangularBCH3.Unitriangular3` | `toUnits`, `toUnits_injective`, `mem_matrixSubgroup_iff`, `matrixEquiv`, `group_commutator`, `matrix_generators_noncommute` |
| `Algebra.UnitriangularBCH3.BCH3` | `expEquiv`, `matrixExpEquiv`, `toNilpotent_triple_mul_zero`, `toNilpotent_mul`, `toMatrix_expEquiv`, `toNilpotent_log`, `quadratic_exp_mul`, `quadratic_exp_mul_neg`, `matrix_group_commutator` |
| `Weyl.OperatorBraiding` | `braidingHolonomy_gauge`, `clock_shift_braid`, `clockUnit_shiftUnit_commutator`, `clockUnit_shiftUnit_commute_iff`, `shift_edgeGauge` |
| `Weyl.OperatorBraidingExamples` | `holonomy_value`, `holonomy_not_scalar`, `holonomy_noncentral`, `clock_shift_matrices_noncommute` |
| `Clifford.SplitQuaternionCurvature` | `axisI`, `axisJ`, `axisK`, `axis_factor_conjugate`, `frame_curvature`, `constant_frame_curvature_action`, `gauge_frame_curvature` |
| `Geometry.AssociativeGaugeConnection` | New `curvature_square_split`, `commutator_square_expansion`, `curvature_square_gauge_covariant`; existing connection and gauge theorems reused |
| `OperatorAlgebra.DerivationDifferentialForms` | Existing `connectionCurvature_bianchi`, `covariantDerivative_commutator`, `connectionCurvature_gaugeOneForm` |

For the nilpotent branch, coordinates `(a,b,c)` represent entries `(0,1)`,
`(1,2)`, `(0,2)`. The unitriangular product is

```text
(a,b,c) * (a',b',c') = (a+a', b+b', c+c'+a*b').
```

The BCH product replaces the third coordinate by
`c+c'+⅟2*(a*b'-a'*b)`. Its exponential maps that coordinate to
`c+⅟2*(a*b)`, and its inverse subtracts the same correction.
`matrixExpEquiv` maps onto the whole unitriangular matrix subgroup;
`mem_matrixSubgroup_iff` characterizes that subgroup by its six fixed entries.

For the holonomy branch, the concrete witness takes coefficient ring
`Matrix (Fin 2) (Fin 2) ℤ`, outer index `Fin 2`, the swap permutation,
constant edge label `!![1,1;0,1]`, and constant vertex label `!![1,0;1,1]`.
The ordered holonomy is `!![0,1;-1,3]`. It has a nonzero off-diagonal entry
and fails to commute with the edge label. The resulting clock and weighted
shift do not commute in the full nested matrix ring.

The quaternion branch uses the repository's negative generator convention
`!![0,1;-1,0]`, the opposite sign to the attachment's displayed skew generator.
Defining `axisK = axisI * axisJ` fixes the orientation consistently.

## Mathematical corrections

1. Clifford polynomial relations over a ring do not establish a universal
   Clifford/matrix algebra equivalence. The integral diagonal-signature
   generators do not generate every integral `2 × 2` matrix.
2. Over the reals, `Cl(0,2)` is the quaternion algebra, while `Cl⁰(0,2)` is
   its two-dimensional even subalgebra. Ring-level quaternion relations do not
   supply compactness or a real Lie algebra identification.
3. The factors `1 ± E`, with `E² = -1`, multiply to `2`. They are constructed
   as units only with an invertible `2`. No original-Clifford Spin membership
   is claimed for an inhomogeneous factor involving an odd generator.
4. The exponential is an isomorphism from the BCH group law, not from ordinary
   addition. Multiplicativity is proved in coordinates. A separate theorem
   proves that every triple product in the strictly upper triangular algebra
   vanishes, a stronger assertion than elementwise vanishing cubes.
5. The weighted shift has row `i`, column `σ i`. The holonomy order is
   `V i * U i * (V (σ i))⁻¹ * (U i)⁻¹`.
6. `d + L_A` is a connection on the right regular module. The stated left
   multiplication action does not make it a left-module connection.
7. A quaternion frame realizes `F₁₂ = 2 E₃` when the derivative contribution
   vanishes; arbitrary derivations of the matrix algebra need not fix it.
8. The ordered square expansion retains both mixed products. No commutation
   of coefficient operators is imposed.

## Dependency discipline

The Clifford, nilpotent, discrete, and differential streams are separate
constructions over associative algebras. Only explicit maps and theorems
connect them. In particular, this work does not assert a discrete-continuum
limit, Mellin inversion, a categorical braiding, an all-stage Clifford
equivalence, or a physical gauge-field consequence.

The established dependency order is:

1. The existing sign-twisted doubling and generic quaternion identities
   construct the nested quaternion frame. The existing connection theorem
   then specializes to its constant curvature and gauge transport.
2. The unitriangular coordinate group is represented faithfully by invertible
   matrices. The BCH law and exponential equivalence are constructed over that
   explicit carrier, with polynomial matrix readouts proved afterwards.
3. The existing plaquette lattice construction gives the loop/shift holonomy
   and its covariance. Invertible weighted permutation matrices realize the
   braid and commutator; the integer-matrix example proves noncentrality.
4. The existing connection calculus supplies curvature and finite covariance.
   Its ordered square expansion is an algebraic consequence. The existing
   derivation Lie lane and Chevalley--Eilenberg calculus supply Bianchi with
   the direction-bracket correction.

The analogy from a square-zero `2 × 2` ladder to the `3 × 3` nilpotent algebra
does not itself define an inclusion or implication. Likewise, the finite
plaquette theorem does not derive the differential connection calculus.

## Reproducing the focused native check

Lean remains `leanprover/lean4:v4.34.1`; Mathlib remains
`d13f23b723b8a846827a245b89c10fc7d3f11612`.
Use the pinned Lean executable on `PATH` and an initialized Mathlib checkout
at that exact revision. The existing source-closure checker acquires the
shared repository build lock and audits every declaration owned by each
selected theorem module:

```bash
python3 tools/quality/check_clifford_dirac.py \
  --mathlib-root .lake/packages/mathlib \
  --target InfoGeometry.Algebra.QuaternionCayley \
  --target InfoGeometry.Algebra.UnitriangularBCH3 \
  --target InfoGeometry.Weyl.OperatorBraiding \
  --target InfoGeometry.Weyl.OperatorBraidingExamples \
  --target InfoGeometry.Clifford.SplitQuaternionCurvature \
  --target InfoGeometry.Geometry.AssociativeCurvatureSquare \
  --target InfoGeometry.OperatorAlgebra.DerivationDifferentialForms \
  --target InfoGeometry.OperatorAlgebra.DerivationGaugeTransport \
  --output /tmp/noncommutative-holonomy-curvature-check
```

Use a fresh output directory for acceptance. The import-only canonical entry
point owns no declarations, so compile it separately against the verified
closure under the same shared lock; it is not a declaration-audit target.
The generated report records the exact source hashes, dependency closure,
compiler version, module outcomes, declaration counts, and permitted axiom
union. The focused check does not certify unrelated root-package targets.

The repository's file/module wrappers and publication gate remain separate
requirements. Their results are recorded at their actual scope alongside
independent semantic review and QA.

## Native verification record

On 2026-11-12, an independent fresh run compiled all 22 repository modules in
the selected dependency closure. All six new theorem owners compiled with
zero warnings. Six unchanged dependencies emitted 22 existing warnings
(one deprecated import and 21 style, simp, or unused-variable warnings).

The native audit checked all 397 declarations owned by the eight selected
modules, including generated and private declarations. The axiom union was
exactly `propext`, `Classical.choice`, and `Quot.sound`.

| Selected owner | Audited declarations | Role |
| --- | ---: | --- |
| `Algebra.QuaternionCayley` | 23 | New |
| `Algebra.UnitriangularBCH3` | 151 | New |
| `Weyl.OperatorBraiding` | 57 | New |
| `Weyl.OperatorBraidingExamples` | 22 | New |
| `Clifford.SplitQuaternionCurvature` | 27 | New |
| `Geometry.AssociativeCurvatureSquare` | 5 | New |
| `OperatorAlgebra.DerivationDifferentialForms` | 83 | Reused |
| `OperatorAlgebra.DerivationGaugeTransport` | 29 | Reused |

This is 285 declarations in new owners and 112 in reused differential owners.
Source SHA-256 values were checked before and after compilation and audit;
the Lean and Mathlib pins and verification implementation remained unchanged.
The independent semantic reviewer also accepted the actual carriers,
hypotheses, coefficient order, and noncentral matrix witnesses at the final
source hashes. Compilation, axiom inspection, and semantic review are
separate completed checks.

The import-only canonical entry point also compiled separately with exit 0
and zero warnings, giving 23 checked repository modules in total. The staged
proof gate and strict OpenGauss scan passed; all seven strict placeholder
scans found zero hard findings. The semantic scan passed at the error
threshold, with 27 advisory `trivial_surface` findings: 24 explicit
coordinate/coercion readouts and three elementary cancellation or diagonal
matrix identities. The placeholder scanner additionally marked two of those
elementary identities as soft skeletal-proof findings. Independent source
review and native kernel checking confirmed their actual content; the
advisories were retained rather than disabled.

The maintained root-package commands were also run:

```bash
python3 tools/infra/run_locked_lean.py --wait-for-build-lock \
  lean/InfoGeometry/Canonical/NoncommutativeHolonomyCurvature.lean
python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock \
  InfoGeometry.Canonical.NoncommutativeHolonomyCurvature
```

Both exited 1 before elaborating the selected source because the root package
requires the absent directory `external_refs/homotopy-hypothesis-lean4`
(`HomotopyHypothesis`). This requirement is already present at the base
revision. The root `lakefile.lean`, manifest, toolchain, and quality gates were
not changed. Therefore the focused native result is a proof certificate for
the stated source closure, while root-package validation remains blocked by
that missing dependency. Publication must respect the repository's separate
pre-push gate.
