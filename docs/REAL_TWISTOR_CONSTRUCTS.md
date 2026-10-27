# Real twistor constructions: owners, theorems, and boundaries

This extension uses intrinsically real carriers. It does not complexify a
space or obtain a new real carrier by forgetting complex scalar structure.
The existing repository contains mixed-scalar dependencies; importing an
existing owner does not change the scalar field of these new constructions.

## Theorem contract and source reuse

The implementation starts from main `b143075bbf27e75860a1011e04423a0f227b7c41`.
The source audit traced actual declarations, hypotheses, imports and consumers.
The following owners already existed and remain authoritative:

- `Clifford/SolderingIsomorphism.solderingEquiv` identifies real split
  spacetime with `M₂(ℝ)`. Its original elementary section is moved unchanged
  into `Clifford/SolderingLinearEquiv`, keeping the same declaration names and
  remaining imported by `SolderingIsomorphism`. The new `operatorSoldering`
  composes this owner with Mathlib's matrix/operator equivalence.
- `Twistor/Incidence` proves the real null-separation criterion. The new native
  submodule/projective interface does not claim to discover that criterion.
- `Projective/ExteriorKleinTwoPlaneQuotient` and the exterior Klein incidence
  modules own real two-plane and exterior/Plücker geometry.
- `Krein/DoubledSpace` owns the doubled real carrier, its fundamental
  symmetry, the positive `doubledHilbertBilin`, and the existing indefinite
  `hessian_indefinite_form` used by the new bridge.
- `Canonical/FiniteDimensionalCCRNoGo` owns the trace obstruction to nonzero
  scalar CCR in finite dimension.
- `Canonical/KahlerAtiyahCartanForms` owns actual exterior multiplication and
  contraction operators and their CAR.
- `Clifford/SplitClifford55ExteriorSpinor` owns the real exterior-spinor
  representation, neutral Clifford action and pure-spinor annihilators.
- `Canonical/QuaternionTwistorSphereReal` owns the real-linear quaternionic
  sphere of square-minus-one operators.

The source-confirmed gaps addressed here are native real incidence subspaces
and reconstruction, their actual dual/projective annihilators, a real
polynomial operator representation with proved normalization, and explicit
maps connecting these constructions to existing owners. Further new owners
construct oriented-line quotients and differential flat twistor-spinor
solutions. No theorem conclusion is introduced as a field of a certificate.

## Construction order

Real spinor modules give graph-incidence maps and submodules. The existing
soldering equivalence then interprets these as split-spacetime incidence
planes. Native bases reconstruct their operators; region-point differences
give null momenta and cyclic conservation.

Actual algebraic duals give symmetric neutral and alternating forms. Dual
annihilators connect them to graph incidence. Separate projectivizations give
the projective ambitwistor constraint. Explicit lightcone maps carry the
neutral form to the existing doubled Krein form using a finite-dimensional
real inner-product self-duality constructed without assuming it.

Polynomial multiplication and differentiation give exact bosonic CCR. The
factorial coefficient form proves positive normalization and algebraic
adjointness. A genuine dual-coordinate equivalence connects the CCR to the
same alternating form. Tensor-product actions combine this representation
with the existing exterior CAR, keeping both operator algebras distinct.

## Coverage

All modules below are under `lean/InfoGeometry/Twistor/`.

| Family or tool | New owner | Exact scope |
| --- | --- | --- |
| Ordinary real split twistors | `RealTwistorIncidence`, `RealTwistorSoldering` | Native incidence submodules, projective injection, real soldering equivalence, dimension two, null intersection criterion |
| Multiple twistors | `RealMultiTwistorReconstruction` | Unique native-basis reconstruction and covariance; no massive constrained-particle reduction |
| Momentum twistors | `RealMomentumTwistor` | Region momenta, cyclic conservation, null-edge incidence equivalence, nonzero null polygon example |
| Dual twistors and affine ambitwistors | `RealDualTwistor`, `RealTwistorDualIncidence` | Actual algebraic dual, nondegenerate pairings, exact annihilator parametrization, nonzero rank-one nilpotence criterion |
| Projective ambitwistors | `RealProjectiveAmbitwistor` | Incidence subtype of the product of separate projective vector/dual spaces and frame covariance; no null-geodesic manifold classification |
| Dual/Krein soldering | `RealDualTwistorKreinBridge` | Explicit algebraic equivalence, bilinear transport, fundamental involution and positive finite-dimensional normalization |
| Algebraic quantization | `RealTwistorPolynomialCCR`, `RealTwistorDualCCR` | Exact infinite-polynomial CCR for nonempty mode sets, occupation/Euler identities, intrinsic dual-coordinate compatibility |
| Algebraic state pairing | `RealTwistorFockPairing` | Positive factorial pairing, unit vacuum, creation/annihilation adjointness, injective map to the algebraic dual |
| Constrained configuration sector | `RealTwistorOneParticleSector`, `RealTwistorOneParticleRealization`, `RealTwistorOneParticleDual` | Actual polynomial projector, faithful number-conserving operators, and pairing-preserving finite primal/dual embedding with an explicit retraction |
| Positive sector and stationary action | `RealDualTwistorPositiveSector`, `RealTwistorSpectralAction` | Normalized positive graph, neutral self-adjoint projectors and operators, actual variational derivative, normalized eigen-equations |
| Supertwistor operator algebra | `RealSupertwistorOperators` | Polynomial tensor exterior carrier, bosonic CCR, fermionic CAR, commuting factors and fermionic nilpotence |
| Higher-dimensional Clifford/pure-spinor bridge | `RealDualTwistorClifford` | Pairing normalization and square-zero action equivalence for the existing real Cl(5,5) module; existing annihilator isotropy reused |
| Euclidean minitwistors | `RealMiniTwistor` | Actual quotient by translation along a fixed unit direction, perpendicular representative equivalence, incidence and unique parameter |
| Flat three-dimensional twistor spinors | `RealFlatTwistorSpinor` | Real quaternion Clifford action, actual Fréchet derivative, calculated Dirac contraction, flat twistor equation and translation law |
| Quaternionic twistor sphere compatibility | `RealFlatTwistorSpinor.sphere_action` | Explicit compatibility of that Clifford action with the existing quaternionic sphere |

The [concrete sector-action extension](REAL_TWISTOR_SECTOR_ACTION.md) connects
these operators to the existing three-configuration nuclear model. It proves
normalized stationary states and transition strengths in polynomial and
genuine-dual realizations, including an exact nonzero-mixing example. That
document records the real resolvent domain, physical interpretation boundary
and current extended validation results.

## Essential distinctions

The ordinary split twistor carrier is `Spinor × Spinor`, with each spinor
space real two-dimensional. A vector/covector pair belongs to `V × V*`;
when `V` is the four-dimensional twistor space, this is an eight-dimensional
phase carrier. Its two separate projectivizations are not the projectivization
of the whole direct sum. The Cl(5,5) adapter and the three-dimensional
quaternionic flat-spinor example use their own stated carriers; no theorem
identifies those different dimensions or signatures.

The symmetric neutral form and the alternating CCR form are different forms.
The square-plus-one fundamental symmetry is different from a real
square-minus-one Clifford operator. Exterior CAR and polynomial CCR remain
different operator relations, acting on different tensor factors.

The algebraic polynomial Fock pairing is positive definite, but its map into
the full algebraic dual is only proved injective. It is not used as an
infinite-dimensional self-duality. The concrete self-duality in the Krein
bridge is finite-dimensional. The lightcone bridge proves bilinear
compatibility of a `LinearEquiv`; it does not claim a topological Krein
completion or an unbounded-operator spectral theorem.

The minitwistor correspondence keeps opposite orientations distinct. It is a
real set/inner-product quotient theorem, not a holomorphic `O(2)` bundle or a
smooth tangent-bundle classification. The flat spinor theorem uses a genuine
derivative, but is not a classification of every solution or a curved spin
connection.

## Remaining larger constructions

The package does not claim a curved nonlinear-graviton correspondence,
Penrose/Ward cohomological transform, worldsheet or BRST quantization,
massive-particle symplectic reduction, BCFW/CHY amplitude theorem, or a
classification of noncommutative twistor deformations. These require their
own geometric, categorical, differential and state-space constructions.
The existing real pure-spinor, Klein, configuration-topology and amplitude
owners remain available without being relabeled as these stronger results.

## Mathematical references

- T. Adamo, *Lectures on twistor theory*, arXiv:1712.02196, real
  split-signature incidence: https://arxiv.org/abs/1712.02196.
- N. J. Hitchin, *Monopoles and Geodesics*, Commun. Math. Phys. 83 (1982),
  579–602, the oriented-geodesic construction:
  https://doi.org/10.1007/BF01208717.
- P. Somberg, *Twistor operators on conformally flat spaces*, Rend. Circ.
  Mat. Palermo Suppl. 66 (2001), 179–197, §1 equations (2)–(3), the flat
  twistor equation and affine spinor solutions: https://dml.cz/dmlcz/701678.

Literature supplies interpretation and conventions. The Lean theorem types
and their kernel-checked proofs determine the formalized scope.

## Integration and dependency boundary

The repository's toolchain, `lakefile.lean`, and manifest remain unchanged.
The elementary soldering extraction and the direct `DoubledSpace` bridge
keep the new audit module independent of `Architect` and the unrelated
projective/thermodynamic dependency chain. The extraction moves existing
declarations and proofs; it does not duplicate or replace the soldering map.

The root Lake configuration requires `external_refs/atlas-lean`, which is
absent from the inspected repository snapshot and is not a tracked gitlink.
That root-package dependency must be supplied before the ordinary root Lake
build and publication gate can be certified. Direct native Lean checks of
this package's actual source closure are reported separately below; they do
not constitute a full root Lake build.

## Initial geometry/quantization verification

The following records the initial PR snapshot at
`1a5e343eeb421f81c56ba3051e55f2d4d60cf405`. The later sector-action modules
enlarge the source closure; their current verification is recorded in
[REAL_TWISTOR_SECTOR_ACTION.md](REAL_TWISTOR_SECTOR_ACTION.md).

The initial `InfoGeometry.Twistor.RealConstructsAudit` check passed with Lean
4.34.1 and Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`, the repository's
unchanged pins. A disposable sequential runner used the repository's shared
build lock and invoked native `lean --root=<source-root> -o <output> <source>`
over the actual import closure. Source/dependency hashes kept compiled inputs
matched to the final source snapshot. The checked closure has 35 local source
modules; its external imports are Lean, Mathlib and Std.

- The final audit finished with zero errors and zero warnings.
- All 39 `#print axioms` queries returned only `propext`, `Classical.choice`
  and `Quot.sound`. None returned `sorryAx` or a custom axiom.
- `tools/quality/proof_proxy_staged_gate.py` passed.
- `tools/infra/axiom_audit.py --fail-on-gaps` found zero explicit proof holes
  or axiom declarations in all 22 changed Lean files.
- `git diff --cached --check` passed.

The larger existing `Clifford.SolderingIsomorphism` compatibility importer
also passed a separate direct source check after the extraction. That broader
diagnostic environment used upstream LeanArchitect revision
`468e8f58fb4ad6e6ad672a08da6d0d0531e95a97`, compatible with Lean 4.34, because
the existing manifest's Lean 4.28-era Architect source fails its metadata API
under Lean 4.34.1. This diagnostic checkout is not a dependency change in the
PR and is not used by the new 35-module audit closure.

The repository's actual path preflight command
`python3 tools/infra/ci_bootstrap.py paths` reported the absent/untracked Atlas
path and the uninitialized GIFT gitlink. Consequently the full root Lake and
publication gates are unverified. Once those authentic dependencies are
available, the repository-native target for this package is:

```sh
python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock \
  InfoGeometry.Twistor.RealConstructsAudit
```

The complete root gate is a separate check:

```sh
bash scripts/quality/post_build_gate.sh --full
```

## Real infinity and glide continuation

The native infinity, literal exterior-square and full glide actions, including
the retained sign on the genuine dual, are documented in
[REAL_INFINITY_CONTRACTION_REPAIR.md](REAL_INFINITY_CONTRACTION_REPAIR.md).
That continuation also repairs the legacy zero contraction implementation
using the same actual exterior operator already owned by the real
Kähler--Atiyah construction. Its verification is recorded separately there.
