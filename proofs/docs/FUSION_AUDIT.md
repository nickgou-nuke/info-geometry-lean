# Fusion Audit: `auto` vs `info-geometry-lean`

Date: 2026-06-10

This repository is now best treated as a thin experimental/frontier layer over
the larger local development at `/home/goutev/info-geometry-lean`.

## Build Status

The local `proofs` package builds with the fused root set:

```text
lake build
Build completed successfully (8057 jobs).
```

The promoted fusion roots include:

```text
AnomalousKMSFlow
ConnesSpectralAction
CuntzKTheoryPairing
KasparovKreinCategory
HilbertPolyaBivariant
DiracColimit
ConcreteCliffordDiracTower
PrimonCuntzTower
ZetaSpectralBridge
KreinDeterminantAnalyticity
KanCayley
DeterminantSupergrading
KANLogDetUnification
IwasawaKUnification
KleinBottleSymmetry
KleinFourAnomalyCancellation
KleinBottleKANCoordinates
KleinParafermionCohomology
PrimonSuperThermodynamics
ZetaCoordinateSymmetry
UnifiedAnomalyArchitecture
tomita_kms_v4
```

An audit of these promoted files found no active `sorry`, `admit`, or top-level
axiom declarations. One hit is explanatory prose in
`KasparovKreinCategory.lean`.

## Complementarity

The larger repository supplies the proved geometric/operator substrate:

```text
InfoGeometry.Clifford.Spacetime
InfoGeometry.Clifford.Soldering
InfoGeometry.Clifford.ChiralBasis
InfoGeometry.Quantum.Fock
InfoGeometry.Quantum.SplitTrialityKernel
InfoGeometry.Quantum.SplitTrialityFockBridge
InfoGeometry.Canonical.BogoliubovFockSuper
InfoGeometry.Canonical.SuperSouriauFermionGasBridge
InfoGeometry.Canonical.ModularSpinorBridge
InfoGeometry.Krein.*
InfoGeometry.Canonical.AQFTOperatorInterface
```

Concrete local examples in `info-geometry-lean` include:

```text
det_soldering
det_soldering_eq_q22
uPlus_is_null
uMinus_is_null
creationOp
annihilationOp
creation_eq_plus_projector
annihilation_eq_minus_projector
creation_annihilation_orthogonal
vectorToLeftSpinor_nilpotent
vectorToRightSpinor_nilpotent
anticommutator_annihilation_creation
```

The smaller `auto` repository complements this by providing frontier adapters:

```text
determinant-sector analyticity over concrete 2x2 transfer matrices
K/A/N phase-scale-boundary unification over concrete 2x2 blocks
trace-zero `sl(2,R)` K/A/N infinitesimal generators
Klein-bottle symmetry axes `J`, `ε`, and nilpotent cross-cap `N`
Klein cross-cap parafermion holonomy obstruction
determinant-sign supergrading for the real doubled atom
finite anomaly/KMS trace bookkeeping
Connes spectral-action lower-bound wrappers
Cuntz/K-theory collapse toy interfaces
Kasparov categorical firewall statements
finite Dirac colimit certificates
primon/Cuntz tower interfaces
zeta spectral bridge certificates
finite Primon/Cuntz Dirac stages with KAN determinant/log bridge
critical-coordinate symmetry and axis-lock lemmas
unified anomaly architecture theorem
```

## Important Correction

The pasted `KreinDeterminantAnalyticity` variant with
`jacobi_formula` and `log_trace_formula` as axioms is not the local best form.
The local file `proofs/KreinDeterminantAnalyticity.lean` is stronger for this
repository: it proves concrete determinant closure, tensor closure, and
hyperbolic unit-determinant flow facts directly, without those axioms.

## Fusion Rule

Use `info-geometry-lean` as the substrate for heavy geometric facts.
Use `auto/proofs` as the compact bridge layer:

```text
proved substrate theorem
  -> thin local adapter
  -> finite/checkable synthesis theorem
  -> promoted Lake root only after build succeeds
```

Do not duplicate large substrate proofs here unless the local statement is a
strictly smaller concrete specialization.

## K/A/N Log-Det Bridge

`KANLogDetUnification.lean` records the local version of the
phase/scale/boundary unification:

```text
KPart θ  : compact phase block, det = 1
APart β  : logarithmic scale block, det = 1
NPart z  : unipotent boundary block, det = 1
NPart z - I : nilpotent boundary displacement, square = 0, det = 0
```

The real doubled atom is supplied by `DeterminantSupergrading.lean`:

```text
J and ε are determinant-odd.
K = Jε is determinant-even.
K² = -I.
```

The log-volume bridge is supplied by `KreinDeterminantAnalyticity.lean`:

```text
diag(exp θ, exp (-θ)) has determinant one and log-volume zero.
```

This is a concrete specialization of the larger `info-geometry-lean` operator
substrate, not a claim that a global KAN decomposition has been proved here for
all operators.

## Iwasawa Generator Layer

`IwasawaKUnification.lean` adds the infinitesimal real Lie-algebra layer:

```text
generatorK θ = [[0, θ], [-θ, 0]]
generatorA r = [[r/2, 0], [0, -r/2]]
generatorN x = [[0, x], [0, 0]]
```

The checked theorem is:

```text
trace(generatorK θ + generatorA r + generatorN x) = 0
```

with the additional concrete facts:

```text
generatorN x squared = 0
generatorK θ squared = diag(-θ², -θ²)
```

This is the local `sl(2,R)` trace-annihilation layer underlying the
determinant/log-volume story.

## Klein Bottle Coordinate Layer

`KleinBottleKANCoordinates.lean` records the symmetry-adapted coordinate axes:

```text
JAxis       = modular_j
epsilonAxis = chiralParity
NAxis x     = IwasawaKUnification.generatorN x
```

The checked coordinate package is:

```text
JAxis² = I
epsilonAxis² = I
NAxis x squared = 0
epsilonAxis * NAxis x * epsilonAxis = -NAxis x
det(NAxis x) = 0
```

It also proves the precise collapse condition:

```text
if epsilonAxis * NAxis x = NAxis x * epsilonAxis,
then NAxis x = 0.
```

So the cancellation statement is conditional: cross-cap oddness plus chiral
commutation forces the nilpotent anomaly to vanish over characteristic zero.

## Parafermion Cross-Cap Cohomology

`KleinParafermionCohomology.lean` records the finite holonomy obstruction:

```text
V4 invariance:        W = mirrorW
cross-cap reversal:  mirrorW = W^-1
therefore:           W^2 = 1
```

The checked consequence is that any nonzero global cross-cap holonomy lands in
the two torsion sectors:

```text
W = 1 or W = -1
```

It also proves the odd-order collapse for the common parafermion phases:

```text
q^5 = 1 and q = q^-1  => q = 1
q^3 = 1 and q = q^-1  => q = 1
```

Thus order-3 and order-5 parafermion phases can exist locally, but if they are
required to be global Klein cross-cap holonomies, the cross-cap projection
collapses them to the trivial bosonic class.

## Primon/Cuntz Finite-Stage Bridge

`PrimonCuntzTower.lean` now includes a bundled finite-stage bridge:

```text
primonCuntz_finite_stage_KAN_bridge
```

It records, for each finite stage `n`:

```text
D_n is self-adjoint
D_n commutes with the embedding emb n
det(K) = 1
det(N) = 1
log det(total KAN factor) = sum_i log(i+1)
```

This is the finite cutoff version of the Dirac/energy tower feeding the local
KAN determinant/log dictionary.

## Finite Mellin/Zeta Spectral Bridge

`ZetaSpectralBridge.lean` now contains a finite Mellin layer connecting the heat
trace language to the Dirichlet trace language:

```text
gammaNormalizedMellinMode s lam = exp(-s * log lam)
finitePrimonHeatTrace n s = finitePrimonMellinTrace n s
finitePrimonMellinTrace n s = finitePrimonDirichletTrace n s
```

The bundled theorem is:

```text
finitePrimonMellin_KAN_synthesis
```

It records that the finite heat trace, Gamma-normalized Mellin trace, finite
Dirichlet trace, and KAN log-determinant generator all use the same finite
Primon spectrum.  This is deliberately a finite spectral identity; it does not
assert the full improper-integral theorem
`∫₀∞ t^(s-1) exp(-lam*t) dt = Gamma(s) * lam^(-s)`.

The same file now also names the infinite real-doubled analyticity interface:

```text
InfiniteIwasawaAnalyticityLock
InfiniteIwasawaAnalyticityLock.infinite_iwasawa_analyticity_lock
```

Here "analyticity" means the algebraic Jacobi-Liouville lock
`det(flow) = 1 ↔ trace(H) = 0`.  The current theorem proves the consequence from
explicit zero-defect data.  The remaining work is to derive that zero-defect
field from the infinite Cuntz/Clifford/Zorn determinant cocycle.

`MellinHeatKernelBridge.lean` adds the assumption-explicit heat-kernel side:

```text
finite_mellin_heat_trace_bridge
finite_primon_heat_mellin_zeta_KAN_bridge
```

The first theorem says that a finite additive Mellin transform with atom formula
`mellin(atom_i) = Gamma(s) * spectralAtom_i(s)` sends the finite heat trace to
`Gamma(s)` times the finite spectral sum.  The second identifies that spectral
sum with the `ZetaSpectralBridge` finite Mellin trace and the existing KAN
log-determinant generator.

## Hurwitz Quaternion / Twisted Sector Layer

`HurwitzTwistedSector.lean` adds the finite quaternionic shifted-spectrum layer:

```text
HurwitzQuaternion.normSq_mul
finiteHurwitzZetaTrace_eq_shiftedDirichlet
finiteHurwitzZetaTrace_shift_one_eq_primon
hurwitzTrace_eq_hurwitzZeta
infiniteHurwitzTrace_mellin_bridge
finiteHurwitzCharacterCombination_add
finiteHurwitzCharacterCombination_smul
finiteHurwitzCharacterCombination_zero
hurwitz_twisted_sector_synthesis
```

The formal content is conservative:

```text
normSq(p*q) = normSq(p) * normSq(q)
finite Hurwitz shifted trace = finite shifted Dirichlet trace
shift a = 1 recovers the finite Primon Mellin trace
on Re(s)>1 the infinite shifted trace agrees with Mathlib Hurwitz zeta
finite character combinations are additive and scalar-linear
```

This gives a finite model for twisted boundary shifts, including the half-shift
sector `a = 1/2`, without asserting analytic continuation of the full Hurwitz
zeta function or a global E8/triality theorem.

`HurwitzQuaternionSpectrum.lean` adds the exact rational lattice version:

```text
IntegralLane / HalfIntegralLane
HurwitzQuaternion.sameLane
HurwitzQuaternion.normSq_conj
finite_mellin_compatibility
finiteHurwitzZetaTrace_eq_quantum_trace
infiniteHurwitzTrace_mellin_bridge
finiteHurwitzCharacterCombination_add
finiteHurwitzCharacterCombination_smul
hurwitz_quaternion_spectrum_synthesis
```

This keeps the Hurwitz order condition in exact arithmetic (`ℚ`) while reusing
the concrete Gamma-normalized Mellin atom from `ZetaSpectralBridge`.  The
half-integer sector is represented by `twistedSectorTrace N s`, the finite
shift `a = 1/2` model.
