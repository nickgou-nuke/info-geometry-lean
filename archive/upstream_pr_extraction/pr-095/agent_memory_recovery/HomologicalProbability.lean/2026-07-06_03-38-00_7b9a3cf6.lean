via the square-root embedding `pᵢ = xᵢ²` (see §1 `squareRootEmbedding`).
-/
structure MomentumMapProbabilityPacket where
  /-- Abstract projective state space (e.g. `Fin n → ℂ` or `ℂPⁿ⁻¹`). -/
  ProjectiveStateSpace : Type*
  /-- Abstract probability simplex (e.g. `Fin n → ℝ` satisfying `Σpᵢ = 1`). -/
  ProbabilitySimplex : Type*
  /-- Torus momentum map: projective state ↦ probability distribution. -/
  momentumMap : ProjectiveStateSpace → ProbabilitySimplex
  /-- Entropy functional on the simplex (metric shadow of spherical geometry). -/
  entropyFn : ProbabilitySimplex → ℝ

/--
**Concrete instance — §11 `momentMap` as a momentum-map packet.**

The `momentMap` and `entropyOfSpectrum` of §11 instantiate
`MomentumMapProbabilityPacket` for `n`-outcome quantum systems.
Mechanically verified: no `by rfl`.
-/
def momentumMapPacketFromFinDim (n : ℕ) : MomentumMapProbabilityPacket :=
  { ProjectiveStateSpace := Fin n → ℂ
    ProbabilitySimplex   := Fin n → ℝ
    momentumMap          := momentMap
    entropyFn            := entropyOfSpectrum }

/--
**Packet 24.2 — Homological measure packet.**

Gromov's replacement of numerical probability by cohomological support ideals.

For an observation map `f : StateSpace → ObservableSpace` and event `U ⊆ O`:
  `I(U) = ker(H*(X) → H*(X \ f⁻¹(U)))` (abstract cohomological support ideal).

Monotonicity: `U ⊆ V → I(U) ≤ I(V)` (larger events have larger support).
Cup product: `I(U) * I(V) ≤ I(U ∩ V)` (cup is compatible with intersection).

See §7's `SupportInvariantMeasureLike` for the related Prop-level version.
-/
structure HomologicalMeasurePacket where
  /-- State space of the physical system (configuration space). -/
  StateSpace : Type*
  /-- Observable space (outcome space). -/
  ObservableSpace : Type*
  /-- Cohomology / invariant algebra where support ideals live. -/
  CohomologyAlgebra : Type*
  /-- Observation map `f : StateSpace → ObservableSpace`. -/
  observableMap : StateSpace → ObservableSpace
  /-- Homological support-ideal assignment: observable event ↦ support ideal. -/
  supportIdeal : Set ObservableSpace → CohomologyAlgebra
  /-- Abstract order relation on the algebra (stands in for `≤`). -/
  idealLeq : CohomologyAlgebra → CohomologyAlgebra → Prop
  /-- Abstract multiplication on the algebra (stands in for cup product). -/
  idealMul : CohomologyAlgebra → CohomologyAlgebra → CohomologyAlgebra
  /-- Monotonicity: larger observable events have larger support ideals. -/
  mono : ∀ U V : Set ObservableSpace,
    U ⊆ V → idealLeq (supportIdeal U) (supportIdeal V)
  /-- Cup product axiom: `I(U) * I(V) ≤ I(U ∩ V)`. -/
  cup_intersection : ∀ U V : Set ObservableSpace,
    idealLeq (idealMul (supportIdeal U) (supportIdeal V)) (supportIdeal (U ∩ V))

/--
**Packet 24.3 — Moving-ball configuration packet.**

Small balls (radius `ε`) moving in a manifold.  Varying the radius `ε` gives
a filtered space whose homology measures packing / covering complexity.

`configurationSpace ε` is the space of `ParticleNumber` balls with exclusion
radius `ε` in the manifold.  Gromov's key point: the homology of the
configuration space (as a function of `ε`) detects volume constraints on cycles.
-/
structure MovingBallConfigurationPacket where
  /-- The ambient manifold (or metric space). -/
  Manifold : Type*
  /-- Number of moving balls (particles). -/
  ParticleNumber : ℕ
  /-- Radius parameter type (e.g. `{ε : ℝ // 0 < ε}` or abstract). -/
  RadiusParameter : Type*
  /-- Filtered configuration space: `ParticleNumber` balls with radius `ε`. -/
  configurationSpace : RadiusParameter → Type*
  /-- Full (unfiltered) configuration space (limit as `ε → 0`). -/
  baseConfigSpace : Type*
  /-- Inclusion of `ε`-filtered configurations into the base. -/
  inclusionInBase : ∀ ε : RadiusParameter, configurationSpace ε → baseConfigSpace

/--
**Packet 24.4 — Cycle-volume spectrum packet.**

The volume filtration on the space of `k`-cycles `𝒵_k(M)` gives a
homological spectrum:
  `λ(α) = inf { V | α detected in 𝒵_k^{≤V}(M) }`.

For `k = n-1` (hypersurfaces), the sorted spectral values are the *p*-widths
`ωₚ(M)` (Gromov–Guth volume spectrum; Liokumovich–Marques–Neves 2018).

The `spectralVal_eq` field connects to the `spectralValue` definition of §8.
-/
structure CycleVolumeSpectrumPacket where
  /-- The ambient manifold. -/
  Manifold : Type*
  /-- Homology class type (e.g. `H_k(M, ℤ)` or an abstract class type). -/
  HomologyClass : Type*
  /-- The cycle space `𝒵_k(M)`. -/
  CycleSpace : Type*
  /-- Volume functional on cycles. -/
  cycleVolume : CycleSpace → ℝ
  /-- Detection predicate: `detected V α` iff class `α` first appears in `𝒵^{≤V}`. -/
  detected : ℝ → HomologyClass → Prop
  /-- Spectral value: infimum volume threshold at which `α` is detected. -/
  spectralVal : HomologyClass → ℝ
  /-- Compatibility: spectral value is the infimum of the detection threshold set. -/
  spectralVal_eq : ∀ α : HomologyClass,
    spectralVal α = sInf { V : ℝ | detected V α }

/--
**Theorem 24.4a — Cycle-spectrum packet agrees with §8 `spectralValue`.**

The `spectralVal` of a `CycleVolumeSpectrumPacket` equals the `spectralValue`
of §8 (mechanically verified directly from the `spectralVal_eq` axiom).
-/
theorem cycleSpectrumPacket_spectralVal_eq
    (pkt : CycleVolumeSpectrumPacket) (α : pkt.HomologyClass) :