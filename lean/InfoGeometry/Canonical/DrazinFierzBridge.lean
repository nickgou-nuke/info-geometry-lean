import Mathlib.Tactic
import InfoGeometry.Meta.Architecture
import InfoGeometry.Meta.SocketTarget

/-!
# Drazin--Fierz bridge

Böttcher--Spitkovsky-style two-projection socket for Drazin-stable Fierz
readouts, stated in expectation-only form.

This file is a local operator chart, not a theorem that two projections
construct a type-III factor.  The two-projection algebra supplies a fiber
matrix `Φ_A(t)`.  Physical observables are expectation values after Drazin
filtering, not traces.

The theorem-safe dictionary is:

```text
two projection chart W*(P,Q)
  -> fiber matrix Φ_A(t)
  -> strata Δ0, Δ10, Δ11, Δ2
  -> Drazin separation criterion
  -> model-supplied Fierz readout
```

Any statement that a Drazin-stable fiber lands on a Fierz quadric is explicitly
a compatibility-assumption readout.
-/

noncomputable section

namespace InfoGeometry.Canonical.DrazinFierzBridge

open scoped BigOperators
open MeasureTheory

/-! ## 1. Trace-free Böttcher--Spitkovsky fiber matrix -/

/--
Generic expectation state.  This is the physical readout primitive in the
type-III-compatible lane.

It is intentionally not assumed to be tracial: there is no field requiring
`expect (a * b) = expect (b * a)`.
-/
@[rep_depth operator]
structure ExpectationState
    (Obs : Type*)
    [One Obs]
    [Mul Obs]
    [Star Obs]
    [AddCommMonoid Obs]
    [SMul ℂ Obs] where
  expect : Obs → ℂ
  map_add :
    ∀ a b : Obs,
      expect (a + b) = expect a + expect b
  map_smul :
    ∀ z : ℂ, ∀ a : Obs,
      expect (z • a) = z * expect a
  unital :
    expect 1 = 1
  positive_re :
    ∀ a : Obs,
      0 ≤ (expect (star a * a)).re
  positive_im :
    ∀ a : Obs,
      (expect (star a * a)).im = 0

/-- A `2 × 2` complex Böttcher--Spitkovsky fiber. -/
@[rep_depth operator]
abbrev FiberMatrix :=
  Matrix (Fin 2) (Fin 2) ℂ

/--
The trace-free Böttcher--Spitkovsky fiber representation.

In the paper the entries are essentially bounded complex functions on the
spectrum of the relative-position operator `H`.  This socket keeps the domain
as `ℝ`; spectral support and spectral measure are supplied separately.
-/
@[rep_depth operator]
abbrev BSExpectationPhi := ℝ → FiberMatrix

namespace BSExpectationPhi

abbrev fiber (Φ : BSExpectationPhi) : ℝ → FiberMatrix :=
  Φ

variable (Φ : BSExpectationPhi)

/-- Zero fiber stratum predicate. -/
@[rep_depth operator]
def IsZeroFiber (t : ℝ) : Prop :=
  Φ.fiber t = 0

/-- Nilpotent noise fiber: nonzero and square-zero. -/
@[rep_depth operator]
def IsNilpotentNoiseFiber (t : ℝ) : Prop :=
  Φ.fiber t ≠ 0 ∧
  Φ.fiber t * Φ.fiber t = 0

/-- Invertible fiber, stated by an explicit two-sided inverse. -/
@[rep_depth operator]
def IsInvertibleFiber (t : ℝ) : Prop :=
  ∃ N : FiberMatrix,
    Φ.fiber t * N = 1 ∧
    N * Φ.fiber t = 1

/--
Stable rank-one fiber, stated without trace.

Instead of using `tr Φ(t) ≠ 0`, this asks for a nonzero scalar `λ` satisfying
`Φ(t)^2 = λ • Φ(t)`.
-/
@[rep_depth operator]
def IsStableRankOneFiber (t : ℝ) : Prop :=
  Φ.fiber t ≠ 0 ∧
  ¬ Φ.IsInvertibleFiber t ∧
  ∃ lam : ℂ,
    lam ≠ 0 ∧
    Φ.fiber t * Φ.fiber t = lam • Φ.fiber t

/-- Zero stratum `Δ₀`. -/
@[rep_depth operator]
def Delta0 (σH : Set ℝ) : Set ℝ :=
  {t | t ∈ σH ∧ Φ.IsZeroFiber t}

/-- Nilpotent noise stratum `Δ₁₀`. -/
@[rep_depth operator]
def Delta10 (σH : Set ℝ) : Set ℝ :=
  {t | t ∈ σH ∧ Φ.IsNilpotentNoiseFiber t}

/-- Stable rank-one stratum `Δ₁₁`, without trace. -/
@[rep_depth operator]
def Delta11 (σH : Set ℝ) : Set ℝ :=
  {t | t ∈ σH ∧ Φ.IsStableRankOneFiber t}

/-- Invertible rank-two stratum `Δ₂`. -/
@[rep_depth operator]
def Delta2 (σH : Set ℝ) : Set ℝ :=
  {t | t ∈ σH ∧ Φ.IsInvertibleFiber t}

end BSExpectationPhi

/-! ## 2. Drazin separation criterion -/

/--
Essential separation from zero on a spectral stratum.

`νH` is the spectral measure associated with the relative-position operator.
This is a measure-theoretic socket; no spectral theorem is proved here.
-/
@[rep_depth operator]
def EssSeparatedFromZeroOn
    (νH : Measure ℝ)
    (S : Set ℝ)
    (f : ℝ → ℂ) : Prop :=
  ∃ ε : ℝ,
    0 < ε ∧
    ∀ᵐ t ∂νH, t ∈ S → ε ≤ ‖f t‖

namespace BSExpectationPhi

/--
Trace-free Drazin data for the Böttcher--Spitkovsky fiber.

`lambdaRankOne` is the stable scalar satisfying `Φ² = λΦ` on the stable
rank-one stratum.  No fiber trace is used.
-/
@[rep_depth operator]
structure NoTraceDrazinData
    (Φ : BSExpectationPhi)
    (νH : Measure ℝ)
    (σH : Set ℝ) where
  drazinFiber : ℝ → FiberMatrix
  lambdaRankOne : ℝ → ℂ
  rankOneLaw :
    ∀ᵐ t ∂νH,
      t ∈ Φ.Delta11 σH →
        Φ.fiber t * Φ.fiber t =
          lambdaRankOne t • Φ.fiber t
  lambdaSeparated :
    EssSeparatedFromZeroOn νH
      (Φ.Delta11 σH)
      lambdaRankOne
  zeroLaw :
    ∀ᵐ t ∂νH,
      t ∈ Φ.Delta0 σH →
        drazinFiber t = 0
  nilpotentLaw :
    ∀ᵐ t ∂νH,
      t ∈ Φ.Delta10 σH →
        drazinFiber t = 0
  stableRankOneLaw :
    ∀ᵐ t ∂νH,
      t ∈ Φ.Delta11 σH →
        drazinFiber t =
          ((lambdaRankOne t)⁻¹ * (lambdaRankOne t)⁻¹) • Φ.fiber t
  invertibleLaw :
    ∀ᵐ t ∂νH,
      t ∈ Φ.Delta2 σH →
        ∃ invM : FiberMatrix,
          Φ.fiber t * invM = 1 ∧
          invM * Φ.fiber t = 1 ∧
          drazinFiber t = invM

end BSExpectationPhi

/-! ## 3. Drazin-stable Fierz readout sockets -/

/--
Model-specific map extracting normalized Fierz coordinates from the stable
Böttcher--Spitkovsky data.
-/
@[rep_depth operator]
def DrazinFierzReadout
    (NormalizedFierzCoordinates : Type*) : Type _ :=
  BSExpectationPhi → Measure ℝ → Set ℝ → NormalizedFierzCoordinates

namespace DrazinFierzReadout

/-- The normalized-coordinate map carried by the direct readout owner. -/
abbrev readout
    {NormalizedFierzCoordinates : Type*}
    (R : DrazinFierzReadout NormalizedFierzCoordinates) :
    BSExpectationPhi → Measure ℝ → Set ℝ → NormalizedFierzCoordinates :=
  R

/-- Construct a normalized-coordinate readout. -/
def mk
    {NormalizedFierzCoordinates : Type*}
    (R : BSExpectationPhi → Measure ℝ → Set ℝ → NormalizedFierzCoordinates) :
    DrazinFierzReadout NormalizedFierzCoordinates :=
  R

end DrazinFierzReadout

/--
Readback: any supplied readout produces a coordinate value on Drazin-stable
two-projection data.
-/
@[rep_depth operator]
theorem drazin_stable_fierz_readout
    {NormalizedFierzCoordinates : Type*}
    (R : DrazinFierzReadout NormalizedFierzCoordinates)
    (Φ : BSExpectationPhi)
    (νH : Measure ℝ)
    (σH : Set ℝ)
    (_hD : BSExpectationPhi.NoTraceDrazinData Φ νH σH) :
    ∃ x : NormalizedFierzCoordinates,
      x = R.readout Φ νH σH :=
  ⟨R.readout Φ νH σH, rfl⟩

/--
Trace-free expectation Fierz readout.

The physical coordinate is an expectation value of the Drazin-filtered
observable, not a trace.
-/
@[rep_depth operator]
inductive FierzChannel where
  | scalar
  | phase
  | metric
  | area
  deriving DecidableEq, Fintype

/-- Family of expectation states indexed by Fierz channel. -/
@[rep_depth operator]
def ExpectationFierzReadout
    (Obs : Type*)
    [One Obs]
    [Mul Obs]
    [Star Obs]
    [AddCommMonoid Obs]
    [SMul ℂ Obs] : Type _ :=
  FierzChannel → ExpectationState Obs

namespace ExpectationFierzReadout

/-- The channel-indexed expectation state family. -/
abbrev state
    {Obs : Type*}
    [One Obs] [Mul Obs] [Star Obs] [AddCommMonoid Obs] [SMul ℂ Obs]
    (R : ExpectationFierzReadout Obs) : FierzChannel → ExpectationState Obs :=
  R

/-- Construct an expectation Fierz readout. -/
def mk
    {Obs : Type*}
    [One Obs] [Mul Obs] [Star Obs] [AddCommMonoid Obs] [SMul ℂ Obs]
    (R : FierzChannel → ExpectationState Obs) : ExpectationFierzReadout Obs :=
  R

end ExpectationFierzReadout

/-- A Drazin-filtered observable, represented by its Drazin inverse/filter output. -/
@[rep_depth operator]
def DrazinFilteredObservable (Obs : Type*) : Type _ :=
  Obs

namespace DrazinFilteredObservable

/-- The filtered observable carried by the direct owner. -/
abbrev AD {Obs : Type*} (X : DrazinFilteredObservable Obs) : Obs :=
  X

/-- Construct a filtered observable. -/
def mk {Obs : Type*} (X : Obs) : DrazinFilteredObservable Obs :=
  X

end DrazinFilteredObservable

/-- Physical Fierz coordinate `φ_ch(Aᴰ)`. -/
@[rep_depth operator]
def expectationFierzCoordinate
    {Obs : Type*}
    [One Obs]
    [Mul Obs]
    [Star Obs]
    [AddCommMonoid Obs]
    [SMul ℂ Obs]
    (R : ExpectationFierzReadout Obs)
    (X : DrazinFilteredObservable Obs)
    (ch : FierzChannel) : ℂ :=
  (R.state ch).expect X.AD

/-! ## 4. Expectation-only channel maps -/

/--
Channel map extracting the observable assigned to a Fierz channel.

The coordinate is obtained only after applying an expectation state.
-/
@[rep_depth operator]
def FierzChannelMap (Obs : Type*) : Type _ :=
  FierzChannel → Obs → Obs

namespace FierzChannelMap

/-- The channel action carried by the direct map owner. -/
abbrev channel {Obs : Type*} (C : FierzChannelMap Obs) : FierzChannel → Obs → Obs :=
  C

/-- Construct a Fierz channel map. -/
def mk {Obs : Type*} (C : FierzChannel → Obs → Obs) : FierzChannelMap Obs :=
  C

end FierzChannelMap

/--
The physical Fierz coordinate `φ(C_ch(Aᴰ))`.
-/
@[rep_depth operator]
def expectationChannelFierzCoordinate
    {Obs : Type*}
    [One Obs]
    [Mul Obs]
    [Star Obs]
    [AddCommMonoid Obs]
    [SMul ℂ Obs]
    (φ : ExpectationState Obs)
    (C : FierzChannelMap Obs)
    (X : DrazinFilteredObservable Obs)
    (ch : FierzChannel) : ℂ :=
  φ.expect (C.channel ch X.AD)

/--
All physical Fierz coordinates are expectation values of Drazin-stabilized
channel observables.
-/
@[rep_depth operator]
def expectationFierzVector
    {Obs : Type*}
    [One Obs]
    [Mul Obs]
    [Star Obs]
    [AddCommMonoid Obs]
    [SMul ℂ Obs]
    (φ : ExpectationState Obs)
    (C : FierzChannelMap Obs)
    (X : DrazinFilteredObservable Obs) :
    FierzChannel → ℂ :=
  fun ch => expectationChannelFierzCoordinate φ C X ch

/-- Normalized expectation-valued Fierz coordinates. -/
@[rep_depth operator]
abbrev NormalizedFierzCoordinates := FierzChannel → ℂ

namespace NormalizedFierzCoordinates

abbrev coord (x : NormalizedFierzCoordinates) : FierzChannel → ℂ :=
  x

end NormalizedFierzCoordinates

/-- Model-specific residual for a normalized Fierz coordinate packet. -/
@[rep_depth operator]
abbrev FierzResidual := NormalizedFierzCoordinates → ℝ

namespace FierzResidual

abbrev residual (r : FierzResidual) : NormalizedFierzCoordinates → ℝ :=
  r

end FierzResidual

/--
Compatibility assumption connecting trace-free Drazin-stable two-projection
fibers to a chosen Fierz residual.

This is not derived from the Böttcher--Spitkovsky criterion alone.
-/
@[rep_depth operator]
structure DrazinFierzCompatibilityAssumption
    (NormalizedFierzCoordinates : Type*) where
  residual : NormalizedFierzCoordinates → ℝ
  readout :
    BSExpectationPhi → Measure ℝ → Set ℝ → NormalizedFierzCoordinates
  sound :
    ∀ (Φ : BSExpectationPhi) (νH : Measure ℝ) (σH : Set ℝ),
      BSExpectationPhi.NoTraceDrazinData Φ νH σH →
      residual (readout Φ νH σH) = 0

/--
Assumption-derived readback: a compatible Drazin/Fierz readout lands on the
chosen residual-zero quadric.
-/
@[rep_depth operator]
theorem drazin_filter_lands_on_fierz_quadric
    {NormalizedFierzCoordinates : Type*}
    (C : DrazinFierzCompatibilityAssumption NormalizedFierzCoordinates)
    (Φ : BSExpectationPhi)
    (νH : Measure ℝ)
    (σH : Set ℝ)
    (hD : BSExpectationPhi.NoTraceDrazinData Φ νH σH) :
    C.residual (C.readout Φ νH σH) = 0 :=
  C.sound Φ νH σH hD

/-! ## 5. Strong alternating-projection limit socket -/

/-- Strong operator convergence of bounded-operator sequences. -/
@[rep_depth operator]
def StrongTendsto
    {E : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℂ E]
    (T : ℕ → E →L[ℂ] E)
    (Tinf : E →L[ℂ] E) : Prop :=
  ∀ x : E, Filter.Tendsto (fun n => T n x) Filter.atTop (nhds (Tinf x))

/--
Assumption packet for the strong alternating-projection limit.

The topology is strong operator convergence, not norm convergence.
-/
@[rep_depth operator]
structure AlternatingProjectionStrongLimitAssumption
    (E : Type*)
    [NormedAddCommGroup E]
    [NormedSpace ℂ E] where
  step : ℕ → E →L[ℂ] E
  limit : E →L[ℂ] E
  strong_limit :
    StrongTendsto step limit

/-- Readback of the supplied strong alternating-projection limit. -/
@[rep_depth operator]
theorem alternating_projection_strong_limit
    {E : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℂ E]
    (A : AlternatingProjectionStrongLimitAssumption E) :
    StrongTendsto A.step A.limit :=
  A.strong_limit

/-! ## 6. Expectation-correlation Birkhoff socket -/

/-- A stochastic channel observable sampled along discrete time. -/
@[rep_depth projective]
abbrev CenteredChannel :=
  ℕ → ℝ

/-- Cesàro mean of a channel observable through time `N`. -/
@[rep_depth projective]
noncomputable def channelCesaroMean
    (X : CenteredChannel)
    (N : ℕ) : ℝ :=
  (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N, X n

/-- Cesàro second moment of a channel observable through time `N`. -/
@[rep_depth projective]
noncomputable def channelCesaroSecondMoment
    (X : CenteredChannel)
    (N : ℕ) : ℝ :=
  (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N, (X n) ^ 2

/-- A channel is centered when its Cesàro mean converges to zero. -/
@[rep_depth projective]
def IsCesaroMeanZero (X : CenteredChannel) : Prop :=
  Filter.Tendsto (channelCesaroMean X) Filter.atTop (nhds 0)

/-- A centered channel has normalized variance when its Cesàro second moment
converges to one. -/
@[rep_depth projective]
def HasNormalizedCesaroVariance (X : CenteredChannel) : Prop :=
  Filter.Tendsto (channelCesaroSecondMoment X) Filter.atTop (nhds 1)

/--
Expectation-based nonnegative correlation energy.

The intended source is a nonnegative channel such as
`|φ(Zᵢ Z'ⱼ)|²`.  No trace Gram matrix is used.
-/
@[rep_depth projective]
structure CorrelationEnergy4 where
  E : Matrix (Fin 4) (Fin 4) ℝ
  nonneg : ∀ i j, 0 ≤ E i j

/--
Expectation-based correlation energy.

The order is fixed as `φ(Zᵢ* Wⱼ)`.  Since `φ` is not assumed tracial, this
order is part of the data.
-/
@[rep_depth projective]
def expectationCorrelationEnergy
    {Obs : Type*}
    [One Obs]
    [Mul Obs]
    [Star Obs]
    [AddCommMonoid Obs]
    [SMul ℂ Obs]
    (φ : ExpectationState Obs)
    (Z W : Fin 4 → Obs) :
    Matrix (Fin 4) (Fin 4) ℝ :=
  fun i j => ‖φ.expect (star (Z i) * W j)‖ ^ 2

/-- Bistochastic `4 × 4` real matrix. -/
@[rep_depth projective]
structure Bistochastic4 where
  M : Matrix (Fin 4) (Fin 4) ℝ
  nonneg : ∀ i j, 0 ≤ M i j
  row_sum :
    ∀ i, (Finset.univ.sum (fun j : Fin 4 => M i j)) = 1
  col_sum :
    ∀ j, (Finset.univ.sum (fun i : Fin 4 => M i j)) = 1

/-- Permutation matrix of a permutation of four channels. -/
@[rep_depth projective]
def permutationMatrix4 (π : Equiv.Perm (Fin 4)) :
    Matrix (Fin 4) (Fin 4) ℝ :=
  fun i j => if π i = j then 1 else 0

/-- Birkhoff decomposition socket for a bistochastic `4 × 4` matrix. -/
@[rep_depth projective]
structure BirkhoffDecomposition4
    (B : Bistochastic4) where
  weights : Equiv.Perm (Fin 4) → ℝ
  nonneg : ∀ π, 0 ≤ weights π
  total_weight :
    Finset.univ.sum (fun π : Equiv.Perm (Fin 4) => weights π) = 1
  reconstruct :
    B.M =
      Finset.univ.sum
        (fun π : Equiv.Perm (Fin 4) =>
          weights π • permutationMatrix4 π)

end InfoGeometry.Canonical.DrazinFierzBridge
