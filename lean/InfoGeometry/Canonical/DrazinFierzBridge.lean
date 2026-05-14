import Mathlib
import InfoGeometry.Meta.Architecture

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
structure BSExpectationPhi where
  fiber : ℝ → FiberMatrix

namespace BSExpectationPhi

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
structure DrazinFierzReadout
    (NormalizedFierzCoordinates : Type*) where
  readout :
    BSExpectationPhi → Measure ℝ → Set ℝ → NormalizedFierzCoordinates

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
structure ExpectationFierzReadout
    (Obs : Type*)
    [One Obs]
    [Mul Obs]
    [Star Obs]
    [AddCommMonoid Obs]
    [SMul ℂ Obs] where
  state : FierzChannel → ExpectationState Obs

/-- A Drazin-filtered observable, represented by its Drazin inverse/filter output. -/
@[rep_depth operator]
structure DrazinFilteredObservable
    (Obs : Type*) where
  AD : Obs

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
structure FierzChannelMap
    (Obs : Type*) where
  channel : FierzChannel → Obs → Obs

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
structure NormalizedFierzCoordinates where
  coord : FierzChannel → ℂ

/-- Model-specific residual for a normalized Fierz coordinate packet. -/
@[rep_depth operator]
structure FierzResidual where
  residual : NormalizedFierzCoordinates → ℝ

/--
Complete expectation-only Fierz socket.

No physical trace exists in this interface.  The residual law is an explicit
compatibility field, not a theorem derived from expectation alone.
-/
@[rep_depth operator]
structure ExpectationOnlyFierzSocket
    (Obs : Type*)
    [One Obs]
    [Mul Obs]
    [Star Obs]
    [AddCommMonoid Obs]
    [SMul ℂ Obs] where
  state :
    ExpectationState Obs
  channels :
    FierzChannelMap Obs
  drazin :
    Obs → DrazinFilteredObservable Obs
  residual :
    FierzResidual
  coords :
    Obs → NormalizedFierzCoordinates
  coords_eq_expectation :
    ∀ A ch,
      (coords A).coord ch =
        expectationChannelFierzCoordinate
          state
          channels
          (drazin A)
          ch
  drazin_sound :
    ∀ A,
      residual.residual (coords A) = 0

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

/-- Centered stochastic channel variable. -/
@[rep_depth projective]
structure CenteredChannel where
  value : ℕ → ℝ
  meanZero : Prop
  normalizedVariance : Prop

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

/--
Correlation-energy matrix together with a normalized bistochastic socket and a
chosen Birkhoff decomposition.
-/
@[rep_depth projective]
structure ExpectationBirkhoffSocket
    {Obs : Type*}
    [One Obs]
    [Mul Obs]
    [Star Obs]
    [AddCommMonoid Obs]
    [SMul ℂ Obs]
    (φ : ExpectationState Obs)
    (Z W : Fin 4 → Obs) where
  rawEnergy : Matrix (Fin 4) (Fin 4) ℝ
  rawEnergy_eq :
    rawEnergy = expectationCorrelationEnergy φ Z W
  normalized : Bistochastic4
  decomposition : BirkhoffDecomposition4 normalized

/--
Explicit representation socket from a Hurwitz-unit-like set to permutations.

This avoids identifying order-24 structures merely by cardinality.
-/
@[rep_depth projective]
structure HurwitzToPermutationSocket where
  HurwitzUnit : Type*
  mul : HurwitzUnit → HurwitzUnit → HurwitzUnit
  toPerm : HurwitzUnit → Equiv.Perm (Fin 4)
  respects_mul : Prop

end InfoGeometry.Canonical.DrazinFierzBridge
