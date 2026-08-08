import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Ring.Finset
import InfoGeometry.Canonical.ModularCoproductFlux
import InfoGeometry.Canonical.ModularHopfCoproductRules
import InfoGeometry.Canonical.NilpotentFluxVirasoroReadout
import InfoGeometry.Canonical.ModularNilpotentAutomorphism
import InfoGeometry.Canonical.SplitCliffordSourceWickVacuum
import InfoGeometry.Canonical.SplitCliffordSourceWickBaseExternalBridge
import InfoGeometry.Canonical.BekensteinBound
import InfoGeometry.External.Virasoro.VirasoroAlgebra

/-!
# Coproduct iteration, cross-flux readout, and Virasoro cocycle normalization

Finite algebraic bridge used to formalize the iterative-coproduct->cocycle idea:
* `liftFlux = N ⊗ 1 + 1 ⊗ N + N ⊗ N` under `N^2 = 0`
* only pairwise cross terms survive beyond linearized order
* accumulated pair contributions scale by the triangular count
* normalization recovers the standard Virasoro central density `m^3 - m`
No analytic limits are asserted.
-/

namespace InfoGeometry.Canonical.CoproductToVirasoroCocycleBridge

open scoped TensorProduct
open scoped BigOperators

open Finset
open InfoGeometry.Canonical.ModularCoproductFlux
open InfoGeometry.Canonical.SplitCliffordSourceWickBase
open InfoGeometry.Canonical.BekensteinBound
open InfoGeometry.Canonical.MoE
open InfoGeometry.Volume.ConnesCocycle

/-- Local concrete matrix carrier reused from the nilpotent automorphism owner. -/
abbrev M2R := InfoGeometry.Canonical.ModularNilpotentAutomorphism.M2R

noncomputable section

/-- Pairing weight for `n` split steps: `0 + 1 + ... + (n - 1)`. -/
def pairContributionWeight : ℕ → ℝ
  | 0 => 0
  | n + 1 => pairContributionWeight n + n

@[simp] theorem pairContributionWeight_zero : pairContributionWeight 0 = 0 := by
  rfl

@[simp] theorem pairContributionWeight_succ (n : ℕ) :
    pairContributionWeight (n + 1) = pairContributionWeight n + n := by
  rfl

/-- Effective central coefficient after `n` pairwise defect layers. -/
def iteratedCentralCoefficient (n : ℕ) (c : ℝ) : ℝ :=
  pairContributionWeight n * c

lemma iteratedCentralCoefficient_succ (n : ℕ) (c : ℝ) :
    iteratedCentralCoefficient (n + 1) c = iteratedCentralCoefficient n c + (n : ℝ) * c := by
  unfold iteratedCentralCoefficient
  simp [pairContributionWeight_succ]
  ring

/-- Resonant cocycle profile: `((m^3 - m)/12) * c` with support on `m + n = 0`. -/
def virasoroCocycleDensity (c : ℝ) (m n : Int) : ℝ :=
  if m + n = 0 then (c / 12) * (((m : ℝ)^3) - (m : ℝ)) else 0

@[simp] theorem virasoroCocycleDensity_eq_zero (c : ℝ) {m n : Int} (h : m + n ≠ 0) :
    virasoroCocycleDensity c m n = 0 := by
  simp [virasoroCocycleDensity, h]

@[simp] theorem virasoroCocycleDensity_eq_resonant (c : ℝ) {m n : Int} (h : m + n = 0) :
    virasoroCocycleDensity c m n = (c / 12) * (((m : ℝ)^3) - (m : ℝ)) := by
  simp [virasoroCocycleDensity, h]

/-- Accumulated cocycle profile after `n` iterative layers. -/
def iteratedVirasoroCocycle (n : ℕ) (c : ℝ) (m n' : Int) : ℝ :=
  virasoroCocycleDensity (iteratedCentralCoefficient n c) m n'

@[simp] theorem iteratedVirasoroCocycle_zero (c : ℝ) (m n : Int) :
    iteratedVirasoroCocycle 0 c m n = 0 := by
  simp [iteratedVirasoroCocycle, iteratedCentralCoefficient, pairContributionWeight_zero, virasoroCocycleDensity]

lemma iteratedVirasoroCocycle_succ (k : ℕ) (c : ℝ) (m n : Int) :
    iteratedVirasoroCocycle (k + 1) c m n =
      iteratedVirasoroCocycle k c m n +
        (if m + n = 0 then ((k : ℝ) * c / 12) * (((m : ℝ)^3) - (m : ℝ)) else 0) := by
  by_cases h : m + n = 0
  · simp [iteratedVirasoroCocycle, virasoroCocycleDensity, iteratedCentralCoefficient_succ, h]
    ring
  · simp [iteratedVirasoroCocycle, virasoroCocycleDensity, h]

@[simp] theorem pairContributionWeight_two : pairContributionWeight 2 = 1 := by
  norm_num [pairContributionWeight]

@[simp] theorem iteratedVirasoroCocycle_two (c : ℝ) (m n : Int) :
    iteratedVirasoroCocycle 2 c m n = virasoroCocycleDensity c m n := by
  rw [iteratedVirasoroCocycle, iteratedCentralCoefficient]
  rw [pairContributionWeight_two]
  simp [virasoroCocycleDensity]

/-- Resonant two-step coefficient is exactly the Virasoro polynomial
`(m^3 - m) / 12` at `n = -m`. -/
theorem iteratedVirasoroCocycle_two_resonant (c : ℝ) (m : Int) :
    iteratedVirasoroCocycle 2 c m (-m) = (c / 12) * (((m : ℝ)^3) - (m : ℝ)) := by
  rw [iteratedVirasoroCocycle_two, virasoroCocycleDensity_eq_resonant (c := c) (m := m) (n := -m) (by simp)]

/-- Readout data attached to a nilpotent cross-flux seed.

The carrier is the ordinary product of the seed and its linear readout; the
subtype predicate contains exactly the two required laws. -/
abbrev NilpotentFluxReadout (A : Type*) [Ring A] [Algebra ℝ A] :=
  {p : A × (A ⊗[ℝ] A →ₗ[ℝ] ℝ) //
    p.1 * p.1 = 0 ∧ p.2 (crossFlux (R := ℝ) p.1) = 1}

namespace NilpotentFluxReadout

variable {A : Type*} [Ring A] [Algebra ℝ A]

abbrev N (S : NilpotentFluxReadout A) : A := S.1.1

abbrev ρ (S : NilpotentFluxReadout A) : A ⊗[ℝ] A →ₗ[ℝ] ℝ := S.1.2

theorem hN (S : NilpotentFluxReadout A) : S.N * S.N = 0 := S.2.1

theorem crossRead (S : NilpotentFluxReadout A) :
    S.ρ (crossFlux (R := ℝ) S.N) = 1 := S.2.2

end NilpotentFluxReadout

/-- Under a linear readout, `liftFlux^2` contributes exactly twice the cross term. -/
theorem liftFlux_sq_readout
    (A : Type*) [Ring A] [Algebra ℝ A]
    (S : NilpotentFluxReadout A) :
    S.ρ (liftFlux (R := ℝ) S.N * liftFlux (R := ℝ) S.N) = 2 := by
  calc
    S.ρ (liftFlux (R := ℝ) S.N * liftFlux (R := ℝ) S.N)
        = S.ρ ((2 : ℝ) • (S.N ⊗ₜ[ℝ] S.N : A ⊗[ℝ] A)) := by
          rw [liftFlux_sq (R := ℝ) (N := S.N) S.hN]
    _ = (2 : ℝ) * S.ρ (S.N ⊗ₜ[ℝ] S.N : A ⊗[ℝ] A) := by simp
    _ = (2 : ℝ) * S.ρ (crossFlux (R := ℝ) S.N) := by simp [crossFlux]
    _ = 2 := by simp [S.crossRead]

/-- If the primitive part is killed by the readout, only the cross term survives in `hatDeltaPhi`. -/
theorem centeredCoproduct_readout_picks_cross
    (A : Type*) [Ring A] [Algebra ℝ A]
    (S : NilpotentFluxReadout A)
    (hPrimitive : S.ρ (primitiveFlux (R := ℝ) S.N) = 0) :
    S.ρ (ModularHopfCoproductRules.hatDeltaPhi (R := ℝ) S.N) = 1 := by
  rw [ModularHopfCoproductRules.hatDeltaPhi_eq_tensor_expansion (R := ℝ) (N := S.N)]
  rw [LinearMap.map_add]
  have hP : S.ρ ((S.N ⊗ₜ[ℝ] (1 : A)) + ((1 : A) ⊗ₜ[ℝ] S.N)) = 0 := by
    exact hPrimitive
  rw [hP]
  rw [show S.ρ (S.N ⊗ₜ[ℝ] S.N) = S.ρ (crossFlux (R := ℝ) S.N) by simp [crossFlux]]
  simp [S.crossRead]

/-- Cubic contributions vanish in any linear readout by `N^2 = 0`. -/
theorem liftFlux_cube_readout (A : Type*) [Ring A] [Algebra ℝ A]
    (S : NilpotentFluxReadout A) :
    S.ρ (liftFlux (R := ℝ) S.N * liftFlux (R := ℝ) S.N * liftFlux (R := ℝ) S.N) = 0 := by
  rw [liftFlux_cube_zero (R := ℝ) (N := S.N) S.hN]
  simp

/-- For any square-zero element, all powers ≥2 vanish. -/
lemma square_zero_pow_succ_zero
    {R : Type*} [MonoidWithZero R] {x : R} (hxx : x * x = 0) :
    ∀ m : ℕ, x ^ (m + 2) = 0 := by
  intro m
  induction m with
  | zero =>
      simpa [pow_two] using hxx
  | succ m ih =>
      calc
        x ^ (m.succ + 2) = x ^ (m + 2) * x := by
          simp [pow_succ, Nat.succ_eq_add_one, Nat.add_assoc]
        _ = 0 := by simp [ih]

/-- Iterated square-zero stability of the cross term `N ⊗ N`. -/
theorem crossFlux_pow_stable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
    (N : A) (hN : N * N = 0) : ∀ m : ℕ, (crossFlux (R := R) N) ^ (m + 2) = 0 := by
  intro m
  apply square_zero_pow_succ_zero
  simpa [crossFlux] using (tensor_nilpotent_sq_zero (R := R) (A := A) N hN)

/-- Coproduct cross-term effects are stable under higher tensor powers: all powers ≥3 vanish. -/
theorem coprod_N_pow_stable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
    (N : A) (hN : N * N = 0) : ∀ m : ℕ, (liftFlux (R := R) N) ^ (m + 3) = 0 := by
  intro m
  induction m with
  | zero =>
      simpa [pow_succ, pow_two, mul_assoc] using
        (liftFlux_cube_zero (R := R) (N := N) hN)
  | succ m ih =>
      calc
        liftFlux (R := R) N ^ (m.succ + 3)
            = liftFlux (R := R) N ^ (m + 3) * liftFlux (R := R) N := by
              simp [pow_succ, Nat.succ_eq_add_one, Nat.add_assoc]
        _ = 0 := by simp [ih]

/-- Split-channel relative-entropy profile generated by a linear nilpotent flux readout.

For central-coefficient normalization `c`, the `k`-th split layer is
`pairContributionWeight k * c` evaluated through the Virasoro cocycle profile on
`(m, n)`.
-/
def splitChannelRelativeEntropy
    (A : Type*) [Ring A] [Algebra ℝ A]
    (S : NilpotentFluxReadout A)
    (m n : Int) : ℕ → ℝ :=
  fun k => iteratedVirasoroCocycle k (S.ρ (crossFlux (R := ℝ) S.N)) m n

/-- Split-channel readout evolves by triangular cocycle increments. -/
theorem splitChannelRelativeEntropy_succ
    {A : Type*} [Ring A] [Algebra ℝ A]
    (S : NilpotentFluxReadout A)
    (m n : Int) (k : ℕ) :
    splitChannelRelativeEntropy (A := A) S m n (k + 1) =
      splitChannelRelativeEntropy (A := A) S m n k +
        (if m + n = 0 then
          ((k : ℝ) * S.ρ (crossFlux (R := ℝ) S.N) / 12) * (((m : ℝ) ^ 3) - (m : ℝ))
          else
            0) := by
  simp [splitChannelRelativeEntropy, iteratedVirasoroCocycle_succ]

/-- Resonant split-channel profile at two layers with arbitrary cross readout. -/
theorem splitChannelRelativeEntropy_two_step_resonant
    {A : Type*} [Ring A] [Algebra ℝ A]
    (S : NilpotentFluxReadout A) (m : Int) :
    splitChannelRelativeEntropy (A := A) S m (-m) 2 =
      (S.ρ (crossFlux (R := ℝ) S.N) / 12) * (((m : ℝ) ^ 3) - (m : ℝ)) := by
  simpa [splitChannelRelativeEntropy] using
    (iteratedVirasoroCocycle_two_resonant (c := S.ρ (crossFlux (R := ℝ) S.N)) m)

/-- Unit-cross-channel specialization.

If the cross readout is normalized to `1`, the split profile is exactly
`iteratedVirasoroCocycle k 1`.
-/
theorem splitChannelRelativeEntropy_unitCross_channel
    {A : Type*} [Ring A] [Algebra ℝ A]
    (S : NilpotentFluxReadout A)
    (hCross : S.ρ (crossFlux (R := ℝ) S.N) = 1) (m n : Int) (k : ℕ) :
    splitChannelRelativeEntropy (A := A) S m n k = iteratedVirasoroCocycle k 1 m n := by
  simp [splitChannelRelativeEntropy, hCross]

/-- Relative-entropy profile notation over split depth.

This is the same sequence as `splitChannelRelativeEntropy`, exposed to make the
Casini-style assumptions in `BekensteinBound` easier to read.
-/
def splitChannelRelativeEntropyProfile
    (A : Type*) [Ring A] [Algebra ℝ A]
    (S : NilpotentFluxReadout A)
    (m n : Int) : Nat → ℝ :=
  splitChannelRelativeEntropy (A := A) S m n

/-- Drop of the split-channel profile: `R(k) - R(k+1)`. -/
def splitChannelRelativeEntropyDrop
    (A : Type*) [Ring A] [Algebra ℝ A]
    (S : NilpotentFluxReadout A)
    (m n : Int) : Nat → ℝ :=
  fun k => splitChannelRelativeEntropyProfile (A := A) S m n k
    - splitChannelRelativeEntropyProfile (A := A) S m n (k + 1)

/-- Closed-form profile drop from the triangular recurrence.

On resonance, the one-step split drop is the negative triangular increment.
-/
theorem splitChannelRelativeEntropyDrop_succ
    {A : Type*} [Ring A] [Algebra ℝ A]
    (S : NilpotentFluxReadout A)
    (m n : Int) (k : ℕ) :
    splitChannelRelativeEntropyDrop (A := A) S m n k
      = -(if m + n = 0 then
          ((k : ℝ) * S.ρ (crossFlux (R := ℝ) S.N) / 12) * (((m : ℝ) ^ 3) - (m : ℝ))
          else 0) := by
  simp [splitChannelRelativeEntropyDrop, splitChannelRelativeEntropy_succ,
    splitChannelRelativeEntropyProfile]


/-- Triangular resonant closed form for the split entropy profile.

At resonance `m + n = 0`, this is `pairContributionWeight k` times the cubic
coefficient.
-/
theorem splitChannelRelativeEntropy_resonant
    {A : Type*} [Ring A] [Algebra ℝ A]
    (S : NilpotentFluxReadout A)
    (m n : Int) (k : ℕ)
    (hRes : m + n = 0) :
    splitChannelRelativeEntropy (A := A) S m n k =
      (pairContributionWeight k * S.ρ (crossFlux (R := ℝ) S.N) / 12)
        * (((m : ℝ) ^ 3) - (m : ℝ)) := by
  simp [splitChannelRelativeEntropy, iteratedVirasoroCocycle, iteratedCentralCoefficient,
    hRes]

/-- Closed form off resonance.

If `m + n ≠ 0`, all profile entries vanish.
-/
theorem splitChannelRelativeEntropy_offResonant
    {A : Type*} [Ring A] [Algebra ℝ A]
    (S : NilpotentFluxReadout A)
    (m n : Int) (k : ℕ)
    (hRes : m + n ≠ 0) :
    splitChannelRelativeEntropy (A := A) S m n k = 0 := by
  simp [splitChannelRelativeEntropy, iteratedVirasoroCocycle, iteratedCentralCoefficient,
    hRes]

/-- Minimal Casini bridge property from split-channel profile matching.

If the cocycle entropy potential increments match split-channel drops and those
match the phase-aligned RN generator, we get a `MinimalCasiniIncrementBridge`
directly.
-/
theorem minimalCasiniIncrementBridge_of_splitChannelRelativeEntropy_match
    (n : ℕ)
    {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {A : Type*} [Ring A] [Algebra ℝ A]
    (σ : AdditiveModularFlow (H := H))
    (u : ℝ → InfoGeometry.Volume.ConnesCocycle.AlgebraEnd H)
    (hBridge : ScalarCocycleBridge (H := H) σ)
    (T : SinkhornTrajectory n)
    (S : NilpotentFluxReadout A)
    (p q : Int)
    (hCocycleIncrement_matches_split :
      ∀ k : ℕ,
        CocycleEntropyPotential (H := H) σ u hBridge (k + 1)
          - CocycleEntropyPotential (H := H) σ u hBridge k
          = splitChannelRelativeEntropyDrop (A := A) S p q k)
    (hSplitPhaseMatch :
      ∀ k : ℕ,
        splitChannelRelativeEntropyDrop (A := A) S p q k
          = phaseRNGeneratorBefore n (phaseAt k) (T.state k)) :
    MinimalCasiniIncrementBridge (n := n) (H := H) σ u hBridge T
      (splitChannelRelativeEntropyProfile (A := A) S p q) := by
  refine ⟨?_, ?_⟩
  · intro k
    simpa [splitChannelRelativeEntropyProfile, splitChannelRelativeEntropyDrop] using
      hCocycleIncrement_matches_split k
  · intro k
    simpa [splitChannelRelativeEntropyProfile, splitChannelRelativeEntropyDrop] using
      hSplitPhaseMatch k

/-- Cocycle generator-lift from split-channel relative-entropy matching.

If the cocycle entropy potential increments agree with the split-channel profile
 drop and that drop matches the phase-aligned RN generator, then the standard
`CocycleGeneratorLift` condition follows.
-/
theorem cocycleGeneratorLift_of_splitChannelRelativeEntropy_match
    (n : ℕ)
    {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {A : Type*} [Ring A] [Algebra ℝ A]
    (σ : AdditiveModularFlow (H := H))
    (u : ℝ → InfoGeometry.Volume.ConnesCocycle.AlgebraEnd H)
    (hBridge : ScalarCocycleBridge (H := H) σ)
    (T : SinkhornTrajectory n)
    (S : NilpotentFluxReadout A)
    (p q : Int)
    (hCocycleIncrement_matches_split :
      ∀ k : ℕ,
        CocycleEntropyPotential (H := H) σ u hBridge (k + 1)
          - CocycleEntropyPotential (H := H) σ u hBridge k
          = splitChannelRelativeEntropyDrop (A := A) S p q k)
    (hSplitPhaseMatch :
      ∀ k : ℕ,
        splitChannelRelativeEntropyDrop (A := A) S p q k
          = phaseRNGeneratorBefore n (phaseAt k) (T.state k)) :
    CocycleGeneratorLift n T (CocycleEntropyPotential (H := H) σ u hBridge) := by
  let relEnt : RelativeEntropyProfile := splitChannelRelativeEntropyProfile (A := A) S p q
  let hCasini : MinimalCasiniIncrementBridge (n := n) (H := H) σ u hBridge T relEnt :=
    minimalCasiniIncrementBridge_of_splitChannelRelativeEntropy_match (n := n) (H := H) (A := A)
      (σ := σ) (u := u) (hBridge := hBridge) (T := T) (S := S)
      (p := p) (q := q) hCocycleIncrement_matches_split hSplitPhaseMatch
  exact cocycleGeneratorLift_of_minimalCasiniIncrementBridge
    (n := n) (σ := σ) (u := u) (hBridge := hBridge)
    (T := T) (relEnt := relEnt) hCasini

/-- Bekenstein consequence for the split-channel Casini alignment.

If both alignments in `cocycleGeneratorLift_of_splitChannelRelativeEntropy_match`
hold, the standard trajectory RN-barrier bound follows.
-/
theorem topologicalBekensteinBound_of_splitChannelRelativeEntropy_match
    (n : ℕ)
    {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {A : Type*} [Ring A] [Algebra ℝ A]
    (σ : AdditiveModularFlow (H := H))
    (u : ℝ → InfoGeometry.Volume.ConnesCocycle.AlgebraEnd H)
    (hBridge : ScalarCocycleBridge (H := H) σ)
    (T : SinkhornTrajectory n)
    (S : NilpotentFluxReadout A)
    (p q : Int)
    (hCocycleIncrement_matches_split :
      ∀ k : ℕ,
        CocycleEntropyPotential (H := H) σ u hBridge (k + 1)
          - CocycleEntropyPotential (H := H) σ u hBridge k
          = splitChannelRelativeEntropyDrop (A := A) S p q k)
    (hSplitPhaseMatch :
      ∀ k : ℕ,
        splitChannelRelativeEntropyDrop (A := A) S p q k
          = phaseRNGeneratorBefore n (phaseAt k) (T.state k)) :
    TopologicalBekensteinBound n T := by
  exact topologicalBekensteinBound_of_minimalCasiniIncrement
    (n := n) (σ := σ) (u := u) (T := T) (hBridge := hBridge)
    (relEnt := splitChannelRelativeEntropyProfile (A := A) S p q)
    (minimalCasiniIncrementBridge_of_splitChannelRelativeEntropy_match (n := n) (H := H)
      (A := A) (σ := σ) (u := u) (hBridge := hBridge) (T := T) (S := S)
      (p := p) (q := q) hCocycleIncrement_matches_split hSplitPhaseMatch)

/-- Abstract conformal-vacuum state-action-expectation packet.

This packages exactly the data used by bra-ket notation
`⟪Ω, A Ω⟫` in the project.
-/
structure ConformalVacuum (R : Type*) [Semiring R]
    (A : Type*) [AddCommMonoid A] [Module R A]
    (StateSpace : Type*) [AddCommGroup StateSpace] [Module R StateSpace] where
  omega : StateSpace
  expect : StateSpace →ₗ[R] R
  /-- Additive representation of algebraic observables on states. -/
  act : A →+ (StateSpace →ₗ[R] StateSpace)

/-- Vacuum expectation value in a chosen algebra action. -/
def vacuumExpectation (R : Type*) [Semiring R]
    {A : Type*} [AddCommMonoid A] [Module R A]
    {StateSpace : Type*} [AddCommGroup StateSpace] [Module R StateSpace]
    (Ω : ConformalVacuum R A StateSpace) : A → R :=
  fun x => Ω.expect (Ω.act x Ω.omega)

/-- Linear nilpotent seed flow on matrices: `E(t) = 1 + t•N`. -/
def modularFlowOperator (t : ℝ) : M2R :=
  (1 : M2R) + t • N

/-- Unit-time modular operator used in this bridge: `Δ := E(1) = 1 + N`. -/
def modularDelta : M2R :=
  modularFlowOperator 1

/-- Modular displacement from the identity, `Δ - 1`. -/
def modularDisplacement : M2R :=
  modularDelta - (1 : M2R)

/-- Exact finite identity of the displacement: `Δ - 1 = N`. -/
@[simp] theorem modularDisplacement_eq : modularDisplacement = N := by
  ext i j <;> fin_cases i <;> fin_cases j <;> simp [modularDisplacement, modularDelta, modularFlowOperator]

/-- In this square-zero sector, the displacement is nilpotent: `(Δ - 1)^2 = 0`. -/
@[simp] theorem modularDisplacement_sq_zero : modularDisplacement * modularDisplacement = (0 : M2R) := by
  rw [modularDisplacement_eq]
  simpa using (InfoGeometry.Canonical.ModularNilpotentAutomorphism.N_sq_zero)

/-- Modular displacement at general time: `(E(t) - 1) = t • N`. -/
theorem modularFlowDisplacement_smul (t : ℝ) :
    modularFlowOperator t - (1 : M2R) = t • N := by
  ext i j <;> fin_cases i <;> fin_cases j <;> simp [modularFlowOperator, sub_eq_add_neg]

/-- The nilpotent log-coordinate in `ModularNilpotentAutomorphism` is the same object. -/
@[simp] theorem modularDisplacement_eq_logModular :
    modularDisplacement = InfoGeometry.Canonical.ModularNilpotentAutomorphism.logModular := by
  simp [modularDisplacement_eq, InfoGeometry.Canonical.ModularNilpotentAutomorphism.logModular]

/-- Flow displacement at time `t` as an additive coordinate on `modularDisplacement`. -/
theorem modularDisplacement_flow_eq (t : ℝ) :
    modularFlowOperator t - (1 : M2R) = t • modularDisplacement := by
  rw [modularFlowDisplacement_smul, modularDisplacement_eq]

/-- Noncommutative thermodynamic seed operators at the local level. -/

def log_modular : M2R :=
  N

def entropy_flux : M2R :=
  modularDisplacement

/-- Information free-energy operator `A_info = (Δ - 1) - log(Δ)`. -/
def information_free_energy : M2R :=
  entropy_flux - log_modular

/-- Local thermodynamic minimum at the symmetry point (`N² = 0` in this sector). -/
@[simp] theorem information_free_energy_eq_zero :
    information_free_energy = 0 := by
  unfold information_free_energy entropy_flux log_modular
  simp [modularDisplacement_eq]


/-- Multi-faceted identity block for the modular generator.

`modularDisplacement` is simultaneously:
1. the unit-time difference `Δ - 1`,
2. the degree-(-1) algebraic seed in this bridge,
3. the formal log-coordinate in the square-zero sector,
4. nilpotent (`(Δ - 1)^2 = 0`).
-/
theorem modularDisplacement_spec (t : ℝ) :
    modularFlowOperator t - (1 : M2R) = t • modularDisplacement ∧
    modularDisplacement = N ∧
    modularDisplacement = InfoGeometry.Canonical.ModularNilpotentAutomorphism.logModular ∧
    modularDisplacement * modularDisplacement = (0 : M2R) := by
  refine ⟨modularDisplacement_flow_eq (t := t), modularDisplacement_eq, modularDisplacement_eq_logModular, modularDisplacement_sq_zero⟩

-- Interpretation summary for `modularDisplacement`:
--
-- 1. Lie tangent: it is the exact modular tangent at the identity
--    (`Δ_t - 1 = t • N`).
-- 2. Entanglement boundary: it is the pure cut-local defect; crossed terms in
--    `liftFlux` propagate through this channel.
-- 3. Conformal realization: it is the linear degree-`-1` seed in the Virasoro split
--    profile.
-- 4. Information geometry: by square-zero, the formal modular logarithm is exactly
--    this coordinate (`log Δ = N`).

/-- Information free-energy operator in this concrete nilpotent sector.

This is the local Helmholtz free-energy coordinate:

`A_info := (Δ - 1) - logModular`.

In the square-zero regime, this vanishes exactly.
-/
def informationFreeEnergy : M2R :=
  entropy_flux - log_modular

/-- Exact cancellation: `(Δ - 1) - logΔ = 0` in the concrete seed model. -/
@[simp] theorem informationFreeEnergy_eq_zero : informationFreeEnergy = 0 := by
  unfold informationFreeEnergy entropy_flux log_modular
  rw [modularDisplacement_eq]
  simp

/-- Compatibility of the local camelCase free-energy notation with the algebraic block form. -/
lemma informationFreeEnergy_eq_information_free_energy :
    informationFreeEnergy = information_free_energy := by
  unfold informationFreeEnergy information_free_energy entropy_flux log_modular
  simp [modularDisplacement_eq]

/-- Vacuity of square-zero free energy in the local equilibrium chamber. -/

theorem modularDisplacement_iff_flow_linear_at_one (X : M2R) :
    modularFlowOperator 1 = (1 : M2R) + (1 : ℝ) • X ↔ X = modularDisplacement := by
  constructor
  · intro hFlow
    have hflowN : modularFlowOperator 1 = (1 : M2R) + (1 : ℝ) • N := by
      have h := modularDisplacement_flow_eq (t := (1 : ℝ))
      have h' := congrArg (fun K => K + (1 : M2R)) h
      simpa [modularDisplacement_eq, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using h'
    have hN' : modularFlowOperator 1 - (1 : M2R) = (1 : ℝ) • X := by
      have h := congrArg (fun K => K - (1 : M2R)) hFlow
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using h
    have hN : (1 : ℝ) • N = (1 : ℝ) • X := by
      have hN0 : modularFlowOperator 1 - (1 : M2R) = (1 : ℝ) • N := by
        have h := congrArg (fun K => K - (1 : M2R)) hflowN
        simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using h
      calc
        (1 : ℝ) • N = modularFlowOperator 1 - (1 : M2R) := by simpa [hN0] using hN0.symm
        _ = (1 : ℝ) • X := hN'
    have hNX : N = X := by simpa using hN
    simpa [modularDisplacement_eq] using hNX.symm
  · intro hX
    have hflowN : modularFlowOperator 1 = (1 : M2R) + (1 : ℝ) • N := by
      have h := modularDisplacement_flow_eq (t := (1 : ℝ))
      have h' := congrArg (fun K => K + (1 : M2R)) h
      simpa [modularDisplacement_eq, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using h'
    simpa [hX] using hflowN

/-- Square-zero coordinate characterization in this finite sector.

`modularDisplacement` is the unique coordinate realizing linear flow at t=1 in the
unit sector, and it is square-zero.
-/
theorem modularDisplacement_is_squareZero_coordinate (X : M2R)
    (hFlow : modularFlowOperator 1 = (1 : M2R) + (1 : ℝ) • X) :
    X = modularDisplacement ∧ X * X = (0 : M2R) := by
  have hX : X = modularDisplacement := (modularDisplacement_iff_flow_linear_at_one X).1 hFlow
  refine ⟨?_, ?_⟩
  · exact hX
  · simpa [hX] using modularDisplacement_sq_zero

/-- Vacuum expectation of the local information free-energy is exactly zero. -/
theorem vacuumExpectation_informationFreeEnergy_vac (StateSpace : Type*) [AddCommGroup StateSpace]
    [Module ℝ StateSpace]
    (Ω : ConformalVacuum ℝ M2R StateSpace) :
    vacuumExpectation ℝ Ω informationFreeEnergy = 0 := by
  unfold informationFreeEnergy
  simp [entropy_flux, log_modular, modularDisplacement_eq, vacuumExpectation]

/-- Local modular automorphism built from `E(t) A E(-t)`. -/
def modularAutomorphism (t : ℝ) (A : M2R) : M2R :=
  modularFlowOperator t * A * modularFlowOperator (-t)

/-- Exact finite expansion for the local nilpotent modular automorphism. -/
theorem modularAutomorphism_exact_expansion (t : ℝ) (A : M2R) :
    modularAutomorphism t A =
      A + t • (N * A - A * N) - (t * t) • (N * A * N) := by
  change InfoGeometry.Canonical.ModularNilpotentAutomorphism.modularAutomorphism t A = _
  simpa [modularFlowOperator, modularAutomorphism] using
    InfoGeometry.Canonical.ModularNilpotentAutomorphism.modularAutomorphism_exact_expansion (t := t) (A := A)

/-- Algebraic KMS continuation in the finite sector:
`σ_{β t}` is an exact quadratic polynomial in `β t` (no analytic continuation
is needed).
-/
theorem modularAutomorphism_beta_polynomial (β t : ℝ) (A : M2R) :
    modularAutomorphism (β * t) A =
      A + (β * t) • (N * A - A * N) - ((β * t) * (β * t)) • (N * A * N) := by
  simpa using (modularAutomorphism_exact_expansion (t := β * t) (A := A))
/-- Finite-β thermodynamic stationarity of the local free-energy coordinate.

In the square-zero sector, `informationFreeEnergy` vanishes identically, hence it is
`modularAutomorphism`-invariant at any modular time and has zero expectation.
-/
theorem modularAutomorphism_informationFreeEnergy_fixed (t : ℝ) :
    modularAutomorphism t informationFreeEnergy = informationFreeEnergy := by
  rw [informationFreeEnergy_eq_zero]
  simp [modularAutomorphism]

/-- Finite-β KMS-step: the modular orbit of `informationFreeEnergy` is trivial,
    so it remains zero at each modular time.
-/
theorem modularAutomorphism_informationFreeEnergy_eq_zero (t : ℝ) :
    modularAutomorphism t informationFreeEnergy = 0 := by
  rw [modularAutomorphism_informationFreeEnergy_fixed (t := t)]
  simp [informationFreeEnergy_eq_zero]

/-- Internal vacuum expectation expansion for the local modular flow.

For a `ConformalVacuum` whose action is `R`-linear in the observable,
this is the action-level truncation
`σ_t(A) = A + t[N,A] - t²NAN` read through vacuum expectation.
-/
theorem modularAutomorphism_expectation_exact_expansion
    {StateSpace : Type*} [AddCommGroup StateSpace] [Module ℝ StateSpace]
    (Ω : ConformalVacuum ℝ M2R StateSpace)
    (A : M2R) (t : ℝ) :
    vacuumExpectation ℝ Ω (modularAutomorphism t A) =
      vacuumExpectation ℝ Ω (A + t • (N * A - A * N) - (t * t) • (N * A * N)) := by
  unfold vacuumExpectation
  rw [modularAutomorphism_exact_expansion (t := t) (A := A)]

/-- Vacuum expectation of free-energy under modular time evolution is zero (finite-β KMS-neutrality). -/
theorem vacuumExpectation_modularAutomorphism_informationFreeEnergy (StateSpace : Type*)
    [AddCommGroup StateSpace] [Module ℝ StateSpace]
    (Ω : ConformalVacuum ℝ M2R StateSpace) (t : ℝ) :
    vacuumExpectation ℝ Ω (modularAutomorphism t informationFreeEnergy) = 0 := by
  rw [modularAutomorphism_informationFreeEnergy_fixed (t := t)]
  exact vacuumExpectation_informationFreeEnergy_vac (StateSpace := StateSpace) Ω

/-- Finite-β scaling variant of KMS-neutrality: any inverse-temperature slot keeps the
expectation of the local information free energy at zero.
-/
theorem finiteTemperature_vacuumExpectation_modularAutomorphism_informationFreeEnergy
    (StateSpace : Type*) [AddCommGroup StateSpace] [Module ℝ StateSpace]
    (Ω : ConformalVacuum ℝ M2R StateSpace) (β t : ℝ) :
    vacuumExpectation ℝ Ω (modularAutomorphism (β * t) informationFreeEnergy) = 0 := by
  simpa using vacuumExpectation_modularAutomorphism_informationFreeEnergy
    (StateSpace := StateSpace) Ω (β * t)

/-- KMS-form statement: finite-β modular time evolution preserves the free-energy
expectation at the thermodynamic vacuum point.
-/
theorem finiteTemperature_vacuumExpectation_modularAutomorphism_informationFreeEnergy_kms
    (StateSpace : Type*) [AddCommGroup StateSpace] [Module ℝ StateSpace]
    (Ω : ConformalVacuum ℝ M2R StateSpace) (β t : ℝ) :
    vacuumExpectation ℝ Ω (modularAutomorphism (β * t) informationFreeEnergy)
      = vacuumExpectation ℝ Ω informationFreeEnergy := by
  rw [finiteTemperature_vacuumExpectation_modularAutomorphism_informationFreeEnergy (StateSpace := StateSpace)
    (Ω := Ω) β t]
  rw [vacuumExpectation_informationFreeEnergy_vac (StateSpace := StateSpace) Ω]

/-- Inner-product-based vacuum expectation via a bilinear form on the state space.

Given a bilinear form `innerProd`, this evaluates an algebra element `x` by

a scalar `⟪Ω | act(x) Ω⟫ = innerProd Ω.omega (Ω.act x Ω.omega)`.
-/
def vacuumExpectationWithInner (R : Type*) [CommSemiring R]
    {A : Type*} [AddCommMonoid A] [Module R A]
    {StateSpace : Type*} [AddCommGroup StateSpace] [Module R StateSpace]
    (innerProd : LinearMap.BilinForm R StateSpace)
    (Ω : ConformalVacuum R A StateSpace) : A → R :=
  fun x => innerProd Ω.omega (Ω.act x Ω.omega)

lemma vacuumExpectationWithInner_zero_of_annihilation
    {R : Type*} [CommSemiring R]
    {A : Type*} [AddCommMonoid A] [Module R A]
    {StateSpace : Type*} [AddCommGroup StateSpace] [Module R StateSpace]
    (innerProd : LinearMap.BilinForm R StateSpace)
    (Ω : ConformalVacuum R A StateSpace) (x : A)
    (h : Ω.act x Ω.omega = 0) :
    vacuumExpectationWithInner (R := R) innerProd Ω x = 0 := by
  simp [vacuumExpectationWithInner, h]

/-- Expectation is linear in the observable insertion. -/
lemma vacuumExpectation_zero_of_observable_zero
    {R : Type*} [Semiring R]
    {A : Type*} [AddCommMonoid A] [Module R A]
    {StateSpace : Type*} [AddCommGroup StateSpace] [Module R StateSpace]
    (Ω : ConformalVacuum R A StateSpace) (x : A)
    (h : Ω.act x Ω.omega = 0) :
    vacuumExpectation R Ω x = 0 := by
  simp [vacuumExpectation, h]

/-- Symmetry-point specialization: if the vacuum is annihilated by `L_{-1}` then
its evaluation in that mode is zero. -/
theorem virasoro_vacuum_mode_minus_one_vanishes
    {R : Type*} [Field R] [CharZero R]
    {StateSpace : Type*} [AddCommGroup StateSpace] [Module R StateSpace]
    (innerProd : LinearMap.BilinForm R StateSpace)
    (Ω : ConformalVacuum R (VirasoroProject.VirasoroAlgebra R) StateSpace)
    (hminus : Ω.act (VirasoroProject.VirasoroAlgebra.lgen R (-1)) Ω.omega = 0) :
    vacuumExpectationWithInner (R := R) innerProd Ω (VirasoroProject.VirasoroAlgebra.lgen R (-1)) = 0 := by
  simpa using
    (vacuumExpectationWithInner_zero_of_annihilation (R := R) (A := VirasoroProject.VirasoroAlgebra R)
      innerProd Ω (VirasoroProject.VirasoroAlgebra.lgen R (-1)) hminus)

/-- Inner-product specialization to the plain vacuum expectation in the same mode. -/
theorem virasoro_vacuum_mode_minus_one_vanishes_raw
    {R : Type*} [Field R] [CharZero R]
    {StateSpace : Type*} [AddCommGroup StateSpace] [Module R StateSpace]
    (Ω : ConformalVacuum R (VirasoroProject.VirasoroAlgebra R) StateSpace)
    (hminus : Ω.act (VirasoroProject.VirasoroAlgebra.lgen R (-1)) Ω.omega = 0) :
    vacuumExpectation R Ω (VirasoroProject.VirasoroAlgebra.lgen R (-1)) = 0 := by
  exact vacuumExpectation_zero_of_observable_zero (R := R) Ω (VirasoroProject.VirasoroAlgebra.lgen R (-1)) hminus

/-- Zero expectation for a decomposition into two independent vanishers. -/
lemma vacuumExpectation_sum_of_zero_actions
    {R : Type*} [Semiring R]
    {A : Type*} [AddCommMonoid A] [Module R A]
    {StateSpace : Type*} [AddCommGroup StateSpace] [Module R StateSpace]
    (Ω : ConformalVacuum R A StateSpace) (x y : A)
    (hx : Ω.act x Ω.omega = 0) (hy : Ω.act y Ω.omega = 0) :
    vacuumExpectation R Ω (x + y) = 0 := by
  simp [vacuumExpectation, AddMonoidHom.map_add, hx, hy]

/-- Expectation of a regularized square-zero seed is annihilated when its primitive
and cross pieces annihilate the vacuum. -/
theorem regularizedFluxExpectation_zero
    {R : Type*} [CommRing R]
    {A : Type*} [Ring A] [Algebra R A]
    (StateSpace : Type*) [AddCommGroup StateSpace] [Module R StateSpace]
    (N : A)
    (Ω : ConformalVacuum R (A ⊗[R] A) StateSpace)
    (hprimitive : Ω.act (primitiveFlux (R := R) N) Ω.omega = 0)
    (hcross : Ω.act (crossFlux (R := R) N) Ω.omega = 0) :
    Ω.expect (Ω.act (liftFlux (R := R) N) Ω.omega) = 0 := by
  rw [liftFlux_eq_primitive_add_cross (R := R) (N := N)]
  simp [AddMonoidHom.map_add, hprimitive, hcross]

/-- Same statement in `vacuumExpectation` notation. -/
theorem regularizedFluxExpectation_zero'
    {R : Type*} [CommRing R]
    {A : Type*} [Ring A] [Algebra R A]
    (StateSpace : Type*) [AddCommGroup StateSpace] [Module R StateSpace]
    (N : A)
    (Ω : ConformalVacuum R (A ⊗[R] A) StateSpace)
    (hprimitive : Ω.act (primitiveFlux (R := R) N) Ω.omega = 0)
    (hcross : Ω.act (crossFlux (R := R) N) Ω.omega = 0) :
    vacuumExpectation R Ω (liftFlux (R := R) N) = 0 := by
  simp [vacuumExpectation, regularizedFluxExpectation_zero (R := R) (A := A) (StateSpace := StateSpace)
      N Ω hprimitive hcross]

/-- If no vacuum assumptions are needed, every sufficiently high tensor power
annihilates the vacuum in expectation under an additive action, since
`liftFlux^(m+3)=0` and `act 0` is the zero operator. -/
theorem regularizedFluxExpectation_pow_zero
    {R : Type*} [CommRing R]
    {A : Type*} [Ring A] [Algebra R A]
    (StateSpace : Type*) [AddCommGroup StateSpace] [Module R StateSpace]
    (N : A) (hN : N * N = 0)
    (Ω : ConformalVacuum R (A ⊗[R] A) StateSpace) :
    ∀ m : ℕ, Ω.expect (Ω.act ((liftFlux (R := R) N) ^ (m + 3)) Ω.omega) = 0 := by
  intro m
  have hpow := coprod_N_pow_stable (R := R) (A := A) N hN m
  rw [hpow]
  simp

/-- Two-step accumulation reproduces the local cocycle seed with unit charge. -/
theorem iterated_two_matches_local_formula (m n : Int) :
    iteratedVirasoroCocycle 2 1 m n =
      InfoGeometry.Canonical.NilpotentFluxVirasoroReadout.nilpotentFluxCentralCoefficient m n := by
  have hpair : iteratedCentralCoefficient 2 1 = 1 := by
    norm_num [iteratedCentralCoefficient, pairContributionWeight]
  rw [iteratedVirasoroCocycle, hpair]
  rw [InfoGeometry.Canonical.NilpotentFluxVirasoroReadout.nilpotentFluxCentralCoefficient_eq_virasoro]
  by_cases h : m + n = 0
  · simp [virasoroCocycleDensity, h, div_eq_mul_inv, mul_comm]
  · simp [virasoroCocycleDensity, h]


/-- Compatibility with the external `VirasoroAlgebra` bracket shape at charge `1`. -/
theorem lgen_central_profile_from_readout (m n : Int) :
    ⁅VirasoroProject.VirasoroAlgebra.lgen ℝ m, VirasoroProject.VirasoroAlgebra.lgen ℝ n⁆ =
      (m - n : ℝ) • VirasoroProject.VirasoroAlgebra.lgen ℝ (m + n) +
        virasoroCocycleDensity 1 m n • VirasoroProject.VirasoroAlgebra.cgen ℝ := by
  simp [VirasoroProject.VirasoroAlgebra.lgen_bracket, virasoroCocycleDensity, div_eq_mul_inv,
    mul_comm]

/-- Concrete charged-Fock conformal vacuum for any bilinear readout functional. -/
def chargedFockConformalVacuum
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜]
    (α : 𝕜)
    (innerProd : LinearMap.BilinForm 𝕜 (VirasoroProject.ChargedFockSpace 𝕜 α)) :
    ConformalVacuum 𝕜 (VirasoroProject.VirasoroAlgebra 𝕜)
      (VirasoroProject.ChargedFockSpace 𝕜 α) :=
  {
    omega := VirasoroProject.ChargedFockSpace.vacuum 𝕜 α,
    expect := innerProd (VirasoroProject.ChargedFockSpace.vacuum 𝕜 α),
    act := (VirasoroProject.ChargedFockSpace.sugawaraRepresentation (𝕜 := 𝕜) α).toAddMonoidHom
  }

/-- Positive-mode annihilation in the concrete charged-Fock conformal packet.

Given the Sugawara highest-weight convention, `L_n` kills the vacuum for `n > 0`. -/
theorem chargedFockConformalVacuum_lgen_positive_annihilates
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜]
    (α : 𝕜)
    (innerProd : LinearMap.BilinForm 𝕜 (VirasoroProject.ChargedFockSpace 𝕜 α))
    (n : Int) (hn : 0 < n) :
    (chargedFockConformalVacuum (𝕜 := 𝕜) α innerProd).act
      (VirasoroProject.VirasoroAlgebra.lgen 𝕜 n)
      (chargedFockConformalVacuum (𝕜 := 𝕜) α innerProd).omega = 0 := by
  simpa [chargedFockConformalVacuum] using
    (InfoGeometry.Canonical.SplitCliffordSourceWickVacuum.chargedFock_sugawara_positive_annihilates_vacuum
      (𝕜 := 𝕜) α hn)

/-- `L_n` vacuum expectation in the concrete packet vanishes for positive modes. -/
theorem chargedFockConformalVacuum_vacuumExpectation_lgen_positive
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜]
    (α : 𝕜)
    (innerProd : LinearMap.BilinForm 𝕜 (VirasoroProject.ChargedFockSpace 𝕜 α))
    (n : Int) (hn : 0 < n) :
    vacuumExpectation 𝕜 (chargedFockConformalVacuum (𝕜 := 𝕜) α innerProd)
      (VirasoroProject.VirasoroAlgebra.lgen 𝕜 n) = 0 := by
  rw [vacuumExpectation, chargedFockConformalVacuum]
  have hzero := chargedFockConformalVacuum_lgen_positive_annihilates (𝕜 := 𝕜) α innerProd n hn
  simpa [chargedFockConformalVacuum] using
    congrArg (fun v => innerProd (VirasoroProject.ChargedFockSpace.vacuum 𝕜 α) v) hzero

/-- Zero-mode readout for the concrete charged-Fock vacuum.

This is the packaged Sugawara highest-weight eigenvalue statement.
-/
theorem chargedFockConformalVacuum_lgen_zero_action
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜]
    (α : 𝕜)
    (innerProd : LinearMap.BilinForm 𝕜 (VirasoroProject.ChargedFockSpace 𝕜 α)) :
    (chargedFockConformalVacuum (𝕜 := 𝕜) α innerProd).act
      (VirasoroProject.VirasoroAlgebra.lgen 𝕜 0)
      (chargedFockConformalVacuum (𝕜 := 𝕜) α innerProd).omega =
      (α ^ 2 / 2) • (VirasoroProject.ChargedFockSpace.vacuum 𝕜 α) := by
  simpa [chargedFockConformalVacuum] using
    (InfoGeometry.Canonical.SplitCliffordSourceWickVacuum.chargedFock_sugawara_zero_mode_on_vacuum
      (𝕜 := 𝕜) α)

/-- Central generator readout in the concrete charged-Fock packet. -/
theorem chargedFockConformalVacuum_central_action
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜]
    (α : 𝕜)
    (innerProd : LinearMap.BilinForm 𝕜 (VirasoroProject.ChargedFockSpace 𝕜 α)) :
    (chargedFockConformalVacuum (𝕜 := 𝕜) α innerProd).act
      (VirasoroProject.VirasoroAlgebra.cgen 𝕜)
      (chargedFockConformalVacuum (𝕜 := 𝕜) α innerProd).omega =
      VirasoroProject.ChargedFockSpace.vacuum 𝕜 α := by
  simpa [chargedFockConformalVacuum] using
    (VirasoroProject.ChargedFockSpace.sugawaraRepresentation_cgen_apply
      (𝕜 := 𝕜) α (VirasoroProject.ChargedFockSpace.vacuum 𝕜 α))

/-- Vacuum expectation of the central generator is the vacuum norm (by identity action). -/
theorem chargedFockConformalVacuum_vacuumExpectation_cgen
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜]
    (α : 𝕜)
    (innerProd : LinearMap.BilinForm 𝕜 (VirasoroProject.ChargedFockSpace 𝕜 α)) :
    vacuumExpectation 𝕜 (chargedFockConformalVacuum (𝕜 := 𝕜) α innerProd)
      (VirasoroProject.VirasoroAlgebra.cgen 𝕜) =
      innerProd (VirasoroProject.ChargedFockSpace.vacuum 𝕜 α)
        (VirasoroProject.ChargedFockSpace.vacuum 𝕜 α) := by
  simpa [vacuumExpectation, chargedFockConformalVacuum] using
    congrArg (fun v => innerProd (VirasoroProject.ChargedFockSpace.vacuum 𝕜 α) v)
      (chargedFockConformalVacuum_central_action (𝕜 := 𝕜) α innerProd)

/-- Vacuum expectation of the zero mode is the zero-mode eigenvalue against the vacuum norm. -/
theorem chargedFockConformalVacuum_vacuumExpectation_lgen_zero
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜]
    (α : 𝕜)
    (innerProd : LinearMap.BilinForm 𝕜 (VirasoroProject.ChargedFockSpace 𝕜 α)) :
    vacuumExpectation 𝕜 (chargedFockConformalVacuum (𝕜 := 𝕜) α innerProd)
      (VirasoroProject.VirasoroAlgebra.lgen 𝕜 0) =
      (α ^ 2 / 2) *
        innerProd (VirasoroProject.ChargedFockSpace.vacuum 𝕜 α)
          (VirasoroProject.ChargedFockSpace.vacuum 𝕜 α) := by
  have hzero := chargedFockConformalVacuum_lgen_zero_action (𝕜 := 𝕜) α innerProd
  have hsmul :
      innerProd (VirasoroProject.ChargedFockSpace.vacuum 𝕜 α)
          ((α ^ 2 / 2) • VirasoroProject.ChargedFockSpace.vacuum 𝕜 α)
        = (α ^ 2 / 2) * innerProd (VirasoroProject.ChargedFockSpace.vacuum 𝕜 α)
          (VirasoroProject.ChargedFockSpace.vacuum 𝕜 α) := by
    calc
      innerProd (VirasoroProject.ChargedFockSpace.vacuum 𝕜 α)
          ((α ^ 2 / 2) • VirasoroProject.ChargedFockSpace.vacuum 𝕜 α) =
          (α ^ 2 / 2) • innerProd (VirasoroProject.ChargedFockSpace.vacuum 𝕜 α)
            (VirasoroProject.ChargedFockSpace.vacuum 𝕜 α) := by
            simpa using
              (innerProd (VirasoroProject.ChargedFockSpace.vacuum 𝕜 α)).map_smul
                (α ^ 2 / 2) (VirasoroProject.ChargedFockSpace.vacuum 𝕜 α)
      _ = (α ^ 2 / 2) * innerProd (VirasoroProject.ChargedFockSpace.vacuum 𝕜 α)
            (VirasoroProject.ChargedFockSpace.vacuum 𝕜 α) := by simp [smul_eq_mul]
  change innerProd (VirasoroProject.ChargedFockSpace.vacuum 𝕜 α)
      ((chargedFockConformalVacuum (𝕜 := 𝕜) α innerProd).act
        (VirasoroProject.VirasoroAlgebra.lgen 𝕜 0)
        (chargedFockConformalVacuum (𝕜 := 𝕜) α innerProd).omega) =
      (α ^ 2 / 2) * innerProd (VirasoroProject.ChargedFockSpace.vacuum 𝕜 α)
        (VirasoroProject.ChargedFockSpace.vacuum 𝕜 α)
  rw [hzero]
  simpa [hsmul]

/-- Inner-product and plain vacuum expectation coincide for this concrete packet.

This is exactly the design principle behind `vacuumExpectationWithInner`.
-/
theorem chargedFockConformalVacuum_expectation_inner_eq
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜]
    (α : 𝕜)
    (innerProd : LinearMap.BilinForm 𝕜 (VirasoroProject.ChargedFockSpace 𝕜 α)) (x : VirasoroProject.VirasoroAlgebra 𝕜) :
    vacuumExpectationWithInner (R := 𝕜) innerProd (chargedFockConformalVacuum (𝕜 := 𝕜) α innerProd) x =
      vacuumExpectation 𝕜 (chargedFockConformalVacuum (𝕜 := 𝕜) α innerProd) x := by
  rfl

/-- Re-exported external mode-one commutator normalisation for the charged-Fock lane. -/
theorem chargedFock_external_mode_one_commutator
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜) :
    let M :
      InfoGeometry.Canonical.CurrentSugawaraBridge.CurrentSugawaraMorphism 𝕜
        (VirasoroProject.ChargedFockSpace 𝕜 α) :=
      InfoGeometry.Canonical.CurrentSugawaraBridge.CurrentSugawaraMorphism.ofHeisenberg
        (InfoGeometry.Canonical.CurrentSugawaraBridge.chargedFockSpaceCurrentHeisenbergRep 𝕜 α)
    (M.heisenberg.J 1).commutator (M.heisenberg.J (-1)) =
      (1 : 𝕜) •
        (1 :
          VirasoroProject.ChargedFockSpace 𝕜 α →ₗ[𝕜]
            VirasoroProject.ChargedFockSpace 𝕜 α) := by
  simpa using
    InfoGeometry.Canonical.SplitCliffordSourceWickBaseExternalBridge.external_chargedFock_mode_one_commutator
      (𝕜 := 𝕜) α

/-- Bracket-on-opposite-modes central channel equals the explicit Virasoro polynomial. -/
theorem bracket_snd_eq_iteratedVirasoroCocycle_two_resonant (m : Int) :
    (⁅VirasoroProject.VirasoroAlgebra.lgen ℝ m,
        VirasoroProject.VirasoroAlgebra.lgen ℝ (-m)⁆).snd =
      iteratedVirasoroCocycle 2 1 m (-m) := by
  have h :=
    (VirasoroProject.VirasoroAlgebra.lgen_bracket_of_add_eq_zero (𝕜 := ℝ) m (-m) (by simp))
  have hs := congrArg (fun x : VirasoroProject.VirasoroAlgebra ℝ => x.snd) h
  have hs' : (⁅VirasoroProject.VirasoroAlgebra.lgen ℝ m,
      VirasoroProject.VirasoroAlgebra.lgen ℝ (-m)⁆).snd =
      (12 : ℝ)⁻¹ * (((m : ℝ)^3) - (m : ℝ)) := by
    simpa [div_eq_mul_inv, sub_eq_add_neg, add_assoc, add_left_comm, add_comm,
      VirasoroProject.VirasoroAlgebra.lgen_eq', VirasoroProject.VirasoroAlgebra.cgen_eq',
      VirasoroProject.VirasoroAlgebra.toWittAlgebra_lgen,
      VirasoroProject.WittAlgebra.virasoroCocycle_apply_lgen_lgen,
      mul_comm, mul_left_comm, mul_assoc] using hs
  calc
    (⁅VirasoroProject.VirasoroAlgebra.lgen ℝ m,
        VirasoroProject.VirasoroAlgebra.lgen ℝ (-m)⁆).snd =
      (12 : ℝ)⁻¹ * (((m : ℝ)^3) - (m : ℝ)) := hs'
    _ = (1 / 12 : ℝ) * (((m : ℝ)^3) - (m : ℝ)) := by ring
    _ = iteratedVirasoroCocycle 2 1 m (-m) := by
      simpa using (iteratedVirasoroCocycle_two_resonant (c := (1 : ℝ)) m).symm

/-- Resonant two-step readout equals the explicit Virasoro algebra central channel on concrete generators. -/
theorem iteratedVirasoroCocycle_two_resonant_eq_lgen_snd (m : Int) :
    iteratedVirasoroCocycle 2 1 m (-m) =
      (⁅VirasoroProject.VirasoroAlgebra.lgen ℝ m,
        VirasoroProject.VirasoroAlgebra.lgen ℝ (-m)⁆).snd := by
  simpa using (bracket_snd_eq_iteratedVirasoroCocycle_two_resonant (m := m)).symm

/-- Final local rewrite: the finite concrete readout gives the same resonant profile. -/
theorem local_cocycle_as_iterated_profile
    {m n : Int} :
    InfoGeometry.Canonical.NilpotentFluxVirasoroReadout.nilpotentFluxCentralCoefficient m n =
      iteratedVirasoroCocycle 2 1 m n := by
  exact (iterated_two_matches_local_formula m n).symm

end

end InfoGeometry.Canonical.CoproductToVirasoroCocycleBridge
