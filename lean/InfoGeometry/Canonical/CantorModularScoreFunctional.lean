import Mathlib
import InfoGeometry.Canonical.CantorCylinderLattice

/-!
# InfoGeometry.Canonical.CantorModularScoreFunctional

Finite dyadic-cylinder modular score functionals.

The original finite point-density lane uses `Fin (2^n)`:

* local density `Δ_{w,n} = 2^n * 1_{ {w} }`,
* centered score `Y_{w,n} = Δ_{w,n} - 1`,
* functional `η_{w,n}(f) = ∫ f Y_{w,n} dμ_n`.

This file also exposes the same finite centering pattern directly on the
Cantor-cylinder level carrier `BinaryWord n → ℝ`:

`scoreAt w f = f w - uniformMean f`.

All statements here are finite algebraic identities.  No infinite state,
measure-theoretic limit, or operator-algebraic completion is constructed here.
-/

namespace InfoGeometry.Canonical.CantorModularScoreFunctional

open scoped BigOperators
open Finset
open InfoGeometry.Canonical.CantorCylinderLattice

noncomputable section

/-- Uniform finite average on `Fin (2^n)`. -/
def muAvg (n : ℕ) (f : Fin (2 ^ n) → ℝ) : ℝ :=
  ((2 ^ n : ℝ)⁻¹) * ∑ i : Fin (2 ^ n), f i

/-- Local point-state density `Δ_{w,n}`. -/
def deltaDensity (n : ℕ) (w : Fin (2 ^ n)) : Fin (2 ^ n) → ℝ :=
  fun i => if i = w then (2 ^ n : ℝ) else 0

/-- Centered modular score `Y_{w,n} = Δ_{w,n} - 1`. -/
def centeredScore (n : ℕ) (w : Fin (2 ^ n)) : Fin (2 ^ n) → ℝ :=
  fun i => deltaDensity n w i - 1

/-- Finite modular score functional `η_{w,n}`. -/
def eta (n : ℕ) (w : Fin (2 ^ n)) (f : Fin (2 ^ n) → ℝ) : ℝ :=
  muAvg n (fun i => f i * centeredScore n w i)

/--
Exact finite score identity:
`η_{w,n}(f) = f(w) - μ_n(f)`.
-/
theorem eta_eq_eval_sub_avg
    (n : ℕ) (w : Fin (2 ^ n)) (f : Fin (2 ^ n) → ℝ) :
    eta n w f = f w - muAvg n f := by
  unfold eta muAvg centeredScore deltaDensity
  have hN : (2 ^ n : ℝ) ≠ 0 := by positivity
  have hsumDelta :
      ∑ i : Fin (2 ^ n), f i * (if i = w then (2 ^ n : ℝ) else 0) = f w * (2 ^ n : ℝ) := by
    simp
  calc
    (↑(2 ^ n))⁻¹ * ∑ i : Fin (2 ^ n), (f i * ((if i = w then ↑(2 ^ n) else 0) - 1))
        = (↑(2 ^ n))⁻¹ *
            (∑ i : Fin (2 ^ n), f i * (if i = w then ↑(2 ^ n) else 0)
              - ∑ i : Fin (2 ^ n), f i) := by
              simp [mul_sub, Finset.sum_sub_distrib]
    _ = (↑(2 ^ n))⁻¹ * (f w * (2 ^ n : ℝ) - ∑ i : Fin (2 ^ n), f i) := by
          rw [hsumDelta]
    _ = (↑(2 ^ n))⁻¹ * (f w * (2 ^ n : ℝ)) - (↑(2 ^ n))⁻¹ * ∑ i : Fin (2 ^ n), f i := by
          ring
    _ = f w - (↑(2 ^ n))⁻¹ * ∑ i : Fin (2 ^ n), f i := by
          field_simp [hN]
    _ = f w - muAvg n f := by rfl

/-- Centered score has zero total mass on the constant observable `1`. -/
theorem eta_one_eq_zero
    (n : ℕ) (w : Fin (2 ^ n)) :
    eta n w (fun _ => (1 : ℝ)) = 0 := by
  rw [eta_eq_eval_sub_avg]
  unfold muAvg
  simp

/-- Uniform finite-level mean of a real observable on level-`n` binary words. -/
def uniformMean {n : Nat} (f : BinaryWord n → ℝ) : ℝ :=
  (Fintype.card (BinaryWord n) : ℝ)⁻¹ * ∑ w : BinaryWord n, f w

/-- Centered finite-level score at a chosen binary word. -/
def scoreAt {n : Nat} (w : BinaryWord n) (f : BinaryWord n → ℝ) : ℝ :=
  f w - uniformMean f

/-- The finite level of binary words is nonempty. -/
theorem binaryWord_card_ne_zero (n : Nat) :
    (Fintype.card (BinaryWord n) : ℝ) ≠ 0 := by
  exact_mod_cast Fintype.card_ne_zero

/-- The uniform mean of the constant-one observable is one. -/
theorem uniformMean_one (n : Nat) :
    uniformMean (n := n) (fun _ : BinaryWord n => (1 : ℝ)) = 1 := by
  unfold uniformMean
  rw [sum_const]
  norm_num

/-- The finite centered score vanishes on the constant-one observable. -/
theorem scoreAt_one {n : Nat} (w : BinaryWord n) :
    scoreAt w (fun _ : BinaryWord n => (1 : ℝ)) = 0 := by
  simp [scoreAt, uniformMean_one]

/-- The uniform mean is additive. -/
theorem uniformMean_add {n : Nat} (f g : BinaryWord n → ℝ) :
    uniformMean (fun w => f w + g w) = uniformMean f + uniformMean g := by
  unfold uniformMean
  rw [sum_add_distrib]
  ring

/-- The uniform mean is homogeneous under real scaling. -/
theorem uniformMean_smul {n : Nat} (c : ℝ) (f : BinaryWord n → ℝ) :
    uniformMean (fun w => c * f w) = c * uniformMean f := by
  unfold uniformMean
  rw [← mul_sum]
  ring

/-- The finite centered score is additive. -/
theorem scoreAt_add {n : Nat} (w : BinaryWord n) (f g : BinaryWord n → ℝ) :
    scoreAt w (fun v => f v + g v) = scoreAt w f + scoreAt w g := by
  simp [scoreAt, uniformMean_add]
  ring

/-- The finite centered score is homogeneous under real scaling. -/
theorem scoreAt_smul {n : Nat} (w : BinaryWord n) (c : ℝ) (f : BinaryWord n → ℝ) :
    scoreAt w (fun v => c * f v) = c * scoreAt w f := by
  simp [scoreAt, uniformMean_smul]
  ring

/-- The finite centered score as a linear map on level-`n` observables. -/
def scoreLinear {n : Nat} (w : BinaryWord n) :
    (BinaryWord n → ℝ) →ₗ[ℝ] ℝ where
  toFun f := scoreAt w f
  map_add' f g := scoreAt_add w f g
  map_smul' c f := by
    exact scoreAt_smul w c f

/-- Readback for the finite centered-score linear map. -/
theorem scoreLinear_apply {n : Nat} (w : BinaryWord n) (f : BinaryWord n → ℝ) :
    scoreLinear w f = scoreAt w f :=
  rfl

/-- The finite centered-score linear map kills constants. -/
theorem scoreLinear_one {n : Nat} (w : BinaryWord n) :
    scoreLinear w (fun _ : BinaryWord n => (1 : ℝ)) = 0 := by
  exact scoreAt_one w

end

end InfoGeometry.Canonical.CantorModularScoreFunctional
