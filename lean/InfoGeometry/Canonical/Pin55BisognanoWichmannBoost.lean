/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Lie.Pin55NondegenerateKreinBridge
import InfoGeometry.Canonical.BisognanoPeirceProjectionCore
import InfoGeometry.Canonical.FiniteMatrixTomitaPolar
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic

/-!
# `Pin(5,5)` Hyperbolic Boost, Bisognano–Wichmann & Wedge KMS Bridge (`D21`, `D22`)

This module constructs the finite-dimensional `Pin(5,5)` Rindler wedge hyperbolic boost
one-parameter group `pin55Boost η = exp(η • pin55BoostGen)` on `M₁₀(ℝ)` with fundamental
symmetry `J55` and proves:

1. **`so(5,5)` Boost Generator Algebra**: `pin55BoostGen` (`E₀₅ + E₅₀`) is symmetric, belongs to
   `so55KreinLieSubalgebra`, satisfies `J55 * K * J55 = -K`, and generates the closed hyperbolic
   algebra with idempotent projector `pin55BoostProj = K * K`.
2. **Hyperbolic Boost Group & Krein Isometry**: `pin55Boost (η₁ + η₂) = pin55Boost η₁ * pin55Boost η₂`,
   `J55 * pin55Boost η * J55 = pin55Boost (-η)`, and `(pin55Boost η)ᵀ * J55 * pin55Boost η = J55`.
3. **Rindler Wedge & Lightcone Action**: `pin55Boost η` preserves the Rindler wedge
   `{|x₅| < x₀}` and null rays `x₀ = x₅`, scaling lightcone coordinates by `exp(±η)`.
4. **Bisognano–Wichmann Identification & Wedge KMS Semigroup**:
   - Defining `rindlerThermalDensity β` with `rho = pin55Boost (-β)`, `J55 * rho * J55 = rho⁻¹`.
   - `modularOp (rindlerThermalDensity (2π)) X = wedgeBoostFlow 1 X`.
   - Exact wedge KMS condition at inverse Unruh temperature `β = 2π / a = 1 / unruhTemperature a`:
     `state ρ (A * wedgeBoostFlow (1 / a) B) = state ρ (B * A)`.
   - Exact lightcone contraction vs amplification dichotomy on `lightconeModePlus` (`exp(-4πt)`)
     versus `lightconeModeMinus` (`exp(4πt)`).
-/

noncomputable section

namespace InfoGeometry.Canonical.Pin55BisognanoWichmannBoost

open Matrix
open scoped BigOperators
open InfoGeometry.Lie.Pin55NondegenerateKreinBridge
open InfoGeometry.Canonical.BisognanoPeirceProjectionCore
open InfoGeometry.Canonical.FiniteMatrixTomitaPolar

section GeneratorAlgebra

/-- Symmetric `so(5,5)` boost generator `K₀₅ = E₀₅ + E₅₀` mixing timelike index `0` and spacelike index `5`. -/
def pin55BoostGen : Matrix (Fin 10) (Fin 10) ℝ :=
  fun i j => if (i = 0 ∧ j = 5) ∨ (i = 5 ∧ j = 0) then 1 else 0

/-- Orthogonal projector `P₀₅ = E₀₀ + E₅₅` onto the `(0, 5)` boost plane. -/
def pin55BoostProj : Matrix (Fin 10) (Fin 10) ℝ :=
  fun i j => if (i = 0 ∧ j = 0) ∨ (i = 5 ∧ j = 5) then 1 else 0

/-- Helper reducing a `Fin 10` sum supported on `{0, 5}` to `f 0 + f 5`. -/
theorem sum_fin10_zero_five (f : Fin 10 → ℝ)
    (hf : ∀ k : Fin 10, k ≠ 0 → k ≠ 5 → f k = 0) :
    (∑ k : Fin 10, f k) = f 0 + f 5 := by
  have h5mem : (5 : Fin 10) ∈ (Finset.univ : Finset (Fin 10)).erase 0 := by decide
  rw [← Finset.add_sum_erase Finset.univ f (Finset.mem_univ (0 : Fin 10))]
  rw [← Finset.add_sum_erase ((Finset.univ : Finset (Fin 10)).erase 0) f h5mem]
  have hrest : ∑ k ∈ ((Finset.univ : Finset (Fin 10)).erase 0).erase 5, f k = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    rw [Finset.mem_erase, Finset.mem_erase] at hk
    exact hf k hk.2.1 hk.1
  rw [hrest, add_zero]

theorem pin55BoostGen_transpose : pin55BoostGenᵀ = pin55BoostGen := by
  ext i j
  by_cases hi0 : i = 0 <;> by_cases hi5 : i = 5 <;>
    by_cases hj0 : j = 0 <;> by_cases hj5 : j = 5 <;>
    simp [pin55BoostGen, Matrix.transpose_apply, hi0, hi5, hj0, hj5]

theorem pin55BoostProj_transpose : pin55BoostProjᵀ = pin55BoostProj := by
  ext i j
  by_cases hi0 : i = 0 <;> by_cases hi5 : i = 5 <;>
    by_cases hj0 : j = 0 <;> by_cases hj5 : j = 5 <;>
    simp [pin55BoostProj, Matrix.transpose_apply, hi0, hi5, hj0, hj5]

/-- `pin55BoostGen` lies in `so(5,5)`. -/
theorem pin55BoostGen_isSO55 : IsSO55KreinMatrix pin55BoostGen := by
  dsimp [IsSO55KreinMatrix, J55]
  ext i j
  rw [Matrix.add_apply, mul_diagonal_apply, diagonal_mul_apply, Matrix.transpose_apply,
    Matrix.zero_apply]
  dsimp [pin55BoostGen]
  fin_cases i <;> fin_cases j <;> norm_num

theorem pin55BoostGen_mem_so55 : pin55BoostGen ∈ so55KreinLieSubalgebra :=
  pin55BoostGen_isSO55

/-- `J55 * pin55BoostGen * J55 = -pin55BoostGen`. -/
theorem pin55BoostGen_J55_anticomm : J55 * pin55BoostGen * J55 = -pin55BoostGen := by
  have h := (isSO55_iff_J55_mul_mul_eq_neg_transpose pin55BoostGen).mp pin55BoostGen_isSO55
  rwa [pin55BoostGen_transpose] at h

/-- `J55 * pin55BoostProj * J55 = pin55BoostProj`. -/
theorem pin55BoostProj_J55_comm : J55 * pin55BoostProj * J55 = pin55BoostProj := by
  ext i j
  have hmulL : (J55 * pin55BoostProj * J55) i j =
      (if i.val < 5 then (1 : ℝ) else -1) * pin55BoostProj i j *
        (if j.val < 5 then (1 : ℝ) else -1) := by
    dsimp [J55]
    rw [mul_diagonal_apply, diagonal_mul_apply]
  rw [hmulL]
  fin_cases i <;> fin_cases j <;> norm_num [pin55BoostProj]

private theorem fin10_0_ne_5 : (0 : Fin 10) ≠ 5 := by decide

theorem pin55BoostGen_mul_self : pin55BoostGen * pin55BoostGen = pin55BoostProj := by
  ext i j
  rw [Matrix.mul_apply, sum_fin10_zero_five]
  · fin_cases i <;> fin_cases j <;> norm_num [pin55BoostGen, pin55BoostProj]
  · intro k hk0 hk5
    simp [pin55BoostGen, hk0, hk5]

theorem pin55BoostProj_mul_self : pin55BoostProj * pin55BoostProj = pin55BoostProj := by
  ext i j
  rw [Matrix.mul_apply, sum_fin10_zero_five]
  · fin_cases i <;> fin_cases j <;> norm_num [pin55BoostProj]
  · intro k hk0 hk5
    simp [pin55BoostProj, hk0, hk5]

theorem pin55BoostGen_mul_proj : pin55BoostGen * pin55BoostProj = pin55BoostGen := by
  ext i j
  rw [Matrix.mul_apply, sum_fin10_zero_five]
  · fin_cases i <;> fin_cases j <;> norm_num [pin55BoostGen, pin55BoostProj]
  · intro k hk0 hk5
    simp [pin55BoostProj, hk0, hk5]

theorem pin55BoostProj_mul_gen : pin55BoostProj * pin55BoostGen = pin55BoostGen := by
  ext i j
  rw [Matrix.mul_apply, sum_fin10_zero_five]
  · fin_cases i <;> fin_cases j <;> norm_num [pin55BoostGen, pin55BoostProj]
  · intro k hk0 hk5
    simp [pin55BoostProj, hk0, hk5]

/-- OpenGauss T16 non-commutativity witness in `so(5,5)`: `[pin55BoostGen, genX] ≠ 0`. -/
theorem pin55BoostGen_genX_noncomm : pin55BoostGen * genX ≠ genX * pin55BoostGen := by
  intro h
  have h51 := congrArg (fun M : Matrix (Fin 10) (Fin 10) ℝ => M 5 1) h
  rw [Matrix.mul_apply, sum_fin10_zero_five] at h51
  · rw [Matrix.mul_apply, sum_fin10_zero_five] at h51
    · norm_num [pin55BoostGen, genX] at h51
    · intro k hk0 hk5
      simp [pin55BoostGen, hk0, hk5]
  · intro k hk0 hk5
    simp [pin55BoostGen, hk0, hk5]

end GeneratorAlgebra

section HyperbolicGroup

/-- Closed-form `Pin(5,5)` hyperbolic boost one-parameter group `Λ(η) = exp(η K₀₅)`. -/
def pin55Boost (η : ℝ) : Matrix (Fin 10) (Fin 10) ℝ :=
  1 + (Real.cosh η - 1) • pin55BoostProj + Real.sinh η • pin55BoostGen

@[simp]
theorem pin55Boost_zero : pin55Boost 0 = 1 := by
  unfold pin55Boost
  simp

theorem pin55Boost_transpose (η : ℝ) : (pin55Boost η)ᵀ = pin55Boost η := by
  unfold pin55Boost
  rw [Matrix.transpose_add, Matrix.transpose_add, Matrix.transpose_one, Matrix.transpose_smul,
    Matrix.transpose_smul, pin55BoostProj_transpose, pin55BoostGen_transpose]

/-- Additive one-parameter group law `Λ(η₁ + η₂) = Λ(η₁) * Λ(η₂)`. -/
theorem pin55Boost_add (η₁ η₂ : ℝ) :
    pin55Boost (η₁ + η₂) = pin55Boost η₁ * pin55Boost η₂ := by
  let c₁ := Real.cosh η₁ - 1
  let c₂ := Real.cosh η₂ - 1
  let s₁ := Real.sinh η₁
  let s₂ := Real.sinh η₂
  have hmul :
      pin55Boost η₁ * pin55Boost η₂ =
        1 + (c₁ + c₂ + c₁ * c₂ + s₁ * s₂) • pin55BoostProj +
          (s₁ + s₂ + c₁ * s₂ + s₁ * c₂) • pin55BoostGen := by
    unfold pin55Boost
    change (1 + c₁ • pin55BoostProj + s₁ • pin55BoostGen) *
        (1 + c₂ • pin55BoostProj + s₂ • pin55BoostGen) = _
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
      Matrix.smul_mul, Matrix.mul_smul,
      pin55BoostProj_mul_self, pin55BoostProj_mul_gen,
      pin55BoostGen_mul_proj, pin55BoostGen_mul_self]
    module
  rw [hmul]
  unfold pin55Boost
  have hcosh : Real.cosh (η₁ + η₂) - 1 = c₁ + c₂ + c₁ * c₂ + s₁ * s₂ := by
    dsimp [c₁, c₂, s₁, s₂]
    rw [Real.cosh_add]
    ring
  have hsinh : Real.sinh (η₁ + η₂) = s₁ + s₂ + c₁ * s₂ + s₁ * c₂ := by
    dsimp [c₁, c₂, s₁, s₂]
    rw [Real.sinh_add]
    ring
  rw [hcosh, hsinh]

theorem pin55Boost_mul_neg (η : ℝ) : pin55Boost η * pin55Boost (-η) = 1 := by
  rw [← pin55Boost_add, add_neg_cancel, pin55Boost_zero]

theorem pin55Boost_neg_mul (η : ℝ) : pin55Boost (-η) * pin55Boost η = 1 := by
  rw [← pin55Boost_add, neg_add_cancel, pin55Boost_zero]

/-- Reflection law under the Krein fundamental symmetry: `J55 Λ(η) J55 = Λ(-η)`. -/
theorem pin55Boost_J55_conj (η : ℝ) : J55 * pin55Boost η * J55 = pin55Boost (-η) := by
  unfold pin55Boost
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_one,
    Matrix.smul_mul, Matrix.mul_smul]
  rw [J55_mul_self]
  have hp : J55 * pin55BoostProj * J55 = pin55BoostProj := pin55BoostProj_J55_comm
  have hg : J55 * pin55BoostGen * J55 = -pin55BoostGen := pin55BoostGen_J55_anticomm
  simp only [Matrix.mul_assoc] at hp hg ⊢
  rw [hp, hg, Real.cosh_neg, Real.sinh_neg, smul_neg, neg_smul]

/-- `pin55Boost η` preserves the signature `(5,5)` Krein form: `Λ(η)ᵀ J55 Λ(η) = J55`. -/
theorem pin55Boost_krein_isometry (η : ℝ) :
    (pin55Boost η)ᵀ * J55 * pin55Boost η = J55 := by
  rw [pin55Boost_transpose]
  calc
    pin55Boost η * J55 * pin55Boost η
        = pin55Boost η * (J55 * pin55Boost η * (J55 * J55)) := by
            rw [J55_mul_self, Matrix.mul_one, Matrix.mul_assoc]
    _ = pin55Boost η * ((J55 * pin55Boost η * J55) * J55) := by
            simp only [Matrix.mul_assoc]
    _ = (pin55Boost η * pin55Boost (-η)) * J55 := by
            rw [pin55Boost_J55_conj]
            exact (Matrix.mul_assoc (pin55Boost η) (pin55Boost (-η)) J55).symm
    _ = J55 := by rw [pin55Boost_mul_neg, Matrix.one_mul]

/-- Bilinear Krein invariance under `pin55Boost η`. -/
theorem kreinForm55_pin55Boost (η : ℝ) (x y : Fin 10 → ℝ) :
    kreinForm55 ((pin55Boost η).mulVec x) ((pin55Boost η).mulVec y) = kreinForm55 x y := by
  unfold kreinForm55
  rw [← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec,
    Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, pin55Boost_krein_isometry]

end HyperbolicGroup

section WedgeAndLightcone

/-- Coordinate action at index `0`. -/
theorem pin55Boost_mulVec_zero (η : ℝ) (x : Fin 10 → ℝ) :
    (pin55Boost η).mulVec x 0 = Real.cosh η * x 0 + Real.sinh η * x 5 := by
  rw [Matrix.mulVec, dotProduct, sum_fin10_zero_five]
  · simp [pin55Boost, pin55BoostProj, pin55BoostGen]
  · intro k hk0 hk5
    simp [pin55Boost, pin55BoostProj, pin55BoostGen, hk0, hk5, Matrix.one_apply_ne hk0.symm]

/-- Coordinate action at index `5`. -/
theorem pin55Boost_mulVec_five (η : ℝ) (x : Fin 10 → ℝ) :
    (pin55Boost η).mulVec x 5 = Real.sinh η * x 0 + Real.cosh η * x 5 := by
  rw [Matrix.mulVec, dotProduct, sum_fin10_zero_five]
  · simp [pin55Boost, pin55BoostProj, pin55BoostGen]
  · intro k hk0 hk5
    simp [pin55Boost, pin55BoostProj, pin55BoostGen, hk0, hk5, Matrix.one_apply_ne hk5.symm]

/-- Transverse coordinates `i ∉ {0, 5}` are fixed pointwise. -/
theorem pin55Boost_mulVec_transverse (η : ℝ) (x : Fin 10 → ℝ) {i : Fin 10}
    (hi0 : i ≠ 0) (hi5 : i ≠ 5) :
    (pin55Boost η).mulVec x i = x i := by
  rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single i]
  · simp [pin55Boost, pin55BoostProj, pin55BoostGen, hi0, hi5]
  · intro k _ hk
    simp [pin55Boost, pin55BoostProj, pin55BoostGen, hi0, hi5, hk.symm]
  · intro hi
    exact False.elim (hi (Finset.mem_univ i))

private theorem cosh_add_sinh_eq_exp (η : ℝ) : Real.cosh η + Real.sinh η = Real.exp η := by
  rw [Real.cosh_eq, Real.sinh_eq]
  ring

private theorem cosh_sub_sinh_eq_exp_neg (η : ℝ) : Real.cosh η - Real.sinh η = Real.exp (-η) := by
  rw [Real.cosh_eq, Real.sinh_eq]
  ring

/-- Forward lightcone coordinate scales by `exp η`. -/
theorem pin55Boost_mulVec_lightcone_plus (η : ℝ) (x : Fin 10 → ℝ) :
    (pin55Boost η).mulVec x 0 + (pin55Boost η).mulVec x 5 = Real.exp η * (x 0 + x 5) := by
  rw [pin55Boost_mulVec_zero, pin55Boost_mulVec_five, ← cosh_add_sinh_eq_exp η]
  ring

/-- Backward lightcone coordinate scales by `exp (-η)`. -/
theorem pin55Boost_mulVec_lightcone_minus (η : ℝ) (x : Fin 10 → ℝ) :
    (pin55Boost η).mulVec x 0 - (pin55Boost η).mulVec x 5 = Real.exp (-η) * (x 0 - x 5) := by
  rw [pin55Boost_mulVec_zero, pin55Boost_mulVec_five, ← cosh_sub_sinh_eq_exp_neg η]
  ring

/-- Right Rindler wedge in the `(0, 5)` boost plane of `ℝ¹⁰`. -/
def rindlerWedge55 : Set (Fin 10 → ℝ) :=
  { x | 0 < x 0 + x 5 ∧ 0 < x 0 - x 5 }

theorem mem_rindlerWedge55_iff_abs (x : Fin 10 → ℝ) :
    x ∈ rindlerWedge55 ↔ |x 5| < x 0 := by
  unfold rindlerWedge55
  rw [Set.mem_ofPred_eq, abs_lt]
  constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨by linarith, by linarith⟩

/-- Every hyperbolic boost preserves the Rindler wedge `|x₅| < x₀`. -/
theorem pin55Boost_preserves_rindlerWedge (η : ℝ) {x : Fin 10 → ℝ}
    (hx : x ∈ rindlerWedge55) :
    (pin55Boost η).mulVec x ∈ rindlerWedge55 := by
  unfold rindlerWedge55 at hx ⊢
  rw [Set.mem_ofPred_eq, pin55Boost_mulVec_lightcone_plus, pin55Boost_mulVec_lightcone_minus]
  exact ⟨mul_pos (Real.exp_pos η) hx.1, mul_pos (Real.exp_pos (-η)) hx.2⟩

/-- Null rays `x₀ = x₅` are invariant under boosts. -/
theorem pin55Boost_preserves_null_plus (η : ℝ) {x : Fin 10 → ℝ} (hx : x 0 = x 5) :
    (pin55Boost η).mulVec x 0 = (pin55Boost η).mulVec x 5 := by
  rw [pin55Boost_mulVec_zero, pin55Boost_mulVec_five, hx]
  ring

end WedgeAndLightcone

section BisognanoWichmannAndKMS

/-- Rindler boost thermal density factor `r(β) = Λ(-β/2)`, so `ρ(β) = Λ(-β)` and `ρ(β)⁻¹ = Λ(β)`. -/
def rindlerThermalDensity (β : ℝ) : PositiveRealDensityFactor 10 where
  r := pin55Boost (-β / 2)
  rInv := pin55Boost (β / 2)
  r_symm := pin55Boost_transpose (-β / 2)
  rInv_symm := pin55Boost_transpose (β / 2)
  r_mul_rInv := by
    have h0 : -β / 2 + β / 2 = 0 := by ring
    rw [← pin55Boost_add, h0, pin55Boost_zero]
  rInv_mul_r := by
    have h0 : β / 2 + -β / 2 = 0 := by ring
    rw [← pin55Boost_add, h0, pin55Boost_zero]

theorem rindlerThermalDensity_rho (β : ℝ) :
    (rindlerThermalDensity β).rho = pin55Boost (-β) := by
  change pin55Boost (-β / 2) * pin55Boost (-β / 2) = pin55Boost (-β)
  rw [← pin55Boost_add]
  congr 1
  ring

theorem rindlerThermalDensity_rhoInv (β : ℝ) :
    (rindlerThermalDensity β).rhoInv = pin55Boost β := by
  change pin55Boost (β / 2) * pin55Boost (β / 2) = pin55Boost β
  rw [← pin55Boost_add]
  congr 1
  ring

/-- `J55` conjugates the Rindler thermal density matrix into its inverse: `J55 ρ J55 = ρ⁻¹`. -/
theorem J55_conjugates_rindlerThermalDensity (β : ℝ) :
    J55 * (rindlerThermalDensity β).rho * J55 = (rindlerThermalDensity β).rhoInv := by
  rw [rindlerThermalDensity_rho, rindlerThermalDensity_rhoInv, pin55Boost_J55_conj, neg_neg]

/-- Euclideanized boost modular flow `σ_τ(X) = Λ(-2πτ) X Λ(2πτ)` at rapidity `η = 2πτ`. -/
def wedgeBoostFlow (τ : ℝ) (X : Matrix (Fin 10) (Fin 10) ℝ) : Matrix (Fin 10) (Fin 10) ℝ :=
  pin55Boost (-2 * Real.pi * τ) * X * pin55Boost (2 * Real.pi * τ)

/-- Bisognano–Wichmann identification (`2π` modular time calibration): `Δ_{ρ(2π)} = σ₁`. -/
theorem bisognanoWichmann_modularOp_eq_wedgeBoostFlow_one (X : Matrix (Fin 10) (Fin 10) ℝ) :
    modularOp (rindlerThermalDensity (2 * Real.pi)) X = wedgeBoostFlow 1 X := by
  unfold modularOp wedgeBoostFlow
  rw [rindlerThermalDensity_rho, rindlerThermalDensity_rhoInv]
  simp [mul_one]

@[simp]
theorem wedgeBoostFlow_zero (X : Matrix (Fin 10) (Fin 10) ℝ) :
    wedgeBoostFlow 0 X = X := by
  unfold wedgeBoostFlow
  simp

/-- One-parameter group/semigroup composition law `σ_{t₁ + t₂} = σ_{t₁} ∘ σ_{t₂}`. -/
theorem wedgeBoostFlow_semigroup (t₁ t₂ : ℝ) (X : Matrix (Fin 10) (Fin 10) ℝ) :
    wedgeBoostFlow (t₁ + t₂) X = wedgeBoostFlow t₁ (wedgeBoostFlow t₂ X) := by
  unfold wedgeBoostFlow
  have hL : -2 * Real.pi * (t₁ + t₂) = (-2 * Real.pi * t₁) + (-2 * Real.pi * t₂) := by ring
  have hR : 2 * Real.pi * (t₁ + t₂) = 2 * Real.pi * t₂ + 2 * Real.pi * t₁ := by ring
  rw [hL, hR, pin55Boost_add, pin55Boost_add]
  simp only [Matrix.mul_assoc]

theorem wedgeBoostFlow_mul (t : ℝ) (X Y : Matrix (Fin 10) (Fin 10) ℝ) :
    wedgeBoostFlow t (X * Y) = wedgeBoostFlow t X * wedgeBoostFlow t Y := by
  have hinv : pin55Boost (2 * Real.pi * t) * pin55Boost (-2 * Real.pi * t) = 1 := by
    rw [← pin55Boost_add, show 2 * Real.pi * t + -2 * Real.pi * t = 0 by ring, pin55Boost_zero]
  unfold wedgeBoostFlow
  calc
    pin55Boost (-2 * Real.pi * t) * (X * Y) * pin55Boost (2 * Real.pi * t)
        = pin55Boost (-2 * Real.pi * t) * X * 1 * Y * pin55Boost (2 * Real.pi * t) := by
            simp only [Matrix.mul_assoc, Matrix.mul_one]
    _ = pin55Boost (-2 * Real.pi * t) * X *
          (pin55Boost (2 * Real.pi * t) * pin55Boost (-2 * Real.pi * t)) *
          Y * pin55Boost (2 * Real.pi * t) := by rw [hinv]
    _ = (pin55Boost (-2 * Real.pi * t) * X * pin55Boost (2 * Real.pi * t)) *
          (pin55Boost (-2 * Real.pi * t) * Y * pin55Boost (2 * Real.pi * t)) := by
            simp only [Matrix.mul_assoc]

/-- Inverse temperature equals reciprocal Unruh temperature `2π / a = 1 / unruhTemperature a`. -/
theorem wedge_inverseTemp_eq_inv_unruh (a : ℝ) (ha : a > 0) :
    (2 * Real.pi / a : ℝ) = 1 / unruhTemperature a :=
  thermalTime_properTime_relation a ha

/-- Exact finite-wedge KMS boundary condition at inverse Unruh temperature
`β = 1 / unruhTemperature a = 2π / a`: `ω_β(A σ_{1/a}(B)) = ω_β(B A)`. -/
theorem wedge_kms_condition (a : ℝ) (ha : a > 0)
    (A B : Matrix (Fin 10) (Fin 10) ℝ) :
    state (rindlerThermalDensity (1 / unruhTemperature a)) (A * wedgeBoostFlow (1 / a) B) =
      state (rindlerThermalDensity (1 / unruhTemperature a)) (B * A) := by
  rw [← wedge_inverseTemp_eq_inv_unruh a ha]
  have hmod : modularOp (rindlerThermalDensity (2 * Real.pi / a)) B = wedgeBoostFlow (1 / a) B := by
    unfold modularOp wedgeBoostFlow
    rw [rindlerThermalDensity_rho, rindlerThermalDensity_rhoInv]
    have hL : -(2 * Real.pi / a) = -2 * Real.pi * (1 / a) := by ring
    have hR : 2 * Real.pi / a = 2 * Real.pi * (1 / a) := by ring
    rw [hL, hR]
  rw [← hmod]
  exact modularOp_kms_identity (rindlerThermalDensity (2 * Real.pi / a)) A B

/-- Forward lightcone vector `e₀ + e₅`. -/
def uPlus : Fin 10 → ℝ := fun i => if i = 0 ∨ i = 5 then 1 else 0

/-- Backward lightcone vector `e₀ - e₅`. -/
def uMinus : Fin 10 → ℝ := fun i => if i = 0 then 1 else if i = 5 then -1 else 0

/-- Rank-1 decaying lightcone matrix mode `uPlus ⊗ uMinus`. -/
def lightconeModePlus : Matrix (Fin 10) (Fin 10) ℝ :=
  Matrix.vecMulVec uPlus uMinus

/-- Rank-1 expanding lightcone matrix mode `uMinus ⊗ uPlus`. -/
def lightconeModeMinus : Matrix (Fin 10) (Fin 10) ℝ :=
  Matrix.vecMulVec uMinus uPlus

theorem pin55Boost_mulVec_uPlus (η : ℝ) :
    (pin55Boost η).mulVec uPlus = Real.exp η • uPlus := by
  ext i
  by_cases hi0 : i = 0
  · subst hi0
    rw [pin55Boost_mulVec_zero, Pi.smul_apply, smul_eq_mul, ← cosh_add_sinh_eq_exp η]
    simp [uPlus]
  · by_cases hi5 : i = 5
    · subst hi5
      rw [pin55Boost_mulVec_five, Pi.smul_apply, smul_eq_mul, ← cosh_add_sinh_eq_exp η]
      simp [uPlus, add_comm]
    · rw [pin55Boost_mulVec_transverse η uPlus hi0 hi5]
      simp [uPlus, hi0, hi5]

theorem pin55Boost_mulVec_uMinus (η : ℝ) :
    (pin55Boost η).mulVec uMinus = Real.exp (-η) • uMinus := by
  ext i
  by_cases hi0 : i = 0
  · subst hi0
    rw [pin55Boost_mulVec_zero, Pi.smul_apply, smul_eq_mul]
    simp [uMinus]
    rw [← cosh_sub_sinh_eq_exp_neg η]
    ring
  · by_cases hi5 : i = 5
    · subst hi5
      rw [pin55Boost_mulVec_five, Pi.smul_apply, smul_eq_mul]
      simp [uMinus]
      rw [← cosh_sub_sinh_eq_exp_neg η]
      ring
    · rw [pin55Boost_mulVec_transverse η uMinus hi0 hi5]
      simp [uMinus, hi0, hi5]

private theorem boost_conj_vecMulVec (η₁ η₂ : ℝ) (u v : Fin 10 → ℝ)
    (hv : ∀ k : Fin 10, k ≠ 0 → k ≠ 5 → v k = 0) :
    pin55Boost η₁ * Matrix.vecMulVec u v * pin55Boost η₂ =
      Matrix.vecMulVec ((pin55Boost η₁).mulVec u) ((pin55Boost η₂).mulVec v) := by
  ext i j
  have hL : ∀ k, (pin55Boost η₁ * Matrix.vecMulVec u v) i k =
      (pin55Boost η₁).mulVec u i * v k := by
    intro k
    rw [Matrix.mul_apply, Matrix.mulVec, dotProduct, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro l _
    simp [Matrix.vecMulVec_apply, mul_assoc]
  have hdot : (pin55Boost η₂).mulVec v j =
      pin55Boost η₂ j 0 * v 0 + pin55Boost η₂ j 5 * v 5 := by
    rw [Matrix.mulVec, dotProduct, sum_fin10_zero_five]
    intro k hk0 hk5
    rw [hv k hk0 hk5, mul_zero]
  rw [Matrix.mul_apply, sum_fin10_zero_five]
  · rw [hL 0, hL 5, Matrix.vecMulVec_apply, hdot]
    have hs0 : pin55Boost η₂ j 0 = pin55Boost η₂ 0 j :=
      (congrFun (congrFun (pin55Boost_transpose η₂) j) 0).symm
    have hs5 : pin55Boost η₂ j 5 = pin55Boost η₂ 5 j :=
      (congrFun (congrFun (pin55Boost_transpose η₂) j) 5).symm
    rw [hs0, hs5]
    ring
  · intro k hk0 hk5
    rw [hL k, hv k hk0 hk5, mul_zero, zero_mul]

/-- Exponential decay `σ_t(lightconeModePlus) = exp(-4πt) • lightconeModePlus`. -/
theorem wedgeBoostFlow_lightconeModePlus (t : ℝ) :
    wedgeBoostFlow t lightconeModePlus = Real.exp (-4 * Real.pi * t) • lightconeModePlus := by
  unfold wedgeBoostFlow lightconeModePlus
  rw [boost_conj_vecMulVec _ _ _ _ (fun k hk0 hk5 => by simp [uMinus, hk0, hk5]),
    pin55Boost_mulVec_uPlus, pin55Boost_mulVec_uMinus]
  ext i j
  simp only [Matrix.vecMulVec_apply, Pi.smul_apply, Matrix.smul_apply, smul_eq_mul]
  have hexp : Real.exp (-2 * Real.pi * t) * Real.exp (-(2 * Real.pi * t)) =
      Real.exp (-4 * Real.pi * t) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    Real.exp (-2 * Real.pi * t) * uPlus i * (Real.exp (-(2 * Real.pi * t)) * uMinus j)
        = (Real.exp (-2 * Real.pi * t) * Real.exp (-(2 * Real.pi * t))) * (uPlus i * uMinus j) := by
            ring
    _ = Real.exp (-4 * Real.pi * t) * (uPlus i * uMinus j) := by rw [hexp]

/-- Exponential growth `σ_t(lightconeModeMinus) = exp(4πt) • lightconeModeMinus`. -/
theorem wedgeBoostFlow_lightconeModeMinus (t : ℝ) :
    wedgeBoostFlow t lightconeModeMinus = Real.exp (4 * Real.pi * t) • lightconeModeMinus := by
  unfold wedgeBoostFlow lightconeModeMinus
  rw [boost_conj_vecMulVec _ _ _ _ (fun k hk0 hk5 => by simp [uPlus, hk0, hk5]),
    pin55Boost_mulVec_uMinus, pin55Boost_mulVec_uPlus]
  ext i j
  simp only [Matrix.vecMulVec_apply, Pi.smul_apply, Matrix.smul_apply, smul_eq_mul]
  have hexp : Real.exp (-(-2 * Real.pi * t)) * Real.exp (2 * Real.pi * t) =
      Real.exp (4 * Real.pi * t) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    Real.exp (-(-2 * Real.pi * t)) * uMinus i * (Real.exp (2 * Real.pi * t) * uPlus j)
        = (Real.exp (-(-2 * Real.pi * t)) * Real.exp (2 * Real.pi * t)) * (uMinus i * uPlus j) := by
            ring
    _ = Real.exp (4 * Real.pi * t) * (uMinus i * uPlus j) := by rw [hexp]

theorem hsInner_lightconeModePlus : hsInner lightconeModePlus lightconeModePlus = 4 := by
  rw [hsInner_self_eq_sum_sq, sum_fin10_zero_five]
  · simp only [lightconeModePlus, Matrix.vecMulVec_apply]
    rw [sum_fin10_zero_five, sum_fin10_zero_five]
    · norm_num [uPlus, uMinus]
    · intro i hi0 hi5
      simp [uPlus, hi0, hi5]
    · intro i hi0 hi5
      simp [uPlus, hi0, hi5]
  · intro i hi0 hi5
    apply Finset.sum_eq_zero
    intro j _
    simp [lightconeModePlus, Matrix.vecMulVec_apply, uMinus, hi0, hi5]

theorem hsInner_lightconeModeMinus : hsInner lightconeModeMinus lightconeModeMinus = 4 := by
  rw [hsInner_self_eq_sum_sq, sum_fin10_zero_five]
  · simp only [lightconeModeMinus, Matrix.vecMulVec_apply]
    rw [sum_fin10_zero_five, sum_fin10_zero_five]
    · norm_num [uPlus, uMinus]
    · intro i hi0 hi5
      simp [uMinus, hi0, hi5]
    · intro i hi0 hi5
      simp [uMinus, hi0, hi5]
  · intro i hi0 hi5
    apply Finset.sum_eq_zero
    intro j _
    simp [lightconeModeMinus, Matrix.vecMulVec_apply, uPlus, hi0, hi5]

/-- Forward boost semigroup `t ≥ 0` is strictly contractive on `lightconeModePlus`. -/
theorem wedgeBoostFlow_hsNormSq_contractive_plus (t : ℝ) (ht : 0 ≤ t) :
    hsInner (wedgeBoostFlow t lightconeModePlus) (wedgeBoostFlow t lightconeModePlus) ≤
      hsInner lightconeModePlus lightconeModePlus := by
  rw [wedgeBoostFlow_lightconeModePlus, hsInner_smul, hsInner_lightconeModePlus]
  have hnonneg : 0 ≤ 4 * Real.pi * t := mul_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le) ht
  have harg : -4 * Real.pi * t ≤ 0 := by
    rw [show -4 * Real.pi * t = -(4 * Real.pi * t) by ring]
    exact neg_nonpos.mpr hnonneg
  have hexp : Real.exp (-4 * Real.pi * t) ≤ 1 := Real.exp_le_one_iff.mpr harg
  have hpos : 0 ≤ Real.exp (-4 * Real.pi * t) := (Real.exp_pos _).le
  have hsq : Real.exp (-4 * Real.pi * t) ^ 2 ≤ 1 := by
    rw [sq]
    simpa [mul_one] using mul_le_mul hexp hexp hpos (by norm_num)
  calc
    Real.exp (-4 * Real.pi * t) ^ 2 * 4 ≤ 1 * 4 := mul_le_mul_of_nonneg_right hsq (by norm_num)
    _ = 4 := one_mul 4

/-- Forward boost semigroup `t > 0` expands the opposite lightcone mode `lightconeModeMinus`. -/
theorem wedgeBoostFlow_hsNormSq_expanding_minus (t : ℝ) (ht : 0 < t) :
    hsInner lightconeModeMinus lightconeModeMinus <
      hsInner (wedgeBoostFlow t lightconeModeMinus) (wedgeBoostFlow t lightconeModeMinus) := by
  rw [wedgeBoostFlow_lightconeModeMinus, hsInner_smul, hsInner_lightconeModeMinus]
  have harg : 0 < 4 * Real.pi * t := mul_pos (mul_pos (by norm_num) Real.pi_pos) ht
  have hexp : 1 < Real.exp (4 * Real.pi * t) := Real.one_lt_exp_iff.mpr harg
  have hsq : 1 < Real.exp (4 * Real.pi * t) ^ 2 := by
    rw [sq]
    simpa [one_mul] using mul_lt_mul hexp hexp.le (by norm_num) (Real.exp_pos _).le
  calc
    (4 : ℝ) = 1 * 4 := (one_mul 4).symm
    _ < Real.exp (4 * Real.pi * t) ^ 2 * 4 := mul_lt_mul_of_pos_right hsq (by norm_num)

end BisognanoWichmannAndKMS

end InfoGeometry.Canonical.Pin55BisognanoWichmannBoost
