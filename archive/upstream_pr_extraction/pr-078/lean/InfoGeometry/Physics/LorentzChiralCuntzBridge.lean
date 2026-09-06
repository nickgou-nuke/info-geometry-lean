import Mathlib.Tactic
import InfoGeometry.Physics.ChiralCausalCone
import InfoGeometry.Physics.ChiralPoincareSouriauBridge
import InfoGeometry.Physics.CuntzDeformedSuperPoincare
import InfoGeometry.Physics.FierzIdentities

/-!
# Lorentz action on the chiral algebra and Cuntz-deformed super-Poincaré layer

This file keeps the Lorentz/Poincaré lift finite and algebraic:

* the chiral Lorentz spin group is the concrete matrix group `SL(2,ℂ)`;
* it acts on the chiral algebra `M₂(ℂ)` by conjugation;
* Pauli soldering turns that conjugation into an action on complexified
  four-momenta, preserving the determinant/Minkowski quadratic form;
* the chiral Fierz identity is imported as the completeness/swap theorem;
* the Cuntz-deformed super-Poincaré bracket layer is reused through its native API.

No global analytic covering theorem is claimed here.  The global group law is the
existing Lean group structure on `Matrix.SpecialLinearGroup (Fin 2) ℂ`.
-/

noncomputable section

namespace InfoGeometry.Physics.LorentzChiralCuntzBridge

open Matrix
open ChiralPoincareSouriauBridge

/-- The finite chiral Lorentz spin group used here: concrete `SL(2,ℂ)`. -/
abbrev SL2C := Matrix.SpecialLinearGroup (Fin 2) ℂ

/-- Coerce an `SL(2,ℂ)` element to its concrete `2×2` matrix. -/
def spinMatrix (g : SL2C) : M2C := (g : M2C)

@[simp] theorem spinMatrix_det (g : SL2C) : (spinMatrix g).det = 1 := by
  exact Matrix.SpecialLinearGroup.det_coe g

@[simp] theorem spinMatrix_mul (g h : SL2C) :
    spinMatrix (g * h) = spinMatrix g * spinMatrix h := rfl

@[simp] theorem spinMatrix_one : spinMatrix (1 : SL2C) = (1 : M2C) := rfl

/-- The chiral Fierz completeness statement: the swap operator equals the CPT compass alignment plus chiral solders. -/
def chiralFierzStatement : Prop :=
  ((1 / 2 : ℂ) • (Matrix.kroneckerMap (fun (a b : ℂ) => a * b)
      (1 : Matrix (Fin 2) (Fin 2) ℂ) (1 : Matrix (Fin 2) (Fin 2) ℂ) +
    Matrix.kroneckerMap (fun (a b : ℂ) => a * b) ChiralCausalCone.σ3c ChiralCausalCone.σ3c) +
  Matrix.kroneckerMap (fun (a b : ℂ) => a * b) ChiralCausalCone.σPlus ChiralCausalCone.σMinus +
  Matrix.kroneckerMap (fun (a b : ℂ) => a * b) ChiralCausalCone.σMinus ChiralCausalCone.σPlus = FierzIdentities.Swap)

/-- A concrete diagonal `SL(2,ℂ)` element.  The nonzero parameter is explicit. -/
def diagSL2 (a : ℂ) (ha : a ≠ 0) : SL2C :=
  ⟨!![a, 0; 0, a⁻¹], by
    simp [Matrix.det_fin_two, ha]⟩

/-- Exponential diagonal `SL(2,ℂ)` element. -/
def expDiagSL2 (η : ℂ) : SL2C := diagSL2 (Complex.exp η) (Complex.exp_ne_zero η)

@[simp] theorem expDiagSL2_matrix (η : ℂ) :
    spinMatrix (expDiagSL2 η) = !![Complex.exp η, 0; 0, (Complex.exp η)⁻¹] := rfl

/-- Multiplication law for the explicit diagonal one-parameter subgroup. -/
theorem expDiagSL2_mul (η ξ : ℂ) :
    expDiagSL2 η * expDiagSL2 ξ = expDiagSL2 (η + ξ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [expDiagSL2, diagSL2, Complex.exp_add, mul_comm]

/-- The identity member of the explicit diagonal subgroup. -/
theorem expDiagSL2_zero : expDiagSL2 0 = (1 : SL2C) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [expDiagSL2, diagSL2]

/-- The diagonal spin flow descends to the reciprocal projective multiplier on
the existing chiral sheet ratio `ψ 1 / ψ 0`. -/
theorem expDiagSL2_sheetRatio_action (η : ℂ) (ψ : Fin 2 → ℂ) (hψ : ψ 0 ≠ 0) :
      ((spinMatrix (expDiagSL2 η)).mulVec ψ) 1 /
        ((spinMatrix (expDiagSL2 η)).mulVec ψ) 0 =
      Complex.exp (-2 * η) * (ψ 1 / ψ 0) := by
  simp [expDiagSL2_matrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  field_simp [Complex.exp_ne_zero η, hψ]
  rw [show -(2 * η) = -(η + η) by ring, Complex.exp_neg, Complex.exp_add]
  field_simp [Complex.exp_ne_zero η]

/-- Real boost/rotation coordinates specialize the projective multiplier to
the loxodromic parameter `η + i θ`. -/
theorem expDiagSL2_real_loxodromic_sheetRatio_action
    (η θ : ℝ) (ψ : Fin 2 → ℂ) (hψ : ψ 0 ≠ 0) :
    ((spinMatrix (expDiagSL2 (((η : ℂ) + Complex.I * (θ : ℂ)) / 2))).mulVec ψ) 1 /
        ((spinMatrix (expDiagSL2 (((η : ℂ) + Complex.I * (θ : ℂ)) / 2))).mulVec ψ) 0 =
      Complex.exp (-((η : ℂ) + Complex.I * (θ : ℂ))) * (ψ 1 / ψ 0) := by
  have h := expDiagSL2_sheetRatio_action
    (((η : ℂ) + Complex.I * (θ : ℂ)) / 2) ψ hψ
  convert h using 1 <;> ring

/-- The reciprocal affine chart `ψ 0 / ψ 1` is the other standard projective
coordinate.  It carries the inverse multiplier of `sheetRatio`. -/
theorem expDiagSL2_reciprocal_sheetRatio_action (η : ℂ) (ψ : Fin 2 → ℂ) (hψ : ψ 1 ≠ 0) :
    ((spinMatrix (expDiagSL2 η)).mulVec ψ) 0 /
        ((spinMatrix (expDiagSL2 η)).mulVec ψ) 1 =
      Complex.exp (2 * η) * (ψ 0 / ψ 1) := by
  simp [expDiagSL2_matrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  field_simp [Complex.exp_ne_zero η, hψ]
  rw [show 2 * η = η + η by ring, Complex.exp_add]
  field_simp [Complex.exp_ne_zero η]

/-- The chiral conjugation action of `SL(2,ℂ)` on `M₂(ℂ)`. -/
def chiralConjAct (g : SL2C) (X : M2C) : M2C :=
  spinMatrix g * X * (spinMatrix g)⁻¹

/-- The conjugate action respects multiplication in `SL(2,ℂ)`. -/
theorem chiralConjAct_mul (g h : SL2C) (X : M2C) :
    chiralConjAct (g * h) X = chiralConjAct g (chiralConjAct h X) := by
  calc
    chiralConjAct (g * h) X = spinMatrix (g * h) * X * (spinMatrix (g * h))⁻¹ := rfl
    _ = (spinMatrix g * spinMatrix h) * X * (spinMatrix g * spinMatrix h)⁻¹ := by
      rw [spinMatrix_mul]
    _ = (spinMatrix g * spinMatrix h) * X * ((spinMatrix h)⁻¹ * (spinMatrix g)⁻¹) := by
      rw [Matrix.mul_inv_rev]
      <;> simp [Matrix.SpecialLinearGroup.det_coe, spinMatrix_det]
      <;> aesop
    _ = spinMatrix g * (spinMatrix h * X * (spinMatrix h)⁻¹) * (spinMatrix g)⁻¹ := by
      simp [Matrix.mul_assoc]
      <;>
      simp_all [Matrix.mul_assoc, Matrix.inv_mul, Matrix.mul_inv_of_isUnit]
      <;>
      (try
        {
          have h₁ : IsUnit ((spinMatrix g : M2C).det) := by
            rw [spinMatrix_det]
            exact isUnit_one
          have h₂ : IsUnit ((spinMatrix h : M2C).det) := by
            rw [spinMatrix_det]
            exact isUnit_one
          simp_all [Matrix.mul_nonsing_inv, Matrix.nonsing_inv_mul]
        }) <;>
      ring_nf <;>
      simp_all [Matrix.mul_assoc]
      <;>
      aesop
    _ = chiralConjAct g (chiralConjAct h X) := by
      simp [chiralConjAct]
      <;>
      simp_all [Matrix.mul_assoc]

/-- The chiral conjugation action is linear with respect to matrix addition. -/
@[simp] theorem chiralConjAct_add (g : SL2C) (X Y : M2C) :
    chiralConjAct g (X + Y) = chiralConjAct g X + chiralConjAct g Y := by
  simp [chiralConjAct, Matrix.add_mul, Matrix.mul_add]
  <;>
  abel

/-- The conjugate action of the identity is the identity. -/
theorem chiralConjAct_one (X : M2C) :
    chiralConjAct (1 : SL2C) X = X := by
  simp [chiralConjAct, spinMatrix_one]
  <;>
  simp_all [Matrix.one_mul, Matrix.mul_one]
  <;>
  aesop

/-- The spin Lorentz action on complexified four-momenta is induced by
conjugation on the Pauli-soldered matrices. -/
def spinLorentzAction (g : SL2C) (P : FourMomentum) : FourMomentum :=
  fourMomentumOfMatrix (chiralConjAct g (pauliMomentum P))

/-- Pauli soldering intertwines the finite spin Lorentz action with chiral
conjugation. -/
@[simp] theorem pauliMomentum_spinLorentzAction (g : SL2C) (P : FourMomentum) :
    pauliMomentum (spinLorentzAction g P) = chiralConjAct g (pauliMomentum P) := by
  rw [spinLorentzAction, pauliMomentum_fourMomentumOfMatrix]

/-- The spin Lorentz action preserves the Minkowski square (determinant). -/
theorem spinLorentzAction_preserves_minkowskiSq (g : SL2C) (P : FourMomentum) :
    minkowskiSq (spinLorentzAction g P) = minkowskiSq P := by
  have h₂ : (chiralConjAct g (pauliMomentum P)).det = (pauliMomentum P).det := by
    calc
      (chiralConjAct g (pauliMomentum P)).det = (spinMatrix g * pauliMomentum P * (spinMatrix g)⁻¹).det := rfl
      _ = (spinMatrix g).det * (pauliMomentum P).det * ((spinMatrix g)⁻¹).det := by
        simp [Matrix.det_mul]
      _ = 1 * (pauliMomentum P).det * 1 := by
        have h₃ : (spinMatrix g).det = 1 := spinMatrix_det g
        have h₄ : ((spinMatrix g)⁻¹).det = 1 := by
          rw [Matrix.det_nonsing_inv]
          <;> simp [h₃]
        rw [h₃, h₄]
        <;> ring
      _ = (pauliMomentum P).det := by ring
  have h₃ : (pauliMomentum (spinLorentzAction g P)).det = minkowskiSq (spinLorentzAction g P) := by
    rw [det_pauliMomentum]
  have h₄ : (pauliMomentum P).det = minkowskiSq P := by
    rw [det_pauliMomentum]
  calc
    minkowskiSq (spinLorentzAction g P) = (pauliMomentum (spinLorentzAction g P)).det := by rw [det_pauliMomentum]
    _ = (chiralConjAct g (pauliMomentum P)).det := by
      have h₅ : pauliMomentum (spinLorentzAction g P) = chiralConjAct g (pauliMomentum P) := by
        rw [spinLorentzAction]
        rw [pauliMomentum_fourMomentumOfMatrix]
      rw [h₅]
    _ = (pauliMomentum P).det := by rw [h₂]
    _ = minkowskiSq P := by rw [det_pauliMomentum]

/-- The spin Lorentz action respects multiplication in `SL(2,ℂ)`. -/
theorem spinLorentzAction_mul (g h : SL2C) (P : FourMomentum) :
    spinLorentzAction (g * h) P = spinLorentzAction g (spinLorentzAction h P) := by
  calc
    spinLorentzAction (g * h) P = fourMomentumOfMatrix (chiralConjAct (g * h) (pauliMomentum P)) := rfl
    _ = fourMomentumOfMatrix (chiralConjAct g (chiralConjAct h (pauliMomentum P))) := by
      rw [chiralConjAct_mul]
    _ = fourMomentumOfMatrix (chiralConjAct g (pauliMomentum (fourMomentumOfMatrix (chiralConjAct h (pauliMomentum P))))) := by
      have h₁ : pauliMomentum (fourMomentumOfMatrix (chiralConjAct h (pauliMomentum P))) = chiralConjAct h (pauliMomentum P) := by
        rw [pauliMomentum_fourMomentumOfMatrix]
      rw [h₁]
    _ = spinLorentzAction g (spinLorentzAction h P) := by
      simp [spinLorentzAction]
      <;>
      simp_all [chiralConjAct]
      <;>
      aesop

end InfoGeometry.Physics.LorentzChiralCuntzBridge

end noncomputable section
