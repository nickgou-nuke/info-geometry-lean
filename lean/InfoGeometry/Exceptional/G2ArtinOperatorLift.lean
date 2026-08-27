/- SPDX-License-Identifier: Apache-2.0 -/

import Mathlib
import InfoGeometry.Exceptional.G2ArtinPresentation

namespace InfoGeometry.Exceptional.ArtinOperators

open InfoGeometry.Exceptional.G2ArtinPresentation

/-!
# $G_2$ Artin Operator Lift and 12-Fold Spin/Cyclotomic Representation

This module formalizes the concrete linear operator representation of the $I_2(6)$
Artin group on state spaces and root carriers without collapsing to the Coxeter quotient.

Key Structures & Theorems:
1. `G2ArtinOperatorLift`: Concrete linear operators $B_s, B_\\ell \\in \\operatorname{End}(\\mathcal{H})$
   satisfying the 6-term Artin relation $B_s B_\\ell B_s B_\\ell B_s B_\\ell = B_\\ell B_s B_\\ell B_s B_\\ell B_s$.
2. `G2SpinOperatorLift`: Spin/projective lift where $C^6 = (B_s B_\\ell)^6 = -I$.
3. 🏆 `spin_coxeter_pow_twelve`: Exact 12-fold cyclotomic closure $C^{12} = I$.
4. 🏆 `braid_conjugation_preserves_nilpotent`: Braid operator conjugation preserves
   the square-zero chiral ladder condition $(Q_\\pm^a)^2 = 0$.
5. 🏆 `hecke_quadratic_expansion`: Braid operators satisfying a quadratic Hecke relation
   $(B - q)(B + q^{-1}) = 0$ expand to $B^2 - (q - q^{-1})B - I = 0$.
-/

/-- Abstract linear operator lift of the $I_2(6)$ Artin group on a complex vector space. -/
structure G2ArtinOperatorLift where
  H : Type*
  [addCommGroup : AddCommGroup H]
  [module : Module ℂ H]
  Bs : Module.End ℂ H
  Bl : Module.End ℂ H
  artin :
    Bs * Bl * Bs * Bl * Bs * Bl =
      Bl * Bs * Bl * Bs * Bl * Bs

attribute [instance] G2ArtinOperatorLift.addCommGroup G2ArtinOperatorLift.module

namespace G2ArtinOperatorLift

variable (ρ : G2ArtinOperatorLift)

/-- The Coxeter braid operator $C = B_s B_\\ell$. -/
def coxeterOp : Module.End ℂ ρ.H :=
  ρ.Bs * ρ.Bl

/-- Fundamental central Garside / Deligne operator $\\Delta = (B_s B_\\ell)^3$. -/
def garsideOp : Module.End ℂ ρ.H :=
  ρ.Bs * ρ.Bl * ρ.Bs * ρ.Bl * ρ.Bs * ρ.Bl

/-- 🏆 THEOREM 1: The Garside operator $\\Delta$ equals the reversed 6-term product $(B_\\ell B_s)^3$. -/
theorem garside_eq_reverse :
    ρ.garsideOp = ρ.Bl * ρ.Bs * ρ.Bl * ρ.Bs * ρ.Bl * ρ.Bs :=
  ρ.artin

/-- 🏆 THEOREM 2: The Garside operator $\\Delta$ commutes with the short generator $B_s$. -/
theorem garside_comm_Bs :
    ρ.garsideOp * ρ.Bs = ρ.Bs * ρ.garsideOp := by
  have h := ρ.artin
  dsimp [garsideOp]
  calc
    ρ.Bs * ρ.Bl * ρ.Bs * ρ.Bl * ρ.Bs * ρ.Bl * ρ.Bs =
        ρ.Bs * (ρ.Bl * ρ.Bs * ρ.Bl * ρ.Bs * ρ.Bl * ρ.Bs) := by
      simp only [mul_assoc]
    _ = ρ.Bs * (ρ.Bs * ρ.Bl * ρ.Bs * ρ.Bl * ρ.Bs * ρ.Bl) := by rw [← h]

/-- 🏆 THEOREM 3: The Garside operator $\\Delta$ commutes with the long generator $B_\\ell$. -/
theorem garside_comm_Bl :
    ρ.garsideOp * ρ.Bl = ρ.Bl * ρ.garsideOp := by
  have h := ρ.artin
  dsimp [garsideOp]
  calc
    ρ.Bs * ρ.Bl * ρ.Bs * ρ.Bl * ρ.Bs * ρ.Bl * ρ.Bl =
        (ρ.Bl * ρ.Bs * ρ.Bl * ρ.Bs * ρ.Bl * ρ.Bs) * ρ.Bl := by rw [h]
    _ = ρ.Bl * (ρ.Bs * ρ.Bl * ρ.Bs * ρ.Bl * ρ.Bs * ρ.Bl) := by
      simp only [mul_assoc]

end G2ArtinOperatorLift

/-- Spin/projective lift where the 6th power of the Coxeter operator is $-I$. -/
structure G2SpinOperatorLift extends G2ArtinOperatorLift where
  coxeter_pow_six_eq_neg_one : (Bs * Bl) ^ 6 = -1

namespace G2SpinOperatorLift

variable (ρ : G2SpinOperatorLift)

/-- 🏆 THEOREM 4: Exact 12-fold cyclotomic closure in the spin lift: $C^{12} = I$. -/
theorem spin_coxeter_pow_twelve :
    (ρ.Bs * ρ.Bl) ^ 12 = 1 := by
  have h12 : (ρ.Bs * ρ.Bl) ^ 12 = ((ρ.Bs * ρ.Bl) ^ 6) ^ 2 := by
    have h_mul : (6 : ℕ) * 2 = 12 := rfl
    rw [← pow_mul, h_mul]
  rw [h12, ρ.coxeter_pow_six_eq_neg_one]
  have h_neg_one_sq : (-1 : Module.End ℂ ρ.H) ^ 2 = 1 := by
    rw [sq, neg_mul_neg, one_mul]
  exact h_neg_one_sq

end G2SpinOperatorLift

/-!
### 3. Nilpotent Conjugation and Chiral Preservation
-/

/-- 🏆 THEOREM 5: Braid conjugation strictly preserves square-zero nilpotent chiral operators.
    If $Q^2 = 0$, then $(B Q B^{-1})^2 = 0$. -/
theorem braid_conjugation_preserves_nilpotent {H : Type*} [AddCommGroup H] [Module ℂ H]
    (B : (Module.End ℂ H)ˣ) (Q : Module.End ℂ H) (hQ : Q ^ 2 = 0) :
    ((B : Module.End ℂ H) * Q * (↑B⁻¹ : Module.End ℂ H)) ^ 2 = 0 := by
  calc
    ((B : Module.End ℂ H) * Q * (↑B⁻¹ : Module.End ℂ H)) ^ 2 =
        ((B : Module.End ℂ H) * Q * (↑B⁻¹ : Module.End ℂ H)) * ((B : Module.End ℂ H) * Q * (↑B⁻¹ : Module.End ℂ H)) := by
      rw [sq]
    _ = (B : Module.End ℂ H) * Q * ((↑B⁻¹ : Module.End ℂ H) * (B : Module.End ℂ H)) * Q * (↑B⁻¹ : Module.End ℂ H) := by
      simp only [mul_assoc]
    _ = (B : Module.End ℂ H) * Q * 1 * Q * (↑B⁻¹ : Module.End ℂ H) := by
      rw [Units.inv_mul]
    _ = (B : Module.End ℂ H) * (Q * Q) * (↑B⁻¹ : Module.End ℂ H) := by
      simp only [mul_one, mul_assoc]
    _ = (B : Module.End ℂ H) * (Q ^ 2) * (↑B⁻¹ : Module.End ℂ H) := by
      rw [sq]
    _ = (B : Module.End ℂ H) * 0 * (↑B⁻¹ : Module.End ℂ H) := by
      rw [hQ]
    _ = 0 := by
      simp only [mul_zero, zero_mul]

/-- 🏆 THEOREM 6: General Hecke quadratic relation: $(B - q)(B + q^{-1}) = 0 \\iff B^2 - (q - q^{-1})B - I = 0$. -/
theorem hecke_quadratic_expansion {H : Type*} [AddCommGroup H] [Module ℂ H]
    (B : Module.End ℂ H) (q : ℂ) (hq : q ≠ 0) :
    (B - q • (1 : Module.End ℂ H)) * (B + q⁻¹ • (1 : Module.End ℂ H)) =
      B ^ 2 - (q - q⁻¹) • B - 1 := by
  ext v
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, sq]
  calc
    (B (B v + q⁻¹ • v) - q • (B v + q⁻¹ • v)) =
        (B (B v) + B (q⁻¹ • v)) - (q • B v + q • (q⁻¹ • v)) := by
      rw [map_add, smul_add]
    _ = (B (B v) + q⁻¹ • B v) - (q • B v + (q * q⁻¹) • v) := by
      rw [LinearMap.map_smul, smul_smul]
    _ = (B (B v) + q⁻¹ • B v) - (q • B v + (1 : ℂ) • v) := by
      rw [mul_inv_cancel₀ hq]
    _ = B (B v) - (q - q⁻¹) • B v - v := by
      simp only [one_smul, sub_smul]
      module

end InfoGeometry.Exceptional.ArtinOperators
