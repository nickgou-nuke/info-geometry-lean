import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.KleinPresentedGroup
import InfoGeometry.Canonical.ProjectiveUnitary6

namespace InfoGeometry.Canonical.KleinSixStateAssociatedBundle

open InfoGeometry.Canonical.KleinPresentedGroup
open InfoGeometry.Canonical.ProjectiveUnitary6

abbrev Fiber := InfoGeometry.Algebra.FiniteSpin.Vec6C
abbrev Base := ℝ × ℝ
abbrev TotalSpace := Base × Fiber

-- Action of A on Base
def actA_Base (w : Base) : Base := (w.1 + 1, -w.2)
def actAInv_Base (w : Base) : Base := (w.1 - 1, -w.2)

theorem actA_actAInv (w : Base) : actA_Base (actAInv_Base w) = w := by
  simp [actA_Base, actAInv_Base]

theorem actAInv_actA (w : Base) : actAInv_Base (actA_Base w) = w := by
  simp [actA_Base, actAInv_Base]

def equivA_Base : Equiv.Perm Base where
  toFun := actA_Base
  invFun := actAInv_Base
  left_inv := actAInv_actA
  right_inv := actA_actAInv

-- Action of B on Base
def actB_Base (w : Base) : Base := (w.1, w.2 + 1)
def actBInv_Base (w : Base) : Base := (w.1, w.2 - 1)

theorem actB_actBInv (w : Base) : actB_Base (actBInv_Base w) = w := by
  simp [actB_Base, actBInv_Base]

theorem actBInv_actB (w : Base) : actBInv_Base (actB_Base w) = w := by
  simp [actB_Base, actBInv_Base]

def equivB_Base : Equiv.Perm Base where
  toFun := actB_Base
  invFun := actBInv_Base
  left_inv := actBInv_actB
  right_inv := actB_actBInv

-- Affine Klein Relation
theorem base_klein_relation (w : Base) :
    equivA_Base (equivB_Base ((equivA_Base⁻¹ : Equiv.Perm Base) (equivB_Base w))) = w := by
  simp [equivA_Base, equivB_Base, actA_Base, actB_Base, actAInv_Base]

-- Action on Fiber
noncomputable def act_Fiber (M : U6) : Equiv.Perm Fiber where
  toFun v := (M : Matrix (Fin 6) (Fin 6) ℂ).mulVec v
  invFun v := ((M⁻¹ : U6) : Matrix (Fin 6) (Fin 6) ℂ).mulVec v
  left_inv v := by
    change ((M⁻¹ : U6) : Matrix (Fin 6) (Fin 6) ℂ).mulVec ((M : Matrix (Fin 6) (Fin 6) ℂ).mulVec v) = v
    rw [Matrix.mulVec_mulVec]
    have h : ((M⁻¹ : U6) : Matrix (Fin 6) (Fin 6) ℂ) * (M : Matrix (Fin 6) (Fin 6) ℂ) = 1 :=
      congrArg Subtype.val (inv_mul_cancel M)
    rw [h]
    exact Matrix.one_mulVec v
  right_inv v := by
    change (M : Matrix (Fin 6) (Fin 6) ℂ).mulVec (((M⁻¹ : U6) : Matrix (Fin 6) (Fin 6) ℂ).mulVec v) = v
    rw [Matrix.mulVec_mulVec]
    have h : (M : Matrix (Fin 6) (Fin 6) ℂ) * ((M⁻¹ : U6) : Matrix (Fin 6) (Fin 6) ℂ) = 1 :=
      congrArg Subtype.val (mul_inv_cancel M)
    rw [h]
    exact Matrix.one_mulVec v

theorem act_Fiber_mul (M N : U6) : act_Fiber (M * N) = act_Fiber M * act_Fiber N := by
  apply Equiv.ext
  intro v
  change ((M * N : U6) : Matrix (Fin 6) (Fin 6) ℂ).mulVec v =
    (M : Matrix (Fin 6) (Fin 6) ℂ).mulVec ((N : Matrix (Fin 6) (Fin 6) ℂ).mulVec v)
  rw [Matrix.mulVec_mulVec]
  rfl

theorem act_Fiber_inv (M : U6) : (act_Fiber M)⁻¹ = act_Fiber (M⁻¹) := by
  ext1 v
  rfl

noncomputable def equivA (Theta : U6) : Equiv.Perm TotalSpace :=
  equivA_Base.prodCongr (act_Fiber Theta)

noncomputable def equivB (T : U6) : Equiv.Perm TotalSpace :=
  equivB_Base.prodCongr (act_Fiber T)

noncomputable def freeTotalAction (Theta T : U6) : KleinFree →* Equiv.Perm TotalSpace :=
  FreeGroup.lift fun g =>
    match g with
    | KleinGenerator.a => equivA Theta
    | KleinGenerator.b => equivB T

theorem total_space_relator_action (Theta T z : U6)
    (_hz : z ∈ centerU6) (hpin : Theta * T * Theta⁻¹ = z * T⁻¹) (x : TotalSpace) :
    (freeTotalAction Theta T kleinRelator) x = (x.1, act_Fiber z x.2) := by
  change (equivA Theta) ((equivB T) ((equivA Theta)⁻¹ ((equivB T) x))) = (x.1, act_Fiber z x.2)
  apply Prod.ext
  · change equivA_Base (equivB_Base (equivA_Base⁻¹ (equivB_Base x.1))) = x.1
    exact base_klein_relation x.1
  · change (Theta : Matrix (Fin 6) (Fin 6) ℂ).mulVec ((T : Matrix (Fin 6) (Fin 6) ℂ).mulVec (((Theta⁻¹ : U6) : Matrix (Fin 6) (Fin 6) ℂ).mulVec ((T : Matrix (Fin 6) (Fin 6) ℂ).mulVec x.2))) = act_Fiber z x.2
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
    have h1 : Theta * T * Theta⁻¹ * T = z := by
      calc
        Theta * T * Theta⁻¹ * T = (Theta * T * Theta⁻¹) * T := by rw [mul_assoc]
        _ = (z * T⁻¹) * T := by rw [hpin]
        _ = z * (T⁻¹ * T) := by rw [mul_assoc]
        _ = z * 1 := by rw [inv_mul_cancel]
        _ = z := by rw [mul_one]
    have h2 : ((Theta * T * Theta⁻¹ * T : U6) : Matrix (Fin 6) (Fin 6) ℂ) = (z : Matrix (Fin 6) (Fin 6) ℂ) := congrArg Subtype.val h1
    change ((Theta : Matrix (Fin 6) (Fin 6) ℂ) * (T : Matrix (Fin 6) (Fin 6) ℂ) * ((Theta⁻¹ : U6) : Matrix (Fin 6) (Fin 6) ℂ) * (T : Matrix (Fin 6) (Fin 6) ℂ)).mulVec x.2 = act_Fiber z x.2
    have h3 : (Theta : Matrix (Fin 6) (Fin 6) ℂ) * (T : Matrix (Fin 6) (Fin 6) ℂ) * ((Theta⁻¹ : U6) : Matrix (Fin 6) (Fin 6) ℂ) * (T : Matrix (Fin 6) (Fin 6) ℂ) = ((Theta * T * Theta⁻¹ * T : U6) : Matrix (Fin 6) (Fin 6) ℂ) := rfl
    rw [h3, h2]
    rfl

end InfoGeometry.Canonical.KleinSixStateAssociatedBundle
