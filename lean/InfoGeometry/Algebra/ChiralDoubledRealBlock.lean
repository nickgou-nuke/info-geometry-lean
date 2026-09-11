import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.RealDoubledKreinMirror

noncomputable section

/-!
# A doubled real Nambu--Gorkov block property

On `H × H`, the swap is a real-linear involution.  The diagonal sign is the
Krein symmetry and half of it is the integer charge clock, so an off-diagonal
particle/hole operator has grades `+1` and `-1`.
-/

namespace InfoGeometry.Algebra

open InfoGeometry.Canonical

noncomputable section

abbrev DoubledRealCarrier (H : Type*) := H × H

def blockDiagonal
    {H : Type*} [AddCommGroup H] [Module ℝ H]
    (A B : H →ₗ[ℝ] H) :
    DoubledRealCarrier H →ₗ[ℝ] DoubledRealCarrier H where
  toFun p := (A p.1, B p.2)
  map_add' p q := by
    ext <;> simp
  map_smul' c p := by
    ext <;> simp

def doubledSwap
    {H : Type*} [AddCommGroup H] [Module ℝ H] :
    DoubledRealCarrier H ≃ₗ[ℝ] DoubledRealCarrier H where
  toFun p := (p.2, p.1)
  invFun p := (p.2, p.1)
  left_inv p := by rfl
  right_inv p := by rfl
  map_add' p q := by ext <;> simp
  map_smul' c p := by ext <;> simp

@[simp] theorem doubledSwap_apply
    {H : Type*} [AddCommGroup H] [Module ℝ H]
    (p : DoubledRealCarrier H) :
    doubledSwap p = (p.2, p.1) :=
  rfl

@[simp] theorem doubledSwap_symm_apply
    {H : Type*} [AddCommGroup H] [Module ℝ H]
    (p : DoubledRealCarrier H) :
    (doubledSwap (H := H)).symm p = (p.2, p.1) :=
  rfl

def doubledKreinEta
    {H : Type*} [AddCommGroup H] [Module ℝ H] :
    Module.End ℝ (DoubledRealCarrier H) :=
  blockDiagonal LinearMap.id (-LinearMap.id)

def doubledChargeClock
    {H : Type*} [AddCommGroup H] [Module ℝ H] :
    Module.End ℝ (DoubledRealCarrier H) :=
  (1 / 2 : ℝ) • doubledKreinEta

def doubledRaisingOperator
    {H : Type*} [AddCommGroup H] [Module ℝ H]
    (C : H →ₗ[ℝ] H) :
    Module.End ℝ (DoubledRealCarrier H) where
  toFun p := (C p.2, 0)
  map_add' p q := by ext <;> simp
  map_smul' c p := by ext <;> simp

def doubledLoweringOperator
    {H : Type*} [AddCommGroup H] [Module ℝ H]
    (C : H →ₗ[ℝ] H) :
    Module.End ℝ (DoubledRealCarrier H) where
  toFun p := (0, C p.1)
  map_add' p q := by ext <;> simp
  map_smul' c p := by ext <;> simp

theorem doubledKreinEta_sq
    {H : Type*} [AddCommGroup H] [Module ℝ H] :
    (doubledKreinEta (H := H)).comp doubledKreinEta =
      LinearMap.id := by
  apply LinearMap.ext
  intro p
  rcases p with ⟨x, y⟩
  simp [doubledKreinEta, blockDiagonal, LinearMap.comp_apply]

theorem doubledSwap_sq
    {H : Type*} [AddCommGroup H] [Module ℝ H] :
    (doubledSwap (H := H)).toLinearMap.comp
        (doubledSwap (H := H)).toLinearMap =
      LinearMap.id := by
  apply LinearMap.ext
  intro p
  rcases p with ⟨x, y⟩
  rfl

theorem doubledSwap_conjugates_eta
    {H : Type*} [AddCommGroup H] [Module ℝ H] :
    (doubledSwap (H := H)).toLinearMap.comp
        ((doubledKreinEta (H := H)).comp
          (doubledSwap (H := H)).symm.toLinearMap) =
      -(doubledKreinEta (H := H)) := by
  apply LinearMap.ext
  intro p
  rcases p with ⟨x, y⟩
  simp [doubledKreinEta, blockDiagonal,
    LinearMap.comp_apply]

theorem doubledSwap_conjugates_clock
    {H : Type*} [AddCommGroup H] [Module ℝ H] :
    (doubledSwap (H := H)).toLinearMap.comp
        ((doubledChargeClock (H := H)).comp
          (doubledSwap (H := H)).symm.toLinearMap) =
      -(doubledChargeClock (H := H)) := by
  apply LinearMap.ext
  intro p
  rcases p with ⟨x, y⟩
  simp [doubledChargeClock, doubledKreinEta, blockDiagonal,
    LinearMap.comp_apply]

def doubledHestenesKreinData
    {H : Type*} [AddCommGroup H] [Module ℝ H] :
    InfoGeometry.Canonical.DoubledHestenesKreinData (DoubledRealCarrier H) where
  eta := doubledKreinEta
  mirror := doubledSwap
  clock := doubledChargeClock
  eta_sq := doubledKreinEta_sq
  mirror_sq := doubledSwap_sq
  mirror_clock := doubledSwap_conjugates_clock

theorem doubledSwap_conjugates_raising
    {H : Type*} [AddCommGroup H] [Module ℝ H]
    (C : H →ₗ[ℝ] H) :
    InfoGeometry.Canonical.DoubledHestenesKreinData.mirrorConjugate
        (doubledHestenesKreinData (H := H))
        (doubledRaisingOperator C) =
      doubledLoweringOperator C := by
  apply LinearMap.ext
  intro p
  rcases p with ⟨x, y⟩
  change (doubledSwap (H := H))
      ((doubledRaisingOperator C)
        ((doubledSwap (H := H)).symm (x, y))) = (0, C x)
  rfl

theorem doubledSwap_conjugates_lowering
    {H : Type*} [AddCommGroup H] [Module ℝ H]
    (C : H →ₗ[ℝ] H) :
    InfoGeometry.Canonical.DoubledHestenesKreinData.mirrorConjugate
        (doubledHestenesKreinData (H := H))
        (doubledLoweringOperator C) =
      doubledRaisingOperator C := by
  apply LinearMap.ext
  intro p
  rcases p with ⟨x, y⟩
  change (doubledSwap (H := H))
      ((doubledLoweringOperator C)
        ((doubledSwap (H := H)).symm (x, y))) = (C y, 0)
  rfl

theorem doubledRaising_grade_one
    {H : Type*} [AddCommGroup H] [Module ℝ H]
    (C : H →ₗ[ℝ] H) :
    InfoGeometry.Canonical.DoubledHestenesKreinData.HasGrade
      (doubledChargeClock (H := H)) 1
      (doubledRaisingOperator C) := by
  unfold InfoGeometry.Canonical.DoubledHestenesKreinData.HasGrade
    InfoGeometry.Canonical.DoubledHestenesKreinData.operatorCommutator
  apply LinearMap.ext
  intro p
  rcases p with ⟨x, y⟩
  simp [doubledChargeClock, doubledKreinEta, blockDiagonal,
    doubledRaisingOperator, LinearMap.comp_apply]
  rw [← add_smul]
  norm_num [one_smul]

theorem doubledLowering_grade_neg_one
    {H : Type*} [AddCommGroup H] [Module ℝ H]
    (C : H →ₗ[ℝ] H) :
    InfoGeometry.Canonical.DoubledHestenesKreinData.HasGrade
      (doubledChargeClock (H := H)) (-1)
      (doubledLoweringOperator C) := by
  unfold InfoGeometry.Canonical.DoubledHestenesKreinData.HasGrade
    InfoGeometry.Canonical.DoubledHestenesKreinData.operatorCommutator
  apply LinearMap.ext
  intro p
  rcases p with ⟨x, y⟩
  simp [doubledChargeClock, doubledKreinEta, blockDiagonal,
    doubledLoweringOperator, LinearMap.comp_apply]
  rw [← neg_smul, ← sub_smul]
  norm_num [one_smul]

end
end InfoGeometry.Algebra
