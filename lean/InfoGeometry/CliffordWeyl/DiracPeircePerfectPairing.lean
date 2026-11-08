/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Core.PeirceMatrixPerfectPairing
import InfoGeometry.CliffordWeyl.DiracPeircePairing

/-! The real Dirac adjoint identifies opposite Peirce corners. Pulling back
their native perfect trace pairing gives the same-corner pairing
`trace (X * K.diracAdjoint Y)`, without a positivity assumption.
-/
noncomputable section
namespace InfoGeometry.Physics.KasparovKreinData
open Matrix InfoGeometry.Core.PeirceDecomposition
variable {n : Type*} [Fintype n] [DecidableEq n]
variable (K : KasparovKreinData (Matrix n n ℝ))
variable (P : Matrix n n ℝ) (hP : P * P = P) (hPK : K.diracAdjoint P = P)

def diracOppositeCornerEquiv :
    LinearMap.range (component10Linear P) ≃ₗ[ℝ]
      LinearMap.range (component01Linear P) where
  toFun X := ⟨K.diracAdjoint X.val, by
    refine ⟨K.diracAdjoint X.val, ?_⟩
    change component01 P (K.diracAdjoint X.val) = K.diracAdjoint X.val
    have h := congrArg K.diracAdjoint (component10_fixed_of_mem_range P hP X)
    rw [diracAdjoint_component10, hPK] at h
    exact h⟩
  invFun X := ⟨K.diracAdjoint X.val, by
    refine ⟨K.diracAdjoint X.val, ?_⟩
    change component10 P (K.diracAdjoint X.val) = K.diracAdjoint X.val
    have h := congrArg K.diracAdjoint (component01_fixed_of_mem_range P hP X)
    rw [diracAdjoint_component01, hPK] at h
    exact h⟩
  left_inv X := by
    apply Subtype.ext
    exact K.diracAdjoint_involution X.val
  right_inv X := by
    apply Subtype.ext
    exact K.diracAdjoint_involution X.val
  map_add' X Y := by
    apply Subtype.ext
    change K.diracAdjoint (X.val + Y.val) = K.diracAdjoint X.val + K.diracAdjoint Y.val
    simp only [diracAdjoint, star_add, mul_add, add_mul]
  map_smul' c X := by
    apply Subtype.ext
    change K.diracAdjoint (c • X.val) = c • K.diracAdjoint X.val
    simp [diracAdjoint, star_smul]

@[simp] theorem diracOppositeCornerEquiv_apply
    (X : LinearMap.range (component10Linear P)) :
    (diracOppositeCornerEquiv K P hP hPK X).val = K.diracAdjoint X.val := rfl

def diracCornerTracePairing :
    LinearMap.range (component10Linear P) →ₗ[ℝ]
      LinearMap.range (component10Linear P) →ₗ[ℝ] ℝ :=
  (oppositeCornerTracePairing P).compl₁₂
    (LinearEquiv.refl ℝ (LinearMap.range (component10Linear P)))
    (diracOppositeCornerEquiv K P hP hPK)

@[simp] theorem diracCornerTracePairing_apply
    (X Y : LinearMap.range (component10Linear P)) :
    diracCornerTracePairing K P hP hPK X Y = trace (X.val * K.diracAdjoint Y.val) := rfl

theorem diracCornerTracePairing_isPerfPair :
    (diracCornerTracePairing K P hP hPK).IsPerfPair := by
  letI := oppositeCornerTracePairing_isPerfPair P hP
  unfold diracCornerTracePairing
  infer_instance

def diracCornerTraceDualEquiv :
    LinearMap.range (component10Linear P) ≃ₗ[ℝ]
      Module.Dual ℝ (LinearMap.range (component10Linear P)) := by
  letI := diracCornerTracePairing_isPerfPair K P hP hPK
  exact (diracCornerTracePairing K P hP hPK).toPerfPair

@[simp] theorem diracCornerTraceDualEquiv_apply
    (X Y : LinearMap.range (component10Linear P)) :
    diracCornerTraceDualEquiv K P hP hPK X Y =
      trace (X.val * K.diracAdjoint Y.val) := rfl

include hP hPK in
/-- Every covector on the corner has a unique representative for Dirac trace pairing. -/
theorem existsUnique_dirac_trace_representative
    (f : Module.Dual ℝ (LinearMap.range (component10Linear P))) :
    ∃! X : LinearMap.range (component10Linear P),
      ∀ Y : LinearMap.range (component10Linear P),
        trace (X.val * K.diracAdjoint Y.val) = f Y := by
  let E := diracCornerTraceDualEquiv K P hP hPK
  refine ⟨E.symm f, ?_, ?_⟩
  · intro Y
    change E (E.symm f) Y = f Y
    rw [E.apply_symm_apply]
  · intro X hX
    apply E.injective
    rw [E.apply_symm_apply]
    apply LinearMap.ext
    intro Y
    exact hX Y

end InfoGeometry.Physics.KasparovKreinData
