import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction

/-!
# The integral translation action on the upper half-plane

This is the theorem-safe `ℤ` adapter for the modular generator `T`.  It is
stated as an action law on points rather than as a homomorphism into a
pointwise multiplicative function monoid: functions act here by composition.
-/

namespace InfoGeometry.Arithmetic.IntegerModularPosition

open UpperHalfPlane

noncomputable def act (n : ℤ) (τ : UpperHalfPlane) : UpperHalfPlane :=
  ModularGroup.T ^ n • τ

@[simp] theorem act_zero (τ : UpperHalfPlane) :
    act 0 τ = τ := by
  simp [act]

theorem act_add (m n : ℤ) (τ : UpperHalfPlane) :
    act (m + n) τ = act m (act n τ) := by
  simp only [act, zpow_add, mul_smul]

theorem act_apply (n : ℤ) (τ : UpperHalfPlane) :
    (act n τ : ℂ) = (n : ℝ) + (τ : ℂ) := by
  have h := UpperHalfPlane.modular_T_zpow_smul τ n
  exact congrArg (fun z : UpperHalfPlane => (z : ℂ)) h

theorem act_apply_add (n : ℤ) (τ : UpperHalfPlane) :
    (act n τ : ℂ) = (n : ℝ) + (τ : ℂ) := by
  exact act_apply n τ

theorem act_neg (n : ℤ) (τ : UpperHalfPlane) :
    act (-n) (act n τ) = τ := by
  have h := act_add (-n) n τ
  simpa using h.symm

end InfoGeometry.Arithmetic.IntegerModularPosition
