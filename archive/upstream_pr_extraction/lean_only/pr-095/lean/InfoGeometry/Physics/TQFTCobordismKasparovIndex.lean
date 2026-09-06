import Mathlib
import InfoGeometry.Physics.KreinDiracKasparovSpinorBilinear

namespace InfoGeometry.Physics

/-!
Algebraic supertrace cancellations for a cyclic trace and an odd Dirac
element.  These theorems are deliberately stated directly from their
mathematical hypotheses: this file does not package a fake Fredholm module,
heat kernel, cobordism, or Atiyah--Singer theorem.
-/

set_option autoImplicit false

variable {A : Type*} [Ring A] [Algebra ℝ A]

def superTrace (Tr : A →ₗ[ℝ] ℝ) (Gamma X : A) : ℝ :=
  Tr (Gamma * X)

theorem mckean_singer_cancellation
    (Tr : A →ₗ[ℝ] ℝ)
    (hTr_comm : ∀ X Y, Tr (X * Y) = Tr (Y * X))
    (Gamma D : A)
    (hD_odd : Gamma * D = -D * Gamma) :
    superTrace Tr Gamma (D * D) = 0 := by
  have hneg :
      Tr (Gamma * (D * D)) = -Tr (Gamma * (D * D)) := by
    calc
      Tr (Gamma * (D * D))
          = Tr ((Gamma * D) * D) := by simp [mul_assoc]
      _ = Tr ((-D * Gamma) * D) := by rw [hD_odd]
      _ = Tr (-(D * (Gamma * D))) := by simp [mul_assoc]
      _ = -Tr (D * (Gamma * D)) := by rw [LinearMap.map_neg]
      _ = -Tr ((Gamma * D) * D) := by rw [hTr_comm]
      _ = -Tr (Gamma * (D * D)) := by simp [mul_assoc]
  dsimp [superTrace]
  linarith

theorem superTrace_anticommutator_zero
    (Tr : A →ₗ[ℝ] ℝ)
    (hTr_comm : ∀ X Y, Tr (X * Y) = Tr (Y * X))
    (Gamma D X : A)
    (hD_odd : Gamma * D = -D * Gamma) :
    superTrace Tr Gamma (D * X + X * D) = 0 := by
  have hfirst :
      Tr (Gamma * (D * X)) = -Tr (D * (Gamma * X)) := by
    calc
      Tr (Gamma * (D * X))
          = Tr ((Gamma * D) * X) := by simp [mul_assoc]
      _ = Tr ((-D * Gamma) * X) := by rw [hD_odd]
      _ = Tr (-(D * (Gamma * X))) := by simp [mul_assoc]
      _ = -Tr (D * (Gamma * X)) := by rw [LinearMap.map_neg]
  have hsecond :
      Tr (Gamma * (X * D)) = Tr (D * (Gamma * X)) := by
    simpa [mul_assoc] using hTr_comm (Gamma * X) D
  dsimp [superTrace]
  have hmul :
      Gamma * (D * X + X * D) = Gamma * (D * X) + Gamma * (X * D) :=
    mul_add Gamma (D * X) (X * D)
  rw [hmul, LinearMap.map_add, hfirst, hsecond]
  ring

end InfoGeometry.Physics
