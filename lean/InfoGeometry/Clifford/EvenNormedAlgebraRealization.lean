import Mathlib.Analysis.Normed.Operator.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.LinearAlgebra.CliffordAlgebra.Even

/-! Continuous regular operators after an explicit finite-dimensional realization. -/

namespace InfoGeometry.Clifford.EvenNormedAlgebraRealization

open CliffordAlgebra
noncomputable section

variable {M E : Type*} [AddCommGroup M] [Module ℝ M]
variable {Q : QuadraticForm ℝ M}
variable [NormedRing E] [NormedAlgebra ℝ E] [FiniteDimensional ℝ E]
variable [CompleteSpace E]

structure Realization where
  equiv : CliffordAlgebra.even Q ≃ₐ[ℝ] E

noncomputable def leftRegularContinuousLinearMap (e : E) : E →L[ℝ] E :=
  ContinuousLinearMap.mk (LinearMap.mulLeft ℝ e)
    (LinearMap.continuous_of_finiteDimensional (LinearMap.mulLeft ℝ e))

noncomputable def rightRegularContinuousLinearMap (e : E) : E →L[ℝ] E :=
  ContinuousLinearMap.mk (LinearMap.mulRight ℝ e)
    (LinearMap.continuous_of_finiteDimensional (LinearMap.mulRight ℝ e))

@[simp] theorem leftRegularContinuousLinearMap_apply (e x : E) :
    leftRegularContinuousLinearMap e x = e * x := rfl

@[simp] theorem rightRegularContinuousLinearMap_apply (e x : E) :
    rightRegularContinuousLinearMap e x = x * e := rfl

theorem leftRegularContinuousLinearMap_mul (e f : E) :
    leftRegularContinuousLinearMap (e * f) =
      (leftRegularContinuousLinearMap e).comp
        (leftRegularContinuousLinearMap f) := by
  ext x
  exact mul_assoc e f x

theorem rightRegularContinuousLinearMap_mul (e f : E) :
    rightRegularContinuousLinearMap (e * f) =
      (rightRegularContinuousLinearMap f).comp
        (rightRegularContinuousLinearMap e) := by
  ext x
  exact (mul_assoc x e f).symm

theorem leftRegularContinuousLinearMap_comp_rightRegularContinuousLinearMap
    (e f : E) :
    (leftRegularContinuousLinearMap e).comp
        (rightRegularContinuousLinearMap f) =
      (rightRegularContinuousLinearMap f).comp
        (leftRegularContinuousLinearMap e) := by
  ext x
  exact (mul_assoc e x f).symm

def leftRegularContinuousCommutant :
    Set (E →L[ℝ] E) :=
  {T | ∀ a x,
    T (leftRegularContinuousLinearMap a x) =
      leftRegularContinuousLinearMap a (T x)}

theorem rightRegularContinuousLinearMap_mem_leftRegularContinuousCommutant
    (b : E) :
    rightRegularContinuousLinearMap b ∈ leftRegularContinuousCommutant (E := E) := by
  intro a x
  simp [leftRegularContinuousCommutant, mul_assoc]

theorem leftRegularContinuousCommutant_eq_rightRegularRange :
    leftRegularContinuousCommutant (E := E) =
      {T | ∃ b : E, T = rightRegularContinuousLinearMap b} := by
  ext T
  constructor
  · intro hT
    refine ⟨T 1, ?_⟩
    apply ContinuousLinearMap.ext
    intro x
    have hx := hT x 1
    simpa only [leftRegularContinuousLinearMap_apply,
      rightRegularContinuousLinearMap_apply, one_mul, mul_one] using hx
  · rintro ⟨b, rfl⟩
    exact rightRegularContinuousLinearMap_mem_leftRegularContinuousCommutant b

theorem rightRegularContinuousLinearMap_injective :
    Function.Injective (rightRegularContinuousLinearMap (E := E)) := by
  intro a b hab
  have h := congrArg (fun T : E →L[ℝ] E => T 1) hab
  simpa only [rightRegularContinuousLinearMap_apply, one_mul] using h

noncomputable def transportedLeft
    (R : Realization (Q := Q) (E := E))
    (a : CliffordAlgebra.even Q) : E →L[ℝ] E :=
  leftRegularContinuousLinearMap (R.equiv a)

noncomputable def transportedRight
    (R : Realization (Q := Q) (E := E))
    (a : CliffordAlgebra.even Q) : E →L[ℝ] E :=
  rightRegularContinuousLinearMap (R.equiv a)

theorem transportedLeft_mul
    (R : Realization (Q := Q) (E := E))
    (a b : CliffordAlgebra.even Q) :
    transportedLeft R (a * b) =
      (transportedLeft R a).comp (transportedLeft R b) := by
  unfold transportedLeft
  rw [map_mul]
  exact leftRegularContinuousLinearMap_mul _ _

theorem transportedRight_mul
    (R : Realization (Q := Q) (E := E))
    (a b : CliffordAlgebra.even Q) :
    transportedRight R (a * b) =
      (transportedRight R b).comp (transportedRight R a) := by
  unfold transportedRight
  rw [map_mul]
  exact rightRegularContinuousLinearMap_mul _ _

noncomputable def leftRegularLinearEquiv (u : Eˣ) : E ≃ₗ[ℝ] E where
  toFun x := (u : E) * x
  invFun x := (↑(u⁻¹) : E) * x
  left_inv x := by simp [mul_assoc]
  right_inv x := by simp [mul_assoc]
  map_add' x y := by exact mul_add _ _ _
  map_smul' r x := by
    simp only [Algebra.smul_def]
    calc
      (u : E) * (algebraMap ℝ E r * x) =
          ((u : E) * algebraMap ℝ E r) * x := (mul_assoc _ _ _).symm
      _ = (algebraMap ℝ E r * (u : E)) * x := by rw [Algebra.commutes]
      _ = algebraMap ℝ E r * ((u : E) * x) := mul_assoc _ _ _

noncomputable def leftRegularContinuousLinearEquiv (u : Eˣ) : E ≃L[ℝ] E :=
  (leftRegularLinearEquiv u).toContinuousLinearEquiv

@[simp] theorem leftRegularContinuousLinearEquiv_apply (u : Eˣ) (x : E) :
    leftRegularContinuousLinearEquiv u x = (u : E) * x := by
  rfl

end
end InfoGeometry.Clifford.EvenNormedAlgebraRealization
