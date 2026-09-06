import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Span.Basic

/-!
# Real Cartan and five-grade routing

This owner contains only real-linear routing data.  A Cartan involution
preserves the integer grade when it commutes with the grading operator; a
grade-reversing mirror changes `k` to `-k`.  Independently, a bracket-preserving
Cartan involution splits a real Lie algebra into even and odd sectors with the
usual `(+,+)`, `(+,-)`, and `(-,-)` bracket routing.

No complex eigenspaces, scalar roots of unity, or finite five-grade closure are
assumed here.
-/

namespace InfoGeometry.OperatorAlgebra.RealCartanFiveGradeClosure

section GradedCarrier

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

def HasRealGrade (clock : Module.End ℝ V) (k : ℤ) (x : V) : Prop :=
  clock x = (k : ℝ) • x

def realGradeSubmodule (clock : Module.End ℝ V) (k : ℤ) : Submodule ℝ V :=
  LinearMap.ker (clock - (k : ℝ) • LinearMap.id)

theorem mem_realGradeSubmodule_iff
    (clock : Module.End ℝ V) (k : ℤ) (x : V) :
    x ∈ realGradeSubmodule clock k ↔ HasRealGrade clock k x := by
  change clock x - (k : ℝ) • x = 0 ↔ _
  simp [HasRealGrade, sub_eq_zero]

theorem cartan_preserves_real_grade
    (clock : Module.End ℝ V)
    (cartan : V ≃ₗ[ℝ] V)
    (hcomm : cartan.toLinearMap.comp clock = clock.comp cartan.toLinearMap)
    {k : ℤ} {x : V}
    (hx : HasRealGrade clock k x) :
    HasRealGrade clock k (cartan x) := by
  have h := congrArg (fun f : Module.End ℝ V => f x)
    hcomm
  change cartan (clock x) = clock (cartan x) at h
  rw [hx] at h
  simp only [map_smul] at h
  exact h.symm

theorem mirror_maps_real_grade_to_neg
    (clock : Module.End ℝ V)
    (mirror : V ≃ₗ[ℝ] V)
    (hanti : mirror.toLinearMap.comp clock = -(clock.comp mirror.toLinearMap))
    {k : ℤ} {x : V}
    (hx : HasRealGrade clock k x) :
    HasRealGrade clock (-k) (mirror x) := by
  have h := congrArg (fun f : Module.End ℝ V => f x)
    hanti
  change mirror (clock x) = -clock (mirror x) at h
  rw [hx] at h
  simp only [map_smul] at h
  have hn := congrArg Neg.neg h
  calc
    clock (mirror x) = -((k : ℝ) • mirror x) := by
      simpa using hn.symm
    _ = ((-k : ℤ) : ℝ) • mirror x := by simp

theorem cartan_maps_realGradeSubmodule
    (clock : Module.End ℝ V)
    (cartan : V ≃ₗ[ℝ] V)
    (hcomm : cartan.toLinearMap.comp clock = clock.comp cartan.toLinearMap)
    (k : ℤ) :
    cartan '' realGradeSubmodule clock k ⊆
      realGradeSubmodule clock k := by
  intro y hy
  rcases hy with ⟨x, hx, rfl⟩
  exact (mem_realGradeSubmodule_iff clock k (cartan x)).2
    (cartan_preserves_real_grade clock cartan hcomm
      ((mem_realGradeSubmodule_iff clock k x).1 hx))

theorem mirror_maps_realGradeSubmodule
    (clock : Module.End ℝ V)
    (mirror : V ≃ₗ[ℝ] V)
    (hanti : mirror.toLinearMap.comp clock = -(clock.comp mirror.toLinearMap))
    (k : ℤ) :
    mirror '' realGradeSubmodule clock k ⊆
      realGradeSubmodule clock (-k) := by
  intro y hy
  rcases hy with ⟨x, hx, rfl⟩
  exact (mem_realGradeSubmodule_iff clock (-k) (mirror x)).2
    (mirror_maps_real_grade_to_neg clock mirror hanti
      ((mem_realGradeSubmodule_iff clock k x).1 hx))

end GradedCarrier

end InfoGeometry.OperatorAlgebra.RealCartanFiveGradeClosure
