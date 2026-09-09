import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Span.Basic
import InfoGeometry.OperatorAlgebra.GradeActionInterface

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

theorem cartan_image_realGradeSubmodule_eq
    (clock : Module.End ℝ V)
    (cartan : V ≃ₗ[ℝ] V)
    (hcomm : cartan.toLinearMap.comp clock = clock.comp cartan.toLinearMap)
    (k : ℤ) :
    cartan '' realGradeSubmodule clock k = realGradeSubmodule clock k := by
  apply Set.Subset.antisymm
  · exact cartan_maps_realGradeSubmodule clock cartan hcomm k
  · intro y hy
    refine ⟨cartan.symm y, ?_, cartan.apply_symm_apply y⟩
    apply (mem_realGradeSubmodule_iff clock k _).2
    have hcomm' : cartan.toLinearMap.comp clock = clock.comp cartan.toLinearMap := hcomm
    have hraw := congrArg (fun f : Module.End ℝ V => f (cartan.symm y)) hcomm'
    simp only [LinearMap.comp_apply] at hraw
    change cartan (clock (cartan.symm y)) = clock (cartan (cartan.symm y)) at hraw
    have h : cartan (clock (cartan.symm y)) = clock y := by
      simpa only [LinearEquiv.apply_symm_apply] using hraw
    have hy' : clock y = (k : ℝ) • y :=
      (mem_realGradeSubmodule_iff clock k y).1 hy
    have hcancel := congrArg cartan.symm h
    rw [hy'] at hcancel
    simpa [HasRealGrade] using hcancel

theorem mirror_image_realGradeSubmodule_eq
    (clock : Module.End ℝ V)
    (mirror : V ≃ₗ[ℝ] V)
    (hanti : mirror.toLinearMap.comp clock = -(clock.comp mirror.toLinearMap))
    (k : ℤ) :
    mirror '' realGradeSubmodule clock k = realGradeSubmodule clock (-k) := by
  apply Set.Subset.antisymm
  · exact mirror_maps_realGradeSubmodule clock mirror hanti k
  · intro y hy
    refine ⟨mirror.symm y, ?_, mirror.apply_symm_apply y⟩
    apply (mem_realGradeSubmodule_iff clock k _).2
    have hraw := congrArg (fun f : Module.End ℝ V => f (mirror.symm y)) hanti
    simp only [LinearMap.comp_apply, LinearMap.neg_apply] at hraw
    change mirror (clock (mirror.symm y)) = -clock (mirror (mirror.symm y)) at hraw
    have hanti' : mirror (clock (mirror.symm y)) = -clock y := by
      simpa only [LinearEquiv.apply_symm_apply] using hraw
    have hy' : clock y = ((-k : ℤ) : ℝ) • y :=
      (mem_realGradeSubmodule_iff clock (-k) y).1 hy
    have hcancel := congrArg mirror.symm hanti'
    rw [hy'] at hcancel
    have hgrade : clock (mirror.symm y) = (k : ℝ) • mirror.symm y := by
      simpa [Int.cast_neg, smul_smul] using hcancel
    exact hgrade

theorem cartan_mapsToGradeBetween
    (clock : Module.End ℝ V)
    (cartan : V ≃ₗ[ℝ] V)
    (hcomm : cartan.toLinearMap.comp clock = clock.comp cartan.toLinearMap) :
    InfoGeometry.OperatorAlgebra.MapsToGradeBetween
      (fun k : ℤ => (realGradeSubmodule clock k : Set V))
      (fun k : ℤ => (realGradeSubmodule clock k : Set V))
      (fun _ : Unit => cartan)
      (fun _ k => k) := by
  intro _ k x hx
  exact (mem_realGradeSubmodule_iff clock k (cartan x)).2
    (cartan_preserves_real_grade clock cartan hcomm
      ((mem_realGradeSubmodule_iff clock k x).1 hx))

theorem mirror_mapsToGradeBetween
    (clock : Module.End ℝ V)
    (mirror : V ≃ₗ[ℝ] V)
    (hanti : mirror.toLinearMap.comp clock = -(clock.comp mirror.toLinearMap)) :
    InfoGeometry.OperatorAlgebra.MapsToGradeBetween
      (fun k : ℤ => (realGradeSubmodule clock k : Set V))
      (fun k : ℤ => (realGradeSubmodule clock k : Set V))
      (fun _ : Unit => mirror)
      (fun _ k => -k) := by
  intro _ k x hx
  exact (mem_realGradeSubmodule_iff clock (-k) (mirror x)).2
    (mirror_maps_real_grade_to_neg clock mirror hanti
      ((mem_realGradeSubmodule_iff clock k x).1 hx))

theorem mirror_after_cartan_mapsToGradeBetween
    (clock : Module.End ℝ V)
    (cartan mirror : V ≃ₗ[ℝ] V)
    (hcomm : cartan.toLinearMap.comp clock = clock.comp cartan.toLinearMap)
    (hanti : mirror.toLinearMap.comp clock = -(clock.comp mirror.toLinearMap)) :
    InfoGeometry.OperatorAlgebra.MapsToGradeBetween
      (fun k : ℤ => (realGradeSubmodule clock k : Set V))
      (fun k : ℤ => (realGradeSubmodule clock k : Set V))
      (fun _ : Unit => fun x => mirror (cartan x))
      (fun _ k => -k) := by
  intro _ k x hx
  have hcartan := cartan_mapsToGradeBetween clock cartan hcomm
  have hmirror := mirror_mapsToGradeBetween clock mirror hanti
  have hcomp := mapsToGradeBetween_comp_family hcartan hmirror
  simpa using hcomp ((), ()) k hx

theorem mirror_after_cartan_image_realGradeSubmodule_eq
    (clock : Module.End ℝ V)
    (cartan mirror : V ≃ₗ[ℝ] V)
    (hcomm : cartan.toLinearMap.comp clock = clock.comp cartan.toLinearMap)
    (hanti : mirror.toLinearMap.comp clock = -(clock.comp mirror.toLinearMap))
    (k : ℤ) :
    (fun x => mirror (cartan x)) '' realGradeSubmodule clock k =
      realGradeSubmodule clock (-k) := by
  rw [show (fun x => mirror (cartan x)) '' realGradeSubmodule clock k =
      mirror '' (cartan '' realGradeSubmodule clock k) by
        ext y
        constructor
        · rintro ⟨x, hx, rfl⟩
          exact ⟨cartan x, ⟨x, hx, rfl⟩, rfl⟩
        · rintro ⟨z, ⟨x, hx, rfl⟩, rfl⟩
          exact ⟨x, hx, rfl⟩]
  rw [cartan_image_realGradeSubmodule_eq clock cartan hcomm k]
  exact mirror_image_realGradeSubmodule_eq clock mirror hanti k

end GradedCarrier

end InfoGeometry.OperatorAlgebra.RealCartanFiveGradeClosure
