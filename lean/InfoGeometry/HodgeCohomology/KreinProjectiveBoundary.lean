import InfoGeometry.HodgeCohomology.KreinDrazinBoundaryRealization
import InfoGeometry.Krein.StateNullCone

namespace InfoGeometry.HodgeCohomology.KreinProjectiveBoundary

open InfoGeometry.Canonical InfoGeometry.Krein
open KreinSpace KreinDrazinBoundarySupport KreinDrazinBoundaryRealization

variable {Space : Type*} [NormedAddCommGroup Space] [InnerProductSpace ℝ Space]
variable [CompleteSpace Space] [metric : KreinSpace Space]

def projectiveBoundary (data : AlgebraicDrazinData (Space →L[ℝ] Space)) :
    Set (KreinStateSpace Space) :=
  {ray | ray ∈ KreinStateSpace.NullCone Space ∧
    ray.submodule ≤ LinearMap.ker (data.H.toLinearMap - 1)}

theorem mem_projectiveBoundary_mk_iff
    (data : AlgebraicDrazinData (Space →L[ℝ] Space)) (state : Space) (nonzero : state ≠ 0) :
    Projectivization.mk ℝ state nonzero ∈ projectiveBoundary data ↔
      data.H state = state ∧ kreinInner state state = 0 := by
  simp [projectiveBoundary, KreinStateSpace.mem_nullCone_mk_iff,
    Submodule.span_singleton_le_iff_mem, sub_eq_zero, and_comm]

theorem mem_projectiveBoundary_iff_rep
    (data : AlgebraicDrazinData (Space →L[ℝ] Space)) (ray : KreinStateSpace Space) :
    ray ∈ projectiveBoundary data ↔
      data.H ray.rep = ray.rep ∧ kreinInner ray.rep ray.rep = 0 := by
  simpa only [Projectivization.mk_rep] using
    mem_projectiveBoundary_mk_iff data ray.rep ray.rep_nonzero

noncomputable def nativeBoundary (data : AlgebraicDrazinData (Space →L[ℝ] Space)) :
    DrazinKreinNullBoundary Space (Space →L[ℝ] Space) (carrier (Space := Space)) data where
  Ray := projectiveBoundary data
  representative := fun ray => ray.val.rep
  representative_nonzero := fun ray => ray.val.rep_nonzero
  representative_is_null := fun ray => (mem_projectiveBoundary_iff_rep data ray.val).mp ray.property

theorem nativeBoundary_rep_recovers_ray
    (data : AlgebraicDrazinData (Space →L[ℝ] Space)) (ray : projectiveBoundary data) :
    Projectivization.mk ℝ ((nativeBoundary data).representative ray)
      ((nativeBoundary data).representative_nonzero ray) = ray.val :=
  Projectivization.mk_rep ray.val

theorem mem_projectiveBoundary_iff_range
    (data : AlgebraicDrazinData (Space →L[ℝ] Space)) (state : Space) (nonzero : state ≠ 0) :
    Projectivization.mk ℝ state nonzero ∈ projectiveBoundary data ↔
      state ∈ LinearMap.range data.H.toLinearMap ∧ kreinInner state state = 0 := by
  rw [mem_projectiveBoundary_mk_iff]
  have fixed_iff : data.H state = state ↔ state ∈ LinearMap.range data.H.toLinearMap := by
    constructor
    · intro fixed
      exact ⟨state, fixed⟩
    · rintro ⟨source, rfl⟩
      exact congrArg (fun operator : Space →L[ℝ] Space => operator source) data.H_idempotent
  rw [fixed_iff]

end InfoGeometry.HodgeCohomology.KreinProjectiveBoundary
