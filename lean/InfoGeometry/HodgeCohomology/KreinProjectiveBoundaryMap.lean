import InfoGeometry.HodgeCohomology.KreinProjectiveBoundary
import InfoGeometry.Canonical.DrazinCommutant

namespace InfoGeometry.HodgeCohomology.KreinProjectiveBoundaryMap

open InfoGeometry.Canonical InfoGeometry.Krein
open KreinSpace KreinDrazinBoundarySupport KreinProjectiveBoundary

variable {Space : Type*} [NormedAddCommGroup Space] [InnerProductSpace ℝ Space]
variable [CompleteSpace Space] [metric : KreinSpace Space]

omit [CompleteSpace Space] metric in
theorem complement_commutes
    (data : AlgebraicDrazinData (Space →L[ℝ] Space)) (symmetry : Module.End ℝ Space)
    (commutes : Commute data.L.toLinearMap symmetry) :
    Commute data.H.toLinearMap symmetry := by
  have inverse_commutes : Commute data.LD.toLinearMap symmetry :=
    DrazinCommutant.inverse_commutes_of_commutes
      (KreinDrazinGreen.linear_drazin_inverse data.isDrazinInverse) symmetry commutes
  rw [data.H_def]
  change Commute (1 - data.L.toLinearMap * data.LD.toLinearMap) symmetry
  exact (Commute.one_left symmetry).sub_left (commutes.mul_left inverse_commutes)

theorem map_mem_iff
    (data : AlgebraicDrazinData (Space →L[ℝ] Space)) (symmetry : Space ≃ₗ[ℝ] Space)
    (commutes : Commute data.H.toLinearMap symmetry.toLinearMap)
    (scale : ℝ) (scale_nonzero : scale ≠ 0)
    (preserves : ∀ state, kreinInner (symmetry state) (symmetry state) =
      scale * kreinInner state state) (ray : KreinStateSpace Space) :
    Projectivization.map symmetry.toLinearMap symmetry.injective ray ∈ projectiveBoundary data ↔
      ray ∈ projectiveBoundary data := by
  induction ray using Projectivization.ind with
  | h state nonzero =>
    rw [Projectivization.map_mk, mem_projectiveBoundary_mk_iff, mem_projectiveBoundary_mk_iff]
    have commutes_state : data.H (symmetry state) = symmetry (data.H state) :=
      LinearMap.congr_fun commutes state
    change (data.H (symmetry state) = symmetry state ∧
      kreinInner (symmetry state) (symmetry state) = 0) ↔ _
    rw [commutes_state, preserves]
    simp only [symmetry.injective.eq_iff, mul_eq_zero, scale_nonzero, false_or]

theorem map_mem_iff_of_commutes_operator
    (data : AlgebraicDrazinData (Space →L[ℝ] Space)) (symmetry : Space ≃ₗ[ℝ] Space)
    (commutes : Commute data.L.toLinearMap symmetry.toLinearMap)
    (scale : ℝ) (scale_nonzero : scale ≠ 0)
    (preserves : ∀ state, kreinInner (symmetry state) (symmetry state) =
      scale * kreinInner state state) (ray : KreinStateSpace Space) :
    Projectivization.map symmetry.toLinearMap symmetry.injective ray ∈ projectiveBoundary data ↔
      ray ∈ projectiveBoundary data :=
  map_mem_iff data symmetry (complement_commutes data symmetry.toLinearMap commutes)
    scale scale_nonzero preserves ray

end InfoGeometry.HodgeCohomology.KreinProjectiveBoundaryMap
