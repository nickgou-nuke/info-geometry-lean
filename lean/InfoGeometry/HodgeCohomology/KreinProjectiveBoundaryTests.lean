import InfoGeometry.HodgeCohomology.KreinProjectiveBoundaryMap
import InfoGeometry.HodgeCohomology.KreinDrazinBoundaryRealizationTests

namespace InfoGeometry.HodgeCohomology.KreinProjectiveBoundary.Tests

open InfoGeometry.Canonical InfoGeometry.Krein
open KreinSpace KreinHodgeObstruction KreinDrazinBoundaryRealization.Tests

noncomputable section

theorem first_one_nonzero (second : ℝ) : (to_doubled 1 second : Plane) ≠ 0 := by
  intro equality
  have first := congrArg WithLp.fst equality
  norm_num at first

def diagonalRay : KreinStateSpace Plane :=
  Projectivization.mk ℝ (to_doubled 1 1) (first_one_nonzero 1)

def antidiagonalRay : KreinStateSpace Plane :=
  Projectivization.mk ℝ (to_doubled 1 (-1)) (first_one_nonzero (-1))

theorem diagonal_mem : diagonalRay ∈ projectiveBoundary nullData := by
  rw [diagonalRay, mem_projectiveBoundary_mk_iff, krein_inner_prod_l2]
  norm_num [nullData]

theorem antidiagonal_mem : antidiagonalRay ∈ projectiveBoundary nullData := by
  rw [antidiagonalRay, mem_projectiveBoundary_mk_iff, krein_inner_prod_l2]
  norm_num [nullData]

theorem rays_distinct : diagonalRay ≠ antidiagonalRay := by
  intro equality
  obtain ⟨scale, scales⟩ := (Projectivization.mk_eq_mk_iff' ℝ _ _ _ _).mp equality
  have first := congrArg WithLp.fst scales
  have second := congrArg WithLp.snd scales
  simp at first second
  linarith

example : Projectivization.mk ℝ (to_doubled 1 0 : Plane) (first_one_nonzero 0) ∉
    projectiveBoundary nullData := by
  rw [mem_projectiveBoundary_mk_iff, krein_inner_prod_l2]
  norm_num [nullData]

example (ray : projectiveBoundary nullData) :
    Projectivization.mk ℝ ((nativeBoundary nullData).representative ray)
      ((nativeBoundary nullData).representative_nonzero ray) = ray.val :=
  nativeBoundary_rep_recovers_ray nullData ray

example : Projectivization.mk ℝ (to_doubled (-2) (-2) : Plane)
    (by intro equality; have first := congrArg WithLp.fst equality; norm_num at first) = diagonalRay := by
  apply (Projectivization.mk_eq_mk_iff' ℝ _ _ _ _).mpr
  refine ⟨-2, ?_⟩
  apply DoubledSpace.ext <;> norm_num

def mirror : Plane ≃ₗ[ℝ] Plane :=
  LinearEquiv.ofInvolutive (modular_j (E := ℝ)).toLinearMap (by
    intro state
    exact congrArg (fun operator : Plane →L[ℝ] Plane => operator state) (modular_j_involution ℝ))

theorem mirror_preserves_boundary (ray : KreinStateSpace Plane) :
    Projectivization.map mirror.toLinearMap mirror.injective ray ∈ projectiveBoundary nullData ↔
      ray ∈ projectiveBoundary nullData := by
  apply KreinProjectiveBoundaryMap.map_mem_iff nullData mirror _ (-1) (by norm_num)
  · intro state
    change kreinInner (modular_j state) (modular_j state) = -1 * kreinInner state state
    rw [krein_inner_prod_l2, krein_inner_prod_l2]
    simp [modular_j]
  · change Commute (1 : Module.End ℝ Plane) mirror.toLinearMap
    exact Commute.one_left _

theorem negation_preserves_boundary (ray : KreinStateSpace Plane) :
    Projectivization.map (LinearEquiv.neg ℝ : Plane ≃ₗ[ℝ] Plane).toLinearMap
      (LinearEquiv.neg ℝ).injective ray ∈ projectiveBoundary nullData ↔
      ray ∈ projectiveBoundary nullData := by
  apply KreinProjectiveBoundaryMap.map_mem_iff_of_commutes_operator nullData
    (LinearEquiv.neg ℝ) _ 1 one_ne_zero
  · intro state
    change kreinInner (-state) (-state) = 1 * kreinInner state state
    simp [kreinInner_def]
  · apply LinearMap.ext
    intro state
    change nullData.L (-state) = -(nullData.L state)
    exact map_neg nullData.L state

#print axioms KreinStateSpace.mem_nullCone_mk_iff
#print axioms KreinStateSpace.mem_nullCone_iff_rep
#print axioms mem_projectiveBoundary_mk_iff
#print axioms mem_projectiveBoundary_iff_rep
#print axioms nativeBoundary
#print axioms nativeBoundary_rep_recovers_ray
#print axioms mem_projectiveBoundary_iff_range
#print axioms KreinProjectiveBoundaryMap.complement_commutes
#print axioms KreinProjectiveBoundaryMap.map_mem_iff
#print axioms KreinProjectiveBoundaryMap.map_mem_iff_of_commutes_operator
#print axioms rays_distinct
#print axioms mirror_preserves_boundary
#print axioms negation_preserves_boundary

end

end InfoGeometry.HodgeCohomology.KreinProjectiveBoundary.Tests
