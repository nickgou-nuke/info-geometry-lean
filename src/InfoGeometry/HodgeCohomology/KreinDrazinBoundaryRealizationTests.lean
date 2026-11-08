import InfoGeometry.HodgeCohomology.KreinDrazinBoundaryRealization
import InfoGeometry.HodgeCohomology.KreinDrazinGreenTests

namespace InfoGeometry.HodgeCohomology.KreinDrazinBoundaryRealization.Tests

open InfoGeometry.Canonical InfoGeometry.Krein
open Drazin KreinSpace KreinDrazinBoundarySupport KreinHodgeObstruction

noncomputable section

theorem null_inverse : IsDrazinInverse nullDirac 0 2 :=
  IsDrazinInverse.mk (by simp) (by simp) (by simp [pow_two, nullDirac_square])

def nullSupport : KreinDrazinBoundarySupport Plane (Plane →L[ℝ] Plane) :=
  boundarySupport nullDirac 0 null_inverse nullDirac_krein_adjoint

theorem null_ray : BoundaryNullRayRepresentative nullSupport (to_doubled 1 (-1)) := by
  refine ⟨?_, ?_, ?_⟩
  · change (to_doubled 1 (-1) : Plane) ≠ 0
    intro equality
    have first := congrArg WithLp.fst equality
    norm_num at first
  · change (1 - nullDirac * 0 : Plane →L[ℝ] Plane) (to_doubled 1 (-1)) = _
    simp
  · change kreinInner (to_doubled 1 (-1) : Plane) (to_doubled 1 (-1)) = 0
    rw [krein_inner_prod_l2]
    norm_num

example : ¬ BoundaryNullRayRepresentative nullSupport (to_doubled 1 0) := by
  intro boundary
  have zero_energy := boundary.2.2
  change kreinInner (to_doubled 1 0 : Plane) (to_doubled 1 0) = 0 at zero_energy
  rw [krein_inner_prod_l2] at zero_energy
  norm_num at zero_energy

def nullData : AlgebraicDrazinData (Plane →L[ℝ] Plane) where
  L := nullDirac
  LD := 0
  H := 1
  index := 2
  isDrazinInverse := null_inverse
  H_def := by simp [IsDrazinInverse.complementaryProjection, IsDrazinInverse.projection]

example : KreinCompatibleDrazinComplement Plane (Plane →L[ℝ] Plane)
    (carrier (Space := Plane)) nullData carrierAdjointData :=
  compatibleComplement nullData nullDirac_krein_adjoint

#print axioms algebraicSplit
#print axioms boundarySupport
#print axioms compatibleComplement
#print axioms null_ray

end

end InfoGeometry.HodgeCohomology.KreinDrazinBoundaryRealization.Tests
