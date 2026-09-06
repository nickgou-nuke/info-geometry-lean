import InfoGeometry.Canonical.ConcreteCuntzFrameTopology

/-!
# Linear-isometric form of the concrete rectangular frame

The two columns are norm-preserving maps `ℂ¹ → ℂ²`.  They are rectangular
isometries, not two elements of a common unital algebra, so this file does not
claim a finite-dimensional realization of the Cuntz relations.
-/

noncomputable section

namespace InfoGeometry.Canonical.ConcreteCuntzFrameIsometry

open InfoGeometry.Canonical.ConcreteCuntzMatrixIsometries
open InfoGeometry.Canonical.ConcreteCuntzFrameTopology

private theorem column_norm_S1 (x : Fin 1 → ℂ) :
    ‖Matrix.mulVec cuntzMatrixS1 x‖ = ‖x‖ := by
  have hx : x = (fun _ : Fin 1 => x 0) := by
    funext i
    fin_cases i
    rfl
  rw [hx]
  simp [cuntzMatrixS1, Pi.norm_def]
  rw [show (Finset.univ : Finset (Fin 2)) = {0, 1} by decide]
  simp

private theorem column_norm_S2 (x : Fin 1 → ℂ) :
    ‖Matrix.mulVec cuntzMatrixS2 x‖ = ‖x‖ := by
  have hx : x = (fun _ : Fin 1 => x 0) := by
    funext i
    fin_cases i
    rfl
  rw [hx]
  simp [cuntzMatrixS2, Pi.norm_def]
  rw [show (Finset.univ : Finset (Fin 2)) = {0, 1} by decide]
  simp

def frameS1LinearIsometry :
    (Fin 1 → ℂ) →ₗᵢ[ℂ] (Fin 2 → ℂ) :=
  LinearIsometry.mk cuntzMatrixS1.mulVecLin column_norm_S1

def frameS2LinearIsometry :
    (Fin 1 → ℂ) →ₗᵢ[ℂ] (Fin 2 → ℂ) :=
  LinearIsometry.mk cuntzMatrixS2.mulVecLin column_norm_S2

@[simp] theorem frameS1LinearIsometry_apply (x : Fin 1 → ℂ) :
    frameS1LinearIsometry x = cuntzMatrixS1.mulVec x :=
  rfl

@[simp] theorem frameS2LinearIsometry_apply (x : Fin 1 → ℂ) :
    frameS2LinearIsometry x = cuntzMatrixS2.mulVec x :=
  rfl

theorem frameS1LinearIsometry_continuous :
    Continuous (frameS1LinearIsometry : (Fin 1 → ℂ) → (Fin 2 → ℂ)) :=
  frameS1LinearIsometry.continuous

theorem frameS2LinearIsometry_continuous :
    Continuous (frameS2LinearIsometry : (Fin 1 → ℂ) → (Fin 2 → ℂ)) :=
  frameS2LinearIsometry.continuous

theorem frameS1LinearIsometry_closedEmbedding :
    Topology.IsClosedEmbedding
      (frameS1LinearIsometry : (Fin 1 → ℂ) → (Fin 2 → ℂ)) :=
  frameS1LinearIsometry.isometry.isClosedEmbedding

theorem frameS2LinearIsometry_closedEmbedding :
    Topology.IsClosedEmbedding
      (frameS2LinearIsometry : (Fin 1 → ℂ) → (Fin 2 → ℂ)) :=
  frameS2LinearIsometry.isometry.isClosedEmbedding

end InfoGeometry.Canonical.ConcreteCuntzFrameIsometry
