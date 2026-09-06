import InfoGeometry.Canonical.CayleyHestenesGradedIntertwinerBridge
import InfoGeometry.Lie.SplitOctonionWittHypercomplexPlaneBridge

/-!
# Concrete graded Cayley--Hestenes datum on the Witt readout

The finite `Mat8` identities are exposed as native `Module.End` identities on
the coordinate carrier `(Fin 8 → ℝ)`.  This is an algebraic realization of
the generic graded Cayley--Hestenes API; it does not assert a Hilbert,
antiunitary, or analytic interpretation.
-/

noncomputable section

namespace InfoGeometry.Canonical.CayleyHestenesWittGradedConcreteBridge

open InfoGeometry.Canonical.CayleyHestenesGradedIntertwinerBridge
open InfoGeometry.Lie.SplitOctonionWittHypercomplexPlaneBridge

abbrev WittCarrier := Fin 8 → ℝ
abbrev WittEnd := Module.End ℝ WittCarrier

def matrixEnd (A : Mat8) : WittEnd := Matrix.mulVecLin A

def wittGradedDatum : CayleyHestenesGradedDatum WittCarrier where
  K := matrixEnd wittHestenesMat
  C := matrixEnd sectorwiseCayleyMat
  M := matrixEnd longitudinalTransverseMat
  K_sq := by
    dsimp [matrixEnd]
    change Matrix.mulVecLin wittHestenesMat ∘ₗ
        Matrix.mulVecLin wittHestenesMat = _
    rw [← Matrix.mulVecLin_mul, wittHestenesMat_sq]
    ext x i
    simp [Matrix.mulVecLin, Matrix.mulVec, dotProduct, Fin.sum_univ_eight]
  C_sq := by
    dsimp [matrixEnd]
    change Matrix.mulVecLin sectorwiseCayleyMat ∘ₗ
        Matrix.mulVecLin sectorwiseCayleyMat = _
    rw [← Matrix.mulVecLin_mul, sectorwiseCayleyMat_sq]
    ext x i
    simp [Matrix.mulVecLin, Matrix.mulVec, dotProduct, Fin.sum_univ_eight]
  M_sq := by
    dsimp [matrixEnd]
    change Matrix.mulVecLin longitudinalTransverseMat ∘ₗ
        Matrix.mulVecLin longitudinalTransverseMat = _
    rw [← Matrix.mulVecLin_mul, longitudinalTransverseMat_sq]
    ext x i
    simp [Matrix.mulVecLin, Matrix.mulVec, dotProduct, Fin.sum_univ_eight]
  M_K_comm := by
    dsimp [matrixEnd]
    change Matrix.mulVecLin longitudinalTransverseMat ∘ₗ
        Matrix.mulVecLin wittHestenesMat =
      Matrix.mulVecLin wittHestenesMat ∘ₗ
        Matrix.mulVecLin longitudinalTransverseMat
    rw [← Matrix.mulVecLin_mul, ← Matrix.mulVecLin_mul,
      longitudinalTransverseMat_comm_wittHestenes]
  M_C_comm := by
    dsimp [matrixEnd]
    change Matrix.mulVecLin longitudinalTransverseMat ∘ₗ
        Matrix.mulVecLin sectorwiseCayleyMat =
      Matrix.mulVecLin sectorwiseCayleyMat ∘ₗ
        Matrix.mulVecLin longitudinalTransverseMat
    rw [← Matrix.mulVecLin_mul, ← Matrix.mulVecLin_mul,
      sectorwiseCayleyMat_comm_longitudinalTransverse]
  cayley_hestenes_twisted := by
    dsimp [matrixEnd]
    have hmat : sectorwiseCayleyMat * wittHestenesMat =
        -(longitudinalTransverseMat * wittHestenesMat *
          sectorwiseCayleyMat) := by
      calc
        sectorwiseCayleyMat * wittHestenesMat =
            (sectorwiseCayleyMat * wittHestenesMat) * 1 := by simp
        _ = (sectorwiseCayleyMat * wittHestenesMat) *
            (sectorwiseCayleyMat * sectorwiseCayleyMat) := by
              rw [sectorwiseCayleyMat_sq]
        _ = ((sectorwiseCayleyMat * wittHestenesMat) *
            sectorwiseCayleyMat) * sectorwiseCayleyMat := by
              noncomm_ring
        _ = (-(longitudinalTransverseMat * wittHestenesMat)) *
            sectorwiseCayleyMat := by
              rw [sectorwiseCayleyMat_wittHestenes_sector_twist]
        _ = -(longitudinalTransverseMat * wittHestenesMat *
            sectorwiseCayleyMat) := by noncomm_ring
    simpa [Matrix.mulVecLin_mul, LinearMap.comp_assoc] using
      congrArg Matrix.mulVecLin hmat

theorem wittGradedDatum_combined_square :
    (wittGradedDatum.C * wittGradedDatum.K) *
        (wittGradedDatum.C * wittGradedDatum.K) = wittGradedDatum.M :=
  CayleyHestenesGradedDatum.combined_square wittGradedDatum

theorem wittGradedDatum_plus_packet :
    (wittGradedDatum.C * wittGradedDatum.K +
        wittGradedDatum.K * wittGradedDatum.C) *
        ((1 : WittEnd) + wittGradedDatum.M) = 0 :=
  twisted_cayley_plus_projector_packet wittGradedDatum

theorem wittGradedDatum_minus_packet :
    (wittGradedDatum.C * wittGradedDatum.K -
        wittGradedDatum.K * wittGradedDatum.C) *
        ((1 : WittEnd) - wittGradedDatum.M) = 0 :=
  twisted_cayley_minus_projector_packet wittGradedDatum

end InfoGeometry.Canonical.CayleyHestenesWittGradedConcreteBridge
