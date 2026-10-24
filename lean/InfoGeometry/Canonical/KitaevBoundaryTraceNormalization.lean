/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.MatrixTwoNoncommutativity
import InfoGeometry.Canonical.KitaevBoundaryFaithful
import InfoGeometry.Canonical.KitaevBoundaryTracePairing
import InfoGeometry.Canonical.ReflexiveMatrixTrace

/-! Exact trace normalization on the concrete two-site matrix carrier.
The metric pairing is transported with the split adjoint, not ordinary star. -/
noncomputable section
namespace InfoGeometry.Canonical.KitaevBoundaryTraceNormalization
open CARMajoranaFiniteBridge KitaevConcreteBoundary KitaevBoundaryDiracPair
open KitaevBoundaryAlgebra KitaevBoundaryTracePairing ReflexiveNilpotentFlows

theorem boundaryOccupation_trace : Matrix.trace boundaryOccupation = (2 : ℂ) := by
  have h := trace_pair_support_scale
    (Matrix.traceLinearMap (Fin 2 × Fin 2) ℂ ℂ) Matrix.trace_mul_comm
    (boundary_support (by decide) twoSiteOperators)
  change (2 : ℂ) * Matrix.trace boundaryOccupation = Matrix.trace (1 : ChainOp) at h
  norm_num [Matrix.trace_one] at h
  linear_combination (1 / 2 : ℂ) * h

theorem boundaryMatrixHom_trace (M : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix.trace (boundaryMatrixHom (by decide) twoSiteOperators M) = 2 * Matrix.trace M := by
  have h := trace_pairMatrixLinear
    (Matrix.traceLinearMap (Fin 2 × Fin 2) ℂ ℂ) Matrix.trace_mul_comm
    (boundaryAnnihilation_sq (by decide) twoSiteOperators)
    (boundaryCreation_sq (by decide) twoSiteOperators)
    (boundary_reflexive (by decide) twoSiteOperators).1
    (boundary_reflexive (by decide) twoSiteOperators).2 M
  change Matrix.trace (boundaryMatrixHom (by decide) twoSiteOperators M) =
    Matrix.trace boundaryOccupation * Matrix.trace M at h
  rw [boundaryOccupation_trace] at h
  exact h

theorem boundaryMatrixHom_dirac_trace (M N : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix.trace (boundaryMatrixHom (by decide) twoSiteOperators M *
      twoSiteKreinData.diracAdjoint (boundaryMatrixHom (by decide) twoSiteOperators N)) =
      2 * Matrix.trace (M * (pairDiracMetric * N.conjTranspose * pairDiracMetric)) := by
  have h : twoSiteKreinData.diracAdjoint (boundaryMatrixHom (by decide) twoSiteOperators N) =
      boundaryMatrixHom (by decide) twoSiteOperators
        (pairDiracMetric * N.conjTranspose * pairDiracMetric) :=
    KitaevBoundaryFaithful.boundaryMatrixHom_dirac (by decide) twoSiteOperators
      (twoSite_star 0) (twoSite_star 3) N
  rw [h]
  rw [← map_mul, boundaryMatrixHom_trace]

/-- A concrete negative diagonal value of the Dirac trace pairing. -/
theorem boundary_dirac_trace_negative :
    let M : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 0, 0]
    Matrix.trace (boundaryMatrixHom (by decide) twoSiteOperators M *
      twoSiteKreinData.diracAdjoint (boundaryMatrixHom (by decide) twoSiteOperators M)) = -2 := by
  dsimp only
  rw [boundaryMatrixHom_dirac_trace]
  norm_num [pairDiracMetric, Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two]

end InfoGeometry.Canonical.KitaevBoundaryTraceNormalization
