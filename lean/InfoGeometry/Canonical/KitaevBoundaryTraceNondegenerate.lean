/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.MatrixTwoNoncommutativity
/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.KitaevBoundaryTraceNormalization

/-! Nondegeneracy of the indefinite Dirac trace pairing on the actual
represented boundary algebra. No ambient-commutant classification is asserted. -/
noncomputable section
namespace InfoGeometry.Canonical.KitaevBoundaryTraceNondegenerate

open KitaevConcreteBoundary KitaevBoundaryAlgebra KitaevBoundaryTraceNormalization
open ReflexiveNilpotentFlows

theorem pairDiracMetric_sq :
    (pairDiracMetric : Matrix (Fin 2) (Fin 2) ℂ) * pairDiracMetric = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [pairDiracMetric, Matrix.mul_apply, Fin.sum_univ_two]

theorem pairDiracMetric_conjTranspose :
    (pairDiracMetric : Matrix (Fin 2) (Fin 2) ℂ).conjTranspose = pairDiracMetric := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pairDiracMetric, Matrix.conjTranspose_apply]

theorem source_dirac_involution (M : Matrix (Fin 2) (Fin 2) ℂ) :
    pairDiracMetric * (pairDiracMetric * M.conjTranspose * pairDiracMetric).conjTranspose *
      pairDiracMetric = M := by
  simp only [Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, pairDiracMetric_conjTranspose]
  calc
    _ = (pairDiracMetric * pairDiracMetric) * M *
        (pairDiracMetric * pairDiracMetric) := by noncomm_ring
    _ = M := by rw [pairDiracMetric_sq]; simp

theorem boundary_dirac_trace_left_separates (M : Matrix (Fin 2) (Fin 2) ℂ)
    (h : ∀ N : Matrix (Fin 2) (Fin 2) ℂ,
      Matrix.trace (boundaryMatrixHom (by decide) twoSiteOperators M *
        twoSiteKreinData.diracAdjoint (boundaryMatrixHom (by decide) twoSiteOperators N)) = 0) :
    M = 0 := by
  apply Matrix.ext_iff_trace_mul_right.mpr
  intro Y
  have ht := h (pairDiracMetric * Y.conjTranspose * pairDiracMetric)
  rw [boundaryMatrixHom_dirac_trace, source_dirac_involution] at ht
  have hz : Matrix.trace (M * Y) = 0 :=
    (mul_eq_zero.mp ht).resolve_left (by norm_num)
  simpa using hz

theorem boundary_dirac_trace_left_image_zero (M : Matrix (Fin 2) (Fin 2) ℂ)
    (h : ∀ N : Matrix (Fin 2) (Fin 2) ℂ,
      Matrix.trace (boundaryMatrixHom (by decide) twoSiteOperators M *
        twoSiteKreinData.diracAdjoint (boundaryMatrixHom (by decide) twoSiteOperators N)) = 0) :
    boundaryMatrixHom (by decide) twoSiteOperators M = 0 := by
  rw [boundary_dirac_trace_left_separates M h, map_zero]

theorem boundary_dirac_trace_right_separates (N : Matrix (Fin 2) (Fin 2) ℂ)
    (h : ∀ M : Matrix (Fin 2) (Fin 2) ℂ,
      Matrix.trace (boundaryMatrixHom (by decide) twoSiteOperators M *
        twoSiteKreinData.diracAdjoint (boundaryMatrixHom (by decide) twoSiteOperators N)) = 0) :
    N = 0 := by
  have hs : pairDiracMetric * N.conjTranspose * pairDiracMetric = 0 := by
    apply Matrix.ext_iff_trace_mul_right.mpr
    intro M
    have ht := h M
    rw [boundaryMatrixHom_dirac_trace] at ht
    have hz : Matrix.trace (M * (pairDiracMetric * N.conjTranspose * pairDiracMetric)) = 0 :=
      (mul_eq_zero.mp ht).resolve_left (by norm_num)
    calc
      Matrix.trace ((pairDiracMetric * N.conjTranspose * pairDiracMetric) * M) =
          Matrix.trace (M * (pairDiracMetric * N.conjTranspose * pairDiracMetric)) :=
        Matrix.trace_mul_comm _ _
      _ = Matrix.trace ((0 : Matrix (Fin 2) (Fin 2) ℂ) * M) := by simpa using hz
  have hh := congrArg (fun X : Matrix (Fin 2) (Fin 2) ℂ =>
    pairDiracMetric * X.conjTranspose * pairDiracMetric) hs
  simpa only [source_dirac_involution, Matrix.conjTranspose_zero, mul_zero, zero_mul] using hh

end InfoGeometry.Canonical.KitaevBoundaryTraceNondegenerate
