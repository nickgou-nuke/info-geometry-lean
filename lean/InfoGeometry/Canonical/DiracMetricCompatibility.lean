import InfoGeometry.Convex.HessianGeometry
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.Matrix.Order

namespace InfoGeometry.Canonical

open InfoGeometry.Convex
open scoped MatrixOrder

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/--
Lower owner for the spectral-root compatibility witness identifying the square
of a Dirac operator with the Hessian metric operator at a chosen basepoint.

This file isolates the root witness consumed by spectral, transport, and
geometry bridge layers without bundling the larger spectral-triple surface.
-/
structure DiracMetricCompatibility
    (D : E →L[ℝ] E) (H : HessianGeometry E) (x₀ : E) where
  dirac_sq_eq_metric : D * D = H.metricOp x₀

namespace DiracMetricCompatibility

section FiniteDimensional

variable [FiniteDimensional ℝ E]

private noncomputable def canonicalDiracLinearOfMetric
    (H : HessianGeometry E) (x₀ : E) : E →ₗ[ℝ] E :=
  let b : OrthonormalBasis (Fin (Module.finrank ℝ E)) ℝ E := stdOrthonormalBasis ℝ E
  let Φ : (E →ₗ[ℝ] E) ≃⋆ₐ[ℝ] Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
    LinearMap.toMatrixOrthonormal b
  Φ.symm (CFC.sqrt (Φ ((H.metricOp x₀).toLinearMap)))

/-- Canonical Dirac operator extracted as the matrix square root of the metric operator. -/
noncomputable def canonicalDiracOfMetric
    (H : HessianGeometry E) (x₀ : E) : E →L[ℝ] E :=
  (canonicalDiracLinearOfMetric (E := E) H x₀).toContinuousLinearMap

private theorem canonicalDiracOfMetric_sq_eq_metric
    (H : HessianGeometry E) (x₀ : E)
    (hSymm : (H.metricOp x₀).toLinearMap.IsSymmetric)
    (hQuad : ∀ u : E, 0 ≤ inner ℝ u (H.metricOp x₀ u)) :
    canonicalDiracOfMetric (E := E) H x₀ * canonicalDiracOfMetric (E := E) H x₀
      = H.metricOp x₀ := by
  let b : OrthonormalBasis (Fin (Module.finrank ℝ E)) ℝ E := stdOrthonormalBasis ℝ E
  let Φ : (E →ₗ[ℝ] E) ≃⋆ₐ[ℝ] Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
    LinearMap.toMatrixOrthonormal b
  have hPos : ((H.metricOp x₀).toLinearMap).IsPositive := by
    exact (LinearMap.isPositive_iff _).2 ⟨hSymm, fun u => by simpa [real_inner_comm] using hQuad u⟩
  have hMatPos : (Φ ((H.metricOp x₀).toLinearMap)).PosSemidef :=
    (LinearMap.posSemidef_toMatrix_iff b).2 hPos
  have hsqLin :
      canonicalDiracLinearOfMetric (E := E) H x₀ * canonicalDiracLinearOfMetric (E := E) H x₀
        = (H.metricOp x₀).toLinearMap := by
    have hDiracMatrix :
        Φ (canonicalDiracLinearOfMetric (E := E) H x₀)
          = CFC.sqrt (Φ ((H.metricOp x₀).toLinearMap)) := by
      change Φ (Φ.symm (CFC.sqrt (Φ ((H.metricOp x₀).toLinearMap))))
          = CFC.sqrt (Φ ((H.metricOp x₀).toLinearMap))
      exact Φ.apply_symm_apply _
    apply Φ.injective
    calc
      Φ (canonicalDiracLinearOfMetric (E := E) H x₀ * canonicalDiracLinearOfMetric (E := E) H x₀)
          = Φ (canonicalDiracLinearOfMetric (E := E) H x₀)
              * Φ (canonicalDiracLinearOfMetric (E := E) H x₀) := by
              exact Φ.map_mul _ _
      _ = CFC.sqrt (Φ ((H.metricOp x₀).toLinearMap))
            * CFC.sqrt (Φ ((H.metricOp x₀).toLinearMap)) := by
              simp [hDiracMatrix]
      _ = Φ ((H.metricOp x₀).toLinearMap) := by
            exact CFC.sqrt_mul_sqrt_self (Φ ((H.metricOp x₀).toLinearMap)) hMatPos.nonneg
  ext v
  have hv :
      (canonicalDiracLinearOfMetric (E := E) H x₀ * canonicalDiracLinearOfMetric (E := E) H x₀) v
        = ((H.metricOp x₀).toLinearMap) v :=
    congrArg (fun A : E →ₗ[ℝ] E => A v) hsqLin
  simpa [canonicalDiracOfMetric, ContinuousLinearMap.mul_apply] using hv

-- theorem-class: derived
/-- The canonical matrix-square-root Dirac operator is positive. -/
theorem canonicalDiracOfMetric_isPositive
    (H : HessianGeometry E) (x₀ : E)
    (hSymm : (H.metricOp x₀).toLinearMap.IsSymmetric)
    (hQuad : ∀ u : E, 0 ≤ inner ℝ u (H.metricOp x₀ u)) :
    (canonicalDiracOfMetric (E := E) H x₀).IsPositive := by
  let b : OrthonormalBasis (Fin (Module.finrank ℝ E)) ℝ E := stdOrthonormalBasis ℝ E
  let Φ : (E →ₗ[ℝ] E) ≃⋆ₐ[ℝ] Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
    LinearMap.toMatrixOrthonormal b
  have hPos : ((H.metricOp x₀).toLinearMap).IsPositive := by
    exact (LinearMap.isPositive_iff _).2 ⟨hSymm, fun u => by simpa [real_inner_comm] using hQuad u⟩
  have hMatPos : (Φ ((H.metricOp x₀).toLinearMap)).PosSemidef :=
    (LinearMap.posSemidef_toMatrix_iff b).2 hPos
  have hDiracMatrix :
      Φ (canonicalDiracLinearOfMetric (E := E) H x₀)
        = CFC.sqrt (Φ ((H.metricOp x₀).toLinearMap)) := by
    change Φ (Φ.symm (CFC.sqrt (Φ ((H.metricOp x₀).toLinearMap))))
        = CFC.sqrt (Φ ((H.metricOp x₀).toLinearMap))
    exact Φ.apply_symm_apply _
  have hDiracMatPos : (Φ (canonicalDiracLinearOfMetric (E := E) H x₀)).PosSemidef := by
    rw [hDiracMatrix]
    exact (Matrix.nonneg_iff_posSemidef).mp
      (CFC.sqrt_nonneg (Φ ((H.metricOp x₀).toLinearMap)))
  have hDiracPos : (canonicalDiracLinearOfMetric (E := E) H x₀).IsPositive :=
    (LinearMap.posSemidef_toMatrix_iff b).1 hDiracMatPos
  simpa [canonicalDiracOfMetric] using
    (LinearMap.isPositive_toContinuousLinearMap_iff
      (canonicalDiracLinearOfMetric (E := E) H x₀)).2 hDiracPos

/--
Canonical compatibility witness produced from the symmetric nonnegative quadratic form carried by
`H.metricOp x₀`.
-/
noncomputable def ofMetric
    (H : HessianGeometry E) (x₀ : E) :
    DiracMetricCompatibility (E := E)
      (canonicalDiracOfMetric (E := E) H x₀) H x₀ where
  dirac_sq_eq_metric := canonicalDiracOfMetric_sq_eq_metric (E := E) H x₀
    (H.metricOp_isSymmetric x₀) (fun u => H.metric_quadratic_nonneg x₀ u)

end FiniteDimensional

variable {D : E →L[ℝ] E} {H : HessianGeometry E} {x₀ : E}

-- theorem-class: derived
/-- The metric at the basepoint is recovered by applying the Dirac operator twice. -/
lemma inner_dirac_sq
    (C : DiracMetricCompatibility (E := E) D H x₀) (u v : E) :
    inner ℝ u (D (D v)) = H.metric x₀ u v := by
  rcases C with ⟨hSq⟩
  have h_eval : (D * D) v = D (D v) := rfl
  rw [← h_eval, hSq]
  rfl

end DiracMetricCompatibility

end InfoGeometry.Canonical
