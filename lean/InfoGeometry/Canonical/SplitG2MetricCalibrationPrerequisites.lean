import InfoGeometry.Canonical.SplitG2MetricDerivedHodgeStar
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.LinearAlgebra.Alternating.DomCoprod

namespace InfoGeometry.Canonical

/-!
Finite metric data used by the split-`G₂` calibration bridge.

This owner stops at the Gram determinant.  It deliberately does not assert a
pseudo-Riemannian calibration inequality: that statement requires a choice of
causal class and a signed-volume convention.
-/

noncomputable def imaginaryGramMatrix (k : ℕ)
    (v w : Fin k → imaginarySplitOctonion) : Matrix (Fin k) (Fin k) ℚ :=
  fun i j => imaginarySplitMetric (v i) (w j)

noncomputable def imaginaryGramDet (k : ℕ)
    (v w : Fin k → imaginarySplitOctonion) : ℚ :=
  (imaginaryGramMatrix k v w).det

/-! Pairing of decomposable exterior elements via their Gram determinant. -/
noncomputable def decomposableExteriorMetricPairing (k : ℕ)
    (v w : Fin k → imaginarySplitOctonion) : ℚ :=
  imaginaryGramDet k v w

@[simp] theorem imaginaryGramMatrix_apply (k : ℕ)
    (v w : Fin k → imaginarySplitOctonion) (i j : Fin k) :
    imaginaryGramMatrix k v w i j = imaginarySplitMetric (v i) (w j) := rfl

theorem imaginaryGramDet_self_eq_matrix_det (k : ℕ)
    (v : Fin k → imaginarySplitOctonion) :
    imaginaryGramDet k v v = (imaginaryGramMatrix k v v).det := rfl

theorem decomposableExteriorMetricPairing_eq_gramDet (k : ℕ)
    (v w : Fin k → imaginarySplitOctonion) :
    decomposableExteriorMetricPairing k v w = imaginaryGramDet k v w := rfl

theorem imaginarySplitMetric_isSymm :
    imaginarySplitMetric.IsSymm := by
  refine ⟨fun x y => ?_⟩
  rw [imaginarySplitMetric_apply, imaginarySplitMetric_apply]
  change (coordinateSplitNorm (x.1 + y.1) - coordinateSplitNorm x.1 -
      coordinateSplitNorm y.1) / 2 =
    (coordinateSplitNorm (y.1 + x.1) - coordinateSplitNorm y.1 -
      coordinateSplitNorm x.1) / 2
  rw [add_comm x.1 y.1]
  ring

theorem decomposableExteriorMetricPairing_swap (k : ℕ)
    (v w : Fin k → imaginarySplitOctonion) :
    decomposableExteriorMetricPairing k v w =
      decomposableExteriorMetricPairing k w v := by
  have hmat : imaginaryGramMatrix k v w =
      (imaginaryGramMatrix k w v).transpose := by
    ext i j
    simp only [imaginaryGramMatrix, Matrix.transpose_apply]
    exact imaginarySplitMetric_isSymm.eq (v i) (w j)
  unfold decomposableExteriorMetricPairing imaginaryGramDet
  rw [hmat, Matrix.det_transpose]

/-! The split `3 + 4` exterior product is owned here because it is a generic
alternating construction, not a split-`G₂`-specific invariant. -/

noncomputable def scalarWedge34
    (α : SplitG2ThreeForms) (β : SplitG2FourForms) :
    AlternatingMap ℚ imaginarySplitOctonion ℚ (Fin 3 ⊕ Fin 4) :=
  (LinearMap.mul' ℚ ℚ).compAlternatingMap (α.domCoprod β)

noncomputable def wedge34
    (α : SplitG2ThreeForms) (β : SplitG2FourForms) :
    AlternatingMap ℚ imaginarySplitOctonion ℚ (Fin 7) :=
  (scalarWedge34 α β).domDomCongr finSumFinEquiv

theorem scalarWedge34_eq_mul_domCoprod
    (α : SplitG2ThreeForms) (β : SplitG2FourForms) :
    scalarWedge34 α β =
      (LinearMap.mul' ℚ ℚ).compAlternatingMap (α.domCoprod β) := rfl

theorem wedge34_swap_reindex
    (α : SplitG2ThreeForms) (β : SplitG2FourForms) :
    wedge34 α β =
      (scalarWedge34 α β).domDomCongr finSumFinEquiv := rfl

theorem imaginaryGramDet_fin_zero
    (v w : Fin 0 → imaginarySplitOctonion) :
    imaginaryGramDet 0 v w = 1 := by
  simp [imaginaryGramDet]

theorem imaginaryGramDet_fin_one
    (v w : Fin 1 → imaginarySplitOctonion) :
    imaginaryGramDet 1 v w = imaginarySplitMetric (v 0) (w 0) := by
  simp [imaginaryGramDet, imaginaryGramMatrix]

theorem imaginaryGramDet_fin_two
    (v w : Fin 2 → imaginarySplitOctonion) :
    imaginaryGramDet 2 v w =
      imaginarySplitMetric (v 0) (w 0) * imaginarySplitMetric (v 1) (w 1) -
        imaginarySplitMetric (v 0) (w 1) * imaginarySplitMetric (v 1) (w 0) := by
  simp [imaginaryGramDet, imaginaryGramMatrix, Matrix.det_fin_two]

end InfoGeometry.Canonical
