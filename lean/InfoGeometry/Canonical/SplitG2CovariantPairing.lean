import InfoGeometry.Canonical.SplitG2VolumeAndGramPairing
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

namespace InfoGeometry.Canonical

open scoped BigOperators

/-!
# Covariant form pairing from the native imaginary metric

This file supplies the missing inverse-metric *construction* without choosing
an arbitrary diagonal function.  The basis and its non-singularity proof are
explicit inputs: the repository has not yet selected an oriented `Fin 7`
basis of the imaginary carrier.
-/

abbrev SplitG2CovariantThreeForm :=
  AlternatingMap ℚ imaginarySplitOctonion ℚ (Fin 3)

noncomputable def splitG2MetricMatrix
    (b : Module.Basis (Fin 7) ℚ imaginarySplitOctonion) :
    Matrix (Fin 7) (Fin 7) ℚ :=
  LinearMap.BilinForm.toMatrixAux b imaginarySplitMetric

noncomputable def splitG2InverseMetricMatrix
    (b : Module.Basis (Fin 7) ℚ imaginarySplitOctonion) :
    Matrix (Fin 7) (Fin 7) ℚ :=
  (splitG2MetricMatrix b)⁻¹

noncomputable def splitG2ThreeFormPairing
    (b : Module.Basis (Fin 7) ℚ imaginarySplitOctonion)
    (α β : SplitG2CovariantThreeForm) : ℚ :=
  (1 / 6 : ℚ) *
    ∑ I : Fin 3 → Fin 7, ∑ J : Fin 3 → Fin 7,
      (Matrix.det (fun a c =>
        splitG2InverseMetricMatrix b (I a) (J c))) *
        α (fun a => b (I a)) * β (fun a => b (J a))

theorem splitG2MetricMatrix_apply
    (b : Module.Basis (Fin 7) ℚ imaginarySplitOctonion)
    (i j : Fin 7) :
    splitG2MetricMatrix b i j = imaginarySplitMetric (b i) (b j) := by
  exact LinearMap.BilinForm.toMatrixAux_apply imaginarySplitMetric b i j

theorem splitG2InverseMetricMatrix_is_inverse
    (b : Module.Basis (Fin 7) ℚ imaginarySplitOctonion)
    (h : (splitG2MetricMatrix b).det ≠ 0) :
    splitG2MetricMatrix b * splitG2InverseMetricMatrix b = 1 := by
  apply Matrix.mul_nonsing_inv
  exact isUnit_iff_ne_zero.mpr h

end InfoGeometry.Canonical
