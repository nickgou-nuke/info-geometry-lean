import InfoGeometry.Canonical.NeutralPhaseSpaceNormalizationBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Source-side CAR for the scaled neutral normalization

The normalization bridge transports the scaled Clifford algebra to the
unscaled direct-CAR algebra.  This file records the corresponding source-side
mixed anticommutator explicitly, so the preservation theorem has a genuine
CAR statement on both sides.
-/

namespace InfoGeometry.Clifford.NeutralPhaseSpaceNormalizationSourceCAR

open InfoGeometry.Clifford.NeutralPhaseSpaceCore

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

theorem scaled_mixed_CAR (u : E) (ξ : Module.Dual ℝ E) :
    CliffordAlgebra.ι (canonicalNeutralForm (E := E)) (u, 0) *
        CliffordAlgebra.ι (canonicalNeutralForm (E := E)) (0, ξ) +
      CliffordAlgebra.ι (canonicalNeutralForm (E := E)) (0, ξ) *
        CliffordAlgebra.ι (canonicalNeutralForm (E := E)) (u, 0) =
      algebraMap ℝ (CliffordAlgebra (canonicalNeutralForm (E := E)))
        ((2 : ℝ) * ξ u) := by
  rw [CliffordAlgebra.ι_mul_ι_add_swap]
  congr 1
  rw [QuadraticMap.polar]
  simp [canonicalNeutralForm, canonicalNeutralBilin_apply]
  ring

theorem scaled_primal_square_zero (u : E) :
    CliffordAlgebra.ι (canonicalNeutralForm (E := E)) (u, 0) *
        CliffordAlgebra.ι (canonicalNeutralForm (E := E)) (u, 0) = 0 := by
  rw [CliffordAlgebra.ι_sq_scalar]
  simp [canonicalNeutralForm_apply]

theorem scaled_dual_square_zero (ξ : Module.Dual ℝ E) :
    CliffordAlgebra.ι (canonicalNeutralForm (E := E)) (0, ξ) *
        CliffordAlgebra.ι (canonicalNeutralForm (E := E)) (0, ξ) = 0 := by
  rw [CliffordAlgebra.ι_sq_scalar]
  simp [canonicalNeutralForm_apply]

end InfoGeometry.Clifford.NeutralPhaseSpaceNormalizationSourceCAR
