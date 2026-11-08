import InfoGeometry.Canonical.SplitCliffordTensorBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Clifford.Cl11Matrix

open scoped TensorProduct

noncomputable section

/-!
# Native split-Clifford tensor-step dimension

This owner keeps the finite-dimensional calculation on the native Mathlib
Clifford quotient.  The recursive stage equivalence is `CliffordAlgebra.prodEquiv`;
the graded tensor carrier is transferred to the ordinary tensor product by
`GradedTensorProduct.of`; the dimension calculation is then Mathlib's
`Module.finrank_tensorProduct`.

No matrix-entry calculation is used here.  Matrix stages remain an executable
readout owned by `Cl11TensorTower`.
-/

namespace InfoGeometry.Clifford.SplitCliffordNativeTensorFinrank

open InfoGeometry.CliffordTower
open InfoGeometry.Canonical.SplitCliffordTensorBridge

private noncomputable def gradedTensorToTensor (n : ℕ) :
    CliffordAlgebra.evenOdd InfoGeometry.CliffordTower.Q11
          ᵍ⊗[ℝ] CliffordAlgebra.evenOdd (Qsplit n)
      ≃ₗ[ℝ]
    TensorProduct ℝ (CliffordAlgebra InfoGeometry.CliffordTower.Q11)
      (CliffordAlgebra (Qsplit n)) :=
  (GradedTensorProduct.of ℝ
      (CliffordAlgebra.evenOdd InfoGeometry.CliffordTower.Q11)
      (CliffordAlgebra.evenOdd (Qsplit n))).symm

private theorem q11_eq_cl11Matrix_q11 :
    InfoGeometry.CliffordTower.Q11 = InfoGeometry.Clifford.Cl11Matrix.q11 := by
  ext v
  simp [InfoGeometry.CliffordTower.Q11,
    InfoGeometry.Clifford.Cl11Matrix.q11,
    InfoGeometry.Clifford.splitQ11_apply,
    CliffordAlgebraQuaternion.Q]
  ring

private theorem native_cl11_finrank :
    Module.finrank ℝ
        (CliffordAlgebra InfoGeometry.CliffordTower.Q11) = 4 := by
  rw [q11_eq_cl11Matrix_q11]
  exact InfoGeometry.Clifford.Cl11Matrix.finrank_cl11

/-- The native graded tensor step has the expected factor-four dimension. -/
theorem gradedTensorStep_finrank (n : ℕ) :
    Module.finrank ℝ
        (CliffordAlgebra.evenOdd InfoGeometry.CliffordTower.Q11
          ᵍ⊗[ℝ] CliffordAlgebra.evenOdd (Qsplit n)) =
      4 * Module.finrank ℝ (CliffordAlgebra (Qsplit n)) := by
  rw [(gradedTensorToTensor n).finrank_eq]
  rw [Module.finrank_tensorProduct, native_cl11_finrank]

/-- Native Mathlib proof of the split-Clifford stage dimension recurrence. -/
theorem splitClNNAlg_finrank_succ (n : ℕ) :
    Module.finrank ℝ (SplitClNNAlg (n + 1)) =
      4 * Module.finrank ℝ (SplitClNNAlg n) := by
  rw [(splitCliffordTensorStepEquiv n).toLinearEquiv.finrank_eq]
  change Module.finrank ℝ
      (CliffordAlgebra.evenOdd InfoGeometry.CliffordTower.Q11
        ᵍ⊗[ℝ] CliffordAlgebra.evenOdd (Qsplit n)) =
      4 * Module.finrank ℝ (CliffordAlgebra (Qsplit n))
  exact gradedTensorStep_finrank n

end InfoGeometry.Clifford.SplitCliffordNativeTensorFinrank
