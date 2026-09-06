import Mathlib
import InfoGeometry.Categorical.QuantumG2RMatrixBraidingDatum

open scoped TensorProduct
open TensorProduct

/-!
# A concrete finite checked-R realization

This is a kernel-checked finite witness for the representation-level interface.
It is intentionally a scalar test object over `ℚ`; it is not a construction of
the universal `U_q (𝔤₂)` R-matrix.
-/

namespace InfoGeometry.Categorical.QuantumG2RMatrixRealizationBridge

open InfoGeometry.Categorical.QuantumG2RMatrixBraidingDatum

abbrev mockV := ℚ

def mockCheckR : (mockV ⊗[ℚ] mockV) ≃ₗ[ℚ] (mockV ⊗[ℚ] mockV) :=
  LinearEquiv.smulOfNeZero ℚ (mockV ⊗[ℚ] mockV) 2 (by decide)

theorem mockMonodromy_ne_id :
    (mockCheckR.trans mockCheckR).toLinearMap ≠
      LinearMap.id := by
  intro h
  have h_eval := congrArg
    (fun f : (mockV ⊗[ℚ] mockV) →ₗ[ℚ] (mockV ⊗[ℚ] mockV) =>
      TensorProduct.rid ℚ ℚ (f ((1 : ℚ) ⊗ₜ[ℚ] (1 : ℚ)))) h
  simp [mockCheckR, LinearEquiv.trans_apply, TensorProduct.rid_tmul,
    smul_eq_mul] at h_eval
  norm_num at h_eval

theorem mock_map12_apply :
    (map12 ℚ mockV mockCheckR).toLinearMap =
      (2 : ℚ) • LinearMap.id := by
  ext
  simp [map12, mockCheckR]
  change (TensorProduct.assoc ℚ mockV mockV mockV)
      ((2 : ℚ) • (((1 : ℚ) ⊗ₜ[ℚ] (1 : ℚ)) ⊗ₜ[ℚ] (1 : ℚ))) = _
  rw [LinearEquiv.map_smul]
  rfl

theorem mock_map23_apply :
    (map23 ℚ mockV mockCheckR).toLinearMap =
      (2 : ℚ) • LinearMap.id := by
  ext
  simp [map23, mockCheckR]

theorem mock_yangBaxter :
    (map12 ℚ mockV mockCheckR).toLinearMap ∘ₗ
          (map23 ℚ mockV mockCheckR).toLinearMap ∘ₗ
          (map12 ℚ mockV mockCheckR).toLinearMap =
      (map23 ℚ mockV mockCheckR).toLinearMap ∘ₗ
          (map12 ℚ mockV mockCheckR).toLinearMap ∘ₗ
          (map23 ℚ mockV mockCheckR).toLinearMap := by
  rw [mock_map12_apply, mock_map23_apply]

noncomputable def mockQuantumG2RMatrixDatum : QuantumG2RMatrixDatum ℚ mockV where
  q := 2
  checkR := mockCheckR
  checkR12 := map12 ℚ mockV mockCheckR
  checkR23 := map23 ℚ mockV mockCheckR
  checkR12_eq := rfl
  checkR23_eq := rfl
  yangBaxter := mock_yangBaxter
  monodromy_nontrivial := mockMonodromy_ne_id

theorem mockDatum_monodromy_ne_id :
    g2Monodromy mockQuantumG2RMatrixDatum ≠ LinearMap.id :=
  g2Monodromy_ne_id mockQuantumG2RMatrixDatum

end InfoGeometry.Categorical.QuantumG2RMatrixRealizationBridge
