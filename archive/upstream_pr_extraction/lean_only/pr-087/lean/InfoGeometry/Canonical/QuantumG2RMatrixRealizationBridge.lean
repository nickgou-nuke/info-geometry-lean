import Mathlib
import InfoGeometry.Canonical.QuantumG2RMatrixBraidingDatum

open scoped TensorProduct
open TensorProduct
open InfoGeometry.Canonical.QuantumG2RMatrixBraidingDatum

/-!
# A concrete finite realization of the checked-R interface

This owner supplies a small tensor-derived witness for the abstract
`QuantumG2RMatrixDatum` interface.  The carrier is one-dimensional over
`ℚ` and the checked R operator is scalar multiplication by `2`.  Thus all
Yang--Baxter and monodromy statements are proved in the tensor API itself.

This is deliberately a finite realization witness, not a construction of a
universal `U_q (g₂)` R-matrix.
-/

namespace InfoGeometry.Canonical.QuantumG2RMatrixRealizationBridge

abbrev mockV := ℚ

def mockCheckR : (mockV ⊗[ℚ] mockV) ≃ₗ[ℚ] (mockV ⊗[ℚ] mockV) :=
  LinearEquiv.smulOfNeZero ℚ (mockV ⊗[ℚ] mockV) 2 (by norm_num)

def mockCheckR12 :
    (mockV ⊗[ℚ] (mockV ⊗[ℚ] mockV)) ≃ₗ[ℚ]
      (mockV ⊗[ℚ] (mockV ⊗[ℚ] mockV)) :=
  (TensorProduct.assoc ℚ mockV mockV mockV).symm.trans $
    (TensorProduct.congr mockCheckR (LinearEquiv.refl ℚ mockV)).trans $
      TensorProduct.assoc ℚ mockV mockV mockV

def mockCheckR23 :
    (mockV ⊗[ℚ] (mockV ⊗[ℚ] mockV)) ≃ₗ[ℚ]
      (mockV ⊗[ℚ] (mockV ⊗[ℚ] mockV)) :=
  TensorProduct.congr (LinearEquiv.refl ℚ mockV) mockCheckR

lemma mockCheckR12_pure (a b c : mockV) :
    mockCheckR12 (a ⊗ₜ[ℚ] (b ⊗ₜ[ℚ] c)) =
      2 • (a ⊗ₜ[ℚ] (b ⊗ₜ[ℚ] c)) := by
  simp only [mockCheckR12, LinearEquiv.trans_apply,
    TensorProduct.assoc_symm_tmul, TensorProduct.congr_tmul,
    mockCheckR, LinearEquiv.smulOfNeZero_apply, LinearEquiv.refl_apply]
  change (TensorProduct.assoc ℚ mockV mockV mockV)
      (((2 • a) ⊗ₜ[ℚ] b) ⊗ₜ[ℚ] c) =
    2 • (a ⊗ₜ[ℚ] (b ⊗ₜ[ℚ] c))
  rw [TensorProduct.smul_tmul, TensorProduct.assoc_tmul]
  calc
    a ⊗ₜ[ℚ] ((2 • b) ⊗ₜ[ℚ] c) =
        a ⊗ₜ[ℚ] (b ⊗ₜ[ℚ] (2 • c)) := by
      exact congrArg (fun z : mockV ⊗[ℚ] mockV => a ⊗ₜ[ℚ] z)
        (TensorProduct.smul_tmul (R := ℚ) (2 : ℚ) b c)
    _ = 2 • (a ⊗ₜ[ℚ] (b ⊗ₜ[ℚ] c)) := by
      rw [TensorProduct.tmul_smul, TensorProduct.tmul_smul]

lemma mockCheckR23_pure (a b c : mockV) :
    mockCheckR23 (a ⊗ₜ[ℚ] (b ⊗ₜ[ℚ] c)) =
      2 • (a ⊗ₜ[ℚ] (b ⊗ₜ[ℚ] c)) := by
  simp only [mockCheckR23, TensorProduct.congr_tmul, mockCheckR,
    LinearEquiv.smulOfNeZero_apply, LinearEquiv.refl_apply]
  exact TensorProduct.tmul_smul (R := ℚ) (2 : ℚ) a
    (b ⊗ₜ[ℚ] c)

lemma mockCheckR12_apply (x : mockV ⊗[ℚ] (mockV ⊗[ℚ] mockV)) :
    mockCheckR12 x = 2 • x := by
  refine TensorProduct.induction_on x ?_ (fun a b => ?_) ?_
  · simp
  · refine TensorProduct.induction_on b ?_ (fun b c => mockCheckR12_pure a b c) ?_
    · simp
    · intro x y hx hy
      have htmul := TensorProduct.tmul_add (R := ℚ) a x y
      rw [htmul, map_add, hx, hy, smul_add]
  · intro x y hx hy
    rw [map_add, hx, hy, smul_add]

lemma mockCheckR23_apply (x : mockV ⊗[ℚ] (mockV ⊗[ℚ] mockV)) :
    mockCheckR23 x = 2 • x := by
  refine TensorProduct.induction_on x ?_ (fun a b => ?_) ?_
  · simp
  · refine TensorProduct.induction_on b ?_ (fun b c => mockCheckR23_pure a b c) ?_
    · simp
    · intro x y hx hy
      have htmul := TensorProduct.tmul_add (R := ℚ) a x y
      rw [htmul, map_add, hx, hy, smul_add]
  · intro x y hx hy
    rw [map_add, hx, hy, smul_add]

theorem mockYangBaxter :
    mockCheckR12.trans (mockCheckR23.trans mockCheckR12) =
      mockCheckR23.trans (mockCheckR12.trans mockCheckR23) := by
  apply LinearEquiv.ext
  intro x
  rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply,
    mockCheckR12_apply, mockCheckR23_apply, mockCheckR12_apply,
    LinearEquiv.trans_apply, LinearEquiv.trans_apply,
    mockCheckR23_apply, mockCheckR12_apply, mockCheckR23_apply]

theorem mockMonodromy_ne_id :
    mockCheckR.trans mockCheckR ≠
      LinearEquiv.refl ℚ (mockV ⊗[ℚ] mockV) := by
  intro h
  have h_eval := congrArg
    (fun f : (mockV ⊗[ℚ] mockV) ≃ₗ[ℚ] (mockV ⊗[ℚ] mockV) =>
      TensorProduct.rid ℚ ℚ (f ((1 : ℚ) ⊗ₜ[ℚ] (1 : ℚ)))) h
  simp [mockCheckR, LinearEquiv.trans_apply, TensorProduct.rid_tmul,
    smul_eq_mul] at h_eval
  norm_num at h_eval

/-- A concrete finite inhabitant of the abstract checked-R interface. -/
noncomputable def concreteQuantumG2RMatrixDatum :
    QuantumG2RMatrixDatum ℚ mockV where
  q := 2
  checkR := mockCheckR
  yangBaxter := by
    simpa [mockCheckR12, mockCheckR23] using mockYangBaxter
  monodromy_nontrivial := by
    exact mockMonodromy_ne_id

theorem concreteMonodromy_ne_id :
    g2Monodromy concreteQuantumG2RMatrixDatum ≠
      LinearEquiv.refl ℚ (mockV ⊗[ℚ] mockV) :=
  g2Monodromy_ne_id concreteQuantumG2RMatrixDatum

end InfoGeometry.Canonical.QuantumG2RMatrixRealizationBridge
