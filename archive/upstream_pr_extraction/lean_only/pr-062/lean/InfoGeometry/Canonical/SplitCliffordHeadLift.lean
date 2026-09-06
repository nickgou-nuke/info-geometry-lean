import InfoGeometry.Canonical.SplitCliffordTensorBridge
import InfoGeometry.Meta.Architecture

open scoped TensorProduct

/-!
# InfoGeometry.Canonical.SplitCliffordHeadLift

Tensor-side owner for the recursive split `Cl(1,1)` head atom inside each Bott
step `Cl(n+1,n+1) ≃ Cl(1,1) ⊗̂ Cl(n,n)`.

This file stays below any DIII/BdG rhetoric. It only records the algebra that
is already present on the recursive head channel:

- the head `J` generator,
- the head `K = Jε` generator,
- the induced head pseudoscalar `ε`,
- the lightlike null pair on the head factor.
-/

namespace InfoGeometry.Canonical.SplitCliffordHeadLift

open SplitCliffordTensorBridge
open InfoGeometry.Clifford.ClNN
open InfoGeometry.CliffordTower

/-- Head `J` generator on the Bott tensor side. -/
@[rep_depth krein]
noncomputable def headJTensor (n : ℕ) : SplitClNNTensorStep n :=
  (CliffordAlgebra.ι InfoGeometry.CliffordTower.Q11 (1, 0)) ᵍ⊗ₜ
    (1 : CliffordAlgebra (Qsplit n))

/-- Head `K` generator on the Bott tensor side. -/
@[rep_depth krein]
noncomputable def headKTensor (n : ℕ) : SplitClNNTensorStep n :=
  (CliffordAlgebra.ι InfoGeometry.CliffordTower.Q11 (0, 1)) ᵍ⊗ₜ
    (1 : CliffordAlgebra (Qsplit n))

/-- Head pseudoscalar `ε = JK` on the Bott tensor side. -/
@[rep_depth krein]
noncomputable def headEpsTensor (n : ℕ) : SplitClNNTensorStep n :=
  headJTensor n * headKTensor n

/-- Head lightlike `u_-` mode on the Bott tensor side. -/
@[rep_depth krein]
noncomputable def headNullMinusTensor (n : ℕ) : SplitClNNTensorStep n :=
  splitCliffordTensorStepEquiv n (gammaHeadNullMinus n)

/-- Head lightlike `u_+` mode on the Bott tensor side. -/
@[rep_depth krein]
noncomputable def headNullPlusTensor (n : ℕ) : SplitClNNTensorStep n :=
  splitCliffordTensorStepEquiv n (gammaHeadNullPlus n)

@[rep_depth krein, simp] theorem headJTensor_preimage (n : ℕ) :
    (splitCliffordTensorStepEquiv n).symm (headJTensor n)
      = CliffordAlgebra.ι (SplitClNNQuad (n + 1)) (headPair n (1, 0)) := by
  simp [headJTensor, SplitClNNQuad, headPair]

@[rep_depth krein, simp] theorem headKTensor_preimage (n : ℕ) :
    (splitCliffordTensorStepEquiv n).symm (headKTensor n)
      = CliffordAlgebra.ι (SplitClNNQuad (n + 1)) (headPair n (0, 1)) := by
  simp [headKTensor, SplitClNNQuad, headPair]

@[rep_depth krein, simp] theorem headJTensor_sq (n : ℕ) :
    headJTensor n * headJTensor n = 1 := by
  apply (splitCliffordTensorStepEquiv n).symm.injective
  simp [headJTensor_preimage, SplitClNNQuad, quad_headPair]

@[rep_depth krein, simp] theorem headKTensor_sq (n : ℕ) :
    headKTensor n * headKTensor n = -(1 : SplitClNNTensorStep n) := by
  apply (splitCliffordTensorStepEquiv n).symm.injective
  simp [headKTensor_preimage, SplitClNNQuad, quad_headPair]

@[rep_depth krein, simp] theorem headJTensor_mul_headKTensor_add_swap (n : ℕ) :
    headJTensor n * headKTensor n + headKTensor n * headJTensor n = 0 := by
  have hpolar :
      QuadraticMap.polar (SplitClNNQuad (n + 1))
        (headPair n (1, 0)) (headPair n (0, 1)) = 0 := by
    have hsum :
        headPair n (1, 0) + headPair n (0, 1) = headPair n (1, 1) := by
      change (((1, 0), 0) + ((0, 1), 0)) = (((1, 1), 0))
      simp
    rw [QuadraticMap.polar, hsum]
    simp [SplitClNNQuad, headPair]
  apply (splitCliffordTensorStepEquiv n).symm.injective
  simpa [headJTensor_preimage, headKTensor_preimage, hpolar] using
    (CliffordAlgebra.ι_mul_ι_add_swap
      (Q := SplitClNNQuad (n + 1)) (headPair n (1, 0)) (headPair n (0, 1)))

@[rep_depth krein, simp] theorem headKTensor_mul_headJTensor (n : ℕ) :
    headKTensor n * headJTensor n = -(headEpsTensor n) := by
  exact eq_neg_of_add_eq_zero_left (by
    change headKTensor n * headJTensor n + headJTensor n * headKTensor n = 0
    rw [add_comm]
    exact headJTensor_mul_headKTensor_add_swap n)

@[rep_depth krein, simp] theorem headEpsTensor_sq (n : ℕ) :
    headEpsTensor n * headEpsTensor n = 1 := by
  unfold headEpsTensor
  have hk :
      headKTensor n * headJTensor n = -(headJTensor n * headKTensor n) := by
    exact headKTensor_mul_headJTensor n
  calc
    (headJTensor n * headKTensor n) * (headJTensor n * headKTensor n)
        = headJTensor n * (headKTensor n * headJTensor n) * headKTensor n := by
            simp only [mul_assoc]
    _ = headJTensor n * (-(headJTensor n * headKTensor n)) * headKTensor n := by rw [hk]
    _ = -((headJTensor n * headJTensor n) * (headKTensor n * headKTensor n)) := by
          simp [mul_assoc]
    _ = 1 := by
          simp [headJTensor_sq, headKTensor_sq]

@[rep_depth krein, simp] theorem headJTensor_mul_headEpsTensor (n : ℕ) :
    headJTensor n * headEpsTensor n = headKTensor n := by
  unfold headEpsTensor
  calc
    headJTensor n * (headJTensor n * headKTensor n)
        = (headJTensor n * headJTensor n) * headKTensor n := by rw [← mul_assoc]
    _ = headKTensor n := by rw [headJTensor_sq, one_mul]

@[rep_depth krein, simp] theorem headEpsTensor_mul_headJTensor (n : ℕ) :
    headEpsTensor n * headJTensor n = -(headKTensor n) := by
  unfold headEpsTensor
  have hk :
      headKTensor n * headJTensor n = -(headJTensor n * headKTensor n) := by
    exact eq_neg_of_add_eq_zero_left (by
      simpa [add_comm] using (headJTensor_mul_headKTensor_add_swap n))
  calc
    (headJTensor n * headKTensor n) * headJTensor n
        = headJTensor n * (headKTensor n * headJTensor n) := by rw [mul_assoc]
    _ = headJTensor n * (-(headJTensor n * headKTensor n)) := by rw [hk]
    _ = -(headJTensor n * (headJTensor n * headKTensor n)) := by simp
    _ = -((headJTensor n * headJTensor n) * headKTensor n) := by rw [← mul_assoc]
    _ = -(headKTensor n) := by rw [headJTensor_sq, one_mul]

@[rep_depth krein, simp] theorem headKTensor_mul_headEpsTensor (n : ℕ) :
    headKTensor n * headEpsTensor n = headJTensor n := by
  unfold headEpsTensor
  have hk :
      headKTensor n * headJTensor n = -(headJTensor n * headKTensor n) := by
    exact eq_neg_of_add_eq_zero_left (by
      simpa [add_comm] using (headJTensor_mul_headKTensor_add_swap n))
  calc
    headKTensor n * (headJTensor n * headKTensor n)
        = (headKTensor n * headJTensor n) * headKTensor n := by rw [← mul_assoc]
    _ = (-(headJTensor n * headKTensor n)) * headKTensor n := by rw [hk]
    _ = -((headJTensor n * headKTensor n) * headKTensor n) := by simp
    _ = -(headJTensor n * (headKTensor n * headKTensor n)) := by rw [mul_assoc]
    _ = headJTensor n := by simp [headKTensor_sq]

@[rep_depth krein, simp] theorem headEpsTensor_mul_headKTensor (n : ℕ) :
    headEpsTensor n * headKTensor n = -(headJTensor n) := by
  unfold headEpsTensor
  calc
    (headJTensor n * headKTensor n) * headKTensor n
        = headJTensor n * (headKTensor n * headKTensor n) := by rw [mul_assoc]
    _ = -(headJTensor n) := by simp [headKTensor_sq]

private theorem headLeftFactor_tmul_smul (n : ℕ) (a : ℝ)
    (x : CliffordAlgebra InfoGeometry.CliffordTower.Q11) :
    (GradedTensorProduct.of ℝ
        (CliffordAlgebra.evenOdd InfoGeometry.CliffordTower.Q11)
        (CliffordAlgebra.evenOdd (Qsplit n)))
      (((a • x) ⊗ₜ[ℝ] (1 : CliffordAlgebra (Qsplit n))))
      = a •
          ((GradedTensorProduct.of ℝ
              (CliffordAlgebra.evenOdd InfoGeometry.CliffordTower.Q11)
              (CliffordAlgebra.evenOdd (Qsplit n)))
            (x ⊗ₜ[ℝ] (1 : CliffordAlgebra (Qsplit n)))) := by
  rw [← LinearEquiv.map_smul, TensorProduct.smul_tmul']

@[rep_depth krein, simp] theorem headNullMinusTensor_eq_formula (n : ℕ) :
    headNullMinusTensor n
      = (1 / 2 : ℝ) • (headJTensor n + headKTensor n) := by
  have hvec :
      ((1 / 2 : ℝ), (1 / 2 : ℝ))
        = (1 / 2 : ℝ) • (1, 0) + (1 / 2 : ℝ) • (0, 1) := by
    ext <;> norm_num
  have hι :
      CliffordAlgebra.ι InfoGeometry.CliffordTower.Q11 ((1 / 2 : ℝ), (1 / 2 : ℝ))
        = (1 / 2 : ℝ) • CliffordAlgebra.ι InfoGeometry.CliffordTower.Q11 (1, 0)
          + (1 / 2 : ℝ) • CliffordAlgebra.ι InfoGeometry.CliffordTower.Q11 (0, 1) := by
    rw [hvec]
    rw [LinearMap.map_add, LinearMap.map_smul, LinearMap.map_smul]
  calc
    headNullMinusTensor n
      = (CliffordAlgebra.ι InfoGeometry.CliffordTower.Q11 ((1 / 2 : ℝ), (1 / 2 : ℝ)))
          ᵍ⊗ₜ (1 : CliffordAlgebra (Qsplit n)) := by
            simpa [headNullMinusTensor] using splitCliffordTensorStep_headNullMinus n
    _ = (((1 / 2 : ℝ) • CliffordAlgebra.ι InfoGeometry.CliffordTower.Q11 (1, 0))
          + ((1 / 2 : ℝ) • CliffordAlgebra.ι InfoGeometry.CliffordTower.Q11 (0, 1)))
          ᵍ⊗ₜ (1 : CliffordAlgebra (Qsplit n)) := by rw [hι]
    _ = ((1 / 2 : ℝ) • CliffordAlgebra.ι InfoGeometry.CliffordTower.Q11 (1, 0))
          ᵍ⊗ₜ (1 : CliffordAlgebra (Qsplit n))
        + ((1 / 2 : ℝ) • CliffordAlgebra.ι InfoGeometry.CliffordTower.Q11 (0, 1))
          ᵍ⊗ₜ (1 : CliffordAlgebra (Qsplit n)) := by
            simp [GradedTensorProduct.tmul, TensorProduct.add_tmul]
    _ = (1 / 2 : ℝ) • headJTensor n + (1 / 2 : ℝ) • headKTensor n := by
          rw [GradedTensorProduct.tmul, GradedTensorProduct.tmul,
            headLeftFactor_tmul_smul, headLeftFactor_tmul_smul]
          simp [headJTensor, headKTensor]
    _ = (1 / 2 : ℝ) • (headJTensor n + headKTensor n) := by
          simp [smul_add]

@[rep_depth krein, simp] theorem headNullPlusTensor_eq_formula (n : ℕ) :
    headNullPlusTensor n
      = (1 / 2 : ℝ) • (headJTensor n - headKTensor n) := by
  have hvec :
      ((1 / 2 : ℝ), (-(1 / 2 : ℝ)))
        = (1 / 2 : ℝ) • (1, 0) - (1 / 2 : ℝ) • (0, 1) := by
    ext <;> norm_num
  have hι :
      CliffordAlgebra.ι InfoGeometry.CliffordTower.Q11 ((1 / 2 : ℝ), (-(1 / 2 : ℝ)))
        = (1 / 2 : ℝ) • CliffordAlgebra.ι InfoGeometry.CliffordTower.Q11 (1, 0)
          + (-(1 / 2 : ℝ)) • CliffordAlgebra.ι InfoGeometry.CliffordTower.Q11 (0, 1) := by
    rw [hvec]
    rw [sub_eq_add_neg, LinearMap.map_add, LinearMap.map_smul, LinearMap.map_neg,
      LinearMap.map_smul]
    simp [neg_smul]
  calc
    headNullPlusTensor n
      = (CliffordAlgebra.ι InfoGeometry.CliffordTower.Q11 ((1 / 2 : ℝ), (-(1 / 2 : ℝ))))
          ᵍ⊗ₜ (1 : CliffordAlgebra (Qsplit n)) := by
            simpa [headNullPlusTensor] using splitCliffordTensorStep_headNullPlus n
    _ = (((1 / 2 : ℝ) • CliffordAlgebra.ι InfoGeometry.CliffordTower.Q11 (1, 0))
          + ((-(1 / 2 : ℝ)) • CliffordAlgebra.ι InfoGeometry.CliffordTower.Q11 (0, 1)))
          ᵍ⊗ₜ (1 : CliffordAlgebra (Qsplit n)) := by rw [hι]
    _ = ((1 / 2 : ℝ) • CliffordAlgebra.ι InfoGeometry.CliffordTower.Q11 (1, 0))
          ᵍ⊗ₜ (1 : CliffordAlgebra (Qsplit n))
        + ((-(1 / 2 : ℝ)) • CliffordAlgebra.ι InfoGeometry.CliffordTower.Q11 (0, 1))
          ᵍ⊗ₜ (1 : CliffordAlgebra (Qsplit n)) := by
            simp [GradedTensorProduct.tmul, TensorProduct.add_tmul]
    _ = (1 / 2 : ℝ) • headJTensor n + (-(1 / 2 : ℝ)) • headKTensor n := by
          rw [GradedTensorProduct.tmul, GradedTensorProduct.tmul,
            headLeftFactor_tmul_smul, headLeftFactor_tmul_smul]
          simp [headJTensor, headKTensor]
    _ = (1 / 2 : ℝ) • (headJTensor n - headKTensor n) := by
          simp [sub_eq_add_neg, smul_add]

@[rep_depth krein, simp] theorem headNullMinusTensor_sq (n : ℕ) :
    headNullMinusTensor n * headNullMinusTensor n = 0 := by
  apply (splitCliffordTensorStepEquiv n).symm.injective
  simp [headNullMinusTensor]

@[rep_depth krein, simp] theorem headNullPlusTensor_sq (n : ℕ) :
    headNullPlusTensor n * headNullPlusTensor n = 0 := by
  apply (splitCliffordTensorStepEquiv n).symm.injective
  simp [headNullPlusTensor]

@[rep_depth krein, simp] theorem headNullMinusTensor_mul_headNullPlusTensor_add_swap
    (n : ℕ) :
    headNullMinusTensor n * headNullPlusTensor n
      + headNullPlusTensor n * headNullMinusTensor n = 1 := by
  apply (splitCliffordTensorStepEquiv n).symm.injective
  simp [headNullMinusTensor, headNullPlusTensor]

end InfoGeometry.Canonical.SplitCliffordHeadLift
