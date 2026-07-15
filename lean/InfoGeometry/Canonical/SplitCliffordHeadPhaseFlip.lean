import InfoGeometry.Canonical.SplitCliffordHeadLift
import InfoGeometry.Clifford.SplitQ11PhaseFlip
import Mathlib.LinearAlgebra.QuadraticForm.IsometryEquiv
import Mathlib.LinearAlgebra.QuadraticForm.Prod
import InfoGeometry.Meta.Architecture

/-!
# InfoGeometry.Canonical.SplitCliffordHeadPhaseFlip

Canonical head involution on the split `Cl(1,1)` factor inside the recursive
split `Cl(n,n)` tower.

This file stays below any DIII rhetoric. It only records the algebra
automorphism induced by flipping the `K`-axis on the head factor:

- `J` is fixed,
- `K` changes sign,
- the head pseudoscalar `ε = JK` changes sign,
- the lightlike null pair `u_- , u_+` is swapped.
-/

namespace SplitCliffordHeadPhaseFlip

open SplitCliffordHeadLift
open SplitCliffordTensorBridge
open InfoGeometry.Clifford.ClNN
open InfoGeometry.CliffordTower
open InfoGeometry.Clifford.SplitQ11PhaseFlip

/-- Head-carrier involution fixing the first split coordinate and negating the second. -/
@[rep_depth krein]
noncomputable def headKFlipCarrierEquiv (n : ℕ) :
    SplitClNNCarrier (n + 1) ≃ₗ[ℝ] SplitClNNCarrier (n + 1) :=
  phaseFlipLinearEquiv.prodCongr (LinearEquiv.refl ℝ (SplitClNNCarrier n))

/-- The head `K`-flip preserves the split quadratic form. -/
@[rep_depth krein]
noncomputable def headKFlipIsometry (n : ℕ) :
    (SplitClNNQuad (n + 1)).IsometryEquiv (SplitClNNQuad (n + 1)) where
  toLinearEquiv := headKFlipCarrierEquiv n
  map_app' := by
    intro X
    rcases X with ⟨x, xs⟩
    change InfoGeometry.CliffordTower.Q11 (phaseFlip x) + Qsplit n xs
      = InfoGeometry.CliffordTower.Q11 x + Qsplit n xs
    exact congrArg (fun t : ℝ => t + Qsplit n xs) (phaseFlip.map_app' x)

/-- Clifford-algebra automorphism induced by flipping the head `K`-axis. -/
@[rep_depth krein]
noncomputable def headKFlipAlg (n : ℕ) :
    SplitClNNAlg (n + 1) ≃ₐ[ℝ] SplitClNNAlg (n + 1) :=
  CliffordAlgebra.equivOfIsometry (headKFlipIsometry n)

/-- Tensor-side form of the head `K`-flip, transported through the Bott step. -/
@[rep_depth krein]
noncomputable def headKFlipTensor (n : ℕ) :
    SplitClNNTensorStep n ≃ₐ[ℝ] SplitClNNTensorStep n :=
  ((splitCliffordTensorStepEquiv n).symm.trans (headKFlipAlg n)).trans
    (splitCliffordTensorStepEquiv n)

@[rep_depth krein, simp] theorem headKFlipCarrier_headPair
    (n : ℕ) (x : ℝ × ℝ) :
    headKFlipCarrierEquiv n (headPair n x) = headPair n (x.1, -x.2) := by
  rcases x with ⟨a, b⟩
  rw [headKFlipCarrierEquiv, LinearEquiv.prodCongr_apply]
  rfl

@[rep_depth krein, simp] theorem headKFlipCarrier_tailLift
    (n : ℕ) (xs : SplitClNNCarrier n) :
    headKFlipCarrierEquiv n (tailLift n xs) = tailLift n xs := by
  rw [headKFlipCarrierEquiv, LinearEquiv.prodCongr_apply]
  simp [tailLift, phaseFlipLinearEquiv]

@[rep_depth krein, simp] theorem headKFlipCarrier_headNullMinus
    (n : ℕ) :
    headKFlipCarrierEquiv n (headNullMinus n) = headNullPlus n := by
  rw [headKFlipCarrierEquiv, LinearEquiv.prodCongr_apply]
  rfl

@[rep_depth krein, simp] theorem headKFlipCarrier_headNullPlus
    (n : ℕ) :
    headKFlipCarrierEquiv n (headNullPlus n) = headNullMinus n := by
  rw [headKFlipCarrierEquiv, LinearEquiv.prodCongr_apply]
  simp [headNullPlus, headNullMinus, headPair, phaseFlipLinearEquiv]

@[rep_depth krein, simp] theorem headKFlipIsometry_apply
    (n : ℕ) (v : SplitClNNCarrier (n + 1)) :
    headKFlipIsometry n v = headKFlipCarrierEquiv n v := by
  rfl

@[rep_depth krein, simp] theorem headKFlipAlg_apply_ι
    (n : ℕ) (v : SplitClNNCarrier (n + 1)) :
    headKFlipAlg n (CliffordAlgebra.ι (SplitClNNQuad (n + 1)) v)
      = CliffordAlgebra.ι (SplitClNNQuad (n + 1)) (headKFlipCarrierEquiv n v) := by
  change CliffordAlgebra.map (headKFlipIsometry n).toIsometry
      (CliffordAlgebra.ι (SplitClNNQuad (n + 1)) v)
    = CliffordAlgebra.ι (SplitClNNQuad (n + 1)) (headKFlipCarrierEquiv n v)
  rw [CliffordAlgebra.map_apply_ι]
  rfl

@[rep_depth krein, simp] theorem headKFlipAlg_headJ
    (n : ℕ) :
    headKFlipAlg n (CliffordAlgebra.ι (SplitClNNQuad (n + 1)) (headPair n (1, 0)))
      = CliffordAlgebra.ι (SplitClNNQuad (n + 1)) (headPair n (1, 0)) := by
  rw [headKFlipAlg_apply_ι, headKFlipCarrier_headPair]
  simp

@[rep_depth krein, simp] theorem headKFlipAlg_headK
    (n : ℕ) :
    headKFlipAlg n (CliffordAlgebra.ι (SplitClNNQuad (n + 1)) (headPair n (0, 1)))
      = -(CliffordAlgebra.ι (SplitClNNQuad (n + 1)) (headPair n (0, 1))) := by
  calc
    headKFlipAlg n (CliffordAlgebra.ι (SplitClNNQuad (n + 1)) (headPair n (0, 1)))
        = CliffordAlgebra.ι (SplitClNNQuad (n + 1))
            (headKFlipCarrierEquiv n (headPair n (0, 1))) := by
            rw [headKFlipAlg_apply_ι]
    _ = CliffordAlgebra.ι (SplitClNNQuad (n + 1)) (headPair n (0, -1)) := by
          rw [headKFlipCarrier_headPair]
    _ = -(CliffordAlgebra.ι (SplitClNNQuad (n + 1)) (headPair n (0, 1))) := by
          have hpair :
              headPair n (0, -1) = -headPair n (0, 1) := by
            change (((0 : ℝ), (-1 : ℝ)), (0 : SplitClNNCarrier n))
              = -(((0 : ℝ), (1 : ℝ)), (0 : SplitClNNCarrier n))
            ext <;> simp
          rw [hpair, (CliffordAlgebra.ι (SplitClNNQuad (n + 1))).map_neg]

@[rep_depth krein, simp] theorem headKFlipAlg_headNullMinus
    (n : ℕ) :
    headKFlipAlg n (gammaHeadNullMinus n) = gammaHeadNullPlus n := by
  unfold gammaHeadNullMinus gammaHeadNullPlus
  rw [headKFlipAlg_apply_ι, headKFlipCarrier_headNullMinus]

@[rep_depth krein, simp] theorem headKFlipAlg_headNullPlus
    (n : ℕ) :
    headKFlipAlg n (gammaHeadNullPlus n) = gammaHeadNullMinus n := by
  unfold gammaHeadNullMinus gammaHeadNullPlus
  rw [headKFlipAlg_apply_ι, headKFlipCarrier_headNullPlus]

@[rep_depth krein, simp] theorem headKFlipTensor_apply_headJTensor
    (n : ℕ) :
    headKFlipTensor n (headJTensor n) = headJTensor n := by
  change splitCliffordTensorStepEquiv n
      (headKFlipAlg n ((splitCliffordTensorStepEquiv n).symm (headJTensor n)))
    = headJTensor n
  rw [headJTensor_preimage, headKFlipAlg_headJ, splitCliffordTensorStep_headFactor]
  simp [headJTensor]

@[rep_depth krein, simp] theorem headKFlipTensor_apply_headKTensor
    (n : ℕ) :
    headKFlipTensor n (headKTensor n) = -(headKTensor n) := by
  change splitCliffordTensorStepEquiv n
      (headKFlipAlg n ((splitCliffordTensorStepEquiv n).symm (headKTensor n)))
    = -(headKTensor n)
  rw [headKTensor_preimage, headKFlipAlg_headK, map_neg, splitCliffordTensorStep_headFactor]
  simp [headKTensor]

@[rep_depth krein, simp] theorem headKFlipTensor_apply_headEpsTensor
    (n : ℕ) :
    headKFlipTensor n (headEpsTensor n) = -(headEpsTensor n) := by
  unfold headEpsTensor
  simp [headKFlipTensor_apply_headJTensor, headKFlipTensor_apply_headKTensor]

@[rep_depth krein, simp] theorem headKFlipTensor_apply_headNullMinusTensor
    (n : ℕ) :
    headKFlipTensor n (headNullMinusTensor n) = headNullPlusTensor n := by
  change splitCliffordTensorStepEquiv n
      (headKFlipAlg n ((splitCliffordTensorStepEquiv n).symm (headNullMinusTensor n)))
    = headNullPlusTensor n
  rw [headNullMinusTensor]
  simp [headKFlipAlg_headNullMinus, headNullPlusTensor]

@[rep_depth krein, simp] theorem headKFlipTensor_apply_headNullPlusTensor
    (n : ℕ) :
    headKFlipTensor n (headNullPlusTensor n) = headNullMinusTensor n := by
  change splitCliffordTensorStepEquiv n
      (headKFlipAlg n ((splitCliffordTensorStepEquiv n).symm (headNullPlusTensor n)))
    = headNullMinusTensor n
  rw [headNullPlusTensor]
  simp [headKFlipAlg_headNullPlus, headNullMinusTensor]

end SplitCliffordHeadPhaseFlip
