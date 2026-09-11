import InfoGeometry.Canonical.SplitCliffordHeadLift
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Meta.Architecture

open scoped TensorProduct

/-!
# InfoGeometry.Canonical.SplitCliffordHeadSuperBracket

Super-bracket identities for the recursive split `Cl(1,1)` head factor
inside the split `Cl(n,n)` Bott tower.

This is a strict coherence layer over `SplitCliffordHeadLift`:
- no new owners,
- no placeholders,
- all statements are direct consequences of already-proved head-lift algebra.
-/

namespace InfoGeometry.Canonical.SplitCliffordHeadSuperBracket

open InfoGeometry.Canonical.SplitCliffordTensorBridge
open InfoGeometry.Canonical.SplitCliffordHeadLift

/-- Head `u_-` null mode (transport alias to the head-lift owner). -/
@[rep_depth krein]
noncomputable abbrev headNullMinus (n : ℕ) : SplitClNNTensorStep n :=
  headNullMinusTensor n

/-- Head `u_+` null mode (transport alias to the head-lift owner). -/
@[rep_depth krein]
noncomputable abbrev headNullPlus (n : ℕ) : SplitClNNTensorStep n :=
  headNullPlusTensor n

/-- Even-even commutator on the head tensor step. -/
@[rep_depth krein]
noncomputable abbrev headCommutator {n : ℕ}
    (A B : SplitClNNTensorStep n) : SplitClNNTensorStep n :=
  A * B - B * A

/-- Odd-odd anticommutator on the head tensor step. -/
@[rep_depth krein]
noncomputable abbrev headAnticommutator {n : ℕ}
    (A B : SplitClNNTensorStep n) : SplitClNNTensorStep n :=
  A * B + B * A

/--
Head null-mode CAR package:
`u_-² = 0`, `u_+² = 0`, and `{u_-, u_+} = 1`.
-/
@[rep_depth transport]
theorem head_null_car_algebra (n : ℕ) :
    headNullMinus n * headNullMinus n = 0
      ∧ headNullPlus n * headNullPlus n = 0
      ∧ headAnticommutator (headNullMinus n) (headNullPlus n) = 1 := by
  refine ⟨headNullMinusTensor_sq n, headNullPlusTensor_sq n, ?_⟩
  simpa [headAnticommutator, headNullMinus, headNullPlus] using
    (headNullMinusTensor_mul_headNullPlusTensor_add_swap n)

/--
Head `J/K` commutator identity:
`[J, K] = 2ε` on the tensor head factor.
-/
@[rep_depth transport]
theorem head_jk_commutator (n : ℕ) :
    headCommutator (headJTensor n) (headKTensor n)
      = (2 : ℝ) • headEpsTensor n := by
  unfold headCommutator
  rw [headKTensor_mul_headJTensor]
  simp [headEpsTensor, sub_eq_add_neg, two_smul]

end InfoGeometry.Canonical.SplitCliffordHeadSuperBracket

