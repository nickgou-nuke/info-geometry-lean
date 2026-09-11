import InfoGeometry.OperatorAlgebra.SplitOctonionPeirceYangBaxterBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.OperatorAlgebra.CantorBernoulliCuntzOperatorTreeBridge
import InfoGeometry.Topological.FibonacciBraiding

/-!
# Finite braid/Cuntz branch transport

This owner exposes the finite, already-proved transport boundary between the
Peirce branch compression and the Fibonacci braid readout.  It does not
identify the nonassociative split-octonion product with a Cuntz algebra, nor
does it assert a colimit representation theorem.
-/

namespace InfoGeometry.Categorical.BraidCuntzEquivalence

open InfoGeometry.Canonical.FiniteMajoranaBraiding
open InfoGeometry.OperatorAlgebra.SplitOctonions.Multiplication
open InfoGeometry.OperatorAlgebra.SplitOctonions.SymplecticFoundation
open InfoGeometry.OperatorAlgebra.SplitOctonions.PeirceYangBaxterBridge
open InfoGeometry.OperatorAlgebra.SplitOctonions.CuntzInductionBridge
open InfoGeometry.OperatorAlgebra.CantorBernoulliCuntzOperatorTreeBridge

abbrev BranchBraidReadout (Gate : Type*) :=
  SplitOct → BraidWord → Gate

def peirceBranchReadout (Gate : Type*)
    (readout : Equiv.Perm ℕ → SplitOct → Gate) : BranchBraidReadout Gate :=
  fun X w => peirceCompressedBraidReadout Gate readout X w

/-! ## Cuntz branch-word readbacks

The Cuntz side already has a native operator-tree carrier.  These lemmas only
identify its one-letter and recursive word forms; they do not introduce a
second branch operator or assert a braid representation on the operator tree.
-/

@[simp] theorem operatorWord_singleton (b : Bool) :
    operatorWord [b] = branchOperator b := by
  simp [operatorWord]

theorem operatorWord_cons_eq_branch_comp (b : Bool) (w : List Bool) :
    operatorWord (b :: w) = (branchOperator b).comp (operatorWord w) := by
  rfl

theorem operatorCylinderProjection_cons_readout (b : Bool) (w : List Bool) :
    operatorCylinderProjection (b :: w) =
      (branchOperator b).comp
        ((operatorCylinderProjection w).comp (star (branchOperator b))) := by
  exact operatorCylinderProjection_cons b w

theorem peirceBranchReadout_yangBaxter
    (Gate : Type*) (readout : Equiv.Perm ℕ → SplitOct → Gate)
    (X : SplitOct) (i : ℕ) (left right : BraidWord) :
    peirceBranchReadout Gate readout X
        (left ++ [i, i + 1, i] ++ right) =
      peirceBranchReadout Gate readout X
        (left ++ [i + 1, i, i + 1] ++ right) := by
  exact peirceCompressedBraidReadout_yangBaxter_rewrite
    Gate readout X i left right

theorem peirceBranchReadout_commute
    (Gate : Type*) (readout : Equiv.Perm ℕ → SplitOct → Gate)
    (X : SplitOct) {i j : ℕ} (hsep : i + 1 < j)
    (left right : BraidWord) :
    peirceBranchReadout Gate readout X
        (left ++ [i, j] ++ right) =
      peirceBranchReadout Gate readout X
        (left ++ [j, i] ++ right) := by
  exact peirceCompressedBraidReadout_commute_rewrite
    Gate readout X hsep left right

theorem peirceBranchReadout_oneZ
    (Gate : Type*) (readout : Equiv.Perm ℕ → SplitOct → Gate)
    (w : BraidWord) :
    peirceBranchReadout Gate readout oneZ w =
      readout (evalBraidWord w) oneZ := by
  exact peirceCompressedBraidReadout_oneZ Gate readout w

theorem peirceBranchReadout_up_zero
    (Gate : Type*) (readout : Equiv.Perm ℕ → SplitOct → Gate)
    (i : Fin 3) (w : BraidWord) :
    peirceBranchReadout Gate readout (up i) w =
      readout (evalBraidWord w) zeroZ := by
  exact peirceCompressedBraidReadout_up_zero Gate readout i w

end InfoGeometry.Categorical.BraidCuntzEquivalence
