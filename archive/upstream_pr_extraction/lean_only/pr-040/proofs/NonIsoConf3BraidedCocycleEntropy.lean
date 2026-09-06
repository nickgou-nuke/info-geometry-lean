import proofs.NonIsoConf3PairwiseNonisotropicCohomology

/-!
# Braided cocycle / Wilson entropy layer for non-isotropic Conf3

The arity-three configuration graph is a triangle.  This file models edge
log-ratios as an additive `1`-cochain on that triangle.

* `a12`, `a23`, `a13` are logarithmic edge potentials;
* the Wilson/entropy cycle defect is `a12 + a23 - a13`;
* detailed balance is the vanishing of that defect;
* broken detailed balance is a nonzero cycle defect;
* reversing the braid/orientation negates the defect.

This is a finite algebraic layer; no analytic logarithm theorem is asserted.
-/

namespace NonIsoConf3BraidedCocycleEntropy

/-- Additive edge log-ratios on the oriented triangle `1 -> 2 -> 3`. -/
structure EdgeLogCochain where
  a12 : ℝ
  a23 : ℝ
  a13 : ℝ

/-- Wilson/entropy defect around the triangle.  It vanishes exactly when the
direct edge `13` equals the composed edge path `12 + 23`. -/
def cycleDefect (A : EdgeLogCochain) : ℝ :=
  A.a12 + A.a23 - A.a13

/-- Detailed balance means no entropy production around the triangle cycle. -/
def DetailedBalance (A : EdgeLogCochain) : Prop :=
  cycleDefect A = 0

/-- Broken detailed balance is a nonzero Wilson/entropy cycle. -/
def BrokenDetailedBalance (A : EdgeLogCochain) : Prop :=
  cycleDefect A ≠ 0

/-- The cocycle condition is the same finite equation as detailed balance. -/
def IsTriangleCocycle (A : EdgeLogCochain) : Prop :=
  A.a13 = A.a12 + A.a23

/-- A triangle cocycle has zero Wilson/entropy defect. -/
theorem cocycle_iff_detailed_balance (A : EdgeLogCochain) :
    IsTriangleCocycle A ↔ DetailedBalance A := by
  constructor
  · intro h
    unfold IsTriangleCocycle at h
    unfold DetailedBalance cycleDefect
    linarith
  · intro h
    unfold DetailedBalance cycleDefect at h
    unfold IsTriangleCocycle
    linarith

/-- Nonzero defect is exactly broken detailed balance. -/
theorem broken_detailed_balance_iff_nonzero_defect (A : EdgeLogCochain) :
    BrokenDetailedBalance A ↔ cycleDefect A ≠ 0 := by
  rfl

/-- Reverse the braid/orientation of the triangle. -/
def reverseBraid (A : EdgeLogCochain) : EdgeLogCochain where
  a12 := -A.a23
  a23 := -A.a12
  a13 := -A.a13

/-- Braid/orientation reversal negates the Wilson/entropy cycle. -/
theorem cycleDefect_reverseBraid (A : EdgeLogCochain) :
    cycleDefect (reverseBraid A) = -cycleDefect A := by
  unfold cycleDefect reverseBraid
  ring

/-- Detailed balance is invariant under braid/orientation reversal. -/
theorem detailedBalance_reverseBraid (A : EdgeLogCochain)
    (h : DetailedBalance A) :
    DetailedBalance (reverseBraid A) := by
  unfold DetailedBalance at *
  rw [cycleDefect_reverseBraid A]
  rw [h]
  norm_num

/-- Broken detailed balance is invariant under braid/orientation reversal. -/
theorem brokenDetailedBalance_reverseBraid (A : EdgeLogCochain)
    (h : BrokenDetailedBalance A) :
    BrokenDetailedBalance (reverseBraid A) := by
  unfold BrokenDetailedBalance at *
  rw [cycleDefect_reverseBraid A]
  intro hz
  apply h
  linarith

/-- Capstone finite package: edge cochains, Wilson defect, cocycle balance, and
braid reversal all compile without invoking analytic logarithms. -/
theorem braided_cocycle_entropy_synthesis (A : EdgeLogCochain) :
    (IsTriangleCocycle A ↔ DetailedBalance A) ∧
    (BrokenDetailedBalance A ↔ cycleDefect A ≠ 0) ∧
    cycleDefect (reverseBraid A) = -cycleDefect A :=
  ⟨cocycle_iff_detailed_balance A,
    broken_detailed_balance_iff_nonzero_defect A,
    cycleDefect_reverseBraid A⟩

end NonIsoConf3BraidedCocycleEntropy
