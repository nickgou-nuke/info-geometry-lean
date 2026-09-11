import InfoGeometry.OperatorAlgebra.CantorBernoulliMatrixUnitSandwich
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.OperatorAlgebra.CantorBernoulliFiniteMatrixRepresentationBridge
import InfoGeometry.OperatorAlgebra.CantorBernoulliKMSStateBridge

/-!
# Verified finite coefficient probe

This owner records the basis-level probe used by the eventual finite
faithfulness theorem.  The full matrix-sum extraction is intentionally not
promoted until its finite linearity normalization is kernel checked.
-/

noncomputable section

open scoped BigOperators

namespace InfoGeometry.OperatorAlgebra.CantorBernoulliFiniteMatrixFaithfulness

open InfoGeometry.OperatorAlgebra.CantorBernoulliCuntzOperatorTreeBridge
open InfoGeometry.OperatorAlgebra.CantorBernoulliFiniteMatrixUnitBridge
open InfoGeometry.OperatorAlgebra.CantorBernoulliFiniteMatrixRepresentationBridge
open InfoGeometry.OperatorAlgebra.CantorBernoulliMatrixUnitSandwich
open InfoGeometry.Canonical.UHFInductiveColimitBoundary
open InfoGeometry.Canonical.CantorBernoulliL2OperatorTransport
open InfoGeometry.OperatorAlgebra.CantorBernoulliKMSStateBridge

private theorem finset_sum_comp
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (g : ι → BoundedL2Operator)
    (f : BoundedL2Operator) :
    (s.sum g).comp f = s.sum (fun i => (g i).comp f) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      simp only [Finset.sum_insert hi, ContinuousLinearMap.add_comp, ih]

private theorem comp_finset_sum
    {ι : Type*} [DecidableEq ι] (f : BoundedL2Operator) (s : Finset ι)
    (g : ι → BoundedL2Operator) :
    f.comp (s.sum g) = s.sum (fun i => f.comp (g i)) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      simp only [Finset.sum_insert hi, ContinuousLinearMap.comp_add, ih]

private theorem finset_sum_comp_univ
    {ι : Type*} [Fintype ι] [DecidableEq ι] (g : ι → BoundedL2Operator)
    (f : BoundedL2Operator) :
    (∑ i : ι, g i).comp f = ∑ i : ι, (g i).comp f := by
  exact finset_sum_comp Finset.univ g f

private theorem comp_finset_sum_univ
    {ι : Type*} [Fintype ι] [DecidableEq ι] (f : BoundedL2Operator)
    (g : ι → BoundedL2Operator) :
    f.comp (∑ i : ι, g i) = ∑ i : ι, f.comp (g i) := by
  exact comp_finset_sum f Finset.univ g

private theorem bitWord_comp_sum
    (n : ℕ) (f : BoundedL2Operator)
    (g : BitWord n → BoundedL2Operator) :
    f.comp (∑ i : BitWord n, g i) = ∑ i : BitWord n, f.comp (g i) := by
  exact comp_finset_sum f Finset.univ g

private theorem bitWord_sum_comp
    (n : ℕ) (g : BitWord n → BoundedL2Operator)
    (f : BoundedL2Operator) :
    (∑ i : BitWord n, g i).comp f = ∑ i : BitWord n, (g i).comp f := by
  exact finset_sum_comp Finset.univ g f

theorem bitWordUnit_sandwich_single
    (n : ℕ) (a b u v : BitWord n) (c : ℂ) :
    (operatorWordDag (List.ofFn u)).comp
        ((bitWordMatrixLinearRepresentation n (Matrix.single a b c)).comp
          (operatorWord (List.ofFn v))) =
      if u = a then
        if b = v then c • ContinuousLinearMap.id ℂ L2Boundary else 0
      else 0 := by
  rw [bitWordMatrixLinearRepresentation_single_smul]
  simp only [ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul]
  rw [bitWordUnit_sandwich]
  by_cases hua : u = a <;> by_cases hbv : b = v <;> simp [hua, hbv]

theorem bitWordMatrixLinearRepresentation_sandwich
    (n : ℕ) (A : BitWordMatrixStage n) (u v : BitWord n) :
    (operatorWordDag (List.ofFn u)).comp
        ((bitWordMatrixLinearRepresentation n A).comp
          (operatorWord (List.ofFn v))) =
      A u v • ContinuousLinearMap.id ℂ L2Boundary := by
  classical
  change (operatorWordDag (List.ofFn u)).comp
      ((∑ i : BitWord n, ∑ j : BitWord n, A i j • bitWordUnit n i j).comp
        (operatorWord (List.ofFn v))) = _
  rw [bitWord_sum_comp, bitWord_comp_sum]
  simp_rw [← ContinuousLinearMap.comp_assoc, bitWord_comp_sum]
  simp only [bitWord_sum_comp]
  simp_rw [ContinuousLinearMap.comp_smul, ContinuousLinearMap.smul_comp,
    ContinuousLinearMap.comp_assoc]
  simp_rw [bitWordUnit_sandwich]
  simp [eq_comm]

theorem bitWordMatrixLinearRepresentation_injective
    (n : ℕ) : Function.Injective (bitWordMatrixLinearRepresentation n) := by
  intro A B hAB
  apply Matrix.ext
  intro u v
  apply (smul_left_injective ℂ (show (ContinuousLinearMap.id ℂ L2Boundary) ≠ 0 by
    intro hzero
    have hstate := congrArg cantorVacuumState hzero
    rw [cantorVacuumState_id] at hstate
    simpa [cantorVacuumState] using hstate))
  change A u v • ContinuousLinearMap.id ℂ L2Boundary =
    B u v • ContinuousLinearMap.id ℂ L2Boundary
  rw [← bitWordMatrixLinearRepresentation_sandwich n A u v,
    ← bitWordMatrixLinearRepresentation_sandwich n B u v]
  exact congrArg (fun T =>
    (operatorWordDag (List.ofFn u)).comp
      (T.comp (operatorWord (List.ofFn v)))) hAB

end InfoGeometry.OperatorAlgebra.CantorBernoulliFiniteMatrixFaithfulness
