import InfoGeometry.Canonical.ThreeColorOperatorCrossCommutator
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# The native `ZMod 3` grading of the operator-valued Zorn carrier

The carrier is not given an additive or associative algebra structure here.
Instead, the three homogeneous sectors are expressed by their native
coordinates, and multiplication closure is proved directly from the native
coordinate formula.
-/

namespace InfoGeometry.Canonical

open InfoGeometry.Physics.NCG

variable {A : Type*} [Ring A]

inductive ChiralSector
  | diagonal
  | plus
  | minus
  deriving DecidableEq, Fintype

def chiralDegree : ChiralSector → ZMod 3
  | .diagonal => 0
  | .plus => 1
  | .minus => 2

def InSector (p : ChiralSector) (X : OperatorZornMatrix A) : Prop :=
  match p with
  | .diagonal =>
      X.sigma_plus = 0 ∧ X.sigma_minus = 0
  | .plus => X.n_plus = 0 ∧ X.n_minus = 0 ∧ X.sigma_minus = 0
  | .minus => X.n_plus = 0 ∧ X.n_minus = 0 ∧ X.sigma_plus = 0

@[simp] private lemma zornDot_zero_right (u : OperatorVector A) :
    NCZornElement.zornDot u 0 = 0 := by
  simp [NCZornElement.zornDot]

@[simp] private lemma zornDot_zero_left (u : OperatorVector A) :
    NCZornElement.zornDot 0 u = 0 := by
  simp [NCZornElement.zornDot]

@[simp] private lemma zornCross_zero_right (u : OperatorVector A) :
    NCZornElement.zornCross u 0 = 0 := by
  funext i
  fin_cases i <;> simp [NCZornElement.zornCross]

@[simp] private lemma zornCross_zero_left (u : OperatorVector A) :
    NCZornElement.zornCross 0 u = 0 := by
  funext i
  fin_cases i <;> simp [NCZornElement.zornCross]

theorem diagonal_mul_diagonal
    {X Y : OperatorZornMatrix A}
    (hX : InSector .diagonal X) (hY : InSector .diagonal Y) :
    InSector .diagonal (operatorZornMul X Y) := by
  rcases hX with ⟨hxp, hxm⟩
  rcases hY with ⟨hyp, hym⟩
  constructor
  · funext i
    fin_cases i <;>
      simp [InSector, operatorZornMul, NCZornElement.mul, hxp, hxm, hyp, hym]
  · funext i
    fin_cases i <;>
      simp [InSector, operatorZornMul, NCZornElement.mul, hxp, hxm, hyp, hym]

theorem diagonal_mul_plus
    {X Y : OperatorZornMatrix A}
    (hX : InSector .diagonal X) (hY : InSector .plus Y) :
    InSector .plus (operatorZornMul X Y) := by
  rcases hX with ⟨hxp, hxm⟩
  rcases hY with ⟨hyp, hym, hyminus⟩
  refine ⟨?_, ?_, ?_⟩
  · simpa [operatorZornMul, NCZornElement.mul, hxp, hxm, hyp, hym, hyminus]
  · simpa [operatorZornMul, NCZornElement.mul, hxp, hxm, hyp, hym, hyminus]
  · funext i
    fin_cases i <;>
      simp [operatorZornMul, NCZornElement.mul, hxp, hxm, hyp, hym, hyminus]

theorem plus_mul_diagonal
    {X Y : OperatorZornMatrix A}
    (hX : InSector .plus X) (hY : InSector .diagonal Y) :
    InSector .plus (operatorZornMul X Y) := by
  rcases hX with ⟨hxp, hxm, hxminus⟩
  rcases hY with ⟨hyp, hym⟩
  refine ⟨?_, ?_, ?_⟩
  · simpa [operatorZornMul, NCZornElement.mul, hxp, hxm, hxminus, hyp, hym]
  · simpa [operatorZornMul, NCZornElement.mul, hxp, hxm, hxminus, hyp, hym]
  · funext i
    fin_cases i <;>
      simp [operatorZornMul, NCZornElement.mul, hxp, hxm, hxminus, hyp, hym]

theorem diagonal_mul_minus
    {X Y : OperatorZornMatrix A}
    (hX : InSector .diagonal X) (hY : InSector .minus Y) :
    InSector .minus (operatorZornMul X Y) := by
  rcases hX with ⟨hxp, hxm⟩
  rcases hY with ⟨hyp, hym, hyplus⟩
  refine ⟨?_, ?_, ?_⟩
  · simpa [operatorZornMul, NCZornElement.mul, hxp, hxm, hyp, hym, hyplus]
  · simpa [operatorZornMul, NCZornElement.mul, hxp, hxm, hyp, hym, hyplus]
  · funext i
    fin_cases i <;>
      simp [operatorZornMul, NCZornElement.mul, hxp, hxm, hyp, hym, hyplus]

theorem minus_mul_diagonal
    {X Y : OperatorZornMatrix A}
    (hX : InSector .minus X) (hY : InSector .diagonal Y) :
    InSector .minus (operatorZornMul X Y) := by
  rcases hX with ⟨hxp, hxm, hxplus⟩
  rcases hY with ⟨hyp, hym⟩
  refine ⟨?_, ?_, ?_⟩
  · simpa [operatorZornMul, NCZornElement.mul, hxp, hxm, hxplus, hyp, hym]
  · simpa [operatorZornMul, NCZornElement.mul, hxp, hxm, hxplus, hyp, hym]
  · funext i
    fin_cases i <;>
      simp [operatorZornMul, NCZornElement.mul, hxp, hxm, hxplus, hyp, hym]

theorem plus_mul_plus
    {X Y : OperatorZornMatrix A}
    (hX : InSector .plus X) (hY : InSector .plus Y) :
    InSector .minus (operatorZornMul X Y) := by
  rcases hX with ⟨hxp, hxm, hxminus⟩
  rcases hY with ⟨hyp, hym, hyminus⟩
  refine ⟨?_, ?_, ?_⟩
  · simpa [operatorZornMul, NCZornElement.mul, hxp, hxm, hxminus, hyp, hym, hyminus]
  · simpa [operatorZornMul, NCZornElement.mul, hxp, hxm, hxminus, hyp, hym, hyminus]
  · funext i
    fin_cases i <;>
      simp [operatorZornMul, NCZornElement.mul, hxp, hxm, hxminus, hyp, hym, hyminus]

theorem minus_mul_minus
    {X Y : OperatorZornMatrix A}
    (hX : InSector .minus X) (hY : InSector .minus Y) :
    InSector .plus (operatorZornMul X Y) := by
  rcases hX with ⟨hxp, hxm, hxplus⟩
  rcases hY with ⟨hyp, hym, hyplus⟩
  refine ⟨?_, ?_, ?_⟩
  · simpa [operatorZornMul, NCZornElement.mul, hxp, hxm, hxplus, hyp, hym, hyplus]
  · simpa [operatorZornMul, NCZornElement.mul, hxp, hxm, hxplus, hyp, hym, hyplus]
  · ext i
    fin_cases i <;>
      simp [operatorZornMul, NCZornElement.mul, hxp, hxm, hxplus, hyp, hym, hyplus]

theorem plus_mul_minus
    {X Y : OperatorZornMatrix A}
    (hX : InSector .plus X) (hY : InSector .minus Y) :
    InSector .diagonal (operatorZornMul X Y) := by
  rcases hX with ⟨hxp, hxm, hxminus⟩
  rcases hY with ⟨hyp, hym, hyplus⟩
  constructor
  · ext i
    fin_cases i <;>
      simp [operatorZornMul, NCZornElement.mul, hxp, hxm, hxminus, hyp, hym, hyplus]
  · ext i
    fin_cases i <;>
      simp [operatorZornMul, NCZornElement.mul, hxp, hxm, hxminus, hyp, hym, hyplus]

theorem minus_mul_plus
    {X Y : OperatorZornMatrix A}
    (hX : InSector .minus X) (hY : InSector .plus Y) :
    InSector .diagonal (operatorZornMul X Y) := by
  rcases hX with ⟨hxp, hxm, hxplus⟩
  rcases hY with ⟨hyp, hym, hyminus⟩
  constructor
  · ext i
    fin_cases i <;>
      simp [operatorZornMul, NCZornElement.mul, hxp, hxm, hxplus, hyp, hym, hyminus]
  · ext i
    fin_cases i <;>
      simp [operatorZornMul, NCZornElement.mul, hxp, hxm, hxplus, hyp, hym, hyminus]

end InfoGeometry.Canonical
