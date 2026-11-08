import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.ThreeColorOperatorCrossCommutator

/-!
# Sage-order translation for operator-valued chiral Zorn coordinates

The symbols `i`, `j`, `k`, `ℓ`, `iℓ`, `jℓ`, `kℓ` are coordinate generators.
The symbols `σ₊` and `σ₋` are not single generators: each is a vector of
three operator coefficients.  This owner records the translation in the
noncommutative Zorn carrier without installing an associative multiplication
on that carrier.
-/

namespace InfoGeometry.Algebra

open InfoGeometry.Canonical
open InfoGeometry.Physics.NCG

variable {A : Type*} [Ring A]

abbrev OperatorSageCarrier (A : Type*) [Ring A] := OperatorZornMatrix A

/-! ### Native chiral-cone coordinates -/

/-- One chiral cone: a scalar operator and its three-component operator vector. -/
abbrev ChiralCone (A : Type*) [Ring A] := A × OperatorVector A

/-- The two-cone coordinate carrier `(u₊, s₊, u₋, s₋)`. -/
abbrev ChiralConeCoordinates (A : Type*) [Ring A] :=
  ChiralCone A × ChiralCone A

/-- Read an operator-valued Zorn element in chiral-cone coordinates. -/
def operatorSageToChiral
    (X : OperatorSageCarrier A) : ChiralConeCoordinates A :=
  ((X.n_plus, X.sigma_plus), (X.n_minus, X.sigma_minus))

/-- Reassemble an operator-valued Zorn element from chiral-cone coordinates. -/
def chiralToOperatorSage
    (X : ChiralConeCoordinates A) : OperatorSageCarrier A :=
  ⟨X.1.1, X.2.1, X.1.2, X.2.2⟩

@[simp] theorem chiralToOperatorSage_operatorSageToChiral
    (X : OperatorSageCarrier A) :
    chiralToOperatorSage (operatorSageToChiral X) = X := by
  cases X
  rfl

@[simp] theorem operatorSageToChiral_chiralToOperatorSage
    (X : ChiralConeCoordinates A) :
    operatorSageToChiral (chiralToOperatorSage X) = X := by
  rcases X with ⟨⟨uPlus, sPlus⟩, ⟨uMinus, sMinus⟩⟩
  rfl

/-- The coordinate unit in the three-component operator vector. -/
def operatorUnit (c : Fin 3) : OperatorVector A :=
  Pi.single c (1 : A)

@[simp] theorem operatorUnit_apply (c d : Fin 3) :
    operatorUnit c d = if c = d then (1 : A) else 0 := by
  by_cases h : c = d
  · subst d
    simp [operatorUnit]
  · simp [operatorUnit, h]

/-- Additive operations on the operator-valued Zorn coordinate carrier. -/
def operatorAdd (X Y : OperatorZornMatrix A) : OperatorZornMatrix A :=
  ⟨X.n_plus + Y.n_plus, X.n_minus + Y.n_minus,
    X.sigma_plus + Y.sigma_plus, X.sigma_minus + Y.sigma_minus⟩

def operatorSub (X Y : OperatorZornMatrix A) : OperatorZornMatrix A :=
  ⟨X.n_plus - Y.n_plus, X.n_minus - Y.n_minus,
    X.sigma_plus - Y.sigma_plus, X.sigma_minus - Y.sigma_minus⟩

def operatorOne : OperatorSageCarrier A :=
  operatorAdd (nPlus (1 : A)) (nMinus (1 : A))

def operatorEll : OperatorSageCarrier A :=
  operatorSub (nPlus (1 : A)) (nMinus (1 : A))

def operatorI : OperatorSageCarrier A :=
  operatorSub (sigmaMinus (operatorUnit 0)) (sigmaPlus (operatorUnit 0))

def operatorJ : OperatorSageCarrier A :=
  operatorSub (sigmaMinus (operatorUnit 1)) (sigmaPlus (operatorUnit 1))

def operatorK : OperatorSageCarrier A :=
  operatorSub (sigmaMinus (operatorUnit 2)) (sigmaPlus (operatorUnit 2))

def operatorIEll : OperatorSageCarrier A :=
  operatorAdd (sigmaPlus (operatorUnit 0)) (sigmaMinus (operatorUnit 0))

def operatorJEll : OperatorSageCarrier A :=
  operatorAdd (sigmaPlus (operatorUnit 1)) (sigmaMinus (operatorUnit 1))

def operatorKEll : OperatorSageCarrier A :=
  operatorAdd (sigmaPlus (operatorUnit 2)) (sigmaMinus (operatorUnit 2))

/-- The SageMath order `{1, i, j, k, ℓ, iℓ, jℓ, kℓ}`. -/
def operatorSageGenerator : Fin 8 → OperatorSageCarrier A
  | 0 => operatorOne
  | 1 => operatorI
  | 2 => operatorJ
  | 3 => operatorK
  | 4 => operatorEll
  | 5 => operatorIEll
  | 6 => operatorJEll
  | 7 => operatorKEll

@[simp] theorem operatorSageGenerator_zero :
    operatorSageGenerator (A := A) 0 = operatorOne (A := A) := rfl

@[simp] theorem operatorSageGenerator_one :
    operatorSageGenerator (A := A) 1 = operatorI (A := A) := rfl

@[simp] theorem operatorSageGenerator_two :
    operatorSageGenerator (A := A) 2 = operatorJ (A := A) := rfl

@[simp] theorem operatorSageGenerator_three :
    operatorSageGenerator (A := A) 3 = operatorK (A := A) := rfl

@[simp] theorem operatorSageGenerator_four :
    operatorSageGenerator (A := A) 4 = operatorEll (A := A) := rfl

@[simp] theorem operatorSageGenerator_five :
    operatorSageGenerator (A := A) 5 = operatorIEll (A := A) := rfl

@[simp] theorem operatorSageGenerator_six :
    operatorSageGenerator (A := A) 6 = operatorJEll (A := A) := rfl

@[simp] theorem operatorSageGenerator_seven :
    operatorSageGenerator (A := A) 7 = operatorKEll (A := A) := rfl

@[simp] theorem operatorOne_components :
    (operatorOne : OperatorSageCarrier A) =
      ⟨1, 1, fun _ => 0, fun _ => 0⟩ := by
  ext <;> simp [operatorOne, operatorAdd, nPlus, nMinus]

@[simp] theorem operatorEll_components :
    (operatorEll : OperatorSageCarrier A) =
      ⟨1, -1, fun _ => 0, fun _ => 0⟩ := by
  ext <;> simp [operatorEll, operatorSub, nPlus, nMinus]

theorem operatorSageGenerator_table :
    operatorSageGenerator (A := A) 0 = operatorAdd (nPlus (1 : A)) (nMinus (1 : A)) ∧
    operatorSageGenerator (A := A) 1 =
      operatorSub (sigmaMinus (operatorUnit (A := A) 0))
        (sigmaPlus (operatorUnit (A := A) 0)) ∧
    operatorSageGenerator (A := A) 2 =
      operatorSub (sigmaMinus (operatorUnit (A := A) 1))
        (sigmaPlus (operatorUnit (A := A) 1)) ∧
    operatorSageGenerator (A := A) 3 =
      operatorSub (sigmaMinus (operatorUnit (A := A) 2))
        (sigmaPlus (operatorUnit (A := A) 2)) ∧
    operatorSageGenerator (A := A) 4 = operatorSub (nPlus (1 : A)) (nMinus (1 : A)) ∧
    operatorSageGenerator (A := A) 5 =
      operatorAdd (sigmaPlus (operatorUnit (A := A) 0))
        (sigmaMinus (operatorUnit (A := A) 0)) ∧
    operatorSageGenerator (A := A) 6 =
      operatorAdd (sigmaPlus (operatorUnit (A := A) 1))
        (sigmaMinus (operatorUnit (A := A) 1)) ∧
    operatorSageGenerator (A := A) 7 =
      operatorAdd (sigmaPlus (operatorUnit (A := A) 2))
        (sigmaMinus (operatorUnit (A := A) 2)) := by
  simp [operatorSageGenerator, operatorOne, operatorI, operatorJ, operatorK,
    operatorEll, operatorIEll, operatorJEll, operatorKEll]

end InfoGeometry.Algebra
