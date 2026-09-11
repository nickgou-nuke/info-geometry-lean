import InfoGeometry.Canonical.ThreeColorOperatorCrossCommutator
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Ordered products and their independent readout channels

The symmetric epsilon-commutator channel does not replace the native Zorn
cross product. The literal source product is defined only for a counterexample.
-/

noncomputable section
namespace InfoGeometry.Canonical.OperatorZornOrderedChannels

open InfoGeometry.Physics.NCG
open scoped BigOperators

variable {A : Type*} [Ring A]

def commutatorCrossTwice (U V : OperatorVector A) : OperatorVector A :=
  fun i => ∑ j : Fin 3, ∑ k : Fin 3,
    (epsilon3 i j k : A) * (U j * V k - V k * U j)

theorem commutatorCrossTwice_eq (U V : OperatorVector A) :
    commutatorCrossTwice U V = operatorCross U V + operatorCross V U := by
  funext i
  fin_cases i <;>
    simp [commutatorCrossTwice, epsilon3, operatorCross, NCZornElement.zornCross,
      Fin.sum_univ_succ] <;> noncomm_ring

theorem commutatorCrossTwice_symmetric (U V : OperatorVector A) :
    commutatorCrossTwice V U = commutatorCrossTwice U V := by
  rw [commutatorCrossTwice_eq, commutatorCrossTwice_eq, add_comm]

theorem orderedDot_commutator_residue (U V : OperatorVector A) :
    operatorDot U V - operatorDot V U = ∑ i : Fin 3, (U i * V i - V i * U i) := by
  simp [operatorDot, NCZornElement.zornDot, Fin.sum_univ_succ]
  noncomm_ring

section RealCoefficients
variable [Algebra ℝ A]

def symmetricDot (U V : OperatorVector A) : A :=
  (1/2 : ℝ) • (operatorDot U V + operatorDot V U)

def commutatorDot (U V : OperatorVector A) : A :=
  (1/2 : ℝ) • (operatorDot U V - operatorDot V U)

theorem orderedDot_reconstruction (U V : OperatorVector A) :
    operatorDot U V = symmetricDot U V + commutatorDot U V := by
  unfold symmetricDot commutatorDot
  module

def commutatorCross (U V : OperatorVector A) : OperatorVector A :=
  (1/2 : ℝ) • commutatorCrossTwice U V

def exteriorCross (U V : OperatorVector A) : OperatorVector A :=
  (1/2 : ℝ) • (operatorCross U V - operatorCross V U)

theorem orderedCross_reconstruction (U V : OperatorVector A) :
    operatorCross U V = exteriorCross U V + commutatorCross U V := by
  rw [exteriorCross, commutatorCross, commutatorCrossTwice_eq]
  module

@[simp] theorem commutatorCross_self (U : OperatorVector A) :
    commutatorCross U U = operatorCross U U := by
  rw [commutatorCross, commutatorCrossTwice_eq]
  module

theorem exteriorCross_antisymmetric (U V : OperatorVector A) :
    exteriorCross V U = -exteriorCross U V := by
  unfold exteriorCross
  module

end RealCoefficients

section Commutative
variable {R : Type*} [CommRing R]

theorem commutatorCrossTwice_commutative (U V : OperatorVector R) :
    commutatorCrossTwice U V = 0 := by
  funext i
  unfold commutatorCrossTwice
  simp [mul_comm]

theorem native_cross_axes :
    operatorCross (![1,0,0] : OperatorVector R) ![0,1,0] = ![0,0,1] := by
  funext i
  fin_cases i <;> simp [operatorCross, NCZornElement.zornCross]

theorem native_cross_axes_ne_zero [Nontrivial R] :
    operatorCross (![1,0,0] : OperatorVector R) ![0,1,0] ≠ 0 := by
  rw [native_cross_axes]
  intro h
  have h2 := congrFun h 2
  have hne : (1 : R) ≠ 0 := one_ne_zero
  exact hne (by simpa using h2)

end Commutative

/-- Diagnostic only: this is never installed as the carrier multiplication. -/
def sourceProduct (X Y : OperatorZornMatrix ℝ) : OperatorZornMatrix ℝ :=
  operatorZornCoordinates
    (X.n_plus * Y.n_plus + symmetricDot X.sigma_plus Y.sigma_minus)
    (X.n_minus * Y.n_minus + symmetricDot X.sigma_minus Y.sigma_plus)
    (fun i => X.n_plus*Y.sigma_plus i + X.sigma_plus i*Y.n_minus -
      commutatorCross X.sigma_minus Y.sigma_minus i)
    (fun i => X.sigma_minus i*Y.n_plus + X.n_minus*Y.sigma_minus i +
      commutatorCross X.sigma_plus Y.sigma_plus i)

def sourceWitness : OperatorZornMatrix ℝ := operatorZornCoordinates 0 0 ![1,0,0] ![1,0,0]
def sourceProbe : OperatorZornMatrix ℝ := sigmaPlus ![0,1,0]

theorem sourceProduct_not_left_alternative :
    sourceProduct (sourceProduct sourceWitness sourceWitness) sourceProbe ≠
      sourceProduct sourceWitness (sourceProduct sourceWitness sourceProbe) := by
  intro h
  have hc := congrArg (fun X : OperatorZornMatrix ℝ => X.sigma_plus 1) h
  norm_num [sourceProduct, sourceWitness, sourceProbe, sigmaPlus,
    operatorZornCoordinates, symmetricDot, operatorDot, NCZornElement.zornDot,
    commutatorCross, commutatorCrossTwice, epsilon3, Fin.sum_univ_succ] at hc
  simp at hc

end InfoGeometry.Canonical.OperatorZornOrderedChannels
