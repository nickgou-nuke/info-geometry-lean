import InfoGeometry.Twistor.PerjesConventions
import InfoGeometry.Twistor.InfinityTwistor
import InfoGeometry.Twistor.SpinorOuterProduct

/-!
# The symmetric kinematic twistor, equations (6.1)-(6.6)

Slots are the existing upper and lower spinors, indexed by a disjoint sum.
The infinity bivector is a dual-to-vector map, not an inverse of the covariant
infinity form. All block readouts retain the spinor index-raising epsilon.
-/

noncomputable section
namespace InfoGeometry.Twistor.TwistorKinematicTensor

open InfoGeometry.Twistor.PenroseIncidence
open InfoGeometry.Twistor.PerjesConventions
open InfoGeometry.Twistor.InfinityTwistor
open scoped BigOperators Matrix

abbrev Slot := Fin 2 ⊕ Fin 2
abbrev KinematicMatrix := Matrix Slot Slot ℂ

def component (Z : Twistor4) : Slot → ℂ := Sum.elim Z.1 Z.2

/-- Spinor index raising with epsilon^(01)=1 and epsilon^(10)=-1. -/
def raiseSpinor (pi : Spinor2) : Spinor2 := ![pi 1, -pi 0]

@[simp] theorem raiseSpinor_twice (pi : Spinor2) :
    raiseSpinor (raiseSpinor pi) = -pi := by
  ext a
  fin_cases a <;> simp [raiseSpinor]

/-- Contravariant infinity bivector: upper alternating block, lower block zero. -/
def infinitySharp : Module.Dual ℂ Twistor4 →ₗ[ℂ] Twistor4 where
  toFun f := ((fun a => if a = 0 then f (![0, 1], 0) else -f (![1, 0], 0)), 0)
  map_add' f g := by ext a <;> fin_cases a <;> simp [add_comm]
  map_smul' c f := by ext a <;> fin_cases a <;> simp [smul_eq_mul]

/-- The two infinity tensors annihilate each other; they are not inverses. -/
theorem infinitySharp_covariant_zero (Z : Twistor4) :
    infinitySharp (infinityTwistor Z) = 0 := by
  ext a <;> fin_cases a <;> simp [infinitySharp, infinityTwistor]

/-- Antilinear square-zero map Z ↦ I^(alpha beta) conjugate(Z)_beta. -/
def infinityConjugate (Z : Twistor4) : Twistor4 :=
  (raiseSpinor (star Z.2), 0)

theorem infinityConjugate_eq_sharp_dual (Z : Twistor4) :
    infinityConjugate Z = infinitySharp (wittDual Z) := by
  ext a <;> fin_cases a <;>
    simp [infinityConjugate, raiseSpinor, infinitySharp, wittDual,
      wittPair, Fin.sum_univ_two]

@[simp] theorem infinityConjugate_sq (Z : Twistor4) :
    infinityConjugate (infinityConjugate Z) = 0 := by
  ext a <;> fin_cases a <;> simp [infinityConjugate, raiseSpinor]

@[simp] theorem infinityConjugate_add (Z W : Twistor4) :
    infinityConjugate (Z + W) = infinityConjugate Z + infinityConjugate W := by
  ext a <;> fin_cases a <;> simp [infinityConjugate, raiseSpinor, add_comm]

@[simp] theorem infinityConjugate_smul (c : ℂ) (Z : Twistor4) :
    infinityConjugate (c • Z) = star c • infinityConjugate Z := by
  ext a <;> fin_cases a <;> simp [infinityConjugate, raiseSpinor, smul_eq_mul]

@[simp] theorem component_add (Z W : Twistor4) (a : Slot) :
    component (Z + W) a = component Z a + component W a := by cases a <;> rfl

@[simp] theorem component_smul (c : ℂ) (Z : Twistor4) (a : Slot) :
    component (c • Z) a = c * component Z a := by cases a <;> rfl

@[simp] theorem component_zero (a : Slot) : component 0 a = 0 := by cases a <;> rfl

@[simp] theorem component_sum {ι : Type*} (s : Finset ι)
    (Z : ι → Twistor4) (a : Slot) :
    component (∑ i ∈ s, Z i) a = ∑ i ∈ s, component (Z i) a := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [hi, ih]

@[simp] theorem infinityConjugate_zero : infinityConjugate 0 = 0 := by
  ext a <;> fin_cases a <;> simp [infinityConjugate, raiseSpinor]

@[simp] theorem infinityConjugate_sum {ι : Type*} (s : Finset ι)
    (Z : ι → Twistor4) :
    infinityConjugate (∑ i ∈ s, Z i) = ∑ i ∈ s, infinityConjugate (Z i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [hi, ih]

/-- Symmetric bilinear tensor product, without the factor 1/2. -/
def symmetricOuter (Z W : Twistor4) : KinematicMatrix :=
  fun a b => component Z a * component W b + component W a * component Z b

/-- Equation (6.4). This is symmetric, not the antisymmetric Plucker bivector. -/
def kinematic (Z : Twistor4) : KinematicMatrix :=
  symmetricOuter Z (infinityConjugate Z)

theorem kinematic_symmetric (Z : Twistor4) : (kinematic Z)ᵀ = kinematic Z := by
  ext a b
  simp [kinematic, symmetricOuter, Matrix.transpose_apply]
  ring

theorem kinematic_smul (c : ℂ) (Z : Twistor4) :
    kinematic (c • Z) = (c * star c) • kinematic Z := by
  ext a b
  simp [kinematic, symmetricOuter, smul_eq_mul]
  ring

theorem kinematic_phase_invariant (c : ℂ) (hc : c * star c = 1) (Z : Twistor4) :
    kinematic (c • Z) = kinematic Z := by rw [kinematic_smul, hc, one_smul]

@[simp] theorem kinematic_neg (Z : Twistor4) : kinematic (-Z) = kinematic Z := by
  simpa using kinematic_phase_invariant (-1) (by norm_num) Z

/-- Hermitian lower-spinor momentum, before raising its first index. -/
def momentum (Z : Twistor4) : ComplexSpacetime :=
  Matrix.vecMulVec (star Z.2) Z.2

/-- The spinor part mu^(AB) in equation (6.2). -/
def angularSpinor (Z : Twistor4) : ComplexSpacetime :=
  fun a b => (Complex.I / 2) *
    (Z.1 a * raiseSpinor (star Z.2) b + raiseSpinor (star Z.2) a * Z.1 b)

@[simp] theorem kinematic_lower_lower (Z : Twistor4) (a b : Fin 2) :
    kinematic Z (.inr a) (.inr b) = 0 := by
  simp [kinematic, symmetricOuter, component, infinityConjugate]

@[simp] theorem kinematic_upper_lower (Z : Twistor4) (a b : Fin 2) :
    kinematic Z (.inl a) (.inr b) = raiseSpinor (star Z.2) a * Z.2 b := by
  simp [kinematic, symmetricOuter, component, infinityConjugate]

/-- The upper block is -2i times the angular-momentum spinor, as in (6.3). -/
theorem kinematic_upper_upper (Z : Twistor4) (a b : Fin 2) :
    kinematic Z (.inl a) (.inl b) = -2 * Complex.I * angularSpinor Z a b := by
  simp [kinematic, symmetricOuter, component, infinityConjugate, angularSpinor]
  ring_nf
  simp [Complex.I_sq]

theorem momentum_hermitian (Z : Twistor4) : (momentum Z)ᴴ = momentum Z := by
  ext a b
  simp [momentum, Matrix.vecMulVec, Matrix.conjTranspose_apply, mul_comm]

theorem momentum_null (Z : Twistor4) : (momentum Z).det = 0 := by
  simp [momentum, Matrix.vecMulVec, Matrix.det_fin_two]
  ring

/-- Nonzero tensor witness, ruling out a constant-zero implementation. -/
theorem kinematic_nonzero_witness :
    kinematic ((0 : Spinor2), ![1, 0]) (.inl 1) (.inr 0) = -1 := by
  simp [kinematic_upper_lower, raiseSpinor]

end InfoGeometry.Twistor.TwistorKinematicTensor
