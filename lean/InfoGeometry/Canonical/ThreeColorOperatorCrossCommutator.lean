import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Physics.NCG.NoncommutativeChiralZornAlgebra

/-!
# Operator-valued three-colour cross products

The coefficient ring is allowed to be noncommutative.  Consequently the
cross product is not declared antisymmetric: its self-cross records
coefficient commutators.  This owner contains only the finite coordinate
calculus and the resulting off-diagonal multiplication identities.
-/

namespace InfoGeometry.Canonical

open InfoGeometry.Physics.NCG

variable {A : Type*} [Ring A]

abbrev OperatorVector (A : Type*) [Ring A] := Fin 3 → A

abbrev operatorDot (U V : OperatorVector A) : A :=
  NCZornElement.zornDot U V

abbrev operatorCross (U V : OperatorVector A) : OperatorVector A :=
  NCZornElement.zornCross U V

/-! ### Operator-valued bivectors and their three-dimensional readout -/

/-- The ordered operator-valued alternating two-tensor. -/
def operatorWedge2 (U V : OperatorVector A) : Fin 3 → Fin 3 → A :=
  fun j k => U j * V k - U k * V j

theorem operatorWedge2_swap_indices
    (U V : OperatorVector A) (j k : Fin 3) :
    operatorWedge2 U V k j = -operatorWedge2 U V j k := by
  simp [operatorWedge2, sub_eq_add_neg, add_comm]

/-- The oriented three-dimensional Hodge readout of a bivector.

For an alternating two-tensor this is the component form of
`(1/2) εᵢⱼₖ Bⱼₖ`, written without division so it works over every ring. -/
def operatorHodgeDual2 (B : Fin 3 → Fin 3 → A) : OperatorVector A :=
  fun i => match i with
  | 0 => B 1 2
  | 1 => B 2 0
  | 2 => B 0 1

theorem operatorHodgeDual2_wedge_eq_operatorCross
    (U V : OperatorVector A) :
    operatorHodgeDual2 (operatorWedge2 U V) = operatorCross U V := by
  funext i
  fin_cases i <;> rfl

/-! ### Explicit integer Levi--Civita readout

The sign tensor is integer-valued, so the adapter remains valid over every
coefficient ring.  Its cast into `A` is the only scalar action used below. -/

def epsilon3 (i j k : Fin 3) : ℤ :=
  if i = 0 ∧ j = 1 ∧ k = 2 then 1 else
  if i = 0 ∧ j = 2 ∧ k = 1 then -1 else
  if i = 1 ∧ j = 2 ∧ k = 0 then 1 else
  if i = 1 ∧ j = 0 ∧ k = 2 then -1 else
  if i = 2 ∧ j = 0 ∧ k = 1 then 1 else
  if i = 2 ∧ j = 1 ∧ k = 0 then -1 else 0

def leviCivitaOperatorCross (U V : OperatorVector A) : OperatorVector A :=
  fun i => ∑ j : Fin 3, ∑ k : Fin 3,
    (epsilon3 i j k : A) * (U j * V k)

theorem leviCivitaOperatorCross_eq_operatorCross
    (U V : OperatorVector A) :
    leviCivitaOperatorCross U V = operatorCross U V := by
  funext i
  fin_cases i <;>
    simp [leviCivitaOperatorCross, epsilon3, operatorCross,
      NCZornElement.zornCross, Fin.sum_univ_succ, sub_eq_add_neg, add_comm]

theorem leviCivitaOperatorCross_eq_hodgeDual2_wedge
    (U V : OperatorVector A) :
    leviCivitaOperatorCross U V =
      operatorHodgeDual2 (operatorWedge2 U V) := by
  rw [leviCivitaOperatorCross_eq_operatorCross,
    operatorHodgeDual2_wedge_eq_operatorCross]

def operatorBivectorChannel (U V : OperatorVector A) :
    Fin 3 → Fin 3 → A :=
  operatorWedge2 U V - operatorWedge2 V U

theorem operatorBivectorChannel_swap
    (U V : OperatorVector A) :
    operatorBivectorChannel V U = -operatorBivectorChannel U V := by
  funext j k
  simp [operatorBivectorChannel, sub_eq_add_neg, add_comm, add_left_comm,
    add_assoc]

theorem operatorHodgeDual2_bivectorChannel_eq_cross_difference
    (U V : OperatorVector A) :
    operatorHodgeDual2 (operatorBivectorChannel U V) =
      operatorCross U V - operatorCross V U := by
  funext i
  fin_cases i <;> rfl

@[simp] theorem operatorCross_self_red (U : OperatorVector A) :
    operatorCross U U 0 = U 1 * U 2 - U 2 * U 1 := rfl

@[simp] theorem operatorCross_self_green (U : OperatorVector A) :
    operatorCross U U 1 = U 2 * U 0 - U 0 * U 2 := rfl

@[simp] theorem operatorCross_self_blue (U : OperatorVector A) :
    operatorCross U U 2 = U 0 * U 1 - U 1 * U 0 := rfl

theorem operatorCross_self_eq_commutators (U : OperatorVector A) :
    operatorCross U U =
      fun c => match c with
      | 0 => U 1 * U 2 - U 2 * U 1
      | 1 => U 2 * U 0 - U 0 * U 2
      | 2 => U 0 * U 1 - U 1 * U 0 := by
  funext c
  fin_cases c <;> rfl

theorem operatorCross_self_eq_zero_iff (U : OperatorVector A) :
    operatorCross U U = 0 ↔
      U 1 * U 2 = U 2 * U 1 ∧
      U 2 * U 0 = U 0 * U 2 ∧
      U 0 * U 1 = U 1 * U 0 := by
  constructor
  · intro h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    have h2 := congrFun h 2
    simp only [operatorCross_self_red, operatorCross_self_green,
      operatorCross_self_blue, Pi.zero_apply, sub_eq_zero] at h0 h1 h2
    exact ⟨h0, h1, h2⟩
  · rintro ⟨h0, h1, h2⟩
    funext c
    fin_cases c
    · exact sub_eq_zero.mpr h0
    · exact sub_eq_zero.mpr h1
    · exact sub_eq_zero.mpr h2

theorem operatorCross_swap_defect (U V : OperatorVector A) :
    (operatorCross U V + operatorCross V U) 0 =
        (U 1 * V 2 - U 2 * V 1) + (V 1 * U 2 - V 2 * U 1) ∧
    (operatorCross U V + operatorCross V U) 1 =
        (U 2 * V 0 - U 0 * V 2) + (V 2 * U 0 - V 0 * U 2) ∧
    (operatorCross U V + operatorCross V U) 2 =
        (U 0 * V 1 - U 1 * V 0) + (V 0 * U 1 - V 1 * U 0) := by
  simp [operatorCross, NCZornElement.zornCross, sub_eq_add_neg,
    add_assoc, add_left_comm, add_comm]

abbrev OperatorZornMatrix (A : Type*) [Ring A] := NCZornElement A

instance : Zero (OperatorZornMatrix A) :=
  ⟨⟨0, 0, fun _ => 0, fun _ => 0⟩⟩

abbrev operatorZornMul (X Y : OperatorZornMatrix A) : OperatorZornMatrix A :=
  NCZornElement.mul X Y

def nPlus (a : A) : OperatorZornMatrix A :=
  ⟨a, 0, fun _ => 0, fun _ => 0⟩

def nMinus (a : A) : OperatorZornMatrix A :=
  ⟨0, a, fun _ => 0, fun _ => 0⟩

def sigmaPlus (U : OperatorVector A) : OperatorZornMatrix A :=
  ⟨0, 0, U, fun _ => 0⟩

def sigmaMinus (U : OperatorVector A) : OperatorZornMatrix A :=
  ⟨0, 0, fun _ => 0, U⟩

@[ext] theorem operatorZornMatrix_ext {X Y : OperatorZornMatrix A}
    (hnp : X.n_plus = Y.n_plus)
    (hnm : X.n_minus = Y.n_minus)
    (hsp : X.sigma_plus = Y.sigma_plus)
    (hsm : X.sigma_minus = Y.sigma_minus) :
    X = Y := by
  cases X
  cases Y
  simp_all

/-! ### Two-sheet operator coordinates

`operatorZornCoordinates` is only the native four-field presentation of the
existing `NCZornElement`; it does not introduce a second carrier or a second
multiplication. -/

def operatorZornCoordinates (a b : A) (u v : OperatorVector A) :
    OperatorZornMatrix A :=
  ⟨a, b, u, v⟩

@[simp] theorem operatorZornCoordinates_nPlus (a b : A)
    (u v : OperatorVector A) :
    (operatorZornCoordinates a b u v).n_plus = a := rfl

@[simp] theorem operatorZornCoordinates_nMinus (a b : A)
    (u v : OperatorVector A) :
    (operatorZornCoordinates a b u v).n_minus = b := rfl

@[simp] theorem operatorZornCoordinates_sigmaPlus (a b : A)
    (u v : OperatorVector A) :
    (operatorZornCoordinates a b u v).sigma_plus = u := rfl

@[simp] theorem operatorZornCoordinates_sigmaMinus (a b : A)
    (u v : OperatorVector A) :
    (operatorZornCoordinates a b u v).sigma_minus = v := rfl

theorem operatorZornMul_coordinates
    (a b c d : A) (u v x y : OperatorVector A) :
    operatorZornMul (operatorZornCoordinates a b u v)
      (operatorZornCoordinates c d x y) =
      operatorZornCoordinates
        (a * c + operatorDot u y)
        (b * d + operatorDot v x)
      (fun i => a * x i + u i * d - operatorCross v y i)
        (fun i => v i * c + b * y i + operatorCross u x i) := by
  apply operatorZornMatrix_ext
  · simp [operatorZornMul, operatorZornCoordinates, NCZornElement.mul,
      operatorDot, NCZornElement.zornDot]
  · simp [operatorZornMul, operatorZornCoordinates, NCZornElement.mul,
      operatorDot, NCZornElement.zornDot]
  · funext i
    simp [operatorZornMul, operatorZornCoordinates, NCZornElement.mul,
      operatorCross, NCZornElement.zornCross, add_comm]
  · funext i
    simp [operatorZornMul, operatorZornCoordinates, NCZornElement.mul,
      operatorCross, NCZornElement.zornCross, add_comm]

def chiralOperatorZorn (u v : OperatorVector A) : OperatorZornMatrix A :=
  operatorZornCoordinates 0 0 u v

theorem operatorZornMul_chiralOperatorZorn
    (u v : OperatorVector A) :
    operatorZornMul (chiralOperatorZorn u v) (chiralOperatorZorn u v) =
      operatorZornCoordinates
        (operatorDot u v)
        (operatorDot v u)
        (-operatorCross v v)
        (operatorCross u u) := by
  apply operatorZornMatrix_ext
  · simp [chiralOperatorZorn, operatorZornCoordinates,
      operatorZornMul, NCZornElement.mul, operatorDot,
      NCZornElement.zornDot]
  · simp [chiralOperatorZorn, operatorZornCoordinates,
      operatorZornMul, NCZornElement.mul, operatorDot,
      NCZornElement.zornDot]
  · funext i
    simp [chiralOperatorZorn, operatorZornCoordinates,
      operatorZornMul, NCZornElement.mul, operatorCross,
      NCZornElement.zornCross]
  · funext i
    simp [chiralOperatorZorn, operatorZornCoordinates,
      operatorZornMul, NCZornElement.mul, operatorCross,
      NCZornElement.zornCross]

theorem operatorZornMul_chiralOperatorZorn_hodge
    (u v : OperatorVector A) :
    operatorZornMul (chiralOperatorZorn u v) (chiralOperatorZorn u v) =
      operatorZornCoordinates
        (operatorDot u v)
        (operatorDot v u)
      (-(operatorHodgeDual2 (operatorWedge2 v v)))
        (operatorHodgeDual2 (operatorWedge2 u u)) := by
  rw [operatorZornMul_chiralOperatorZorn]
  rw [operatorHodgeDual2_wedge_eq_operatorCross,
    operatorHodgeDual2_wedge_eq_operatorCross]

@[simp] theorem nPlus_mul_nPlus (a b : A) :
    operatorZornMul (nPlus a) (nPlus b) = nPlus (a * b) := by
  apply operatorZornMatrix_ext <;>
    simp [operatorZornMul, nPlus, NCZornElement.mul,
      NCZornElement.zornDot]

@[simp] theorem nMinus_mul_nMinus (a b : A) :
    operatorZornMul (nMinus a) (nMinus b) = nMinus (a * b) := by
  apply operatorZornMatrix_ext <;>
    simp [operatorZornMul, nMinus, NCZornElement.mul,
      NCZornElement.zornDot]

theorem nPlus_idempotent_iff (a : A) :
    operatorZornMul (nPlus a) (nPlus a) = nPlus a ↔ a * a = a := by
  constructor
  · intro h
    simpa [operatorZornMul, nPlus, NCZornElement.mul,
      NCZornElement.zornDot] using congrArg NCZornElement.n_plus h
  · intro h
    apply operatorZornMatrix_ext <;>
      simp [operatorZornMul, nPlus, NCZornElement.mul,
        NCZornElement.zornDot, h]

theorem nMinus_idempotent_iff (a : A) :
    operatorZornMul (nMinus a) (nMinus a) = nMinus a ↔ a * a = a := by
  constructor
  · intro h
    simpa [operatorZornMul, nMinus, NCZornElement.mul,
      NCZornElement.zornDot] using congrArg NCZornElement.n_minus h
  · intro h
    apply operatorZornMatrix_ext <;>
      simp [operatorZornMul, nMinus, NCZornElement.mul,
        NCZornElement.zornDot, h]

@[simp] theorem sigmaPlus_mul_sigmaPlus (U V : OperatorVector A) :
    operatorZornMul (sigmaPlus U) (sigmaPlus V) =
      sigmaMinus (operatorCross U V) := by
  apply operatorZornMatrix_ext
  · simp [operatorZornMul, sigmaPlus, sigmaMinus, NCZornElement.mul,
      NCZornElement.zornDot]
  · simp [operatorZornMul, sigmaPlus, sigmaMinus, NCZornElement.mul,
      NCZornElement.zornDot]
  · funext c
    fin_cases c <;>
      simp [operatorZornMul, sigmaPlus, sigmaMinus, NCZornElement.mul,
        NCZornElement.zornDot, operatorCross, NCZornElement.zornCross]
  · funext c
    simp [operatorZornMul, sigmaPlus, sigmaMinus, NCZornElement.mul,
      NCZornElement.zornDot]

@[simp] theorem sigmaMinus_mul_sigmaMinus (U V : OperatorVector A) :
    operatorZornMul (sigmaMinus U) (sigmaMinus V) =
      sigmaPlus (-operatorCross U V) := by
  apply operatorZornMatrix_ext
  · simp [operatorZornMul, sigmaPlus, sigmaMinus, NCZornElement.mul,
      NCZornElement.zornDot]
  · simp [operatorZornMul, sigmaPlus, sigmaMinus, NCZornElement.mul,
      NCZornElement.zornDot]
  · funext c
    simp [operatorZornMul, sigmaPlus, sigmaMinus, NCZornElement.mul,
      NCZornElement.zornDot, operatorCross, NCZornElement.zornCross]
  · funext c
    fin_cases c <;>
      simp [operatorZornMul, sigmaPlus, sigmaMinus, NCZornElement.mul,
        NCZornElement.zornDot]

@[simp] theorem sigmaPlus_mul_sigmaMinus (U V : OperatorVector A) :
    operatorZornMul (sigmaPlus U) (sigmaMinus V) = nPlus (operatorDot U V) := by
  apply operatorZornMatrix_ext
  · simp [operatorZornMul, sigmaPlus, sigmaMinus, NCZornElement.mul,
      NCZornElement.zornDot, operatorDot, nPlus]
  · simp [operatorZornMul, sigmaPlus, sigmaMinus, NCZornElement.mul,
      NCZornElement.zornDot, operatorDot, nPlus]
  · funext c
    fin_cases c <;>
      simp [operatorZornMul, sigmaPlus, sigmaMinus, NCZornElement.mul,
        NCZornElement.zornDot, operatorDot, nPlus, NCZornElement.zornCross]
  · funext c
    fin_cases c <;>
      simp [operatorZornMul, sigmaPlus, sigmaMinus, NCZornElement.mul,
        NCZornElement.zornDot, operatorDot, nPlus, NCZornElement.zornCross]

@[simp] theorem sigmaMinus_mul_sigmaPlus (U V : OperatorVector A) :
    operatorZornMul (sigmaMinus U) (sigmaPlus V) = nMinus (operatorDot U V) := by
  apply operatorZornMatrix_ext
  · simp [operatorZornMul, sigmaPlus, sigmaMinus, NCZornElement.mul,
      NCZornElement.zornDot, operatorDot, nMinus]
  · simp [operatorZornMul, sigmaPlus, sigmaMinus, NCZornElement.mul,
      NCZornElement.zornDot, operatorDot, nMinus]
  · funext c
    fin_cases c <;>
      simp [operatorZornMul, sigmaPlus, sigmaMinus, NCZornElement.mul,
        NCZornElement.zornDot, operatorDot, nMinus, NCZornElement.zornCross]
  · funext c
    fin_cases c <;>
      simp [operatorZornMul, sigmaPlus, sigmaMinus, NCZornElement.mul,
        NCZornElement.zornDot, operatorDot, nMinus, NCZornElement.zornCross]

theorem sigmaPlus_sq (U : OperatorVector A) :
    operatorZornMul (sigmaPlus U) (sigmaPlus U) =
      sigmaMinus (operatorCross U U) :=
  sigmaPlus_mul_sigmaPlus U U

theorem sigmaPlus_sq_eq_zero_of_pairwise_commute
    (U : OperatorVector A)
    (h : U 1 * U 2 = U 2 * U 1 ∧
      U 2 * U 0 = U 0 * U 2 ∧
      U 0 * U 1 = U 1 * U 0) :
    operatorZornMul (sigmaPlus U) (sigmaPlus U) =
      (0 : OperatorZornMatrix A) := by
  rw [sigmaPlus_sq, operatorCross_self_eq_zero_iff U |>.2 h]
  rfl

end InfoGeometry.Canonical
