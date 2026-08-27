import InfoGeometry.Exceptional.Freudenthal
import Mathlib

/-!
# Linear structure on the Freudenthal charge carrier

The existing `FreudenthalCharge` structure is the coordinate carrier
`ℝ × ℝ × J × J`.  This owner supplies the pointwise additive and real-module
structure needed by later finite symplectic constructions.  It does not name
or construct an exceptional Lie algebra.
-/

noncomputable section

namespace InfoGeometry.Exceptional.Freudenthal

variable {J : Type*} [AddCommGroup J] [Module ℝ J]

def coordinateEquiv :
    FreudenthalCharge J ≃ (ℝ × ℝ × J × J) where
  toFun Q := (Q.alpha, Q.beta, Q.x, Q.y)
  invFun t :=
    { alpha := t.1
      beta := t.2.1
      x := t.2.2.1
      y := t.2.2.2 }
  left_inv Q := by cases Q; rfl
  right_inv t := by rcases t with ⟨a, b, x, y⟩; rfl

noncomputable instance : AddCommGroup (FreudenthalCharge J) :=
  Equiv.addCommGroup coordinateEquiv

noncomputable instance : Module ℝ (FreudenthalCharge J) :=
  Equiv.module ℝ coordinateEquiv

def heisenbergCoordinateEquiv :
    HeisenbergElement J ≃ (FreudenthalCharge J × ℝ) where
  toFun X := (X.charge, X.center)
  invFun p := { charge := p.1, center := p.2 }
  left_inv X := by cases X; rfl
  right_inv p := by rcases p with ⟨Q, r⟩; rfl

noncomputable instance : AddCommGroup (HeisenbergElement J) :=
  Equiv.addCommGroup heisenbergCoordinateEquiv

noncomputable instance : Module ℝ (HeisenbergElement J) :=
  Equiv.module ℝ heisenbergCoordinateEquiv

@[simp] theorem heisenbergCoordinateEquiv_apply (X : HeisenbergElement J) :
    heisenbergCoordinateEquiv X = (X.charge, X.center) := rfl

@[simp] theorem heisenberg_charge_add
    (X Y : HeisenbergElement J) :
    (X + Y).charge = X.charge + Y.charge := rfl

@[simp] theorem heisenberg_center_add
    (X Y : HeisenbergElement J) :
    (X + Y).center = X.center + Y.center := rfl

@[simp] theorem coordinateEquiv_apply (Q : FreudenthalCharge J) :
    coordinateEquiv Q = (Q.alpha, Q.beta, Q.x, Q.y) := rfl

@[simp] theorem coordinateEquiv_symm_apply
    (a b : ℝ) (x y : J) :
    coordinateEquiv.symm (a, b, x, y) =
      { alpha := a, beta := b, x := x, y := y } := rfl

@[simp] theorem alpha_add (Q R : FreudenthalCharge J) :
    (Q + R).alpha = Q.alpha + R.alpha := rfl

@[simp] theorem beta_add (Q R : FreudenthalCharge J) :
    (Q + R).beta = Q.beta + R.beta := rfl

@[simp] theorem x_add (Q R : FreudenthalCharge J) :
    (Q + R).x = Q.x + R.x := rfl

@[simp] theorem y_add (Q R : FreudenthalCharge J) :
    (Q + R).y = Q.y + R.y := rfl

@[simp] theorem alpha_smul (r : ℝ) (Q : FreudenthalCharge J) :
    (r • Q).alpha = r * Q.alpha := rfl

@[simp] theorem beta_smul (r : ℝ) (Q : FreudenthalCharge J) :
    (r • Q).beta = r * Q.beta := rfl

@[simp] theorem x_smul (r : ℝ) (Q : FreudenthalCharge J) :
    (r • Q).x = r • Q.x := rfl

@[simp] theorem y_smul (r : ℝ) (Q : FreudenthalCharge J) :
    (r • Q).y = r • Q.y := rfl

def symplecticFormLinear (D : CubicJordanDatum J) (Q : FreudenthalCharge J) :
    FreudenthalCharge J →ₗ[ℝ] ℝ where
  toFun P := FreudenthalCharge.symplecticForm D Q P
  map_add' P R := by
    simp only [FreudenthalCharge.symplecticForm, beta_add, alpha_add,
      x_add, y_add, map_add, mul_add]
    ring
  map_smul' r P := by
    simp only [FreudenthalCharge.symplecticForm, beta_smul, alpha_smul,
      x_smul, y_smul, map_smul, smul_eq_mul,
      RingHom.id_apply]
    ring

theorem symplecticForm_smul_left
    (D : CubicJordanDatum J) (r : ℝ)
    (P Q : FreudenthalCharge J) :
    FreudenthalCharge.symplecticForm D (r • P) Q =
      r * FreudenthalCharge.symplecticForm D P Q := by
  simp only [FreudenthalCharge.symplecticForm, alpha_smul, beta_smul,
    x_smul, y_smul, map_smul, LinearMap.smul_apply, smul_eq_mul]
  ring

/-! The symplectic form is nondegenerate once the stored trace pairing is.

This is the exact hypothesis available at the present abstract datum level;
no nondegeneracy of the cubic norm or of the quadratic adjoint is needed. -/
theorem symplecticForm_nondegenerate_of_traceBilin_nondegenerate
    (D : CubicJordanDatum J)
    (htrace : ∀ x : J, (∀ y : J, D.traceBilin x y = 0) → x = 0) :
    ∀ Q : FreudenthalCharge J,
      (∀ P : FreudenthalCharge J,
        FreudenthalCharge.symplecticForm D Q P = 0) → Q = 0 := by
  intro Q hQ
  have hβ : Q.beta = 0 := by
    have h := hQ {alpha := 1, beta := 0, x := 0, y := 0}
    simpa [FreudenthalCharge.symplecticForm] using h
  have hα : Q.alpha = 0 := by
    have h := hQ {alpha := 0, beta := 1, x := 0, y := 0}
    simpa [FreudenthalCharge.symplecticForm] using h
  have hx : Q.x = 0 := by
    apply htrace Q.x
    intro y
    have h := hQ {alpha := 0, beta := 0, x := 0, y := y}
    simpa [FreudenthalCharge.symplecticForm] using h
  have hy : Q.y = 0 := by
    apply htrace Q.y
    intro x
    have h := hQ {alpha := 0, beta := 0, x := x, y := 0}
    have h' : D.traceBilin Q.y x = 0 := by
      simpa [FreudenthalCharge.symplecticForm] using h
    simpa [D.trace_comm] using h'
  apply FreudenthalCharge.ext
  · exact hα
  · exact hβ
  · exact hx
  · exact hy

@[simp] theorem symplecticForm_add_right
    (D : CubicJordanDatum J) (P Q R : FreudenthalCharge J) :
    FreudenthalCharge.symplecticForm D P (Q + R) =
      FreudenthalCharge.symplecticForm D P Q +
        FreudenthalCharge.symplecticForm D P R := by
  exact (symplecticFormLinear D P).map_add Q R

@[simp] theorem symplecticForm_smul_right
    (D : CubicJordanDatum J) (r : ℝ)
    (P Q : FreudenthalCharge J) :
    FreudenthalCharge.symplecticForm D P (r • Q) =
      r * FreudenthalCharge.symplecticForm D P Q := by
  exact (symplecticFormLinear D P).map_smul r Q

theorem symplecticForm_neg_right
    (D : CubicJordanDatum J) (P Q : FreudenthalCharge J) :
    FreudenthalCharge.symplecticForm D P (-Q) =
      - FreudenthalCharge.symplecticForm D P Q := by
  exact (symplecticFormLinear D P).map_neg Q

theorem symplecticForm_neg_left
    (D : CubicJordanDatum J) (P Q : FreudenthalCharge J) :
    FreudenthalCharge.symplecticForm D (-P) Q =
      - FreudenthalCharge.symplecticForm D P Q := by
  rw [FreudenthalCharge.symplectic_form_skew D Q (-P),
    symplecticForm_neg_right,
    FreudenthalCharge.symplectic_form_skew D P Q]
  ring

@[simp] theorem symplecticForm_add_left
    (D : CubicJordanDatum J) (P Q R : FreudenthalCharge J) :
    FreudenthalCharge.symplecticForm D (P + Q) R =
      FreudenthalCharge.symplecticForm D P R +
        FreudenthalCharge.symplecticForm D Q R := by
  simp only [FreudenthalCharge.symplecticForm, alpha_add, beta_add,
    x_add, y_add, map_add, LinearMap.add_apply, add_mul]
  ring

theorem symplecticForm_sub_left
    (D : CubicJordanDatum J) (P Q R : FreudenthalCharge J) :
    FreudenthalCharge.symplecticForm D (P - Q) R =
      FreudenthalCharge.symplecticForm D P R -
        FreudenthalCharge.symplecticForm D Q R := by
  rw [sub_eq_add_neg, symplecticForm_add_left, symplecticForm_neg_left]
  rfl

theorem symplecticForm_sub_right
    (D : CubicJordanDatum J) (P Q R : FreudenthalCharge J) :
    FreudenthalCharge.symplecticForm D P (Q - R) =
      FreudenthalCharge.symplecticForm D P Q -
        FreudenthalCharge.symplecticForm D P R := by
  rw [sub_eq_add_neg, symplecticForm_add_right, symplecticForm_neg_right]
  rfl

def symplecticRankTwo (D : CubicJordanDatum J)
    (X Y : FreudenthalCharge J) :
    FreudenthalCharge J →ₗ[ℝ] FreudenthalCharge J :=
  (symplecticFormLinear D Y).smulRight X +
    (symplecticFormLinear D X).smulRight Y

def IsSymplecticOperator (D : CubicJordanDatum J)
    (T : FreudenthalCharge J →ₗ[ℝ] FreudenthalCharge J) : Prop :=
  ∀ Z W,
    FreudenthalCharge.symplecticForm D (T Z) W
      + FreudenthalCharge.symplecticForm D Z (T W) = 0

theorem isSymplecticOperator_zero
    (D : CubicJordanDatum J) :
    IsSymplecticOperator D (0 : FreudenthalCharge J →ₗ[ℝ] FreudenthalCharge J) := by
  intro Z W
  simp only [LinearMap.zero_apply]
  rw [FreudenthalCharge.symplectic_form_skew D W 0]
  change -(symplecticFormLinear D W) 0 + (symplecticFormLinear D Z) 0 = 0
  rw [map_zero, map_zero, neg_zero, add_zero]

theorem isSymplecticOperator_add
    (D : CubicJordanDatum J)
    {T U : FreudenthalCharge J →ₗ[ℝ] FreudenthalCharge J}
    (hT : IsSymplecticOperator D T)
    (hU : IsSymplecticOperator D U) :
    IsSymplecticOperator D (T + U) := by
  intro Z W
  simp only [LinearMap.add_apply, symplecticForm_add_left,
    symplecticForm_add_right]
  linear_combination hT Z W + hU Z W

theorem isSymplecticOperator_smul
    (D : CubicJordanDatum J) (r : ℝ)
    {T : FreudenthalCharge J →ₗ[ℝ] FreudenthalCharge J}
    (hT : IsSymplecticOperator D T) :
    IsSymplecticOperator D (r • T) := by
  intro Z W
  simp only [LinearMap.smul_apply, symplecticForm_smul_left,
    symplecticForm_smul_right]
  linear_combination r * (hT Z W)

theorem isSymplecticOperator_commutator
    (D : CubicJordanDatum J)
    {T U : FreudenthalCharge J →ₗ[ℝ] FreudenthalCharge J}
    (hT : IsSymplecticOperator D T)
    (hU : IsSymplecticOperator D U) :
    IsSymplecticOperator D (T * U - U * T) := by
  intro Z W
  simp only [LinearMap.sub_apply, Module.End.mul_apply,
    symplecticForm_sub_left, symplecticForm_sub_right]
  linear_combination hT (U Z) W - hU (T Z) W + hT Z (U W) - hU Z (T W)

@[simp] theorem symplecticRankTwo_apply
    (D : CubicJordanDatum J) (X Y Z : FreudenthalCharge J) :
    symplecticRankTwo D X Y Z =
      FreudenthalCharge.symplecticForm D Y Z • X
        + FreudenthalCharge.symplecticForm D X Z • Y := by
  rfl

theorem symplecticRankTwo_swap
    (D : CubicJordanDatum J) (X Y : FreudenthalCharge J) :
    symplecticRankTwo D X Y = symplecticRankTwo D Y X := by
  apply LinearMap.ext
  intro Z
  simp only [symplecticRankTwo_apply]
  rw [add_comm]

theorem symplecticRankTwo_cyclic_sum
    (D : CubicJordanDatum J) (x y z : FreudenthalCharge J) :
    symplecticRankTwo D z y x + symplecticRankTwo D x y z =
      FreudenthalCharge.symplecticForm D y z • x -
        FreudenthalCharge.symplecticForm D x y • z := by
  rw [symplecticRankTwo_apply, symplecticRankTwo_apply,
    FreudenthalCharge.symplectic_form_skew D y x,
    FreudenthalCharge.symplectic_form_skew D z x]
  module

theorem symplecticRankTwo_swap23
    (D : CubicJordanDatum J) (x y z : FreudenthalCharge J) :
    symplecticRankTwo D x y z - symplecticRankTwo D x z y =
      FreudenthalCharge.symplecticForm D x z • y -
        FreudenthalCharge.symplecticForm D x y • z +
          (2 * FreudenthalCharge.symplecticForm D y z) • x := by
  simp only [symplecticRankTwo_apply]
  rw [FreudenthalCharge.symplectic_form_skew D z y]
  module

theorem symplecticRankTwo_preserves
    (D : CubicJordanDatum J) (X Y Z W : FreudenthalCharge J) :
    FreudenthalCharge.symplecticForm D (symplecticRankTwo D X Y Z) W
      + FreudenthalCharge.symplecticForm D Z (symplecticRankTwo D X Y W) = 0 := by
  change
    FreudenthalCharge.symplecticForm D
        (FreudenthalCharge.symplecticForm D Y Z • X
          + FreudenthalCharge.symplecticForm D X Z • Y) W
      + FreudenthalCharge.symplecticForm D Z
        (FreudenthalCharge.symplecticForm D Y W • X
          + FreudenthalCharge.symplecticForm D X W • Y) = 0
  rw [symplecticForm_add_left, symplecticForm_add_right,
    symplecticForm_smul_left, symplecticForm_smul_left,
    symplecticForm_smul_right, symplecticForm_smul_right]
  rw [FreudenthalCharge.symplectic_form_skew D Z Y,
    FreudenthalCharge.symplectic_form_skew D Z X]
  ring

theorem symplecticRankTwo_isSymplectic
    (D : CubicJordanDatum J) (X Y : FreudenthalCharge J) :
    IsSymplecticOperator D (symplecticRankTwo D X Y) := by
  intro Z W
  exact symplecticRankTwo_preserves D X Y Z W

def symplecticOperatorLieSubalgebra (D : CubicJordanDatum J) :
    LieSubalgebra ℝ (Module.End ℝ (FreudenthalCharge J)) where
  carrier := {T | IsSymplecticOperator D T}
  zero_mem' := isSymplecticOperator_zero D
  add_mem' hT hU := isSymplecticOperator_add D hT hU
  smul_mem' r T hT := isSymplecticOperator_smul D r hT
  lie_mem' := by
    intro T U hT hU
    exact isSymplecticOperator_commutator D hT hU

theorem symplecticRankTwo_mem_subalgebra
    (D : CubicJordanDatum J) (X Y : FreudenthalCharge J) :
    symplecticRankTwo D X Y ∈ symplecticOperatorLieSubalgebra D := by
  exact symplecticRankTwo_isSymplectic D X Y

end InfoGeometry.Exceptional.Freudenthal
