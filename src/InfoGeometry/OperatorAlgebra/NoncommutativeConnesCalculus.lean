/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.NoncommutativeGradedTrace
import InfoGeometry.OperatorAlgebra.PeirceQuantumGeometricTensor
import Mathlib.Tactic

/-!
# Connes differential identities in an associative operator algebra

For an involution `F`, the commutator differential is a derivation, its values
are odd under `F`, and products of two such values commute with `F`. Cyclic
trace consequences are stated for an arbitrary cyclic additive functional.
No Fredholm, compact-resolvent, or index-theorem conclusion is included.
-/

namespace InfoGeometry.OperatorAlgebra.NoncommutativeConnesCalculus

open InfoGeometry.OperatorAlgebra.NoncommutativeGradedTrace
open InfoGeometry.OperatorAlgebra.PeirceQuantumGeometricTensor
open InfoGeometry.Core.PeirceDecomposition
open InfoGeometry.Core.PeirceGrading

variable {A : Type*} [Ring A]

/-- The inner Connes differential associated with an operator `F`. -/
def connesDifferential (F x : A) : A := operatorCommutator F x

/-- The commutator differential obeys the noncommutative Leibniz rule. -/
theorem connesDifferential_leibniz (F x y : A) :
    connesDifferential F (x * y) =
      connesDifferential F x * y + x * connesDifferential F y := by
  unfold connesDifferential operatorCommutator
  noncomm_ring

/-- The square of an odd operator commutes with the grading, in any
associative operator ring. -/
theorem oddOperator_square_commutes_with_grading {γ D : A}
    (hOdd : γ * D = -(D * γ)) :
    γ * (D * D) = (D * D) * γ := by
  calc
    γ * (D * D) = (γ * D) * D := by rw [mul_assoc]
    _ = -(D * γ) * D := by rw [hOdd]
    _ = -((D * γ) * D) := by rw [neg_mul]
    _ = -(D * (γ * D)) := by rw [mul_assoc]
    _ = -(D * (-(D * γ))) := by rw [hOdd]
    _ = (D * D) * γ := by simp [mul_assoc]

/-- Conjugation by an involutive grading flips an odd operator. -/
theorem grading_conjugates_oddOperator {γ D : A}
    (hSquare : γ * γ = 1) (hOdd : γ * D = -(D * γ)) :
    γ * D * γ = -D := by
  calc
    γ * D * γ = -(D * γ) * γ := by rw [hOdd]
    _ = -((D * γ) * γ) := by rw [neg_mul]
    _ = -(D * (γ * γ)) := by rw [mul_assoc]
    _ = -D := by rw [hSquare, mul_one]

/-- The commutator of an odd operator with a grading-even operator is odd.
This is the operator-algebraic chirality law for the Dirac differential. -/
theorem commutator_oddOperator_evenElement_is_odd {γ D a : A}
    (hOdd : γ * D = -(D * γ)) (hEven : γ * a = a * γ) :
    operatorAnticommutator γ (operatorCommutator D a) = 0 := by
  unfold operatorAnticommutator operatorCommutator
  have hfirst : D * (a * γ) = (D * γ) * a := by
    rw [← hEven, mul_assoc]
  have hsecond : (a * γ) * D = -(a * (D * γ)) := by
    calc
      (a * γ) * D = a * (γ * D) := by rw [mul_assoc]
      _ = a * -(D * γ) := by rw [hOdd]
      _ = -(a * (D * γ)) := by rw [mul_neg]
  have hExpand : γ * (D * a - a * D) + (D * a - a * D) * γ =
      (γ * D) * a - (γ * a) * D + D * (a * γ) - a * (D * γ) := by
    noncomm_ring
  rw [hExpand, hOdd, hEven, hfirst, hsecond]
  noncomm_ring

/-- The matrix-level Dirac chirality packet in an arbitrary associative
operator ring: an odd Dirac operator conjugates to its negative, its square is
graded-even, and its commutator with a grading-even element is grading-odd.
No matrix coordinates, self-adjointness, or spectral assumptions are needed. -/
theorem graded_dirac_laplacian_and_even_gradient {γ D a : A}
    (hSquare : γ * γ = 1)
    (hOdd : γ * D = -(D * γ))
    (hEven : γ * a = a * γ) :
    γ * D * γ = -D ∧
    operatorCommutator γ (D * D) = 0 ∧
    operatorAnticommutator γ (operatorCommutator D a) = 0 := by
  exact ⟨grading_conjugates_oddOperator hSquare hOdd,
    sub_eq_zero.mpr (oddOperator_square_commutes_with_grading hOdd),
    commutator_oddOperator_evenElement_is_odd hOdd hEven⟩

/-- If `F` is an involution, every value of its inner differential
anticommutes with `F`. -/
theorem connesDifferential_anticommutes {F : A} (hF : F * F = 1) (x : A) :
    operatorAnticommutator F (connesDifferential F x) = 0 := by
  unfold operatorAnticommutator connesDifferential operatorCommutator
  calc
    F * (F * x - x * F) + (F * x - x * F) * F =
        (F * F) * x - (F * x) * F + (F * x) * F - x * (F * F) := by
          noncomm_ring
    _ = 0 := by rw [hF]; simp

/-- A product of two Connes differentials commutes with the involution. -/
theorem connesDifferential_product_commutes {F : A} (hF : F * F = 1)
    (x y : A) :
    operatorCommutator F
      (connesDifferential F x * connesDifferential F y) = 0 := by
  have hx := connesDifferential_anticommutes hF x
  have hy := connesDifferential_anticommutes hF y
  have hx' : F * connesDifferential F x =
      -(connesDifferential F x * F) := eq_neg_of_add_eq_zero_left hx
  have hy' : F * connesDifferential F y =
      -(connesDifferential F y * F) := eq_neg_of_add_eq_zero_left hy
  have hprod : F * (connesDifferential F x * connesDifferential F y) =
      (connesDifferential F x * connesDifferential F y) * F := by
    calc
      F * (connesDifferential F x * connesDifferential F y) =
          (F * connesDifferential F x) * connesDifferential F y := by rw [mul_assoc]
      _ = -(connesDifferential F x * F) * connesDifferential F y := by rw [hx']
      _ = -(connesDifferential F x * (F * connesDifferential F y)) := by
        rw [neg_mul, mul_assoc]
      _ = -(connesDifferential F x *
          -(connesDifferential F y * F)) := by rw [hy']
      _ = (connesDifferential F x * connesDifferential F y) * F := by
        simp [mul_assoc]
  unfold operatorCommutator
  rw [hprod]
  exact sub_self _

/-- Cyclicity makes the graded trace of a single exact differential vanish
when the grading squares to one. -/
theorem cyclic_gradedTrace_differential_eq_zero {R : Type*}
    [AddCommGroup R] (τ : A →+ R) (hτ : IsCyclic τ) {F : A}
    (hF : F * F = 1) (x : A) :
    gradedTrace τ F (connesDifferential F x) = 0 := by
  have hcycle : τ (F * x * F) = τ x := by
    calc
      τ ((F * x) * F) = τ (F * (F * x)) := hτ (F * x) F
      _ = τ ((F * F) * x) := by rw [mul_assoc]
      _ = τ x := by rw [hF, one_mul]
  unfold gradedTrace connesDifferential operatorCommutator
  calc
    τ (F * (F * x - x * F)) = τ ((F * F) * x) - τ ((F * x) * F) := by
      rw [mul_sub, map_sub, ← mul_assoc, ← mul_assoc]
    _ = τ x - τ x := by rw [hF, one_mul, hcycle]
    _ = 0 := sub_self _

/-- The cyclic graded trace of a product of two exact differentials is
skew-symmetric in its two differential factors. -/
theorem cyclic_gradedTrace_differential_pair_skew {R : Type*}
    [AddCommGroup R] (τ : A →+ R) (hτ : IsCyclic τ) {F : A}
    (hF : F * F = 1) (x y : A) :
    gradedTrace τ F
        (connesDifferential F x * connesDifferential F y) =
      -gradedTrace τ F
        (connesDifferential F y * connesDifferential F x) := by
  have hx := connesDifferential_anticommutes hF x
  have hx' : F * connesDifferential F x =
      -(connesDifferential F x * F) := eq_neg_of_add_eq_zero_left hx
  unfold gradedTrace
  calc
    τ (F * (connesDifferential F x * connesDifferential F y)) =
        τ ((F * connesDifferential F x) * connesDifferential F y) := by
      rw [mul_assoc]
    _ = τ (connesDifferential F y *
        (F * connesDifferential F x)) := hτ (F * connesDifferential F x)
          (connesDifferential F y)
    _ = τ (-(connesDifferential F y *
        (connesDifferential F x * F))) := by rw [hx', mul_neg]
    _ = -τ (connesDifferential F y *
        (connesDifferential F x * F)) := by rw [map_neg]
    _ = -τ (F * (connesDifferential F y * connesDifferential F x)) := by
      congr 1
      calc
        τ (connesDifferential F y *
            (connesDifferential F x * F)) =
            τ ((connesDifferential F y * connesDifferential F x) * F) := by
          rw [mul_assoc]
        _ = τ (F *
            (connesDifferential F y * connesDifferential F x)) := hτ _ _

/-- The cyclic trace of a tangent-curvature commutator splits into opposite
Peirce corner contributions. The identity is valid in any associative ring
with a cyclic additive functional, not just for matrix trace. -/
theorem cyclic_tangent_curvature_corner_cancellation {R : Type*}
    [AddCommGroup R] (τ : A →+ R) (hτ : IsCyclic τ) {p : A}
    (hp : IsIdempotentElem p) (a b : A) :
    τ (p * operatorComm (peirceTangent p a) (peirceTangent p b) * p) +
      τ ((1 - p) * operatorComm (peirceTangent p a) (peirceTangent p b) * (1 - p)) = 0 := by
  let q : A := 1 - p
  let curvature : A := operatorComm (peirceTangent p a) (peirceTangent p b)
  have hpq : p * q = 0 := by
    dsimp [q]
    noncomm_ring [hp.eq]
  have hqp : q * p = 0 := by
    dsimp [q]
    noncomm_ring [hp.eq]
  have hq : q * q = q := by
    dsimp [q]
    noncomm_ring [hp.eq]
  have hcurvature_comm : p * curvature = curvature * p := by
    change p * operatorComm (peirceTangent p a) (peirceTangent p b) =
      operatorComm (peirceTangent p a) (peirceTangent p b) * p
    exact (mem_even_iff hp).mp
      (tangent_lie_jordan_products_mem_even hp a b).1
  have hcurvature_q_comm : q * curvature = curvature * q := by
    dsimp [q]
    noncomm_ring [hcurvature_comm]
  have hcross₁ : p * curvature * q = 0 := by
    calc
      p * curvature * q = curvature * p * q := by rw [hcurvature_comm]
      _ = curvature * (p * q) := by rw [mul_assoc]
      _ = 0 := by rw [hpq, mul_zero]
  have hcross₂ : q * curvature * p = 0 := by
    calc
      q * curvature * p = curvature * q * p := by rw [hcurvature_q_comm]
      _ = curvature * (q * p) := by rw [mul_assoc]
      _ = 0 := by rw [hqp, mul_zero]
  have hdecomp : p * curvature * p + q * curvature * q = curvature := by
    calc
      p * curvature * p + q * curvature * q =
          (p + q) * curvature * (p + q) := by
        noncomm_ring [hcross₁, hcross₂]
      _ = curvature := by dsimp [q]; noncomm_ring
  have htrace_curvature : τ curvature = 0 := by
    change τ (operatorComm (peirceTangent p a) (peirceTangent p b)) = 0
    unfold operatorComm
    rw [map_sub, hτ (peirceTangent p a) (peirceTangent p b), sub_self]
  calc
    τ (p * curvature * p) + τ (q * curvature * q) = τ curvature := by
      rw [← map_add, hdecomp]
    _ = 0 := htrace_curvature

/-- The Cartan-weighted cyclic curvature equals twice its core Peirce trace.
This is a finite algebraic Chern/Berry pairing identity and carries no
topological index or continuum interpretation. -/
theorem cyclic_connes_curvature_eq_two_core_flux {R : Type*}
    [AddCommGroup R] (τ : A →+ R) (hτ : IsCyclic τ) {p : A}
    (hp : IsIdempotentElem p) (a b : A) :
    τ ((p - (1 - p)) *
        operatorComm (peirceTangent p a) (peirceTangent p b)) =
      (2 : ℕ) • τ (p *
        operatorComm (peirceTangent p a) (peirceTangent p b) * p) := by
  let q : A := 1 - p
  let curvature : A := operatorComm (peirceTangent p a) (peirceTangent p b)
  have hpq : p * q = 0 := by
    dsimp [q]
    noncomm_ring [hp.eq]
  have hqp : q * p = 0 := by
    dsimp [q]
    noncomm_ring [hp.eq]
  have hq : q * q = q := by
    dsimp [q]
    noncomm_ring [hp.eq]
  have hcurvature_comm : p * curvature = curvature * p := by
    change p * operatorComm (peirceTangent p a) (peirceTangent p b) =
      operatorComm (peirceTangent p a) (peirceTangent p b) * p
    exact (mem_even_iff hp).mp
      (tangent_lie_jordan_products_mem_even hp a b).1
  have hcurvature_q_comm : q * curvature = curvature * q := by
    dsimp [q]
    noncomm_ring [hcurvature_comm]
  have hpCorner : p * curvature * p = p * curvature := by
    calc
      p * curvature * p = p * (curvature * p) := by rw [mul_assoc]
      _ = p * (p * curvature) := by rw [← hcurvature_comm]
      _ = p * curvature := by rw [← mul_assoc, hp.eq]
  have hqCorner : q * curvature * q = q * curvature := by
    calc
      q * curvature * q = q * (curvature * q) := by rw [mul_assoc]
      _ = q * (q * curvature) := by rw [← hcurvature_q_comm]
      _ = q * curvature := by rw [← mul_assoc, hq]
  have hcorner_trace : τ (p * curvature) + τ (q * curvature) = 0 := by
    calc
      τ (p * curvature) + τ (q * curvature) =
          τ (p * curvature * p) + τ (q * curvature * q) := by
        rw [hpCorner, hqCorner]
      _ = 0 := cyclic_tangent_curvature_corner_cancellation τ hτ hp a b
  have hq_trace : τ (q * curvature) = -τ (p * curvature) :=
    eq_neg_of_add_eq_zero_right hcorner_trace
  calc
    τ ((p - q) * curvature) =
        τ (p * curvature) - τ (q * curvature) := by
      rw [sub_mul, map_sub]
    _ = τ (p * curvature) + τ (p * curvature) := by rw [hq_trace]; abel
    _ = (2 : ℕ) • τ (p * curvature) := by rw [two_nsmul]
    _ = (2 : ℕ) • τ (p * curvature * p) := by rw [hpCorner]

end InfoGeometry.OperatorAlgebra.NoncommutativeConnesCalculus
