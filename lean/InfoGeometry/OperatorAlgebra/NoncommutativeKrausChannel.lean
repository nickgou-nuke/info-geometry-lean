/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.NoncommutativeGradedTrace
import Mathlib.Algebra.Star.Basic

/-!
# Finite Kraus sums on noncommutative operator algebras

This owner states the algebraic finite Kraus formula on an arbitrary
associative star ring. Unitality and preservation of a cyclic functional use
their respective ordered completeness equations. Positivity and complete
positivity require additional order structure and are not asserted here.
-/

namespace InfoGeometry.OperatorAlgebra.NoncommutativeKrausChannel

open InfoGeometry.OperatorAlgebra.NoncommutativeGradedTrace

variable {A : Type*} [Ring A] [StarRing A]

/-- Conjugation by an operator and its adjoint. -/
def unitaryConjugation (u x : A) : A := u * x * star u

/-- If the adjoint is a left inverse, conjugation preserves ordered
multiplication. -/
theorem unitaryConjugation_mul {u : A} (hu : star u * u = 1) (x y : A) :
    unitaryConjugation u (x * y) =
      unitaryConjugation u x * unitaryConjugation u y := by
  unfold unitaryConjugation
  calc
    u * (x * y) * star u = u * x * (y * star u) := by noncomm_ring
    _ = u * x * (star u * u) * (y * star u) := by rw [hu]; simp
    _ = (u * x * star u) * (u * y * star u) := by noncomm_ring

/-- Unitary conjugation preserves the operator commutator. -/
theorem unitaryConjugation_commutator {u : A} (hu : star u * u = 1)
    (x y : A) :
    unitaryConjugation u (operatorCommutator x y) =
      operatorCommutator (unitaryConjugation u x) (unitaryConjugation u y) := by
  unfold operatorCommutator
  calc
    unitaryConjugation u (x * y - y * x) =
        unitaryConjugation u (x * y) - unitaryConjugation u (y * x) := by
      unfold unitaryConjugation
      rw [mul_sub, sub_mul]
    _ = unitaryConjugation u x * unitaryConjugation u y -
        unitaryConjugation u y * unitaryConjugation u x := by
      rw [unitaryConjugation_mul hu x y, unitaryConjugation_mul hu y x]

/-- Unitary conjugation preserves the symmetric operator product. -/
theorem unitaryConjugation_anticommutator {u : A} (hu : star u * u = 1)
    (x y : A) :
    unitaryConjugation u (operatorAnticommutator x y) =
      operatorAnticommutator (unitaryConjugation u x) (unitaryConjugation u y) := by
  unfold operatorAnticommutator
  calc
    unitaryConjugation u (x * y + y * x) =
        unitaryConjugation u (x * y) + unitaryConjugation u (y * x) := by
      unfold unitaryConjugation
      rw [mul_add, add_mul]
    _ = unitaryConjugation u x * unitaryConjugation u y +
        unitaryConjugation u y * unitaryConjugation u x := by
      rw [unitaryConjugation_mul hu x y, unitaryConjugation_mul hu y x]

/-- Two-sided unitarity makes adjoint conjugation unital. -/
theorem unitaryConjugation_one {u : A} (hu : u * star u = 1) :
    unitaryConjugation u 1 = 1 := by
  unfold unitaryConjugation
  rw [mul_one, hu]

/-- The finite Kraus sum associated with an operator family. -/
def krausChannel {ι : Type*} [Fintype ι] (V : ι → A) (x : A) : A :=
  ∑ i, V i * x * star (V i)

/-- The finite Kraus action as an additive superoperator on the operator
algebra. -/
def krausChannelAddHom {ι : Type*} [Fintype ι] (V : ι → A) : A →+ A where
  toFun := krausChannel V
  map_zero' := by simp [krausChannel]
  map_add' x y := by
    simp only [krausChannel, mul_add, add_mul, Finset.sum_add_distrib]

/-- The backward Kraus action on observables, using the adjoint family. -/
def krausDual {ι : Type*} [Fintype ι] (V : ι → A) (y : A) : A :=
  ∑ i, star (V i) * y * V i

/-- Forward and backward Kraus actions are dual under every cyclic additive
functional. -/
theorem cyclicFunctional_kraus_pairing {R ι : Type*} [AddCommGroup R]
    [Fintype ι] (V : ι → A) (x y : A)
    (τ : A →+ R) (hτ : IsCyclic τ) :
    τ (krausChannel V x * y) = τ (x * krausDual V y) := by
  have hterm (i : ι) :
      τ ((V i * x * star (V i)) * y) =
        τ (x * (star (V i) * y * V i)) := by
    calc
      τ ((V i * x * star (V i)) * y) =
          τ (V i * (x * star (V i) * y)) := by simp only [mul_assoc]
      _ = τ ((x * star (V i) * y) * V i) := hτ _ _
      _ = τ (x * (star (V i) * y * V i)) := by simp only [mul_assoc]
  unfold krausChannel krausDual
  calc
    τ ((∑ i, V i * x * star (V i)) * y) =
        τ (∑ i, (V i * x * star (V i)) * y) := by rw [Finset.sum_mul]
    _ = ∑ i, τ ((V i * x * star (V i)) * y) := map_sum τ _ _
    _ = ∑ i, τ (x * (star (V i) * y * V i)) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact hterm i
    _ = τ (x * ∑ i, star (V i) * y * V i) := by
      rw [← map_sum, ← Finset.mul_sum]

/-- The channel's value at the identity is its left completeness sum. -/
theorem krausChannel_one {ι : Type*} [Fintype ι] (V : ι → A) :
    krausChannel V 1 = ∑ i, V i * star (V i) := by
  unfold krausChannel
  apply Finset.sum_congr rfl
  intro i hi
  rw [mul_one]

/-- Left completeness makes the finite Kraus channel unital. -/
theorem krausChannel_unital {ι : Type*} [Fintype ι] (V : ι → A)
    (hV : ∑ i, V i * star (V i) = 1) :
    krausChannel V 1 = 1 := by
  rw [krausChannel_one, hV]

/-- Right completeness makes the finite Kraus channel preserve every cyclic
additive functional. The order of `star (V i) * V i` is essential. -/
theorem krausChannel_preserves_cyclicFunctional {R ι : Type*}
    [AddCommGroup R] [Fintype ι] (V : ι → A)
    (hV : ∑ i, star (V i) * V i = 1)
    (τ : A →+ R) (hτ : IsCyclic τ) (x : A) :
    τ (krausChannel V x) = τ x := by
  have hterm (i : ι) :
      τ (V i * x * star (V i)) = τ ((star (V i) * V i) * x) := by
    calc
      τ (V i * x * star (V i)) = τ ((V i * x) * star (V i)) := by
        rw [mul_assoc]
      _ = τ (star (V i) * (V i * x)) := hτ (V i * x) (star (V i))
      _ = τ ((star (V i) * V i) * x) := by rw [mul_assoc]
  unfold krausChannel
  calc
    τ (∑ i, V i * x * star (V i)) =
        ∑ i, τ (V i * x * star (V i)) := map_sum τ _ _
    _ = ∑ i, τ ((star (V i) * V i) * x) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact hterm i
    _ = τ ((∑ i, star (V i) * V i) * x) := by
      rw [Finset.sum_mul, ← map_sum]
    _ = τ x := by rw [hV, one_mul]

section WeightedUnitaryMixtures

variable {R A ι : Type*} [CommSemiring R] [Ring A] [Algebra R A]
  [StarRing A] [Fintype ι]

/-- A finite weighted mixture of adjoint conjugations on an associative
operator algebra.  The weights are central scalars; no commutativity of the
operator algebra is assumed. -/
def finiteUnitaryMixture (w : ι → R) (U : ι → A) (x : A) : A :=
  ∑ i, w i • (U i * x * star (U i))

/-- A normalized weighted mixture of left-unitary conjugations is unital. -/
theorem finiteUnitaryMixture_unital (w : ι → R) (U : ι → A)
    (hw : ∑ i, w i = 1)
    (hU : ∀ i, U i * star (U i) = 1) :
    finiteUnitaryMixture w U 1 = 1 := by
  unfold finiteUnitaryMixture
  have hterm (i : ι) : U i * 1 * star (U i) = 1 := by
    rw [mul_one, hU i]
  simp_rw [hterm]
  rw [← Finset.sum_smul, hw, one_smul]

/-- A normalized weighted mixture of right-unitary conjugations preserves
every `R`-linear cyclic functional. -/
theorem finiteUnitaryMixture_preserves_cyclicLinearFunctional
    {S : Type*} [AddCommMonoid S] [Module R S]
    (w : ι → R) (U : ι → A) (hw : ∑ i, w i = 1)
    (hU : ∀ i, star (U i) * U i = 1)
    (τ : A →ₗ[R] S)
    (hτ : ∀ a b : A, τ (a * b) = τ (b * a)) (x : A) :
    τ (finiteUnitaryMixture w U x) = τ x := by
  have hterm (i : ι) : τ (U i * x * star (U i)) = τ x := by
    calc
      τ (U i * x * star (U i)) = τ (star (U i) * (U i * x)) := by
        exact hτ (U i * x) (star (U i))
      _ = τ ((star (U i) * U i) * x) := by rw [mul_assoc]
      _ = τ x := by rw [hU i, one_mul]
  unfold finiteUnitaryMixture
  rw [map_sum]
  simp_rw [map_smul, hterm]
  rw [← Finset.sum_smul, hw, one_smul]

end WeightedUnitaryMixtures

end InfoGeometry.OperatorAlgebra.NoncommutativeKrausChannel
