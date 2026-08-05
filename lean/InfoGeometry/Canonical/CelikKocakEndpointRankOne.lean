import InfoGeometry.Canonical.CelikKocakPaperFiniteMatrixReadout

/-!
# Rank-one decomposition of the finite endpoint operator algebra

The endpoint operators are treated as linear maps on the native finite
function space.  This file supplies the matrix-unit replacement needed for a
future proof that the tilt/switch-generated subalgebra is all of the endpoint
operator algebra.
-/

noncomputable section

namespace InfoGeometry.Canonical.CelikKocakPaperFormalism

open FunctionSpace

noncomputable def endpointRankOne {n : ℕ}
    (x y : CantorAddress n) : EndpointOperator n :=
  (LinearMap.single ℂ (fun _ : CantorAddress n => ℂ) x).comp
    (LinearMap.proj y)

@[simp] theorem endpointRankOne_apply {n : ℕ}
    (x y z : CantorAddress n) (f : FunctionSpace n) :
    endpointRankOne x y f z = if z = x then f y else 0 := by
  simp [endpointRankOne, Pi.single_apply]

@[simp] theorem endpointRankOne_basis_apply {n : ℕ}
    (x y z : CantorAddress n) :
    endpointRankOne x y (endpointBasis (n := n) z) =
      if y = z then endpointBasis (n := n) x else 0 := by
  apply funext
  intro w
  by_cases hyz : y = z
  · subst hyz
    rw [endpointRankOne_apply, endpointBasis_apply]
    by_cases hwx : w = x
    · simp [hwx]
    · have hxw : x ≠ w := Ne.symm hwx
      simp [hwx, hxw]
  · simp [endpointRankOne_apply, hyz]

private theorem endpointOperator_sum_apply {n : ℕ}
    (g : CantorAddress n → EndpointOperator n) (f : FunctionSpace n) :
    (∑ i, g i) f = ∑ i, g i f := by
  classical
  change (Finset.univ.sum (fun i : CantorAddress n => g i)) f = _
  induction (Finset.univ : Finset (CantorAddress n)) using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      simp only [Finset.sum_insert ha, LinearMap.add_apply, ih]

theorem endpointOperator_eq_rankOne_sum {n : ℕ} (A : EndpointOperator n) :
    A = ∑ y : CantorAddress n, ∑ x : CantorAddress n,
      ((endpointBasis (n := n)).repr (A (endpointBasis (n := n) y))) x •
        endpointRankOne x y := by
  apply (endpointBasis (n := n)).ext
  intro y
  change A (endpointBasis (n := n) y) =
    (∑ y' : CantorAddress n, ∑ x : CantorAddress n,
      ((endpointBasis (n := n)).repr
        (A (endpointBasis (n := n) y'))) x • endpointRankOne x y')
      (endpointBasis (n := n) y)
  have houter :
      (∑ y' : CantorAddress n, ∑ x : CantorAddress n,
        ((endpointBasis (n := n)).repr
          (A (endpointBasis (n := n) y'))) x • endpointRankOne x y')
          (endpointBasis (n := n) y) =
        ∑ y' : CantorAddress n,
          (∑ x : CantorAddress n,
            ((endpointBasis (n := n)).repr
              (A (endpointBasis (n := n) y'))) x • endpointRankOne x y')
            (endpointBasis (n := n) y) :=
    by exact endpointOperator_sum_apply _ _
  rw [houter]
  rw [Fintype.sum_eq_single y]
  · have hinner :
        (∑ x : CantorAddress n,
          ((endpointBasis (n := n)).repr
            (A (endpointBasis (n := n) y))) x • endpointRankOne x y)
            (endpointBasis (n := n) y) =
          ∑ x : CantorAddress n,
            ((endpointBasis (n := n)).repr
              (A (endpointBasis (n := n) y))) x •
              endpointRankOne x y (endpointBasis (n := n) y) :=
      by exact endpointOperator_sum_apply _ _
    rw [hinner]
    simp_rw [endpointRankOne_basis_apply]
    simpa using ((endpointBasis (n := n)).sum_repr
      (A (endpointBasis (n := n) y))).symm
  · intro y' hy'
    have hzero :
        (∑ x : CantorAddress n,
          ((endpointBasis (n := n)).repr
            (A (endpointBasis (n := n) y'))) x • endpointRankOne x y')
            (endpointBasis (n := n) y) =
          ∑ x : CantorAddress n,
            ((endpointBasis (n := n)).repr
              (A (endpointBasis (n := n) y'))) x •
              endpointRankOne x y' (endpointBasis (n := n) y) := by
      exact endpointOperator_sum_apply _ _
    rw [hzero]
    apply Finset.sum_eq_zero
    intro x hx
    rw [endpointRankOne_basis_apply]
    simp [hy']

end InfoGeometry.Canonical.CelikKocakPaperFormalism
