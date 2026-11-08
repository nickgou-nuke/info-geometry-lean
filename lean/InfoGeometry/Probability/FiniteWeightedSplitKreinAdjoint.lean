/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Probability.FiniteMarkovWeightedAdjoint
import Mathlib.Tactic

/-!
# Finite weighted split pairing and adjoints

For a finite index type with nonzero weights, the existing `weightedAdjoint`
is adjoint to matrix action for the weighted pairing. Its block action on the
two summands is consequently self-adjoint for the off-diagonal neutral
pairing. The pairing is indefinite; this is not positive-Hilbert
self-adjointness. No stochasticity or detailed-balance hypothesis is used.
-/

namespace InfoGeometry.Probability

open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The diagonal-weighted bilinear pairing on functions on a finite set. -/
def weightedVectorPairing (π u v : ι → ℝ) : ℝ :=
  ∑ i, π i * u i * v i

omit [DecidableEq ι] in
/-- The weighted pairing is additive in its first argument. -/
theorem weightedVectorPairing_add_left (π u v w : ι → ℝ) :
    weightedVectorPairing π (u + v) w =
      weightedVectorPairing π u w + weightedVectorPairing π v w := by
  unfold weightedVectorPairing
  calc
    (∑ i, π i * (u i + v i) * w i) =
        ∑ i, (π i * u i * w i + π i * v i * w i) := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [mul_add, add_mul]
    _ = (∑ i, π i * u i * w i) + ∑ i, π i * v i * w i :=
      Finset.sum_add_distrib

omit [DecidableEq ι] in
/-- The weighted pairing is homogeneous in its first argument. -/
theorem weightedVectorPairing_smul_left (π : ι → ℝ) (c : ℝ) (u v : ι → ℝ) :
    weightedVectorPairing π (c • u) v =
      c * weightedVectorPairing π u v := by
  unfold weightedVectorPairing
  simp only [Pi.smul_apply, smul_eq_mul]
  calc
    (∑ i, π i * (c * u i) * v i) =
        ∑ i, c * (π i * u i * v i) := by
          apply Finset.sum_congr rfl
          intro i hi
          ring
    _ = c * ∑ i, π i * u i * v i := by rw [Finset.mul_sum]

/-- The off-diagonal neutral pairing on two copies of a weighted finite space. -/
def splitWeightedPairing (π : ι → ℝ)
    (x y : (ι → ℝ) × (ι → ℝ)) : ℝ :=
  weightedVectorPairing π x.1 y.2 + weightedVectorPairing π x.2 y.1

/-- The block action of `P` on the first sheet and its `π`-weighted adjoint
on the second sheet. -/
noncomputable def splitWeightedOperator (π : ι → ℝ) (P : Matrix ι ι ℝ)
    (x : (ι → ℝ) × (ι → ℝ)) : (ι → ℝ) × (ι → ℝ) :=
  (P *ᵥ x.1, weightedAdjoint π P *ᵥ x.2)

/-- The alternating companion form associated with the off-diagonal pairing. -/
def splitWeightedSymplectic (π : ι → ℝ)
    (x y : (ι → ℝ) × (ι → ℝ)) : ℝ :=
  weightedVectorPairing π x.1 y.2 - weightedVectorPairing π x.2 y.1

/-- The sheet polarization, acting by `+1` on the first summand and `-1` on
the second. -/
def splitWeightedPolarization (x : (ι → ℝ) × (ι → ℝ)) : (ι → ℝ) × (ι → ℝ) :=
  (x.1, -x.2)

/-- The sheet exchange on the doubled carrier. -/
def splitWeightedSheetSwap (x : (ι → ℝ) × (ι → ℝ)) : (ι → ℝ) × (ι → ℝ) :=
  (x.2, x.1)

/-- The half-sum action of a matrix and its weighted adjoint. -/
noncomputable def weightedSymmetrizedAction (π : ι → ℝ) (P : Matrix ι ι ℝ)
    (u : ι → ℝ) : ι → ℝ :=
  (1 / 2 : ℝ) • (P *ᵥ u + weightedAdjoint π P *ᵥ u)

omit [DecidableEq ι] in
/-- Matrix action is adjoint to `weightedAdjoint` for the weighted pairing.
The only weight hypothesis is non-vanishing, needed by the inverse in the
definition of `weightedAdjoint`. -/
theorem weightedVectorPairing_mulVec_eq_mulVec_weightedAdjoint
    (π : ι → ℝ) (P : Matrix ι ι ℝ) (u v : ι → ℝ)
    (hπ : ∀ i, π i ≠ 0) :
    weightedVectorPairing π (P *ᵥ u) v =
      weightedVectorPairing π u (weightedAdjoint π P *ᵥ v) := by
  classical
  change (∑ i, π i * (∑ j, P i j * u j) * v i) =
    ∑ j, π j * u j * (∑ i, (π j)⁻¹ * P i j * π i * v i)
  calc
    (∑ i, π i * (∑ j, P i j * u j) * v i) =
        ∑ i, ∑ j, π i * (P i j * u j) * v i := by
          apply Finset.sum_congr rfl
          intro i _
          rw [Finset.mul_sum, Finset.sum_mul]
    _ = ∑ j, ∑ i, π i * (P i j * u j) * v i := Finset.sum_comm
    _ = ∑ j, ∑ i, π j * u j * ((π j)⁻¹ * P i j * π i * v i) := by
          apply Finset.sum_congr rfl
          intro j _
          apply Finset.sum_congr rfl
          intro i _
          field_simp [hπ j]
    _ = ∑ j, π j * u j * (∑ i, (π j)⁻¹ * P i j * π i * v i) := by
          apply Finset.sum_congr rfl
          intro j _
          rw [Finset.mul_sum]

omit [Fintype ι] [DecidableEq ι] in
/-- The weighted adjoint is an involution when all weights are nonzero. -/
theorem weightedAdjoint_involutive
    (π : ι → ℝ) (P : Matrix ι ι ℝ) (hπ : ∀ i, π i ≠ 0) :
    weightedAdjoint π (weightedAdjoint π P) = P := by
  classical
  ext i j
  simp only [weightedAdjoint]
  field_simp [hπ i, hπ j]

/-- Powers commute with taking the weighted adjoint: the anti-multiplicative
law reverses a word, and a power consists of repeated copies of one matrix. -/
theorem weightedAdjoint_pow
    (π : ι → ℝ) (P : Matrix ι ι ℝ) (hπ : ∀ i, π i ≠ 0) (k : ℕ) :
    weightedAdjoint π P ^ k = weightedAdjoint π (P ^ k) := by
  induction k with
  | zero => simp [weightedAdjoint_one π hπ]
  | succ k ih =>
    calc
      weightedAdjoint π P ^ (k + 1) =
          weightedAdjoint π P ^ k * weightedAdjoint π P := by rw [pow_succ]
      _ = weightedAdjoint π (P ^ k) * weightedAdjoint π P := by rw [ih]
      _ = weightedAdjoint π (P * P ^ k) := by
            rw [weightedAdjoint_mul π P (P ^ k) hπ]
      _ = weightedAdjoint π (P ^ (k + 1)) := by rw [pow_succ']

omit [DecidableEq ι] in
/-- The two coordinate sheets are isotropic for the off-diagonal pairing. -/
theorem splitWeightedPairing_firstSheet_zero (π : ι → ℝ) (u v : ι → ℝ) :
    splitWeightedPairing π (u, 0) (v, 0) = 0 := by
  simp [splitWeightedPairing, weightedVectorPairing]

omit [DecidableEq ι] in
theorem splitWeightedPairing_secondSheet_zero (π : ι → ℝ) (u v : ι → ℝ) :
    splitWeightedPairing π (0, u) (0, v) = 0 := by
  simp [splitWeightedPairing, weightedVectorPairing]

omit [DecidableEq ι] in
/-- Exact self-adjointness of the doubled block operator for the neutral
off-diagonal weighted pairing. This statement applies to every matrix `P`;
causality, when separately assumed, constrains the dual block to the reverse
triangular support. -/
theorem splitWeightedOperator_selfAdjoint
    (π : ι → ℝ) (P : Matrix ι ι ℝ) (x y : (ι → ℝ) × (ι → ℝ))
    (hπ : ∀ i, π i ≠ 0) :
    splitWeightedPairing π (splitWeightedOperator π P x) y =
      splitWeightedPairing π x (splitWeightedOperator π P y) := by
  rcases x with ⟨xp, xm⟩
  rcases y with ⟨yp, ym⟩
  simp only [splitWeightedOperator, splitWeightedPairing]
  rw [weightedVectorPairing_mulVec_eq_mulVec_weightedAdjoint π P xp ym hπ,
    weightedVectorPairing_mulVec_eq_mulVec_weightedAdjoint π
      (weightedAdjoint π P) xm yp ?_]
  · rw [weightedAdjoint_involutive π P hπ]
  · exact hπ

omit [DecidableEq ι] in
/-- The two coordinate sheets are invariant under the block operator, with
the original matrix acting on the first sheet. -/
theorem splitWeightedOperator_firstSheet (π : ι → ℝ) (P : Matrix ι ι ℝ)
    (u : ι → ℝ) :
    splitWeightedOperator π P (u, 0) = (P *ᵥ u, 0) := by
  simp [splitWeightedOperator]

omit [DecidableEq ι] in
/-- The second coordinate sheet is invariant, with the weighted adjoint acting
there. -/
theorem splitWeightedOperator_secondSheet (π : ι → ℝ) (P : Matrix ι ι ℝ)
    (u : ι → ℝ) :
    splitWeightedOperator π P (0, u) = (0, weightedAdjoint π P *ᵥ u) := by
  simp [splitWeightedOperator]

omit [DecidableEq ι] in
/-- The doubled block operator commutes with the sheet polarization. -/
theorem splitWeightedOperator_commutes_polarization
    (π : ι → ℝ) (P : Matrix ι ι ℝ) (x : (ι → ℝ) × (ι → ℝ)) :
    splitWeightedPolarization (splitWeightedOperator π P x) =
      splitWeightedOperator π P (splitWeightedPolarization x) := by
  rcases x with ⟨xp, xm⟩
  simp [splitWeightedPolarization, splitWeightedOperator, Matrix.mulVec_neg]

omit [DecidableEq ι] in
/-- The doubled block operator is self-adjoint for the alternating companion
form as well. Here this means the displayed bilinear identity; it is not the
Hamiltonian (skew-adjoint) convention. -/
theorem splitWeightedOperator_symplecticSelfAdjoint
    (π : ι → ℝ) (P : Matrix ι ι ℝ) (x y : (ι → ℝ) × (ι → ℝ))
    (hπ : ∀ i, π i ≠ 0) :
    splitWeightedSymplectic π (splitWeightedOperator π P x) y =
      splitWeightedSymplectic π x (splitWeightedOperator π P y) := by
  rcases x with ⟨xp, xm⟩
  rcases y with ⟨yp, ym⟩
  simp only [splitWeightedSymplectic, splitWeightedOperator]
  rw [weightedVectorPairing_mulVec_eq_mulVec_weightedAdjoint π P xp ym hπ]
  have h := weightedVectorPairing_mulVec_eq_mulVec_weightedAdjoint
    π (weightedAdjoint π P) xm yp hπ
  rw [weightedAdjoint_involutive π P hπ] at h
  rw [h]

omit [DecidableEq ι] in
/-- Exchanging the two sheets conjugates the doubled operator to the one with
the weighted-adjoint matrix on the first sheet. -/
theorem splitWeightedSheetSwap_conj
    (π : ι → ℝ) (P : Matrix ι ι ℝ) (x : (ι → ℝ) × (ι → ℝ))
    (hπ : ∀ i, π i ≠ 0) :
    splitWeightedSheetSwap (splitWeightedOperator π P (splitWeightedSheetSwap x)) =
      splitWeightedOperator (π := π) (weightedAdjoint π P) x := by
  rcases x with ⟨xp, xm⟩
  simp only [splitWeightedSheetSwap, splitWeightedOperator]
  rw [weightedAdjoint_involutive π P hπ]

omit [DecidableEq ι] in
/-- Restricting the neutral pairing to the diagonal copy gives the pairing
with the half-sum action of `P` and its weighted adjoint. -/
theorem splitWeightedOperator_diagonal_halfSum
    (π : ι → ℝ) (P : Matrix ι ι ℝ) (u v : ι → ℝ) :
    (1 / 2 : ℝ) * splitWeightedPairing π
        (splitWeightedOperator π P (u, u)) (v, v) =
      weightedVectorPairing π (weightedSymmetrizedAction π P u) v := by
  change (1 / 2 : ℝ) *
      (weightedVectorPairing π (P *ᵥ u) v +
        weightedVectorPairing π (weightedAdjoint π P *ᵥ u) v) =
    weightedVectorPairing π
      ((1 / 2 : ℝ) • (P *ᵥ u + weightedAdjoint π P *ᵥ u)) v
  rw [weightedVectorPairing_smul_left, weightedVectorPairing_add_left, mul_add]

omit [Fintype ι] [DecidableEq ι] in
/-- For a lower-triangular matrix `P` (entries vanish when the column index
is strictly larger), its weighted adjoint has the reverse, upper-triangular
support. -/
theorem weightedAdjoint_lowerTriangular_entry_zero
    [LinearOrder ι] (π : ι → ℝ) (P : Matrix ι ι ℝ)
    (hP : ∀ i j, i < j → P i j = 0) :
    ∀ i j, j < i → weightedAdjoint π P i j = 0 := by
  intro i j hji
  simp [weightedAdjoint, hP j i hji]

end InfoGeometry.Probability
