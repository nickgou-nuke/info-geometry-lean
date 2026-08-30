import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

/-!
# Canonical oriented Pfaffian owner

This file introduces the data-free signed perfect-matching surface used by the
Hestenes--Krein Gauss--Bonnet corridor.

Unlike `PfaffianMatchingExpansionPacket`, no matching family, sign, Pfaffian
amplitude, or determinant identity is supplied as structure data. A perfect
matching is an involutive fixed-point-free partner map on `Fin (2 * m)`.

The Pfaffian sign is the parity of geometric crossings of the canonically
ordered pairs. This is essential: the permutation sign of the partner
involution itself is always `(-1)^m` and therefore cannot encode the oriented
Pfaffian sign.

The hard identities `Pf(A)^2 = det(A)`, congruence covariance, and block-skew
compatibility are not postulated here. They are subsequent theorems to be
proved from this owner by matching/permutation decomposition.
-/

noncomputable section

namespace InfoGeometry.Volume.OrientedPfaffian

open scoped BigOperators

/-- A perfect matching of `2 * m` ordered endpoints. -/
structure PerfectMatching (m : ℕ) where
  partner : Fin (2 * m) → Fin (2 * m)
  involutive : Function.Involutive partner
  fixed_free : ∀ i, partner i ≠ i

noncomputable instance perfectMatchingFintype (m : ℕ) : Fintype (PerfectMatching m) :=
  Fintype.ofFinite _

namespace PerfectMatching

variable {m : ℕ}

@[simp] theorem partner_partner (M : PerfectMatching m) (i : Fin (2 * m)) :
    M.partner (M.partner i) = i :=
  M.involutive i

@[simp] theorem partner_ne_self (M : PerfectMatching m) (i : Fin (2 * m)) :
    M.partner i ≠ i :=
  M.fixed_free i

theorem partner_injective (M : PerfectMatching m) : Function.Injective M.partner :=
  M.involutive.injective

theorem partner_surjective (M : PerfectMatching m) : Function.Surjective M.partner :=
  M.involutive.surjective

def partnerPerm (M : PerfectMatching m) : Equiv.Perm (Fin (2 * m)) :=
  Equiv.ofBijective M.partner ⟨M.partner_injective, M.partner_surjective⟩

@[simp] theorem partnerPerm_apply (M : PerfectMatching m) (i : Fin (2 * m)) :
    M.partnerPerm i = M.partner i :=
  rfl

/-- Smaller endpoint of every matched pair. -/
def leftEndpoints (M : PerfectMatching m) : Finset (Fin (2 * m)) :=
  Finset.univ.filter fun i => i < M.partner i

/-- Larger endpoint of every matched pair. -/
def rightEndpoints (M : PerfectMatching m) : Finset (Fin (2 * m)) :=
  Finset.univ.filter fun i => M.partner i < i

@[simp] theorem mem_leftEndpoints (M : PerfectMatching m) (i : Fin (2 * m)) :
    i ∈ M.leftEndpoints ↔ i < M.partner i := by
  simp [leftEndpoints]

@[simp] theorem mem_rightEndpoints (M : PerfectMatching m) (i : Fin (2 * m)) :
    i ∈ M.rightEndpoints ↔ M.partner i < i := by
  simp [rightEndpoints]

/-- Every endpoint belongs to exactly one orientation of its matched pair. -/
theorem leftEndpoints_union_rightEndpoints (M : PerfectMatching m) :
    M.leftEndpoints ∪ M.rightEndpoints = Finset.univ := by
  ext i
  simp only [Finset.mem_union, mem_leftEndpoints, mem_rightEndpoints, Finset.mem_univ, iff_true]
  exact lt_or_gt_of_ne (M.partner_ne_self i)

/-- The two endpoint orientations are disjoint. -/
theorem leftEndpoints_disjoint_rightEndpoints (M : PerfectMatching m) :
    Disjoint M.leftEndpoints M.rightEndpoints := by
  refine Finset.disjoint_left.2 ?_
  intro i hi hj
  rw [M.mem_leftEndpoints] at hi
  rw [M.mem_rightEndpoints] at hj
  exact (lt_asymm hi hj) hj

/-- `partner` bijects left endpoints with right endpoints. -/
theorem leftEndpoints_card_eq_rightEndpoints_card (M : PerfectMatching m) :
    M.leftEndpoints.card = M.rightEndpoints.card := by
  refine Finset.card_bij (fun i _ => M.partner i) ?_ ?_ ?_
  · intro i hi
    rw [M.mem_leftEndpoints] at hi
    rw [M.mem_rightEndpoints]
    simpa using hi
  · intro i₁ h₁ i₂ h₂ h
    exact M.partner_injective h
  · intro j hj
    refine ⟨M.partner j, ?_, ?_⟩
    · rw [M.mem_rightEndpoints] at hj
      rw [M.mem_leftEndpoints]
      simpa using hj
    · exact M.partner_partner j

/-- The left and right endpoint counts sum to the ambient cardinality `2*m`. -/
theorem leftEndpoints_card_add_rightEndpoints_card (M : PerfectMatching m) :
    M.leftEndpoints.card + M.rightEndpoints.card = 2 * m := by
  have hdisj := M.leftEndpoints_disjoint_rightEndpoints
  have hcard := Finset.card_union_of_disjoint hdisj
  rw [M.leftEndpoints_union_rightEndpoints] at hcard
  simpa using hcard

/-- A fixed-point-free involution on `Fin (2*m)` has exactly `m` unordered pairs. -/
theorem leftEndpoints_card (M : PerfectMatching m) :
    M.leftEndpoints.card = m := by
  have hsum := M.leftEndpoints_card_add_rightEndpoints_card
  have heq := M.leftEndpoints_card_eq_rightEndpoints_card
  omega

/-- Canonical product of matrix entries along the matched pairs. -/
def matchingWeight
    (A : Matrix (Fin (2 * m)) (Fin (2 * m)) ℝ)
    (M : PerfectMatching m) : ℝ :=
  ∏ i ∈ M.leftEndpoints, A i (M.partner i)

/-- Two matched pairs cross in the natural order if
`i < j < partner i < partner j`. -/
def crossingPairs (M : PerfectMatching m) : Finset (Fin (2 * m) × Fin (2 * m)) :=
  (M.leftEndpoints.product M.leftEndpoints).filter fun p =>
    p.1 < p.2 ∧ p.2 < M.partner p.1 ∧ M.partner p.1 < M.partner p.2

def crossingNumber (M : PerfectMatching m) : ℕ :=
  M.crossingPairs.card

def matchingSign (M : PerfectMatching m) : ℝ :=
  (-1 : ℝ) ^ M.crossingNumber

@[simp] theorem matchingSign_sq (M : PerfectMatching m) :
    M.matchingSign ^ 2 = 1 := by
  simp [matchingSign, pow_two]

end PerfectMatching

/-- Canonical signed oriented Pfaffian by perfect-matchings. -/
def orientedPfaffian
    (m : ℕ)
    (A : Matrix (Fin (2 * m)) (Fin (2 * m)) ℝ) : ℝ :=
  ∑ M : PerfectMatching m, M.matchingSign * M.matchingWeight A

@[simp] theorem orientedPfaffian_eq_matchingSum
    (m : ℕ)
    (A : Matrix (Fin (2 * m)) (Fin (2 * m)) ℝ) :
    orientedPfaffian m A =
      ∑ M : PerfectMatching m, M.matchingSign * M.matchingWeight A :=
  rfl

def IsSkew
    {m : ℕ}
    (A : Matrix (Fin (2 * m)) (Fin (2 * m)) ℝ) : Prop :=
  ∀ i j, A i j = -A j i

theorem IsSkew.diagonal_zero
    {m : ℕ}
    {A : Matrix (Fin (2 * m)) (Fin (2 * m)) ℝ}
    (hA : IsSkew A)
    (i : Fin (2 * m)) :
    A i i = 0 := by
  have h := hA i i
  linarith

end InfoGeometry.Volume.OrientedPfaffian
