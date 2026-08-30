import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
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
proved from this owner.
-/

noncomputable section

namespace InfoGeometry.Volume.OrientedPfaffian

open scoped BigOperators

/-- A perfect matching of `2 * m` ordered endpoints.

`partner` is required only to be an involution without fixed points. Its
bijection property is a theorem, not additional structure data. -/
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

/-- The partner map of a perfect matching is injective. -/
theorem partner_injective (M : PerfectMatching m) : Function.Injective M.partner :=
  M.involutive.injective

/-- The partner map of a perfect matching is surjective. -/
theorem partner_surjective (M : PerfectMatching m) : Function.Surjective M.partner :=
  M.involutive.surjective

/-- The partner map bundled as the permutation it canonically determines. -/
def partnerPerm (M : PerfectMatching m) : Equiv.Perm (Fin (2 * m)) :=
  Equiv.ofBijective M.partner ⟨M.partner_injective, M.partner_surjective⟩

@[simp] theorem partnerPerm_apply (M : PerfectMatching m) (i : Fin (2 * m)) :
    M.partnerPerm i = M.partner i :=
  rfl

/-- Canonical set of left endpoints: exactly the smaller endpoint of each
matched pair is retained. -/
def leftEndpoints (M : PerfectMatching m) : Finset (Fin (2 * m)) :=
  Finset.univ.filter fun i => i < M.partner i

@[simp] theorem mem_leftEndpoints (M : PerfectMatching m) (i : Fin (2 * m)) :
    i ∈ M.leftEndpoints ↔ i < M.partner i := by
  simp [leftEndpoints]

/-- Canonical product of matrix entries along the matched pairs. -/
def matchingWeight
    (A : Matrix (Fin (2 * m)) (Fin (2 * m)) ℝ)
    (M : PerfectMatching m) : ℝ :=
  ∏ i ∈ M.leftEndpoints, A i (M.partner i)

/-- Two canonical matched pairs cross in the natural linear order if their
endpoints occur as `i < j < partner i < partner j`. -/
def crossingPairs (M : PerfectMatching m) : Finset (Fin (2 * m) × Fin (2 * m)) :=
  (M.leftEndpoints.product M.leftEndpoints).filter fun p =>
    p.1 < p.2 ∧ p.2 < M.partner p.1 ∧ M.partner p.1 < M.partner p.2

/-- Number of crossings in the canonical chord diagram of a perfect matching. -/
def crossingNumber (M : PerfectMatching m) : ℕ :=
  M.crossingPairs.card

/-- Canonical oriented Pfaffian sign of a perfect matching.

This is the crossing parity `(-1)^(crossingNumber M)`, not the sign of the
fixed-point-free involution `partnerPerm`. -/
def matchingSign (M : PerfectMatching m) : ℝ :=
  (-1 : ℝ) ^ M.crossingNumber

@[simp] theorem matchingSign_sq (M : PerfectMatching m) :
    M.matchingSign ^ 2 = 1 := by
  simp [matchingSign, pow_two]

end PerfectMatching

/-- The canonical signed oriented Pfaffian on a real `2m × 2m` matrix.

The definition is the signed perfect-matching expansion. For skew matrices it
is the usual oriented Pfaffian. It is defined on all matrices so skewness
remains an explicit theorem hypothesis rather than hidden structure data. -/
def orientedPfaffian
    (m : ℕ)
    (A : Matrix (Fin (2 * m)) (Fin (2 * m)) ℝ) : ℝ :=
  ∑ M : PerfectMatching m, M.matchingSign * M.matchingWeight A

/-- Exact canonical perfect-matching expansion of the oriented Pfaffian. -/
theorem orientedPfaffian_eq_matchingSum
    (m : ℕ)
    (A : Matrix (Fin (2 * m)) (Fin (2 * m)) ℝ) :
    orientedPfaffian m A =
      ∑ M : PerfectMatching m, M.matchingSign * M.matchingWeight A :=
  rfl

/-- Skewness predicate used by the characteristic-form corridor. -/
def IsSkew
    {m : ℕ}
    (A : Matrix (Fin (2 * m)) (Fin (2 * m)) ℝ) : Prop :=
  ∀ i j, A i j = -A j i

/-- Skew matrices have zero diagonal. -/
theorem IsSkew.diagonal_zero
    {m : ℕ}
    {A : Matrix (Fin (2 * m)) (Fin (2 * m)) ℝ}
    (hA : IsSkew A)
    (i : Fin (2 * m)) :
    A i i = 0 := by
  have h := hA i i
  linarith

end InfoGeometry.Volume.OrientedPfaffian
