/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.Drazin

/-!
# Rose Drazin Polynomial

Finite theorem layer extracted from Nicholas J. Rose, "A Note On Computing the
Drazin Inverse" (Linear Algebra and its Applications 15, 1976, 95--98).

Rose shows how to compute the Drazin inverse as a polynomial in `A` using only
the characteristic polynomial.  This file formalizes the theorem-safe algebra
behind Example 1:

`c(λ) = λ²(λ² + 5λ + 1)`.

For the nonsingular block `C`, the equation `C² + 5C + 1 = 0` gives
`C⁻¹ = -C - 5`; for the nilpotent block `N² = 0`, the Drazin inverse kills the
nilpotent lane.  The block pair `(N, C)` is modeled by the product ring.

#### BUCKET 1: CLOSED FINITE THEOREMS
The inverse-power identities for `λ² + 5λ + 1`, and the Drazin equations for
the exact block model of Rose Example 1.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES
The Drazin equations depend only on the explicit premises `N² = 0` and
`C² + 5C + 1 = 0`.

#### BUCKET 3: OPEN CLOSURE DEBT
The all-degree characteristic-polynomial algorithm, Jordan decomposition,
minimal-polynomial reduction, and eigenvalue classification are not asserted
in Lean here.
-/

namespace InfoGeometry.Canonical.RoseDrazinPolynomial

noncomputable section

variable {R : Type*} [Ring R]

/-- Polynomial-form candidate for an index-`k` Drazin inverse.

The hypotheses needed for it to be a Drazin inverse are supplied by the
commutation `a * p = p * a` and the factorization `a^(k+1) * p = a^k`. -/
def polynomialDrazinCandidate (a p : R) (k : ℕ) : R :=
  a ^ k * p ^ (k + 1)

/-- The polynomial candidate is a Drazin inverse under the exact factorization
and commutation hypotheses; no commutativity of the ambient ring is assumed. -/
theorem isDrazinInverse_polynomialDrazinCandidate
    (a p : R) (k : ℕ) (hcomm : a * p = p * a)
    (hpow : a ^ (k + 1) * p = a ^ k) :
    InfoGeometry.Canonical.Drazin.IsDrazinInverse a
      (polynomialDrazinCandidate a p k) k := by
  let q : R := a * p
  have hc : Commute a p := hcomm
  have hqpow : q ^ k = a ^ k * p ^ k := by
    dsimp [q]
    exact hc.mul_pow k
  have hq : a ^ k * q = a ^ k := by
    dsimp [q]
    calc
      a ^ k * (a * p) = (a ^ k * a) * p := by noncomm_ring
      _ = a ^ (k + 1) * p := by rw [pow_succ]
      _ = a ^ k := hpow
  have hq_iter : ∀ n : ℕ, a ^ k * q ^ n = a ^ k := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        calc
          a ^ k * q ^ (n + 1) = (a ^ k * q ^ n) * q := by rw [pow_succ]; rw [mul_assoc]
          _ = a ^ k * q := by rw [ih]
          _ = a ^ k := hq
  have hqp : p * q ^ k = polynomialDrazinCandidate a p k := by
    rw [hqpow]
    dsimp [polynomialDrazinCandidate]
    calc
      p * (a ^ k * p ^ k) = (p * a ^ k) * p ^ k := by noncomm_ring
      _ = (a ^ k * p) * p ^ k := by rw [(hc.symm.pow_right k).eq]
      _ = a ^ k * (p * p ^ k) := by noncomm_ring
      _ = a ^ k * p ^ (k + 1) := by rw [← pow_succ']
  have hqpow_stable : q ^ k * q = q ^ k := by
    rw [hqpow]
    dsimp [q]
    calc
      a ^ k * p ^ k * (a * p) = a ^ k * a * (p ^ k * p) := by
        calc
          a ^ k * p ^ k * (a * p) = a ^ k * (p ^ k * a) * p := by noncomm_ring
          _ = a ^ k * (a * p ^ k) * p := by rw [(hc.symm.pow_left k).eq]
          _ = a ^ k * a * (p ^ k * p) := by noncomm_ring
      _ = a ^ (k + 1) * p ^ (k + 1) := by
        calc
          a ^ k * a * (p ^ k * p) = (a ^ k * a) * (p ^ k * p) := by noncomm_ring
          _ = a ^ (k + 1) * p ^ (k + 1) := by rw [pow_succ, pow_succ]
      _ = a ^ (k + 1) * (p * p ^ k) := by rw [pow_succ' p k]
      _ = a ^ k * p ^ k := by
        rw [← mul_assoc, hpow]
  have hqpow_stable_iter : ∀ n : ℕ, q ^ k * q ^ n = q ^ k := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        calc
          q ^ k * q ^ (n + 1) = q ^ k * (q ^ n * q) := by rw [pow_succ]
          _ = (q ^ k * q ^ n) * q := by rw [mul_assoc]
          _ = q ^ k * q := by rw [ih]
          _ = q ^ k := hqpow_stable
  have hqpow_idem : q ^ k * q ^ k = q ^ k := hqpow_stable_iter k
  have hcomm_aq : a * q ^ k = q ^ k * a := by
    rw [hqpow]
    calc
      a * (a ^ k * p ^ k) = (a * a ^ k) * p ^ k := by noncomm_ring
      _ = a ^ (k + 1) * p ^ k := by rw [pow_succ']
      _ = a ^ k * p ^ k * a := by
        calc
          a ^ (k + 1) * p ^ k = (a ^ k * a) * p ^ k := by rw [pow_succ]
          _ = a ^ k * (a * p ^ k) := by noncomm_ring
          _ = a ^ k * (p ^ k * a) := by rw [(hc.pow_right k).eq]
          _ = a ^ k * p ^ k * a := by noncomm_ring
  have hq_comm_p : q ^ k * p = p * q ^ k := by
    have hqp0 : Commute q p := hc.mul_left (Commute.refl p)
    exact (hqp0.pow_left k).eq
  have hq_left_stable : q * q ^ k = q ^ k := by
    calc
      q * q ^ k = q ^ k * q := by
        simpa [pow_one] using (pow_mul_comm q 1 k)
      _ = q ^ k := hqpow_stable
  have hcomm_apoly : a * (p * q ^ k) = (p * q ^ k) * a := by
    calc
      a * (p * q ^ k) = (a * p) * q ^ k := by noncomm_ring
      _ = (p * a) * q ^ k := by rw [hcomm]
      _ = p * (q ^ k * a) := by rw [mul_assoc, ← hcomm_aq]
      _ = p * q ^ k * a := by noncomm_ring
  have hidem : (p * q ^ k) * a * (p * q ^ k) = p * q ^ k := by
    calc
      (p * q ^ k) * a * (p * q ^ k) = p * (q ^ k * a * p) * q ^ k := by noncomm_ring
      _ = p * (a * q ^ k * p) * q ^ k := by rw [hcomm_aq]
      _ = p * (a * (q ^ k * p)) * q ^ k := by congr 2 <;> noncomm_ring
      _ = p * (a * (p * q ^ k)) * q ^ k := by rw [hq_comm_p]
      _ = p * ((a * p) * q ^ k) * q ^ k := by noncomm_ring
      _ = p * (q * q ^ k) * q ^ k := by dsimp [q]
      _ = p * q ^ k := by
        rw [hq_left_stable]
        calc
          p * q ^ k * q ^ k = p * (q ^ k * q ^ k) := by noncomm_ring
          _ = p * q ^ k := by rw [hqpow_idem]
  have hpower : a ^ (k + 1) * (p * q ^ k) = a ^ k := by
    calc
      a ^ (k + 1) * (p * q ^ k) = a ^ k * (q * q ^ k) := by
        calc
          a ^ (k + 1) * (p * q ^ k) = (a ^ k * a) * (p * q ^ k) := by rw [pow_succ]
          _ = a ^ k * ((a * p) * q ^ k) := by noncomm_ring
          _ = a ^ k * (q * q ^ k) := by rfl
      _ = a ^ k := by rw [hq_left_stable, hq_iter k]
  have hD : InfoGeometry.Canonical.Drazin.IsDrazinInverse a (p * q ^ k) k :=
    InfoGeometry.Canonical.Drazin.IsDrazinInverse.mk hcomm_apoly hidem hpower
  simpa [hqp] using hD

/-- The regular projector of the polynomial candidate is `a^k * p^k`. -/
theorem polynomialDrazinCandidate_projection_eq
    (a p : R) (k : ℕ)
    (hpow : a ^ (k + 1) * p = a ^ k) :
    InfoGeometry.Canonical.Drazin.IsDrazinInverse.projection a
      (polynomialDrazinCandidate a p k) = a ^ k * p ^ k := by
  unfold InfoGeometry.Canonical.Drazin.IsDrazinInverse.projection
  dsimp [polynomialDrazinCandidate]
  calc
    a * (a ^ k * p ^ (k + 1)) = a ^ (k + 1) * p ^ (k + 1) := by
      calc
        a * (a ^ k * p ^ (k + 1)) = (a * a ^ k) * p ^ (k + 1) := by rw [← mul_assoc]
        _ = a ^ (k + 1) * p ^ (k + 1) := by rw [pow_succ' a k]
    _ = (a ^ (k + 1) * p) * p ^ k := by
      rw [pow_succ' p k, ← mul_assoc]
    _ = a ^ k * p ^ k := by rw [hpow]

/-- Rose Example 1 inverse candidate for the nonsingular block. -/
def roseExampleOneInverseBlock (c : R) : R :=
  -c - 5

/-- From `c² + 5c + 1 = 0`, Rose obtains `c⁻¹ = -c - 5`. -/
theorem roseExampleOne_right_inverse
    (c : R)
    (hc : c ^ 2 + 5 * c + 1 = 0) :
    c * roseExampleOneInverseBlock c = 1 := by
  unfold roseExampleOneInverseBlock
  have htail : c ^ 2 + 5 * c = -1 := by
    calc
      c ^ 2 + 5 * c = (c ^ 2 + 5 * c + 1) - 1 := by noncomm_ring
      _ = 0 - 1 := by rw [hc]
      _ = -1 := by noncomm_ring
  calc
    c * (-c - 5) = -(c ^ 2 + 5 * c) := by noncomm_ring
    _ = -(-1) := by rw [htail]
    _ = 1 := neg_neg 1

/-- Over any ring, the same candidate is also a left inverse. -/
theorem roseExampleOne_left_inverse
    (c : R)
    (hc : c ^ 2 + 5 * c + 1 = 0) :
    roseExampleOneInverseBlock c * c = 1 := by
  unfold roseExampleOneInverseBlock
  have htail : c ^ 2 + 5 * c = -1 := by
    calc
      c ^ 2 + 5 * c = (c ^ 2 + 5 * c + 1) - 1 := by noncomm_ring
      _ = 0 - 1 := by rw [hc]
      _ = -1 := by noncomm_ring
  calc
    (-c - 5) * c = -(c ^ 2 + 5 * c) := by noncomm_ring
    _ = -(-1) := by rw [htail]
    _ = 1 := neg_neg 1

/--
Rose's recursive inverse-power computation in Example 1 reaches
`c³ * (-24c - 115) = 1`.
-/
theorem roseExampleOne_inversePower_three
    {R : Type} [CommRing R]
    (c : R)
    (hc : c ^ 2 + 5 * c + 1 = 0) :
    c ^ 3 * (-24 * c - 115) = 1 := by
  linear_combination (-24 * c ^ 2 + 5 * c - 1) * hc

/-- Block model for Rose Example 1: nilpotent block and nonsingular block. -/
def roseExampleOneBlock (n c : R) : R × R :=
  (n, c)

/-- Drazin candidate for the Rose Example 1 block model. -/
def roseExampleOneDrazinBlock (c : R) : R × R :=
  (0, roseExampleOneInverseBlock c)

/-- Rose Example 1 satisfies the index-two Drazin equations in the block model. -/
theorem roseExampleOne_drazin_equations
    (n c : R)
    (hn : n ^ 2 = 0)
    (hc : c ^ 2 + 5 * c + 1 = 0) :
    let A := roseExampleOneBlock n c
    let X := roseExampleOneDrazinBlock c
    A * X = X * A ∧ X * A * X = X ∧ A ^ 3 * X = A ^ 2 := by
  intro A X
  constructor
  · ext
    · simp [A, X, roseExampleOneBlock, roseExampleOneDrazinBlock,
        roseExampleOneInverseBlock]
    · simp [A, X, roseExampleOneBlock, roseExampleOneDrazinBlock,
        roseExampleOneInverseBlock]
      noncomm_ring
  constructor
  · ext
    · simp [A, X, roseExampleOneBlock, roseExampleOneDrazinBlock]
    · simp [A, X, roseExampleOneBlock, roseExampleOneDrazinBlock]
      calc
        roseExampleOneInverseBlock c * c * roseExampleOneInverseBlock c
            = 1 * roseExampleOneInverseBlock c := by rw [roseExampleOne_left_inverse c hc]
        _ = roseExampleOneInverseBlock c := by noncomm_ring
  · ext
    · simp [A, X, roseExampleOneBlock, roseExampleOneDrazinBlock]
      rw [hn]
    · simp [A, X, roseExampleOneBlock, roseExampleOneDrazinBlock]
      calc
        c ^ 3 * roseExampleOneInverseBlock c = c ^ 2 * (c * roseExampleOneInverseBlock c) := by noncomm_ring
        _ = c ^ 2 * 1 := by rw [roseExampleOne_right_inverse c hc]
        _ = c ^ 2 := by noncomm_ring

end

end InfoGeometry.Canonical.RoseDrazinPolynomial
