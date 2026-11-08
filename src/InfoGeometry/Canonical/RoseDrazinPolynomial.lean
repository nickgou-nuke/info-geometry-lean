/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.Drazin

/-!
# Rose Drazin Polynomial and Cline Non-Commutative Drazin Shift

Finite and general ring-level theorem layer extracted from Nicholas J. Rose,
"A Note On Computing the Drazin Inverse" (Linear Algebra and its Applications 15,
1976, 95--98) and R. E. Cline, "An application of representations for the
generalized inverse of a matrix" (MRC Technical Summary Report 592, 1965).

1. **Rose Example 1 Block Model (`Section 1`)**:
   Formalizes the theorem-safe algebra behind Example 1, `c(λ) = λ²(λ² + 5λ + 1)`.
   For the nonsingular block `C`, `C² + 5C + 1 = 0` gives `C⁻¹ = -C - 5`; for the
   nilpotent block `N² = 0`, the Drazin inverse kills the nilpotent lane.

2. **All-Degree Polynomial / Herstein–Souriau–Frame Drazin Construction (`Section 2`)**:
   Over any associative unital ring `[Ring R]`, if `a, p ∈ R` commute (`a * p = p * a`)
   and satisfy the index-`k` factorization `a ^ (k + 1) * p = a ^ k` (taken as a
   hypothesis), then `b := a ^ k * p ^ (k + 1)` is an index-`k` Drazin inverse of `a`
   (`IsDrazinInverse a (a ^ k * p ^ (k + 1)) k`), with spectral projector
   `P_D = a ^ k * p ^ k`.  Uniqueness is the separate theorem
   `IsDrazinInverse.unique_of_indices`.

3. **Cline's Non-Commutative Drazin Shift Theorem (`Section 3`)**:
   Over any associative unital ring `[Ring R]`, if `a * b` admits a Drazin inverse `d`
   at index `k` (`IsDrazinInverse (a * b) d k`), then the reversed product `b * a`
   admits the Drazin inverse `clineDrazinShift a b d := b * d ^ 2 * a` at index `k + 1`,
   with spectral projector `P_{ba} = b * d * a`, complementary projector `1 - b * d * a`,
   and Fitting regular core `b * (a * b) * d * a`.

#### BUCKET 1: CLOSED FINITE & RING-LEVEL THEOREMS
* Inverse-power identities and block Drazin equations for Rose Example 1.
* All-degree commuting/polynomial Drazin construction (`isDrazinInverse_polynomialDrazinCandidate`
  and `isDrazinInverse_of_polynomial_eval₂`).
* Cline's non-commutative Drazin shift theorem (`isDrazinInverse_clineDrazinShift`).

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES
The Drazin equations depend only on the explicit algebraic premises (`N² = 0` and
`C² + 5C + 1 = 0` in Section 1; `a * p = p * a` and `a ^ (k + 1) * p = a ^ k` in
Section 2; `IsDrazinInverse (a * b) d k` in Section 3).

#### BUCKET 3: OPEN (NOT FORMALIZED HERE)
* Deriving the factorization `a ^ (k + 1) * q.eval₂ φ a = a ^ k` from a characteristic
  or minimal polynomial of `a` (Rose's algorithm proper: root multiplicity `k` at `0`,
  coprime cofactor, Bézout inversion) is not formalized; it is a hypothesis of
  Section 2.
-/

namespace InfoGeometry.Canonical.RoseDrazinPolynomial

noncomputable section

variable {R : Type} [Field R]

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
    rw [← sub_eq_zero]
    linear_combination hc
  calc
    c * (-c - 5) = -(c ^ 2 + 5 * c) := by ring
    _ = -(-1) := by rw [htail]
    _ = 1 := by ring

/-- In a field, the same candidate is also a left inverse. -/
theorem roseExampleOne_left_inverse
    (c : R)
    (hc : c ^ 2 + 5 * c + 1 = 0) :
    roseExampleOneInverseBlock c * c = 1 := by
  rw [mul_comm]
  exact roseExampleOne_right_inverse c hc

/--
Rose's recursive inverse-power computation in Example 1 reaches
`c³ * (-24c - 115) = 1`.
-/
theorem roseExampleOne_inversePower_three
    (c : R)
    (hc : c ^ 2 + 5 * c + 1 = 0) :
    c ^ 3 * (-24 * c - 115) = 1 := by
  have hc2 : c ^ 2 = -5 * c - 1 := by
    rw [← sub_eq_zero]
    linear_combination hc
  have hc3 : c ^ 3 = 24 * c + 5 := by
    calc
      c ^ 3 = c * c ^ 2 := by ring
      _ = c * (-5 * c - 1) := by rw [hc2]
      _ = -5 * c ^ 2 - c := by ring
      _ = -5 * (-5 * c - 1) - c := by rw [hc2]
      _ = 24 * c + 5 := by ring
  calc
    c ^ 3 * (-24 * c - 115) = (24 * c + 5) * (-24 * c - 115) := by rw [hc3]
    _ = -576 * c ^ 2 - 2880 * c - 575 := by ring
    _ = -576 * (-5 * c - 1) - 2880 * c - 575 := by rw [hc2]
    _ = 1 := by ring

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
      ring
  constructor
  · ext
    · simp [A, X, roseExampleOneBlock, roseExampleOneDrazinBlock]
    · simp [A, X, roseExampleOneBlock, roseExampleOneDrazinBlock]
      calc
        roseExampleOneInverseBlock c * c * roseExampleOneInverseBlock c
            = (c * roseExampleOneInverseBlock c) * roseExampleOneInverseBlock c := by ring
        _ = 1 * roseExampleOneInverseBlock c := by rw [roseExampleOne_right_inverse c hc]
        _ = roseExampleOneInverseBlock c := by ring
  · ext
    · simp [A, X, roseExampleOneBlock, roseExampleOneDrazinBlock]
      rw [hn]
    · simp [A, X, roseExampleOneBlock, roseExampleOneDrazinBlock]
      calc
        c ^ 3 * roseExampleOneInverseBlock c = c ^ 2 * (c * roseExampleOneInverseBlock c) := by ring
        _ = c ^ 2 * 1 := by rw [roseExampleOne_right_inverse c hc]
        _ = c ^ 2 := by ring

/-! ## Section 2: All-Degree Polynomial / Herstein–Souriau–Frame Drazin Construction -/

section AllDegreePolynomialDrazin

open InfoGeometry.Canonical.Drazin

variable {R : Type*} [Ring R]

/-- All-degree polynomial / commuting-factor Drazin candidate:
given `a ^ (k + 1) * p = a ^ k` with `a * p = p * a`, the index-`k` Drazin inverse of `a`
is `a ^ k * p ^ (k + 1)`. -/
def polynomialDrazinCandidate (a p : R) (k : ℕ) : R :=
  a ^ k * p ^ (k + 1)

/-- Recursive power-absorption law: if `a * p = p * a` and `a ^ (k + 1) * p = a ^ k`,
then `a ^ k * (a ^ m * p ^ m) = a ^ k` for every `m : ℕ`. -/
theorem polynomial_power_absorption
    (a p : R) (k : ℕ)
    (hcomm : a * p = p * a)
    (hpow : a ^ (k + 1) * p = a ^ k) :
    ∀ m : ℕ, a ^ k * (a ^ m * p ^ m) = a ^ k := by
  have hc : Commute a p := hcomm
  intro m
  induction m with
  | zero =>
      simp
  | succ m ih =>
      have hcomm_m : a ^ m * p = p * a ^ m := (hc.pow_left m).eq
      calc
        a ^ k * (a ^ (m + 1) * p ^ (m + 1))
            = a ^ k * ((a * a ^ m) * (p * p ^ m)) := by
                rw [pow_succ', pow_succ']
        _ = (a ^ k * a) * (a ^ m * p) * p ^ m := by noncomm_ring
        _ = a ^ (k + 1) * (p * a ^ m) * p ^ m := by
              rw [← pow_succ, hcomm_m]
        _ = (a ^ (k + 1) * p) * (a ^ m * p ^ m) := by noncomm_ring
        _ = a ^ k * (a ^ m * p ^ m) := by rw [hpow]
        _ = a ^ k := ih

/-- `polynomialDrazinCandidate a p k = a ^ k * p ^ (k + 1)` commutes with `a` whenever `a * p = p * a`. -/
theorem commute_polynomialDrazinCandidate
    (a p : R) (k : ℕ)
    (hcomm : a * p = p * a) :
    a * polynomialDrazinCandidate a p k = polynomialDrazinCandidate a p k * a := by
  have hc : Commute a p := hcomm
  exact ((Commute.refl a).pow_right k |>.mul_right (hc.pow_right (k + 1))).eq

/-- **All-Degree Commuting/Polynomial Drazin Theorem**:
In any associative ring `R`, if `a` and `p` commute (`a * p = p * a`) and satisfy
`a ^ (k + 1) * p = a ^ k`, then `polynomialDrazinCandidate a p k := a ^ k * p ^ (k + 1)`
is the canonical Drazin inverse of `a` at index `k`. -/
theorem isDrazinInverse_polynomialDrazinCandidate
    (a p : R) (k : ℕ)
    (hcomm : a * p = p * a)
    (hpow : a ^ (k + 1) * p = a ^ k) :
    IsDrazinInverse a (polynomialDrazinCandidate a p k) k := by
  have hc : Commute a p := hcomm
  have habs_k1 : a ^ k * (a ^ (k + 1) * p ^ (k + 1)) = a ^ k :=
    polynomial_power_absorption a p k hcomm hpow (k + 1)
  have h_pow_drazin : a ^ (k + 1) * polynomialDrazinCandidate a p k = a ^ k := by
    unfold polynomialDrazinCandidate
    have ha_comm : a ^ (k + 1) * a ^ k = a ^ k * a ^ (k + 1) := by
      rw [← pow_add, ← pow_add, Nat.add_comm]
    calc
      a ^ (k + 1) * (a ^ k * p ^ (k + 1))
          = (a ^ (k + 1) * a ^ k) * p ^ (k + 1) := by noncomm_ring
      _ = (a ^ k * a ^ (k + 1)) * p ^ (k + 1) := by rw [ha_comm]
      _ = a ^ k * (a ^ (k + 1) * p ^ (k + 1)) := by noncomm_ring
      _ = a ^ k := habs_k1
  have h_idem :
      polynomialDrazinCandidate a p k * a * polynomialDrazinCandidate a p k =
        polynomialDrazinCandidate a p k := by
    have h_pow_raw : a ^ (k + 1) * (a ^ k * p ^ (k + 1)) = a ^ k := h_pow_drazin
    unfold polynomialDrazinCandidate
    have hp_comm : p ^ (k + 1) * a = a * p ^ (k + 1) := (hc.symm.pow_left (k + 1)).eq
    have hp_comm_ak : p ^ (k + 1) * a ^ k = a ^ k * p ^ (k + 1) :=
      (hc.symm.pow_pow (k + 1) k).eq
    calc
      (a ^ k * p ^ (k + 1)) * a * (a ^ k * p ^ (k + 1))
          = a ^ k * (p ^ (k + 1) * a) * a ^ k * p ^ (k + 1) := by noncomm_ring
      _ = a ^ k * (a * p ^ (k + 1)) * a ^ k * p ^ (k + 1) := by rw [hp_comm]
      _ = a ^ k * a * (p ^ (k + 1) * a ^ k) * p ^ (k + 1) := by noncomm_ring
      _ = (a ^ k * a) * (a ^ k * p ^ (k + 1)) * p ^ (k + 1) := by
            rw [hp_comm_ak]
      _ = (a ^ (k + 1) * (a ^ k * p ^ (k + 1))) * p ^ (k + 1) := by
            rw [← pow_succ a k]
      _ = a ^ k * p ^ (k + 1) := by
            rw [h_pow_raw]
  exact ⟨commute_polynomialDrazinCandidate a p k hcomm, h_idem, h_pow_drazin⟩

/-- The spectral projector `a * b` of `polynomialDrazinCandidate a p k` equals `a ^ k * p ^ k`. -/
theorem polynomialDrazinCandidate_projection_eq
    (a p : R) (k : ℕ)
    (hpow : a ^ (k + 1) * p = a ^ k) :
    IsDrazinInverse.projection a (polynomialDrazinCandidate a p k) = a ^ k * p ^ k := by
  unfold IsDrazinInverse.projection polynomialDrazinCandidate
  calc
    a * (a ^ k * p ^ (k + 1))
        = (a * a ^ k) * (p * p ^ k) := by
            rw [pow_succ' p k]
            noncomm_ring
    _ = (a ^ (k + 1) * p) * p ^ k := by
          rw [← pow_succ' a k]
          noncomm_ring
    _ = a ^ k * p ^ k := by rw [hpow]

/-- Any polynomial `q : Polynomial S` evaluated at `a` via a ring homomorphism `φ : S →+* R`
whose range commutes with `a` automatically commutes with `a`. -/
theorem commute_eval₂_of_commute_range
    {S : Type*} [Semiring S] (φ : S →+* R) (a : R)
    (hφ : ∀ s : S, a * φ s = φ s * a) (q : Polynomial S) :
    a * q.eval₂ φ a = q.eval₂ φ a * a := by
  induction q using Polynomial.induction_on' with
  | add p₁ p₂ ih₁ ih₂ =>
      rw [Polynomial.eval₂_add]
      have hc₁ : Commute a (p₁.eval₂ φ a) := ih₁
      have hc₂ : Commute a (p₂.eval₂ φ a) := ih₂
      exact (hc₁.add_right hc₂).eq
  | monomial n s =>
      rw [Polynomial.eval₂_monomial]
      have hcs : Commute a (φ s) := hφ s
      have hca : Commute a (a ^ n) := (Commute.refl a).pow_right n
      exact (hcs.mul_right hca).eq

/-- **All-Degree Polynomial Evaluation Drazin Theorem**:
If `q : Polynomial S` satisfies `a ^ (k + 1) * q.eval₂ φ a = a ^ k` where the scalar image
of `φ : S →+* R` commutes with `a`, then `polynomialDrazinCandidate a (q.eval₂ φ a) k`
is an index-`k` Drazin inverse of `a` (unique by `IsDrazinInverse.unique_of_indices`).
The factorization `hpow` is a hypothesis; deriving it from a characteristic polynomial
is not formalized. -/
theorem isDrazinInverse_of_polynomial_eval₂
    {S : Type*} [Semiring S] (φ : S →+* R) (a : R) (k : ℕ)
    (hφ : ∀ s : S, a * φ s = φ s * a)
    (q : Polynomial S)
    (hpow : a ^ (k + 1) * q.eval₂ φ a = a ^ k) :
    IsDrazinInverse a (polynomialDrazinCandidate a (q.eval₂ φ a) k) k :=
  isDrazinInverse_polynomialDrazinCandidate a (q.eval₂ φ a) k
    (commute_eval₂_of_commute_range φ a hφ q) hpow

end AllDegreePolynomialDrazin

/-! ## Section 3: Cline's Non-Commutative Drazin Shift Theorem (`ab → ba`) -/

section ClineDrazinShift

open InfoGeometry.Canonical.Drazin

variable {R : Type*} [Ring R]

/-- **Cline's shifted Drazin inverse candidate**:
if `d` is the Drazin inverse of `a * b`, then `b * d ^ 2 * a` is the Drazin inverse of `b * a`. -/
def clineDrazinShift (a b d : R) : R :=
  b * d ^ 2 * a

/-- Associative shift identity for powers of reversed products:
`(b * a) ^ (n + 1) = b * (a * b) ^ n * a`. -/
theorem mul_pow_shift (a b : R) :
    ∀ n : ℕ, (b * a) ^ (n + 1) = b * (a * b) ^ n * a := by
  intro n
  induction n with
  | zero =>
      simp
  | succ n ih =>
      calc
        (b * a) ^ (n + 2) = (b * a) ^ (n + 1) * (b * a) := by rw [pow_succ]
        _ = (b * (a * b) ^ n * a) * (b * a) := by rw [ih]
        _ = b * ((a * b) ^ n * (a * b)) * a := by noncomm_ring
        _ = b * (a * b) ^ (n + 1) * a := by rw [← pow_succ]

/-- In any Drazin pair `IsDrazinInverse m d k`, `m * d ^ 2 = d`. -/
theorem mul_drazin_sq_eq {m d : R} {k : ℕ}
    (h : IsDrazinInverse m d k) :
    m * d ^ 2 = d := by
  calc
    m * d ^ 2 = (m * d) * d := by rw [sq]; noncomm_ring
    _ = (d * m) * d := by rw [h.comm]
    _ = d := h.idempotent

/-- In any Drazin pair `IsDrazinInverse m d k`, `d ^ 2 * m = d`. -/
theorem drazin_sq_mul_eq {m d : R} {k : ℕ}
    (h : IsDrazinInverse m d k) :
    d ^ 2 * m = d := by
  calc
    d ^ 2 * m = d * (d * m) := by rw [sq]; noncomm_ring
    _ = d * (m * d) := by rw [← h.comm]
    _ = (d * m) * d := by noncomm_ring
    _ = d := h.idempotent

/-- Left multiplication of `clineDrazinShift a b d` by `b * a` yields `b * d * a`. -/
theorem mul_clineDrazinShift_eq
    {a b d : R} {k : ℕ}
    (h : IsDrazinInverse (a * b) d k) :
    (b * a) * clineDrazinShift a b d = b * d * a := by
  unfold clineDrazinShift
  calc
    (b * a) * (b * d ^ 2 * a)
        = b * ((a * b) * d ^ 2) * a := by noncomm_ring
    _ = b * d * a := by rw [mul_drazin_sq_eq h]

/-- Right multiplication of `clineDrazinShift a b d` by `b * a` yields `b * d * a`. -/
theorem clineDrazinShift_mul_eq
    {a b d : R} {k : ℕ}
    (h : IsDrazinInverse (a * b) d k) :
    clineDrazinShift a b d * (b * a) = b * d * a := by
  unfold clineDrazinShift
  calc
    (b * d ^ 2 * a) * (b * a)
        = b * (d ^ 2 * (a * b)) * a := by noncomm_ring
    _ = b * d * a := by rw [drazin_sq_mul_eq h]

/-- **Cline's Non-Commutative Drazin Shift Theorem (1965)**:
Over any associative ring `R`, if `a * b` has Drazin inverse `d` at index `k`,
then `b * a` has Drazin inverse `clineDrazinShift a b d := b * d ^ 2 * a` at index `k + 1`. -/
theorem isDrazinInverse_clineDrazinShift
    {a b d : R} {k : ℕ}
    (h : IsDrazinInverse (a * b) d k) :
    IsDrazinInverse (b * a) (clineDrazinShift a b d) (k + 1) := by
  have h_comm :
      (b * a) * clineDrazinShift a b d = clineDrazinShift a b d * (b * a) := by
    rw [mul_clineDrazinShift_eq h, clineDrazinShift_mul_eq h]
  have h_idem :
      clineDrazinShift a b d * (b * a) * clineDrazinShift a b d =
        clineDrazinShift a b d := by
    rw [clineDrazinShift_mul_eq h]
    unfold clineDrazinShift
    calc
      (b * d * a) * (b * d ^ 2 * a)
          = b * (d * (a * b) * d) * d * a := by
              rw [sq]
              noncomm_ring
      _ = b * d * d * a := by rw [h.idempotent]
      _ = b * d ^ 2 * a := by
            rw [sq]
            noncomm_ring
  have h_pow :
      (b * a) ^ ((k + 1) + 1) * clineDrazinShift a b d = (b * a) ^ (k + 1) := by
    calc
      (b * a) ^ ((k + 1) + 1) * clineDrazinShift a b d
          = (b * a) ^ (k + 1) * ((b * a) * clineDrazinShift a b d) := by
              rw [pow_succ]
              noncomm_ring
      _ = (b * (a * b) ^ k * a) * (b * d * a) := by
            rw [mul_pow_shift a b k, mul_clineDrazinShift_eq h]
      _ = b * (((a * b) ^ k * (a * b)) * d) * a := by noncomm_ring
      _ = b * ((a * b) ^ (k + 1) * d) * a := by rw [← pow_succ]
      _ = b * (a * b) ^ k * a := by rw [h.power]
      _ = (b * a) ^ (k + 1) := (mul_pow_shift a b k).symm
  exact ⟨h_comm, h_idem, h_pow⟩

/-- The spectral core projector `P_{ba} = (b * a) * (b * a)ᴰ` of Cline's shift equals `b * d * a`. -/
theorem clineDrazinShift_projection_eq
    {a b d : R} {k : ℕ}
    (h : IsDrazinInverse (a * b) d k) :
    IsDrazinInverse.projection (b * a) (clineDrazinShift a b d) = b * d * a :=
  mul_clineDrazinShift_eq h

/-- The complementary null projector `Q_{ba} = 1 - (b * a) * (b * a)ᴰ` of Cline's shift
equals `1 - b * d * a`. -/
theorem clineDrazinShift_complementaryProjection_eq
    {a b d : R} {k : ℕ}
    (h : IsDrazinInverse (a * b) d k) :
    IsDrazinInverse.complementaryProjection (b * a) (clineDrazinShift a b d) =
      1 - b * d * a := by
  unfold IsDrazinInverse.complementaryProjection
  rw [clineDrazinShift_projection_eq h]

/-- The Fitting regular core `C_{ba} = (b * a) * P_{ba}` of Cline's shift equals
`b * ((a * b) * d) * a = b * P_{ab} * a`. -/
theorem clineDrazinShift_fittingRegularPart_eq
    {a b d : R} {k : ℕ}
    (h : IsDrazinInverse (a * b) d k) :
    IsDrazinInverse.fittingRegularPart (b * a) (clineDrazinShift a b d) =
      b * IsDrazinInverse.projection (a * b) d * a := by
  unfold IsDrazinInverse.fittingRegularPart
  rw [clineDrazinShift_projection_eq h]
  unfold IsDrazinInverse.projection
  noncomm_ring

end ClineDrazinShift

end

end InfoGeometry.Canonical.RoseDrazinPolynomial
