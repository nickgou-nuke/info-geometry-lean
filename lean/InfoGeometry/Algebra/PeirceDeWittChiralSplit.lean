import Mathlib.Algebra.Algebra.Basic
import Mathlib.Tactic.NoncommRing
import InfoGeometry.Algebra.IdempotentProjector

/-!
# Parity split from a Peirce frame

For an idempotent `p` in an associative ring, the existing
`IdempotentProjector` owner supplies the four Peirce corners.  This file
packages their diagonal and off-diagonal sums as even and odd parts and proves
their grading identities.  The names `body` and `soul` sometimes used for
these parts are analogies only: no nilpotent-ideal quotient or supermanifold
body map is asserted here.

The final square identity is conditional algebra in an `ℝ`-algebra.  It does
not assert a Dirac equation or a physical mass-shell theorem.
-/

namespace InfoGeometry.Algebra.PeirceDeWittChiralSplit

variable {A : Type*} [Ring A] (p : A) (hp : IsIdempotent p)

/-- The diagonal Peirce part associated to `p` and its complement. -/
def evenPart (x : A) : A := peirce11 p x + peirce00 p x

/-- The off-diagonal Peirce part associated to `p` and its complement. -/
def oddPart (x : A) : A := peirce10 p x + peirce01 p x

/-- The grading element determined by the complementary idempotents. -/
def grading : A := p - compIdempotent p

/-- The four Peirce corners reconstruct the original element, grouped by
diagonal and off-diagonal parity. -/
theorem peirce_even_odd_decomposition (x : A) :
    x = evenPart p x + oddPart p x := by
  unfold evenPart oddPart
  calc
    peirce11 p x + peirce00 p x + (peirce10 p x + peirce01 p x) =
        peirce11 p x + peirce10 p x + peirce01 p x + peirce00 p x := by
          noncomm_ring
    _ = x := (peirce_decomposition_sum p x).symm

/-- The grading element is an involution. -/
theorem grading_sq : grading p * grading p = 1 := by
  have hp' : p * p = p := hp
  have hc' : compIdempotent p * compIdempotent p = compIdempotent p :=
    compIdempotent_isIdempotent hp
  have hpc : p * compIdempotent p = 0 := compIdempotent_orthogonal hp
  have hcp : compIdempotent p * p = 0 := compIdempotent_orthogonal_rev hp
  unfold grading compIdempotent
  noncomm_ring [hp', hc', hpc, hcp]

/-- The diagonal Peirce part commutes with the grading element. -/
theorem grading_commutes_evenPart (x : A) :
    grading p * evenPart p x = evenPart p x * grading p := by
  have hp' : p * p = p := hp
  have hc' : compIdempotent p * compIdempotent p = compIdempotent p :=
    compIdempotent_isIdempotent hp
  have hpc : p * compIdempotent p = 0 := compIdempotent_orthogonal hp
  have hcp : compIdempotent p * p = 0 := compIdempotent_orthogonal_rev hp
  unfold grading evenPart peirce11 peirce00 compIdempotent
  noncomm_ring [hp', hc', hpc, hcp]

/-- The off-diagonal Peirce part anticommutes with the grading element. -/
theorem grading_anticommutes_oddPart (x : A) :
    grading p * oddPart p x + oddPart p x * grading p = 0 := by
  have hp' : p * p = p := hp
  have hc' : compIdempotent p * compIdempotent p = compIdempotent p :=
    compIdempotent_isIdempotent hp
  have hpc : p * compIdempotent p = 0 := compIdempotent_orthogonal hp
  have hcp : compIdempotent p * p = 0 := compIdempotent_orthogonal_rev hp
  unfold grading oddPart peirce10 peirce01 compIdempotent
  noncomm_ring [hp', hc', hpc, hcp]

/-- The product of two off-diagonal Peirce parts is diagonal.  In particular,
the square of an odd part belongs to the even part; it need not be zero. -/
theorem oddPart_mul_oddPart_is_even (x y : A) :
    evenPart p (oddPart p x * oddPart p y) =
      oddPart p x * oddPart p y := by
  have hp' : p * p = p := hp
  have hc' : compIdempotent p * compIdempotent p = compIdempotent p :=
    compIdempotent_isIdempotent hp
  have hpc : p * compIdempotent p = 0 := compIdempotent_orthogonal hp
  have hcp : compIdempotent p * p = 0 := compIdempotent_orthogonal_rev hp
  unfold evenPart oddPart peirce11 peirce00 peirce10 peirce01 compIdempotent
  noncomm_ring [hp', hc', hpc, hcp]

/-- Conjugation by the grading fixes the diagonal Peirce part. -/
theorem grading_conjugates_evenPart (x : A) :
    grading p * evenPart p x * grading p = evenPart p x := by
  calc
    grading p * evenPart p x * grading p =
        (evenPart p x * grading p) * grading p := by
          rw [grading_commutes_evenPart p hp x]
    _ = evenPart p x * (grading p * grading p) := by rw [mul_assoc]
    _ = evenPart p x := by rw [grading_sq p hp, mul_one]

/-- Conjugation by the grading negates the off-diagonal Peirce part. -/
theorem grading_conjugates_oddPart (x : A) :
    grading p * oddPart p x * grading p = - oddPart p x := by
  have hanti := grading_anticommutes_oddPart p hp x
  have hleft : grading p * oddPart p x =
      -(oddPart p x * grading p) := by
    exact eq_neg_of_add_eq_zero_right hanti
  calc
    grading p * oddPart p x * grading p =
        -(oddPart p x * grading p) * grading p := by rw [hleft]
    _ = -(oddPart p x * (grading p * grading p)) := by rw [mul_assoc]
    _ = - oddPart p x := by rw [grading_sq p hp, mul_one]

/-- A conditional dispersion-style square identity: an odd element whose
square is the scalar `mSq` contributes no mixed term to `(q G + M)^2`. -/
theorem scalar_grading_square_add_odd (q mSq : ℝ) (M : A) [Algebra ℝ A]
    (hM_odd : oddPart p M = M)
    (hM_sq : M * M = algebraMap ℝ A mSq) :
    let H := algebraMap ℝ A q * grading p + M
    H * H = algebraMap ℝ A (q ^ 2 + mSq) := by
  dsimp
  let s : A := algebraMap ℝ A q
  let g : A := grading p
  have hs (x : A) : s * x = x * s := Algebra.commutes q x
  have hg : g * g = 1 := grading_sq p hp
  have hodd : g * M + M * g = 0 := by
    rw [← hM_odd]
    exact grading_anticommutes_oddPart p hp M
  have hcross : (s * g) * M + M * (s * g) = 0 := by
    calc
      (s * g) * M + M * (s * g) = s * (g * M) + s * (M * g) := by
        rw [mul_assoc]
        congr 1
        rw [← mul_assoc, ← hs M, mul_assoc]
      _ = s * (g * M + M * g) := by rw [← mul_add]
      _ = 0 := by rw [hodd, mul_zero]
  have hkinetic : (s * g) * (s * g) = algebraMap ℝ A (q ^ 2) := by
    calc
      (s * g) * (s * g) = (s * s) * (g * g) := by noncomm_ring [hs g]
      _ = algebraMap ℝ A (q * q) := by
        dsimp [s]
        rw [← map_mul, hg, mul_one]
      _ = algebraMap ℝ A (q ^ 2) := by rw [pow_two]
  calc
    (s * g + M) * (s * g + M) =
        (s * g) * (s * g) + ((s * g) * M + M * (s * g)) + M * M := by
          noncomm_ring
    _ = algebraMap ℝ A (q ^ 2) + 0 + algebraMap ℝ A mSq := by
      rw [hkinetic, hcross, hM_sq]
    _ = algebraMap ℝ A (q ^ 2 + mSq) := by rw [add_zero, ← map_add]

end InfoGeometry.Algebra.PeirceDeWittChiralSplit
