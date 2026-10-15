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
    x = peirce11 p x + peirce10 p x + peirce01 p x + peirce00 p x :=
      (peirce_decomposition_sum p x).symm
    _ = peirce11 p x + peirce00 p x + (peirce10 p x + peirce01 p x) := by
      abel

/-- The grading element is an involution. -/
theorem grading_sq (hp : IsIdempotent p) : grading p * grading p = 1 := by
  have hp' : p * p = p := hp
  let c := compIdempotent p
  have hc' : c * c = c := compIdempotent_isIdempotent hp
  have hpc : p * c = 0 := compIdempotent_orthogonal hp
  have hcp : c * p = 0 := compIdempotent_orthogonal_rev hp
  unfold grading
  calc
    (p - c) * (p - c) = p * p - p * c - c * p + c * c := by noncomm_ring
    _ = p + c := by rw [hp', hpc, hcp, hc']; abel
    _ = 1 := compIdempotent_add_eq_one p

/-- The diagonal Peirce part commutes with the grading element. -/
theorem grading_commutes_evenPart (hp : IsIdempotent p) (x : A) :
    grading p * evenPart p x = evenPart p x * grading p := by
  have hp' : p * p = p := hp
  have hc' : compIdempotent p * compIdempotent p = compIdempotent p :=
    compIdempotent_isIdempotent hp
  have hpc : p * compIdempotent p = 0 := compIdempotent_orthogonal hp
  have hcp : compIdempotent p * p = 0 := compIdempotent_orthogonal_rev hp
  have h11L : p * peirce11 p x = peirce11 p x := by
    unfold peirce11
    calc
      p * (p * x * p) = (p * p) * x * p := by noncomm_ring
      _ = p * x * p := by rw [hp']
  have h00L : p * peirce00 p x = 0 := by
    unfold peirce00
    calc
      p * (compIdempotent p * x * compIdempotent p) =
          (p * compIdempotent p) * x * compIdempotent p := by noncomm_ring
      _ = 0 := by rw [hpc]; simp
  have h11C : compIdempotent p * peirce11 p x = 0 := by
    unfold peirce11
    calc
      compIdempotent p * (p * x * p) =
          (compIdempotent p * p) * x * p := by noncomm_ring
      _ = 0 := by rw [hcp]; simp
  have h00C : compIdempotent p * peirce00 p x = peirce00 p x := by
    unfold peirce00
    calc
      compIdempotent p * (compIdempotent p * x * compIdempotent p) =
          (compIdempotent p * compIdempotent p) * x * compIdempotent p := by noncomm_ring
      _ = compIdempotent p * x * compIdempotent p := by rw [hc']
  have h11R : peirce11 p x * p = peirce11 p x := by
    unfold peirce11
    calc
      (p * x * p) * p = p * x * (p * p) := by noncomm_ring
      _ = p * x * p := by rw [hp']
  have h00R : peirce00 p x * p = 0 := by
    unfold peirce00
    calc
      (compIdempotent p * x * compIdempotent p) * p =
          compIdempotent p * x * (compIdempotent p * p) := by noncomm_ring
      _ = 0 := by rw [hcp]; simp
  have h11CR : peirce11 p x * compIdempotent p = 0 := by
    unfold peirce11
    calc
      (p * x * p) * compIdempotent p = p * x * (p * compIdempotent p) := by noncomm_ring
      _ = 0 := by rw [hpc]; simp
  have h00CR : peirce00 p x * compIdempotent p = peirce00 p x := by
    unfold peirce00
    calc
      (compIdempotent p * x * compIdempotent p) * compIdempotent p =
          compIdempotent p * x * (compIdempotent p * compIdempotent p) := by noncomm_ring
      _ = compIdempotent p * x * compIdempotent p := by rw [hc']
  have hleft :
      (p - compIdempotent p) * (peirce11 p x + peirce00 p x) =
        peirce11 p x - peirce00 p x := by
    simp only [sub_mul, mul_add, h11L, h00L, h11C, h00C]
    abel
  have hright :
      (peirce11 p x + peirce00 p x) * (p - compIdempotent p) =
        peirce11 p x - peirce00 p x := by
    simp only [mul_sub, add_mul, h11R, h00R, h11CR, h00CR]
    abel
  simpa [grading, evenPart] using hleft.trans hright.symm

/-- The off-diagonal Peirce part anticommutes with the grading element. -/
theorem grading_anticommutes_oddPart (hp : IsIdempotent p) (x : A) :
    grading p * oddPart p x + oddPart p x * grading p = 0 := by
  have hp' : p * p = p := hp
  have hc' : compIdempotent p * compIdempotent p = compIdempotent p :=
    compIdempotent_isIdempotent hp
  have hpc : p * compIdempotent p = 0 := compIdempotent_orthogonal hp
  have hcp : compIdempotent p * p = 0 := compIdempotent_orthogonal_rev hp
  have h10L : p * peirce10 p x = peirce10 p x := by
    unfold peirce10
    calc
      p * (p * x * compIdempotent p) =
          (p * p) * x * compIdempotent p := by noncomm_ring
      _ = p * x * compIdempotent p := by rw [hp']
  have h01L : p * peirce01 p x = 0 := by
    unfold peirce01
    calc
      p * (compIdempotent p * x * p) =
          (p * compIdempotent p) * x * p := by noncomm_ring
      _ = 0 := by rw [hpc]; simp
  have hc10L : compIdempotent p * peirce10 p x = 0 := by
    unfold peirce10
    calc
      compIdempotent p * (p * x * compIdempotent p) =
          (compIdempotent p * p) * x * compIdempotent p := by noncomm_ring
      _ = 0 := by rw [hcp]; simp
  have hc01L : compIdempotent p * peirce01 p x = peirce01 p x := by
    unfold peirce01
    calc
      compIdempotent p * (compIdempotent p * x * p) =
          (compIdempotent p * compIdempotent p) * x * p := by noncomm_ring
      _ = compIdempotent p * x * p := by rw [hc']
  have h10R : peirce10 p x * p = 0 := by
    unfold peirce10
    calc
      (p * x * compIdempotent p) * p =
          p * x * (compIdempotent p * p) := by noncomm_ring
      _ = 0 := by rw [hcp]; simp
  have h01R : peirce01 p x * p = peirce01 p x := by
    unfold peirce01
    calc
      (compIdempotent p * x * p) * p =
          compIdempotent p * x * (p * p) := by noncomm_ring
      _ = compIdempotent p * x * p := by rw [hp']
  have h10CR : peirce10 p x * compIdempotent p = peirce10 p x := by
    unfold peirce10
    calc
      (p * x * compIdempotent p) * compIdempotent p =
          p * x * (compIdempotent p * compIdempotent p) := by noncomm_ring
      _ = p * x * compIdempotent p := by rw [hc']
  have h01CR : peirce01 p x * compIdempotent p = 0 := by
    unfold peirce01
    calc
      (compIdempotent p * x * p) * compIdempotent p =
          compIdempotent p * x * (p * compIdempotent p) := by noncomm_ring
      _ = 0 := by rw [hpc]; simp
  have hleft :
      (p - compIdempotent p) * (peirce10 p x + peirce01 p x) =
        peirce10 p x - peirce01 p x := by
    simp only [sub_mul, mul_add, h10L, h01L, hc10L, hc01L]
    abel
  have hright :
      (peirce10 p x + peirce01 p x) * (p - compIdempotent p) =
        -peirce10 p x + peirce01 p x := by
    simp only [mul_sub, add_mul, h10R, h01R, h10CR, h01CR]
    abel
  change (p - compIdempotent p) * (peirce10 p x + peirce01 p x) +
      (peirce10 p x + peirce01 p x) * (p - compIdempotent p) = 0
  rw [hleft, hright]
  abel

/-- The product of two off-diagonal Peirce parts is diagonal.  In particular,
the square of an odd part belongs to the even part; it need not be zero. -/
theorem oddPart_mul_oddPart_is_even (hp : IsIdempotent p) (x y : A) :
    evenPart p (oddPart p x * oddPart p y) =
      oddPart p x * oddPart p y := by
  have h10sq : peirce10 p x * peirce10 p y = 0 := by
    dsimp [peirce10]
    have hfactor :
        (p * x * compIdempotent p) * (p * y * compIdempotent p) =
          p * x * (compIdempotent p * p) * (y * compIdempotent p) := by
      noncomm_ring
    rw [hfactor, compIdempotent_orthogonal_rev hp]
    simp
  have h01sq : peirce01 p x * peirce01 p y = 0 := by
    dsimp [peirce01]
    have hfactor :
        (compIdempotent p * x * p) * (compIdempotent p * y * p) =
          compIdempotent p * x * (p * compIdempotent p) * (y * p) := by
      noncomm_ring
    rw [hfactor, compIdempotent_orthogonal hp]
    simp
  have h10_01 := peirce10_mul_peirce01 hp x y
  have h01_10 := peirce01_mul_peirce10 hp x y
  have hproduct :
      oddPart p x * oddPart p y =
        peirce11 p (x * compIdempotent p * y) + peirce00 p (x * p * y) := by
    unfold oddPart
    simp only [add_mul, mul_add]
    rw [h10sq, h10_01, h01_10, h01sq]
    abel
  rw [hproduct]
  have hp' : p * p = p := hp
  have hc' : compIdempotent p * compIdempotent p = compIdempotent p :=
    compIdempotent_isIdempotent hp
  have hpc : p * compIdempotent p = 0 := compIdempotent_orthogonal hp
  have hcp : compIdempotent p * p = 0 := compIdempotent_orthogonal_rev hp
  have hfix11 (z : A) : evenPart p (peirce11 p z) = peirce11 p z := by
    unfold evenPart peirce11 peirce00
    have hdiag : p * (p * z * p) * p = p * z * p := by
      calc
        p * (p * z * p) * p = (p * p) * z * (p * p) := by noncomm_ring
        _ = p * z * p := by rw [hp']
    have hoff : compIdempotent p * (p * z * p) * compIdempotent p = 0 := by
      calc
        compIdempotent p * (p * z * p) * compIdempotent p =
            (compIdempotent p * p) * z * (p * compIdempotent p) := by noncomm_ring
        _ = 0 := by rw [hcp, hpc]; simp
    rw [hdiag, hoff, add_zero]
  have hfix00 (z : A) : evenPart p (peirce00 p z) = peirce00 p z := by
    unfold evenPart peirce11 peirce00
    have hoff : p * (compIdempotent p * z * compIdempotent p) * p = 0 := by
      calc
        p * (compIdempotent p * z * compIdempotent p) * p =
            (p * compIdempotent p) * z * (compIdempotent p * p) := by noncomm_ring
        _ = 0 := by rw [hpc, hcp]; simp
    have hdiag :
        compIdempotent p * (compIdempotent p * z * compIdempotent p) *
          compIdempotent p = compIdempotent p * z * compIdempotent p := by
      calc
        compIdempotent p * (compIdempotent p * z * compIdempotent p) *
            compIdempotent p =
            (compIdempotent p * compIdempotent p) * z *
              (compIdempotent p * compIdempotent p) := by noncomm_ring
        _ = compIdempotent p * z * compIdempotent p := by rw [hc']
    rw [hoff, hdiag, zero_add]
  have hevenAdd (a b : A) : evenPart p (a + b) = evenPart p a + evenPart p b := by
    unfold evenPart peirce11 peirce00
    simp only [mul_add, add_mul]
    abel
  rw [hevenAdd, hfix11, hfix00]

/-- Conjugation by the grading fixes the diagonal Peirce part. -/
theorem grading_conjugates_evenPart (hp : IsIdempotent p) (x : A) :
    grading p * evenPart p x * grading p = evenPart p x := by
  calc
    grading p * evenPart p x * grading p =
        (evenPart p x * grading p) * grading p := by
          rw [grading_commutes_evenPart p hp x]
    _ = evenPart p x * (grading p * grading p) := by rw [mul_assoc]
    _ = evenPart p x := by rw [grading_sq p hp, mul_one]

/-- Conjugation by the grading negates the off-diagonal Peirce part. -/
theorem grading_conjugates_oddPart (hp : IsIdempotent p) (x : A) :
    grading p * oddPart p x * grading p = - oddPart p x := by
  have hanti := grading_anticommutes_oddPart p hp x
  have hleft : grading p * oddPart p x =
      -(oddPart p x * grading p) := by
    exact eq_neg_of_add_eq_zero_left hanti
  calc
    grading p * oddPart p x * grading p =
        -(oddPart p x * grading p) * grading p := by rw [hleft]
    _ = -(oddPart p x * (grading p * grading p)) := by rw [neg_mul, mul_assoc]
    _ = - oddPart p x := by rw [grading_sq p hp, mul_one]

/-- A conditional dispersion-style square identity: an odd element whose
square is the scalar `mSq` contributes no mixed term to `(q G + M)^2`. -/
theorem scalar_grading_square_add_odd (hp : IsIdempotent p)
    (q mSq : ℝ) (M : A) [Algebra ℝ A]
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
      (s * g) * (s * g) = s * (g * s) * g := by noncomm_ring
      _ = s * (s * g) * g := by rw [hs g]
      _ = (s * s) * (g * g) := by noncomm_ring
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
