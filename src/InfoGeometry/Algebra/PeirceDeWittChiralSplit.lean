/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

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

/-- Symmetric interband operator for a chosen pair of Peirce corners. -/
def interbandSum (a c : A) : A := peirce10 p a + peirce01 p c

/-- Oriented interband operator for a chosen pair of Peirce corners. -/
def interbandDifference (a c : A) : A := peirce10 p a - peirce01 p c

/-- The Jordan return operator of two opposing Peirce corners. -/
def interbandMetric (a c : A) : A :=
  peirce10 p a * peirce01 p c + peirce01 p c * peirce10 p a

/-- The oriented return operator of two opposing Peirce corners. -/
def interbandCurvature (a c : A) : A :=
  peirce10 p a * peirce01 p c - peirce01 p c * peirce10 p a

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

/-- Left multiplication by the Peirce grading sends the odd component to the
oriented difference of the two transition corners. This is the algebraic
content of the parity-string action on an odd operator. -/
theorem grading_oddPart_left_action (hp : IsIdempotent p) (x : A) :
    grading p * oddPart p x = peirce10 p x - peirce01 p x := by
  have hp' : p * p = p := hp
  have hc' : compIdempotent p * compIdempotent p = compIdempotent p :=
    compIdempotent_isIdempotent hp
  have hpc : p * compIdempotent p = 0 := compIdempotent_orthogonal hp
  have hcp : compIdempotent p * p = 0 := compIdempotent_orthogonal_rev hp
  have hsum : p + compIdempotent p = 1 := compIdempotent_add_eq_one p
  change (p - compIdempotent p) *
      (peirce10 p x + peirce01 p x) = peirce10 p x - peirce01 p x
  have h10L : p * peirce10 p x = peirce10 p x := by
    unfold peirce10
    calc
      p * (p * x * compIdempotent p) = (p * p) * x * compIdempotent p := by
        noncomm_ring
      _ = p * x * compIdempotent p := by rw [hp']
  have h01L : p * peirce01 p x = 0 := by
    unfold peirce01
    calc
      p * (compIdempotent p * x * p) = (p * compIdempotent p) * x * p := by
        noncomm_ring
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
  simp only [sub_mul, mul_add, h10L, h01L, hc10L, hc01L]
  abel

/-- Equivalently, the grading-dressed odd part is the commutator with the
idempotent cut. The multiplication order is explicit. -/
theorem grading_oddPart_eq_cut_commutator (hp : IsIdempotent p) (x : A) :
    grading p * oddPart p x = p * x - x * p := by
  rw [grading_oddPart_left_action p hp x]
  have hsum : p + compIdempotent p = 1 := compIdempotent_add_eq_one p
  have hpx : p * x = peirce11 p x + peirce10 p x := by
    calc
      p * x = p * x * (p + compIdempotent p) := by rw [hsum, mul_one]
      _ = peirce11 p x + peirce10 p x := by
        unfold peirce11 peirce10
        noncomm_ring
  have hxp : x * p = peirce11 p x + peirce01 p x := by
    calc
      x * p = (p + compIdempotent p) * x * p := by rw [hsum, one_mul]
      _ = peirce11 p x + peirce01 p x := by
        unfold peirce11 peirce01
        noncomm_ring
  rw [hpx, hxp]
  unfold peirce10 peirce01
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

/-- Lower unipotent factor associated to the lower Peirce corner. -/
def dewittLower (a : A) : A := 1 + peirce01 p a

/-- Upper unipotent factor associated to the upper Peirce corner. -/
def dewittUpper (a : A) : A := 1 + peirce10 p a

/-- Inverse candidate for the lower unipotent factor. -/
def dewittLowerInv (c : A) : A := 1 - peirce01 p c

/-- Inverse candidate for the upper unipotent factor. -/
def dewittUpperInv (a : A) : A := 1 - peirce10 p a

/-- The lower-right Schur correction for the chosen off-diagonal blocks. -/
def dewittSchur00 (a c m : A) : A :=
  p + (peirce00 p m - peirce01 p c * peirce10 p a)

/-- Peirce-corner LDU reconstruction. The correction is the ordered product
`N₋ N₊`; no inverse of either Peirce idempotent is used or asserted. -/
theorem dewitt_peirce_LDU (hp : IsIdempotent p) (a c m : A) :
    dewittLower p c * dewittSchur00 p a c m * dewittUpper p a =
      p + peirce10 p a + peirce01 p c + peirce00 p m := by
  let n := peirce01 p c
  let u := peirce10 p a
  let d := peirce00 p m
  have hnp : n * p = n := by
    dsimp [n, peirce01]
    calc
      compIdempotent p * c * p * p = compIdempotent p * c * (p * p) := by
        noncomm_ring
      _ = compIdempotent p * c * p := by rw [hp]
  have hnd : n * d = 0 := by
    have hpc : p * compIdempotent p = 0 := compIdempotent_orthogonal hp
    dsimp [n, d, peirce01, peirce00]
    calc
      (compIdempotent p * c * p) *
          (compIdempotent p * m * compIdempotent p) =
        compIdempotent p * c * (p * compIdempotent p) * m *
          compIdempotent p := by noncomm_ring
      _ = 0 := by rw [hpc]; noncomm_ring
  have hnn : n * n = 0 := peirce01_square_zero hp c
  have hdu : d * u = 0 := by
    have hcp : compIdempotent p * p = 0 := compIdempotent_orthogonal_rev hp
    dsimp [d, u, peirce00, peirce10]
    calc
      (compIdempotent p * m * compIdempotent p) *
          (p * a * compIdempotent p) =
        compIdempotent p * m * (compIdempotent p * p) * a *
          compIdempotent p := by noncomm_ring
      _ = 0 := by rw [hcp]; noncomm_ring
  have hpu : p * u = u := by
    dsimp [u, peirce10]
    calc
      p * (p * a * compIdempotent p) = (p * p) * a * compIdempotent p := by
        noncomm_ring
      _ = p * a * compIdempotent p := by rw [hp]
  have huu : u * u = 0 := peirce10_square_zero hp a
  have hzero : n * (n * u) = 0 := by
    rw [← mul_assoc, hnn, zero_mul]
  change (1 + n) * (p + (d - n * u)) * (1 + u) = p + u + n + d
  calc
    (1 + n) * (p + (d - n * u)) * (1 + u) =
        (p + d + n - n * u) * (1 + u) := by
      congr 1
      noncomm_ring [hnp, hnd, hzero]
    _ = p + u + n + d := by
      noncomm_ring [hdu, hpu, huu, hzero]

/-- The complementary Peirce frame gives the dual upper-diagonal-lower
factorization, with the ordered Schur correction `N₊ N₋`. -/
theorem dewitt_peirce_dual_LDU (hp : IsIdempotent p) (a c m : A) :
    dewittUpper p a *
        (compIdempotent p + (peirce11 p m - peirce10 p a * peirce01 p c)) *
        dewittLower p c =
      compIdempotent p + peirce10 p a + peirce01 p c + peirce11 p m := by
  have hq : IsIdempotent (compIdempotent p) := compIdempotent_isIdempotent hp
  have h01q : peirce01 (compIdempotent p) a = peirce10 p a := by
    dsimp [peirce10, peirce01, compIdempotent]
    noncomm_ring [hp]
  have h10q : peirce10 (compIdempotent p) c = peirce01 p c := by
    dsimp [peirce10, peirce01, compIdempotent]
    noncomm_ring [hp]
  have h00q : peirce00 (compIdempotent p) m = peirce11 p m := by
    dsimp [peirce00, peirce11, compIdempotent] <;> noncomm_ring [hp]
  have h := dewitt_peirce_LDU (compIdempotent p) hq c a m
  simp only [dewittLower, dewittUpper, dewittSchur00,
    h10q, h01q, h00q] at h
  calc
    dewittUpper p a *
        (compIdempotent p + (peirce11 p m - peirce10 p a * peirce01 p c)) *
        dewittLower p c =
      compIdempotent p + peirce01 p c + peirce10 p a + peirce11 p m := h
    _ = compIdempotent p + peirce10 p a + peirce01 p c + peirce11 p m := by abel

/-- The Peirce-supported off-diagonal factors are square-zero, so the
corresponding unipotent factors have two-sided inverses. -/
theorem dewitt_unipotent_inverse (hp : IsIdempotent p) (a c : A) :
    dewittLowerInv p c * dewittLower p c = 1 ∧
    dewittLower p c * dewittLowerInv p c = 1 ∧
    dewittUpperInv p a * dewittUpper p a = 1 ∧
    dewittUpper p a * dewittUpperInv p a = 1 := by
  have hn := peirce01_square_zero hp c
  have hu := peirce10_square_zero hp a
  dsimp [dewittLowerInv, dewittLower, dewittUpperInv, dewittUpper]
  exact ⟨by noncomm_ring [hn], by noncomm_ring [hn],
         by noncomm_ring [hu], by noncomm_ring [hu]⟩

/-- Unipotent stripping recovers the diagonal Schur block from the LDU
reconstruction. This uses only the Peirce corner laws, not inverses of `p` or
its complement. -/
theorem dewitt_peirce_block_diagonalization (hp : IsIdempotent p)
    (a c m : A) :
    dewittLowerInv p c *
        (p + peirce10 p a + peirce01 p c + peirce00 p m) *
        dewittUpperInv p a = dewittSchur00 p a c m := by
  rw [← dewitt_peirce_LDU p hp a c m]
  obtain ⟨hL, _, _, hU⟩ := dewitt_unipotent_inverse p hp a c
  calc
    dewittLowerInv p c *
        (dewittLower p c * dewittSchur00 p a c m * dewittUpper p a) *
        dewittUpperInv p a =
      (dewittLowerInv p c * dewittLower p c) * dewittSchur00 p a c m *
        (dewittUpper p a * dewittUpperInv p a) := by noncomm_ring
    _ = dewittSchur00 p a c m := by rw [hL, hU]; simp

/-- The complementary Peirce frame has the dual stripping identity: the
inverse upper and lower factors remove the off-diagonal blocks from the
dual U-D-L reconstruction. -/
theorem dewitt_peirce_dual_block_diagonalization (hp : IsIdempotent p)
    (a c m : A) :
    dewittUpperInv p a *
        (compIdempotent p + peirce10 p a + peirce01 p c + peirce11 p m) *
        dewittLowerInv p c =
      compIdempotent p + (peirce11 p m - peirce10 p a * peirce01 p c) := by
  rw [← dewitt_peirce_dual_LDU p hp a c m]
  obtain ⟨_, hL, hU, _⟩ := dewitt_unipotent_inverse p hp a c
  calc
    dewittUpperInv p a *
        (dewittUpper p a *
          (compIdempotent p + (peirce11 p m - peirce10 p a * peirce01 p c)) *
          dewittLower p c) * dewittLowerInv p c =
        (dewittUpperInv p a * dewittUpper p a) *
          (compIdempotent p + (peirce11 p m - peirce10 p a * peirce01 p c)) *
          (dewittLower p c * dewittLowerInv p c) := by noncomm_ring
    _ = compIdempotent p + (peirce11 p m - peirce10 p a * peirce01 p c) := by
      rw [hU, hL]
      simp

/-- Golden transfer specialization of the LDU theorem, with zero lower-right
input block. -/
theorem dewitt_golden_transfer_LDU (hp : IsIdempotent p) (a c : A) :
    dewittLower p c *
        (p - peirce01 p c * peirce10 p a) * dewittUpper p a =
      p + peirce10 p a + peirce01 p c := by
  simpa only [dewittSchur00, peirce00, mul_zero, zero_mul, add_zero, zero_add,
    sub_eq_add_neg] using
    dewitt_peirce_LDU p hp a c 0

/-- The corresponding inverse factors strip the golden transfer operator to
its diagonal round-trip correction. -/
theorem dewitt_golden_transfer_stripping (hp : IsIdempotent p) (a c : A) :
    dewittLowerInv p c *
        (p + peirce10 p a + peirce01 p c) * dewittUpperInv p a =
      p - peirce01 p c * peirce10 p a := by
  simpa only [dewittSchur00, peirce00, mul_zero, zero_mul, add_zero, zero_add,
    sub_eq_add_neg] using
    dewitt_peirce_block_diagonalization p hp a c 0

/-- A parity string converts a commutator into the anticommutator of the
string-dressed operator. The only hypothesis is the sign relation between
the string and the first operator. -/
theorem jw_commutator_to_anticommutator (s n x : A)
    (hsn : n * s = -(s * n)) :
    n * (s * x) + (s * x) * n = -(s * (n * x - x * n)) := by
  calc
    n * (s * x) + (s * x) * n = (n * s) * x + s * (x * n) := by
      noncomm_ring
    _ = (-(s * n)) * x + s * (x * n) := by rw [hsn]
    _ = -(s * (n * x - x * n)) := by noncomm_ring

/-- Two square-zero site operators with vanishing cross anticommutator have a
square-zero sum. This is the internal-ring algebraic step behind a two-site
Jordan–Wigner chain. -/
theorem jw_two_site_sum_square_zero (x y : A)
    (hx : x * x = 0) (hy : y * y = 0)
    (hcross : x * y + y * x = 0) :
    (x + y) * (x + y) = 0 := by
  calc
    (x + y) * (x + y) = x * x + (x * y + y * x) + y * y := by
      noncomm_ring
    _ = 0 := by rw [hx, hcross, hy]; abel

/-- The anticommutator of two sums splits into the site terms when the two
cross-site anticommutators vanish. -/
theorem jw_two_site_metric_additive (x₁ y₁ x₂ y₂ : A)
    (hcross₁ : x₁ * y₂ + y₂ * x₁ = 0)
    (hcross₂ : x₂ * y₁ + y₁ * x₂ = 0) :
    (x₁ + x₂) * (y₁ + y₂) + (y₁ + y₂) * (x₁ + x₂) =
      (x₁ * y₁ + y₁ * x₁) + (x₂ * y₂ + y₂ * x₂) := by
  calc
    (x₁ + x₂) * (y₁ + y₂) + (y₁ + y₂) * (x₁ + x₂) =
        (x₁ * y₁ + y₁ * x₁) + (x₁ * y₂ + y₂ * x₁) +
          (x₂ * y₁ + y₁ * x₂) + (x₂ * y₂ + y₂ * x₂) := by noncomm_ring
    _ = (x₁ * y₁ + y₁ * x₁) + (x₂ * y₂ + y₂ * x₂) := by
      rw [hcross₁, hcross₂]
      simp

/-- Anticommuting with a finite sum distributes termwise in any associative
ring. This is the reusable expansion needed for arbitrary finite
Jordan--Wigner chains. -/
theorem jw_anticommutator_finite_sum {ι : Type*} [DecidableEq ι]
    (a : A) (s : Finset ι) (f : ι → A) :
    a * (∑ i ∈ s, f i) + (∑ i ∈ s, f i) * a =
      ∑ i ∈ s, (a * f i + f i * a) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      simp only [Finset.sum_insert hi, mul_add, add_mul]
      rw [← ih]
      abel

/-- A finite family of pairwise anticommuting square-zero operators has a
square-zero sum. This is the arbitrary-finite-site algebraic closure behind
Jordan--Wigner dressing; no tensor product, scalar matrix, or commutative
operator assumption is involved. -/
theorem jw_finite_sum_square_zero {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f : ι → A)
    (hsq : ∀ i ∈ s, f i * f i = 0)
    (hcross : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      f i * f j + f j * f i = 0) :
    (∑ i ∈ s, f i) * (∑ i ∈ s, f i) = 0 := by
  classical
  revert hsq hcross
  induction s using Finset.induction_on with
  | empty =>
      intro _ _
      simp
  | @insert a s ha ih =>
      intro hsq hcross
      have hsqRest : ∀ i ∈ s, f i * f i = 0 := by
        intro i hi
        exact hsq i (Finset.mem_insert_of_mem hi)
      have hcrossRest : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
          f i * f j + f j * f i = 0 := by
        intro i hi j hj hne
        exact hcross i (Finset.mem_insert_of_mem hi) j
          (Finset.mem_insert_of_mem hj) hne
      have hrest := ih hsqRest hcrossRest
      have hsqA : f a * f a = 0 := hsq a (Finset.mem_insert_self a s)
      have hcrossA : f a * (∑ i ∈ s, f i) +
          (∑ i ∈ s, f i) * f a = 0 := by
        rw [jw_anticommutator_finite_sum]
        apply Finset.sum_eq_zero
        intro i hi
        have hne : a ≠ i := by
          intro heq
          subst i
          exact ha hi
        have hterm := hcross a (Finset.mem_insert_self a s) i
          (Finset.mem_insert_of_mem hi) hne
        simpa [add_comm] using hterm
      rw [Finset.sum_insert ha]
      calc
        (f a + (∑ i ∈ s, f i)) * (f a + (∑ i ∈ s, f i)) =
            f a * f a +
              (f a * (∑ i ∈ s, f i) + (∑ i ∈ s, f i) * f a) +
                (∑ i ∈ s, f i) * (∑ i ∈ s, f i) := by noncomm_ring
        _ = 0 := by rw [hsqA, hcrossA, hrest]; abel

/-- For two finite families whose mixed anticommutators vanish off the
diagonal, the anticommutator of their sums is the sum of the on-site
anticommutators. This is the finite-chain additive metric law. -/
theorem jw_finite_sum_metric_additive {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f g : ι → A)
    (hcross : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      f i * g j + g j * f i = 0) :
    (∑ i ∈ s, f i) * (∑ i ∈ s, g i) +
      (∑ i ∈ s, g i) * (∑ i ∈ s, f i) =
        ∑ i ∈ s, (f i * g i + g i * f i) := by
  classical
  revert hcross
  induction s using Finset.induction_on with
  | empty =>
      intro _
      simp
  | @insert a s ha ih =>
      intro hcross
      have hcrossRest : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
          f i * g j + g j * f i = 0 := by
        intro i hi j hj hne
        exact hcross i (Finset.mem_insert_of_mem hi) j
          (Finset.mem_insert_of_mem hj) hne
      have hrest := ih hcrossRest
      have hfirst : f a * (∑ i ∈ s, g i) +
          (∑ i ∈ s, g i) * f a = 0 := by
        rw [jw_anticommutator_finite_sum]
        apply Finset.sum_eq_zero
        intro i hi
        have hne : a ≠ i := by
          intro heq
          subst i
          exact ha hi
        exact hcross a (Finset.mem_insert_self a s) i
          (Finset.mem_insert_of_mem hi) hne
      have hsecond : (∑ i ∈ s, f i) * g a +
          g a * (∑ i ∈ s, f i) = 0 := by
        have hsecond' : g a * (∑ i ∈ s, f i) +
            (∑ i ∈ s, f i) * g a = 0 := by
          rw [jw_anticommutator_finite_sum]
          apply Finset.sum_eq_zero
          intro i hi
          have hne : i ≠ a := by
            intro heq
            subst i
            exact ha hi
          have hterm := hcross i (Finset.mem_insert_of_mem hi) a
            (Finset.mem_insert_self a s) hne
          simpa [add_comm] using hterm
        simpa [add_comm] using hsecond'
      rw [Finset.sum_insert ha, Finset.sum_insert ha, Finset.sum_insert ha]
      calc
        (f a + (∑ i ∈ s, f i)) * (g a + (∑ i ∈ s, g i)) +
            (g a + (∑ i ∈ s, g i)) * (f a + (∑ i ∈ s, f i)) =
          (f a * g a + g a * f a) +
            (f a * (∑ i ∈ s, g i) + (∑ i ∈ s, g i) * f a) +
            ((∑ i ∈ s, f i) * g a + g a * (∑ i ∈ s, f i)) +
            ((∑ i ∈ s, f i) * (∑ i ∈ s, g i) +
              (∑ i ∈ s, g i) * (∑ i ∈ s, f i)) := by noncomm_ring
        _ = (f a * g a + g a * f a) +
            ∑ i ∈ s, (f i * g i + g i * f i) := by
              rw [hfirst, hsecond, hrest]
              abel

/-- Dressing by an involution preserves square-zero when the site operator
commutes with the string. This is the local nilpotency step for an internal
Jordan–Wigner chain. -/
theorem jw_dressing_preserves_square_zero (s x : A)
    (hs : s * s = 1) (hsx : x * s = s * x) (hx : x * x = 0) :
    (s * x) * (s * x) = 0 := by
  calc
    (s * x) * (s * x) = s * (x * s) * x := by noncomm_ring
    _ = s * (s * x) * x := by rw [hsx]
    _ = (s * s) * (x * x) := by noncomm_ring
    _ = 0 := by rw [hs, hx]; simp

/-- If a site-1 odd operator anticommutes with the parity string and commutes
with a site-2 operator, its anticommutator with the string-dressed site-2
operator vanishes. This isolates the operator algebra needed for the
Jordan–Wigner cross-site sign. -/
theorem jw_cross_site_anticommutator_zero (n s x : A)
    (hns : n * s = -(s * n)) (hnx : n * x = x * n) :
    n * (s * x) + (s * x) * n = 0 := by
  rw [jw_commutator_to_anticommutator s n x hns, hnx]
  simp

/-- Two-site Jordan–Wigner closure, stated entirely inside one associative
ring. The site-2 modes commute with the parity string and square to zero;
the dressed modes anticommute with the site-1 modes. Consequently the total
modes remain square-zero, and the paired anticommutator is additive when the
opposite cross-site anticommutators vanish as well. -/
theorem jw_two_site_chain_closure (s x₁ y₁ x₂ y₂ : A)
    (hs : s * s = 1)
    (hxs : x₂ * s = s * x₂) (hys : y₂ * s = s * y₂)
    (hx₁ : x₁ * x₁ = 0) (hy₁ : y₁ * y₁ = 0)
    (hx₂ : x₂ * x₂ = 0) (hy₂ : y₂ * y₂ = 0)
    (hpx : x₁ * (s * x₂) + (s * x₂) * x₁ = 0)
    (hpy : y₁ * (s * y₂) + (s * y₂) * y₁ = 0)
    (hcross₁ : x₁ * (s * y₂) + (s * y₂) * x₁ = 0)
    (hcross₂ : (s * x₂) * y₁ + y₁ * (s * x₂) = 0) :
    (s * x₂) * (s * x₂) = 0 ∧
    (s * y₂) * (s * y₂) = 0 ∧
    (x₁ + s * x₂) * (x₁ + s * x₂) = 0 ∧
    (y₁ + s * y₂) * (y₁ + s * y₂) = 0 ∧
    (x₁ + s * x₂) * (y₁ + s * y₂) +
        (y₁ + s * y₂) * (x₁ + s * x₂) =
      (x₁ * y₁ + y₁ * x₁) + (x₂ * y₂ + y₂ * x₂) := by
  have hdx := jw_dressing_preserves_square_zero s x₂ hs hxs hx₂
  have hdy := jw_dressing_preserves_square_zero s y₂ hs hys hy₂
  have hxt := jw_two_site_sum_square_zero x₁ (s * x₂) hx₁ hdx hpx
  have hyt := jw_two_site_sum_square_zero y₁ (s * y₂) hy₁ hdy hpy
  have hmetric := jw_two_site_metric_additive x₁ y₁ (s * x₂) (s * y₂)
    hcross₁ hcross₂
  have hsite : (s * x₂) * (s * y₂) + (s * y₂) * (s * x₂) =
      x₂ * y₂ + y₂ * x₂ := by
    calc
      (s * x₂) * (s * y₂) + (s * y₂) * (s * x₂) =
          s * (x₂ * s) * y₂ + s * (y₂ * s) * x₂ := by noncomm_ring
      _ = s * (s * x₂) * y₂ + s * (s * y₂) * x₂ := by rw [hxs, hys]
      _ = (s * s) * (x₂ * y₂) + (s * s) * (y₂ * x₂) := by noncomm_ring
      _ = x₂ * y₂ + y₂ * x₂ := by rw [hs]; simp
  rw [hsite] at hmetric
  exact ⟨hdx, hdy, hxt, hyt, hmetric⟩

/-- Peirce-specialized two-site Jordan–Wigner closure. The first-site modes
are the two off-diagonal corners of `p`; the second-site modes commute with
the cut, the first-site corners, and each other as stipulated below. The
grading string then supplies the cross-site anticommutators, so these need not
be assumed separately. -/
theorem jw_peirce_two_site_chain_closure (hp : IsIdempotent p)
    (a c x₂ y₂ : A)
    (hx₂ : x₂ * x₂ = 0) (hy₂ : y₂ * y₂ = 0)
    (hpx₂ : p * x₂ = x₂ * p) (hpy₂ : p * y₂ = y₂ * p)
    (hxx : peirce10 p a * x₂ = x₂ * peirce10 p a)
    (hxy : peirce10 p a * y₂ = y₂ * peirce10 p a)
    (hyx : peirce01 p c * x₂ = x₂ * peirce01 p c)
    (hyy : peirce01 p c * y₂ = y₂ * peirce01 p c) :
    (grading p * x₂) * (grading p * x₂) = 0 ∧
    (grading p * y₂) * (grading p * y₂) = 0 ∧
    (peirce10 p a + grading p * x₂) *
        (peirce10 p a + grading p * x₂) = 0 ∧
    (peirce01 p c + grading p * y₂) *
        (peirce01 p c + grading p * y₂) = 0 ∧
    (peirce10 p a + grading p * x₂) *
        (peirce01 p c + grading p * y₂) +
      (peirce01 p c + grading p * y₂) *
        (peirce10 p a + grading p * x₂) =
      interbandMetric p a c + (x₂ * y₂ + y₂ * x₂) := by
  have hp' : p * p = p := hp
  have hq' : compIdempotent p * compIdempotent p = compIdempotent p :=
    compIdempotent_isIdempotent hp
  have hpq : p * compIdempotent p = 0 := compIdempotent_orthogonal hp
  have hqp : compIdempotent p * p = 0 := compIdempotent_orthogonal_rev hp
  have hS : grading p * grading p = 1 := grading_sq p hp
  have hSx : x₂ * grading p = grading p * x₂ := by
    simp only [grading, compIdempotent, mul_sub, sub_mul, one_mul, mul_one]
    rw [hpx₂]
  have hSy : y₂ * grading p = grading p * y₂ := by
    simp only [grading, compIdempotent, mul_sub, sub_mul, one_mul, mul_one]
    rw [hpy₂]
  have h10pL : p * peirce10 p a = peirce10 p a := by
    unfold peirce10
    calc
      p * (p * a * compIdempotent p) = (p * p) * a * compIdempotent p := by noncomm_ring
      _ = p * a * compIdempotent p := by rw [hp']
  have h10qL : compIdempotent p * peirce10 p a = 0 := by
    unfold peirce10
    calc
      compIdempotent p * (p * a * compIdempotent p) =
          (compIdempotent p * p) * a * compIdempotent p := by noncomm_ring
      _ = 0 := by rw [hqp]; simp
  have h10pR : peirce10 p a * p = 0 := by
    unfold peirce10
    calc
      (p * a * compIdempotent p) * p = p * a * (compIdempotent p * p) := by noncomm_ring
      _ = 0 := by rw [hqp]; simp
  have h10qR : peirce10 p a * compIdempotent p = peirce10 p a := by
    unfold peirce10
    calc
      (p * a * compIdempotent p) * compIdempotent p =
          p * a * (compIdempotent p * compIdempotent p) := by noncomm_ring
      _ = p * a * compIdempotent p := by rw [hq']
  have h01pL : p * peirce01 p c = 0 := by
    unfold peirce01
    calc
      p * (compIdempotent p * c * p) = (p * compIdempotent p) * c * p := by noncomm_ring
      _ = 0 := by rw [hpq]; simp
  have h01qL : compIdempotent p * peirce01 p c = peirce01 p c := by
    unfold peirce01
    calc
      compIdempotent p * (compIdempotent p * c * p) =
          (compIdempotent p * compIdempotent p) * c * p := by noncomm_ring
      _ = compIdempotent p * c * p := by rw [hq']
  have h01pR : peirce01 p c * p = peirce01 p c := by
    unfold peirce01
    calc
      (compIdempotent p * c * p) * p = compIdempotent p * c * (p * p) := by noncomm_ring
      _ = compIdempotent p * c * p := by rw [hp']
  have h01qR : peirce01 p c * compIdempotent p = 0 := by
    unfold peirce01
    calc
      (compIdempotent p * c * p) * compIdempotent p =
          compIdempotent p * c * (p * compIdempotent p) := by noncomm_ring
      _ = 0 := by rw [hpq]; simp
  have h10L : grading p * peirce10 p a = peirce10 p a := by
    unfold grading
    rw [sub_mul, h10pL, h10qL, sub_zero]
  have h10R : peirce10 p a * grading p = -peirce10 p a := by
    unfold grading
    rw [mul_sub, h10pR, h10qR, zero_sub]
  have h01L : grading p * peirce01 p c = -peirce01 p c := by
    unfold grading
    rw [sub_mul, h01pL, h01qL, zero_sub]
  have h01R : peirce01 p c * grading p = peirce01 p c := by
    unfold grading
    rw [mul_sub, h01pR, h01qR, sub_zero]
  have h10S : peirce10 p a * grading p =
      -(grading p * peirce10 p a) := by rw [h10L, h10R]
  have h01S : peirce01 p c * grading p =
      -(grading p * peirce01 p c) := by rw [h01L, h01R, neg_neg]
  have hx₁ : peirce10 p a * peirce10 p a = 0 := peirce10_square_zero hp a
  have hy₁ : peirce01 p c * peirce01 p c = 0 := peirce01_square_zero hp c
  have hpx : peirce10 p a * (grading p * x₂) +
      (grading p * x₂) * peirce10 p a = 0 :=
    jw_cross_site_anticommutator_zero _ _ _ h10S hxx
  have hpy : peirce01 p c * (grading p * y₂) +
      (grading p * y₂) * peirce01 p c = 0 :=
    jw_cross_site_anticommutator_zero _ _ _ h01S hyy
  have hcross₁ : peirce10 p a * (grading p * y₂) +
      (grading p * y₂) * peirce10 p a = 0 :=
    jw_cross_site_anticommutator_zero _ _ _ h10S hxy
  have hcross₂ : (grading p * x₂) * peirce01 p c +
      peirce01 p c * (grading p * x₂) = 0 := by
    have h := jw_cross_site_anticommutator_zero _ _ _ h01S hyx
    simpa only [add_comm] using h
  have hclosure := jw_two_site_chain_closure (grading p)
    (peirce10 p a) (peirce01 p c) x₂ y₂ hS hSx hSy hx₁ hy₁ hx₂ hy₂
    hpx hpy hcross₁ hcross₂
  simpa only [interbandMetric] using hclosure

/-- Multiplication table for the four operators built from two square-zero
interband corners. The clock anticommutes with both shifts; the ordered mixed
products retain the operator weights `Φ Σ = -V J` and `J Σ = -V Φ`. -/
theorem interband_sylvester_table (hp : IsIdempotent p) (a c : A) :
    interbandSum p a c * interbandSum p a c = interbandMetric p a c ∧
    interbandDifference p a c * interbandDifference p a c =
      -interbandMetric p a c ∧
    interbandDifference p a c * interbandSum p a c =
      interbandCurvature p a c ∧
    interbandSum p a c * interbandDifference p a c =
      -interbandCurvature p a c ∧
    interbandCurvature p a c * interbandCurvature p a c =
      interbandMetric p a c * interbandMetric p a c ∧
    interbandSum p a c * interbandCurvature p a c =
      -(interbandMetric p a c * interbandDifference p a c) ∧
    interbandSum p a c * interbandCurvature p a c =
      -(interbandCurvature p a c * interbandSum p a c) ∧
    interbandDifference p a c * interbandCurvature p a c =
      -(interbandMetric p a c * interbandSum p a c) ∧
    interbandDifference p a c * interbandCurvature p a c =
      -(interbandCurvature p a c * interbandDifference p a c) := by
  have hn := peirce10_square_zero hp a
  have hm := peirce01_square_zero hp c
  have hnnm : peirce10 p a * (peirce10 p a * peirce01 p c) = 0 := by
    rw [← mul_assoc, hn]
    simp
  have hmmn : peirce01 p c * (peirce01 p c * peirce10 p a) = 0 := by
    rw [← mul_assoc, hm]
    simp
  dsimp [interbandSum, interbandDifference, interbandMetric,
    interbandCurvature]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    noncomm_ring [hn, hm, hnnm, hmmn]

end InfoGeometry.Algebra.PeirceDeWittChiralSplit
