/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.SteinbergBraidDefectSpine
import Mathlib.Tactic.NoncommRing

/-!
# Graded Peirce differentials in an associative operator ring

This module isolates the algebraic grading and superderivation identities
suggested by the AI Studio transcript. The carrier is an arbitrary
associative unital ring with an idempotent; no commutative or scalar model is
used. The mixed ordinary/dual differential identity is stated with its exact
Jordan action. In particular, it is not identified with the commutator by
`Σ`.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceGradedSuperderivations

open PureNonCommutativeOperatorSpine

variable {B : Type*} [Ring B]

/-- A square-zero Leibniz differential on an associative ring. -/
def IsSquareZeroRingDifferential (d : B →+ B) : Prop :=
  (∀ x y : B, d (x * y) = d x * y + x * d y) ∧ ∀ x : B, d (d x) = 0

theorem squareZero_differential_not_Peirce_commutator_on_nonzero_odd
    {d : B →+ B} (hd : IsSquareZeroRingDifferential d)
    {P X : B} (hP : P * P = P) (hdP : d P = 0)
    (hodd₁ : P * X * P = 0)
    (hodd₀ : (1 - P) * X * (1 - P) = 0)
    (hcompat : d X = P * X - X * P) : X = 0 := by
  have hodd₀_expand : X - P * X - X * P + P * X * P = 0 := by
    calc
      X - P * X - X * P + P * X * P = (1 - P) * X * (1 - P) := by
        noncomm_ring
      _ = 0 := hodd₀
  rw [hodd₁] at hodd₀_expand
  have hodd₀_linear : X - P * X - X * P = 0 := by simpa using hodd₀_expand
  have hdecomp : X = P * X + X * P := by
    calc
      X = (X - P * X - X * P) + P * X + X * P := by abel
      _ = P * X + X * P := by rw [hodd₀_linear]; abel
  have hsecond : d (P * X - X * P) = 0 := by
    calc
      d (P * X - X * P) = d (d X) := by rw [hcompat]
      _ = 0 := hd.2 X
  rw [map_sub, hd.1 P X, hd.1 X P, hdP, zero_mul, mul_zero, hcompat] at hsecond
  simp only [zero_add, add_zero] at hsecond
  have hcomm_sq : P * (P * X - X * P) - (P * X - X * P) * P = X := by
    calc
      P * (P * X - X * P) - (P * X - X * P) * P =
          P * P * X - P * X * P - P * X * P + X * P * P := by noncomm_ring
      _ = P * X - P * X * P - P * X * P + X * P := by
        rw [hP, mul_assoc X P P, hP]
      _ = P * X + X * P := by rw [hodd₁]; module
      _ = X := hdecomp.symm
  rw [hcomm_sq] at hsecond
  exact hsecond

/-- The closed-cut obstruction needs only the two Leibniz rules involving the
cut and the tested odd element. This form applies to a graded differential:
when `P` is even and `d P = 0`, both local rules reduce to the displayed
identities even though `d` is not an ordinary derivation on the whole ring. -/
theorem squareZero_local_differential_not_Peirce_commutator_on_nonzero_odd
    {d : B →+ B} {P X : B}
    (hSq : ∀ Y : B, d (d Y) = 0)
    (hP : P * P = P) (hdP : d P = 0)
    (hodd₁ : P * X * P = 0)
    (hodd₀ : (1 - P) * X * (1 - P) = 0)
    (hPX : d (P * X) = d P * X + P * d X)
    (hXP : d (X * P) = d X * P + X * d P)
    (hcompat : d X = P * X - X * P) : X = 0 := by
  have hodd₀_expand : X - P * X - X * P + P * X * P = 0 := by
    calc
      X - P * X - X * P + P * X * P = (1 - P) * X * (1 - P) := by
        noncomm_ring
      _ = 0 := hodd₀
  rw [hodd₁] at hodd₀_expand
  have hodd₀_linear : X - P * X - X * P = 0 := by simpa using hodd₀_expand
  have hdecomp : X = P * X + X * P := by
    calc
      X = (X - P * X - X * P) + P * X + X * P := by abel
      _ = P * X + X * P := by rw [hodd₀_linear]; abel
  have hsecond : d (P * X - X * P) = 0 := by
    calc d (P * X - X * P) = d (d X) := by rw [← hcompat]
      _ = 0 := hSq X
  rw [map_sub, hPX, hXP, hdP, zero_mul, mul_zero] at hsecond
  rw [hcompat] at hsecond
  have hcomm_sq : P * (P * X - X * P) - (P * X - X * P) * P = X := by
    calc
      P * (P * X - X * P) - (P * X - X * P) * P =
          P * P * X - P * X * P - P * X * P + X * P * P := by noncomm_ring
      _ = P * X - P * X * P - P * X * P + X * P := by
        rw [hP, mul_assoc X P P, hP]
      _ = P * X + X * P := by rw [hodd₁]; module
      _ = X := hdecomp.symm
  simpa [hcomm_sq] using hsecond

section AbstractGrading

/-- Conjugation by a grading element. -/
def twist (S X : B) : B := S * X * S

theorem twist_add (S X Y : B) : twist S (X + Y) = twist S X + twist S Y := by
  simp only [twist, mul_add, add_mul]

theorem twist_sub (S X Y : B) : twist S (X - Y) = twist S X - twist S Y := by
  simp only [twist, mul_sub, sub_mul]

theorem twist_mul {S : B} (hS : S * S = 1) (X Y : B) :
    twist S (X * Y) = twist S X * twist S Y := by
  simp only [twist, mul_assoc]
  rw [← mul_assoc S S (Y * S), hS, one_mul]

theorem twist_twist {S : B} (hS : S * S = 1) (X : B) :
    twist S (twist S X) = X := by
  simp only [twist]
  calc
    S * (S * X * S) * S = (S * S) * X * (S * S) := by noncomm_ring
    _ = X := by rw [hS]; simp

theorem twist_odd {S N : B} (hS : S * S = 1) (hSN : S * N = -(N * S)) :
    twist S N = -N := by
  simp only [twist]
  calc
    S * N * S = -(N * S) * S := by rw [hSN]
    _ = -(N * (S * S)) := by noncomm_ring
    _ = -N := by rw [hS]; simp

/-- Odd inner graded differential `d_N(X) = N X - (S X S) N`. -/
def oddDiff (S N X : B) : B := N * X - twist S X * N

/-- Dual graded differential with the opposite sign in its twist term. -/
def oddDiffBar (S N X : B) : B := N * X + twist S X * N

theorem oddDiff_square_zero {S N : B} (hS : S * S = 1) (hN : N * N = 0)
    (hSN : S * N = -(N * S)) (X : B) :
    oddDiff S N (oddDiff S N X) = 0 := by
  unfold oddDiff
  simp only [twist_sub, twist_mul hS, twist_odd hS hSN, twist_twist hS]
  noncomm_ring [hN]
  rw [← mul_assoc, hN, zero_mul]

theorem oddDiffBar_square_zero {S N : B} (hS : S * S = 1) (hN : N * N = 0)
    (hSN : S * N = -(N * S)) (X : B) :
    oddDiffBar S N (oddDiffBar S N X) = 0 := by
  unfold oddDiffBar
  simp only [twist_add, twist_mul hS, twist_odd hS hSN, twist_twist hS]
  noncomm_ring [hN]
  rw [← mul_assoc, hN, zero_mul]

theorem oddDiff_graded_leibniz {S N : B} (hS : S * S = 1) (X Y : B) :
    oddDiff S N (X * Y) = oddDiff S N X * Y + twist S X * oddDiff S N Y := by
  unfold oddDiff
  rw [twist_mul hS]
  noncomm_ring

/-- An odd differential anticommutes with its grading involution. -/
theorem oddDiff_twist_anticommute {S N : B} (hS : S * S = 1)
    (hSN : S * N = -(N * S)) (X : B) :
    twist S (oddDiff S N X) = -oddDiff S N (twist S X) := by
  unfold oddDiff
  simp only [twist_sub, twist_mul hS, twist_odd hS hSN, twist_twist hS]
  noncomm_ring

theorem oddDiff_pair {S N M : B} (hS : S * S = 1)
    (hSN : S * N = -(N * S)) (hSM : S * M = -(M * S)) (X : B) :
    oddDiff S N (oddDiff S M X) + oddDiff S M (oddDiff S N X) =
      (N * M + M * N) * X - X * (N * M + M * N) := by
  unfold oddDiff
  simp only [twist_sub, twist_mul hS, twist_odd hS hSM, twist_twist hS,
    twist_sub, twist_mul hS, twist_odd hS hSN, twist_twist hS]
  noncomm_ring

/-- The ordinary/dual mixed anticommutator is the Jordan action of `{N,M}`. -/
theorem oddDiff_oddDiffBar_pair {S N M : B} (hS : S * S = 1)
    (hSN : S * N = -(N * S)) (hSM : S * M = -(M * S)) (X : B) :
    oddDiff S N (oddDiffBar S M X) + oddDiffBar S M (oddDiff S N X) =
      (N * M + M * N) * X + X * (N * M + M * N) := by
  unfold oddDiff oddDiffBar
  simp only [twist_add, twist_mul hS, twist_odd hS hSM, twist_twist hS,
    twist_sub, twist_mul hS, twist_odd hS hSN, twist_twist hS]
  noncomm_ring

end AbstractGrading

section PeirceSpecialization

variable {P : B} (hP : P * P = P) (A C X Y : B)

/-- The Peirce grading parity automorphism induced by `2P - 1`. -/
def parity (P X : B) : B := twist (invS P) X

def differentialPlus (P A X : B) : B :=
  oddDiff (invS P) (conePlus P A) X

def differentialMinus (P C X : B) : B :=
  oddDiff (invS P) (coneMinus P C) X

def differentialPlusBar (P A X : B) : B :=
  oddDiffBar (invS P) (conePlus P A) X

def differentialMinusBar (P C X : B) : B :=
  oddDiffBar (invS P) (coneMinus P C) X

def differentialPhi (P A C X : B) : B :=
  differentialPlus P A X + differentialMinus P C X

def differentialJ (P A C X : B) : B :=
  differentialPlus P A X - differentialMinus P C X

theorem differentialPlus_square_zero (hP : P * P = P) :
    differentialPlus P A (differentialPlus P A X) = 0 := by
  unfold differentialPlus
  apply oddDiff_square_zero (invS_sq hP) (conePlus_sq_zero hP A)
  rw [invS_mul_conePlus hP A, conePlus_mul_invS hP A]
  simp

theorem differentialMinus_square_zero (hP : P * P = P) :
    differentialMinus P C (differentialMinus P C X) = 0 := by
  unfold differentialMinus
  apply oddDiff_square_zero (invS_sq hP) (coneMinus_sq_zero hP C)
  rw [invS_mul_coneMinus hP C, coneMinus_mul_invS hP C]

theorem differentialPlusBar_square_zero (hP : P * P = P) :
    differentialPlusBar P A (differentialPlusBar P A X) = 0 := by
  unfold differentialPlusBar
  apply oddDiffBar_square_zero (invS_sq hP) (conePlus_sq_zero hP A)
  rw [invS_mul_conePlus hP A, conePlus_mul_invS hP A]
  simp

theorem differentialMinusBar_square_zero (hP : P * P = P) :
    differentialMinusBar P C (differentialMinusBar P C X) = 0 := by
  unfold differentialMinusBar
  apply oddDiffBar_square_zero (invS_sq hP) (coneMinus_sq_zero hP C)
  rw [invS_mul_coneMinus hP C, coneMinus_mul_invS hP C]

theorem differentialPlus_graded_leibniz (hP : P * P = P) :
    differentialPlus P A (X * Y) =
      differentialPlus P A X * Y + parity P X * differentialPlus P A Y := by
  unfold differentialPlus parity
  exact oddDiff_graded_leibniz (invS_sq hP) X Y

theorem differentialMinus_graded_leibniz (hP : P * P = P) :
    differentialMinus P C (X * Y) =
      differentialMinus P C X * Y + parity P X * differentialMinus P C Y := by
  unfold differentialMinus parity
  exact oddDiff_graded_leibniz (invS_sq hP) X Y

/-- The upper-corner Peirce differential is odd for the involution `parity`. -/
theorem differentialPlus_parity_odd (hP : P * P = P) :
    parity P (differentialPlus P A X) =
      -differentialPlus P A (parity P X) := by
  unfold differentialPlus parity
  apply oddDiff_twist_anticommute (invS_sq hP)
  rw [invS_mul_conePlus hP A, conePlus_mul_invS hP A]
  simp

/-- The lower-corner Peirce differential is odd for the involution `parity`. -/
theorem differentialMinus_parity_odd (hP : P * P = P) :
    parity P (differentialMinus P C X) =
      -differentialMinus P C (parity P X) := by
  unfold differentialMinus parity
  apply oddDiff_twist_anticommute (invS_sq hP)
  rw [invS_mul_coneMinus hP C, coneMinus_mul_invS hP C]

/-- The total Peirce differential is odd for the grading involution. -/
theorem differentialPhi_parity_odd (hP : P * P = P) :
    parity P (differentialPhi P A C X) =
      -differentialPhi P A C (parity P X) := by
  unfold differentialPhi
  calc parity P (differentialPlus P A X + differentialMinus P C X)
      = parity P (differentialPlus P A X) +
          parity P (differentialMinus P C X) := by
            unfold parity
            exact twist_add (invS P) _ _
    _ = -differentialPlus P A (parity P X) -
          differentialMinus P C (parity P X) := by
            rw [differentialPlus_parity_odd (P := P) (A := A) (X := X) hP,
              differentialMinus_parity_odd (P := P) (C := C) (X := X) hP]
            abel
    _ = -differentialPhi P A C (parity P X) := by
          unfold differentialPhi
          abel

/-- The anticommutator of the two Peirce differentials is the inner
commutator by the anticommutator of the ordered corners, namely `V`. -/
theorem differentialPlus_differentialMinus_pair (hP : P * P = P) :
    differentialPlus P A (differentialMinus P C X) +
      differentialMinus P C (differentialPlus P A X) =
        PureNonCommutativeOperatorSpine.comm (genV P A C) X := by
  unfold differentialPlus differentialMinus
  have hpair := oddDiff_pair (invS_sq hP)
    (by rw [invS_mul_conePlus hP A, conePlus_mul_invS hP A]; simp)
    (by rw [invS_mul_coneMinus hP C, coneMinus_mul_invS hP C]) X
  simpa [PureNonCommutativeOperatorSpine.comm, genV, anticomm] using hpair

/-- The ordinary/dual Peirce differential anticommutator is the Jordan
action of `V`; this is distinct from the commutator identity above. -/
theorem differentialPlus_differentialMinusBar_pair (hP : P * P = P) :
    differentialPlus P A (differentialMinusBar P C X) +
      differentialMinusBar P C (differentialPlus P A X) =
        genV P A C * X + X * genV P A C := by
  unfold differentialPlus differentialMinusBar
  have hpair := oddDiff_oddDiffBar_pair (invS_sq hP)
    (by rw [invS_mul_conePlus hP A, conePlus_mul_invS hP A]; simp)
    (by rw [invS_mul_coneMinus hP C, coneMinus_mul_invS hP C]) X
  simpa [genV, anticomm] using hpair

end PeirceSpecialization

end InfoGeometry.OperatorAlgebra.PeirceGradedSuperderivations
