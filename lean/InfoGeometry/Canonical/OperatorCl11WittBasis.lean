import Mathlib.Tactic

/-!
# The abstract operator `Cl(1,1)` Witt packet

This file records the noncommutative operator theorem behind the concrete
matrix and doubled-carrier realizations.  The coefficients are elements of an
arbitrary associative ring; only the rational scalar `1 / 2` is supplied by
the algebra structure.
-/

variable {A : Type*} [Ring A] [Algebra ℚ A]

namespace InfoGeometry.Canonical.OperatorCl11WittBasis

class OperatorCl11 (Γ J : A) : Prop where
  gamma_sq : Γ * Γ = 1
  exchange_sq : J * J = 1
  exchange_gamma_anticomm : J * Γ = - (Γ * J)

variable {Γ J : A} [hCl : OperatorCl11 Γ J]

def half : A := algebraMap ℚ A (1 / 2)

def phase (Γ J : A) : A := J * Γ

def wittPlus (Γ J : A) : A := half * (Γ + phase Γ J)

def wittMinus (Γ J : A) : A := half * (Γ - phase Γ J)

lemma half_sq : half (A := A) * half (A := A) = algebraMap ℚ A (1 / 4) := by
  unfold half
  rw [← map_mul]
  norm_num

lemma quarter_four :
    algebraMap ℚ A (1 / 4) * (1 + 1 + 1 + 1) = 1 := by
  have hfour : (1 + 1 + 1 + 1 : A) = algebraMap ℚ A 4 := by
    norm_num
    exact (map_ofNat (algebraMap ℚ A) 4).symm
  rw [hfour, ← map_mul]
  norm_num

omit [Algebra ℚ A] in
lemma gamma_mul_exchange : Γ * J = -(J * Γ) := by
  have h := congrArg Neg.neg hCl.exchange_gamma_anticomm
  simpa using h.symm

omit [Algebra ℚ A] in
lemma phase_sq : phase Γ J * phase Γ J = -1 := by
  unfold phase
  have hGJ : Γ * J = -(J * Γ) := gamma_mul_exchange (Γ := Γ) (J := J)
  calc
    (J * Γ) * (J * Γ) = J * (Γ * J) * Γ := by simp only [mul_assoc]
    _ = J * (-(J * Γ)) * Γ := by rw [hGJ]
    _ = -(J * (J * Γ) * Γ) := by simp only [mul_neg, neg_mul]
    _ = -((J * J) * (Γ * Γ)) := by congr 1; noncomm_ring
    _ = -1 := by rw [hCl.exchange_sq, hCl.gamma_sq, one_mul]

/-! The reverse product is the hyperbolic (product-structure) direction. -/
omit [Algebra ℚ A] in
lemma gamma_phase_sq :
    (Γ * phase Γ J) * (Γ * phase Γ J) = 1 := by
  unfold phase
  have hGJ : Γ * J = -(J * Γ) := gamma_mul_exchange (Γ := Γ) (J := J)
  calc
    (Γ * (J * Γ)) * (Γ * (J * Γ)) =
        Γ * J * (Γ * Γ) * J * Γ := by simp only [mul_assoc]
    _ = Γ * J * 1 * J * Γ := by rw [hCl.gamma_sq]
    _ = Γ * J * J * Γ := by simp
    _ = Γ * (J * J) * Γ := by simp only [mul_assoc]
    _ = Γ * 1 * Γ := by rw [hCl.exchange_sq]
    _ = 1 := by simp [hCl.gamma_sq]

omit [Algebra ℚ A] in
lemma gamma_phase_anticomm : Γ * phase Γ J = -(phase Γ J * Γ) := by
  unfold phase
  have hGJ : Γ * J = -(J * Γ) := gamma_mul_exchange (Γ := Γ) (J := J)
  calc
    Γ * (J * Γ) = (Γ * J) * Γ := by simp only [mul_assoc]
    _ = (-(J * Γ)) * Γ := by rw [hGJ]
    _ = -((J * Γ) * Γ) := by simp only [neg_mul]

omit [Algebra ℚ A] in
lemma gamma_phase_add_phase_gamma :
    Γ * phase Γ J + phase Γ J * Γ = 0 := by
  rw [gamma_phase_anticomm]
  abel

omit [Algebra ℚ A] in
lemma gamma_add_phase_sq :
    (Γ + phase Γ J) * (Γ + phase Γ J) = 0 := by
  calc
    (Γ + phase Γ J) * (Γ + phase Γ J) =
        Γ * Γ + Γ * phase Γ J + phase Γ J * Γ +
          phase Γ J * phase Γ J := by noncomm_ring
    _ =
        Γ * Γ + (Γ * phase Γ J + phase Γ J * Γ) +
          phase Γ J * phase Γ J := by abel
    _ = 1 + 0 + -1 := by
      rw [hCl.gamma_sq, gamma_phase_add_phase_gamma, phase_sq]
    _ = 0 := by simp

omit [Algebra ℚ A] in
lemma gamma_sub_phase_sq :
    (Γ - phase Γ J) * (Γ - phase Γ J) = 0 := by
  calc
    (Γ - phase Γ J) * (Γ - phase Γ J) =
        Γ * Γ - Γ * phase Γ J - phase Γ J * Γ +
          phase Γ J * phase Γ J := by noncomm_ring
    _ =
        Γ * Γ - (Γ * phase Γ J + phase Γ J * Γ) +
          phase Γ J * phase Γ J := by abel
    _ = 1 - 0 + -1 := by
      rw [hCl.gamma_sq, gamma_phase_add_phase_gamma, phase_sq]
    _ = 0 := by simp

lemma half_comm (x : A) : half (A := A) * x = x * half (A := A) :=
  Algebra.commutes _ _

lemma half_scaled_mul (x y : A) :
    (half (A := A) * x) * (half (A := A) * y) =
      (half (A := A) * half (A := A)) * (x * y) := by
  calc
    (half * x) * (half * y) = half * (x * half) * y := by
      simp only [mul_assoc]
    _ = half * (half * x) * y := by rw [half_comm x]
    _ = (half * half) * (x * y) := by simp only [mul_assoc]

lemma wittPlus_sq : wittPlus Γ J * wittPlus Γ J = 0 := by
  unfold wittPlus
  calc
    (half * (Γ + phase Γ J)) * (half * (Γ + phase Γ J)) =
        (half * half) * ((Γ + phase Γ J) * (Γ + phase Γ J)) :=
      half_scaled_mul _ _
    _ = 0 := by rw [gamma_add_phase_sq, mul_zero]

lemma wittMinus_sq : wittMinus Γ J * wittMinus Γ J = 0 := by
  unfold wittMinus
  calc
    (half * (Γ - phase Γ J)) * (half * (Γ - phase Γ J)) =
        (half * half) * ((Γ - phase Γ J) * (Γ - phase Γ J)) :=
      half_scaled_mul _ _
    _ = 0 := by rw [gamma_sub_phase_sq, mul_zero]

omit [Algebra ℚ A] in
lemma gamma_sub_phase_mul_add_gamma_add_phase_mul :
    (Γ + phase Γ J) * (Γ - phase Γ J) +
        (Γ - phase Γ J) * (Γ + phase Γ J) = 1 + 1 + 1 + 1 := by
  calc
    (Γ + phase Γ J) * (Γ - phase Γ J) +
        (Γ - phase Γ J) * (Γ + phase Γ J) =
      (Γ * Γ - Γ * phase Γ J + phase Γ J * Γ - phase Γ J * phase Γ J) +
        (Γ * Γ + Γ * phase Γ J - phase Γ J * Γ -
          phase Γ J * phase Γ J) := by noncomm_ring
    _ =
        Γ * Γ + Γ * Γ - phase Γ J * phase Γ J -
          phase Γ J * phase Γ J := by noncomm_ring
    _ = 1 + 1 + 1 + 1 := by
      rw [hCl.gamma_sq, phase_sq (Γ := Γ) (J := J)]
      noncomm_ring

theorem witt_car :
    wittPlus Γ J * wittMinus Γ J +
        wittMinus Γ J * wittPlus Γ J = 1 := by
  unfold wittPlus wittMinus
  calc
    (half * (Γ + phase Γ J)) * (half * (Γ - phase Γ J)) +
        (half * (Γ - phase Γ J)) * (half * (Γ + phase Γ J)) =
        (half * half) *
          ((Γ + phase Γ J) * (Γ - phase Γ J) +
            (Γ - phase Γ J) * (Γ + phase Γ J)) := by
      rw [half_scaled_mul, half_scaled_mul, ← mul_add]
    _ = (half * half) * (1 + 1 + 1 + 1) := by
      rw [gamma_sub_phase_mul_add_gamma_add_phase_mul]
    _ = 1 := by rw [half_sq]; exact quarter_four

end InfoGeometry.Canonical.OperatorCl11WittBasis
