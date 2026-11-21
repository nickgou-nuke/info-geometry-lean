/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib

/-!
# All-scale Hodge–parabolic identities in an iterated matrix tower

The carrier here is the recursively iterated matrix ring `Tower A n`; no
Clifford-algebra universal property is asserted. The trace is the recursively
unnormalized matrix trace. The energy results are star-square identities in a
star ring, not positivity statements in an ordered cone.
-/

namespace InfoGeometry.Algebra.HodgeParabolicTower

universe u

@[reducible] def Tower (A : Type u) : ℕ → Type u
  | 0 => A
  | n + 1 => Matrix (Fin 2) (Fin 2) (Tower A n)

instance instRingTower {A : Type u} [Ring A] : ∀ n, Ring (Tower A n)
  | 0 => inferInstanceAs (Ring A)
  | n + 1 => by
      letI : Ring (Tower A n) := instRingTower n
      exact inferInstanceAs (Ring (Matrix (Fin 2) (Fin 2) (Tower A n)))

instance instStarRingTower {A : Type u} [Ring A] [StarRing A] :
    ∀ n, StarRing (Tower A n)
  | 0 => inferInstanceAs (StarRing A)
  | n + 1 => by
      letI : Ring (Tower A n) := instRingTower n
      letI : StarRing (Tower A n) := instStarRingTower n
      exact inferInstanceAs (StarRing (Matrix (Fin 2) (Fin 2) (Tower A n)))

variable {A : Type u} [Ring A]

def mat2 (a b c d : A) : Matrix (Fin 2) (Fin 2) A := fun i j =>
  match i, j with
  | 0, 0 => a
  | 0, 1 => b
  | 1, 0 => c
  | 1, 1 => d

omit [Ring A] in
@[simp] theorem mat2_00 (a b c d : A) : mat2 a b c d 0 0 = a := rfl
omit [Ring A] in
@[simp] theorem mat2_01 (a b c d : A) : mat2 a b c d 0 1 = b := rfl
omit [Ring A] in
@[simp] theorem mat2_10 (a b c d : A) : mat2 a b c d 1 0 = c := rfl
omit [Ring A] in
@[simp] theorem mat2_11 (a b c d : A) : mat2 a b c d 1 1 = d := rfl

omit [Ring A] in
theorem mat2_ext {M N : Matrix (Fin 2) (Fin 2) A}
    (h00 : M 0 0 = N 0 0) (h01 : M 0 1 = N 0 1)
    (h10 : M 1 0 = N 1 0) (h11 : M 1 1 = N 1 1) : M = N := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact h00
  · exact h01
  · exact h10
  · exact h11

theorem mat2_mul (a b c d e f g h : A) :
    mat2 a b c d * mat2 e f g h =
      mat2 (a * e + b * g) (a * f + b * h)
        (c * e + d * g) (c * f + d * h) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [mat2, Matrix.mul_apply, Fin.sum_univ_two]

theorem mat2_add (a b c d e f g h : A) :
    mat2 a b c d + mat2 e f g h = mat2 (a + e) (b + f) (c + g) (d + h) := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem mat2_sub (a b c d e f g h : A) :
    mat2 a b c d - mat2 e f g h = mat2 (a - e) (b - f) (c - g) (d - h) := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem mat2_one : (1 : Matrix (Fin 2) (Fin 2) A) = mat2 1 0 0 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem mat2_zero : mat2 (0 : A) 0 0 0 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

def cantorProj {A : Type u} [Ring A] : (n : ℕ) → Tower A n
  | 0 => 1
  | n + 1 => mat2 (cantorProj (A := A) n) 0 0 0

def chirality {A : Type u} [Ring A] : (n : ℕ) → Tower A n
  | 0 => 1
  | n + 1 => mat2 (chirality (A := A) n) 0 0 (-chirality (A := A) n)

def towerTrace : (n : ℕ) → Tower A n → A
  | 0, x => x
  | n + 1, M => towerTrace n (M 0 0) + towerTrace n (M 1 1)

def superTrace (n : ℕ) (M : Tower A n) : A :=
  towerTrace n (chirality (A := A) n * M)

@[simp] theorem towerTrace_zero : ∀ n, towerTrace (A := A) n (0 : Tower A n) = 0
  | 0 => rfl
  | n + 1 => by
      change towerTrace n (0 : Tower A n) + towerTrace n (0 : Tower A n) = 0
      simp [towerTrace_zero n]

theorem towerTrace_add : ∀ n (X Y : Tower A n),
    towerTrace (A := A) n (X + Y) = towerTrace n X + towerTrace n Y
  | 0, X, Y => rfl
  | n + 1, X, Y => by
      change towerTrace n (X 0 0 + Y 0 0) + towerTrace n (X 1 1 + Y 1 1) =
        (towerTrace n (X 0 0) + towerTrace n (X 1 1)) +
          (towerTrace n (Y 0 0) + towerTrace n (Y 1 1))
      rw [towerTrace_add n, towerTrace_add n]
      abel

theorem towerTrace_neg : ∀ n (X : Tower A n),
    towerTrace (A := A) n (-X) = -towerTrace n X
  | 0, X => rfl
  | n + 1, X => by
      change towerTrace n (-(X 0 0)) + towerTrace n (-(X 1 1)) =
        -(towerTrace n (X 0 0) + towerTrace n (X 1 1))
      rw [towerTrace_neg n, towerTrace_neg n]
      abel

theorem towerTrace_nsmul (n k : ℕ) (X : Tower A n) :
    towerTrace n (k • X) = k • towerTrace n X := by
  induction k with
  | zero => simp [towerTrace_zero]
  | succ k ih => rw [add_nsmul, one_nsmul, towerTrace_add, ih, add_nsmul, one_nsmul]

theorem cantorProj_idempotent : ∀ n,
    cantorProj (A := A) n * cantorProj n = cantorProj n
  | 0 => by simp [cantorProj]
  | n + 1 => by
      change mat2 (cantorProj (A := A) n) 0 0 0 *
          mat2 (cantorProj n) 0 0 0 = mat2 (cantorProj n) 0 0 0
      rw [mat2_mul]
      simp [cantorProj_idempotent n]

theorem cantorProj_selfAdjoint [StarRing A] : ∀ n,
    star (cantorProj (A := A) n) = cantorProj n
  | 0 => by simp [cantorProj]
  | n + 1 => by
      ext i j
      fin_cases i <;> fin_cases j
      all_goals simp [cantorProj, cantorProj_selfAdjoint n]

theorem cantorProj_trace (n : ℕ) : towerTrace (A := A) n (cantorProj n) = 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change towerTrace n (cantorProj n) + towerTrace n (0 : Tower A n) = 1
      simp [ih]

theorem chirality_cantorProj : ∀ n,
    chirality (A := A) n * cantorProj n = cantorProj n
  | 0 => by simp [chirality, cantorProj]
  | n + 1 => by
      change mat2 (chirality (A := A) n) 0 0 (-chirality n) *
          mat2 (cantorProj n) 0 0 0 = mat2 (cantorProj n) 0 0 0
      rw [mat2_mul]
      simp [chirality_cantorProj n]

section Hodge

def wittD (n : ℕ) : Tower A (n + 1) := mat2 0 (cantorProj (A := A) n) 0 0
def wittDelta (n : ℕ) : Tower A (n + 1) := mat2 0 0 (cantorProj (A := A) n) 0
def sigma (n : ℕ) : Tower A (n + 1) := wittD n + wittDelta n
def omega (n : ℕ) : Tower A (n + 1) := wittDelta n - wittD n
def gamma (n : ℕ) : Tower A (n + 1) := wittD n * wittDelta n - wittDelta n * wittD n
def nilpotent (n : ℕ) : Tower A (n + 1) := omega n - gamma n
def monodromy (n : ℕ) : Tower A (n + 1) := 1 + nilpotent n
def harmonicProjection (n : ℕ) : Tower A (n + 1) :=
  1 - (wittD n * wittDelta n + wittDelta n * wittD n)

theorem nilpotent_explicit (n : ℕ) :
    nilpotent (A := A) n =
      mat2 (-(cantorProj (A := A) n)) (-(cantorProj n)) (cantorProj n) (cantorProj n) := by
  have hP := cantorProj_idempotent (A := A) n
  simp [nilpotent, omega, gamma, wittD, wittDelta, mat2_mul, mat2_sub, hP]

theorem nilpotent_sq_zero (n : ℕ) :
    nilpotent (A := A) n * nilpotent n = 0 := by
  rw [nilpotent_explicit, mat2_mul]
  simpa using (mat2_zero (A := Tower A n))

theorem sigma_nilpotent_sigma (n : ℕ) :
    sigma (A := A) n * nilpotent n * sigma n = -nilpotent n := by
  have hP := cantorProj_idempotent (A := A) n
  unfold sigma wittD wittDelta
  rw [nilpotent_explicit, mat2_add, mat2_mul, mat2_mul]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mat2, hP]

theorem nilpotent_harmonic_zero (n : ℕ) :
    nilpotent (A := A) n *
      (1 - (wittD n * wittDelta n + wittDelta n * wittD n)) = 0 := by
  have hP := cantorProj_idempotent (A := A) n
  rw [nilpotent_explicit]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [wittD, wittDelta, mat2, Matrix.mul_apply, Fin.sum_univ_two, hP] <;> noncomm_ring [hP]

theorem monodromy_pow (n k : ℕ) :
    monodromy (A := A) n ^ k = 1 + k • nilpotent n := by
  induction k with
  | zero => simp [monodromy]
  | succ k ih =>
      rw [pow_succ, ih, monodromy, add_nsmul, one_nsmul]
      have hmul : (k • nilpotent (A := A) n) * nilpotent n = 0 := by
        rw [nsmul_eq_mul, mul_assoc, nilpotent_sq_zero, mul_zero]
      calc
        (1 + k • nilpotent (A := A) n) * (1 + nilpotent n) =
            1 + (k • nilpotent n + nilpotent n) +
              (k • nilpotent n) * nilpotent n := by noncomm_ring
        _ = 1 + (k • nilpotent n + nilpotent n) := by rw [hmul, add_zero]

theorem all_scales_hodge_parabolic_generator_properties (n k : ℕ) :
    nilpotent (A := A) n * nilpotent n = 0 ∧
    sigma (A := A) n * nilpotent n * sigma n = -nilpotent n ∧
    nilpotent n * harmonicProjection (A := A) n = 0 ∧
    monodromy (A := A) n ^ k = 1 + k • nilpotent n := by
  exact ⟨nilpotent_sq_zero n, sigma_nilpotent_sigma n,
    nilpotent_harmonic_zero n, monodromy_pow n k⟩

end Hodge

section Vacuum

def vacuumProjection (n : ℕ) : Tower A (n + 1) := cantorProj (A := A) (n + 1)
def coexactProjection (n : ℕ) : Tower A (n + 1) := wittDelta (A := A) n * wittD n

theorem vacuum_evacuation_and_coexact_iterate (n k : ℕ) :
    monodromy (A := A) n * vacuumProjection n = wittDelta (A := A) n ∧
    vacuumProjection n * monodromy (A := A) n * vacuumProjection n = 0 ∧
    coexactProjection n * monodromy (A := A) n ^ k * vacuumProjection n =
      k • wittDelta (A := A) n := by
  have hP := cantorProj_idempotent (A := A) n
  refine ⟨?_, ?_, ?_⟩
  · rw [monodromy, nilpotent_explicit]
    ext i j
    fin_cases i <;> fin_cases j
    all_goals simp [vacuumProjection, cantorProj, wittDelta, mat2,
      Matrix.mul_apply, Fin.sum_univ_two, hP] <;> noncomm_ring [hP]
  · rw [monodromy, nilpotent_explicit]
    ext i j
    fin_cases i <;> fin_cases j
    all_goals simp [vacuumProjection, cantorProj, mat2, Matrix.mul_apply,
      Fin.sum_univ_two, hP] <;> noncomm_ring [hP]
  · have hp : cantorProj (A := A) n * cantorProj n = cantorProj n := hP
    have hE : coexactProjection (A := A) n =
        mat2 0 0 0 (cantorProj (A := A) n) := by
      dsimp [coexactProjection, wittDelta, wittD]
      rw [mat2_mul]
      simp [hp]
    have hV : vacuumProjection (A := A) n =
        mat2 (cantorProj (A := A) n) 0 0 0 := rfl
    have hN := nilpotent_explicit (A := A) n
    have hzero : coexactProjection (A := A) n * vacuumProjection n = 0 := by
      rw [hE, hV, mat2_mul]
      simp
      exact mat2_zero
    have htransfer :
        coexactProjection (A := A) n * nilpotent n * vacuumProjection n =
          wittDelta n := by
      rw [hE, hN, hV, mat2_mul, mat2_mul]
      simp [wittDelta, hp]
    have h_expand :
        coexactProjection (A := A) n *
            ((1 : Tower A (n + 1)) + (k • nilpotent n)) * vacuumProjection n =
          coexactProjection n * vacuumProjection n +
            k • (coexactProjection n * nilpotent n * vacuumProjection n) := by
      calc
        coexactProjection n * ((1 : Tower A (n + 1)) + (k • nilpotent n)) *
            vacuumProjection n =
          (coexactProjection n * 1) * vacuumProjection n +
            (coexactProjection n * (k • nilpotent n)) * vacuumProjection n := by
              rw [mul_add, add_mul]
        _ = coexactProjection n * vacuumProjection n +
            k • (coexactProjection n * nilpotent n * vacuumProjection n) := by
              rw [mul_one, mul_smul_comm, smul_mul_assoc]
    rw [monodromy_pow]
    rw [h_expand, hzero, htransfer, zero_add]

end Vacuum

section StarEnergy

variable [StarRing A]

theorem mat2_star (a b c d : A) :
    star (mat2 a b c d) = mat2 (star a) (star c) (star b) (star d) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mat2]

theorem star_wittDelta_mul_wittDelta (n : ℕ) :
    star (wittDelta (A := A) n) * wittDelta n = vacuumProjection n := by
  have hp := cantorProj_selfAdjoint (A := A) n
  change star (mat2 (0 : Tower A n) 0 (cantorProj n) 0) *
      mat2 0 0 (cantorProj n) 0 = mat2 (cantorProj n) 0 0 0
  rw [mat2_star]
  simp only [star_zero, hp]
  rw [mat2_mul]
  simp [cantorProj_idempotent]

theorem coexact_leakage_star_square (n k : ℕ) :
    star (coexactProjection (A := A) n * monodromy n ^ k * vacuumProjection n) *
        (coexactProjection n * monodromy n ^ k * vacuumProjection n) =
      (k * k) • vacuumProjection n := by
  have hleak := (vacuum_evacuation_and_coexact_iterate (A := A) n k).2.2
  rw [hleak, star_nsmul, smul_mul_assoc, mul_smul_comm,
    star_wittDelta_mul_wittDelta, smul_smul]

/-- The finite-stage star-square splits algebraically into compressed vacuum
survival and coexact leakage. No order or positivity structure is assumed. -/
theorem monodromy_state_star_square_split (n k : ℕ) :
    let P := vacuumProjection (A := A) n
    let Q := monodromy (A := A) n ^ k
    star (Q * P) * (Q * P) =
      star (P * Q * P) * (P * Q * P) + (k * k) • P := by
  intro P Q
  have hP_idem := cantorProj_idempotent (A := A) n
  have h_co := (vacuum_evacuation_and_coexact_iterate (A := A) n k).2.2
  have h_del_sq : star (wittDelta (A := A) n) * wittDelta n = P := by
    change star (wittDelta (A := A) n) * wittDelta n =
      vacuumProjection (A := A) n
    exact star_wittDelta_mul_wittDelta (A := A) n
  have h_leak :
      star (coexactProjection (A := A) n * Q * P) *
        (coexactProjection n * Q * P) = (k * k) • P := by
    change star (coexactProjection (A := A) n * monodromy (A := A) n ^ k * P) *
      (coexactProjection n * monodromy n ^ k * P) = (k * k) • P
    rw [h_co, star_nsmul, smul_mul_assoc, mul_smul_comm, h_del_sq, smul_smul]
  rw [← h_leak]
  have h_decomp : Q * P = P * Q * P + k • wittDelta n := by
    dsimp [Q, P, vacuumProjection]
    rw [monodromy_pow]
    have hL : (1 + k • nilpotent (A := A) n) *
        cantorProj (A := A) (n + 1) =
        cantorProj (n + 1) + k • (nilpotent n * cantorProj (n + 1)) := by
      rw [add_mul, one_mul, smul_mul_assoc]
    have hR : cantorProj (A := A) (n + 1) *
        (1 + k • nilpotent n) * cantorProj (n + 1) =
        cantorProj (n + 1) + k •
          (cantorProj (n + 1) * nilpotent n * cantorProj (n + 1)) := by
      rw [mul_add, mul_one, mul_smul_comm, add_mul, smul_mul_assoc,
        cantorProj_idempotent (n + 1)]
    rw [hL, hR, add_assoc]
    congr 1
    rw [← smul_add]
    congr 1
    rw [nilpotent_explicit]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [cantorProj, wittDelta, Matrix.mul_apply, Fin.sum_univ_two,
        hP_idem]
  have h_orth1 : star (P * Q * P) * (k • wittDelta n) = 0 := by
    rw [mul_smul_comm]
    have h0 : star (P * Q * P) * wittDelta n = 0 := by
      dsimp [P, vacuumProjection]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [cantorProj, wittDelta, Matrix.mul_apply,
          Fin.sum_univ_two, cantorProj_selfAdjoint]
    rw [h0, smul_zero]
  have h_orth2 : star (k • wittDelta n) * (P * Q * P) = 0 := by
    rw [star_nsmul, smul_mul_assoc]
    have h0 : star (wittDelta n) * (P * Q * P) = 0 := by
      dsimp [P, vacuumProjection]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [cantorProj, wittDelta, Matrix.mul_apply,
          Fin.sum_univ_two, cantorProj_selfAdjoint]
    rw [h0, smul_zero]
  rw [h_decomp, star_add, mul_add, add_mul, add_mul, h_orth1, h_orth2]
  simp only [zero_add, add_zero]
  calc
    star (P * Q * P) * (P * Q * P) +
        star (k • wittDelta n) * (k • wittDelta n) =
        star (P * Q * P) * (P * Q * P) + (k * k) • P := by
          rw [star_nsmul, smul_mul_assoc, mul_smul_comm, h_del_sq, smul_smul]
    _ = star (P * Q * P) * (P * Q * P) +
          star (coexactProjection (A := A) n * Q * P) *
            (coexactProjection n * Q * P) := by rw [h_leak]

end StarEnergy

section Supertrace

theorem towerTrace_chirality_succ (n : ℕ) :
    towerTrace (A := A) (n + 1) (chirality (A := A) (n + 1)) = 0 := by
  change towerTrace n (chirality n) + towerTrace n (-chirality n) = 0
  rw [towerTrace_neg]
  abel

theorem superTrace_one_succ (n : ℕ) :
    superTrace (A := A) (n + 1) (1 : Tower A (n + 1)) = 0 := by
  unfold superTrace
  rw [mul_one]
  exact towerTrace_chirality_succ (A := A) n

theorem all_scales_trace_blindness_vs_supertrace_winding (n k : ℕ) :
    towerTrace (A := A) (n + 1) (nilpotent (A := A) n) = 0 ∧
    superTrace (A := A) (n + 1) (nilpotent n) = -(2 • (1 : A)) ∧
    superTrace (A := A) (n + 1) (monodromy (A := A) n ^ k) =
      -((2 * k) • (1 : A)) := by
  have hP := cantorProj_idempotent (A := A) n
  have h_super_nil :
      superTrace (A := A) (n + 1) (nilpotent (A := A) n) = -(2 • (1 : A)) := by
    change towerTrace n
      ((chirality (A := A) (n + 1) * nilpotent (A := A) n) 0 0) +
      towerTrace n ((chirality (A := A) (n + 1) * nilpotent (A := A) n) 1 1) = _
    rw [nilpotent_explicit]
    simp [chirality, mat2, Matrix.mul_apply, Fin.sum_univ_two,
      chirality_cantorProj, towerTrace_neg, cantorProj_trace]
    norm_num
  refine ⟨?_, h_super_nil, ?_⟩
  · rw [nilpotent_explicit]
    change towerTrace n
      (mat2 (-cantorProj n) (-(cantorProj n)) (cantorProj n) (cantorProj n) 0 0) +
      towerTrace n
        (mat2 (-cantorProj n) (-(cantorProj n)) (cantorProj n) (cantorProj n) 1 1) = 0
    simp [towerTrace_neg, cantorProj_trace]
  · rw [monodromy_pow]
    change towerTrace (n + 1)
      (chirality (A := A) (n + 1) * (1 + k • nilpotent n)) = _
    have h_lin : chirality (A := A) (n + 1) *
        (1 + k • nilpotent (A := A) n) =
        chirality (n + 1) * 1 +
          k • (chirality (n + 1) * nilpotent (A := A) n) := by
      rw [mul_add, mul_one, mul_smul_comm]
    rw [h_lin, towerTrace_add, towerTrace_nsmul]
    change superTrace (A := A) (n + 1) (1 : Tower A (n + 1)) +
        k • superTrace (A := A) (n + 1) (nilpotent (A := A) n) =
        -((2 * k) • (1 : A))
    rw [superTrace_one_succ, h_super_nil, zero_add]
    simp [nsmul_eq_mul]
    noncomm_ring

end Supertrace

end InfoGeometry.Algebra.HodgeParabolicTower
