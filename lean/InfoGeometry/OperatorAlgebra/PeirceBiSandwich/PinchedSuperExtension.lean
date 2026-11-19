/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.OperatorAlgebra.PeirceBiSandwich.Core

/-!
# Pinched vs. Ambient Super-Extension (`K₀ ≺ … ≺ K₉`)

Formalizes Pass 5 of the Epistemic Compilation (*Solve et Coagula*):
1. `DayRel`, `dayMul`, `dayStar`, and `day_congruence_iff_centralizer`:
   exact centralizer boundary `C_B(V)` where Day-convolution localization
   preserves multiplication and involution.
2. `integral_unitary_defect_law` and `on_shell_integral_weyl_reflection`:
   the universal integral unitary defect `u₀* u₀ - 1 = δ(V) = u₀ u₀* - 1`
   and global Weyl reflection `u₀ Σ u₀* = -Σ` over `ℤ`.
3. `centralizer_kills_odd_kkt_modes` and `parity_inverted_fermionic_supercharge`:
   `C_B(V)` annihilates odd KKT modes, while ambient parity-inverted blocks
   `Q₊ D₁ P_{0,+} + P_{0,-} D₂ Q₋` restore exact KKT grade `+1` and
   anticommute with `Γ_Σ = 2V - 1`.
4. `clifford8_parity_inversion_and_andreev_closure`:
   concrete `Mat₈(ℤ)` realization witnessing parity inversion, non-zero
   Morita spacetime translation `Q_odd² ≠ 0`, and Andreev retro-reflection
   `P₀ [Δ₋₂, Q_odd] Q₊ ≠ 0`.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceBiSandwich

/-- Day-convolution localization relation for `(k, X)` at denominator `s`. -/
def DayRel {B : Type*} [Ring B] (s : B) (p q : ℕ × B) : Prop :=
  ∃ m : ℕ, s ^ m * (s ^ q.1 * p.2) = s ^ m * (s ^ p.1 * q.2)

/-- Day-convolution product on `ℕ × B`. -/
def dayMul {B : Type*} [Ring B] (p q : ℕ × B) : ℕ × B := (p.1 + q.1, p.2 * q.2)

/-- Day-convolution involution on `ℕ × B`. -/
def dayStar {B : Type*} [Ring B] [StarRing B] (p : ℕ × B) : ℕ × B := (p.1, star p.2)

/-! ### Stage K₂: Exact Centralizer Boundary of Day-Convolution Congruence -/

/-- Under 3-sum `★`-faithfulness, `(0, 1) ~ (1, 1 + V)` and `(0, X) ~ (1, (1 + V) X)`
    hold universally, yet left-multiplying by `(0, X)` or applying `dayStar` preserves
    `DayRel (1 + V)` if and only if `X ∈ C_B(V)` (`comm V X = 0`). -/
theorem day_congruence_iff_centralizer {B : Type*} [Ring B] [StarRing B]
    {P A : B} (hP_star : star P = P)
    (hfaith3 : ∀ Y1 Y2 Y3 : B, star Y1 * Y1 + star Y2 * Y2 + star Y3 * Y3 = 0 → Y1 = 0)
    (X : B) :
    let V := casimirV P A (star A)
    let s := 1 + V
    DayRel s (0, 1) (1, s) ∧
    DayRel s (0, X) (1, s * X) ∧
    (DayRel s (dayMul (0, X) (0, 1)) (dayMul (0, X) (1, s)) ↔ comm V X = 0) ∧
    (DayRel s (dayStar (0, X)) (dayStar (1, s * X)) ↔ comm V X = 0) := by
  intro V s
  have hNp_star : star (Nplus P A) = Nminus P (star A) := by
    dsimp [Nplus, Nminus]; simp only [star_mul, star_sub, star_one, hP_star, mul_assoc]
  have hNm_star : star (Nminus P (star A)) = Nplus P A := by
    rw [← hNp_star, star_star]
  have hV_star : star V = V := by
    dsimp [V, casimirV, Qplus, Qminus]
    simp only [star_add, star_mul, hNp_star, hNm_star]
  have hs_star : star s = s := by
    dsimp [s]; rw [star_add, star_one, hV_star]
  have hs_cancel : ∀ Z : B, s * Z = 0 → Z = 0 := by
    intro Z hZ
    have hsum : star Z * Z +
        star (Nminus P (star A) * Z) * (Nminus P (star A) * Z) +
        star (Nplus P A * Z) * (Nplus P A * Z) = 0 := by
      calc star Z * Z +
             star (Nminus P (star A) * Z) * (Nminus P (star A) * Z) +
             star (Nplus P A * Z) * (Nplus P A * Z)
          = star Z * (s * Z) := by
            simp only [star_mul, hNm_star, hNp_star]
            dsimp [s, V, casimirV, Qplus, Qminus]; noncomm_ring
        _ = 0 := by rw [hZ, mul_zero]
    exact hfaith3 Z (Nminus P (star A) * Z) (Nplus P A * Z) hsum
  have hs_pow_cancel : ∀ (m : ℕ) (Z : B), s ^ m * Z = 0 → Z = 0 := by
    intro m
    induction m with
    | zero => intro Z hZ; simpa using hZ
    | succ k ih =>
      intro Z hZ
      rw [pow_succ', mul_assoc] at hZ
      exact ih Z (hs_cancel _ hZ)
  refine ⟨⟨0, by simp⟩, ⟨0, by simp⟩, ?_, ?_⟩
  · constructor
    · rintro ⟨m, hm⟩
      dsimp [dayMul] at hm
      simp only [pow_zero, pow_one, mul_one, one_mul] at hm
      have hsub : s ^ m * (s * X - X * s) = 0 := by rw [mul_sub, hm, sub_self]
      have hsX : s * X - X * s = 0 := hs_pow_cancel m _ hsub
      dsimp [comm, s] at hsX ⊢
      calc V * X - X * V = (1 + V) * X - X * (1 + V) := by noncomm_ring
        _ = 0 := hsX
    · intro hcomm
      refine ⟨0, ?_⟩
      dsimp [dayMul]
      simp only [pow_zero, pow_one, mul_one, one_mul]
      have hVX : V * X = X * V := sub_eq_zero.mp hcomm
      dsimp [s]
      calc (1 + V) * X = X + V * X := by noncomm_ring
        _ = X * (1 + V) := by rw [hVX]; noncomm_ring
  · constructor
    · rintro ⟨m, hm⟩
      dsimp [dayStar] at hm
      simp only [pow_zero, pow_one, one_mul, star_mul, hs_star] at hm
      have hsub : s ^ m * (s * star X - star X * s) = 0 := by rw [mul_sub, hm, sub_self]
      have hsXstar : s * star X = star X * s := sub_eq_zero.mp (hs_pow_cancel m _ hsub)
      have hsX : X * s = s * X := by
        calc X * s = star (s * star X) := by rw [star_mul, star_star, hs_star]
          _ = star (star X * s) := by rw [hsXstar]
          _ = s * X := by rw [star_mul, star_star, hs_star]
      dsimp [comm]
      calc V * X - X * V = s * X - X * s := by dsimp [s]; noncomm_ring
        _ = 0 := by rw [hsX, sub_self]
    · intro hcomm
      refine ⟨0, ?_⟩
      dsimp [dayStar]
      simp only [pow_zero, pow_one, one_mul, star_mul, hs_star]
      have hVX : V * X = X * V := sub_eq_zero.mp hcomm
      have hVstarX : V * star X = star X * V := by
        calc V * star X = star (X * V) := by rw [star_mul, hV_star]
          _ = star (V * X) := by rw [hVX]
          _ = star X * V := by rw [star_mul, hV_star]
      dsimp [s]
      calc (1 + V) * star X = star X + V * star X := by noncomm_ring
        _ = star X * (1 + V) := by rw [hVstarX]; noncomm_ring

/-! ### Stage K₃ & K₄: Integral Unitary Defect Law & Global Weyl Reflection -/

/-- Universal integral unitary defect law: `u₀* u₀ - 1 = δ(V) = u₀ u₀* - 1`
    in any `★`-ring. -/
theorem integral_unitary_defect_law {B : Type*} [Ring B] [StarRing B]
    {P A : B} (hP : delta P = 0) (hP_star : star P = P) :
    let u0 := uZero P A (star A)
    let V := casimirV P A (star A)
    star u0 * u0 - 1 = delta V ∧ u0 * star u0 - 1 = delta V := by
  intro u0 V
  have hNp_star : star (Nplus P A) = Nminus P (star A) := by
    dsimp [Nplus, Nminus]; simp only [star_mul, star_sub, star_one, hP_star, mul_assoc]
  have hNm_star : star (Nminus P (star A)) = Nplus P A := by
    rw [← hNp_star, star_star]
  have hV_star : star V = V := by
    dsimp [V, casimirV, Qplus, Qminus]
    simp only [star_add, star_mul, hNp_star, hNm_star]
  have hJ_star : star (jOp P A (star A)) = -jOp P A (star A) := by
    dsimp [jOp]; simp only [star_sub, hNp_star, hNm_star]; noncomm_ring
  have hu0_star : star u0 = 1 - V - jOp P A (star A) := by
    dsimp [u0, uZero, V]
    simp only [star_add, star_sub, star_one]
    rw [show star (casimirV P A (star A)) = casimirV P A (star A) from hV_star, hJ_star]
    noncomm_ring
  have hVJ : V * jOp P A (star A) = jOp P A (star A) * V := by
    dsimp [V, jOp]; rw [mul_sub, sub_mul, V_comm_Nplus hP, V_comm_Nminus hP]
  have hj2 : jOp P A (star A) * jOp P A (star A) = -V := by
    dsimp [jOp, V, casimirV, Qplus, Qminus]
    calc (Nplus P A - Nminus P (star A)) * (Nplus P A - Nminus P (star A))
        = Nplus P A * Nplus P A - (Nplus P A * Nminus P (star A) + Nminus P (star A) * Nplus P A) +
          Nminus P (star A) * Nminus P (star A) := by noncomm_ring
      _ = -(Nplus P A * Nminus P (star A) + Nminus P (star A) * Nplus P A) := by
          rw [Nplus_sq hP, Nminus_sq hP]; noncomm_ring
  refine ⟨?_, ?_⟩
  · rw [hu0_star]; dsimp [u0, uZero, delta]
    calc (1 - V - jOp P A (star A)) * (1 - V + jOp P A (star A)) - 1
        = V ^ 2 - 2 * V + (jOp P A (star A) * V - V * jOp P A (star A)) -
          jOp P A (star A) * jOp P A (star A) := by noncomm_ring
      _ = V ^ 2 - V := by rw [hVJ, hj2]; noncomm_ring
  · rw [hu0_star]; dsimp [u0, uZero, delta]
    calc (1 - V + jOp P A (star A)) * (1 - V - jOp P A (star A)) - 1
        = V ^ 2 - 2 * V - (jOp P A (star A) * V - V * jOp P A (star A)) -
          jOp P A (star A) * jOp P A (star A) := by noncomm_ring
      _ = V ^ 2 - V := by rw [hVJ, hj2]; noncomm_ring

/-- On-shell integral Weyl reflection: when `δ(V) = 0`, `u₀ = 1 - V + J` is strictly
    unitary over `ℤ`, inverts the Cartan grading `u₀ Σ u₀* = -Σ`, and maps `P` to
    `P_{0,+} + Q₋`. -/
theorem on_shell_integral_weyl_reflection {B : Type*} [Ring B] [StarRing B]
    {P A : B} (hP : delta P = 0) (hP_star : star P = P)
    (hfaith3 : ∀ Y1 Y2 Y3 : B, star Y1 * Y1 + star Y2 * Y2 + star Y3 * Y3 = 0 → Y1 = 0)
    (hV : delta (casimirV P A (star A)) = 0) :
    let u0 := uZero P A (star A)
    let sig := sigmaOp P A (star A)
    star u0 * u0 = 1 ∧ u0 * star u0 = 1 ∧
    u0 * sig * star u0 = -sig ∧
    u0 * P * star u0 = P0_plus P A (star A) + Qminus P A (star A) := by
  intro u0 sig
  obtain ⟨hu1, hu2⟩ := integral_unitary_defect_law hP hP_star (A := A)
  rw [hV] at hu1 hu2
  have hNp_star : star (Nplus P A) = Nminus P (star A) := by
    dsimp [Nplus, Nminus]; simp only [star_mul, star_sub, star_one, hP_star, mul_assoc]
  have hNm_star : star (Nminus P (star A)) = Nplus P A := by
    rw [← hNp_star, star_star]
  have hV_star : star (casimirV P A (star A)) = casimirV P A (star A) := by
    dsimp [casimirV, Qplus, Qminus]
    simp only [star_add, star_mul, hNp_star, hNm_star]
  have hJ_star : star (jOp P A (star A)) = -jOp P A (star A) := by
    dsimp [jOp]; simp only [star_sub, hNp_star, hNm_star]; noncomm_ring
  have hu0_star : star u0 = 1 - casimirV P A (star A) - jOp P A (star A) := by
    dsimp [u0, uZero]; simp only [star_add, star_sub, star_one, hV_star, hJ_star]; noncomm_ring
  have h1V_V : (1 - casimirV P A (star A)) * casimirV P A (star A) = 0 := by
    calc (1 - casimirV P A (star A)) * casimirV P A (star A)
        = -(casimirV P A (star A) ^ 2 - casimirV P A (star A)) := by noncomm_ring
      _ = -delta (casimirV P A (star A)) := rfl
      _ = 0 := by rw [hV, neg_zero]
  have hfaith1 : ∀ Y : B, star Y * Y = 0 → Y = 0 := fun Y hY =>
    hfaith3 Y 0 0 (by simpa using hY)
  have hP0_Np : (1 - casimirV P A (star A)) * Nplus P A = 0 := by
    let Y := Nminus P (star A) * (1 - casimirV P A (star A))
    have hY_star : star Y = (1 - casimirV P A (star A)) * Nplus P A := by
      dsimp [Y]; simp only [star_mul, star_sub, star_one, hV_star, hNm_star]
    have hYY : star Y * Y = 0 := by
      rw [hY_star]; dsimp [Y]
      calc (1 - casimirV P A (star A)) * Nplus P A * (Nminus P (star A) * (1 - casimirV P A (star A)))
          = ((1 - casimirV P A (star A)) * casimirV P A (star A)) * P *
            (1 - casimirV P A (star A)) := by
            rw [mul_assoc (1 - casimirV P A (star A)) (casimirV P A (star A)) P, V_mul_P hP]
            dsimp [Qplus]; noncomm_ring
        _ = 0 := by rw [h1V_V]; noncomm_ring
    rw [← hY_star, hfaith1 Y hYY, star_zero]
  have hP0_Nm : (1 - casimirV P A (star A)) * Nminus P (star A) = 0 := by
    let Z := Nplus P A * (1 - casimirV P A (star A))
    have hZ_star : star Z = (1 - casimirV P A (star A)) * Nminus P (star A) := by
      dsimp [Z]; simp only [star_mul, star_sub, star_one, hV_star, hNp_star]
    have hZZ : star Z * Z = 0 := by
      rw [hZ_star]; dsimp [Z]
      have hQm : Nminus P (star A) * Nplus P A = casimirV P A (star A) * (1 - P) := by
        calc Nminus P (star A) * Nplus P A
            = casimirV P A (star A) - Qplus P A (star A) := by
              dsimp [casimirV, Qminus]; noncomm_ring
          _ = casimirV P A (star A) * (1 - P) := by rw [← V_mul_P hP]; noncomm_ring
      calc (1 - casimirV P A (star A)) * Nminus P (star A) *
             (Nplus P A * (1 - casimirV P A (star A)))
          = ((1 - casimirV P A (star A)) * casimirV P A (star A)) * (1 - P) *
            (1 - casimirV P A (star A)) := by rw [← mul_assoc, mul_assoc _ (Nminus _ _), hQm]; noncomm_ring
        _ = 0 := by rw [h1V_V]; noncomm_ring
    rw [← hZ_star, hfaith1 Z hZZ, star_zero]
  have hP0_J : (1 - casimirV P A (star A)) * jOp P A (star A) = 0 := by
    dsimp [jOp]; rw [mul_sub, hP0_Np, hP0_Nm, sub_self]
  have hJ_P0 : jOp P A (star A) * (1 - casimirV P A (star A)) = 0 := by
    dsimp [jOp]
    calc (Nplus P A - Nminus P (star A)) * (1 - casimirV P A (star A))
        = (1 - casimirV P A (star A)) * Nplus P A - (1 - casimirV P A (star A)) * Nminus P (star A) +
          (casimirV P A (star A) * Nplus P A - Nplus P A * casimirV P A (star A)) -
          (casimirV P A (star A) * Nminus P (star A) - Nminus P (star A) * casimirV P A (star A)) := by
          noncomm_ring
      _ = 0 := by rw [hP0_Np, hP0_Nm, V_comm_Nplus hP, V_comm_Nminus hP]; noncomm_ring
  refine ⟨sub_eq_zero.mp hu1, sub_eq_zero.mp hu2, ?_, ?_⟩
  · rw [hu0_star]; dsimp [u0, uZero]
    have hP0_Sig : (1 - casimirV P A (star A)) * sig = 0 := by
      dsimp [sig, sigmaOp, Qplus, Qminus]
      calc (1 - casimirV P A (star A)) * (Nplus P A * Nminus P (star A) - Nminus P (star A) * Nplus P A)
          = ((1 - casimirV P A (star A)) * Nplus P A) * Nminus P (star A) -
            ((1 - casimirV P A (star A)) * Nminus P (star A)) * Nplus P A := by noncomm_ring
        _ = 0 := by rw [hP0_Np, hP0_Nm]; noncomm_ring
    have hJSig : jOp P A (star A) * sig = -sig * jOp P A (star A) := by
      have h := jOp_anticomm_sigmaOp hP A (star A)
      calc jOp P A (star A) * sig = (jOp P A (star A) * sig + sig * jOp P A (star A)) - sig * jOp P A (star A) := by
            noncomm_ring
        _ = -sig * jOp P A (star A) := by rw [h]; noncomm_ring
    have hj2 : jOp P A (star A) * jOp P A (star A) = -casimirV P A (star A) := by
      dsimp [jOp, casimirV, Qplus, Qminus]
      calc (Nplus P A - Nminus P (star A)) * (Nplus P A - Nminus P (star A))
          = Nplus P A * Nplus P A - (Nplus P A * Nminus P (star A) + Nminus P (star A) * Nplus P A) +
            Nminus P (star A) * Nminus P (star A) := by noncomm_ring
        _ = -(Nplus P A * Nminus P (star A) + Nminus P (star A) * Nplus P A) := by
            rw [Nplus_sq hP, Nminus_sq hP]; noncomm_ring
    have hSig_V : sig * casimirV P A (star A) = sig := by
      have hV_Sig : casimirV P A (star A) * sig = sig := by
        calc casimirV P A (star A) * sig = sig - (1 - casimirV P A (star A)) * sig := by noncomm_ring
          _ = sig := by rw [hP0_Sig, sub_zero]
      have hcomm : casimirV P A (star A) * sig = sig * casimirV P A (star A) := by
        dsimp [sig, sigmaOp]
        rw [mul_sub, sub_mul]
        congr 1
        · dsimp [Qplus]; rw [← mul_assoc, V_comm_Nplus hP, mul_assoc, V_comm_Nminus hP, ← mul_assoc]
        · dsimp [Qminus]; rw [← mul_assoc, V_comm_Nminus hP, mul_assoc, V_comm_Nplus hP, ← mul_assoc]
      rw [← hcomm, hV_Sig]
    calc (1 - casimirV P A (star A) + jOp P A (star A)) * sig *
           (1 - casimirV P A (star A) - jOp P A (star A))
        = ((1 - casimirV P A (star A)) * sig + jOp P A (star A) * sig) *
          (1 - casimirV P A (star A) - jOp P A (star A)) := by noncomm_ring
      _ = (-sig * jOp P A (star A)) * (1 - casimirV P A (star A) - jOp P A (star A)) := by
          rw [hP0_Sig, zero_add, hJSig]
      _ = -sig * (jOp P A (star A) * (1 - casimirV P A (star A))) +
          sig * (jOp P A (star A) * jOp P A (star A)) := by noncomm_ring
      _ = -(sig * casimirV P A (star A)) := by rw [hJ_P0, hj2]; noncomm_ring
      _ = -sig := by rw [hSig_V]
  · rw [hu0_star]; dsimp [u0, uZero, P0_plus]
    have hJP : jOp P A (star A) * P = -Nminus P (star A) := by
      dsimp [jOp]
      calc (Nplus P A - Nminus P (star A)) * P = Nplus P A * P - Nminus P (star A) * P := by noncomm_ring
        _ = -Nminus P (star A) := by rw [Nplus_mul_P hP, Nminus_mul_P hP]; noncomm_ring
    have hNmJ : Nminus P (star A) * jOp P A (star A) = Qminus P A (star A) := by
      dsimp [jOp, Qminus]
      calc Nminus P (star A) * (Nplus P A - Nminus P (star A))
          = Nminus P (star A) * Nplus P A - Nminus P (star A) * Nminus P (star A) := by noncomm_ring
        _ = Nminus P (star A) * Nplus P A := by rw [Nminus_sq hP, sub_zero]
    have hNm_P0 : Nminus P (star A) * (1 - casimirV P A (star A)) = 0 := by
      calc Nminus P (star A) * (1 - casimirV P A (star A))
          = (1 - casimirV P A (star A)) * Nminus P (star A) +
            (casimirV P A (star A) * Nminus P (star A) - Nminus P (star A) * casimirV P A (star A)) := by
            noncomm_ring
        _ = 0 := by rw [hP0_Nm, V_comm_Nminus hP]; noncomm_ring
    have hP_P0 : P * (1 - casimirV P A (star A)) = (1 - casimirV P A (star A)) * P := by
      calc P * (1 - casimirV P A (star A)) = P - P * casimirV P A (star A) := by noncomm_ring
        _ = (1 - casimirV P A (star A)) * P := by rw [P_mul_V hP, ← V_mul_P hP]; noncomm_ring
    have hP0_sq : (1 - casimirV P A (star A)) * (1 - casimirV P A (star A)) =
        1 - casimirV P A (star A) := by
      calc (1 - casimirV P A (star A)) * (1 - casimirV P A (star A))
          = 1 - casimirV P A (star A) + delta (casimirV P A (star A)) := by dsimp [delta]; noncomm_ring
        _ = 1 - casimirV P A (star A) := by rw [hV, add_zero]
    calc (1 - casimirV P A (star A) + jOp P A (star A)) * P *
           (1 - casimirV P A (star A) - jOp P A (star A))
        = (P * (1 - casimirV P A (star A)) + jOp P A (star A) * P) *
          (1 - casimirV P A (star A) - jOp P A (star A)) := by rw [hP_P0]; noncomm_ring
      _ = (P * (1 - casimirV P A (star A)) - Nminus P (star A)) *
          (1 - casimirV P A (star A) - jOp P A (star A)) := by rw [hJP]; noncomm_ring
      _ = P * ((1 - casimirV P A (star A)) * (1 - casimirV P A (star A))) -
          P * ((1 - casimirV P A (star A)) * jOp P A (star A)) -
          Nminus P (star A) * (1 - casimirV P A (star A)) +
          Nminus P (star A) * jOp P A (star A) := by noncomm_ring
      _ = P * (1 - casimirV P A (star A)) + Qminus P A (star A) := by
          rw [hP0_sq, hP0_J, hNm_P0, hNmJ]; noncomm_ring

/-! ### Stage K₅: Bosonic Starvation of C_B(V) & Parity-Inverted Fermionic Supercharges -/

/-- At `δ(V) = 0`, any `X ∈ C_B(V)` has identically zero odd KKT projections
    `Q₊ X P₀`, `P₀ X Q₊`, `Q₋ X P₀`, and `P₀ X Q₋` without dividing by 2. -/
theorem centralizer_kills_odd_kkt_modes {B : Type*} [Ring B] {P : B}
    (hP : delta P = 0) (A C : B) (hV : delta (casimirV P A C) = 0)
    {X : B} (hcomm : comm (casimirV P A C) X = 0) :
    let Qp := Qplus P A C
    let Qm := Qminus P A C
    let P0 := 1 - casimirV P A C
    Qp * X * P0 = 0 ∧ P0 * X * Qp = 0 ∧ Qm * X * P0 = 0 ∧ P0 * X * Qm = 0 := by
  intro Qp Qm P0
  have hQpV : Qp * casimirV P A C = Qp := by
    have hV2 : casimirV P A C * casimirV P A C = casimirV P A C := P_mul_P hV
    dsimp [Qp]
    calc Qplus P A C * casimirV P A C = P * (casimirV P A C * casimirV P A C) := by
          rw [← P_mul_V hP]; noncomm_ring
      _ = Qplus P A C := by rw [hV2, P_mul_V hP]
  have hQmV : Qm * casimirV P A C = Qm := by
    have hV2 : casimirV P A C * casimirV P A C = casimirV P A C := P_mul_P hV
    have hQm_eq : Qm = (1 - P) * casimirV P A C := by
      calc Qm = casimirV P A C - Qplus P A C := by dsimp [Qm, casimirV]; noncomm_ring
        _ = casimirV P A C - P * casimirV P A C := by rw [P_mul_V hP]
        _ = (1 - P) * casimirV P A C := by noncomm_ring
    calc Qm * casimirV P A C = (1 - P) * (casimirV P A C * casimirV P A C) := by
          rw [hQm_eq]; noncomm_ring
      _ = Qm := by rw [hV2, ← hQm_eq]
  have hVP0 : casimirV P A C * P0 = 0 := by
    dsimp [P0]
    calc casimirV P A C * (1 - casimirV P A C) = -delta (casimirV P A C) := by
          dsimp [delta]; noncomm_ring
      _ = 0 := by rw [hV, neg_zero]
  have hP0V : P0 * casimirV P A C = 0 := by
    dsimp [P0]
    calc (1 - casimirV P A C) * casimirV P A C = -delta (casimirV P A C) := by
          dsimp [delta]; noncomm_ring
      _ = 0 := by rw [hV, neg_zero]
  refine ⟨?_, ?_, ?_, ?_⟩
  · calc Qp * X * P0
        = (Qp * casimirV P A C) * X * P0 - Qp * X * (casimirV P A C * P0) := by
          rw [hQpV, hVP0]; noncomm_ring
      _ = Qp * comm (casimirV P A C) X * P0 := by dsimp [comm]; noncomm_ring
      _ = 0 := by rw [hcomm]; noncomm_ring
  · have hVQp : casimirV P A C * Qp = Qp := by
      dsimp [Qp]
      calc casimirV P A C * Qplus P A C = (casimirV P A C * casimirV P A C) * P := by
            rw [← V_mul_P hP]; noncomm_ring
        _ = Qplus P A C := by rw [P_mul_P hV, V_mul_P hP]
    calc P0 * X * Qp
        = P0 * X * (casimirV P A C * Qp) - (P0 * casimirV P A C) * X * Qp := by
          rw [hVQp, hP0V]; noncomm_ring
      _ = -P0 * comm (casimirV P A C) X * Qp := by dsimp [comm]; noncomm_ring
      _ = 0 := by rw [hcomm]; noncomm_ring
  · calc Qm * X * P0
        = (Qm * casimirV P A C) * X * P0 - Qm * X * (casimirV P A C * P0) := by
          rw [hQmV, hVP0]; noncomm_ring
      _ = Qm * comm (casimirV P A C) X * P0 := by dsimp [comm]; noncomm_ring
      _ = 0 := by rw [hcomm]; noncomm_ring
  · have hVQm : casimirV P A C * Qm = Qm := by
      have hQm_eq : Qm = casimirV P A C * (1 - P) := by
        calc Qm = casimirV P A C - Qplus P A C := by dsimp [Qm, casimirV]; noncomm_ring
          _ = casimirV P A C - casimirV P A C * P := by rw [V_mul_P hP]
          _ = casimirV P A C * (1 - P) := by noncomm_ring
      calc casimirV P A C * Qm = (casimirV P A C * casimirV P A C) * (1 - P) := by
            rw [hQm_eq]; noncomm_ring
        _ = Qm := by rw [P_mul_P hV, ← hQm_eq]
    calc P0 * X * Qm
        = P0 * X * (casimirV P A C * Qm) - (P0 * casimirV P A C) * X * Qm := by
          rw [hVQm, hP0V]; noncomm_ring
      _ = -P0 * comm (casimirV P A C) X * Qm := by dsimp [comm]; noncomm_ring
      _ = 0 := by rw [hcomm]; noncomm_ring

/-- Parity-inverted fermionic recovery: at `δ(V) = 0`, any ambient block
    `Q₊ D₁ P_{0,+} + P_{0,-} D₂ Q₋` has exact KKT grade `+1` under `Σ` while
    anticommuting with `Γ_Σ = 2V - 1`. -/
theorem parity_inverted_fermionic_supercharge {B : Type*} [Ring B] {P : B}
    (hP : delta P = 0) (A C : B) (hV : delta (casimirV P A C) = 0) (D1 D2 : B) :
    let Qp := Qplus P A C
    let Qm := Qminus P A C
    let sig := sigmaOp P A C
    let V := casimirV P A C
    let Q_odd := Qp * D1 * P0_plus P A C + P0_minus P A C * D2 * Qm
    comm sig Q_odd = Q_odd ∧ anticomm (2 * V - 1) Q_odd = 0 := by
  intro Qp Qm sig V Q_odd
  have hPP := P_mul_P hP
  have hVV := P_mul_P hV
  have hQpQm : Qp * Qm = 0 := by
    dsimp [Qp, Qm, Qplus, Qminus, Nplus, Nminus]
    calc P * A * (1 - P) * ((1 - P) * C * P) * ((1 - P) * C * P * (P * A * (1 - P)))
        = P * A * (1 - P) * ((1 - P) * C * (P - P * P) * C * P) * (P * A * (1 - P)) := by
          noncomm_ring
      _ = 0 := by rw [hPP]; noncomm_ring
  have hQmQp : Qm * Qp = 0 := by
    have h1PP : (1 - P) * P = 0 := by
      calc (1 - P) * P = P - P * P := by noncomm_ring
        _ = 0 := by rw [hPP, sub_self]
    dsimp [Qp, Qm, Qplus, Qminus, Nplus, Nminus]
    calc (1 - P) * C * P * (P * A * (1 - P)) * (P * A * (1 - P) * ((1 - P) * C * P))
        = (1 - P) * C * P * (P * A * ((1 - P) * P) * A * (1 - P)) * ((1 - P) * C * P) := by
          noncomm_ring
      _ = 0 := by rw [h1PP]; noncomm_ring
  have hVQp : V * Qp = Qp := by
    dsimp [V, Qp]
    calc casimirV P A C * Qplus P A C = (casimirV P A C * casimirV P A C) * P := by
          rw [← V_mul_P hP]; noncomm_ring
      _ = Qplus P A C := by rw [hVV, V_mul_P hP]
  have hVQm : V * Qm = Qm := by
    have hQm_eq : Qm = V * (1 - P) := by
      calc Qm = V - Qplus P A C := by dsimp [Qm, V, casimirV]; noncomm_ring
        _ = V - V * P := by dsimp [V]; rw [V_mul_P hP]
        _ = V * (1 - P) := by noncomm_ring
    calc V * Qm = (V * V) * (1 - P) := by rw [hQm_eq]; noncomm_ring
      _ = Qm := by rw [hVV, ← hQm_eq]
  have hQp_sq : Qp * Qp = Qp := by
    calc Qp * Qp = (V * Qp) - Qm * Qp := by dsimp [V, casimirV]; noncomm_ring
      _ = Qp := by rw [hVQp, hQmQp, sub_zero]
  have hQm_sq : Qm * Qm = Qm := by
    calc Qm * Qm = (V * Qm) - Qp * Qm := by dsimp [V, casimirV]; noncomm_ring
      _ = Qm := by rw [hVQm, hQpQm, sub_zero]
  have hSig_Qp : sig * Qp = Qp := by
    dsimp [sig, sigmaOp]; calc (Qp - Qm) * Qp = Qp * Qp - Qm * Qp := by noncomm_ring
      _ = Qp := by rw [hQp_sq, hQmQp, sub_zero]
  have hQm_Sig : Qm * sig = -Qm := by
    dsimp [sig, sigmaOp]; calc Qm * (Qp - Qm) = Qm * Qp - Qm * Qm := by noncomm_ring
      _ = -Qm := by rw [hQmQp, hQm_sq, zero_sub]
  have hQm_V : Qm * V = Qm := by
    dsimp [V, casimirV]; calc Qm * (Qp + Qm) = Qm * Qp + Qm * Qm := by noncomm_ring
      _ = Qm := by rw [hQmQp, hQm_sq, zero_add]
  have hP0p_V : P0_plus P A C * V = 0 := by
    dsimp [P0_plus]; calc P * (1 - V) * V = P * (V - V * V) := by noncomm_ring
      _ = 0 := by rw [hVV, sub_self, mul_zero]
  have hP0p_Sig : P0_plus P A C * sig = 0 := by
    have hSig_eq : sig = V * (2 * P - 1) := by
      dsimp [sig, sigmaOp, V]
      calc Qplus P A C - Qminus P A C = 2 * Qplus P A C - (Qplus P A C + Qminus P A C) := by
            noncomm_ring
        _ = 2 * (casimirV P A C * P) - casimirV P A C := by
            rw [V_mul_P hP]; dsimp [casimirV]
        _ = casimirV P A C * (2 * P - 1) := by noncomm_ring
    rw [hSig_eq, ← mul_assoc, hP0p_V, zero_mul]
  have hV_P0m : V * P0_minus P A C = 0 := by
    have hVP : V * P = P * V := by rw [V_mul_P hP, P_mul_V hP]
    dsimp [P0_minus]
    calc V * ((1 - P) * (1 - V))
        = (V - V * P) * (1 - V) := by noncomm_ring
      _ = (1 - P) * (V - V * V) := by rw [hVP]; noncomm_ring
      _ = 0 := by rw [hVV, sub_self, mul_zero]
  have hSig_P0m : sig * P0_minus P A C = 0 := by
    have hSig_eq : sig = (2 * P - 1) * V := by
      dsimp [sig, sigmaOp, V]
      calc Qplus P A C - Qminus P A C = 2 * Qplus P A C - (Qplus P A C + Qminus P A C) := by
            noncomm_ring
        _ = 2 * (P * casimirV P A C) - casimirV P A C := by
            rw [P_mul_V hP]; dsimp [casimirV]
        _ = (2 * P - 1) * casimirV P A C := by noncomm_ring
    rw [hSig_eq, mul_assoc, hV_P0m, mul_zero]
  refine ⟨?_, ?_⟩
  · dsimp [comm, Q_odd]
    calc sig * (Qp * D1 * P0_plus P A C + P0_minus P A C * D2 * Qm) -
         (Qp * D1 * P0_plus P A C + P0_minus P A C * D2 * Qm) * sig
        = (sig * Qp) * D1 * P0_plus P A C + (sig * P0_minus P A C) * D2 * Qm -
          Qp * D1 * (P0_plus P A C * sig) - P0_minus P A C * D2 * (Qm * sig) := by noncomm_ring
      _ = Qp * D1 * P0_plus P A C + P0_minus P A C * D2 * Qm := by
          rw [hSig_Qp, hSig_P0m, hP0p_Sig, hQm_Sig]; noncomm_ring
  · dsimp [anticomm, Q_odd]
    calc (2 * V - 1) * (Qp * D1 * P0_plus P A C + P0_minus P A C * D2 * Qm) +
         (Qp * D1 * P0_plus P A C + P0_minus P A C * D2 * Qm) * (2 * V - 1)
        = 2 * (V * Qp) * D1 * P0_plus P A C + 2 * (V * P0_minus P A C) * D2 * Qm +
          2 * Qp * D1 * (P0_plus P A C * V) + 2 * P0_minus P A C * D2 * (Qm * V) -
          2 * (Qp * D1 * P0_plus P A C + P0_minus P A C * D2 * Qm) := by noncomm_ring
      _ = 0 := by rw [hVQp, hV_P0m, hP0p_V, hQm_V]; noncomm_ring

/-! ### Stage K₆–K₉: Clifford-8 Super-Extension, Morita Spacetime & Andreev Retro-Reflection -/

/-- Canonical 4+4 idempotent cut in `Mat₈(ℤ)`. -/
def P8_Z : Matrix (Fin 8) (Fin 8) ℤ := Matrix.diagonal ![1, 1, 1, 1, 0, 0, 0, 0]

/-- Canonical off-diagonal witness `A₈ ∈ Mat₈(ℤ)` coupling `{0,1}` with `{6,7}`. -/
def A8_Z : Matrix (Fin 8) (Fin 8) ℤ :=
  Matrix.of fun i j =>
    if (i = 0 ∧ j = 6) ∨ (i = 1 ∧ j = 7) ∨ (i = 6 ∧ j = 0) ∨ (i = 7 ∧ j = 1) then 1
    else 0

/-- `P₈`-even diagonal operator `D₈ ∈ P₈ B P₈ ⊕ (1 - P₈) B (1 - P₈)`. -/
def D8_Z : Matrix (Fin 8) (Fin 8) ℤ :=
  Matrix.of fun i j =>
    if (i = 0 ∧ j = 2) ∨ (i = 1 ∧ j = 3) ∨ (i = 2 ∧ j = 0) ∨ (i = 3 ∧ j = 1) ∨
       (i = 4 ∧ j = 6) ∨ (i = 5 ∧ j = 7) ∨ (i = 6 ∧ j = 4) ∨ (i = 7 ∧ j = 5) then 1
    else 0

/-- Internal Supercolor bridge `G₈ ∈ P₀ B P₀` coupling `P_{0,+}` and `P_{0,-}`. -/
def G8_Z : Matrix (Fin 8) (Fin 8) ℤ :=
  Matrix.of fun i j =>
    if (i = 2 ∧ j = 4) ∨ (i = 3 ∧ j = 5) ∨ (i = 4 ∧ j = 2) ∨ (i = 5 ∧ j = 3) then 1
    else 0

/-- Master Clifford-8 Super-Extension Theorem (Stage `K₉`):
    in `Mat₈(ℤ)`, `D₈` commutes with `P₈` and together with `G₈` resurrects the odd
    fermionic horizon mode `Q_odd ∈ g₊₁(Σ₈) \ C_B(V₈)`, yielding non-zero Morita
    spacetime translation `Q_odd² ≠ 0` and Andreev retro-reflection `P₀ [Δ₋₂, Q_odd] Q₊ ≠ 0`. -/
theorem clifford8_parity_inversion_and_andreev_closure :
    let V := casimirV P8_Z A8_Z A8_Z
    let Qp := Qplus P8_Z A8_Z A8_Z
    let Qm := Qminus P8_Z A8_Z A8_Z
    let P0 := 1 - V
    let sig := sigmaOp P8_Z A8_Z A8_Z
    let Q_odd := Qp * (D8_Z * G8_Z) * P0 + P0 * D8_Z * Qm
    let Delta_minus2 := Nminus P8_Z A8_Z
    comm P8_Z D8_Z = 0 ∧
    Q_odd ≠ 0 ∧
    comm sig Q_odd = Q_odd ∧
    comm V Q_odd ≠ 0 ∧
    Q_odd * Q_odd = Qp * A8_Z * Qm ∧
    Q_odd * Q_odd ≠ 0 ∧
    P0 * comm Delta_minus2 Q_odd * Qp ≠ 0 := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

end InfoGeometry.OperatorAlgebra.PeirceBiSandwich
