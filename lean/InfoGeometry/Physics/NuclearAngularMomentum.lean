/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Integer triangle inequalities for angular momentum labels

This module proves the natural-number triangle constraints on a coupled
angular-momentum label. Clebsch–Gordan coefficients and the Wigner–Eckart
theorem are not formalized here.
-/

noncomputable section

namespace InfoGeometry.Physics.NuclearAngularMomentum

/- The triangle inequalities are stated both in subtraction form and in the
addition form that avoids truncated subtraction. -/

/-- Equivalent forms of the natural-number triangle inequalities. -/
theorem angular_momentum_triangle_iff (j₁ j₂ J : ℕ) :
    (j₁ - j₂ ≤ J ∧ j₂ - j₁ ≤ J ∧ J ≤ j₁ + j₂) ↔
      (j₁ ≤ J + j₂ ∧ j₂ ≤ J + j₁ ∧ J ≤ j₁ + j₂) := by
  omega

/-- Convert the three triangle bounds into their equivalent subtraction form. -/
theorem angular_momentum_triangle (j₁ j₂ J : ℕ)
    (hJ : J ≤ j₁ + j₂) (hJ₁ : j₁ ≤ J + j₂) (hJ₂ : j₂ ≤ J + j₁) :
    j₁ - j₂ ≤ J ∧ j₂ - j₁ ≤ J ∧ J ≤ j₁ + j₂ := by
  exact (angular_momentum_triangle_iff j₁ j₂ J).2 ⟨hJ₁, hJ₂, hJ⟩

/-! ## Finite SU(2) representations, spherical tensors, and Wigner--Eckart selection -/

/-- A representation of the `su(2)` Lie algebra on a `K`-module `V`. -/
structure SU2Rep (K V : Type*) [CommRing K] [AddCommGroup V] [Module K V] where
  J_zero : Module.End K V
  J_plus : Module.End K V
  J_minus : Module.End K V
  comm_zero_plus : J_zero * J_plus - J_plus * J_zero = J_plus
  comm_zero_minus : J_zero * J_minus - J_minus * J_zero = -J_minus
  comm_plus_minus : J_plus * J_minus - J_minus * J_plus = (2 : K) • J_zero

/-- The fundamental spin-`1/2` `SU(2)` representation on `ℂ²` from `FiniteSpinAlgebra`. -/
def spinHalfSU2Rep : SU2Rep ℂ (Fin 2 → ℂ) where
  J_zero := Matrix.toLin' InfoGeometry.Algebra.FiniteSpin.J_zero
  J_plus := Matrix.toLin' InfoGeometry.Algebra.FiniteSpin.J_plus
  J_minus := Matrix.toLin' InfoGeometry.Algebra.FiniteSpin.J_minus
  comm_zero_plus := by
    change Matrix.toLin' InfoGeometry.Algebra.FiniteSpin.J_zero ∘ₗ
        Matrix.toLin' InfoGeometry.Algebra.FiniteSpin.J_plus -
      Matrix.toLin' InfoGeometry.Algebra.FiniteSpin.J_plus ∘ₗ
        Matrix.toLin' InfoGeometry.Algebra.FiniteSpin.J_zero =
      Matrix.toLin' InfoGeometry.Algebra.FiniteSpin.J_plus
    rw [← Matrix.toLin'_mul, ← Matrix.toLin'_mul, ← map_sub]
    exact congrArg Matrix.toLin' InfoGeometry.Algebra.FiniteSpin.comm_J_zero_J_plus
  comm_zero_minus := by
    change Matrix.toLin' InfoGeometry.Algebra.FiniteSpin.J_zero ∘ₗ
        Matrix.toLin' InfoGeometry.Algebra.FiniteSpin.J_minus -
      Matrix.toLin' InfoGeometry.Algebra.FiniteSpin.J_minus ∘ₗ
        Matrix.toLin' InfoGeometry.Algebra.FiniteSpin.J_zero =
      -Matrix.toLin' InfoGeometry.Algebra.FiniteSpin.J_minus
    rw [← Matrix.toLin'_mul, ← Matrix.toLin'_mul, ← map_sub, ← map_neg]
    exact congrArg Matrix.toLin' InfoGeometry.Algebra.FiniteSpin.comm_J_zero_J_minus
  comm_plus_minus := by
    change Matrix.toLin' InfoGeometry.Algebra.FiniteSpin.J_plus ∘ₗ
        Matrix.toLin' InfoGeometry.Algebra.FiniteSpin.J_minus -
      Matrix.toLin' InfoGeometry.Algebra.FiniteSpin.J_minus ∘ₗ
        Matrix.toLin' InfoGeometry.Algebra.FiniteSpin.J_plus =
      (2 : ℂ) • Matrix.toLin' InfoGeometry.Algebra.FiniteSpin.J_zero
    rw [← Matrix.toLin'_mul, ← Matrix.toLin'_mul, ← map_sub, ← map_smul]
    exact congrArg Matrix.toLin' InfoGeometry.Algebra.FiniteSpin.comm_J_plus_J_minus

/-- Non-commutativity witness for `spinHalfSU2Rep`. -/
theorem spinHalfSU2Rep_noncomm :
    spinHalfSU2Rep.J_plus * spinHalfSU2Rep.J_minus ≠
      spinHalfSU2Rep.J_minus * spinHalfSU2Rep.J_plus := by
  intro h
  have h1 : spinHalfSU2Rep.J_plus * spinHalfSU2Rep.J_minus -
      spinHalfSU2Rep.J_minus * spinHalfSU2Rep.J_plus = 0 := sub_eq_zero.mpr h
  rw [spinHalfSU2Rep.comm_plus_minus] at h1
  have hval := congrArg (fun f : Module.End ℂ (Fin 2 → ℂ) => f (Pi.single 0 1) 0) h1
  simp [spinHalfSU2Rep, InfoGeometry.Algebra.FiniteSpin.J_zero] at hval

/-- Racah raising coefficient `√((k - q)(k + q + 1))`. -/
def racahPlus (k : ℕ) (q : ℤ) : ℂ :=
  ((Real.sqrt (((k : ℝ) - q) * ((k : ℝ) + q + 1)) : ℝ) : ℂ)

/-- Racah lowering coefficient `√((k + q)(k - q + 1))`. -/
def racahMinus (k : ℕ) (q : ℤ) : ℂ :=
  ((Real.sqrt (((k : ℝ) + q) * ((k : ℝ) - q + 1)) : ℝ) : ℂ)

/-- An irreducible spherical tensor operator `T^(k)` of integer rank `k` relative to `rep`
with ladder coefficients `(cPlus, cMinus)` over an arbitrary commutative ring `K`. -/
structure SphericalTensorOperator {K V : Type*} [CommRing K] [AddCommGroup V] [Module K V]
    (rep : SU2Rep K V) (k : ℕ) (cPlus cMinus : ℤ → K) where
  comp : ℤ → Module.End K V
  support_zero : ∀ q : ℤ, (k : ℤ) < |q| → comp q = 0
  comm_J_zero : ∀ q : ℤ, rep.J_zero * comp q - comp q * rep.J_zero = (q : K) • comp q
  comm_J_plus : ∀ q : ℤ, rep.J_plus * comp q - comp q * rep.J_plus = cPlus q • comp (q + 1)
  comm_J_minus : ∀ q : ℤ, rep.J_minus * comp q - comp q * rep.J_minus = cMinus q • comp (q - 1)

/-- Component map for `vectorTensorOperatorOver` using `if` branches for clean algebraic rewriting. -/
def vectorTensorComp {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (rep : SU2Rep K V) (sqrtTwo : K) (q : ℤ) : Module.End K V :=
  if q = 1 then -((1 / sqrtTwo) • rep.J_plus)
  else if q = 0 then rep.J_zero
  else if q = -1 then (1 / sqrtTwo) • rep.J_minus
  else 0

/-- Generalized rank-1 spherical vector tensor operator over any field `K` containing `sqrtTwo`
with `sqrtTwo * sqrtTwo = 2`. -/
def vectorTensorOperatorOver {K V : Type*} [Field K] [CharZero K] [AddCommGroup V] [Module K V]
    (rep : SU2Rep K V) (sqrtTwo : K) (hsqrt : sqrtTwo * sqrtTwo = 2)
    (cPlus cMinus : ℤ → K)
    (hp1 : cPlus 1 = 0) (hp0 : cPlus 0 = sqrtTwo) (hpm1 : cPlus (-1) = sqrtTwo) (hpm2 : cPlus (-2) = 0)
    (hm2 : cMinus 2 = 0) (hm1 : cMinus 1 = sqrtTwo) (hm0 : cMinus 0 = sqrtTwo) (hmm1 : cMinus (-1) = 0) :
    SphericalTensorOperator rep 1 cPlus cMinus where
  comp := vectorTensorComp rep sqrtTwo
  support_zero q hq := by
    have h1 : q ≠ 1 := by rcases abs_cases q with ⟨_, _⟩ | ⟨_, _⟩ <;> omega
    have h0 : q ≠ 0 := by rcases abs_cases q with ⟨_, _⟩ | ⟨_, _⟩ <;> omega
    have hm1_ne : q ≠ -1 := by rcases abs_cases q with ⟨_, _⟩ | ⟨_, _⟩ <;> omega
    simp [vectorTensorComp, h1, h0, hm1_ne]
  comm_J_zero q := by
    by_cases h1 : q = 1
    · subst h1
      simp only [vectorTensorComp, ↓reduceIte, Int.cast_one, one_smul]
      rw [mul_neg, neg_mul, mul_smul_comm, smul_mul_assoc, neg_sub_neg, ← smul_sub,
        ← neg_sub (rep.J_zero * rep.J_plus), rep.comm_zero_plus, smul_neg]
    · by_cases h0 : q = 0
      · subst h0
        simp [vectorTensorComp, sub_self]
      · by_cases hm1_ne : q = -1
        · subst hm1_ne
          simp only [vectorTensorComp, h1, h0, ↓reduceIte, Int.cast_neg, Int.cast_one, neg_smul,
            one_smul]
          rw [mul_smul_comm, smul_mul_assoc, ← smul_sub, rep.comm_zero_minus, smul_neg]
        · simp [vectorTensorComp, h1, h0, hm1_ne]
  comm_J_plus q := by
    have hsqrt_ne : sqrtTwo ≠ 0 := by
      intro h; rw [h, mul_zero] at hsqrt; norm_num at hsqrt
    by_cases h1 : q = 1
    · subst h1
      simp [vectorTensorComp, hp1]
    · by_cases h0 : q = 0
      · subst h0
        simp only [vectorTensorComp, ↓reduceIte, hp0, zero_add, show (0 : ℤ) ≠ 1 by decide]
        have hcomm : rep.J_plus * rep.J_zero - rep.J_zero * rep.J_plus = -rep.J_plus := by
          rw [← neg_sub (rep.J_zero * rep.J_plus), rep.comm_zero_plus]
        rw [hcomm, smul_neg, smul_smul, mul_one_div, div_self hsqrt_ne, one_smul]
      · by_cases hm1_ne : q = -1
        · subst hm1_ne
          simp only [vectorTensorComp, ↓reduceIte, hpm1, neg_add_cancel,
            show (-1 : ℤ) ≠ 1 by decide, show (-1 : ℤ) ≠ 0 by decide,
            show (0 : ℤ) ≠ 1 by decide]
          rw [mul_smul_comm, smul_mul_assoc, ← smul_sub, rep.comm_plus_minus, smul_smul]
          have htwo : sqrtTwo * (1 / sqrtTwo * 2) = sqrtTwo * sqrtTwo := by
            rw [← hsqrt]; field_simp [hsqrt_ne]
          have htwo' : 1 / sqrtTwo * 2 = sqrtTwo := mul_left_cancel₀ hsqrt_ne htwo
          rw [htwo']
        · by_cases hm2_ne : q = -2
          · subst hm2_ne
            simp [vectorTensorComp, hpm2]
          · have hq1 : q + 1 ≠ 1 := fun h => h0 (by omega)
            have hq0 : q + 1 ≠ 0 := fun h => hm1_ne (by omega)
            have hqm1 : q + 1 ≠ -1 := fun h => hm2_ne (by omega)
            simp [vectorTensorComp, h1, h0, hm1_ne, hq1, hq0, hqm1]
  comm_J_minus q := by
    have hsqrt_ne : sqrtTwo ≠ 0 := by
      intro h; rw [h, mul_zero] at hsqrt; norm_num at hsqrt
    by_cases hm1_ne : q = -1
    · subst hm1_ne
      simp [vectorTensorComp, hmm1]
    · by_cases h0 : q = 0
      · subst h0
        simp only [vectorTensorComp, ↓reduceIte, hm0, zero_sub, show (0 : ℤ) ≠ 1 by decide,
          show (-1 : ℤ) ≠ 1 by decide, show (-1 : ℤ) ≠ 0 by decide]
        have hcomm : rep.J_minus * rep.J_zero - rep.J_zero * rep.J_minus = rep.J_minus := by
          rw [← neg_sub (rep.J_zero * rep.J_minus), rep.comm_zero_minus, neg_neg]
        rw [hcomm, smul_smul, mul_one_div, div_self hsqrt_ne, one_smul]
      · by_cases h1 : q = 1
        · subst h1
          simp only [vectorTensorComp, ↓reduceIte, hm1, sub_self, show (0 : ℤ) ≠ 1 by decide]
          have hcomm : rep.J_minus * rep.J_plus - rep.J_plus * rep.J_minus =
              -((2 : K) • rep.J_zero) := by
            rw [← neg_sub (rep.J_plus * rep.J_minus), rep.comm_plus_minus]
          rw [mul_neg, neg_mul, mul_smul_comm, smul_mul_assoc, neg_sub_neg, ← smul_sub,
            ← neg_sub (rep.J_minus * rep.J_plus), hcomm, neg_neg, smul_smul]
          have htwo : sqrtTwo * (1 / sqrtTwo * 2) = sqrtTwo * sqrtTwo := by
            rw [← hsqrt]; field_simp [hsqrt_ne]
          have htwo' : 1 / sqrtTwo * 2 = sqrtTwo := mul_left_cancel₀ hsqrt_ne htwo
          rw [htwo']
        · by_cases h2 : q = 2
          · subst h2
            simp [vectorTensorComp, hm2]
          · have hq1 : q - 1 ≠ 1 := fun h => h2 (by omega)
            have hq0 : q - 1 ≠ 0 := fun h => h1 (by omega)
            have hqm1 : q - 1 ≠ -1 := fun h => h0 (by omega)
            simp [vectorTensorComp, h1, h0, hm1_ne, hq1, hq0, hqm1]

/-- Canonical rank-1 spherical vector tensor operator built from any complex `SU2Rep ℂ V`. -/
def vectorTensorOperator {V : Type*} [AddCommGroup V] [Module ℂ V]
    (rep : SU2Rep ℂ V) : SphericalTensorOperator rep 1 (racahPlus 1) (racahMinus 1) :=
  vectorTensorOperatorOver rep (Real.sqrt 2 : ℂ)
    (by exact_mod_cast (by simp : (Real.sqrt 2 : ℝ) * Real.sqrt 2 = 2))
    (racahPlus 1) (racahMinus 1)
    (by unfold racahPlus; norm_num) (by unfold racahPlus; norm_num)
    (by unfold racahPlus; norm_num) (by unfold racahPlus; norm_num)
    (by unfold racahMinus; norm_num) (by unfold racahMinus; norm_num)
    (by unfold racahMinus; norm_num) (by unfold racahMinus; norm_num)

/-- Obstruction-driven grade shift: `[J₀, T_q^(k)] = q T_q^(k)` shifts any `J₀`-eigenstate
from magnetic/`K` weight `m` to `m + q`. -/
theorem tensor_comp_shifts_weight
    {K V : Type*} [CommRing K] [AddCommGroup V] [Module K V]
    {rep : SU2Rep K V} {k : ℕ} {cPlus cMinus : ℤ → K}
    (T : SphericalTensorOperator rep k cPlus cMinus)
    (q : ℤ) (ket : V) (m : K)
    (hket : rep.J_zero ket = m • ket) :
    rep.J_zero (T.comp q ket) = (m + q) • T.comp q ket := by
  have hcomm := congrArg (fun op : Module.End K V => op ket) (T.comm_J_zero q)
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply, hket, map_smul] at hcomm
  rw [add_smul]
  exact sub_eq_iff_eq_add'.mp hcomm

/-- Coriolis `ΔK = ±1` ladder shift induced by `[J₀, J₊] = J₊` and `[J₀, J₋] = -J₋`. -/
theorem ladder_shifts_weight
    {K V : Type*} [CommRing K] [AddCommGroup V] [Module K V]
    (rep : SU2Rep K V) (ket : V) (m : K)
    (hket : rep.J_zero ket = m • ket) :
    rep.J_zero (rep.J_plus ket) = (m + 1) • rep.J_plus ket ∧
    rep.J_zero (rep.J_minus ket) = (m - 1) • rep.J_minus ket := by
  have hp := congrArg (fun op : Module.End K V => op ket) rep.comm_zero_plus
  have hm := congrArg (fun op : Module.End K V => op ket) rep.comm_zero_minus
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.neg_apply, hket, map_smul] at hp hm
  constructor
  · rw [add_smul, one_smul]
    exact sub_eq_iff_eq_add'.mp hp
  · rw [sub_smul, one_smul, sub_eq_add_neg]
    exact sub_eq_iff_eq_add'.mp hm

/-- Generalized magnetic quantum-number selection rule over any field `K` and any `SU2Rep K V`. -/
theorem magnetic_selection_rule
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {rep : SU2Rep K V} {k : ℕ} {cPlus cMinus : ℤ → K}
    (T : SphericalTensorOperator rep k cPlus cMinus)
    (q : ℤ) (bra : V →ₗ[K] K) (ket : V) (m m' : K)
    (hket : rep.J_zero ket = m • ket)
    (hbra : ∀ v : V, bra (rep.J_zero v) = m' * bra v)
    (hne : m' ≠ m + q) :
    bra (T.comp q ket) = 0 := by
  have hshift := congrArg bra (tensor_comp_shifts_weight T q ket m hket)
  rw [hbra, map_smul, smul_eq_mul] at hshift
  have hprod : (m' - (m + q)) * bra (T.comp q ket) = 0 := by
    linear_combination hshift
  exact (mul_eq_zero.mp hprod).resolve_left (sub_ne_zero.mpr hne)

/-- Generalized axial `K`-projection selection rule over any characteristic-zero field `K`. -/
theorem k_projection_selection_rule
    {K V : Type*} [Field K] [CharZero K] [AddCommGroup V] [Module K V]
    {rep : SU2Rep K V} {lam : ℕ} {cPlus cMinus : ℤ → K}
    (T : SphericalTensorOperator rep lam cPlus cMinus)
    (q : ℤ) (bra : V →ₗ[K] K) (ket : V) (twoKi twoKf : ℤ)
    (hket : rep.J_zero ket = ((twoKi : K) / 2) • ket)
    (hbra : ∀ v : V, bra (rep.J_zero v) = ((twoKf : K) / 2) * bra v)
    (hnonzero : bra (T.comp q ket) ≠ 0) :
    twoKf = twoKi + 2 * q ∧ |q| ≤ (lam : ℤ) ∧ |twoKf - twoKi| ≤ 2 * (lam : ℤ) := by
  have hmatch : ((twoKf : K) / 2) = ((twoKi : K) / 2) + (q : K) := by
    by_contra hne
    exact hnonzero (magnetic_selection_rule T q bra ket _ _ hket hbra hne)
  have hmatch_z : twoKf = twoKi + 2 * q := by
    have hc : (twoKf : K) = ((twoKi + 2 * q : ℤ) : K) := by
      push_cast
      linear_combination 2 * hmatch
    exact_mod_cast hc
  have hsupp : |q| ≤ (lam : ℤ) := by
    by_contra hlt
    have hgt : (lam : ℤ) < |q| := by omega
    have hz : T.comp q = 0 := T.support_zero q hgt
    apply hnonzero
    rw [hz]
    simp
  have hbound : |twoKf - twoKi| ≤ 2 * (lam : ℤ) := by
    rw [hmatch_z]
    have hdiff : twoKi + 2 * q - twoKi = 2 * q := by ring
    rw [hdiff, abs_mul, abs_of_nonneg (by norm_num : (0 : ℤ) ≤ 2)]
    omega
  exact ⟨hmatch_z, hsupp, hbound⟩

/-- Any `K`-forbidden transition (`|Kf - Ki| > λ`) vanishes identically over any `CharZero` field `K`. -/
theorem k_forbidden_transition_vanishes
    {K V : Type*} [Field K] [CharZero K] [AddCommGroup V] [Module K V]
    {rep : SU2Rep K V} {lam : ℕ} {cPlus cMinus : ℤ → K}
    (T : SphericalTensorOperator rep lam cPlus cMinus)
    (bra : V →ₗ[K] K) (ket : V) (twoKi twoKf : ℤ)
    (hket : rep.J_zero ket = ((twoKi : K) / 2) • ket)
    (hbra : ∀ v : V, bra (rep.J_zero v) = ((twoKf : K) / 2) * bra v)
    (hforbid : 2 * (lam : ℤ) < |twoKf - twoKi|) :
    ∀ q : ℤ, bra (T.comp q ket) = 0 := by
  intro q
  by_contra hnz
  have hsel := k_projection_selection_rule T q bra ket twoKi twoKf hket hbra hnz
  have hgt : 2 * (lam : ℤ) < |twoKf - twoKi| := hforbid
  omega

/-- Concrete rank-1 spherical vector tensor inhabitant on `spinHalfSU2Rep`. -/
def spinHalfVectorTensorOperator :
    SphericalTensorOperator spinHalfSU2Rep 1 (racahPlus 1) (racahMinus 1) :=
  vectorTensorOperator spinHalfSU2Rep

/-- Constructive finite Wigner--Eckart theorem on `spinHalfSU2Rep` for rank-1 spherical tensors:
every `T : SphericalTensorOperator spinHalfSU2Rep 1 (racahPlus 1) (racahMinus 1)` is proportional
to `vectorTensorOperator spinHalfSU2Rep`. -/
theorem wigner_eckart_spinHalf_rank1
    (T : SphericalTensorOperator spinHalfSU2Rep 1 (racahPlus 1) (racahMinus 1)) :
    let r : ℂ := 2 * (T.comp 0 (Pi.single 0 1)) 0
    ∀ q : ℤ, T.comp q = r • (vectorTensorOperator spinHalfSU2Rep).comp q := by
  intro r q
  set e0 : Fin 2 → ℂ := Pi.single 0 1
  set e1 : Fin 2 → ℂ := Pi.single 1 1
  have hbasis (f g : Module.End ℂ (Fin 2 → ℂ))
      (h0 : f e0 = g e0) (h1 : f e1 = g e1) : f = g := by
    apply LinearMap.ext
    intro v
    have hv : v = v 0 • e0 + v 1 • e1 := by
      ext i; fin_cases i <;> simp [e0, e1]
    rw [hv, map_add, map_add, map_smul, map_smul, map_smul, map_smul, h0, h1]
  have hj0_e0 : spinHalfSU2Rep.J_zero e0 = (1 / 2 : ℂ) • e0 := by
    ext i; fin_cases i <;> simp [spinHalfSU2Rep, InfoGeometry.Algebra.FiniteSpin.J_zero, e0]
  have hj0_e1 : spinHalfSU2Rep.J_zero e1 = -(1 / 2 : ℂ) • e1 := by
    ext i; fin_cases i <;> simp [spinHalfSU2Rep, InfoGeometry.Algebra.FiniteSpin.J_zero, e1]
  have hjp_e0 : spinHalfSU2Rep.J_plus e0 = 0 := by
    ext i; fin_cases i <;> simp [spinHalfSU2Rep, InfoGeometry.Algebra.FiniteSpin.J_plus, e0]
  have hjp_e1 : spinHalfSU2Rep.J_plus e1 = e0 := by
    ext i; fin_cases i <;> simp [spinHalfSU2Rep, InfoGeometry.Algebra.FiniteSpin.J_plus, e0, e1]
  have hjm_e0 : spinHalfSU2Rep.J_minus e0 = e1 := by
    ext i; fin_cases i <;> simp [spinHalfSU2Rep, InfoGeometry.Algebra.FiniteSpin.J_minus, e0, e1]
  have hjm_e1 : spinHalfSU2Rep.J_minus e1 = 0 := by
    ext i; fin_cases i <;> simp [spinHalfSU2Rep, InfoGeometry.Algebra.FiniteSpin.J_minus, e1]
  have hsqrt_re : (Real.sqrt 2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hsqrt_sq : (Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ) = 2 := by
    exact_mod_cast (by simp : (Real.sqrt 2 : ℝ) * Real.sqrt 2 = 2)
  have hsqrt_sq_pow : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by
    rw [sq, hsqrt_sq]
  have hsqrt_ne : (Real.sqrt 2 : ℂ) ≠ 0 := by
    intro h; rw [h, mul_zero] at hsqrt_sq; norm_num at hsqrt_sq
  have hc0_e0 : spinHalfSU2Rep.J_zero (T.comp 0 e0) = (1 / 2 : ℂ) • T.comp 0 e0 := by
    have h := congrArg (fun op : Module.End ℂ (Fin 2 → ℂ) => op e0) (T.comm_J_zero 0)
    simp only [LinearMap.sub_apply, Module.End.mul_apply, Int.cast_zero, zero_smul,
      hj0_e0, map_smul] at h
    exact sub_eq_zero.mp h
  have hc0_e1 : spinHalfSU2Rep.J_zero (T.comp 0 e1) = -(1 / 2 : ℂ) • T.comp 0 e1 := by
    have h := congrArg (fun op : Module.End ℂ (Fin 2 → ℂ) => op e1) (T.comm_J_zero 0)
    simp only [LinearMap.sub_apply, Module.End.mul_apply, Int.cast_zero, zero_smul,
      hj0_e1, map_smul] at h
    exact sub_eq_zero.mp h
  have hT0_e0_1 : (T.comp 0 e0) 1 = 0 := by
    have hv := congrFun hc0_e0 1
    dsimp [spinHalfSU2Rep, InfoGeometry.Algebra.FiniteSpin.J_zero] at hv
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at hv
    norm_num at hv
    linear_combination -hv
  have hT0_e1_0 : (T.comp 0 e1) 0 = 0 := by
    have hv := congrFun hc0_e1 0
    dsimp [spinHalfSU2Rep, InfoGeometry.Algebra.FiniteSpin.J_zero] at hv
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at hv
    norm_num at hv
    linear_combination hv
  set a : ℂ := (T.comp 0 e0) 0
  set b : ℂ := (T.comp 0 e1) 1
  have hT0_e0 : T.comp 0 e0 = a • e0 := by
    ext i; fin_cases i <;> simp [a, hT0_e0_1, e0]
  have hT0_e1 : T.comp 0 e1 = b • e1 := by
    ext i; fin_cases i <;> simp [b, hT0_e1_0, e1]
  have hrp0 : racahPlus 1 0 = (Real.sqrt 2 : ℂ) := by unfold racahPlus; norm_num
  have hT1_e0 : T.comp 1 e0 = 0 := by
    have h := congrArg (fun op : Module.End ℂ (Fin 2 → ℂ) => op e0) (T.comm_J_plus 0)
    simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply,
      hrp0, zero_add, hT0_e0, map_smul, hjp_e0, map_zero, smul_zero, sub_zero] at h
    exact (smul_eq_zero.mp h.symm).resolve_left hsqrt_ne
  have hT1_e1 : T.comp 1 e1 = ((b - a) / (Real.sqrt 2 : ℂ)) • e0 := by
    have h := congrArg (fun op : Module.End ℂ (Fin 2 → ℂ) => op e1) (T.comm_J_plus 0)
    simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply,
      hrp0, zero_add, hT0_e1, map_smul, hjp_e1, hT0_e0] at h
    have hs : (Real.sqrt 2 : ℂ) • T.comp 1 e1 = (b - a) • e0 := by
      rw [← h, sub_smul]
    have hs2 := congrArg (fun v => (1 / (Real.sqrt 2 : ℂ)) • v) hs
    rw [smul_smul, smul_smul, one_div, inv_mul_cancel₀ hsqrt_ne, one_smul] at hs2
    simpa [div_eq_mul_inv, mul_comm] using hs2
  have hrm1 : racahMinus 1 1 = (Real.sqrt 2 : ℂ) := by unfold racahMinus; norm_num
  have hb_eq : b = -a := by
    have h := congrArg (fun op : Module.End ℂ (Fin 2 → ℂ) => op e0) (T.comm_J_minus 1)
    simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply,
      hrm1, sub_self, hT1_e0, map_zero, hjm_e0, hT0_e0] at h
    rw [hT1_e1] at h
    have hv := congrFun h 0
    simp only [zero_sub, Pi.neg_apply, Pi.smul_apply, smul_eq_mul, e0, Pi.single_eq_same,
      mul_one] at hv
    have hv2 : -((b - a) / (Real.sqrt 2 : ℂ)) * (Real.sqrt 2 : ℂ) =
        ((Real.sqrt 2 : ℂ) * a) * (Real.sqrt 2 : ℂ) := by
      rw [hv]
    rw [neg_mul, div_mul_cancel₀ _ hsqrt_ne] at hv2
    have hv3 : -(b - a) = ((Real.sqrt 2 : ℂ) ^ 2) * a := by
      linear_combination hv2
    rw [hsqrt_sq_pow] at hv3
    linear_combination -hv3
  have ha_eq : a = r / 2 := by
    dsimp [r, a, e0]; ring
  have hrm0 : racahMinus 1 0 = (Real.sqrt 2 : ℂ) := by unfold racahMinus; norm_num
  have hTm1_e0 : T.comp (-1) e0 = (r / (Real.sqrt 2 : ℂ)) • e1 := by
    have h := congrArg (fun op : Module.End ℂ (Fin 2 → ℂ) => op e0) (T.comm_J_minus 0)
    simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply,
      hrm0, zero_sub, hT0_e0, map_smul, hjm_e0, hT0_e1] at h
    have hs : (Real.sqrt 2 : ℂ) • T.comp (-1) e0 = r • e1 := by
      rw [← h, ← sub_smul, hb_eq, ha_eq]
      congr 1; ring
    have hs2 := congrArg (fun v => (1 / (Real.sqrt 2 : ℂ)) • v) hs
    rw [smul_smul, smul_smul, one_div, inv_mul_cancel₀ hsqrt_ne, one_smul] at hs2
    simpa [div_eq_mul_inv, mul_comm] using hs2
  have hTm1_e1 : T.comp (-1) e1 = 0 := by
    have h := congrArg (fun op : Module.End ℂ (Fin 2 → ℂ) => op e1) (T.comm_J_minus 0)
    simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply,
      hrm0, zero_sub, hT0_e1, map_smul, hjm_e1, map_zero, smul_zero, sub_zero] at h
    exact (smul_eq_zero.mp h.symm).resolve_left hsqrt_ne
  by_cases hq1 : q = 1
  · subst hq1
    apply hbasis
    · change T.comp 1 e0 = r • vectorTensorComp spinHalfSU2Rep (Real.sqrt 2 : ℂ) 1 e0
      simp [vectorTensorComp, hT1_e0, hjp_e0]
    · change T.comp 1 e1 = r • vectorTensorComp spinHalfSU2Rep (Real.sqrt 2 : ℂ) 1 e1
      simp only [vectorTensorComp, ↓reduceIte, LinearMap.smul_apply, LinearMap.neg_apply,
        hjp_e1, hT1_e1, hb_eq, ha_eq, smul_neg, smul_smul]
      rw [← neg_smul]
      congr 1; ring
  · by_cases hq0 : q = 0
    · subst hq0
      apply hbasis
      · change T.comp 0 e0 = r • vectorTensorComp spinHalfSU2Rep (Real.sqrt 2 : ℂ) 0 e0
        simp only [vectorTensorComp, ↓reduceIte, hT0_e0, hj0_e0, ha_eq,
          smul_smul, show (0 : ℤ) ≠ 1 by decide]
        congr 1; ring
      · change T.comp 0 e1 = r • vectorTensorComp spinHalfSU2Rep (Real.sqrt 2 : ℂ) 0 e1
        simp only [vectorTensorComp, ↓reduceIte, hT0_e1, hj0_e1, hb_eq,
          ha_eq, smul_smul, show (0 : ℤ) ≠ 1 by decide]
        congr 1; ring
    · by_cases hqm1 : q = -1
      · subst hqm1
        apply hbasis
        · change T.comp (-1) e0 = r • vectorTensorComp spinHalfSU2Rep (Real.sqrt 2 : ℂ) (-1) e0
          simp only [vectorTensorComp, ↓reduceIte, hTm1_e0,
            show (-1 : ℤ) ≠ 1 by decide, show (-1 : ℤ) ≠ 0 by decide]
          rw [LinearMap.smul_apply, hjm_e0, smul_smul]
          congr 1; ring
        · change T.comp (-1) e1 = r • vectorTensorComp spinHalfSU2Rep (Real.sqrt 2 : ℂ) (-1) e1
          simp [vectorTensorComp, hTm1_e1, hjm_e1]
      · have hgt : (1 : ℤ) < |q| := by
          rcases abs_cases q with ⟨_, _⟩ | ⟨_, _⟩ <;> omega
        rw [T.support_zero q hgt,
          (vectorTensorOperator spinHalfSU2Rep).support_zero q hgt, smul_zero]

end InfoGeometry.Physics.NuclearAngularMomentum
