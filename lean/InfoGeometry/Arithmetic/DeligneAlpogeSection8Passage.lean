/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import InfoGeometry.Arithmetic.DeligneAlpogeBoundSynthesis
import InfoGeometry.LinearAlgebra.TraceInvariantSubmodule

/-!
# InfoGeometry.Arithmetic.DeligneAlpogeSection8Passage

Section 8 cohomological-spectral passage reductions for `hexagon:2611.00789v1`,
using rank-nullity (`LinearMap.injective_iff_surjective`) so every step holds
regardless of non-diagonalizable Jordan blocks:

1. `stalk_base_change_weight_bound`: propagates closed-point degree-`e` bounds
   `‖α ^ e‖ ≤ q ^ (e * w / 2)` down to `‖α‖ ≤ q ^ (w / 2)`.
2. `equivariant_surjection_eigenvalue_lift` & `gysin_tate_twist_degree_step`:
   lifts eigenvalues across equivariant surjections and propagates weight bounds
   across Gysin `+2` Tate-twist steps `H^{i-2}_c(Y)(-1) ↠ H^i_c(U)`.
3. `excision_exact_sequence_eigenvalue_dichotomy`: splits eigenvalues of a
   middle object `VM` in a 3-term equivariant exact sequence `VL → VM → VR`
   into eigenvalues of `VL` or `VR`.
4. `poincare_duality_pairing_eigenvalue` & `smooth_proper_poincare_purity_synthesis`:
   extracts the dual eigenvalue `q ^ d / α` via a nondegenerate pairing and
   combines both bounds via `poincare_duality_purity_eq` to conclude exact
   purity `‖α‖ = q ^ ((w + i) / 2)`.
-/

noncomputable section

namespace InfoGeometry.Arithmetic.DeligneAlpogeSection8Passage

open InfoGeometry.Arithmetic.DeligneAlpogeBoundSynthesis
open InfoGeometry.Arithmetic.AlpogeDeligneSignOnlyCore
open InfoGeometry.LinearAlgebra.TraceInvariantSubmodule

theorem kernel_invariant_of_intertwining
    {K V W : Type*} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (F : Module.End K V) (G : Module.End K W) (π : V →ₗ[K] W)
    (hcomm : π.comp F = G.comp π) :
    LinearMap.ker π ≤ Submodule.comap F (LinearMap.ker π) := by
  intro x hx
  rw [Submodule.mem_comap, LinearMap.mem_ker]
  have h := LinearMap.congr_fun hcomm x
  simpa [LinearMap.comp_apply, LinearMap.mem_ker.mp hx] using h

/-! ### Finite-dimensional equivariant exact-sequence trace decomposition

This turns the scalar trace additivity used in sign-alignment arguments into a
statement derived from an actual surjective intertwining map. The kernel term
is the induced endomorphism on the kernel, and the quotient term is identified
with the given target endomorphism. -/

theorem trace_pow_eq_kernel_add_codomain_of_equivariant_surjection
    {K V W : Type*} [Field K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (F : Module.End K V) (G : Module.End K W) (π : V →ₗ[K] W)
    (hπ : Function.Surjective π)
    (hcomm : π.comp F = G.comp π) (n : ℕ) :
    LinearMap.trace K V (F ^ n) =
      LinearMap.trace K (LinearMap.ker π)
        (InfoGeometry.LinearAlgebra.TraceInvariantSubmodule.invariantRestriction
          F (LinearMap.ker π)
          (kernel_invariant_of_intertwining F G π hcomm) ^ n) +
      LinearMap.trace K W (G ^ n) := by
  let S : Submodule K V := LinearMap.ker π
  have hS : S ≤ Submodule.comap F S := by
    simpa [S] using kernel_invariant_of_intertwining F G π hcomm
  let QF : Module.End K (V ⧸ S) :=
    LinearAlgebra.TraceInvariantSubmodule.invariantQuotientMap F S hS
  let e : (V ⧸ S) ≃ₗ[K] W := π.quotKerEquivOfSurjective hπ
  have hconj : e.conjRingEquiv QF = G := by
    apply LinearMap.ext
    intro y
    change e (QF (e.symm y)) = G y
    obtain ⟨x, rfl⟩ := hπ y
    rw [π.quotKerEquivOfSurjective_symm_apply hπ x]
    change e (Submodule.mapQ S S F hS (Submodule.Quotient.mk x)) = G (π x)
    rw [Submodule.mapQ_apply, π.quotKerEquivOfSurjective_apply_mk]
    change π (F x) = G (π x)
    exact LinearMap.congr_fun hcomm x
  have hpowConj : e.conjRingEquiv (QF ^ n) = G ^ n := by
    rw [map_pow, hconj]
  have htrace :=
    trace_pow_eq_trace_restriction_pow_add_trace_quotient_pow F S hS n
  have hquot : LinearMap.trace K (V ⧸ S) (QF ^ n) =
      LinearMap.trace K W (G ^ n) := by
    rw [← hpowConj]
    exact (LinearMap.trace_conj' (QF ^ n) e).symm
  calc
    LinearMap.trace K V (F ^ n) =
        LinearMap.trace K S (invariantRestriction F S hS ^ n) +
          LinearMap.trace K (V ⧸ S) (QF ^ n) := by
            simpa [QF] using htrace
    _ = _ := by rw [hquot]

/-- The degree-`d₀` term in the scalar `+2` sign-alignment identity can be
derived from an actual finite-dimensional equivariant surjection. The higher
degree shift and low-degree vanishing remain explicit inputs. -/
theorem gysin_sign_aligned_trace_of_equivariant_surjection
    (d₀ : ℕ) (TX TY : ℕ → ℂ)
    {V W : Type*}
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (FY : Module.End ℂ V) (FX : Module.End ℂ W) (π : V →ₗ[ℂ] W)
    (hπ : Function.Surjective π)
    (hcomm : π.comp FY = FX.comp π)
    (hTY : TY d₀ = LinearMap.trace ℂ V FY)
    (hTX : TX (d₀ + 2) = LinearMap.trace ℂ W FX)
    (hX_low : ∀ b : ℕ, b < d₀ + 1 → TX b = 0)
    (hY_low : ∀ a : ℕ, a < d₀ → TY a = 0)
    (hIso : ∀ a : ℕ, d₀ < a → TY a = TX (a + 2)) :
    (∑ a ∈ Finset.range (2 * d₀ + 1), (-1 : ℂ) ^ a * TY a) -
      (∑ b ∈ Finset.range (2 * d₀ + 3), (-1 : ℂ) ^ b * TX b) =
    (-1 : ℂ) ^ d₀ *
      (LinearMap.trace ℂ (LinearMap.ker π)
        (invariantRestriction FY (LinearMap.ker π)
          (kernel_invariant_of_intertwining FY FX π hcomm)) + TX (d₀ + 1)) := by
  have hSES : TY d₀ =
      LinearMap.trace ℂ (LinearMap.ker π)
        (invariantRestriction FY (LinearMap.ker π)
          (kernel_invariant_of_intertwining FY FX π hcomm)) + TX (d₀ + 2) := by
    rw [hTY, hTX]
    simpa using
      (trace_pow_eq_kernel_add_codomain_of_equivariant_surjection FY FX π hπ hcomm 1)
  exact gysin_plus_two_same_sign_remainder d₀ TX TY _ hX_low hY_low hSES hIso

theorem nonneg_eq_of_sq_eq {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : a ^ 2 = b ^ 2) :
    a = b := by
  have hfac : (a - b) * (a + b) = 0 := by linarith [h]
  rcases mul_eq_zero.mp hfac with h1 | h2
  · linarith [h1]
  · linarith [ha, hb, h2]

theorem complex_norm_ofReal_pos {q : ℝ} (hq : 0 < q) : ‖(q : ℂ)‖ = q := by
  refine nonneg_eq_of_sq_eq (norm_nonneg _) hq.le ?_
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_ofReal]; ring

/-! ### 1. Closed-Point Base-Change Stalk Weight Propagation -/

theorem stalk_base_change_weight_bound {α : ℂ} {q w : ℝ} {e : ℕ}
    (hq : 0 < q) (he : 1 ≤ e) (hpow : ‖α ^ e‖ ≤ q ^ ((e : ℝ) * (w / 2))) :
    ‖α‖ ≤ q ^ (w / 2) := by
  have he_pos : (0 : ℝ) < e := Nat.cast_pos.mpr (lt_of_lt_of_le zero_lt_one he)
  rw [norm_pow, ← Real.rpow_natCast] at hpow
  have hrpow := Real.rpow_le_rpow (Real.rpow_nonneg (norm_nonneg α) e) hpow
    (inv_nonneg.mpr he_pos.le)
  rw [← Real.rpow_mul (norm_nonneg α), mul_inv_cancel₀ (ne_of_gt he_pos),
    Real.rpow_one, ← Real.rpow_mul hq.le] at hrpow
  have hexp : (e : ℝ) * (w / 2) * (e : ℝ)⁻¹ = w / 2 := by
    field_simp [ne_of_gt he_pos]
  rwa [hexp] at hrpow

/-! ### 2. Jordan-Safe Equivariant Surjection Lift & Gysin `+2` Tate-Twist Step -/

theorem equivariant_surjection_eigenvalue_lift
    {K W Q : Type*} [Field K]
    [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    [AddCommGroup Q] [Module K Q] [FiniteDimensional K Q]
    (FW : W →ₗ[K] W) (FQ : Q →ₗ[K] Q) (π : W →ₗ[K] Q)
    (hπ : Function.Surjective π) (heq : ∀ x : W, π (FW x) = FQ (π x))
    {α : K} {v : Q} (hv : v ≠ 0) (hFv : FQ v = α • v) :
    ∃ u : W, u ≠ 0 ∧ FW u = α • u := by
  by_contra hall
  push Not at hall
  let TW : W →ₗ[K] W := FW - α • LinearMap.id
  let TQ : Q →ₗ[K] Q := FQ - α • LinearMap.id
  have hinjW : Function.Injective TW := by
    intro x y hxy
    by_contra hne
    have h0 : TW (x - y) = 0 := by rw [map_sub, hxy, sub_self]
    have hsub : FW (x - y) - α • (x - y) = 0 := by simpa [TW] using h0
    exact hall (x - y) (sub_ne_zero.mpr hne) (sub_eq_zero.mp hsub)
  have hsurjW : Function.Surjective TW := LinearMap.injective_iff_surjective.mp hinjW
  have hsurjQ : Function.Surjective TQ := by
    intro y
    obtain ⟨w, rfl⟩ := hπ y
    obtain ⟨w₀, hw₀⟩ := hsurjW w
    refine ⟨π w₀, ?_⟩
    calc TQ (π w₀) = FQ (π w₀) - α • π w₀ := rfl
      _ = π (FW w₀ - α • w₀) := by rw [map_sub, heq, map_smul]
      _ = π (TW w₀) := rfl
      _ = π w := by rw [hw₀]
  have hinjQ : Function.Injective TQ := LinearMap.injective_iff_surjective.mpr hsurjQ
  have hv0 : TQ v = 0 := by simp [TQ, hFv]
  exact hv (hinjQ (hv0.trans (map_zero TQ).symm))

theorem gysin_tate_twist_degree_step
    {W Q : Type*}
    [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    [AddCommGroup Q] [Module ℂ Q] [FiniteDimensional ℂ Q]
    (FY : W →ₗ[ℂ] W) (FU : Q →ₗ[ℂ] Q) (π : W →ₗ[ℂ] Q)
    {q w i : ℝ} (hq : 0 < q)
    (hπ : Function.Surjective π)
    (heq : ∀ x : W, π ((q : ℂ) • FY x) = FU (π x))
    (hY_bound : ∀ (β : ℂ) (u : W), u ≠ 0 → FY u = β • u →
      ‖β‖ ≤ q ^ ((w + (i - 2)) / 2))
    {α : ℂ} {v : Q} (hv : v ≠ 0) (hFv : FU v = α • v) :
    ‖α‖ ≤ q ^ ((w + i) / 2) := by
  obtain ⟨u, hu0, hu_eq⟩ :=
    equivariant_surjection_eigenvalue_lift ((q : ℂ) • FY) FU π hπ heq hv hFv
  have hq_ne : (q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hq)
  let β : ℂ := (q : ℂ)⁻¹ * α
  have hFYu : FY u = β • u := by
    have hsmul : (q : ℂ) • FY u = α • u := hu_eq
    calc FY u = ((q : ℂ)⁻¹ * (q : ℂ)) • FY u := by simp [inv_mul_cancel₀ hq_ne]
      _ = (q : ℂ)⁻¹ • ((q : ℂ) • FY u) := mul_smul _ _ _
      _ = (q : ℂ)⁻¹ • (α • u) := by rw [hsmul]
      _ = β • u := (mul_smul _ _ _).symm
  have hβ := hY_bound β u hu0 hFYu
  have hα_eq : α = (q : ℂ) * β := by
    dsimp [β]; rw [← mul_assoc, mul_inv_cancel₀ hq_ne, one_mul]
  calc ‖α‖ = ‖(q : ℂ) * β‖ := by rw [hα_eq]
    _ = q * ‖β‖ := by rw [norm_mul, complex_norm_ofReal_pos hq]
    _ ≤ q ^ (1 : ℝ) * q ^ ((w + (i - 2)) / 2) := by
          rw [Real.rpow_one]; exact mul_le_mul_of_nonneg_left hβ hq.le
    _ = q ^ ((w + i) / 2) := by
          rw [← Real.rpow_add hq]; congr 1; ring

/-! ### 3. Open–Closed Excision Exact-Sequence Eigenvalue Dichotomy -/

theorem excision_exact_sequence_eigenvalue_dichotomy
    {K VL VM VR : Type*} [Field K]
    [AddCommGroup VL] [Module K VL] [FiniteDimensional K VL]
    [AddCommGroup VM] [Module K VM]
    [AddCommGroup VR] [Module K VR]
    (FL : VL →ₗ[K] VL) (FM : VM →ₗ[K] VM) (FR : VR →ₗ[K] VR)
    (f : VL →ₗ[K] VM) (g : VM →ₗ[K] VR)
    (heqL : ∀ y : VL, f (FL y) = FM (f y))
    (heqR : ∀ x : VM, g (FM x) = FR (g x))
    (hexact : ∀ x : VM, g x = 0 → ∃ y : VL, f y = x)
    {α : K} {v : VM} (hv : v ≠ 0) (hFv : FM v = α • v) :
    (∃ y : VL, y ≠ 0 ∧ FL y = α • y) ∨ (∃ z : VR, z ≠ 0 ∧ FR z = α • z) := by
  by_cases hgv : g v = 0
  · left
    let W : Submodule K VM := LinearMap.range f
    have hW_inv : ∀ w ∈ W, FM w ∈ W := by
      rintro _ ⟨y, rfl⟩; exact ⟨FL y, heqL y⟩
    let FW : W →ₗ[K] W := FM.restrict hW_inv
    let vw : W := ⟨v, hexact v hgv⟩
    have hvw0 : vw ≠ 0 := fun h0 => hv (congrArg Subtype.val h0)
    have hFWv : FW vw = α • vw := Subtype.ext hFv
    exact equivariant_surjection_eigenvalue_lift FL FW f.rangeRestrict
      f.surjective_rangeRestrict (fun y => Subtype.ext (heqL y)) hvw0 hFWv
  · right
    refine ⟨g v, hgv, ?_⟩
    rw [← heqR v, hFv, map_smul]

/-! ### 4. Poincaré Duality Bilinear Pairing & Theorem 1(b) Purity -/

theorem poincare_duality_pairing_eigenvalue
    {K V Vdual : Type*} [Field K]
    [AddCommGroup V] [Module K V]
    [AddCommGroup Vdual] [Module K Vdual] [FiniteDimensional K Vdual]
    (B : V →ₗ[K] Vdual →ₗ[K] K)
    (hB : ∀ x : V, (∀ y : Vdual, B x y = 0) → x = 0)
    (F : V →ₗ[K] V) (Fdual : Vdual →ₗ[K] Vdual) (qd : K)
    (hpair : ∀ (x : V) (y : Vdual), B (F x) (Fdual y) = qd * B x y)
    {α : K} (hα : α ≠ 0) {v : V} (hv : v ≠ 0) (hFv : F v = α • v) :
    ∃ u : Vdual, u ≠ 0 ∧ Fdual u = (qd / α) • u := by
  by_contra hall
  push Not at hall
  let Tdual : Vdual →ₗ[K] Vdual := Fdual - (qd / α) • LinearMap.id
  have hinj : Function.Injective Tdual := by
    intro y₁ y₂ hy
    by_contra hne
    have h0 : Tdual (y₁ - y₂) = 0 := by rw [map_sub, hy, sub_self]
    have hsub : Fdual (y₁ - y₂) - (qd / α) • (y₁ - y₂) = 0 := by simpa [Tdual] using h0
    exact hall (y₁ - y₂) (sub_ne_zero.mpr hne) (sub_eq_zero.mp hsub)
  have hsurj : Function.Surjective Tdual := LinearMap.injective_iff_surjective.mp hinj
  have hv_zero : ∀ y : Vdual, B v y = 0 := by
    intro y
    obtain ⟨y₀, rfl⟩ := hsurj y
    have hmul : α * B v (Tdual y₀) = 0 := by
      dsimp [Tdual]
      rw [map_sub, map_smul, smul_eq_mul, mul_sub]
      have h1 : α * B v (Fdual y₀) = qd * B v y₀ := by
        calc α * B v (Fdual y₀) = B (α • v) (Fdual y₀) := by
              rw [map_smul, LinearMap.smul_apply, smul_eq_mul]
          _ = B (F v) (Fdual y₀) := by rw [hFv]
          _ = qd * B v y₀ := hpair v y₀
      have h2 : α * (qd / α * B v y₀) = qd * B v y₀ := by
        field_simp [hα]
      rw [h1, h2, sub_self]
    exact (mul_eq_zero.mp hmul).resolve_left hα
  exact hv (hB v hv_zero)

theorem smooth_proper_poincare_purity_synthesis
    {V Vdual : Type*}
    [AddCommGroup V] [Module ℂ V]
    [AddCommGroup Vdual] [Module ℂ Vdual] [FiniteDimensional ℂ Vdual]
    (B : V →ₗ[ℂ] Vdual →ₗ[ℂ] ℂ)
    (hB : ∀ x : V, (∀ y : Vdual, B x y = 0) → x = 0)
    (F : V →ₗ[ℂ] V) (Fdual : Vdual →ₗ[ℂ] Vdual)
    {q w i : ℝ} (d : ℕ) (hq : 0 < q)
    (hpair : ∀ (x : V) (y : Vdual), B (F x) (Fdual y) = ((q ^ d : ℝ) : ℂ) * B x y)
    (hF_upper : ∀ (α : ℂ) (x : V), x ≠ 0 → F x = α • x → ‖α‖ ≤ q ^ ((w + i) / 2))
    (hFdual_upper : ∀ (β : ℂ) (y : Vdual), y ≠ 0 → Fdual y = β • y →
      ‖β‖ ≤ q ^ ((-w + (2 * (d : ℝ) - i)) / 2))
    {α : ℂ} {v : V} (hv : v ≠ 0) (hFv : F v = α • v) :
    ‖α‖ = q ^ ((w + i) / 2) := by
  have hqd_pos : 0 < q ^ d := pow_pos hq d
  have hα_ne : α ≠ 0 := by
    intro h0
    subst h0
    have hall : ∀ y : Vdual, B v y = 0 := by
      intro y
      have hp := hpair v y
      rw [hFv, zero_smul, map_zero, LinearMap.zero_apply] at hp
      have hne : ((q ^ d : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hqd_pos)
      exact (mul_eq_zero.mp hp.symm).resolve_left hne
    exact hv (hB v hall)
  obtain ⟨u, hu0, hFu⟩ := poincare_duality_pairing_eigenvalue B hB F Fdual
    ((q ^ d : ℝ) : ℂ) hpair hα_ne hv hFv
  let β : ℂ := ((q ^ d : ℝ) : ℂ) / α
  have hprod : ‖α * β‖ = q ^ (d : ℝ) := by
    have hab : α * β = ((q ^ d : ℝ) : ℂ) := mul_div_cancel₀ _ hα_ne
    rw [hab, complex_norm_ofReal_pos hqd_pos, Real.rpow_natCast]
  exact poincare_duality_purity_eq hq hprod (hF_upper α v hv hFv)
    (hFdual_upper β u hu0 hFu)

end InfoGeometry.Arithmetic.DeligneAlpogeSection8Passage
