/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.SouriauBostConnesTransition
import InfoGeometry.Canonical.ConcreteHilbertSewnAnomaly
import InfoGeometry.Canonical.FormalPrimeRootSystem
import Mathlib.Data.ZMod.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic

/-!
# Souriau–Bost–Connes Profinite Galois KMS Simplex, Trace-Ideal Anomaly Cancellation, and Primon Souriau–Fisher Hessian

Extends `InfoGeometry.Canonical.SouriauBostConnesTransition` along three exact mathematical axes:

1. **Profinite Unit Group `\widehat{\mathbb{Z}}^\times` and Extremal `\mathrm{KMS}_\beta` Phase States (`β > 1`):**
   - `ProfiniteUnits`: projective limit `lim (ZMod m)ˣ` over `m : ℕ+` with divisibility compatibility,
     group structure, and nontrivial element `negOne ≠ 1`.
   - `bcKMSPhaseState`: concrete Bost–Connes extremal `\mathrm{KMS}_\beta` phase state
     `φ_{β, χ}(e(a/m)) = Z(β)⁻¹ ∑_{n ≥ 1} n^{-β} χ_m(n) e(a n / m)` with scaling invariance,
     Galois equivariance under `ProfiniteUnits`, finite convex-combination normalization,
     zero-temperature limit `φ_{β, χ}(e(a/m)) → χ(e(a/m))` as `β → ∞`, separation of distinct
     profinite characters, spontaneous symmetry breaking witness, and high-temperature `β ≤ 1` divergence.

2. **Sewn Operator Subalgebra and Anti-Sewn Chiral Trace Ideal on `H_lp ℝ`:**
   - `SewnOperatorSubalgebra`: noncommutative `ℝ`-subalgebra of `J_lp_clm`-invariant bounded
     operators on `H_lp ℝ` containing the Cuntz `O₂` shifts `S_left_lp_clm`, `S_right_lp_clm`.
   - `IsAntiSewn`: two-sided `SewnOperatorSubalgebra`-bimodule of `J_lp_clm`-anticommuting
     operators containing `epsilon_lp_clm` and odd products, with vanishing expectation on
     `J_lp_clm`-fixed states, vanishing `tsum` chiral trace on `J_lp_clm`-paired families,
     and invariance under `J_lp_clm`-intertwining orthogonal conjugation.

3. **Exact Finite Primon Souriau–Fisher Log-Partition Hessian:**
   - Proves exact first derivative `d/dβ log Z_P(β) = -E_P(β)` and second derivative
     `d/dβ (-E_P(β)) = g_P^{SF}(β) > 0` (Souriau–Fisher variance) on finite prime lattices.
-/

noncomputable section

namespace InfoGeometry.Canonical.SouriauBostConnesKMSAndTraceIdeal

open scoped BigOperators ComplexConjugate
open Filter
open InfoGeometry.Canonical.SouriauBostConnesTransition
open InfoGeometry.Canonical.FormalPrimeRootSystem
open InfoGeometry.Canonical.ConcreteHilbertCommutation
open InfoGeometry.Canonical.ConcreteHilbertCuntzO2
open InfoGeometry.Canonical.ConcreteHilbertSewnAnomaly

/-! ## 1. Profinite Unit Group `\widehat{\mathbb{Z}}^\times = \varprojlim (\mathbb{Z}/m\mathbb{Z})^\times` -/

/-- Projective limit of unit groups `(\mathbb{Z}/m\mathbb{Z})ˣ` over `m : ℕ+`, modeling `\widehat{\mathbb{Z}}^\times`. -/
@[ext]
structure ProfiniteUnits where
  component : ∀ m : ℕ+, (ZMod m)ˣ
  compat : ∀ {m n : ℕ+} (h : (m : ℕ) ∣ (n : ℕ)),
    ZMod.castHom h (ZMod m) (component n : ZMod n) = (component m : ZMod m)

namespace ProfiniteUnits

instance : One ProfiniteUnits where
  one :=
    { component := fun _ => 1
      compat := fun h => by simp [map_one] }

instance : Mul ProfiniteUnits where
  mul χ ψ :=
    { component := fun m => χ.component m * ψ.component m
      compat := fun {m n} h => by
        simp only [Units.val_mul, map_mul, χ.compat h, ψ.compat h] }

instance : Inv ProfiniteUnits where
  inv χ :=
    { component := fun m => (χ.component m)⁻¹
      compat := fun {m n} h => by
        let f : ZMod n →+* ZMod m := ZMod.castHom h (ZMod m)
        have hf_unit : Units.map f.toMonoidHom (χ.component n) = χ.component m := by
          ext1
          exact χ.compat h
        have hinv := congrArg (fun u : (ZMod m)ˣ => ((u⁻¹ : (ZMod m)ˣ) : ZMod m)) hf_unit
        simpa [f, map_inv] using hinv }

@[simp] theorem one_component (m : ℕ+) : (1 : ProfiniteUnits).component m = 1 := rfl
@[simp] theorem mul_component (χ ψ : ProfiniteUnits) (m : ℕ+) :
    (χ * ψ).component m = χ.component m * ψ.component m := rfl
@[simp] theorem inv_component (χ : ProfiniteUnits) (m : ℕ+) :
    (χ⁻¹).component m = (χ.component m)⁻¹ := rfl

instance : Group ProfiniteUnits where
  mul_assoc a b c := by ext m; simp [mul_assoc]
  one_mul a := by ext m; simp
  mul_one a := by ext m; simp
  inv_mul_cancel a := by ext m; simp

/-- Canonical projection homomorphism `\widehat{\mathbb{Z}}^\times →* (ZMod m)ˣ`. -/
def proj (m : ℕ+) : ProfiniteUnits →* (ZMod m)ˣ where
  toFun χ := χ.component m
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The nontrivial sign involution `-1 ∈ \widehat{\mathbb{Z}}^\times`. -/
def negOne : ProfiniteUnits where
  component _ := -1
  compat {m n} h := by
    change ZMod.castHom h (ZMod m) (-1 : ZMod n) = (-1 : ZMod m)
    rw [map_neg, map_one]

/-- `-1 ≠ 1` in `ProfiniteUnits` (witnessed at modulus `3`). -/
theorem negOne_ne_one : negOne ≠ 1 := by
  intro h
  let m3 : ℕ+ := ⟨3, by norm_num⟩
  have h3 : negOne.component m3 = (1 : ProfiniteUnits).component m3 :=
    congrArg (fun χ : ProfiniteUnits => χ.component m3) h
  have h3v := congrArg (fun u : (ZMod m3)ˣ => (u : ZMod m3)) h3
  change (-1 : ZMod 3) = (1 : ZMod 3) at h3v
  revert h3v
  decide

end ProfiniteUnits

/-! ## 2. Concrete Bost–Connes `\mathrm{KMS}_β` Phase States (`β > 1`) & Galois Action -/

/-- Phase character factor `exp(2πi * a * n * χ_m / m)` for rational generator `e(a/m)`. -/
def bcPhaseChar (χ : ProfiniteUnits) (a : ℤ) (m : ℕ+) (n : ℕ) : ℂ :=
  Complex.exp
    (((2 * Real.pi *
      (((a * (n : ℤ) * ((χ.component m : ZMod m).val : ℤ) : ℤ) : ℝ) / (m : ℝ)) : ℝ) : ℂ) *
      Complex.I)

theorem norm_bcPhaseChar (χ : ProfiniteUnits) (a : ℤ) (m : ℕ+) (n : ℕ) :
    ‖bcPhaseChar χ a m n‖ = 1 := by
  unfold bcPhaseChar
  exact Complex.norm_exp_ofReal_mul_I _

@[simp] theorem bcPhaseChar_zero (χ : ProfiniteUnits) (m : ℕ+) (n : ℕ) :
    bcPhaseChar χ 0 m n = 1 := by
  simp [bcPhaseChar]

private lemma exp_two_pi_mul_I_mul_div_int_eq_of_zmod
    {m : ℕ+} {u v : ℤ} (huv : (u : ZMod m) = (v : ZMod m)) (c : ℤ) :
    Complex.exp (((2 * Real.pi * (((c * u : ℤ) : ℝ) / (m : ℝ)) : ℝ) : ℂ) * Complex.I) =
      Complex.exp (((2 * Real.pi * (((c * v : ℤ) : ℝ) / (m : ℝ)) : ℝ) : ℂ) * Complex.I) := by
  have hdvd : (m : ℤ) ∣ (u - v) :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd (u - v) m).mp (by simp [huv])
  rcases hdvd with ⟨t, ht⟩
  have hdiff_int : u = v + (m : ℤ) * t := by linarith
  have hm_ne : (m : ℝ) ≠ 0 := by exact_mod_cast m.ne_zero
  have hexp_split :
      (((2 * Real.pi * (((c * u : ℤ) : ℝ) / (m : ℝ)) : ℝ) : ℂ) * Complex.I) =
        (((2 * Real.pi * (((c * v : ℤ) : ℝ) / (m : ℝ)) : ℝ) : ℂ) * Complex.I) +
          ((c * t : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
    rw [hdiff_int]
    push_cast
    field_simp [hm_ne]
  rw [hexp_split, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- Compatibility of `bcPhaseChar` under rational fraction scaling `(a, m) ↦ (k * a, k * m)`. -/
theorem bcPhaseChar_scale (χ : ProfiniteUnits) (a : ℤ) (m k : ℕ+) (n : ℕ) :
    bcPhaseChar χ ((k : ℤ) * a) (k * m) n = bcPhaseChar χ a m n := by
  let km : ℕ+ := k * m
  have hdiv : (m : ℕ) ∣ (km : ℕ) := ⟨(k : ℕ), by simp [km, PNat.mul_coe, mul_comm]⟩
  have hcast :
      (((χ.component km : ZMod km).val : ℤ) : ZMod m) =
        (((χ.component m : ZMod m).val : ℤ) : ZMod m) := by
    have hcomp := χ.compat hdiv
    calc
      (((χ.component km : ZMod km).val : ℤ) : ZMod m)
          = ZMod.castHom hdiv (ZMod m) ((χ.component km : ZMod km).val : ZMod km) := by simp
      _ = ZMod.castHom hdiv (ZMod m) (χ.component km : ZMod km) := by
            rw [ZMod.natCast_zmod_val]
      _ = (χ.component m : ZMod m) := hcomp
      _ = (((χ.component m : ZMod m).val : ℤ) : ZMod m) := by
            simp [ZMod.natCast_zmod_val]
  have hfrac :
      (((((k : ℤ) * a * (n : ℤ) * ((χ.component km : ZMod km).val : ℤ) : ℤ) : ℝ) /
          (km : ℝ))) =
        ((((a * (n : ℤ)) * ((χ.component km : ZMod km).val : ℤ) : ℤ) : ℝ) / (m : ℝ)) := by
    have hk_ne : (k : ℝ) ≠ 0 := by exact_mod_cast k.ne_zero
    have hm_ne : (m : ℝ) ≠ 0 := by exact_mod_cast m.ne_zero
    have hkm : (km : ℝ) = (k : ℝ) * (m : ℝ) := by
      change ((k * m : ℕ+) : ℝ) = (k : ℝ) * (m : ℝ)
      exact_mod_cast PNat.mul_coe k m
    rw [hkm]
    push_cast
    field_simp [hk_ne, hm_ne]
  have heq_base :
      bcPhaseChar χ ((k : ℤ) * a) (k * m) n =
        Complex.exp
          (((2 * Real.pi *
            ((((a * (n : ℤ)) * ((χ.component km : ZMod km).val : ℤ) : ℤ) : ℝ) / (m : ℝ)) : ℝ) : ℂ) *
            Complex.I) := by
    change
      Complex.exp
        (((2 * Real.pi *
          (((((k : ℤ) * a * (n : ℤ) * ((χ.component km : ZMod km).val : ℤ) : ℤ) : ℝ) / (km : ℝ))) : ℝ) : ℂ) *
          Complex.I) = _
    rw [hfrac]
  rw [heq_base]
  simpa [bcPhaseChar, mul_assoc] using
    exp_two_pi_mul_I_mul_div_int_eq_of_zmod hcast (a * (n : ℤ))

/-- Multiplication in `ProfiniteUnits` acts on `bcPhaseChar` by twisting the numerator `a`. -/
theorem bcPhaseChar_mul_profinite (χ ψ : ProfiniteUnits) (a : ℤ) (m : ℕ+) (n : ℕ) :
    bcPhaseChar (χ * ψ) a m n =
      bcPhaseChar χ (a * ((ψ.component m : ZMod m).val : ℤ)) m n := by
  have hzmod :
      ((((χ * ψ).component m : ZMod m).val : ℤ) : ZMod m) =
        ((((χ.component m : ZMod m).val : ℤ) * ((ψ.component m : ZMod m).val : ℤ) : ℤ) : ZMod m) := by
    have h1 : ((((χ * ψ).component m : ZMod m).val : ℤ) : ZMod m) = ((χ * ψ).component m : ZMod m) := by
      simpa using ZMod.natCast_zmod_val ((χ * ψ).component m : ZMod m)
    have h2 : (((χ.component m : ZMod m).val : ℤ) : ZMod m) = (χ.component m : ZMod m) := by
      simpa using ZMod.natCast_zmod_val (χ.component m : ZMod m)
    have h3 : (((ψ.component m : ZMod m).val : ℤ) : ZMod m) = (ψ.component m : ZMod m) := by
      simpa using ZMod.natCast_zmod_val (ψ.component m : ZMod m)
    rw [h1, ProfiniteUnits.mul_component, Units.val_mul, Int.cast_mul, h2, h3]
  have h1 :=
    exp_two_pi_mul_I_mul_div_int_eq_of_zmod hzmod (a * (n : ℤ))
  unfold bcPhaseChar
  have h1' :
      Complex.exp
        (((2 * Real.pi *
          ((((a * (n : ℤ)) * (((χ * ψ).component m : ZMod m).val : ℤ) : ℤ) : ℝ) / (m : ℝ)) : ℝ) : ℂ) *
          Complex.I) =
      Complex.exp
        (((2 * Real.pi *
          ((((a * (n : ℤ)) * (((χ.component m : ZMod m).val : ℤ) * ((ψ.component m : ZMod m).val : ℤ)) : ℤ) : ℝ) / (m : ℝ)) : ℝ) : ℂ) *
          Complex.I) := h1
  have hlhs :
      (((a * (n : ℤ) * (((χ * ψ).component m : ZMod m).val : ℤ) : ℤ) : ℝ) / (m : ℝ)) =
        ((((a * (n : ℤ)) * (((χ * ψ).component m : ZMod m).val : ℤ) : ℤ) : ℝ) / (m : ℝ)) := by
    push_cast; ring
  have hrhs :
      ((((a * (n : ℤ)) * (((χ.component m : ZMod m).val : ℤ) * ((ψ.component m : ZMod m).val : ℤ)) : ℤ) : ℝ) / (m : ℝ)) =
        (((a * ((ψ.component m : ZMod m).val : ℤ) * (n : ℤ) * ((χ.component m : ZMod m).val : ℤ) : ℤ) : ℝ) / (m : ℝ)) := by
    push_cast; ring
  rw [hlhs, h1', hrhs]

/-- Concrete extremal Bost–Connes `\mathrm{KMS}_β` state on `e(a/m)` at inverse temperature `β > 1`. -/
def bcKMSPhaseState (β : ℝ) (_hβ : 1 < β) (χ : ProfiniteUnits) (a : ℤ) (m : ℕ+) : ℂ :=
  (dirichletSeriesBC β _hβ : ℂ)⁻¹ *
    ∑' n : ℕ, if n = 0 then (0 : ℂ) else Complex.ofReal ((n : ℝ) ^ (-β)) * bcPhaseChar χ a m n

/-- Summability of the extremal Bost–Connes `\mathrm{KMS}_β` phase series for `β > 1`. -/
theorem bcKMSPhaseState_summable {β : ℝ} (hβ : 1 < β) (χ : ProfiniteUnits) (a : ℤ) (m : ℕ+) :
    Summable (fun n : ℕ => if n = 0 then (0 : ℂ) else Complex.ofReal ((n : ℝ) ^ (-β)) * bcPhaseChar χ a m n) := by
  have h_rpow : Summable (fun n : ℕ => (n : ℝ) ^ (-β)) :=
    Real.summable_nat_rpow.mpr (by linarith [hβ])
  refine h_rpow.of_norm_bounded (fun n => ?_)
  by_cases hn : n = 0
  · subst hn
    simp only [↓reduceIte, norm_zero, Nat.cast_zero]
    exact Real.rpow_nonneg (le_refl (0 : ℝ)) (-β)
  · simp only [hn, ↓reduceIte]
    rw [norm_mul, Complex.norm_real, norm_bcPhaseChar, mul_one,
      Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)]

/-- Normalization at the identity element `e(0/m) = 1`: `φ_{β, χ}(1) = 1`. -/
theorem bcKMSPhaseState_zero {β : ℝ} (hβ : 1 < β) (χ : ProfiniteUnits) (m : ℕ+) :
    bcKMSPhaseState β hβ χ 0 m = 1 := by
  unfold bcKMSPhaseState
  have h_eq :
      (fun n : ℕ => if n = 0 then (0 : ℂ) else Complex.ofReal ((n : ℝ) ^ (-β)) * bcPhaseChar χ 0 m n) =
        fun n : ℕ => Complex.ofReal ((n : ℝ) ^ (-β)) := by
    funext n
    by_cases hn : n = 0
    · subst hn
      have hneg : -β ≠ 0 := by linarith [hβ]
      simp [Real.zero_rpow hneg]
    · simp [hn]
  rw [h_eq]
  have h_tsum :
      (∑' n : ℕ, Complex.ofReal ((n : ℝ) ^ (-β))) = Complex.ofReal (dirichletSeriesBC β hβ) := by
    have hs := (dirichletSeriesBC_hasSum β hβ).map Complex.ofRealCLM Complex.continuous_ofReal
    exact hs.tsum_eq
  rw [h_tsum]
  have hpos : (Complex.ofReal (dirichletSeriesBC β hβ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (dirichletSeriesBC_pos β hβ))
  exact inv_mul_cancel₀ hpos

/-- Boundedness of the extremal KMS phase state: `‖φ_{β, χ}(e(a/m))‖ ≤ 1`. -/
theorem norm_bcKMSPhaseState_le_one {β : ℝ} (hβ : 1 < β) (χ : ProfiniteUnits) (a : ℤ) (m : ℕ+) :
    ‖bcKMSPhaseState β hβ χ a m‖ ≤ 1 := by
  unfold bcKMSPhaseState
  have hsum_c := bcKMSPhaseState_summable hβ χ a m
  have hsum_r : Summable (fun n : ℕ => (n : ℝ) ^ (-β)) :=
    Real.summable_nat_rpow.mpr (by linarith [hβ])
  have hnorm_sum :
      ‖∑' n : ℕ, if n = 0 then (0 : ℂ) else Complex.ofReal ((n : ℝ) ^ (-β)) * bcPhaseChar χ a m n‖ ≤
        dirichletSeriesBC β hβ := by
    calc
      ‖∑' n : ℕ, if n = 0 then (0 : ℂ) else Complex.ofReal ((n : ℝ) ^ (-β)) * bcPhaseChar χ a m n‖
          ≤ ∑' n : ℕ, ‖if n = 0 then (0 : ℂ) else Complex.ofReal ((n : ℝ) ^ (-β)) * bcPhaseChar χ a m n‖ :=
            norm_tsum_le_tsum_norm hsum_c.norm
      _ ≤ ∑' n : ℕ, (n : ℝ) ^ (-β) := by
            refine hsum_c.norm.tsum_le_tsum (fun n => ?_) hsum_r
            by_cases hn : n = 0
            · subst hn
              simp only [↓reduceIte, norm_zero, Nat.cast_zero]
              exact Real.rpow_nonneg (le_refl (0 : ℝ)) (-β)
            · simp only [hn, ↓reduceIte]
              rw [norm_mul, Complex.norm_real, norm_bcPhaseChar, mul_one,
                Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)]
      _ = dirichletSeriesBC β hβ := rfl
  have hpos : 0 < dirichletSeriesBC β hβ := dirichletSeriesBC_pos β hβ
  rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hpos.le]
  calc
    (dirichletSeriesBC β hβ)⁻¹ *
        ‖∑' n : ℕ, if n = 0 then (0 : ℂ) else Complex.ofReal ((n : ℝ) ^ (-β)) * bcPhaseChar χ a m n‖
        ≤ (dirichletSeriesBC β hβ)⁻¹ * dirichletSeriesBC β hβ :=
          mul_le_mul_of_nonneg_left hnorm_sum (inv_nonneg.mpr hpos.le)
    _ = 1 := inv_mul_cancel₀ (ne_of_gt hpos)

/-- Scaling invariance of `bcKMSPhaseState` under `(a, m) ↦ (k * a, k * m)`. -/
theorem bcKMSPhaseState_scale {β : ℝ} (hβ : 1 < β) (χ : ProfiniteUnits) (a : ℤ) (m k : ℕ+) :
    bcKMSPhaseState β hβ χ ((k : ℤ) * a) (k * m) = bcKMSPhaseState β hβ χ a m := by
  unfold bcKMSPhaseState
  congr 1
  refine tsum_congr fun n => ?_
  by_cases hn : n = 0
  · simp [hn]
  · simp only [hn, ↓reduceIte, bcPhaseChar_scale]

/-- Exact Galois equivariance of `bcKMSPhaseState` under right action of `ProfiniteUnits`. -/
theorem bcKMSPhaseState_galois_action {β : ℝ} (hβ : 1 < β) (χ ψ : ProfiniteUnits) (a : ℤ) (m : ℕ+) :
    bcKMSPhaseState β hβ (χ * ψ) a m =
      bcKMSPhaseState β hβ χ (a * ((ψ.component m : ZMod m).val : ℤ)) m := by
  unfold bcKMSPhaseState
  congr 1
  refine tsum_congr fun n => ?_
  by_cases hn : n = 0
  · simp [hn]
  · simp only [hn, ↓reduceIte, bcPhaseChar_mul_profinite]

private lemma dirichletSeriesBC_eq_one_add_tail {β : ℝ} (hβ : 1 < β) :
    dirichletSeriesBC β hβ = 1 + ∑' n : ℕ, ((n + 2 : ℕ) : ℝ) ^ (-β) := by
  have hs0 : Summable (fun n : ℕ => (n : ℝ) ^ (-β)) :=
    Real.summable_nat_rpow.mpr (by linarith [hβ])
  have hs1 : Summable (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ (-β)) := (summable_nat_add_iff 1).mpr hs0
  have hsplit0 := hs0.tsum_eq_zero_add
  have h0 : ((0 : ℕ) : ℝ) ^ (-β) = 0 := by
    simpa using Real.zero_rpow (by linarith [hβ] : -β ≠ 0)
  have hsplit1 := hs1.tsum_eq_zero_add
  have h1 : (((0 + 1 : ℕ) : ℝ) ^ (-β)) = 1 := by simp
  have hstep :
      (∑' n : ℕ, (((n + 1) + 1 : ℕ) : ℝ) ^ (-β)) = ∑' n : ℕ, ((n + 2 : ℕ) : ℝ) ^ (-β) := rfl
  unfold dirichletSeriesBC
  rw [hsplit0, h0, zero_add, hsplit1, h1, hstep]

private lemma tsum_bcKMS_eq_one_add_tail {β : ℝ} (hβ : 1 < β) (χ : ProfiniteUnits) (a : ℤ) (m : ℕ+) :
    (∑' n : ℕ, if n = 0 then (0 : ℂ) else Complex.ofReal ((n : ℝ) ^ (-β)) * bcPhaseChar χ a m n) =
      bcPhaseChar χ a m 1 +
        ∑' n : ℕ, Complex.ofReal (((n + 2 : ℕ) : ℝ) ^ (-β)) * bcPhaseChar χ a m (n + 2) := by
  let f : ℕ → ℂ := fun n => if n = 0 then 0 else Complex.ofReal ((n : ℝ) ^ (-β)) * bcPhaseChar χ a m n
  have hs0 : Summable f := bcKMSPhaseState_summable hβ χ a m
  have hs1 : Summable (fun n : ℕ => f (n + 1)) := (summable_nat_add_iff 1).mpr hs0
  have hsplit0 := hs0.tsum_eq_zero_add
  have hsplit1 := hs1.tsum_eq_zero_add
  have hf0 : f 0 = 0 := rfl
  have hf1 : f (0 + 1) = bcPhaseChar χ a m 1 := by
    simp [f]
  have hstep :
      (∑' n : ℕ, f ((n + 1) + 1)) =
        ∑' n : ℕ, Complex.ofReal (((n + 2 : ℕ) : ℝ) ^ (-β)) * bcPhaseChar χ a m (n + 2) := by
    refine tsum_congr fun n => ?_
    have hidx : n + 1 + 1 = n + 2 := by omega
    simp only [f, hidx, Nat.add_eq_zero_iff, OfNat.ofNat_ne_zero, and_false, ↓reduceIte]
  change ∑' n : ℕ, f n = _
  rw [hsplit0, hf0, zero_add, hsplit1, hf1, hstep]

/-- Explicit zero-temperature deviation bound from the character limit `bcPhaseChar χ a m 1`. -/
theorem bcKMSPhaseState_zeroTemp_bound {β : ℝ} (hβ : 1 < β)
    (χ : ProfiniteUnits) (a : ℤ) (m : ℕ+) :
    ‖bcKMSPhaseState β hβ χ a m - bcPhaseChar χ a m 1‖ ≤
      2 * (∑' n : ℕ, ((n + 2 : ℕ) : ℝ) ^ (-β)) / dirichletSeriesBC β hβ := by
  set T : ℝ := ∑' n : ℕ, ((n + 2 : ℕ) : ℝ) ^ (-β)
  have hZpos : 0 < dirichletSeriesBC β hβ := dirichletSeriesBC_pos β hβ
  have hZne : (dirichletSeriesBC β hβ : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt hZpos)
  have hZeq : dirichletSeriesBC β hβ = 1 + T := dirichletSeriesBC_eq_one_add_tail hβ
  let tailC : ℂ := ∑' n : ℕ, Complex.ofReal (((n + 2 : ℕ) : ℝ) ^ (-β)) * bcPhaseChar χ a m (n + 2)
  have hsum_tailC :
      Summable (fun n : ℕ => Complex.ofReal (((n + 2 : ℕ) : ℝ) ^ (-β)) * bcPhaseChar χ a m (n + 2)) := by
    have hs := (summable_nat_add_iff 2).mpr (bcKMSPhaseState_summable hβ χ a m)
    refine hs.congr fun n => ?_
    simp
  have hsum_tailR : Summable (fun n : ℕ => ((n + 2 : ℕ) : ℝ) ^ (-β)) :=
    (summable_nat_add_iff 2).mpr (Real.summable_nat_rpow.mpr (by linarith [hβ]))
  have hnorm_tailC : ‖tailC‖ ≤ T := by
    calc
      ‖tailC‖ ≤ ∑' n : ℕ, ‖Complex.ofReal (((n + 2 : ℕ) : ℝ) ^ (-β)) * bcPhaseChar χ a m (n + 2)‖ :=
        norm_tsum_le_tsum_norm hsum_tailC.norm
      _ ≤ ∑' n : ℕ, ((n + 2 : ℕ) : ℝ) ^ (-β) := by
        refine hsum_tailC.norm.tsum_le_tsum (fun n => ?_) hsum_tailR
        rw [norm_mul, Complex.norm_real, norm_bcPhaseChar, mul_one,
          Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
  have hdiff :
      bcKMSPhaseState β hβ χ a m - bcPhaseChar χ a m 1 =
        (dirichletSeriesBC β hβ : ℂ)⁻¹ * (tailC - (T : ℂ) * bcPhaseChar χ a m 1) := by
    have hZ_c : (dirichletSeriesBC β hβ : ℂ) = 1 + (T : ℂ) := by
      exact_mod_cast hZeq
    have h1 :
        bcKMSPhaseState β hβ χ a m =
          (dirichletSeriesBC β hβ : ℂ)⁻¹ * (bcPhaseChar χ a m 1 + tailC) := by
      unfold bcKMSPhaseState
      rw [tsum_bcKMS_eq_one_add_tail hβ χ a m]
    have h2 :
        bcPhaseChar χ a m 1 =
          (dirichletSeriesBC β hβ : ℂ)⁻¹ * ((1 + (T : ℂ)) * bcPhaseChar χ a m 1) := by
      rw [← hZ_c, ← mul_assoc, inv_mul_cancel₀ hZne, one_mul]
    calc
      bcKMSPhaseState β hβ χ a m - bcPhaseChar χ a m 1
          = (dirichletSeriesBC β hβ : ℂ)⁻¹ * (bcPhaseChar χ a m 1 + tailC) -
              (dirichletSeriesBC β hβ : ℂ)⁻¹ * ((1 + (T : ℂ)) * bcPhaseChar χ a m 1) := by
            rw [h1]
            conv_lhs => rhs; rw [h2]
      _ = (dirichletSeriesBC β hβ : ℂ)⁻¹ * (tailC - (T : ℂ) * bcPhaseChar χ a m 1) := by ring
  rw [hdiff, norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hZpos.le]
  have hTnonneg : 0 ≤ T := tsum_nonneg fun n => Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hsub_norm : ‖tailC - (T : ℂ) * bcPhaseChar χ a m 1‖ ≤ 2 * T := by
    calc
      ‖tailC - (T : ℂ) * bcPhaseChar χ a m 1‖
          ≤ ‖tailC‖ + ‖(T : ℂ) * bcPhaseChar χ a m 1‖ := norm_sub_le _ _
      _ ≤ T + T := by
        have h2 : ‖(T : ℂ) * bcPhaseChar χ a m 1‖ = T := by
          rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hTnonneg, norm_bcPhaseChar, mul_one]
        linarith [hnorm_tailC, h2]
      _ = 2 * T := by ring
  rw [inv_mul_eq_div]
  exact div_le_div_of_nonneg_right hsub_norm hZpos.le

private lemma tendsto_excited_tail_zero :
    Tendsto (fun β : ℝ => ∑' n : ℕ, ((n + 2 : ℕ) : ℝ) ^ (-β)) atTop (nhds 0) :=
  (d3ZeroTempCantorCrystallizationCandidate.evidence ()).2

/-- Zero-temperature crystallization: as `β → ∞`, `φ_{β, χ}(e(a/m))` converges to the profinite
unit-circle character `bcPhaseChar χ a m 1`. -/
theorem bcKMSPhaseState_tendsto_zeroTemp (χ : ProfiniteUnits) (a : ℤ) (m : ℕ+)
    {βseq : ℕ → ℝ} (hβseq : ∀ k, 1 < βseq k) (hlim : Tendsto βseq atTop atTop) :
    Tendsto (fun k => bcKMSPhaseState (βseq k) (hβseq k) χ a m)
      atTop (nhds (bcPhaseChar χ a m 1)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have h_upper :
      Tendsto (fun k => 2 * (∑' n : ℕ, ((n + 2 : ℕ) : ℝ) ^ (-βseq k))) atTop (nhds 0) := by
    have hc := (tendsto_excited_tail_zero.comp hlim).const_mul 2
    simpa using hc
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h_upper
    (Eventually.of_forall fun k => norm_nonneg _) (Eventually.of_forall fun k => ?_)
  have hb := bcKMSPhaseState_zeroTemp_bound (hβseq k) χ a m
  have hZge1 : 1 ≤ dirichletSeriesBC (βseq k) (hβseq k) := by
    rw [dirichletSeriesBC_eq_one_add_tail (hβseq k)]
    have htn : 0 ≤ ∑' n : ℕ, ((n + 2 : ℕ) : ℝ) ^ (-βseq k) :=
      tsum_nonneg fun n => Real.rpow_nonneg (Nat.cast_nonneg _) _
    linarith
  have hnum_nn : 0 ≤ 2 * (∑' n : ℕ, ((n + 2 : ℕ) : ℝ) ^ (-βseq k)) := by
    have htn : 0 ≤ ∑' n : ℕ, ((n + 2 : ℕ) : ℝ) ^ (-βseq k) :=
      tsum_nonneg fun n => Real.rpow_nonneg (Nat.cast_nonneg _) _
    linarith
  exact hb.trans (div_le_self hnum_nn hZge1)

private lemma bcPhaseChar_eq_iff_component_eq (χ ψ : ProfiniteUnits) (m : ℕ+) :
    bcPhaseChar χ 1 m 1 = bcPhaseChar ψ 1 m 1 ↔ χ.component m = ψ.component m := by
  constructor
  · intro heq
    unfold bcPhaseChar at heq
    rw [Complex.exp_eq_exp_iff_exists_int] at heq
    rcases heq with ⟨k, hk⟩
    have hm_ne : (m : ℝ) ≠ 0 := by exact_mod_cast m.ne_zero
    have hk_im :
        ((k : ℂ) * (2 * ↑Real.pi * Complex.I)).im = (k : ℝ) * (2 * Real.pi) := by
      have hkx : (k : ℂ) * (2 * ↑Real.pi * Complex.I) =
          (((k : ℝ) * (2 * Real.pi) : ℝ) : ℂ) * Complex.I := by
        push_cast; ring
      rw [hkx, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
      ring
    have h_im_raw := congrArg Complex.im hk
    simp only [Complex.add_im, hk_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_mul, add_zero] at h_im_raw
    have h_im_real :
        2 * Real.pi * ((((χ.component m : ZMod m).val : ℤ) : ℝ) / (m : ℝ)) =
          2 * Real.pi * ((((ψ.component m : ZMod m).val : ℤ) : ℝ) / (m : ℝ)) +
            (k : ℝ) * (2 * Real.pi) := by
      simpa [mul_assoc] using h_im_raw
    have h2pi_ne : (2 * Real.pi : ℝ) ≠ 0 := by positivity
    have hdiv :
        ((((χ.component m : ZMod m).val : ℤ) : ℝ) / (m : ℝ)) =
          ((((ψ.component m : ZMod m).val : ℤ) : ℝ) / (m : ℝ)) + (k : ℝ) := by
      apply mul_left_cancel₀ h2pi_ne
      calc
        (2 * Real.pi) * ((((χ.component m : ZMod m).val : ℤ) : ℝ) / (m : ℝ))
            = 2 * Real.pi * ((((ψ.component m : ZMod m).val : ℤ) : ℝ) / (m : ℝ)) +
                (k : ℝ) * (2 * Real.pi) := h_im_real
        _ = (2 * Real.pi) * ((((ψ.component m : ZMod m).val : ℤ) : ℝ) / (m : ℝ) + (k : ℝ)) := by ring
    have hmul :
        (((χ.component m : ZMod m).val : ℤ) : ℝ) =
          (((ψ.component m : ZMod m).val : ℤ) : ℝ) + (k : ℝ) * (m : ℝ) := by
      calc
        (((χ.component m : ZMod m).val : ℤ) : ℝ)
            = ((((χ.component m : ZMod m).val : ℤ) : ℝ) / (m : ℝ)) * (m : ℝ) := by
                field_simp [hm_ne]
        _ = ((((ψ.component m : ZMod m).val : ℤ) : ℝ) / (m : ℝ) + (k : ℝ)) * (m : ℝ) := by
                rw [hdiv]
        _ = (((ψ.component m : ZMod m).val : ℤ) : ℝ) + (k : ℝ) * (m : ℝ) := by
                field_simp [hm_ne]
    have hmul_int :
        ((χ.component m : ZMod m).val : ℤ) =
          ((ψ.component m : ZMod m).val : ℤ) + k * (m : ℤ) := by
      exact_mod_cast hmul
    have hx_lt : (χ.component m : ZMod m).val < (m : ℕ) :=
      ZMod.val_lt (χ.component m : ZMod m)
    have hy_lt : (ψ.component m : ZMod m).val < (m : ℕ) :=
      ZMod.val_lt (ψ.component m : ZMod m)
    have hx_nn : (0 : ℤ) ≤ ((χ.component m : ZMod m).val : ℤ) := Int.natCast_nonneg _
    have hy_nn : (0 : ℤ) ≤ ((ψ.component m : ZMod m).val : ℤ) := Int.natCast_nonneg _
    have hx_lt_int : ((χ.component m : ZMod m).val : ℤ) < (m : ℤ) := by exact_mod_cast hx_lt
    have hy_lt_int : ((ψ.component m : ZMod m).val : ℤ) < (m : ℤ) := by exact_mod_cast hy_lt
    have hval : (χ.component m : ZMod m).val = (ψ.component m : ZMod m).val := by
      have hm_pos : (0 : ℤ) < (m : ℤ) := by exact_mod_cast m.pos
      have hk0 : k = 0 := by
        by_contra hk_ne
        rcases lt_or_gt_of_ne hk_ne with hk_neg | hk_pos
        · have hle : k ≤ -1 := by omega
          have h1 : k * (m : ℤ) ≤ -(m : ℤ) := by nlinarith
          linarith [hmul_int, hx_nn, hy_lt_int, h1]
        · have hge : (1 : ℤ) ≤ k := by omega
          have h1 : (m : ℤ) ≤ k * (m : ℤ) := by nlinarith
          linarith [hmul_int, hy_nn, hx_lt_int, h1]
      subst hk0
      omega
    ext1
    exact ZMod.val_injective m hval
  · intro h
    simp [bcPhaseChar, h]

/-- Distinct elements of `ProfiniteUnits` are separated by their character limits and by their
extremal `\mathrm{KMS}_β` states at sufficiently large `β`. -/
theorem bcKMSPhaseState_separates_profiniteUnits {χ ψ : ProfiniteUnits} (hneq : χ ≠ ψ) :
    ∃ m : ℕ+, bcPhaseChar χ 1 m 1 ≠ bcPhaseChar ψ 1 m 1 ∧
      ∀ᶠ β : ℝ in atTop, ∀ (hβ : 1 < β), bcKMSPhaseState β hβ χ 1 m ≠ bcKMSPhaseState β hβ ψ 1 m := by
  have hm_ex : ∃ m : ℕ+, χ.component m ≠ ψ.component m := by
    by_contra hall
    push Not at hall
    exact hneq (ProfiniteUnits.ext (funext hall))
  rcases hm_ex with ⟨m, hm⟩
  have hchar : bcPhaseChar χ 1 m 1 ≠ bcPhaseChar ψ 1 m 1 := by
    rwa [Ne, bcPhaseChar_eq_iff_component_eq]
  refine ⟨m, hchar, ?_⟩
  set δ : ℝ := ‖bcPhaseChar χ 1 m 1 - bcPhaseChar ψ 1 m 1‖
  have hδ : 0 < δ := norm_pos_iff.mpr (sub_ne_zero.mpr hchar)
  have h_tend :
      Tendsto (fun β : ℝ => 2 * (∑' n : ℕ, ((n + 2 : ℕ) : ℝ) ^ (-β))) atTop (nhds 0) := by
    simpa using tendsto_excited_tail_zero.const_mul 2
  have hev : ∀ᶠ β : ℝ in atTop, 2 * (∑' n : ℕ, ((n + 2 : ℕ) : ℝ) ^ (-β)) < δ / 2 :=
    h_tend.eventually (Iio_mem_nhds (by linarith))
  filter_upwards [hev, eventually_gt_atTop (1 : ℝ)] with β htail _ hβ heq
  have hb1 := bcKMSPhaseState_zeroTemp_bound hβ χ 1 m
  have hb2 := bcKMSPhaseState_zeroTemp_bound hβ ψ 1 m
  have htn_nn : 0 ≤ ∑' n : ℕ, ((n + 2 : ℕ) : ℝ) ^ (-β) :=
    tsum_nonneg fun n => Real.rpow_nonneg (Nat.cast_nonneg (n + 2)) (-β)
  have hZge1 : 1 ≤ dirichletSeriesBC β hβ := by
    rw [dirichletSeriesBC_eq_one_add_tail hβ]
    linarith [htn_nn]
  have h2tn_nn : 0 ≤ 2 * (∑' n : ℕ, ((n + 2 : ℕ) : ℝ) ^ (-β)) := by
    linarith [htn_nn]
  have hb1' : ‖bcKMSPhaseState β hβ χ 1 m - bcPhaseChar χ 1 m 1‖ < δ / 2 :=
    lt_of_le_of_lt (hb1.trans (div_le_self h2tn_nn hZge1)) htail
  have hb2' : ‖bcKMSPhaseState β hβ ψ 1 m - bcPhaseChar ψ 1 m 1‖ < δ / 2 :=
    lt_of_le_of_lt (hb2.trans (div_le_self h2tn_nn hZge1)) htail
  have htri : δ ≤ ‖bcKMSPhaseState β hβ χ 1 m - bcPhaseChar χ 1 m 1‖ +
      ‖bcKMSPhaseState β hβ ψ 1 m - bcPhaseChar ψ 1 m 1‖ := by
    have hsub : bcPhaseChar χ 1 m 1 - bcPhaseChar ψ 1 m 1 =
        (bcPhaseChar χ 1 m 1 - bcKMSPhaseState β hβ χ 1 m) +
          (bcKMSPhaseState β hβ ψ 1 m - bcPhaseChar ψ 1 m 1) := by
      rw [heq]
      ring
    calc
      δ = ‖bcPhaseChar χ 1 m 1 - bcPhaseChar ψ 1 m 1‖ := rfl
      _ ≤ ‖bcPhaseChar χ 1 m 1 - bcKMSPhaseState β hβ χ 1 m‖ +
            ‖bcKMSPhaseState β hβ ψ 1 m - bcPhaseChar ψ 1 m 1‖ := by rw [hsub]; exact norm_add_le _ _
      _ = ‖bcKMSPhaseState β hβ χ 1 m - bcPhaseChar χ 1 m 1‖ +
            ‖bcKMSPhaseState β hβ ψ 1 m - bcPhaseChar ψ 1 m 1‖ := by rw [norm_sub_rev]
  linarith

/-- Concrete low-temperature symmetry-breaking witness: for large `β > 1`, `φ_{β, 1}` and `φ_{β, -1}`
take distinct values on `e(1/3)`. -/
theorem bcKMSPhaseState_ssb_witness :
    ∃ m : ℕ+, ∀ᶠ β : ℝ in atTop, ∀ (hβ : 1 < β),
      bcKMSPhaseState β hβ ProfiniteUnits.negOne 1 m ≠ bcKMSPhaseState β hβ 1 1 m := by
  rcases bcKMSPhaseState_separates_profiniteUnits ProfiniteUnits.negOne_ne_one with ⟨m, _, h⟩
  exact ⟨m, h⟩

/-- Finite convex combination of extremal `\mathrm{KMS}_β` states remains normalized (`= 1` at `a = 0`). -/
theorem bcKMSPhaseState_convex_zero {ι : Type*} (s : Finset ι) (w : ι → ℝ)
    (hw : ∑ i ∈ s, w i = 1) (χ : ι → ProfiniteUnits) {β : ℝ} (hβ : 1 < β) (m : ℕ+) :
    (∑ i ∈ s, (w i : ℂ) * bcKMSPhaseState β hβ (χ i) 0 m) = 1 := by
  simp only [bcKMSPhaseState_zero, mul_one, ← Complex.ofReal_sum, hw, Complex.ofReal_one]

/-- High-temperature divergence (`β ≤ 1`): the harmonic/Dirichlet weight sum `∑ n^{-β}` diverges. -/
theorem not_summable_rpow_neg_of_le_one {β : ℝ} (hβ : β ≤ 1) :
    ¬ Summable (fun n : ℕ => (n : ℝ) ^ (-β)) := by
  rw [Real.summable_nat_rpow]
  linarith [hβ]

/-- The symmetric high-temperature rational state (`1` at `0`, `0` on `a/m ∉ ℤ`) is automatically
`\widehat{\mathbb{Z}}^\times`-invariant, contrasting with low-temperature SSB. -/
def bcHighTempSymmetricState (a : ℤ) (m : ℕ+) : ℂ :=
  if (m : ℤ) ∣ a then 1 else 0

theorem bcHighTempSymmetricState_scale (a : ℤ) (m k : ℕ+) :
    bcHighTempSymmetricState ((k : ℤ) * a) (k * m) = bcHighTempSymmetricState a m := by
  unfold bcHighTempSymmetricState
  have hk_ne : (k : ℤ) ≠ 0 := by exact_mod_cast k.ne_zero
  simp only [PNat.mul_coe, Nat.cast_mul, mul_dvd_mul_iff_left hk_ne]

/-! ## 3. Sewn Operator Subalgebra & Anti-Sewn Chiral Trace Ideal on `H_lp ℝ` -/

/-- Noncommutative subalgebra of `J_lp_clm`-invariant bounded operators on `H_lp ℝ`. -/
def SewnOperatorSubalgebra : Subalgebra ℝ (H_lp ℝ →L[ℝ] H_lp ℝ) where
  carrier := {B | (J_lp_clm (E := ℝ)).comp (B.comp (J_lp_clm (E := ℝ))) = B}
  mul_mem' {A B} hA hB := by
    change (J_lp_clm (E := ℝ)).comp ((A.comp B).comp (J_lp_clm (E := ℝ))) = A.comp B
    have hA' : (J_lp_clm (E := ℝ)).comp (A.comp (J_lp_clm (E := ℝ))) = A := hA
    have hB' : (J_lp_clm (E := ℝ)).comp (B.comp (J_lp_clm (E := ℝ))) = B := hB
    have hJ : (J_lp_clm (E := ℝ)).comp (J_lp_clm (E := ℝ)) = ContinuousLinearMap.id ℝ (H_lp ℝ) :=
      J_lp_clm_comp_self
    calc
      (J_lp_clm (E := ℝ)).comp ((A.comp B).comp (J_lp_clm (E := ℝ)))
          = ((J_lp_clm (E := ℝ)).comp A).comp (B.comp (J_lp_clm (E := ℝ))) := by
              simp only [ContinuousLinearMap.comp_assoc]
      _ = ((J_lp_clm (E := ℝ)).comp A).comp
            (((J_lp_clm (E := ℝ)).comp (J_lp_clm (E := ℝ))).comp (B.comp (J_lp_clm (E := ℝ)))) := by
              rw [hJ, ContinuousLinearMap.id_comp]
      _ = ((J_lp_clm (E := ℝ)).comp (A.comp (J_lp_clm (E := ℝ)))).comp
            ((J_lp_clm (E := ℝ)).comp (B.comp (J_lp_clm (E := ℝ)))) := by
              simp only [ContinuousLinearMap.comp_assoc]
      _ = A.comp B := by rw [hA', hB']
  one_mem' := by
    change (J_lp_clm (E := ℝ)).comp
      ((ContinuousLinearMap.id ℝ (H_lp ℝ)).comp (J_lp_clm (E := ℝ))) =
        ContinuousLinearMap.id ℝ (H_lp ℝ)
    rw [ContinuousLinearMap.id_comp]
    exact J_lp_clm_comp_self
  add_mem' {A B} hA hB := by
    change (J_lp_clm (E := ℝ)).comp ((A + B).comp (J_lp_clm (E := ℝ))) = A + B
    simp only [ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_add]
    rw [hA, hB]
  zero_mem' := by
    change (J_lp_clm (E := ℝ)).comp ((0 : H_lp ℝ →L[ℝ] H_lp ℝ).comp (J_lp_clm (E := ℝ))) = 0
    simp
  algebraMap_mem' r := by
    change (J_lp_clm (E := ℝ)).comp
      ((r • ContinuousLinearMap.id ℝ (H_lp ℝ)).comp (J_lp_clm (E := ℝ))) =
        r • ContinuousLinearMap.id ℝ (H_lp ℝ)
    rw [ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul, ContinuousLinearMap.id_comp,
      J_lp_clm_comp_self]

theorem S_left_mem_sewn : S_left_lp_clm (E := ℝ) ∈ SewnOperatorSubalgebra :=
  S_left_lp_clm_sewn_invariant

theorem S_right_mem_sewn : S_right_lp_clm (E := ℝ) ∈ SewnOperatorSubalgebra :=
  S_right_lp_clm_sewn_invariant

/-- `SewnOperatorSubalgebra` is genuinely noncommutative (witnessed by Cuntz `O₂` shifts). -/
theorem sewnOperatorSubalgebra_noncomm :
    ∃ A B : SewnOperatorSubalgebra, A * B ≠ B * A := by
  refine ⟨⟨S_left_lp_clm (E := ℝ), S_left_mem_sewn⟩, ⟨S_right_lp_clm (E := ℝ), S_right_mem_sewn⟩, ?_⟩
  intro h
  have hval := congrArg Subtype.val h
  exact S_left_right_lp_clm_noncomm hval

/-- Predicate for `J_lp_clm`-anti-sewn bounded operators `J_lp ∘ A ∘ J_lp = -A` on `H_lp E`. -/
def IsAntiSewn {E : Type 0} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (A : H_lp E →L[ℝ] H_lp E) : Prop :=
  (J_lp_clm (E := E)).comp (A.comp (J_lp_clm (E := E))) = -A

theorem epsilon_lp_clm_isAntiSewn
    {E : Type 0} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] :
    IsAntiSewn (epsilon_lp_clm (E := E)) := by
  unfold IsAntiSewn
  calc
    (J_lp_clm (E := E)).comp ((epsilon_lp_clm (E := E)).comp (J_lp_clm (E := E)))
        = ((J_lp_clm (E := E)).comp (epsilon_lp_clm (E := E))).comp (J_lp_clm (E := E)) := by
            rw [ContinuousLinearMap.comp_assoc]
    _ = (-((epsilon_lp_clm (E := E)).comp (J_lp_clm (E := E)))).comp (J_lp_clm (E := E)) := by
            rw [J_lp_clm_anticomm_epsilon_lp_clm]
    _ = -((epsilon_lp_clm (E := E)).comp ((J_lp_clm (E := E)).comp (J_lp_clm (E := E)))) := by
            rw [ContinuousLinearMap.neg_comp, ContinuousLinearMap.comp_assoc]
    _ = -epsilon_lp_clm (E := E) := by
            rw [J_lp_clm_comp_self, ContinuousLinearMap.comp_id]

/-- Right action of `SewnOperatorSubalgebra` preserves `IsAntiSewn` (right ideal property). -/
theorem isAntiSewn_comp_sewn {A : H_lp ℝ →L[ℝ] H_lp ℝ} {B : H_lp ℝ →L[ℝ] H_lp ℝ}
    (hA : IsAntiSewn A) (hB : B ∈ SewnOperatorSubalgebra) :
    IsAntiSewn (A.comp B) := by
  unfold IsAntiSewn at hA ⊢
  have hB' : (J_lp_clm (E := ℝ)).comp (B.comp (J_lp_clm (E := ℝ))) = B := hB
  calc
    (J_lp_clm (E := ℝ)).comp ((A.comp B).comp (J_lp_clm (E := ℝ)))
        = ((J_lp_clm (E := ℝ)).comp A).comp
            (((J_lp_clm (E := ℝ)).comp (J_lp_clm (E := ℝ))).comp (B.comp (J_lp_clm (E := ℝ)))) := by
            rw [J_lp_clm_comp_self, ContinuousLinearMap.id_comp, ContinuousLinearMap.comp_assoc,
              ContinuousLinearMap.comp_assoc]
    _ = ((J_lp_clm (E := ℝ)).comp (A.comp (J_lp_clm (E := ℝ)))).comp
          ((J_lp_clm (E := ℝ)).comp (B.comp (J_lp_clm (E := ℝ)))) := by
            simp only [ContinuousLinearMap.comp_assoc]
    _ = (-A).comp B := by rw [hA, hB']
    _ = -(A.comp B) := ContinuousLinearMap.neg_comp _ _

/-- Left action of `SewnOperatorSubalgebra` preserves `IsAntiSewn` (left ideal property). -/
theorem sewn_comp_isAntiSewn {A : H_lp ℝ →L[ℝ] H_lp ℝ} {B : H_lp ℝ →L[ℝ] H_lp ℝ}
    (hB : B ∈ SewnOperatorSubalgebra) (hA : IsAntiSewn A) :
    IsAntiSewn (B.comp A) := by
  unfold IsAntiSewn at hA ⊢
  have hB' : (J_lp_clm (E := ℝ)).comp (B.comp (J_lp_clm (E := ℝ))) = B := hB
  have hJ : (J_lp_clm (E := ℝ)).comp (J_lp_clm (E := ℝ)) = ContinuousLinearMap.id ℝ (H_lp ℝ) :=
    J_lp_clm_comp_self
  calc
    (J_lp_clm (E := ℝ)).comp ((B.comp A).comp (J_lp_clm (E := ℝ)))
        = ((J_lp_clm (E := ℝ)).comp B).comp
            (((J_lp_clm (E := ℝ)).comp (J_lp_clm (E := ℝ))).comp (A.comp (J_lp_clm (E := ℝ)))) := by
            rw [hJ, ContinuousLinearMap.id_comp]
            simp only [ContinuousLinearMap.comp_assoc]
    _ = ((J_lp_clm (E := ℝ)).comp (B.comp (J_lp_clm (E := ℝ)))).comp
          ((J_lp_clm (E := ℝ)).comp (A.comp (J_lp_clm (E := ℝ)))) := by
            simp only [ContinuousLinearMap.comp_assoc]
    _ = B.comp (-A) := by rw [hB', hA]
    _ = -(B.comp A) := ContinuousLinearMap.comp_neg _ _

/-- `IsAntiSewn` is closed under addition, negation, and real scalar multiplication. -/
theorem isAntiSewn_add {E : Type 0} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {A B : H_lp E →L[ℝ] H_lp E} (hA : IsAntiSewn A) (hB : IsAntiSewn B) :
    IsAntiSewn (A + B) := by
  unfold IsAntiSewn at hA hB ⊢
  simp only [ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_add]
  rw [hA, hB, neg_add]

theorem isAntiSewn_smul {E : Type 0} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (c : ℝ) {A : H_lp E →L[ℝ] H_lp E} (hA : IsAntiSewn A) :
    IsAntiSewn (c • A) := by
  unfold IsAntiSewn at hA ⊢
  rw [ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul, hA, smul_neg]

/-- Product of two `IsAntiSewn` operators becomes `J_lp_clm`-sewn (even grading parity). -/
theorem isAntiSewn_comp_isAntiSewn_mem_sewn {A B : H_lp ℝ →L[ℝ] H_lp ℝ}
    (hA : IsAntiSewn A) (hB : IsAntiSewn B) :
    A.comp B ∈ SewnOperatorSubalgebra := by
  change (J_lp_clm (E := ℝ)).comp ((A.comp B).comp (J_lp_clm (E := ℝ))) = A.comp B
  have hJ : (J_lp_clm (E := ℝ)).comp (J_lp_clm (E := ℝ)) = ContinuousLinearMap.id ℝ (H_lp ℝ) :=
    J_lp_clm_comp_self
  calc
    (J_lp_clm (E := ℝ)).comp ((A.comp B).comp (J_lp_clm (E := ℝ)))
        = ((J_lp_clm (E := ℝ)).comp A).comp
            (((J_lp_clm (E := ℝ)).comp (J_lp_clm (E := ℝ))).comp (B.comp (J_lp_clm (E := ℝ)))) := by
            rw [hJ, ContinuousLinearMap.id_comp]
            simp only [ContinuousLinearMap.comp_assoc]
    _ = ((J_lp_clm (E := ℝ)).comp (A.comp (J_lp_clm (E := ℝ)))).comp
          ((J_lp_clm (E := ℝ)).comp (B.comp (J_lp_clm (E := ℝ)))) := by
            simp only [ContinuousLinearMap.comp_assoc]
    _ = (-A).comp (-B) := by rw [hA, hB]
    _ = A.comp B := by simp

/-- Every `J_lp_clm`-anti-sewn bounded operator has zero paired chiral expectation on `H_lp E`. -/
theorem infinite_hilbert_antiSewn_paired_zero
    {E : Type 0} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (A : H_lp E →L[ℝ] H_lp E) (hA : IsAntiSewn A) (v : H_lp E) :
    inner ℝ v (A v) + inner ℝ (J_lp_clm (E := E) v) (A (J_lp_clm (E := E) v)) = 0 := by
  have h2 : inner ℝ (J_lp_clm (E := E) v) (A (J_lp_clm (E := E) v)) = -inner ℝ v (A v) := by
    calc
      inner ℝ (J_lp_clm (E := E) v) (A (J_lp_clm (E := E) v))
          = inner ℝ v ((J_lp_clm (E := E)) (A (J_lp_clm (E := E) v))) :=
              inner_J_lp_clm_selfAdjoint v _
      _ = inner ℝ v (((J_lp_clm (E := E)).comp (A.comp (J_lp_clm (E := E)))) v) := rfl
      _ = inner ℝ v ((-A) v) := by rw [hA]
      _ = -inner ℝ v (A v) := by simp [inner_neg_right]
  linarith

/-- General vanishing of expectation value `⟪ψ, A ψ⟫ = 0` for any `J_lp_clm`-fixed state `ψ`
and any `J_lp_clm`-anti-sewn bounded operator `A`. -/
theorem infinite_hilbert_antiSewn_expectation_zero
    {E : Type 0} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (A : H_lp E →L[ℝ] H_lp E) (hA : IsAntiSewn A)
    (ψ : H_lp E) (hψ : J_lp_clm (E := E) ψ = ψ) :
    inner ℝ ψ (A ψ) = 0 := by
  have hp := infinite_hilbert_antiSewn_paired_zero A hA ψ
  rw [hψ] at hp
  linarith

/-- General infinite-series chiral trace vanishing `∑' i, ⟪e i, A (e i)⟫ = 0` for every
`J_lp_clm`-paired family `(e i)` and every `J_lp_clm`-anti-sewn bounded operator `A`. -/
theorem infinite_hilbert_antiSewn_tsum_trace_zero
    {E : Type 0} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {ι : Type*} (σ : ι ≃ ι) (e : ι → H_lp E)
    (he : ∀ i, e (σ i) = J_lp_clm (E := E) (e i))
    (A : H_lp E →L[ℝ] H_lp E) (hA : IsAntiSewn A)
    (hsum : Summable (fun i : ι => inner ℝ (e i) (A (e i)))) :
    (∑' i : ι, inner ℝ (e i) (A (e i))) = 0 := by
  let f : ι → ℝ := fun i => inner ℝ (e i) (A (e i))
  have hf_pair : ∀ i : ι, f i + f (σ i) = 0 := by
    intro i
    dsimp [f]
    rw [he i]
    exact infinite_hilbert_antiSewn_paired_zero A hA (e i)
  have hsum_σ : Summable (fun i : ι => f (σ i)) := (σ.summable_iff).mpr hsum
  have htsum_σ : (∑' i : ι, f (σ i)) = ∑' i : ι, f i := σ.tsum_eq f
  have hdouble : (∑' i : ι, f i) + (∑' i : ι, f i) = 0 := by
    calc
      (∑' i : ι, f i) + (∑' i : ι, f i)
          = (∑' i : ι, f i) + (∑' i : ι, f (σ i)) := by rw [htsum_σ]
      _ = ∑' i : ι, (f i + f (σ i)) := (hsum.tsum_add hsum_σ).symm
      _ = ∑' _ : ι, (0 : ℝ) := tsum_congr hf_pair
      _ = 0 := tsum_zero
  change (∑' i : ι, f i) = 0
  linarith

/-- Orthogonal invariance of trace cancellation: if `U` preserves inner products and commutes
with `J_lp_clm`, then `⟪U ψ, A (U ψ)⟫ = 0` for any `J_lp_clm`-fixed `ψ` and anti-sewn `A`. -/
theorem infinite_hilbert_antiSewn_orthogonal_conj_zero
    {E : Type 0} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (U : H_lp E →L[ℝ] H_lp E)
    (hUJ : U.comp (J_lp_clm (E := E)) = (J_lp_clm (E := E)).comp U)
    (A : H_lp E →L[ℝ] H_lp E) (hA : IsAntiSewn A)
    (ψ : H_lp E) (hψ : J_lp_clm (E := E) ψ = ψ) :
    inner ℝ (U ψ) (A (U ψ)) = 0 := by
  apply infinite_hilbert_antiSewn_expectation_zero A hA (U ψ)
  have h1 := congrArg (fun T : H_lp E →L[ℝ] H_lp E => T ψ) hUJ
  calc
    J_lp_clm (E := E) (U ψ) = U (J_lp_clm (E := E) ψ) := by
      simpa [ContinuousLinearMap.comp_apply] using h1.symm
    _ = U ψ := by rw [hψ]

/-! ## 4. Exact Finite Primon Souriau–Fisher Log-Partition Hessian -/

/-- Log-partition potential `ψ_P(β) = log Z_P(β)` of the finite primon gas cutoff `L`. -/
def primonLogPartition (L : FormalPrimeRootLattice) (β : ℝ) : ℝ :=
  Real.log (finitePrimonPartition L β)

/-- Primon Bose–Einstein mean energy `E_P(β) = ∑_{p ∈ L} log(p) * p^{-β} / (1 - p^{-β})`. -/
def primonMeanEnergy (L : FormalPrimeRootLattice) (β : ℝ) : ℝ :=
  ∑ p ∈ L.primes, Real.log (p : ℝ) * boltzmannRootVariable β p / (1 - boltzmannRootVariable β p)

/-- Souriau–Fisher metric `g_P^{SF}(β) = ∑_{p ∈ L} (log p)^2 * p^{-β} / (1 - p^{-β})^2` on `L`. -/
def primonSouriauFisherMetric (L : FormalPrimeRootLattice) (β : ℝ) : ℝ :=
  ∑ p ∈ L.primes, (Real.log (p : ℝ)) ^ 2 * boltzmannRootVariable β p / (1 - boltzmannRootVariable β p) ^ 2

private lemma boltzmannRootVariable_pos (β : ℝ) (p : ℕ) : 0 < boltzmannRootVariable β p :=
  Real.exp_pos _

private lemma boltzmannRootVariable_lt_one_of_prime {p : ℕ} (hp : Nat.Prime p) {β : ℝ} (hβ : 0 < β) :
    boltzmannRootVariable β p < 1 := by
  unfold boltzmannRootVariable
  have h1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.one_lt
  have hlog : 0 < Real.log (p : ℝ) := Real.log_pos h1
  have hneg : -β * Real.log (p : ℝ) < 0 := by nlinarith [hβ, hlog]
  rw [← Real.exp_zero]
  exact Real.exp_lt_exp.mpr hneg

private lemma hasDerivAt_boltzmannRootVariable (p : ℕ) (β : ℝ) :
    HasDerivAt (fun x => boltzmannRootVariable x p)
      (-Real.log (p : ℝ) * boltzmannRootVariable β p) β := by
  unfold boltzmannRootVariable
  have h_lin : HasDerivAt (fun x : ℝ => -x * Real.log (p : ℝ)) (-Real.log (p : ℝ)) β := by
    have h0 := (hasDerivAt_id β).neg.mul_const (Real.log (p : ℝ))
    simpa using h0
  simpa [mul_comm] using h_lin.exp

private lemma hasDerivAt_neg_log_one_sub_boltzmann
    {p : ℕ} (hp : Nat.Prime p) {β : ℝ} (hβ : 0 < β) :
    HasDerivAt (fun x => -Real.log (1 - boltzmannRootVariable x p))
      (-(Real.log (p : ℝ) * boltzmannRootVariable β p / (1 - boltzmannRootVariable β p))) β := by
  have hsub : HasDerivAt (fun x => 1 - boltzmannRootVariable x p)
      (-(-Real.log (p : ℝ) * boltzmannRootVariable β p)) β :=
    (hasDerivAt_boltzmannRootVariable p β).const_sub 1
  have hpos : 1 - boltzmannRootVariable β p ≠ 0 :=
    ne_of_gt (sub_pos.mpr (boltzmannRootVariable_lt_one_of_prime hp hβ))
  have hlog : HasDerivAt (fun x => Real.log (1 - boltzmannRootVariable x p))
      ((-(-Real.log (p : ℝ) * boltzmannRootVariable β p)) / (1 - boltzmannRootVariable β p)) β :=
    hsub.log hpos
  convert hlog.neg using 1
  ring

/-- Local additive expansion `primonLogPartition L x = ∑ p ∈ L.primes, -log (1 - exp(-x log p))`
holding for all `x > 0`. -/
theorem primonLogPartition_eq_sum_of_pos (L : FormalPrimeRootLattice) {x : ℝ} (hx : 0 < x) :
    primonLogPartition L x =
      ∑ p ∈ L.primes, -Real.log (1 - boltzmannRootVariable x p) := by
  unfold primonLogPartition finitePrimonPartition
  have hpos : ∀ p ∈ L.primes, 0 < (1 - boltzmannRootVariable x p)⁻¹ := fun p hp =>
    inv_pos.mpr (sub_pos.mpr (boltzmannRootVariable_lt_one_of_prime (L.prime_mem p hp) hx))
  rw [Real.log_prod (fun p hp => ne_of_gt (hpos p hp))]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Real.log_inv]

/-- Exact first derivative of the finite primon log-partition function: `ψ_P'(β) = -E_P(β)`. -/
theorem hasDerivAt_primonLogPartition (L : FormalPrimeRootLattice) {β : ℝ} (hβ : 0 < β) :
    HasDerivAt (primonLogPartition L) (-primonMeanEnergy L β) β := by
  have hsum :
      HasDerivAt (fun x => ∑ p ∈ L.primes, -Real.log (1 - boltzmannRootVariable x p))
        (∑ p ∈ L.primes, -(Real.log (p : ℝ) * boltzmannRootVariable β p / (1 - boltzmannRootVariable β p))) β := by
    convert HasDerivAt.fun_sum fun p hp =>
      hasDerivAt_neg_log_one_sub_boltzmann (L.prime_mem p hp) hβ
  have heq : (primonLogPartition L) =ᶠ[nhds β]
      (fun x => ∑ p ∈ L.primes, -Real.log (1 - boltzmannRootVariable x p)) := by
    filter_upwards [eventually_gt_nhds hβ] with x hx
    exact primonLogPartition_eq_sum_of_pos L hx
  refine (hsum.congr_of_eventuallyEq heq).congr_deriv ?_
  simp [primonMeanEnergy, Finset.sum_neg_distrib]

/-- Exact second derivative of `ψ_P(β)`: `(-E_P)'(β) = g_P^{SF}(β)` (the Souriau–Fisher metric). -/
theorem hasDerivAt_neg_primonMeanEnergy (L : FormalPrimeRootLattice) {β : ℝ} (hβ : 0 < β) :
    HasDerivAt (fun x => -primonMeanEnergy L x) (primonSouriauFisherMetric L β) β := by
  have h_term : ∀ p ∈ L.primes,
      HasDerivAt (fun x => -(Real.log (p : ℝ) * boltzmannRootVariable x p / (1 - boltzmannRootVariable x p)))
        ((Real.log (p : ℝ)) ^ 2 * boltzmannRootVariable β p / (1 - boltzmannRootVariable β p) ^ 2) β := by
    intro p hp
    have hnum : HasDerivAt (fun x => Real.log (p : ℝ) * boltzmannRootVariable x p)
        (Real.log (p : ℝ) * (-Real.log (p : ℝ) * boltzmannRootVariable β p)) β :=
      (hasDerivAt_boltzmannRootVariable p β).const_mul (Real.log (p : ℝ))
    have hden : HasDerivAt (fun x => 1 - boltzmannRootVariable x p)
        (-(-Real.log (p : ℝ) * boltzmannRootVariable β p)) β :=
      (hasDerivAt_boltzmannRootVariable p β).const_sub 1
    have hne : 1 - boltzmannRootVariable β p ≠ 0 :=
      ne_of_gt (sub_pos.mpr (boltzmannRootVariable_lt_one_of_prime (L.prime_mem p hp) hβ))
    have hdiv := hnum.div hden hne
    convert hdiv.neg using 1
    field_simp [hne]
    ring
  have hsum := HasDerivAt.fun_sum h_term
  simpa [primonMeanEnergy, primonSouriauFisherMetric, Finset.sum_neg_distrib] using hsum

/-- Nonnegativity of the primon Souriau–Fisher metric `g_P^{SF}(β) ≥ 0`. -/
theorem primonSouriauFisherMetric_nonneg (L : FormalPrimeRootLattice) (β : ℝ) :
    0 ≤ primonSouriauFisherMetric L β := by
  unfold primonSouriauFisherMetric
  refine Finset.sum_nonneg fun p _ => ?_
  exact div_nonneg (mul_nonneg (sq_nonneg _) (boltzmannRootVariable_pos β p).le) (sq_nonneg _)

/-- Strict positivity of the primon Souriau–Fisher metric `g_P^{SF}(β) > 0` for nonempty prime
cutoffs at `β > 0`. -/
theorem primonSouriauFisherMetric_pos (L : FormalPrimeRootLattice) (hne : L.primes.Nonempty)
    {β : ℝ} (hβ : 0 < β) :
    0 < primonSouriauFisherMetric L β := by
  unfold primonSouriauFisherMetric
  refine Finset.sum_pos ?_ hne
  intro p hp
  have hprime := L.prime_mem p hp
  have h1p : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hprime.one_lt
  have hlog : 0 < Real.log (p : ℝ) := Real.log_pos h1p
  have hden : 0 < 1 - boltzmannRootVariable β p :=
    sub_pos.mpr (boltzmannRootVariable_lt_one_of_prime hprime hβ)
  exact div_pos (mul_pos (sq_pos_of_pos hlog) (boltzmannRootVariable_pos β p)) (sq_pos_of_pos hden)

end InfoGeometry.Canonical.SouriauBostConnesKMSAndTraceIdeal
