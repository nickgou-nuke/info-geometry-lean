/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Tactic

/-!
# Classification of Coadjoint Orbits Carrying Gibbs Ensembles (Neeb `arXiv:2601.04934v1`)

Formalizes the core theorems of Karl-Hermann Neeb's *A classification of coadjoint orbits carrying
Gibbs ensembles* (Source 5, `arXiv:2601.04934v1`, §§2 & 6):

1. **Abstract Symplectic Gibbs Laplace Transform (§2, Remark 6.15)**:
   - Shift equivariance `L(μ_{λ + λ₀})(x) = e^{-λ₀(x)} L(μ_λ)(x)`.
   - Convexity of the admissible cone `Ω_μ` and log-partition / Laplace transform `L(μ)`.
2. **Oscillator Algebra `heis(ℝ², Ω) ⋊ ℝ z₀` & Positive Complex Structure (Lemmas 6.6–6.7, Ex. 6.9)**:
   - Explicit skew/Jacobi Lie bracket on `ℝ × ℝ² × ℝ`, compatible positive complex structure
     `I_pos (p, q) = (q, -p)` (`I_pos² = -id`, `Ω(I_pos v, I_pos w) = Ω(v, w)`), positive
     Gaussian quadratic form `Ω(I_pos v, v) = p² + q² > 0`, and orbit lower bound `λ(Ad♯ v) ≥ c s`.
3. **Exact 2D Coadjoint Orbit Gibbs Classification (Example 6.14)**:
   - **Elliptic `sl₂(ℝ)` / Hyperbolic Disc (`t > 0`)**:
     `∫_{r>0} e^{-t (lam0 + r)} dr = e^{-t lam0} / t`, nilpotent limit `1 / t`, Souriau geometric heat
     `Q(t) = lam0 + 1 / t`, and strictly positive Fisher–Souriau calorific capacity `1 / t² > 0`.
   - **Hyperbolic `sl₂(ℝ)` Obstruction (`Ω_λ = ∅`)**: `r ↦ e^{-t r}` is NOT integrable on `ℝ`
     for ANY `t ∈ ℝ`.
   - **Compact `su₂(ℂ)` / Sphere `S²` (`t ≠ 0`)**:
     `∫_{-lam0}^{lam0} e^{-t r} dr = 2 sinh(t lam0) / t`.
   - **Flat Kähler Oscillator Orbit (`t > 0`)**:
     `∫_{r>0} e^{-(s lamC + t (lamZ + r / 2))} dr = 2 e^{-(s lamC + t lamZ)} / t`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Real
open scoped ENNReal

namespace InfoGeometry.Canonical.NeebCoadjointOrbitGibbsClassification

/-! ### Part 1: Abstract Symplectic Gibbs Laplace Transform & Cone Convexity (Neeb §2, Rem. 6.15) -/

/-- Gibbs Laplace kernel `x ↦ e^{-⟨a, x⟩}` on an orbit sample `a`. -/
def laplaceKernel {α E : Type*} [AddCommMonoid E] [Module ℝ E]
    (pair : α → E →ₗ[ℝ] ℝ) (x : E) (a : α) : ℝ :=
  Real.exp (-(pair a x))

/-- Symplectic Gibbs Laplace transform `L(μ)(x) = ∫ a, e^{-⟨a, x⟩} ∂μ(a)`. -/
def gibbsLaplace {α E : Type*} [MeasurableSpace α] [AddCommMonoid E] [Module ℝ E]
    (μ : Measure α) (pair : α → E →ₗ[ℝ] ℝ) (x : E) : ℝ :=
  ∫ a, laplaceKernel pair x a ∂μ

/-- **Neeb Remark 6.15 (Orbit Shift Equivariance)**:
Shifting an orbit by a central/fixed functional `a₀` factors out `e^{-⟨a₀, x⟩}` from `L(μ)`. -/
theorem gibbsLaplace_shift_equivariance {α E : Type*} [MeasurableSpace α]
    [AddCommMonoid E] [Module ℝ E] (μ : Measure α)
    (pair : α → E →ₗ[ℝ] ℝ) (a₀ : α) (shift : α → α)
    (hShift : ∀ a : α, ∀ x : E, pair (shift a) x = pair a x + pair a₀ x) (x : E) :
    (∫ a, laplaceKernel pair x (shift a) ∂μ) =
      Real.exp (-(pair a₀ x)) * gibbsLaplace μ pair x := by
  unfold gibbsLaplace laplaceKernel
  have hfun : (fun a : α => Real.exp (-(pair (shift a) x))) =
      fun a : α => Real.exp (-(pair a₀ x)) * Real.exp (-(pair a x)) := by
    ext a
    rw [hShift a x, ← Real.exp_add]
    congr 1
    ring
  rw [hfun, MeasureTheory.integral_const_mul]

/-- Pointwise convexity of the exponential Laplace kernel along segments in `E`. -/
theorem laplaceKernel_convex_bound {α E : Type*} [AddCommGroup E] [Module ℝ E]
    (pair : α → E →ₗ[ℝ] ℝ) (x y : E) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (a : α) :
    laplaceKernel pair ((1 - t) • x + t • y) a ≤
      (1 - t) * laplaceKernel pair x a + t * laplaceKernel pair y a := by
  unfold laplaceKernel
  have hLin : -(pair a ((1 - t) • x + t • y)) =
      (1 - t) • (-(pair a x)) + t • (-(pair a y)) := by
    simp only [map_add, map_smul, smul_eq_mul]
    ring
  rw [hLin]
  exact convexOn_exp.2 (Set.mem_univ _) (Set.mem_univ _) (sub_nonneg.mpr ht1) ht0
    (by ring : (1 - t) + t = 1)

/-- **Neeb §2 (Convexity of Admissible Cone `Ω_μ` & Laplace Functional)**:
If `x, y ∈ Ω_μ` (both Laplace kernels integrable), then every convex combination
`(1 - t) • x + t • y` also belongs to `Ω_μ` and `L(μ)` is convex on `Ω_μ`. -/
theorem gibbsLaplace_convex_on_domain {α E : Type*} [MeasurableSpace α] (μ : Measure α)
    [AddCommGroup E] [Module ℝ E]
    (pair : α → E →ₗ[ℝ] ℝ) (hMeas : ∀ z : E, Measurable (fun a => pair a z))
    (x y : E) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hx : Integrable (laplaceKernel pair x) μ)
    (hy : Integrable (laplaceKernel pair y) μ) :
    Integrable (laplaceKernel pair ((1 - t) • x + t • y)) μ ∧
      gibbsLaplace μ pair ((1 - t) • x + t • y) ≤
        (1 - t) * gibbsLaplace μ pair x + t * gibbsLaplace μ pair y := by
  have hBoundIntegrable :
      Integrable (fun a => (1 - t) * laplaceKernel pair x a + t * laplaceKernel pair y a) μ :=
    (hx.const_mul (1 - t)).add (hy.const_mul t)
  have hAESM : AEStronglyMeasurable (laplaceKernel pair ((1 - t) • x + t • y)) μ :=
    (Real.continuous_exp.measurable.comp (hMeas _).neg).aestronglyMeasurable
  have hInt : Integrable (laplaceKernel pair ((1 - t) • x + t • y)) μ := by
    refine hBoundIntegrable.mono' hAESM (Eventually.of_forall fun a => ?_)
    have hpos : 0 ≤ laplaceKernel pair ((1 - t) • x + t • y) a := (Real.exp_pos _).le
    rw [Real.norm_of_nonneg hpos]
    exact laplaceKernel_convex_bound pair x y ht0 ht1 a
  refine ⟨hInt, ?_⟩
  unfold gibbsLaplace
  have hMono := MeasureTheory.integral_mono hInt hBoundIntegrable
    (fun a => laplaceKernel_convex_bound pair x y ht0 ht1 a)
  rw [MeasureTheory.integral_add (hx.const_mul (1 - t)) (hy.const_mul t),
    MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul] at hMono
  exact hMono

/-! ### Part 2: Oscillator Algebra `heis(ℝ², Ω) ⋊ ℝ z₀` & Positive Complex Structure (Neeb §6) -/

/-- Canonical symplectic form on `ℝ²`: `Ω((p₁, q₁), (p₂, q₂)) = p₁ q₂ - q₁ p₂`. -/
def symp2 (v w : ℝ × ℝ) : ℝ :=
  v.1 * w.2 - v.2 * w.1

/-- Positive compatible complex structure `I_pos(p, q) = (q, -p)` (`Neeb Lemmas 6.6–6.7`). -/
def posComplexStr (v : ℝ × ℝ) : ℝ × ℝ :=
  (v.2, -v.1)

/-- `I_pos` satisfies `I_pos² = -id`, preserves `Ω`, and induces positive quadratic form
`Ω(I_pos v, v) = p² + q²` (strictly positive for `v ≠ 0`). -/
theorem posComplexStr_symplectic_positive (v w : ℝ × ℝ) :
    posComplexStr (posComplexStr v) = (-v.1, -v.2) ∧
    symp2 (posComplexStr v) (posComplexStr w) = symp2 v w ∧
    symp2 (posComplexStr v) v = v.1 ^ 2 + v.2 ^ 2 ∧
    (v ≠ (0, 0) → 0 < symp2 (posComplexStr v) v) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [posComplexStr]
  · unfold posComplexStr symp2
    ring
  · unfold posComplexStr symp2
    ring
  · intro hv
    have hq : symp2 (posComplexStr v) v = v.1 ^ 2 + v.2 ^ 2 := by
      unfold posComplexStr symp2
      ring
    rw [hq]
    by_contra hle
    push Not at hle
    have hv1 : v.1 = 0 := by nlinarith [sq_nonneg v.1, sq_nonneg v.2, hle]
    have hv2 : v.2 = 0 := by nlinarith [sq_nonneg v.1, sq_nonneg v.2, hle]
    exact hv (Prod.ext hv1 hv2)

/-- Carrier for the 4D oscillator Lie algebra `heis(ℝ², Ω) ⋊ ℝ z₀` parameterized by `(z, p, q, t)`. -/
abbrev OscAlg := ℝ × ℝ × ℝ × ℝ

/-- Oscillator Lie bracket combining `[(0,v,0), (0,w,0)] = Ω(v,w) c` and `[z₀, v] = I_pos v`. -/
def oscBracket (x y : OscAlg) : OscAlg :=
  (x.2.1 * y.2.2.1 - x.2.2.1 * y.2.1,
   x.2.2.2 * y.2.2.1 - y.2.2.2 * x.2.2.1,
   -(x.2.2.2 * y.2.1 - y.2.2.2 * x.2.1),
   0)

/-- Antisymmetry and Jacobi identity verifying `oscBracket` is a genuine 4D Lie algebra. -/
theorem oscBracket_antisymm_and_jacobi (x y z : OscAlg) :
    oscBracket x y = (-((oscBracket y x).1), -((oscBracket y x).2.1),
      -((oscBracket y x).2.2.1), -((oscBracket y x).2.2.2)) ∧
    oscBracket x (oscBracket y z) + oscBracket y (oscBracket z x) + oscBracket z (oscBracket x y) =
      (0, 0, 0, 0) := by
  constructor
  · ext <;> (simp [oscBracket]; try ring)
  · ext <;> (simp [oscBracket]; try ring)

/-- **Neeb Example 6.9 (Gaussian Positivity on Oscillator Coadjoint Orbit)**:
The coadjoint orbit coordinate `c * s + (c * t / 2) * (p² + q²)` satisfies a uniform lower bound
`c * s ≤ c * s + (c * t / 2) * (p² + q²)` whenever `c > 0` and `t > 0`. -/
theorem osc_coadjoint_gaussian_lower_bound {c s t p q : ℝ} (hc : 0 < c) (ht : 0 < t) :
    c * s ≤ c * s + (c * t / 2) * (p ^ 2 + q ^ 2) := by
  have h1 : 0 ≤ c * t / 2 := by nlinarith [hc, ht]
  have h2 : 0 ≤ p ^ 2 + q ^ 2 := add_nonneg (sq_nonneg p) (sq_nonneg q)
  nlinarith [mul_nonneg h1 h2]

/-! ### Part 3: Neeb Example 6.14 Exact 2D Coadjoint Orbit Gibbs Classification -/

/-- **Neeb Ex. 6.14(1) — Elliptic `sl₂(ℝ)` / Hyperbolic Disc Laplace Transform**:
`∫ r in Ioi 0, exp (-t * (lam0 + r)) = exp (-t * lam0) / t` for every `t > 0`. -/
theorem neeb_ex614_sl2_elliptic_laplace {lam0 t : ℝ} (ht : 0 < t) :
    (∫ r in Ioi (0 : ℝ), Real.exp (-t * (lam0 + r))) = Real.exp (-t * lam0) / t := by
  let F : ℝ → ℝ := fun r => -Real.exp (-t * (lam0 + r)) / t
  have hderiv : ∀ r ∈ Ici (0 : ℝ), HasDerivAt F (Real.exp (-t * (lam0 + r))) r := by
    intro r _hr
    have harg : HasDerivAt (fun u : ℝ => -t * (lam0 + u)) (-t * 1) r :=
      ((hasDerivAt_id r).const_add lam0).const_mul (-t)
    have hexp : HasDerivAt (fun u : ℝ => Real.exp (-t * (lam0 + u)))
        (Real.exp (-t * (lam0 + r)) * (-t * 1)) r := harg.exp
    exact ((hexp.neg).div_const t).congr_deriv (by field_simp [ht.ne'])
  have hlim : Tendsto F atTop (𝓝 0) := by
    have hlin : Tendsto (fun r : ℝ => t * (lam0 + r)) atTop atTop :=
      Filter.tendsto_atTop.mpr fun B =>
        Filter.eventually_atTop.mpr ⟨B / t - lam0, fun r hr => by
          have h1 : B / t ≤ lam0 + r := by linarith [hr]
          have h2 := mul_le_mul_of_nonneg_left h1 ht.le
          have hbt : t * (B / t) = B := mul_div_cancel₀ B ht.ne'
          linarith [h2, hbt]⟩
    have hexp : Tendsto (fun r : ℝ => Real.exp (-t * (lam0 + r))) atTop (𝓝 0) := by
      simpa [Function.comp_def, neg_mul] using Real.tendsto_exp_neg_atTop_nhds_zero.comp hlin
    simpa [F] using (hexp.neg).div_const t
  have hint : IntegrableOn (fun r : ℝ => Real.exp (-t * (lam0 + r))) (Ioi 0) :=
    integrableOn_Ioi_deriv_of_nonneg' hderiv (fun r _ => (Real.exp_pos _).le) hlim
  rw [integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hint hlim]
  simp [F, neg_div]

/-- **Neeb Ex. 6.14 Nilpotent Orbit Limit (`lam0 = 0`)**:
`∫ r in Ioi 0, exp (-t * r) = 1 / t` for `t > 0`. -/
theorem neeb_ex614_sl2_nilpotent_limit {t : ℝ} (ht : 0 < t) :
    (∫ r in Ioi (0 : ℝ), Real.exp (-t * r)) = 1 / t := by
  have h := neeb_ex614_sl2_elliptic_laplace (lam0 := 0) ht
  simpa using h

/-- Souriau Massieu potential for the elliptic `sl₂(ℝ)` orbit: `ψ(t) = -t lam0 - log t`. -/
def sl2EllipticMassieu (lam0 t : ℝ) : ℝ :=
  -t * lam0 - Real.log t

/-- Consistency with `log L(μ)`: `log (exp (-t lam0) / t) = sl2EllipticMassieu lam0 t` for `t > 0`. -/
theorem sl2EllipticMassieu_eq_log_laplace (lam0 : ℝ) {t : ℝ} (ht : 0 < t) :
    Real.log (Real.exp (-t * lam0) / t) = sl2EllipticMassieu lam0 t := by
  rw [Real.log_div (Real.exp_pos _).ne' ht.ne', Real.log_exp]
  rfl

/-- **Souriau Geometric Heat Diffeomorphism & Fisher Calorific Capacity (`sl₂(ℝ)` elliptic)**:
1. `d/dt (-ψ(t)) = lam0 + 1 / t`, bijectively mapping `(0, ∞)` onto `(lam0, ∞)`.
2. `d/dt (-(lam0 + 1 / t)) = 1 / t² > 0`, giving strictly positive Fisher–Souriau calorific capacity. -/
theorem sl2_elliptic_heat_and_fisher_capacity (lam0 : ℝ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun u => -sl2EllipticMassieu lam0 u) (lam0 + 1 / t) t ∧
    HasDerivAt (fun u => -(lam0 + 1 / u)) (1 / t ^ 2) t ∧
    0 < (1 / t ^ 2) := by
  refine ⟨?_, ?_, one_div_pos.mpr (sq_pos_of_pos ht)⟩
  · have h1 : HasDerivAt (fun u : ℝ => u * lam0) lam0 t := by
      simpa using (hasDerivAt_id t).mul_const lam0
    have h2 : HasDerivAt Real.log (1 / t) t := by
      simpa [one_div] using Real.hasDerivAt_log ht.ne'
    have hfun : (fun u : ℝ => -sl2EllipticMassieu lam0 u) = fun u => u * lam0 + Real.log u := by
      ext u
      unfold sl2EllipticMassieu
      ring
    rw [hfun]
    exact h1.add h2
  · have hInv : HasDerivAt (fun u : ℝ => u⁻¹) (-(t ^ 2)⁻¹) t :=
      hasDerivAt_inv ht.ne'
    have hfun : (fun u : ℝ => -(lam0 + 1 / u)) = fun u => -(lam0 + u⁻¹) := by
      ext u
      simp [one_div]
    rw [hfun]
    have h := (hInv.const_add lam0).neg
    convert h using 1
    simp [one_div]

/-- **Neeb Ex. 6.14(1) Hyperbolic `sl₂(ℝ)` Obstruction (`Ω_λ = ∅`)**:
No inverse temperature `t : ℝ` makes `r ↦ exp (-t * r)` Lebesgue integrable over `ℝ`. -/
theorem neeb_ex614_sl2_hyperbolic_not_integrable (t : ℝ) :
    ¬ Integrable (fun r : ℝ => Real.exp (-t * r)) (volume : Measure ℝ) := by
  intro hint
  have checkSet : ∀ (s : Set ℝ), MeasurableSet s → volume s = ⊤ →
      (∀ r ∈ s, (1 : ℝ) ≤ Real.exp (-t * r)) → False := by
    intro s hsMeas hsTop hge
    have hLFin : (∫⁻ r in s, ‖Real.exp (-t * r)‖ₑ ∂volume) < ⊤ :=
      lt_of_le_of_lt (setLIntegral_le_lintegral s (fun r => ‖Real.exp (-t * r)‖ₑ)) hint.2
    have h1le : ∀ r ∈ s, (1 : ℝ≥0∞) ≤ ‖Real.exp (-t * r)‖ₑ := fun r hr => by
      have hexp1 : (1 : ℝ) ≤ Real.exp (-t * r) := hge r hr
      rw [Real.enorm_of_nonneg (Real.exp_pos _).le, ← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal hexp1
    have hvol : volume s ≤ ∫⁻ r in s, ‖Real.exp (-t * r)‖ₑ ∂volume := by
      calc
        volume s = ∫⁻ _r in s, (1 : ℝ≥0∞) ∂volume := by simp
        _ ≤ ∫⁻ r in s, ‖Real.exp (-t * r)‖ₑ ∂volume :=
            setLIntegral_mono' hsMeas h1le
    have hlt : volume s < ⊤ := lt_of_le_of_lt hvol hLFin
    rw [hsTop] at hlt
    exact (lt_self_iff_false ⊤).mp hlt
  by_cases ht : t ≤ 0
  · exact checkSet (Ici 0) measurableSet_Ici Real.volume_Ici fun r hr => by
      rw [Real.one_le_exp_iff]
      nlinarith [ht, show (0 : ℝ) ≤ r from hr]
  · push Not at ht
    exact checkSet (Iic 0) measurableSet_Iic Real.volume_Iic fun r hr => by
      rw [Real.one_le_exp_iff]
      nlinarith [ht, show r ≤ 0 from hr]

/-- **Neeb Ex. 6.14(2) — Compact `su₂(ℂ)` / Sphere `S²` Gibbs Laplace Transform**:
`∫ r in (-lam0)..lam0, exp (-t * r) = 2 * sinh (t * lam0) / t` for every `t ≠ 0`. -/
theorem neeb_ex614_su2_sphere_laplace (lam0 : ℝ) {t : ℝ} (ht : t ≠ 0) :
    (∫ r in (-lam0)..lam0, Real.exp (-t * r)) = 2 * Real.sinh (t * lam0) / t := by
  let F : ℝ → ℝ := fun r => -Real.exp (-t * r) / t
  have hderiv : ∀ r ∈ Set.uIcc (-lam0) lam0, HasDerivAt F (Real.exp (-t * r)) r := by
    intro r _hr
    have harg : HasDerivAt (fun u : ℝ => -t * u) (-t * 1) r :=
      (hasDerivAt_id r).const_mul (-t)
    exact (((harg.exp).neg).div_const t).congr_deriv (by field_simp [ht])
  have hint : IntervalIntegrable (fun r : ℝ => Real.exp (-t * r)) volume (-lam0) lam0 :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).intervalIntegrable _ _
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  dsimp [F]
  rw [Real.sinh_eq]
  have h1 : -t * (-lam0) = t * lam0 := by ring
  have h2 : -t * lam0 = -(t * lam0) := by ring
  rw [h1, h2]
  field_simp [ht]
  ring

/-- **Neeb Ex. 6.14(3) — Flat Kähler Oscillator Orbit `heis(ℝ², Ω) ⋊ ℝ z₀` Laplace Transform**:
`∫ r in Ioi 0, exp (-(s * lamC + t * (lamZ + r / 2))) = 2 * exp (-(s * lamC + t * lamZ)) / t`
for every `t > 0`. -/
theorem neeb_ex614_oscillator_laplace (s lamC lamZ : ℝ) {t : ℝ} (ht : 0 < t) :
    (∫ r in Ioi (0 : ℝ), Real.exp (-(s * lamC + t * (lamZ + r / 2)))) =
      2 * Real.exp (-(s * lamC + t * lamZ)) / t := by
  have hFactor : (fun r : ℝ => Real.exp (-(s * lamC + t * (lamZ + r / 2)))) =
      fun r : ℝ => Real.exp (-(s * lamC + t * lamZ)) * Real.exp (-(t / 2) * r) := by
    ext r
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hFactor, MeasureTheory.integral_const_mul]
  have hhalf : 0 < t / 2 := half_pos ht
  rw [neeb_ex614_sl2_nilpotent_limit hhalf]
  field_simp [ht.ne']

end InfoGeometry.Canonical.NeebCoadjointOrbitGibbsClassification
