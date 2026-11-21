/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.NumberTheory.NumberField.AdeleRing
import Mathlib.NumberTheory.ArithmeticFunction.LFunction
import Mathlib.NumberTheory.MulChar.Basic
import Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients.Norm
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.WellKnown
import InfoGeometry.Arithmetic.ArithmeticFunctionLSeriesEulerProduct
import InfoGeometry.Arithmetic.NumberFieldCompletionFinitePlace
import InfoGeometry.Arithmetic.NumberFieldDedekindZetaEulerProduct

/-!
# Hecke characters and their local Euler factors

The local-character and Euler-factor definitions follow Thomas Browning's
RiemannMasullo project (Apache-2.0, revision
`be5d4cb0356d48406eae83233d73c99085b9a038`); their proofs are checked against
this repository's pinned Mathlib revision.

This file supplies the Hecke-character/L-function layer missing from the pinned
Mathlib revision. Its carrier is Mathlib's actual idele class group; local
restrictions, unramifiedness, local factors, and the global Dirichlet series
are defined from that carrier.
-/

public section

open Filter Function ArithmeticFunction NumberField IsDedekindDomain
open InfoGeometry.Arithmetic.ArithmeticFunctionLSeriesEulerProduct
open scoped Topology

noncomputable section

namespace NumberField

variable (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]

/-- A Hecke character on the idele class group of a fraction field. This has the
usual number-field interpretation under `[IsIntegralClosure ℤ R K]` and
`[NumberField K]`; the general carrier is retained so local restriction remains
available over any Dedekind fraction field. -/
abbrev HeckeCharacter := (IdeleClassGroup R K) →ₜ* ℂ

variable {R K} (χ : HeckeCharacter R K)

namespace HeckeCharacter

/-- Restriction of a Hecke character to the multiplicative group of a finite completion. -/
@[simps!]
def restrict (v : HeightOneSpectrum R) : MulChar (v.adicCompletion K) ℂ :=
  .ofUnitHom <| χ.toMonoidHom.toHomUnits.comp <| IdeleClassGroup.ofAdicCompletion R K v

/-- Unramifiedness means triviality on the local unit group. -/
def IsUnramifiedAt (v : HeightOneSpectrum R) : Prop :=
  (χ.restrict v).toUnitHom.comp
    (Units.map (v.adicCompletionIntegers K).subtype.toMonoidHom) = 1

variable {χ}

theorem isUnramifiedAt_iff {v : HeightOneSpectrum R} :
    χ.IsUnramifiedAt v ↔ ∀ x : (v.adicCompletionIntegers K)ˣ, χ.restrict v x = 1 := by
  simp [IsUnramifiedAt, MonoidHom.ext_iff, Units.ext_iff]

namespace IsUnramifiedAt

variable {v : HeightOneSpectrum R}

theorem restrict_apply_unit_eq_one (h : χ.IsUnramifiedAt v)
    (x : (v.adicCompletionIntegers K)ˣ) : χ.restrict v x = 1 :=
  isUnramifiedAt_iff.mp h x

theorem restrict_apply_eq_one (h : χ.IsUnramifiedAt v) (x : v.adicCompletion K)
    (hx : Valued.v x = 1) : χ.restrict v x = 1 := by
  have hx : x ∈ v.adicCompletionIntegers K := (v.mem_adicCompletionIntegers R K).mp hx.le
  replace hx : IsUnit (⟨x, hx⟩ : v.adicCompletionIntegers K) := by
    rwa [HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one, Subtype.coe_mk]
  exact h.restrict_apply_unit_eq_one hx.unit

theorem restrict_apply_eq (h : χ.IsUnramifiedAt v) {x y : v.adicCompletion K}
    (hxy : Valued.v x = Valued.v y) : χ.restrict v x = χ.restrict v y := by
  rcases eq_or_ne x 0 with rfl | hx
  · rw [eq_comm, Valued.v.map_zero, map_eq_zero] at hxy
    rw [hxy]
  rcases eq_or_ne y 0 with rfl | hy
  · rw [Valued.v.map_zero, map_eq_zero] at hxy
    rw [hxy]
  apply eq_of_div_eq_one
  simpa [hx, hy, IsUnit.unit_div] using h.restrict_apply_eq_one (x / y) (by simpa [hxy])

theorem restrict_apply_eq_of_isUniformizer (h : χ.IsUnramifiedAt v) {x y : v.adicCompletion K}
    (hx : Valued.v.IsUniformizer x) (hy : Valued.v.IsUniformizer y) :
    χ.restrict v x = χ.restrict v y :=
  h.restrict_apply_eq (hx.trans hy.symm)

end IsUnramifiedAt

variable (χ)

/-- The value of the local character on a chosen uniformizer. -/
def localValue (v : HeightOneSpectrum R) : ℂ :=
  letI val : Valuation (v.adicCompletion K) (WithZero (Multiplicative ℤ)) := Valued.v
  χ.restrict v val.exists_isUniformizer_of_isCyclic_of_nontrivial.choose

theorem IsUnramifiedAt.localValue_eq {v : HeightOneSpectrum R}
    (h : χ.IsUnramifiedAt v) (π : v.adicCompletion K) (hπ : Valued.v.IsUniformizer π) :
    χ.localValue v = χ.restrict v π :=
  h.restrict_apply_eq_of_isUniformizer
    Valued.v.exists_isUniformizer_of_isCyclic_of_nontrivial.choose_spec hπ

open Classical Polynomial in
/-- The local polynomial is `1 - χᵥ(πᵥ) X` when unramified, and `1` otherwise. -/
def localPolynomial (v : HeightOneSpectrum R) : ℂ[X] :=
  if χ.IsUnramifiedAt v then 1 - C (χ.localValue v) * X else 1

/-- The inverse local polynomial as a formal power series. -/
def localPowerSeries (v : HeightOneSpectrum R) : PowerSeries ℂ :=
  .invOfUnit (χ.localPolynomial v) 1

/-- The local Euler factor viewed as an arithmetic function. -/
def localEulerFactor (v : HeightOneSpectrum R) : ArithmeticFunction ℂ :=
  .ofPowerSeries (Nat.card (IsLocalRing.ResidueField (v.adicCompletionIntegers K)))
    (χ.localPowerSeries v)

/-- The arithmetic-function Euler product of the finite local Hecke factors. -/
def LFunction : ArithmeticFunction ℂ :=
  .eulerProduct fun v : HeightOneSpectrum R ↦ χ.localEulerFactor v

/-- The Dirichlet series attached to the Hecke arithmetic function. -/
protected def LSeries (s : ℂ) := LSeries χ.LFunction s

end HeckeCharacter
end NumberField

open Classical Polynomial in
/-- The local inverse Euler polynomial has geometric coefficients, with ratio zero
at ramified places. -/
theorem hecke_localPowerSeries_eq_mk {R F : Type*} [CommRing R] [IsDedekindDomain R]
    [Field F] [Algebra R F] [IsFractionRing R F] (χ : HeckeCharacter R F)
    (v : HeightOneSpectrum R) :
    let a := if χ.IsUnramifiedAt v then χ.localValue v else 0
    χ.localPowerSeries v = PowerSeries.mk (fun k ↦ a ^ k) := by
  classical
  let a := if χ.IsUnramifiedAt v then χ.localValue v else 0
  let P : PowerSeries ℂ := 1 - PowerSeries.C a * PowerSeries.X
  have hP : (χ.localPolynomial v : PowerSeries ℂ) = P := by
    by_cases h : χ.IsUnramifiedAt v <;> simp [HeckeCharacter.localPolynomial, a, P, h]
  have hinv : P * χ.localPowerSeries v = 1 := by
    rw [HeckeCharacter.localPowerSeries, hP]
    apply PowerSeries.mul_invOfUnit
    simp [P]
  have hgeom : PowerSeries.mk (fun k ↦ a ^ k) * P = 1 := by
    simpa [P, PowerSeries.rescale_mk, PowerSeries.rescale_X] using
      congrArg (PowerSeries.rescale a) (PowerSeries.mk_one_mul_one_sub_eq_one ℂ)
  exact (left_inv_eq_right_inv hgeom hinv).symm

/-- Finite Hecke Euler factors stabilize coefficientwise at the global arithmetic-function
Euler product; residue-field cardinalities equal the corresponding absolute ideal norms. -/
theorem heckeLocalEulerFactor_eventually_prod_eq {F : Type*} [Field F] [NumberField F]
    (χ : HeckeCharacter (𝓞 F) F) (n : ℕ) :
    ∀ᶠ S : Finset (HeightOneSpectrum (𝓞 F)) in atTop,
      (∏ v ∈ S, χ.localEulerFactor v) n = χ.LFunction n := by
  simpa only [HeckeCharacter.LFunction, HeckeCharacter.localEulerFactor,
    InfoGeometry.Arithmetic.NumberFieldCompletionFinitePlace.card_residueField_adicCompletion] using
    tendsTo_eulerProduct_ofPowerSeries
      (fun v : HeightOneSpectrum (𝓞 F) ↦ v.asIdeal.absNorm) χ.localPowerSeries
      (fun v ↦ by simp [HeckeCharacter.localPowerSeries, PowerSeries.constantCoeff_invOfUnit]) n

/-- A local character value of norm at most one gives an absolutely convergent geometric
Dirichlet series with a uniform exponential bound. -/
theorem LSeries_heckeLocalEulerFactor_bound {F : Type*} [Field F] [NumberField F]
    (χ : HeckeCharacter (𝓞 F) F) (v : HeightOneSpectrum (𝓞 F)) {s : ℂ}
    (hs : 1 < s.re) (hχ : χ.IsUnramifiedAt v → ‖χ.localValue v‖ ≤ 1) :
    LSeriesSummable (χ.localEulerFactor v) s ∧
      (∑' n, ‖LSeries.term (χ.localEulerFactor v) s n‖) ≤
        Real.exp (2 * (v.asIdeal.absNorm : ℝ) ^ (-s.re)) := by
  classical
  let q := v.asIdeal.absNorm
  let a := if χ.IsUnramifiedAt v then χ.localValue v else 0
  have hq : 1 < q := NumberField.HeightOneSpectrum.one_lt_absNorm v
  have hq₂ : (2 : ℝ) ≤ q := by exact_mod_cast (show 2 ≤ q by omega)
  have hq' : 0 < (q : ℝ) := by linarith
  let r := (q : ℝ) ^ (-s.re)
  have hr : 0 ≤ r := Real.rpow_nonneg hq'.le _
  have hrhalf : r ≤ 1 / 2 := calc
    r ≤ (q : ℝ) ^ (-1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ (q : ℝ)) (by linarith)
    _ = 1 / q := by rw [Real.rpow_neg hq'.le, Real.rpow_one, one_div]
    _ ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hq₂
  have ha : ‖a‖ ≤ 1 := by
    dsimp [a]
    split_ifs with h
    · exact hχ h
    · simp
  let z := a * (q : ℂ) ^ (-s)
  have hz : ‖z‖ ≤ r := by
    change ‖a * ((q : ℝ) : ℂ) ^ (-s)‖ ≤ r
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hq' _, Complex.neg_re]
    exact mul_le_of_le_one_left hr ha
  have hz' : ‖z‖ < 1 := by linarith
  have hsum : HasSum (fun n ↦ ‖LSeries.term (χ.localEulerFactor v) s n‖)
      (1 - ‖z‖)⁻¹ := by
    rw [HeckeCharacter.localEulerFactor,
      InfoGeometry.Arithmetic.NumberFieldCompletionFinitePlace.card_residueField_adicCompletion,
      hecke_localPowerSeries_eq_mk]
    exact hasSum_norm_LSeries_term_ofPowerSeries hq hz'
  refine ⟨hsum.summable.of_norm, hsum.tsum_eq.le.trans ?_⟩
  apply le_trans (b := 2 * r + 1) _ (Real.add_one_le_exp _)
  rw [inv_eq_one_div, div_le_iff₀ (sub_pos.mpr hz')]
  nlinarith [mul_nonneg (by linarith : 0 ≤ 1 - 2 * r) hr,
    mul_le_mul_of_nonneg_left hz (by linarith : 0 ≤ 2 * r + 1)]

/-- If all unramified local values have norm at most one, the Hecke Euler-product
Dirichlet series is absolutely summable in `re(s) > 1`. -/
theorem LSeriesSummable_heckeLFunction {F : Type*} [Field F] [NumberField F]
    (χ : HeckeCharacter (𝓞 F) F) {s : ℂ} (hs : 1 < s.re)
    (hχ : ∀ v, χ.IsUnramifiedAt v → ‖χ.localValue v‖ ≤ 1) :
    LSeriesSummable χ.LFunction s := by
  have hq : Summable fun v : HeightOneSpectrum (𝓞 F) ↦
      (v.asIdeal.absNorm : ℝ) ^ (-s.re) :=
    (InfoGeometry.Arithmetic.NumberFieldDedekindZetaEulerProduct.summable_absNorm_rpow
      F hs).comp_injective (fun _ _ he ↦ HeightOneSpectrum.ext he)
  have hlocal (v) := LSeries_heckeLocalEulerFactor_bound χ v hs (hχ v)
  exact LSeriesSummable_of_eventuallyEq_finset_prod
    (fun v ↦ χ.localEulerFactor v) χ.LFunction s
    (hq.mul_left 2)
    (fun v ↦ mul_nonneg (by norm_num) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
    (fun v ↦ (hlocal v).1) (fun v ↦ (hlocal v).2)
    (heckeLocalEulerFactor_eventually_prod_eq χ)

end noncomputable section
