/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Conformal.MaxwellStressTensor
import InfoGeometry.Conformal.BesselHagenCurrent

/-!
# Maxwell and Bianchi equations imply stress conservation

All coefficients belong to a commutative real algebra. The real derivations,
constant involutive diagonal metric, antisymmetry, Bianchi identity, and vacuum
Maxwell equations are explicit hypotheses. The conclusion is derived stress
conservation, rather than a structure field assuming that conclusion.

The theorem does not require dimension four. Four dimensions are required by
the separate metric-trace-zero theorem used for conformal currents.
-/

noncomputable section

namespace InfoGeometry.Conformal.MaxwellStressTensor

open scoped BigOperators
open InfoGeometry.Conformal.BesselHagenCurrent

variable {A ι : Type*} [CommRing A] [Algebra ℝ A]
variable [Fintype ι] [DecidableEq ι]

/-- The field-gradient contraction appearing in the stress divergence. -/
def transportContraction (D : ι → Derivation ℝ A A) (ε : ι → A)
    (F : Matrix ι ι A) (ν : ι) : A :=
  ∑ μ, ∑ ρ, ε μ * ε ρ * F μ ρ * D μ (F ν ρ)

/-- Half of the derivative of the metric field square. -/
def squareGradientContraction (D : ι → Derivation ℝ A A) (ε : ι → A)
    (F : Matrix ι ι A) (ν : ι) : A :=
  ∑ μ, ∑ ρ, ε μ * ε ρ * F μ ρ * D ν (F μ ρ)

omit [DecidableEq ι] in
/-- Differentiating the field square uses the constancy of the metric coefficients. -/
theorem deriv_fieldSquare (D : ι → Derivation ℝ A A) (ε : ι → A)
    (F : Matrix ι ι A) (hεconst : ∀ μ ν, D μ (ε ν) = 0) (ν : ι) :
    D ν (fieldSquare ε F) =
      squareGradientContraction D ε F ν + squareGradientContraction D ε F ν := by
  have hterm (μ ρ : ι) :
      D ν (ε μ * ε ρ * (F μ ρ) ^ 2) =
        ε μ * ε ρ * F μ ρ * D ν (F μ ρ) +
          ε μ * ε ρ * F μ ρ * D ν (F μ ρ) := by
    simp only [pow_two, Derivation.leibniz, smul_eq_mul, hεconst,
      mul_zero, add_zero]
    simp only [mul_add]
    ac_rfl
  simp only [fieldSquare, map_sum, hterm, Finset.sum_add_distrib,
    squareGradientContraction]

omit [DecidableEq ι] in
/-- Contracting Bianchi with the antisymmetric field produces the factor of two. -/
theorem bianchi_contraction (D : ι → Derivation ℝ A A) (ε : ι → A)
    (F : Matrix ι ι A) (hskew : ∀ μ ν, F μ ν = -F ν μ)
    (hBianchi : ∀ μ ν ρ, D μ (F ν ρ) + D ν (F ρ μ) + D ρ (F μ ν) = 0)
    (ν : ι) :
    squareGradientContraction D ε F ν =
      transportContraction D ε F ν + transportContraction D ε F ν := by
  have hpoint (μ ρ : ι) :
      ε μ * ε ρ * F μ ρ * D ν (F μ ρ) =
        ε μ * ε ρ * F μ ρ * D μ (F ν ρ) -
          ε μ * ε ρ * F μ ρ * D ρ (F ν μ) := by
    have hb := hBianchi μ ν ρ
    rw [hskew ρ μ, hskew μ ν, map_neg, map_neg] at hb
    linear_combination -(ε μ * ε ρ * F μ ρ) * hb
  have hswap :
      (∑ μ, ∑ ρ, ε μ * ε ρ * F μ ρ * D ρ (F ν μ)) =
        -(∑ μ, ∑ ρ, ε μ * ε ρ * F μ ρ * D μ (F ν ρ)) := by
    calc
      (∑ μ, ∑ ρ, ε μ * ε ρ * F μ ρ * D ρ (F ν μ)) =
          ∑ ρ, ∑ μ, ε μ * ε ρ * F μ ρ * D ρ (F ν μ) := Finset.sum_comm
      _ = ∑ μ, ∑ ρ, -(ε μ * ε ρ * F μ ρ * D μ (F ν ρ)) := by
        apply Finset.sum_congr rfl
        intro μ _
        apply Finset.sum_congr rfl
        intro ρ _
        rw [hskew ρ μ]
        simp only [mul_neg, neg_mul]
        ac_rfl
      _ = -(∑ μ, ∑ ρ, ε μ * ε ρ * F μ ρ * D μ (F ν ρ)) := by
        simp only [Finset.sum_neg_distrib]
  unfold squareGradientContraction transportContraction
  simp only [hpoint, Finset.sum_sub_distrib]
  rw [hswap, sub_neg_eq_add]

omit [DecidableEq ι] in
/-- The Bianchi contribution cancels the derivative of the one-quarter trace term. -/
theorem transportContraction_eq_quarter_deriv_fieldSquare
    (D : ι → Derivation ℝ A A) (ε : ι → A) (F : Matrix ι ι A)
    (hεconst : ∀ μ ν, D μ (ε ν) = 0)
    (hskew : ∀ μ ν, F μ ν = -F ν μ)
    (hBianchi : ∀ μ ν ρ, D μ (F ν ρ) + D ν (F ρ μ) + D ρ (F μ ν) = 0)
    (ν : ι) :
    transportContraction D ε F ν = algebraMap ℝ A (1 / 4) * D ν (fieldSquare ε F) := by
  have hquarter : algebraMap ℝ A (1 / 4) * (4 : A) = 1 := by
    calc
      algebraMap ℝ A (1 / 4) * (4 : A) =
          algebraMap ℝ A ((1 / 4 : ℝ) * 4) := by
        simp only [map_mul, map_ofNat]
      _ = 1 := by norm_num
  rw [deriv_fieldSquare D ε F hεconst ν, bianchi_contraction D ε F hskew hBianchi ν]
  calc
    transportContraction D ε F ν =
        (algebraMap ℝ A (1 / 4) * 4) * transportContraction D ε F ν := by
      rw [hquarter, one_mul]
    _ = _ := by
      rw [show (4 : A) = 2 + 2 by norm_num]
      simp only [mul_add, add_mul, mul_assoc, two_mul]

/-- Vacuum Maxwell and Bianchi equations imply the metric-weighted covariant stress divergence. -/
theorem weighted_tensor_divergence_zero
    (D : ι → Derivation ℝ A A) (ε : ι → A) (F : Matrix ι ι A)
    (hε : ∀ μ, ε μ * ε μ = 1)
    (hεconst : ∀ μ ν, D μ (ε ν) = 0)
    (hskew : ∀ μ ν, F μ ν = -F ν μ)
    (hBianchi : ∀ μ ν ρ, D μ (F ν ρ) + D ν (F ρ μ) + D ρ (F μ ν) = 0)
    (hMaxwell : ∀ ν, ∑ μ, ε μ * D μ (F μ ν) = 0)
    (ν : ι) :
    (∑ μ, ε μ * D μ (tensor ε F μ ν)) = 0 := by
  have hg (μ α β : ι) : D μ (metricEntry ε α β) = 0 := by
    by_cases hab : α = β
    · subst β
      simp only [metricEntry_self, hεconst]
    · simp only [metricEntry, hab, ite_false, map_zero]
  have hproduct (μ ρ : ι) :
      D μ (ε ρ * F μ ρ * F ν ρ) =
        ε ρ * D μ (F μ ρ) * F ν ρ + ε ρ * F μ ρ * D μ (F ν ρ) := by
    simp only [Derivation.leibniz, smul_eq_mul, hεconst,
      mul_zero, add_zero]
    ac_rfl
  have htrace (μ : ι) :
      D μ (algebraMap ℝ A (1 / 4) * metricEntry ε μ ν * fieldSquare ε F) =
        algebraMap ℝ A (1 / 4) * metricEntry ε μ ν * D μ (fieldSquare ε F) := by
    simp only [Derivation.leibniz, smul_eq_mul, Derivation.map_algebraMap, hg,
      mul_zero, add_zero]
  have hderiv (μ : ι) :
      D μ (tensor ε F μ ν) =
        (∑ ρ, ε ρ * D μ (F μ ρ) * F ν ρ) +
          (∑ ρ, ε ρ * F μ ρ * D μ (F ν ρ)) -
          algebraMap ℝ A (1 / 4) * metricEntry ε μ ν * D μ (fieldSquare ε F) := by
    simp only [tensor, map_sub, map_sum, hproduct, htrace, Finset.sum_add_distrib]
  have hsplit (μ : ι) :
      ε μ * D μ (tensor ε F μ ν) =
        (∑ ρ, ε μ * ε ρ * D μ (F μ ρ) * F ν ρ) +
          (∑ ρ, ε μ * ε ρ * F μ ρ * D μ (F ν ρ)) -
          algebraMap ℝ A (1 / 4) * (ε μ * metricEntry ε μ ν) * D μ (fieldSquare ε F) := by
    rw [hderiv]
    simp only [mul_sub, mul_add, Finset.mul_sum, mul_assoc]
    ac_rfl
  have hfirst : (∑ μ, ∑ ρ, ε μ * ε ρ * D μ (F μ ρ) * F ν ρ) = 0 := by
    calc
      (∑ μ, ∑ ρ, ε μ * ε ρ * D μ (F μ ρ) * F ν ρ) =
          ∑ ρ, ∑ μ, ε μ * ε ρ * D μ (F μ ρ) * F ν ρ := Finset.sum_comm
      _ = ∑ ρ, ε ρ * (∑ μ, ε μ * D μ (F μ ρ)) * F ν ρ := by
        apply Finset.sum_congr rfl
        intro ρ _
        simp only [Finset.mul_sum, Finset.sum_mul]
        exact Finset.sum_congr rfl fun μ _ => by ring
      _ = 0 := by simp only [hMaxwell, mul_zero, zero_mul, Finset.sum_const_zero]
  have htraceSum :
      (∑ μ, algebraMap ℝ A (1 / 4) * (ε μ * metricEntry ε μ ν) * D μ (fieldSquare ε F)) =
        algebraMap ℝ A (1 / 4) * D ν (fieldSquare ε F) := by
    rw [Finset.sum_eq_single ν]
    · simp only [metricEntry_self, hε, mul_one]
    · intro μ _ hne
      simp only [metricEntry, hne, ite_false, mul_zero, zero_mul]
    · simp
  simp only [hsplit, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [hfirst, htraceSum]
  change 0 + transportContraction D ε F ν -
      algebraMap ℝ A (1 / 4) * D ν (fieldSquare ε F) = 0
  rw [transportContraction_eq_quarter_deriv_fieldSquare D ε F hεconst hskew hBianchi ν]
  simp only [zero_add, sub_self]

/-- Raising the constant metric indices gives the ordinary divergence of the contravariant stress. -/
theorem raisedTensor_stressDivergence_zero
    (D : ι → Derivation ℝ A A) (ε : ι → A) (F : Matrix ι ι A)
    (hε : ∀ μ, ε μ * ε μ = 1)
    (hεconst : ∀ μ ν, D μ (ε ν) = 0)
    (hskew : ∀ μ ν, F μ ν = -F ν μ)
    (hBianchi : ∀ μ ν ρ, D μ (F ν ρ) + D ν (F ρ μ) + D ρ (F μ ν) = 0)
    (hMaxwell : ∀ ν, ∑ μ, ε μ * D μ (F μ ν) = 0)
    (ν : ι) :
    stressDivergence D (raisedTensor ε F) ν = 0 := by
  have hderiv (μ : ι) :
      D μ (raisedTensor ε F μ ν) = ε μ * ε ν * D μ (tensor ε F μ ν) := by
    simp only [raisedTensor, Derivation.leibniz, smul_eq_mul, hεconst,
      mul_zero, add_zero]
  unfold stressDivergence
  simp only [hderiv]
  calc
    (∑ μ, ε μ * ε ν * D μ (tensor ε F μ ν)) =
        ε ν * (∑ μ, ε μ * D μ (tensor ε F μ ν)) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun μ _ => by ac_rfl
    _ = 0 := by
      rw [weighted_tensor_divergence_zero D ε F hε hεconst hskew hBianchi hMaxwell ν,
        mul_zero]

end InfoGeometry.Conformal.MaxwellStressTensor
