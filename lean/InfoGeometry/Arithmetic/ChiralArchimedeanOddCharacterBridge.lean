/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Analysis.GammaStripRatioSchwartzGaussian
import InfoGeometry.Arithmetic.TateAdelicSignAndOddCharacterCosetBridge
import InfoGeometry.Arithmetic.CompletedZetaSouriauDInfinityThermodynamics

/-!
# InfoGeometry.Arithmetic.ChiralArchimedeanOddCharacterBridge

Welds the even (`n = 0`) and odd (`n = 1`) weighted Gaussian Mellin transforms and
vertical-strip Gamma ratios (`GammaStripRatioSchwartzGaussian`) directly to
Tate's opposite-sign adelic cancellation and odd-character shifted-coset
non-vanishing (`TateAdelicSignAndOddCharacterCosetBridge`), together with the
Souriau `D_∞` critical-line reflection (`CompletedZetaSouriauDInfinityThermodynamics`):

1. **Even vs. Odd Archimedean Mellin Factors at `b = π`**:
   - `n = 0` (`evenArchimedeanKernel t = exp (-π t²)`): even (`f (-t) = f t`) with
     Mellin transform `(1 / 2) * π^(-(s / 2)) * Γ(s / 2)`.
   - `n = 1` (`oddArchimedeanKernel t = t * exp (-π t²)`): odd (`f (-t) = -f t`) with
     Mellin transform `(1 / 2) * π^(-((s + 1) / 2)) * Γ((s + 1) / 2)`.
2. **Functional-Equation Gamma Ratio Exponent & Critical-Line Balance**:
   On `|σ| ≤ M`, `|1 - σ| ≤ M`, `1 ≤ |t|`, `‖Γ⟨σ, t⟩ / Γ⟨1 - σ, t⟩‖ ≤ C * |t| ^ (2 * σ - 1)`,
   and the exponent `2 * σ - 1` vanishes if and only if `CriticalLine ⟨σ, t⟩`
   (equivalently `antiunitaryCriticalReflection ⟨σ, t⟩ = ⟨σ, t⟩`).
3. **Unified Chiral Archimedean ↔ Odd-Character Coset ↔ Souriau Synthesis**:
   Packages the even/odd Archimedean Mellin identities, `quadCharMod3` oddness,
   even-indicator erasure vs. shifted-coset non-vanishing, Tate opposite-sign
   cancellation at `1 / 3`, and the Souriau critical-line balance condition.
-/

noncomputable section

namespace InfoGeometry.Arithmetic.ChiralArchimedeanOddCharacterBridge

open InfoGeometry.Analysis.GammaStripRatioSchwartzGaussian
open InfoGeometry.Arithmetic.TateAdelicSignAndOddCharacterCosetBridge
open InfoGeometry.Arithmetic.CompletedZetaSouriauDInfinityThermodynamics

/-! ## 1. Even (`n = 0`) and odd (`n = 1`) Archimedean Gaussian kernels at `b = π` -/

/-- Even Archimedean Gaussian test function `t ↦ exp (-π t²)` (`χ(-1) = +1`). -/
def evenArchimedeanKernel (t : ℝ) : ℂ :=
  (Real.exp (-Real.pi * t ^ 2) : ℂ)

/-- Odd Archimedean weighted Gaussian test function `t ↦ t * exp (-π t²)` (`χ(-1) = -1`). -/
def oddArchimedeanKernel (t : ℝ) : ℂ :=
  (t : ℂ) * (Real.exp (-Real.pi * t ^ 2) : ℂ)

theorem evenArchimedeanKernel_neg (t : ℝ) :
    evenArchimedeanKernel (-t) = evenArchimedeanKernel t := by
  simp [evenArchimedeanKernel]

theorem oddArchimedeanKernel_neg (t : ℝ) :
    oddArchimedeanKernel (-t) = -oddArchimedeanKernel t := by
  simp [oddArchimedeanKernel]

/-- Even (`n = 0`) Archimedean Mellin transform at `b = π`. -/
theorem mellin_evenArchimedeanKernel {s : ℂ} (hs : 0 < s.re) :
    mellin evenArchimedeanKernel s =
      (1 / 2 : ℂ) * (Real.pi : ℂ) ^ (-(s / 2)) * Complex.Gamma (s / 2) := by
  unfold evenArchimedeanKernel
  have h := mellin_weightedGaussian Real.pi Real.pi_pos 0 s hs
  simpa only [pow_zero, one_mul, Nat.cast_zero, add_zero] using h

/-- Odd (`n = 1`) Archimedean Mellin transform at `b = π`, matching odd Dirichlet
characters (`χ(-1) = -1`) such as `quadCharMod3`. -/
theorem mellin_oddArchimedeanKernel {s : ℂ} (hs : 0 < s.re) :
    mellin oddArchimedeanKernel s =
      (1 / 2 : ℂ) * (Real.pi : ℂ) ^ (-((s + 1) / 2)) * Complex.Gamma ((s + 1) / 2) := by
  unfold oddArchimedeanKernel
  have h := mellin_weightedGaussian Real.pi Real.pi_pos 1 s hs
  simpa only [pow_one, Nat.cast_one] using h

/-! ## 2. Functional-equation Gamma ratio exponent and Souriau critical-line balance -/

/-- Across functional reflection `σ ↦ 1 - σ`, the vertical-strip Gamma ratio
has exact height exponent `2 * σ - 1`. -/
theorem norm_Gamma_functionalReflection_ratio_bound {M : ℝ} (hM : 1 ≤ M) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ t : ℝ, |σ| ≤ M → |1 - σ| ≤ M → 1 ≤ |t| →
      ‖Complex.Gamma ⟨σ, t⟩ / Complex.Gamma ⟨1 - σ, t⟩‖ ≤ C * |t| ^ (2 * σ - 1) := by
  obtain ⟨C, hC, hbound⟩ := norm_Gamma_div_le_rpow_on_strip hM
  refine ⟨C, hC, fun σ t hσ h1σ ht ↦ ?_⟩
  have hsub : σ - (1 - σ) = 2 * σ - 1 := by ring
  simpa [hsub] using hbound σ (1 - σ) t hσ h1σ ht

/-- The functional-equation Gamma-ratio exponent `2 * σ - 1` vanishes if and only
if `⟨σ, t⟩` lies on the Souriau `D_∞` critical line (`antiunitaryCriticalReflection`
fixed locus). -/
theorem gammaRatioExponent_eq_zero_iff_criticalLine (σ t : ℝ) :
    (2 * σ - 1 = 0 ↔ CriticalLine ⟨σ, t⟩) ∧
    (2 * σ - 1 = 0 ↔ antiunitaryCriticalReflection ⟨σ, t⟩ = ⟨σ, t⟩) := by
  have hcrit : 2 * σ - 1 = 0 ↔ CriticalLine ⟨σ, t⟩ := by
    simp only [CriticalLine]
    constructor <;> intro h <;> linarith
  exact ⟨hcrit,
    hcrit.trans ((fixed_antiunitaryCriticalReflection_iff_criticalLine ⟨σ, t⟩).symm.trans eq_comm)⟩

/-! ## 3. Unified Chiral Archimedean ↔ Odd-Character Coset ↔ Souriau Synthesis -/

/-- Joint chiral Archimedean + Tate adelic + odd-character mod-3 + Souriau `D_∞`
synthesis theorem. -/
theorem chiralArchimedean_oddCharacter_souriau_synthesis
    {s : ℂ} (hs : 0 < s.re) (σ t : ℝ) :
    (mellin evenArchimedeanKernel s =
      (1 / 2 : ℂ) * (Real.pi : ℂ) ^ (-(s / 2)) * Complex.Gamma (s / 2)) ∧
    (mellin oddArchimedeanKernel s =
      (1 / 2 : ℂ) * (Real.pi : ℂ) ^ (-((s + 1) / 2)) * Complex.Gamma ((s + 1) / 2)) ∧
    (∀ u : ℝ, evenArchimedeanKernel (-u) = evenArchimedeanKernel u ∧
      oddArchimedeanKernel (-u) = -oddArchimedeanKernel u) ∧
    (quadCharMod3 (-1) = -1 ∧
      (∀ f : (ZMod 3)ˣ → ℂ, (∀ u, f (-u) = f u) →
        (∑ u : (ZMod 3)ˣ, quadCharMod3 u * f u) = 0) ∧
      (∑ u : (ZMod 3)ˣ, quadCharMod3 u * shiftedCosetIndicator 1 u) = 1) ∧
    (addCharNeg (1 / 3 : ℝ) * addCharPos (1 / 3 : ℝ) = 1) ∧
    (2 * σ - 1 = 0 ↔ antiunitaryCriticalReflection ⟨σ, t⟩ = ⟨σ, t⟩) :=
  ⟨mellin_evenArchimedeanKernel hs,
   mellin_oddArchimedeanKernel hs,
   fun u => ⟨evenArchimedeanKernel_neg u, oddArchimedeanKernel_neg u⟩,
   odd_quad_char_mod3_witness,
   tate_opposite_sign_at_one_third,
   (gammaRatioExponent_eq_zero_iff_criticalLine σ t).2⟩

end InfoGeometry.Arithmetic.ChiralArchimedeanOddCharacterBridge
