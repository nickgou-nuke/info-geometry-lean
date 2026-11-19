/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Conditional thermal wavelength and parameter identification

Source: M. M. Vopson, "Experimental protocol for testing the
mass-energy-information equivalence principle", AIP Advances 12, 035311
(2022), equation (11), article page 4 (PDF page 5), DOI 10.1063/5.0087175.

The mathematical input is the proposed wavelength law `h*c/(I*kB*T*log 2)`.
All quantities are real numerical values in fixed consistent units. Its
physical applicability is a hypothesis: these theorems do not construct an
erasure process or derive additional photons from thermodynamics.

The final two results explicitly introduce an additional model parameter
`eta`: the fraction of the proposed energy assigned to each putative emitted
photon. It is not a detection probability. Ordinary detection inefficiency
affects counts and need not change a photon's wavelength. In this conditional
energy-fraction model the identifiable parameter is `eta * I`.
-/

namespace InfoGeometry.Physics.InformationEnergy.ThermalSpectrum

/-- The proposed monochromatic wavelength, expressed in consistent units. -/
noncomputable def wavelength (h c kB I T : ℝ) : ℝ :=
  h * c / (I * kB * T * Real.log 2)

/-- Positive constants, temperature, and information give a positive wavelength. -/
theorem wavelength_pos {h c kB I T : ℝ}
    (hh : 0 < h) (hc : 0 < c) (hkB : 0 < kB) (hI : 0 < I) (hT : 0 < T) :
    0 < wavelength h c kB I T := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  unfold wavelength
  exact div_pos (mul_pos hh hc) (mul_pos (mul_pos (mul_pos hI hkB) hT) hlog)

/-- The product of wavelength, information, and temperature is constant. -/
theorem wavelength_mul_information_mul_temperature {h c kB I T : ℝ}
    (hkB : 0 < kB) (hI : 0 < I) (hT : 0 < T) :
    wavelength h c kB I T * I * T = h * c / (kB * Real.log 2) := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  unfold wavelength
  field_simp [hkB.ne', hI.ne', hT.ne', hlog.ne']

/-- Scaling the positive temperature by `a` divides the wavelength by `a`. -/
theorem wavelength_temperature_scale {h c kB I T a : ℝ}
    (hkB : 0 < kB) (hI : 0 < I) (hT : 0 < T) (ha : 0 < a) :
    wavelength h c kB I (a * T) = wavelength h c kB I T / a := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  unfold wavelength
  field_simp [hkB.ne', hI.ne', hT.ne', ha.ne', hlog.ne']

/-- At fixed positive information, the proposed spectrum strictly decreases with temperature. -/
theorem wavelength_strictAntiOn_temperature {h c kB I : ℝ}
    (hh : 0 < h) (hc : 0 < c) (hkB : 0 < kB) (hI : 0 < I) :
    StrictAntiOn (wavelength h c kB I) (Set.Ioi 0) := by
  intro T₁ hT₁ T₂ hT₂ hT
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hden₁ : 0 < I * kB * T₁ * Real.log 2 :=
    mul_pos (mul_pos (mul_pos hI hkB) hT₁) hlog
  have hden₂ : 0 < I * kB * T₂ * Real.log 2 :=
    mul_pos (mul_pos (mul_pos hI hkB) hT₂) hlog
  unfold wavelength
  apply (div_lt_div_iff_of_pos_left (mul_pos hh hc) hden₂ hden₁).mpr
  exact mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_left hT (mul_pos hI hkB)) hlog

/-- At fixed positive temperature, wavelength order is the reverse of information order. -/
theorem wavelength_lt_iff_information_gt {h c kB I₁ I₂ T : ℝ}
    (hh : 0 < h) (hc : 0 < c) (hkB : 0 < kB)
    (hI₁ : 0 < I₁) (hI₂ : 0 < I₂) (hT : 0 < T) :
    wavelength h c kB I₁ T < wavelength h c kB I₂ T ↔ I₂ < I₁ := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hden₁ : 0 < I₁ * kB * T * Real.log 2 :=
    mul_pos (mul_pos (mul_pos hI₁ hkB) hT) hlog
  have hden₂ : 0 < I₂ * kB * T * Real.log 2 :=
    mul_pos (mul_pos (mul_pos hI₂ hkB) hT) hlog
  unfold wavelength
  rw [div_lt_div_iff_of_pos_left (mul_pos hh hc) hden₁ hden₂,
    mul_lt_mul_iff_of_pos_right hlog, mul_lt_mul_iff_of_pos_right hT,
    mul_lt_mul_iff_of_pos_right hkB]

/-- Positive wavelength data identify information exactly, conditional on the proposed law. -/
theorem information_eq_iff_wavelength_eq {h c kB I T observed : ℝ}
    (hkB : 0 < kB) (hI : 0 < I) (hT : 0 < T) (hobserved : 0 < observed) :
    I = h * c / (kB * T * Real.log 2 * observed) ↔
      observed = wavelength h c kB I T := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hleft : kB * T * Real.log 2 * observed ≠ 0 :=
    ne_of_gt (mul_pos (mul_pos (mul_pos hkB hT) hlog) hobserved)
  have hright : I * kB * T * Real.log 2 ≠ 0 :=
    ne_of_gt (mul_pos (mul_pos (mul_pos hI hkB) hT) hlog)
  unfold wavelength
  rw [eq_div_iff hleft, eq_div_iff hright]
  constructor
  · intro hdata
    calc
      observed * (I * kB * T * Real.log 2) =
          I * (kB * T * Real.log 2 * observed) := by ring
      _ = h * c := hdata
  · intro hdata
    calc
      I * (kB * T * Real.log 2 * observed) =
          observed * (I * kB * T * Real.log 2) := by ring
      _ = h * c := hdata

/-- With an unknown emitted-energy fraction, equal wavelengths identify only `eta * I`. -/
theorem effective_wavelength_eq_iff {h c kB T eta₁ eta₂ I₁ I₂ : ℝ}
    (hh : 0 < h) (hc : 0 < c) (hkB : 0 < kB) (hT : 0 < T)
    (heta₁ : 0 < eta₁) (heta₂ : 0 < eta₂) (hI₁ : 0 < I₁) (hI₂ : 0 < I₂) :
    wavelength h c kB (eta₁ * I₁) T = wavelength h c kB (eta₂ * I₂) T ↔
      eta₁ * I₁ = eta₂ * I₂ := by
  constructor
  · intro hwavelength
    have hpos₁ := wavelength_pos hh hc hkB (mul_pos heta₁ hI₁) hT
    have hpos₂ := wavelength_pos hh hc hkB (mul_pos heta₂ hI₂) hT
    have hinverse₁ : eta₁ * I₁ = h * c /
        (kB * T * Real.log 2 * wavelength h c kB (eta₁ * I₁) T) :=
      (information_eq_iff_wavelength_eq hkB (mul_pos heta₁ hI₁) hT hpos₁).mpr rfl
    have hinverse₂ : eta₂ * I₂ = h * c /
        (kB * T * Real.log 2 * wavelength h c kB (eta₂ * I₂) T) :=
      (information_eq_iff_wavelength_eq hkB (mul_pos heta₂ hI₂) hT hpos₂).mpr rfl
    rw [hwavelength] at hinverse₁
    exact hinverse₁.trans hinverse₂.symm
  · intro heffective
    rw [heffective]

/-- Opposite rescalings of emitted fraction and intrinsic information preserve the spectrum.

When `eta` is physically restricted to at most one, admissibility of `a * eta`
is an additional condition on the reparametrization, not a consequence here.
-/
theorem emitted_fraction_rescaling (h c kB I T eta : ℝ) {a : ℝ} (ha : 0 < a) :
    wavelength h c kB ((a * eta) * (I / a)) T =
      wavelength h c kB (eta * I) T := by
  have heffective : (a * eta) * (I / a) = eta * I := by
    field_simp [ha.ne']
  rw [heffective]

end InfoGeometry.Physics.InformationEnergy.ThermalSpectrum
