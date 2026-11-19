/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Analysis.InternalPhaseFourier
import InfoGeometry.Krein.DoubledSpace

/-!
# The native doubled real phase axis inside the Fourier integral

The carrier is the repository's `DoubledSpace E`, with the existing bounded
operator `complex_i = modular_j.comp spectral_epsilon`. Its square is `-id`
by `InfoGeometry.Krein.complex_i_sq`.

The phase axis preserves frequency. The two existing involutions
`modular_j` and `spectral_epsilon` reverse it, because their native operator
products anticommute with `complex_i`. These statements concern the actual
Lebesgue Bochner integral and require integrability of the signal.
-/

noncomputable section

namespace InfoGeometry.Analysis.DoubledInternalPhaseFourier

open MeasureTheory
open InfoGeometry.Krein
open InfoGeometry.Analysis.InternalPhaseFourier

variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Applying the internal phase axis before or after integration agrees. -/
theorem complex_i_fourierIntegral
    {f : ℝ → DoubledSpace E} (hf : Integrable f) (ξ : ℝ) :
    complex_i (E := E) (fourierIntegral (complex_i (E := E)) f ξ) =
      fourierIntegral (complex_i (E := E))
        (fun x => complex_i (E := E) (f x)) ξ := by
  exact map_fourierIntegral_of_intertwines
    (complex_i (E := E)) (complex_i (E := E)) (complex_i (E := E)) rfl hf ξ

/-- The native modular swap reverses the Fourier frequency. -/
theorem modular_j_fourierIntegral
    {f : ℝ → DoubledSpace E} (hf : Integrable f) (ξ : ℝ) :
    modular_j (E := E) (fourierIntegral (complex_i (E := E)) f ξ) =
      fourierIntegral (complex_i (E := E))
        (fun x => modular_j (E := E) (f x)) (-ξ) := by
  have hJK : (modular_j (E := E)).comp (complex_i (E := E)) =
      -((complex_i (E := E)).comp (modular_j (E := E))) := by
    rw [modular_j_comp_complex_i, complex_i_comp_modular_j, neg_neg]
  exact map_fourierIntegral_of_antiintertwines
    (complex_i (E := E)) (complex_i (E := E)) (modular_j (E := E)) hJK hf ξ

/-- The native fundamental symmetry also reverses the Fourier frequency. -/
theorem spectral_epsilon_fourierIntegral
    {f : ℝ → DoubledSpace E} (hf : Integrable f) (ξ : ℝ) :
    spectral_epsilon (E := E) (fourierIntegral (complex_i (E := E)) f ξ) =
      fourierIntegral (complex_i (E := E))
        (fun x => spectral_epsilon (E := E) (f x)) (-ξ) := by
  have hεK : (spectral_epsilon (E := E)).comp (complex_i (E := E)) =
      -((complex_i (E := E)).comp (spectral_epsilon (E := E))) := by
    rw [spectral_epsilon_comp_complex_i, complex_i_comp_spectral_epsilon]
  exact map_fourierIntegral_of_antiintertwines
    (complex_i (E := E)) (complex_i (E := E))
    (spectral_epsilon (E := E)) hεK hf ξ

end InfoGeometry.Analysis.DoubledInternalPhaseFourier

end
