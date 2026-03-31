import InfoGeometry.Canonical.BogoliubovClosedForms
import InfoGeometry.Krein.SplitQuadraticSheets

namespace InfoGeometry.Canonical.BogoliubovProjectorTransport

open InfoGeometry.Canonical.BogoliubovTransport
open InfoGeometry.Canonical.BogoliubovClosedForms
open InfoGeometry.Canonical.TomitaTakesaki
open InfoGeometry.Krein

section Basic

variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

section Projectors

theorem eps_comp_spectralPlusProj :
    (modularSignEpsilon (E := E)).comp (spectralPlusProj (E := E))
      = spectralPlusProj (E := E) := by
  apply ContinuousLinearMap.ext
  intro x
  apply DoubledSpace.ext <;>
    simp [spectralPlusProj, TomitaTakesaki.modularSignEpsilon, spectral_epsilon_apply]

theorem eps_comp_spectralMinusProj :
    (modularSignEpsilon (E := E)).comp (spectralMinusProj (E := E))
      = -(spectralMinusProj (E := E)) := by
  apply ContinuousLinearMap.ext
  intro x
  apply DoubledSpace.ext <;>
    simp [spectralMinusProj, TomitaTakesaki.modularSignEpsilon, spectral_epsilon_apply,
      sub_eq_add_neg, smul_add, smul_neg]

theorem spectralPlusProj_comp_eps :
    (spectralPlusProj (E := E)).comp (modularSignEpsilon (E := E))
      = spectralPlusProj (E := E) := by
  apply ContinuousLinearMap.ext
  intro x
  apply DoubledSpace.ext <;>
    simp [spectralPlusProj, TomitaTakesaki.modularSignEpsilon, spectral_epsilon_apply]

theorem spectralMinusProj_comp_eps :
    (spectralMinusProj (E := E)).comp (modularSignEpsilon (E := E))
      = -(spectralMinusProj (E := E)) := by
  apply ContinuousLinearMap.ext
  intro x
  apply DoubledSpace.ext <;>
    simp [spectralMinusProj, TomitaTakesaki.modularSignEpsilon, spectral_epsilon_apply,
      sub_eq_add_neg, smul_add, smul_neg]

omit [CompleteSpace E] in
theorem spectralPlusProj_comp_J :
    (spectralPlusProj (E := E)).comp (modularConjugationJ (E := E))
      = (modularConjugationJ (E := E)).comp (spectralMinusProj (E := E)) := by
  apply ContinuousLinearMap.ext
  intro x
  apply DoubledSpace.ext <;>
    simp [spectralPlusProj, spectralMinusProj, TomitaTakesaki.modularConjugationJ,
      spectral_epsilon_apply, sub_eq_add_neg, smul_add, smul_neg]

omit [CompleteSpace E] in
theorem spectralMinusProj_comp_J :
    (spectralMinusProj (E := E)).comp (modularConjugationJ (E := E))
      = (modularConjugationJ (E := E)).comp (spectralPlusProj (E := E)) := by
  apply ContinuousLinearMap.ext
  intro x
  apply DoubledSpace.ext <;>
    simp [spectralPlusProj, spectralMinusProj, TomitaTakesaki.modularConjugationJ,
      spectral_epsilon_apply, sub_eq_add_neg, smul_add, smul_neg]

omit [CompleteSpace E] in
theorem spectralPlusProj_comp_K :
    (spectralPlusProj (E := E)).comp (modularComplexI (E := E))
      = (modularComplexI (E := E)).comp (spectralMinusProj (E := E)) := by
  apply ContinuousLinearMap.ext
  intro x
  apply DoubledSpace.ext <;>
    simp [spectralPlusProj, spectralMinusProj, TomitaTakesaki.modularComplexI,
      spectral_epsilon_apply, sub_eq_add_neg, smul_add, smul_neg]

omit [CompleteSpace E] in
theorem spectralMinusProj_comp_K :
    (spectralMinusProj (E := E)).comp (modularComplexI (E := E))
      = (modularComplexI (E := E)).comp (spectralPlusProj (E := E)) := by
  apply ContinuousLinearMap.ext
  intro x
  apply DoubledSpace.ext <;>
    simp [spectralPlusProj, spectralMinusProj, TomitaTakesaki.modularComplexI,
      spectral_epsilon_apply, sub_eq_add_neg, smul_add, smul_neg]

/-- Positive projector block of the `ε`-boost transport matrix. -/
theorem spectralPlusProj_comp_epsilonBoost
    (t : ℝ) :
    (spectralPlusProj (E := E)).comp (epsilonBoost (E := E) t)
      = Real.exp t • (spectralPlusProj (E := E)) := by
  rw [epsilonBoost_eq_cosh_add_sinh_eps (E := E) t]
  rw [ContinuousLinearMap.comp_add, ContinuousLinearMap.comp_smul, ContinuousLinearMap.comp_smul,
    spectralPlusProj_comp_eps (E := E)]
  calc
    Real.cosh t • (spectralPlusProj (E := E)) + Real.sinh t • (spectralPlusProj (E := E))
      = (Real.cosh t + Real.sinh t) • (spectralPlusProj (E := E)) := by
          simpa using
            (add_smul (Real.cosh t) (Real.sinh t) (spectralPlusProj (E := E))).symm
    _ = Real.exp t • (spectralPlusProj (E := E)) := by
          rw [Real.cosh_add_sinh]

/-- Negative projector block of the `ε`-boost transport matrix. -/
theorem spectralMinusProj_comp_epsilonBoost
    (t : ℝ) :
    (spectralMinusProj (E := E)).comp (epsilonBoost (E := E) t)
      = Real.exp (-t) • (spectralMinusProj (E := E)) := by
  rw [epsilonBoost_eq_cosh_add_sinh_eps (E := E) t]
  rw [ContinuousLinearMap.comp_add, ContinuousLinearMap.comp_smul, ContinuousLinearMap.comp_smul,
    spectralMinusProj_comp_eps (E := E)]
  rw [smul_neg]
  calc
    Real.cosh t • (spectralMinusProj (E := E)) + -(Real.sinh t • (spectralMinusProj (E := E)))
      = (Real.cosh t - Real.sinh t) • (spectralMinusProj (E := E)) := by
          simpa [sub_eq_add_neg] using
            (sub_smul (Real.cosh t) (Real.sinh t) (spectralMinusProj (E := E))).symm
    _ = Real.exp (-t) • (spectralMinusProj (E := E)) := by
          rw [Real.cosh_sub_sinh]

/-- Positive projector block of the `J`-boost transport matrix. -/
theorem spectralPlusProj_comp_JBoost
    (t : ℝ) :
    (spectralPlusProj (E := E)).comp (JBoost (E := E) t)
      = Real.cosh t • (spectralPlusProj (E := E))
        + Real.sinh t • ((modularConjugationJ (E := E)).comp (spectralMinusProj (E := E))) := by
  rw [JBoost_eq_cosh_add_sinh_J (E := E) t]
  rw [ContinuousLinearMap.comp_add, ContinuousLinearMap.comp_smul, ContinuousLinearMap.comp_smul]
  have hcomp1 : (spectralPlusProj (E := E)).comp (1 : EndH) = spectralPlusProj (E := E) := by
    change (spectralPlusProj (E := E)).comp (ContinuousLinearMap.id ℝ H₂) =
      spectralPlusProj (E := E)
    exact ContinuousLinearMap.comp_id (spectralPlusProj (E := E))
  rw [hcomp1, spectralPlusProj_comp_J (E := E)]

/-- Negative projector block of the `J`-boost transport matrix. -/
theorem spectralMinusProj_comp_JBoost
    (t : ℝ) :
    (spectralMinusProj (E := E)).comp (JBoost (E := E) t)
      = Real.cosh t • (spectralMinusProj (E := E))
        + Real.sinh t • ((modularConjugationJ (E := E)).comp (spectralPlusProj (E := E))) := by
  rw [JBoost_eq_cosh_add_sinh_J (E := E) t]
  rw [ContinuousLinearMap.comp_add, ContinuousLinearMap.comp_smul, ContinuousLinearMap.comp_smul]
  have hcomp1 : (spectralMinusProj (E := E)).comp (1 : EndH) = spectralMinusProj (E := E) := by
    change (spectralMinusProj (E := E)).comp (ContinuousLinearMap.id ℝ H₂) =
      spectralMinusProj (E := E)
    exact ContinuousLinearMap.comp_id (spectralMinusProj (E := E))
  rw [hcomp1, spectralMinusProj_comp_J (E := E)]

/-- Positive projector block of the `K`-rotation transport matrix. -/
theorem spectralPlusProj_comp_KRotation
    (t : ℝ) :
    (spectralPlusProj (E := E)).comp (KRotation (E := E) t)
      = Real.cos t • (spectralPlusProj (E := E))
        + Real.sin t • ((modularComplexI (E := E)).comp (spectralMinusProj (E := E))) := by
  rw [KRotation_eq_cos_add_sin_K (E := E) t]
  rw [ContinuousLinearMap.comp_add, ContinuousLinearMap.comp_smul, ContinuousLinearMap.comp_smul]
  have hcomp1 : (spectralPlusProj (E := E)).comp (1 : EndH) = spectralPlusProj (E := E) := by
    change (spectralPlusProj (E := E)).comp (ContinuousLinearMap.id ℝ H₂) =
      spectralPlusProj (E := E)
    exact ContinuousLinearMap.comp_id (spectralPlusProj (E := E))
  rw [hcomp1, spectralPlusProj_comp_K (E := E)]

/-- Negative projector block of the `K`-rotation transport matrix. -/
theorem spectralMinusProj_comp_KRotation
    (t : ℝ) :
    (spectralMinusProj (E := E)).comp (KRotation (E := E) t)
      = Real.cos t • (spectralMinusProj (E := E))
        + Real.sin t • ((modularComplexI (E := E)).comp (spectralPlusProj (E := E))) := by
  rw [KRotation_eq_cos_add_sin_K (E := E) t]
  rw [ContinuousLinearMap.comp_add, ContinuousLinearMap.comp_smul, ContinuousLinearMap.comp_smul]
  have hcomp1 : (spectralMinusProj (E := E)).comp (1 : EndH) = spectralMinusProj (E := E) := by
    change (spectralMinusProj (E := E)).comp (ContinuousLinearMap.id ℝ H₂) =
      spectralMinusProj (E := E)
    exact ContinuousLinearMap.comp_id (spectralMinusProj (E := E))
  rw [hcomp1, spectralMinusProj_comp_K (E := E)]

end Projectors

section Sheets

open InfoGeometry.Krein.SplitQuadraticSheets

theorem epsilonBoost_preserves_plusSheet
    (t : ℝ) {u : H₂} (hu : u ∈ plusSheet (E := E)) :
    epsilonBoost (E := E) t u ∈ plusSheet (E := E) := by
  rw [eq_plusPoint_of_mem_plusSheet (E := E) hu]
  rw [mem_plusSheet_iff_snd_eq_zero]
  simp [plusPoint, epsilonBoost_apply, TomitaTakesaki.modularSignEpsilon]

theorem epsilonBoost_preserves_minusSheet
    (t : ℝ) {u : H₂} (hu : u ∈ minusSheet (E := E)) :
    epsilonBoost (E := E) t u ∈ minusSheet (E := E) := by
  rw [eq_minusPoint_of_mem_minusSheet (E := E) hu]
  rw [mem_minusSheet_iff_fst_eq_zero]
  simp [minusPoint, epsilonBoost_apply, TomitaTakesaki.modularSignEpsilon]

omit [CompleteSpace E] in
theorem modularConjugationJ_maps_plusSheet_to_minusSheet
    {u : H₂} (hu : u ∈ plusSheet (E := E)) :
    modularConjugationJ (E := E) u ∈ minusSheet (E := E) := by
  rw [eq_plusPoint_of_mem_plusSheet (E := E) hu]
  rw [mem_minusSheet_iff_fst_eq_zero]
  simp [plusPoint, TomitaTakesaki.modularConjugationJ]

omit [CompleteSpace E] in
theorem modularConjugationJ_maps_minusSheet_to_plusSheet
    {u : H₂} (hu : u ∈ minusSheet (E := E)) :
    modularConjugationJ (E := E) u ∈ plusSheet (E := E) := by
  rw [eq_minusPoint_of_mem_minusSheet (E := E) hu]
  rw [mem_plusSheet_iff_snd_eq_zero]
  simp [minusPoint, TomitaTakesaki.modularConjugationJ]

omit [CompleteSpace E] in
theorem modularComplexI_maps_plusSheet_to_minusSheet
    {u : H₂} (hu : u ∈ plusSheet (E := E)) :
    modularComplexI (E := E) u ∈ minusSheet (E := E) := by
  rw [eq_plusPoint_of_mem_plusSheet (E := E) hu]
  rw [mem_minusSheet_iff_fst_eq_zero]
  simp [plusPoint, TomitaTakesaki.modularComplexI]

omit [CompleteSpace E] in
theorem modularComplexI_maps_minusSheet_to_plusSheet
    {u : H₂} (hu : u ∈ minusSheet (E := E)) :
    modularComplexI (E := E) u ∈ plusSheet (E := E) := by
  rw [eq_minusPoint_of_mem_minusSheet (E := E) hu]
  rw [mem_plusSheet_iff_snd_eq_zero]
  simp [minusPoint, TomitaTakesaki.modularComplexI]

end Sheets

end Basic

end InfoGeometry.Canonical.BogoliubovProjectorTransport
