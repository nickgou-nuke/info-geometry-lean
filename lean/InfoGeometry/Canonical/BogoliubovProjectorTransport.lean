import InfoGeometry.Canonical.BogoliubovClosedForms
import InfoGeometry.Krein.SplitQuadraticSheets
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.Calculus.FDeriv.Analytic

namespace BogoliubovProjectorTransport

open BogoliubovTransport
open BogoliubovClosedForms
open TomitaTakesaki
open InfoGeometry.Krein

section Basic

variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

noncomputable local instance : NormedRing EndH := inferInstance
noncomputable local instance : NormedAlgebra ℝ EndH := inferInstance
local instance : IsTopologicalRing EndH := inferInstance
local instance : CompleteSpace EndH := inferInstance

section Projectors

theorem eps_comp_spectralPlusProj :
    (modularSignEpsilon (E := E)).comp (spectralPlusProj (E := E))
      = spectralPlusProj (E := E) := by
  apply ContinuousLinearMap.ext
  intro x
  apply DoubledSpace.ext <;>
    simp [spectralPlusProj, TomitaTakesaki.modularSignEpsilon, spectral_epsilon_apply]

theorem spectral_epsilon_comp_spectralPlusProj :
    (spectral_epsilon (E := E)).comp (spectralPlusProj (E := E))
      = spectralPlusProj (E := E) := by
  simpa [TomitaTakesaki.modularSignEpsilon_eq_spectral_epsilon] using
    eps_comp_spectralPlusProj (E := E)

theorem eps_comp_spectralMinusProj :
    (modularSignEpsilon (E := E)).comp (spectralMinusProj (E := E))
      = -(spectralMinusProj (E := E)) := by
  apply ContinuousLinearMap.ext
  intro x
  apply DoubledSpace.ext <;>
    simp [spectralMinusProj, TomitaTakesaki.modularSignEpsilon, spectral_epsilon_apply,
      sub_eq_add_neg, smul_add, smul_neg]

theorem spectral_epsilon_comp_spectralMinusProj :
    (spectral_epsilon (E := E)).comp (spectralMinusProj (E := E))
      = -(spectralMinusProj (E := E)) := by
  simpa [TomitaTakesaki.modularSignEpsilon_eq_spectral_epsilon] using
    eps_comp_spectralMinusProj (E := E)

theorem spectralPlusProj_comp_eps :
    (spectralPlusProj (E := E)).comp (modularSignEpsilon (E := E))
      = spectralPlusProj (E := E) := by
  apply ContinuousLinearMap.ext
  intro x
  apply DoubledSpace.ext <;>
    simp [spectralPlusProj, TomitaTakesaki.modularSignEpsilon, spectral_epsilon_apply]

theorem spectralPlusProj_comp_spectral_epsilon :
    (spectralPlusProj (E := E)).comp (spectral_epsilon (E := E))
      = spectralPlusProj (E := E) := by
  simpa [TomitaTakesaki.modularSignEpsilon_eq_spectral_epsilon] using
    spectralPlusProj_comp_eps (E := E)

theorem spectralMinusProj_comp_eps :
    (spectralMinusProj (E := E)).comp (modularSignEpsilon (E := E))
      = -(spectralMinusProj (E := E)) := by
  apply ContinuousLinearMap.ext
  intro x
  apply DoubledSpace.ext <;>
    simp [spectralMinusProj, TomitaTakesaki.modularSignEpsilon, spectral_epsilon_apply,
      sub_eq_add_neg, smul_add, smul_neg]

theorem spectralMinusProj_comp_spectral_epsilon :
    (spectralMinusProj (E := E)).comp (spectral_epsilon (E := E))
      = -(spectralMinusProj (E := E)) := by
  simpa [TomitaTakesaki.modularSignEpsilon_eq_spectral_epsilon] using
    spectralMinusProj_comp_eps (E := E)

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
theorem spectralPlusProj_comp_modular_j :
    (spectralPlusProj (E := E)).comp (modular_j (E := E))
      = (modular_j (E := E)).comp (spectralMinusProj (E := E)) := by
  simpa [TomitaTakesaki.modularConjugationJ_eq_modular_j] using
    spectralPlusProj_comp_J (E := E)

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
theorem spectralMinusProj_comp_modular_j :
    (spectralMinusProj (E := E)).comp (modular_j (E := E))
      = (modular_j (E := E)).comp (spectralPlusProj (E := E)) := by
  simpa [TomitaTakesaki.modularConjugationJ_eq_modular_j] using
    spectralMinusProj_comp_J (E := E)

/--
A `J`-fixed doubled state is a real Majorana combination of opposite Weyl
sectors: its negative-chirality component is the `J`-mirror of its positive
chirality component.
-/
theorem majorana_fixed_eq_weylPlus_add_mirror
  (u : H₂)
  (hu : modular_j (E := E) u = u) :
    u = spectralPlusProj (E := E) u
        + modular_j (E := E) (spectralPlusProj (E := E) u) := by
  have hsum :
      spectralPlusProj (E := E) u + spectralMinusProj (E := E) u = u := by
    exact congrArg (fun F : EndH => F u) (spectralProj_sum (E := E))
  have hmirror :
      spectralMinusProj (E := E) u
        = modular_j (E := E) (spectralPlusProj (E := E) u) := by
    have h :=
      congrArg (fun F : EndH => F u)
        (spectralMinusProj_comp_modular_j (E := E))
    simpa [ContinuousLinearMap.comp_apply, hu] using h
  calc
    u = spectralPlusProj (E := E) u + spectralMinusProj (E := E) u := hsum.symm
    _ = spectralPlusProj (E := E) u
          + modular_j (E := E) (spectralPlusProj (E := E) u) := by
          rw [hmirror]

omit [CompleteSpace E] in
theorem spectralPlusProj_comp_K :
    (spectralPlusProj (E := E)).comp (InfoGeometry.Krein.clockAxis (E := E))
      = (InfoGeometry.Krein.clockAxis (E := E)).comp (spectralMinusProj (E := E)) := by
  apply ContinuousLinearMap.ext
  intro x
  apply DoubledSpace.ext <;>
    simp [spectralPlusProj, spectralMinusProj,
      spectral_epsilon_apply, sub_eq_add_neg, smul_add, smul_neg]

omit [CompleteSpace E] in
theorem spectralPlusProj_comp_complex_i :
    (spectralPlusProj (E := E)).comp (complex_i (E := E))
      = (complex_i (E := E)).comp (spectralMinusProj (E := E)) := by
  simpa [TomitaTakesaki.clockAxis_eq_complex_i] using
    spectralPlusProj_comp_K (E := E)

omit [CompleteSpace E] in
theorem spectralMinusProj_comp_K :
    (spectralMinusProj (E := E)).comp (InfoGeometry.Krein.clockAxis (E := E))
      = (InfoGeometry.Krein.clockAxis (E := E)).comp (spectralPlusProj (E := E)) := by
  apply ContinuousLinearMap.ext
  intro x
  apply DoubledSpace.ext <;>
    simp [spectralPlusProj, spectralMinusProj,
      spectral_epsilon_apply, sub_eq_add_neg, smul_add, smul_neg]

omit [CompleteSpace E] in
theorem spectralMinusProj_comp_complex_i :
    (spectralMinusProj (E := E)).comp (complex_i (E := E))
      = (complex_i (E := E)).comp (spectralPlusProj (E := E)) := by
  simpa [TomitaTakesaki.clockAxis_eq_complex_i] using
    spectralMinusProj_comp_K (E := E)

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
        + Real.sin t • ((InfoGeometry.Krein.clockAxis (E := E)).comp (spectralMinusProj (E := E))) := by
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
        + Real.sin t • ((InfoGeometry.Krein.clockAxis (E := E)).comp (spectralPlusProj (E := E))) := by
  rw [KRotation_eq_cos_add_sin_K (E := E) t]
  rw [ContinuousLinearMap.comp_add, ContinuousLinearMap.comp_smul, ContinuousLinearMap.comp_smul]
  have hcomp1 : (spectralMinusProj (E := E)).comp (1 : EndH) = spectralMinusProj (E := E) := by
    change (spectralMinusProj (E := E)).comp (ContinuousLinearMap.id ℝ H₂) =
      spectralMinusProj (E := E)
    exact ContinuousLinearMap.comp_id (spectralMinusProj (E := E))
  rw [hcomp1, spectralMinusProj_comp_K (E := E)]

end Projectors

section Sheets

open SplitQuadraticSheets

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
theorem modular_j_maps_plusSheet_to_minusSheet
    {u : H₂} (hu : u ∈ plusSheet (E := E)) :
    modular_j (E := E) u ∈ minusSheet (E := E) := by
  simpa [TomitaTakesaki.modularConjugationJ_eq_modular_j] using
    modularConjugationJ_maps_plusSheet_to_minusSheet (E := E) hu

omit [CompleteSpace E] in
theorem modularConjugationJ_maps_minusSheet_to_plusSheet
    {u : H₂} (hu : u ∈ minusSheet (E := E)) :
    modularConjugationJ (E := E) u ∈ plusSheet (E := E) := by
  rw [eq_minusPoint_of_mem_minusSheet (E := E) hu]
  rw [mem_plusSheet_iff_snd_eq_zero]
  simp [minusPoint, TomitaTakesaki.modularConjugationJ]

omit [CompleteSpace E] in
theorem modular_j_maps_minusSheet_to_plusSheet
    {u : H₂} (hu : u ∈ minusSheet (E := E)) :
    modular_j (E := E) u ∈ plusSheet (E := E) := by
  simpa [TomitaTakesaki.modularConjugationJ_eq_modular_j] using
    modularConjugationJ_maps_minusSheet_to_plusSheet (E := E) hu

omit [CompleteSpace E] in
theorem modularComplexI_maps_plusSheet_to_minusSheet
    {u : H₂} (hu : u ∈ plusSheet (E := E)) :
    InfoGeometry.Krein.clockAxis (E := E) u ∈ minusSheet (E := E) := by
  rw [eq_plusPoint_of_mem_plusSheet (E := E) hu]
  rw [mem_minusSheet_iff_fst_eq_zero]
  simp [plusPoint]

omit [CompleteSpace E] in
theorem complex_i_maps_plusSheet_to_minusSheet
    {u : H₂} (hu : u ∈ plusSheet (E := E)) :
    complex_i (E := E) u ∈ minusSheet (E := E) := by
  simpa [TomitaTakesaki.clockAxis_eq_complex_i] using
    modularComplexI_maps_plusSheet_to_minusSheet (E := E) hu

omit [CompleteSpace E] in
theorem modularComplexI_maps_minusSheet_to_plusSheet
    {u : H₂} (hu : u ∈ minusSheet (E := E)) :
    InfoGeometry.Krein.clockAxis (E := E) u ∈ plusSheet (E := E) := by
  rw [eq_minusPoint_of_mem_minusSheet (E := E) hu]
  rw [mem_plusSheet_iff_snd_eq_zero]
  simp [minusPoint]

omit [CompleteSpace E] in
theorem complex_i_maps_minusSheet_to_plusSheet
    {u : H₂} (hu : u ∈ minusSheet (E := E)) :
    complex_i (E := E) u ∈ plusSheet (E := E) := by
  simpa [TomitaTakesaki.clockAxis_eq_complex_i] using
    modularComplexI_maps_minusSheet_to_plusSheet (E := E) hu

section ModularFlow

/--
Derivative of the modular transport flow at time `t`.
This is the infinitesimal generator identity for the flow generated by
`A = hMod ∘ Kop`, proved via Mathlib's analytic exponential API.
-/
theorem modularTransportFlow_deriv (hMod : EndH) (t : ℝ) :
    HasDerivAt (fun s => modularTransportFlow hMod s)
    (modularTransportGenerator hMod * modularTransportFlow hMod t) t := by
  simpa [modularTransportFlow] using
    (hasDerivAt_exp_smul_const' (x := modularTransportGenerator hMod) (t := t))

omit [CompleteSpace E] in
/--
State projector commutation with the modular transport flow.
If the projector commutes with the generator, it commutes with the whole flow.
-/
theorem spectralPlusProj_commutes_modularTransportFlow (hMod : EndH) (t : ℝ)
    (h_comm : Commute (spectralPlusProj (E := E)) (modularTransportGenerator hMod)) :
    Commute (spectralPlusProj (E := E)) (modularTransportFlow hMod t) := by
  simpa [modularTransportFlow] using (h_comm.smul_right t).exp_right

omit [CompleteSpace E] in
/--
Projector transport equality as a corollary of commutation.
-/
theorem spectralPlusProj_comp_modularTransportFlow (hMod : EndH) (t : ℝ)
    (h_comm : Commute (spectralPlusProj (E := E)) (modularTransportGenerator hMod)) :
    (spectralPlusProj (E := E)).comp (modularTransportFlow hMod t) =
      (modularTransportFlow hMod t).comp (spectralPlusProj (E := E)) :=
  (spectralPlusProj_commutes_modularTransportFlow hMod t h_comm).eq

end ModularFlow

end Sheets

end Basic

end BogoliubovProjectorTransport
