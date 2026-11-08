/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Krein.SplitOctonionDoubleKreinSheetBridge
import InfoGeometry.Canonical.SuperchargeCARCCRBridge
import InfoGeometry.Canonical.RealifiedDoubledKreinHodgeBridge

/-! # Concrete doubled-Krein tetraktys sign change

The existing creation and annihilation maps yield an invertible sheet swap.
Their commutator is the Krein grading, and the swap reverses that grading.
-/

noncomputable section

namespace InfoGeometry.Krein.DoubledTetraktysSheetSign

open InfoGeometry.Krein
open InfoGeometry.Canonical.BogoliubovFockSuper
open InfoGeometry.Canonical.SuperchargeCARCCRBridge
open InfoGeometry.Canonical.MajoranaPHSZeroMode
open InfoGeometry.Krein.MajoranaSheetConnectors
open InfoGeometry.Krein.SplitQuadraticSheets
open InfoGeometry.Canonical.RealifiedDoubledKreinHodgeBridge

variable {E : Type 0} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The concrete tetraktys odd sum is the doubled-space sheet swap. -/
theorem concretePhi_eq_swap :
    concreteCARCreation (E := E) + concreteCARAnnihilation (E := E) = modular_j :=
  concrete_majorana_swap_eq_modular_j

/-- The concrete tetraktys commutator is the doubled-space grading. -/
theorem concreteSigma_eq_grading :
    CCRBracket (E := E) (concreteCARCreation (E := E))
      (concreteCARAnnihilation (E := E)) = spectral_epsilon :=
  concrete_car_creation_annihilation_ccrBracket_eq_spectral_epsilon

/-- The swap reverses the grading as an actual operator on doubled space. -/
theorem concretePhi_Sigma_Phi :
    (concreteCARCreation (E := E) + concreteCARAnnihilation (E := E)).comp
      ((CCRBracket (E := E) (concreteCARCreation (E := E))
        (concreteCARAnnihilation (E := E))).comp
        (concreteCARCreation (E := E) + concreteCARAnnihilation (E := E))) =
      -(CCRBracket (E := E) (concreteCARCreation (E := E))
        (concreteCARAnnihilation (E := E))) := by
  rw [concretePhi_eq_swap, concreteSigma_eq_grading]
  apply ContinuousLinearMap.ext
  intro u
  apply DoubledSpace.ext <;>
    simp [ContinuousLinearMap.comp_apply, modular_j, spectral_epsilon]

/-- The same swap exchanges the concrete sheets in both directions. -/
theorem concretePhi_exchanges_sheets (x : E) :
    (concreteCARCreation (E := E) + concreteCARAnnihilation (E := E)) (plusPoint x) =
      minusPoint x ∧
    (concreteCARCreation (E := E) + concreteCARAnnihilation (E := E)) (minusPoint x) =
      plusPoint x :=
  ⟨majorana_swap_maps_plusPoint_to_minusPoint x, majorana_swap_maps_minusPoint_to_plusPoint x⟩

/-- On the whole doubled carrier, the actual sheet swap reverses the
indefinite Krein form in both arguments. -/
theorem concretePhi_reverses_kreinForm (u v : DoubledSpace E) :
    kreinForm E
      ((concreteCARCreation (E := E) + concreteCARAnnihilation (E := E)) u)
      ((concreteCARCreation (E := E) + concreteCARAnnihilation (E := E)) v) =
      -kreinForm E u v := by
  rw [concretePhi_eq_swap]
  have hu : to_doubled (WithLp.fst u) (WithLp.snd u) = u := by
    apply DoubledSpace.ext <;> simp [to_doubled]
  have hv : to_doubled (WithLp.fst v) (WithLp.snd v) = v := by
    apply DoubledSpace.ext <;> simp [to_doubled]
  rw [← hu, ← hv]
  simp [modular_j, kreinForm_apply, to_doubled]

end InfoGeometry.Krein.DoubledTetraktysSheetSign

end
