import Mathlib
import proofs.SplitOctonionDerivationSpace
import proofs.SplitOctonionTrialityCore
import proofs.SplitOctonionDerivationSkew44

open SplitOctonion
open SplitOctonionNorm44
open SplitOctonionTrialityCore
open OctDerivation

namespace SplitOctonionTrialityCore

noncomputable def derivationToSO44 (D : OctDerivation) : SO44 :=
  ⟨D.toLinearMap, by
    intro x y
    change splitBilinear (D.toLinearMap x) y = - splitBilinear x (D.toLinearMap y)
    linarith [OctDerivation.derivation_is_skew_adjoint D x y]⟩

lemma derivation_is_triality (D : OctDerivation) :
  IsTriality (derivationToSO44 D, derivationToSO44 D, derivationToSO44 D) := by
  intro x y
  exact D.leibniz' x y

noncomputable def derivationTrialityHom : OctDerivation →ₗ⁅ℝ⁆ trialityLieSubalgebra where
  toFun D := ⟨(derivationToSO44 D, derivationToSO44 D, derivationToSO44 D), derivation_is_triality D⟩
  map_add' := by intro D1 D2; ext <;> rfl
  map_smul' := by intro c D; ext <;> rfl
  map_lie' := by intro D1 D2; ext <;> rfl

end SplitOctonionTrialityCore
