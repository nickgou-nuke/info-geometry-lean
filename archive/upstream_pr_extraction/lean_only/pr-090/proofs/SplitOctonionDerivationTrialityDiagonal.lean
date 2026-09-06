import Mathlib
import proofs.SplitOctonionSkewDerivation
import proofs.SplitOctonionTrialityCore

set_option synthInstance.maxHeartbeats 100000

open SplitOctonion
open SplitOctonionNorm44
open OctDerivation
open SkewDerivation
open SplitOctonionTrialityCore

namespace SplitOctonionDerivationTriality

noncomputable def skewDerivationToSO44 (D : SkewDerivation) : SO44 :=
  ⟨D.toOctDerivation.toLinearMap, by
    intro x y
    change splitBilinear (D.toOctDerivation.toLinearMap x) y = - splitBilinear x (D.toOctDerivation.toLinearMap y)
    have h := D.skew' x y
    exact eq_neg_of_add_eq_zero_left h⟩

lemma skewDerivationToSO44_add (D1 D2 : SkewDerivation) :
  skewDerivationToSO44 (D1 + D2) = skewDerivationToSO44 D1 + skewDerivationToSO44 D2 := by
  apply SetCoe.ext
  rfl

lemma skewDerivationToSO44_smul (c : ℝ) (D : SkewDerivation) :
  skewDerivationToSO44 (c • D) = c • skewDerivationToSO44 D := by
  apply SetCoe.ext
  rfl

lemma skewDerivationToSO44_bracket (D1 D2 : SkewDerivation) :
  skewDerivationToSO44 ⁅D1, D2⁆ = ⁅skewDerivationToSO44 D1, skewDerivationToSO44 D2⁆ := by
  apply SetCoe.ext
  rfl

noncomputable def skewDerivationToSO44LieHom : SkewDerivation →ₗ⁅ℝ⁆ SO44 where
  toFun := skewDerivationToSO44
  map_add' := skewDerivationToSO44_add
  map_smul' := skewDerivationToSO44_smul
  map_lie' := by intros; apply skewDerivationToSO44_bracket

lemma skewDerivationToSO44_injective : Function.Injective skewDerivationToSO44LieHom := by
  intro D1 D2 h
  apply ext_skew
  apply ext_lin
  change skewDerivationToSO44 D1 = skewDerivationToSO44 D2 at h
  have h_ext : (skewDerivationToSO44 D1).val = (skewDerivationToSO44 D2).val := congrArg Subtype.val h
  exact h_ext

noncomputable def derivationTrialityAmbient (D : SkewDerivation) : TrialityAmbient :=
  (skewDerivationToSO44 D, skewDerivationToSO44 D, skewDerivationToSO44 D)

lemma derivationTriality_isTriality (D : SkewDerivation) :
  IsTriality (derivationTrialityAmbient D) := by
  intro x y
  change D.toOctDerivation.toLinearMap (x * y) = D.toOctDerivation.toLinearMap x * y + x * D.toOctDerivation.toLinearMap y
  exact D.toOctDerivation.leibniz' x y

noncomputable def skewDerivationToTriality (D : SkewDerivation) : trialityLieSubalgebra :=
  ⟨derivationTrialityAmbient D, derivationTriality_isTriality D⟩

lemma skewDerivationToTriality_add (D1 D2 : SkewDerivation) :
  skewDerivationToTriality (D1 + D2) = skewDerivationToTriality D1 + skewDerivationToTriality D2 := by
  apply SetCoe.ext
  rfl

lemma skewDerivationToTriality_smul (c : ℝ) (D : SkewDerivation) :
  skewDerivationToTriality (c • D) = c • skewDerivationToTriality D := by
  apply SetCoe.ext
  rfl

lemma skewDerivationToTriality_bracket (D1 D2 : SkewDerivation) :
  skewDerivationToTriality ⁅D1, D2⁆ = ⁅skewDerivationToTriality D1, skewDerivationToTriality D2⁆ := by
  apply SetCoe.ext
  rfl

noncomputable def skewDerivationToTrialityLieHom : SkewDerivation →ₗ⁅ℝ⁆ trialityLieSubalgebra where
  toFun := skewDerivationToTriality
  map_add' := skewDerivationToTriality_add
  map_smul' := skewDerivationToTriality_smul
  map_lie' := by intros; apply skewDerivationToTriality_bracket

lemma skewDerivationToTriality_injective : Function.Injective skewDerivationToTrialityLieHom := by
  intro D1 D2 h
  change skewDerivationToTriality D1 = skewDerivationToTriality D2 at h
  have h_val : (skewDerivationToTriality D1).val = (skewDerivationToTriality D2).val := congrArg Subtype.val h
  have h_fst : (skewDerivationToTriality D1).val.1 = (skewDerivationToTriality D2).val.1 := congrArg Prod.fst h_val
  apply skewDerivationToSO44_injective
  change skewDerivationToSO44LieHom D1 = skewDerivationToSO44LieHom D2
  exact h_fst

/-- The converse: the diagonal elements of the triality algebra are exactly the SkewDerivations. -/
theorem diagonal_isTriality_iff_leibniz (D : SO44) :
  IsTriality (D, D, D) ↔ ∀ x y, D.val (x * y) = D.val x * y + x * D.val y := by
  apply Iff.intro
  · intro h x y
    exact h x y
  · intro h x y
    exact h x y

end SplitOctonionDerivationTriality
