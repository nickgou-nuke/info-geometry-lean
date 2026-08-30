import InfoGeometry.Lie.CanonicalZornG2UnificationBridge
import InfoGeometry.Lie.CanonicalZornDerivationRealAutBridge

/-!
# The split `G₂` real-form capstone

This file collects the independently proved pieces of the real split form:
the explicit fourteen-parameter derivation model, the canonical derivation Lie
subalgebra, its Cartan/root datum, and the integrated automorphism flow.

It deliberately does not identify this data with a global Lie group without a
separate manifold/group-classification development.
-/

noncomputable section

namespace InfoGeometry.Lie.SplitG2RealFormCapstone

open InfoGeometry.Lie.CanonicalZornDerivationDimension
open InfoGeometry.Lie.CanonicalZornDerivation
open InfoGeometry.Lie.CanonicalZornDerivationExponential
open InfoGeometry.Lie.CanonicalZornG2UnificationBridge
open InfoGeometry.Lie.CanonicalZornDerivationRealAutBridge
open InfoGeometry.Lie.CanonicalZornRootSystemComparison
open InfoGeometry.Canonical

/-! The coordinate model really parametrizes the canonical derivation Lie algebra. -/

theorem parameter_model_is_fourteen_dimensional :
    Module.finrank ℝ
        InfoGeometry.Lie.CanonicalZornDerivation.canonicalZornDerivations = 14 :=
  finrank_canonicalZornDerivations

theorem parameter_model_is_linear_equivalent_to_derivations :
    ∃ e : Params ≃ₗ[ℝ]
        InfoGeometry.Lie.CanonicalZornDerivation.canonicalZornDerivations,
      e = canonicalParameterLinearEquiv := by
  exact ⟨canonicalParameterLinearEquiv, rfl⟩

/-! The Cartan/root data has the split `G₂` rank and twelve-root pattern. -/

theorem split_g2_cartan_root_data :
    Fintype.card RootIndex = 12 ∧
      Function.Bijective nativeRootIndex := by
  exact ⟨root_system_card_12,
    ⟨nativeRootIndex_injective, nativeRootIndex_surjective⟩⟩

/-! Every canonical derivation integrates to the native real automorphism group. -/

theorem split_g2_derivation_exponential_is_real_automorphism
    (D : canonicalZornDerivations) (t : ℝ) :
    ∃ F : RealSplitOctonionAut,
      (F : SplitOctonionAutCandidate ℝ) = zornFlowLinearEquiv D.1 t := by
  exact ⟨zornFlowRealAut D t, zornFlowRealAut_coe D t⟩

theorem split_g2_flow_is_one_parameter_subgroup
    (D : canonicalZornDerivations) (s t : ℝ) :
    zornFlowRealAut D (s + t) =
      zornFlowRealAut D s * zornFlowRealAut D t :=
  zornFlowRealAut_add D s t

/-! A single theorem exposing the complete real-form package proved here. -/

theorem split_g2_real_form_capstone :
      Module.finrank ℝ
        InfoGeometry.Lie.CanonicalZornDerivation.canonicalZornDerivations = 14 ∧
      Fintype.card RootIndex = 12 ∧
      Function.Bijective nativeRootIndex := by
  exact ⟨parameter_model_is_fourteen_dimensional,
    root_system_card_12,
    ⟨nativeRootIndex_injective, nativeRootIndex_surjective⟩⟩

end InfoGeometry.Lie.SplitG2RealFormCapstone
