/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.NativeTitsE8Carrier
import InfoGeometry.Canonical.SplitFreudenthalTitsE8Carrier
import InfoGeometry.Algebra.H3ZornF4DimensionClosure
import InfoGeometry.Algebra.MagicSquareTitsBracket
import InfoGeometry.Algebra.SplitE8RootSystem
import InfoGeometry.Algebra.SplitE8Simplicity
import InfoGeometry.Lie.CanonicalZornIsKilling
import InfoGeometry.Lie.SplitG2RealFormCapstone
import InfoGeometry.Lie.SplitOctonionStandardDerivation
import InfoGeometry.Lie.CanonicalZornRootSystemComparison

/-!
# E2E Tests for `E₈(8)` Magic Square Lie Algebra, Root System & Simplicity (R3)

Covers all `[IMMEDIATE]` and `[M6-CONTRACT]` Tier 1 and Tier 2 requirements for Features 14–15:
- Feature 14: Unconditional 248D `NativeTitsCarrier` (`14 + 182 + 52 = 248`),
  `NativeTitsCarrier ≃ₗ[ℝ] SplitTitsE8Carrier`, 248D `SplitE8Lie` (`LieRing`, `LieAlgebra ℝ`,
  verified Jacobi across all 27 cells), `G₂(2)` and `F₄(4)` Lie embeddings, mixed-sector bracket
  constants `(1/3, -2, 1)`, concrete nonzero mixed brackets, antisymmetry, mutual `G₂`/`F₄`
  commutation, and traceless boundary checks (`1 ∉ ker Tr`)
- Feature 15: `G₂(2)` `IsKilling` / `HasTrivialRadical` / `RootPairing`, unconditional 52D
  `F₄(4)`, `8D` split Cartan `splitE8Cartan` (`IsCartanSubalgebra`, `IsLieAbelian`,
  `IsTriangularizable`), `240` roots (`e8RootEquiv`, `card_splitE8Cartan_root = 240`),
  `splitE8RootSystem` (`IsRootSystem`, `IsCrystallographic`, `IsReduced`, `IsIrreducible`,
  `CartanMatrix.E 8`), `IsSl2Triple`, `IsKilling ℝ`, `IsSimple ℝ`, `IsSemisimple ℝ`,
  non-abelian/no-abelian-ideal dichotomy (`G₂` and `F₄` not ideals), and 1D root spaces
-/

set_option autoImplicit false

namespace InfoGeometry.Tests.E8MagicSquare

open InfoGeometry.Algebra
open InfoGeometry.Canonical.NativeTitsE8Carrier
open InfoGeometry.Canonical.SplitFreudenthalTitsE8Carrier
open InfoGeometry.Lie.CanonicalZornDerivation
open InfoGeometry.Lie.CanonicalZornDerivationDimension
open InfoGeometry.Lie.SplitG2RealFormCapstone
open InfoGeometry.Lie.SplitOctonionStandardDerivation
open InfoGeometry.Lie.CanonicalZornRootSystemComparison

attribute [local instance 100] LieRing.ofAssociativeRing

/-! ## Feature 14: 248D `𝔈₈(8)` Magic Square Carrier & `G₂(2)` Summand (Tier 1 & Tier 2) -/

theorem native_tits_e8_carrier_unconditional_248 :
    Module.finrank ℝ NativeTitsCarrier = 248 :=
  finrank_nativeTitsCarrier_of_f4 finrank_H3ZornF4Derivations

theorem native_tits_carrier_sector_dimensions :
    Module.finrank ℝ splitOctonionTraceZero = 7 ∧
    Module.finrank ℝ h3TraceZero = 26 ∧
    Module.finrank ℝ MixedCarrier = 182 ∧
    Module.finrank ℝ G2DerivationCarrier = 14 ∧
    Module.finrank ℝ (G2DerivationCarrier × MixedCarrier) = 196 :=
  ⟨finrank_splitOctonionTraceZero, finrank_h3TraceZero,
    finrank_mixedCarrier, finrank_g2DerivationCarrier, finrank_g2_plus_mixed⟩

theorem split_tits_e8_carrier_248_and_packet :
    Module.finrank ℝ SplitTitsE8Carrier = 248 ∧
    Module.finrank ℝ G2CertifiedCarrier = 14 ∧
    Module.finrank ℝ ZornTraceless = 7 ∧
    Module.finrank ℝ AlbertTraceless = 26 ∧
    Module.finrank ℝ MixedCoordinateCarrier = 182 ∧
    Module.finrank ℝ F4CertifiedCarrier = 52 :=
  ⟨splitTitsE8Carrier_finrank,
    split_tits_dimension_packet.1,
    split_tits_dimension_packet.2.1,
    split_tits_dimension_packet.2.2.1,
    split_tits_dimension_packet.2.2.2.1,
    split_tits_dimension_packet.2.2.2.2⟩

theorem g2_standard_derivations_span_top_and_columns :
    standardDerivationSpan = ⊤ ∧
    Module.finrank ℝ canonicalZornDerivations = 14 ∧
    canonicalParameterLinearEquiv.symm
      (canonicalStandardDerivationOfCanonical canonicalE11 (canonicalU 0)) =
        parameterUnit 10 (-1) ∧
    canonicalParameterLinearEquiv.symm
      (canonicalStandardDerivationOfCanonical canonicalE11 (canonicalU 1)) =
        parameterUnit 9 :=
  ⟨standardDerivations_span_top, canonical_derivation_finrank,
    standardColumn_E11_U0, standardColumn_E11_U1⟩

theorem g2_real_aut_flow_and_capstone (D : canonicalZornDerivations) (s t : ℝ) :
    Module.finrank ℝ canonicalZornDerivations = 14 ∧
    (∃ e : Params ≃ₗ[ℝ] canonicalZornDerivations, e = canonicalParameterLinearEquiv) ∧
    (∃ F : InfoGeometry.Canonical.RealSplitOctonionAut,
      (F : InfoGeometry.Canonical.SplitOctonionAutCandidate ℝ) =
        InfoGeometry.Lie.CanonicalZornDerivationExponential.zornFlowLinearEquiv D.1 t) ∧
    InfoGeometry.Lie.CanonicalZornDerivationRealAutBridge.zornFlowRealAut D (s + t) =
      InfoGeometry.Lie.CanonicalZornDerivationRealAutBridge.zornFlowRealAut D s *
        InfoGeometry.Lie.CanonicalZornDerivationRealAutBridge.zornFlowRealAut D t :=
  ⟨parameter_model_is_fourteen_dimensional,
    parameter_model_is_linear_equivalent_to_derivations,
    split_g2_derivation_exponential_is_real_automorphism D t,
    split_g2_flow_is_one_parameter_subgroup D s t⟩

theorem traceless_octonion_excludes_one :
    ZornVectorMatrix.one (R := ℝ) ∉ splitOctonionTraceZero ∧
    Module.finrank ℝ splitOctonionTraceZero = 7 := by
  refine ⟨?_, finrank_splitOctonionTraceZero⟩
  intro h1
  change InfoGeometry.Canonical.NativeTitsE8Carrier.zornTraceLinear
    (ZornVectorMatrix.one (R := ℝ)) = 0 at h1
  have hval : InfoGeometry.Canonical.NativeTitsE8Carrier.zornTraceLinear
      (ZornVectorMatrix.one (R := ℝ)) = 2 := by
    change ZornVectorMatrix.trace (ZornVectorMatrix.one (R := ℝ)) = 2
    simp [ZornVectorMatrix.trace, ZornVectorMatrix.one]
    norm_num
  rw [hval] at h1
  norm_num at h1

theorem traceless_albert_excludes_one :
    (1 : H3Zorn ℝ) ∉ h3TraceZero ∧
    Module.finrank ℝ h3TraceZero = 26 := by
  refine ⟨?_, finrank_h3TraceZero⟩
  intro h1
  change h3TraceLinear (1 : H3Zorn ℝ) = 0 at h1
  have hval : h3TraceLinear (1 : H3Zorn ℝ) = 3 := by
    change H3Zorn.linearTrace (1 : H3Zorn ℝ) = 3
    simp [H3Zorn.linearTrace, H3Zorn.one_readback]
    norm_num
  rw [hval] at h1
  norm_num at h1

theorem g2_standard_derivation_self_zero_and_skew
    (x y : InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge.CanonicalZorn) :
    directCanonicalStanDerMap x x = 0 ∧
    directCanonicalStanDerMap y x = -directCanonicalStanDerMap x y := by
  have hstan_self : ∀ u : InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge.CanonicalZorn,
      directCanonicalStanDerMap u u = 0 := by
    intro u
    rw [← canonicalStandardEnd_transport_eq_direct]
    apply LinearMap.ext
    intro z
    change InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge.kingdonCanonicalLinearEquiv
        ((kingdonStandardDerivation
          (InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge.kingdonCanonicalLinearEquiv.symm u)
          (InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge.kingdonCanonicalLinearEquiv.symm u))
          (InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge.kingdonCanonicalLinearEquiv.symm z)) = 0
    change InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge.kingdonCanonicalLinearEquiv
        (stanDerMap (R := ℝ)
          (InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge.kingdonCanonicalLinearEquiv.symm u)
          (InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge.kingdonCanonicalLinearEquiv.symm u)
          (InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge.kingdonCanonicalLinearEquiv.symm z)) = 0
    rw [stanDerMap_apply_normal_form (R := ℝ)
      (InfoGeometry.Algebra.Kingdon.Algebra.alternative_left
        InfoGeometry.Canonical.ZornVectorMatrixExplicit.KingdonSplitOctonion.formedBilin)
      (InfoGeometry.Algebra.Kingdon.Algebra.alternative_right
        InfoGeometry.Canonical.ZornVectorMatrixExplicit.KingdonSplitOctonion.formedBilin)]
    have hassoc : associator
        (InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge.kingdonCanonicalLinearEquiv.symm u)
        (InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge.kingdonCanonicalLinearEquiv.symm u)
        (InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge.kingdonCanonicalLinearEquiv.symm z) = 0 := by
      rw [associator_apply]
      exact sub_eq_zero.mpr (InfoGeometry.Algebra.Kingdon.Algebra.alternative_left
        InfoGeometry.Canonical.ZornVectorMatrixExplicit.KingdonSplitOctonion.formedBilin _ _)
    rw [sub_self, zero_mul, mul_zero, sub_self, hassoc]
    simp
  refine ⟨hstan_self x, ?_⟩
  have hlin : directCanonicalStanDerMap (x + y) (x + y) =
      directCanonicalStanDerMap x x + directCanonicalStanDerMap x y +
        directCanonicalStanDerMap y x + directCanonicalStanDerMap y y := by
    rw [← canonicalStandardEnd_transport_eq_direct, ← canonicalStandardEnd_transport_eq_direct,
      ← canonicalStandardEnd_transport_eq_direct, ← canonicalStandardEnd_transport_eq_direct,
      ← canonicalStandardEnd_transport_eq_direct]
    apply LinearMap.ext
    intro z
    change InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge.kingdonCanonicalLinearEquiv
        (stanDerMap (R := ℝ)
          (InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge.kingdonCanonicalLinearEquiv.symm (x + y))
          (InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge.kingdonCanonicalLinearEquiv.symm (x + y))
          (InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge.kingdonCanonicalLinearEquiv.symm z)) =
      InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge.kingdonCanonicalLinearEquiv
        (stanDerMap (R := ℝ)
          (InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge.kingdonCanonicalLinearEquiv.symm x)
          (InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge.kingdonCanonicalLinearEquiv.symm x)
          (InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge.kingdonCanonicalLinearEquiv.symm z)) +
      InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge.kingdonCanonicalLinearEquiv
        (stanDerMap (R := ℝ)
          (InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge.kingdonCanonicalLinearEquiv.symm x)
          (InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge.kingdonCanonicalLinearEquiv.symm y)
          (InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge.kingdonCanonicalLinearEquiv.symm z)) +
      InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge.kingdonCanonicalLinearEquiv
        (stanDerMap (R := ℝ)
          (InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge.kingdonCanonicalLinearEquiv.symm y)
          (InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge.kingdonCanonicalLinearEquiv.symm x)
          (InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge.kingdonCanonicalLinearEquiv.symm z)) +
      InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge.kingdonCanonicalLinearEquiv
        (stanDerMap (R := ℝ)
          (InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge.kingdonCanonicalLinearEquiv.symm y)
          (InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge.kingdonCanonicalLinearEquiv.symm y)
          (InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge.kingdonCanonicalLinearEquiv.symm z))
    rw [← map_add, ← map_add, ← map_add]
    congr 1
    have hstan_def :
        ∀ a b c : InfoGeometry.Canonical.ZornVectorMatrixExplicit.KingdonSplitOctonion.AbstractKingdon,
        stanDerMap (R := ℝ) a b c =
          (a * (b * c) - b * (a * c)) + (a * (c * b) - (a * c) * b) +
            ((c * b) * a - (c * a) * b) := fun _ _ _ => rfl
    rw [map_add]
    simp only [hstan_def, add_mul, mul_add]
    abel
  have hxy := hstan_self (x + y)
  rw [hlin, hstan_self x, hstan_self y, zero_add, add_zero] at hxy
  exact eq_neg_of_add_eq_zero_right hxy

/-! ## Feature 15: `G₂(2)` Killing/Root System, `F₄(4)` 52D, & Cartan Ranks (Tier 1 & Tier 2) -/

theorem g2_isKilling_and_hasTrivialRadical :
    LieAlgebra.IsKilling ℝ InfoGeometry.Lie.CanonicalZornIsKilling.Der ∧
    LieAlgebra.HasTrivialRadical ℝ InfoGeometry.Lie.CanonicalZornIsKilling.Der :=
  ⟨InfoGeometry.Lie.CanonicalZornIsKilling.der_isKilling,
    InfoGeometry.Lie.CanonicalZornIsKilling.der_hasTrivialRadical⟩

noncomputable def g2_root_pairing :
    RootPairing
      (InfoGeometry.Lie.CanonicalZornIsKilling.Cartan :
        LieSubalgebra ℝ InfoGeometry.Lie.CanonicalZornIsKilling.Der).root
      ℝ (Module.Dual ℝ InfoGeometry.Lie.CanonicalZornIsKilling.Cartan)
      InfoGeometry.Lie.CanonicalZornIsKilling.Cartan :=
  InfoGeometry.Lie.CanonicalZornIsKilling.canonicalZornRootSystem

theorem g2_root_count_12_and_bijective :
    Fintype.card RootIndex = 12 ∧ Function.Bijective nativeRootIndex :=
  split_g2_cartan_root_data

theorem f4_unconditional_52d_and_basis_span :
    Module.finrank ℝ H3ZornF4Derivations = 52 ∧
    f4BasisSpan = H3ZornF4Derivations.toSubmodule :=
  ⟨finrank_H3ZornF4Derivations, f4BasisSpan_eq_H3ZornF4Derivations⟩

theorem g2_root_chain_and_highest_weight :
    (nativeRootWeightMathlib ⟨9, by decide, by decide⟩).toFun =
        simpleWeightOnCartan 0 + simpleWeightOnCartan 1 ∧
      (nativeRootWeightMathlib ⟨8, by decide, by decide⟩).toFun =
        2 • simpleWeightOnCartan 0 + simpleWeightOnCartan 1 ∧
      (nativeRootWeightMathlib ⟨11, by decide, by decide⟩).toFun =
        3 • simpleWeightOnCartan 0 + simpleWeightOnCartan 1 ∧
      (nativeRootWeightMathlib ⟨12, by decide, by decide⟩).toFun =
        3 • simpleWeightOnCartan 0 + 2 • simpleWeightOnCartan 1 ∧
      LieAlgebra.rootSpace InfoGeometry.Lie.CanonicalZornIsKilling.Cartan
        (3 • InfoGeometry.Lie.CanonicalZornCartanRootSystem.nativeRootWeight
            nativeShortSimpleIndex +
          InfoGeometry.Lie.CanonicalZornCartanRootSystem.nativeRootWeight
            nativeLongSimpleIndex) ≠ ⊥ ∧
      LieAlgebra.rootSpace InfoGeometry.Lie.CanonicalZornIsKilling.Cartan
        (4 • InfoGeometry.Lie.CanonicalZornCartanRootSystem.nativeRootWeight
            nativeShortSimpleIndex +
          InfoGeometry.Lie.CanonicalZornCartanRootSystem.nativeRootWeight
            nativeLongSimpleIndex) = ⊥ :=
  ⟨nativePositiveRootWeight_chain.1, nativePositiveRootWeight_chain.2.1,
    nativePositiveRootWeight_chain.2.2, native_highest_root_weight,
    native_root_string_top_nontrivial, native_root_string_next_vanishing⟩

theorem g2_and_f4_cartan_ranks_below_e8_rank :
    Module.finrank ℝ InfoGeometry.Lie.CanonicalZornIsKilling.Cartan = 2 ∧
    Module.finrank ℝ InfoGeometry.Lie.CanonicalZornIsKilling.Cartan + 4 < 8 := by
  have h2 : Module.finrank ℝ InfoGeometry.Lie.CanonicalZornIsKilling.Cartan = 2 :=
    InfoGeometry.Lie.SplitOctonionAxialCartanErlangen.axialCartanLieSubalgebra_finrank
  refine ⟨h2, ?_⟩
  rw [h2]
  norm_num

theorem g2_nonabelian_witness :
    ∃ D E : canonicalZornDerivations, ⁅D, E⁆ ≠ 0 := by
  by_contra h
  push Not at h
  have hAb : IsLieAbelian (⊤ : LieIdeal ℝ InfoGeometry.Lie.CanonicalZornIsKilling.Der) := by
    refine ⟨fun x y => ?_⟩
    exact Subtype.ext (h x.1 y.1)
  have hbot : (⊤ : LieIdeal ℝ InfoGeometry.Lie.CanonicalZornIsKilling.Der) = ⊥ :=
    (LieAlgebra.hasTrivialRadical_iff_no_abelian_ideals ℝ
      InfoGeometry.Lie.CanonicalZornIsKilling.Der).mp
      InfoGeometry.Lie.CanonicalZornIsKilling.der_hasTrivialRadical ⊤ hAb
  have hne : canonicalStandardDerivationOfCanonical canonicalE11 (canonicalU 0) ≠ 0 := by
    intro hz
    have hc := congrArg canonicalParameterLinearEquiv.symm hz
    rw [standardColumn_E11_U0, map_zero] at hc
    have h10 := congrFun hc 10
    simp [parameterUnit] at h10
  have hmem : canonicalStandardDerivationOfCanonical canonicalE11 (canonicalU 0) ∈
      (⊥ : LieIdeal ℝ InfoGeometry.Lie.CanonicalZornIsKilling.Der) := by
    rw [← hbot]
    trivial
  exact hne ((LieSubmodule.mem_bot _).mp hmem)

section M6MagicSquareAndRootSystem

open InfoGeometry.Algebra.MagicSquareTitsBracket
open InfoGeometry.Exceptional.CFSGPort.Chevalley

/-! ## `[M6-CONTRACT]` Feature 14: 248D `𝔈₈(8)` Magic Square Lie Algebra (Tier 1 & Tier 2) -/

noncomputable def e8_native_to_split_equiv :
    NativeTitsCarrier ≃ₗ[ℝ] SplitTitsE8Carrier :=
  nativeToSplitTitsE8Equiv

noncomputable def e8_split_lie_to_native_equiv :
    SplitE8Lie ≃ₗ[ℝ] NativeTitsCarrier :=
  splitE8LinearEquiv

theorem e8_native_tits_unconditional_248_and_packet :
    Module.finrank ℝ NativeTitsCarrier = 248 ∧
    Module.finrank ℝ SplitTitsE8Carrier = 248 ∧
    Module.finrank ℝ splitOctonionTraceZero = 7 ∧
    Module.finrank ℝ h3TraceZero = 26 ∧
    Module.finrank ℝ MixedCarrier = 182 ∧
    Module.finrank ℝ G2DerivationCarrier = 14 ∧
    Module.finrank ℝ F4DerivationCarrier = 52 :=
  ⟨finrank_nativeTitsCarrier, splitTitsE8Carrier_finrank,
    native_tits_carrier_packet.1, native_tits_carrier_packet.2.1,
    native_tits_carrier_packet.2.2.1, native_tits_carrier_packet.2.2.2.1,
    native_tits_carrier_packet.2.2.2.2.1⟩

theorem e8_split_lie_finrank_248_and_jacobi
    (r : ℝ) (X Y Z : SplitE8Lie) :
    Module.Finite ℝ SplitE8Lie ∧
    Module.finrank ℝ SplitE8Lie = 248 ∧
    magicBracketLM X (magicBracketLM Y Z) =
      magicBracketLM (magicBracketLM X Y) Z + magicBracketLM Y (magicBracketLM X Z) ∧
    ⁅X, ⁅Y, Z⁆⁆ = ⁅⁅X, Y⁆, Z⁆ + ⁅Y, ⁅X, Z⁆⁆ ∧
    ⁅X, r • Y⁆ = r • ⁅X, Y⁆ :=
  ⟨inferInstance, finrank_splitE8Lie,
    magicBracketLM_leibniz X Y Z, leibniz_lie X Y Z, lie_smul r X Y⟩

theorem e8_g2_f4_mixed_embeddings_and_grade_decomp
    (D₁ D₂ : G2DerivationCarrier) (E₁ E₂ : F4DerivationCarrier)
    (a : splitOctonionTraceZero) (x : h3TraceZero) (X : SplitE8Lie) :
    Function.Injective embedG2 ∧
    Function.Injective embedF4 ∧
    embedG2 ⁅D₁, D₂⁆ = ⁅embedG2 D₁, embedG2 D₂⁆ ∧
    embedF4 ⁅E₁, E₂⁆ = ⁅embedF4 E₁, embedF4 E₂⁆ ∧
    ⁅embedG2 D₁, embedTensor a x⁆ = embedTensor (g2Act D₁ a) x ∧
    ⁅embedF4 E₁, embedTensor a x⁆ = embedTensor a (f4Act E₁ x) ∧
    (∑ i : SplitE8Grade, gradeProj i X) = X ∧
    embedG2 (projG2 X) + embedMixed (projMixed X) + embedF4 (projF4 X) = X := by
  have hinjG2 : Function.Injective embedG2 := fun u v h => congrArg projG2 h
  have hinjF4 : Function.Injective embedF4 := fun u v h => congrArg projF4 h
  have hsum : embedG2 (projG2 X) + embedMixed (projMixed X) + embedF4 (projF4 X) = X := by
    apply SplitE8Lie.ext <;> simp [embedG2_apply, embedMixed_apply, embedF4_apply,
      projG2, projMixed, projF4]
  exact ⟨hinjG2, hinjF4, (bracket_g2_g2 D₁ D₂).symm, (bracket_f4_f4 E₁ E₂).symm,
    bracket_g2_tensor D₁ a x, bracket_f4_tensor E₁ a x, gradeProj_sum X, hsum⟩

theorem e8_magic_square_mixed_bracket_and_identities
    (a b c : splitOctonionTraceZero) (x y z : h3TraceZero) :
    ⁅embedTensor a x, embedTensor b y⁆ =
      embedG2 (((1 / 3 : ℝ) * H3Zorn.traceBilin x.1 y.1) • g2Inner a b) +
      embedTensor (zornComm0 a b) (h3Mul0 x y) +
      embedF4 (((-2 : ℝ) * zornBilin a.1 b.1) • f4Inner x y) ∧
    zornBilin a.1 (zornComm0 b c).1 = zornBilin b.1 (zornComm0 c a).1 ∧
    f4Inner x (h3Mul0 y z) + f4Inner y (h3Mul0 z x) + f4Inner z (h3Mul0 x y) = 0 ∧
    (1 / 3 : ℝ) • h3Proj0 (x.1 * (y.1 * z.1) + y.1 * (z.1 * x.1) + z.1 * (x.1 * y.1)) =
      (1 / 6 : ℝ) •
        (H3Zorn.traceBilin y.1 z.1 • x + H3Zorn.traceBilin z.1 x.1 • y +
          H3Zorn.traceBilin x.1 y.1 • z) :=
  ⟨bracket_tensor_tensor a b x y, zornBilin_comm_cyclic a b c,
    f4Inner_mul_cyclic_zero x y z, h3Proj0_cyclic_cube_polarized x y z⟩

theorem e8_concrete_nonzero_mixed_bracket_witness :
    (∃ x y : SplitE8Lie, ⁅x, y⁆ ≠ 0) ∧
    (let u := embedTensor (zornU 0) (h3EmbedJ23 (zorn_basis 0))
     ⁅embedTensor zornE0 h3DiagZero₁, u⁆ = -u ∧
     ⁅embedTensor zornE0 h3DiagZero₁, u⁆ ≠ 0) := by
  refine ⟨exists_bracket_ne_zero, ?_⟩
  intro u
  have hbr : ⁅embedTensor zornE0 h3DiagZero₁, u⁆ = -u := by
    change ⁅embedTensor zornE0 h3DiagZero₁, embedTensor (zornU 0) (h3EmbedJ23 (zorn_basis 0))⁆ =
      -embedTensor (zornU 0) (h3EmbedJ23 (zorn_basis 0))
    rw [bracket_tensor_tensor, traceBilin_h3DiagZero₁_h3EmbedJ23, zornBilin_zornE0_zornU,
      zornComm0_zornE0_zornU, h3Mul0_h3DiagZero₁_h3EmbedJ23]
    simp only [mul_zero, zero_smul, map_zero, zero_add, add_zero, embedTensor_apply,
      TensorProduct.smul_tmul, TensorProduct.tmul_smul, smul_smul]
    norm_num
    apply SplitE8Lie.ext <;> simp
  refine ⟨hbr, ?_⟩
  rw [hbr]
  intro hneg
  have hu : u = 0 := neg_eq_zero.mp hneg
  exact embedTensor_ne_zero_witness_aux hu
where
  embedTensor_ne_zero_witness_aux :
      embedTensor (zornU 0) (h3EmbedJ23 (zorn_basis 0)) ≠ 0 := by
    let f1 : splitOctonionTraceZero →ₗ[ℝ] ℝ :=
      { toFun := fun a => a.1.v 0
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    let f2 : h3TraceZero →ₗ[ℝ] ℝ :=
      { toFun := fun x => x.1.b.a
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    let f : MixedCarrier →ₗ[ℝ] ℝ :=
      TensorProduct.lift (LinearMap.lsmul ℝ ℝ |>.compl₂ f2 |>.comp f1)
    intro h0
    have hm := congrArg (fun X => f (projMixed X)) h0
    have hval : f (projMixed (embedTensor (zornU 0) (h3EmbedJ23 (zorn_basis 0)))) = 1 := by
      change (zornU 0).1.v 0 * (h3EmbedJ23 (zorn_basis 0)).1.b.a = 1
      simp [zornU, ZornVectorMatrix.U, ZornVec3.basis, h3EmbedJ23, embedJ23, zorn_basis]
    rw [hval, map_zero, map_zero] at hm
    exact one_ne_zero hm

theorem e8_bracket_antisymm_self_and_zero (X Y : SplitE8Lie) :
    magicBracketLM Y X = -magicBracketLM X Y ∧
    ⁅Y, X⁆ = -⁅X, Y⁆ ∧
    magicBracketLM X X = 0 ∧
    ⁅X, X⁆ = 0 ∧
    ⁅(0 : SplitE8Lie), X⁆ = 0 ∧
    ⁅X, (0 : SplitE8Lie)⁆ = 0 :=
  ⟨magicBracketLM_antisymm X Y, (lie_skew Y X).symm, magicBracketLM_self X,
    lie_self X, zero_lie X, lie_zero X⟩

theorem e8_g2_and_f4_commute_inside_e8
    (D : G2DerivationCarrier) (E : F4DerivationCarrier) :
    ⁅embedG2 D, embedF4 E⁆ = 0 ∧
    ⁅embedF4 E, embedG2 D⁆ = 0 :=
  ⟨bracket_g2_f4 D E, bracket_f4_g2 E D⟩

theorem e8_mixed_bracket_all_three_projections_nontrivial :
    let X := ⁅e8SimpleE 5, e8SimpleF 5⁆
    projG2 X ≠ 0 ∧ projMixed X ≠ 0 ∧ projF4 X ≠ 0 := by
  intro X
  have hX : X = e8SimpleH 5 := rfl
  have heq : e8SimpleH 5 =
      (-2 / 3 : ℝ) • cartan8 0 + (1 / 3 : ℝ) • cartan8 1 -
        cartan8 2 - cartan8 3 - (1 / 2 : ℝ) • cartan8 5 +
        (1 / 6 : ℝ) • cartan8 6 + (1 / 3 : ℝ) • cartan8 7 :=
    e8SimpleH_eq_linear_comb_cartan8 5
  refine ⟨?_, ?_, ?_⟩
  · intro h0
    have hproj : projG2 (e8SimpleH 5) =
        (-2 / 3 : ℝ) • g2CartanBasis 0 + (1 / 3 : ℝ) • g2CartanBasis 1 := by
      have hp1 : ∀ D : G2DerivationCarrier, projG2 (embedG2 D) = D := fun _ => rfl
      have hp2 : ∀ E : F4DerivationCarrier, projG2 (embedF4 E) = 0 := fun _ => rfl
      have hp3 : ∀ a x, projG2 (embedTensor a x) = 0 := fun _ _ => rfl
      rw [heq]
      simp only [map_add, map_sub, map_smul, cartan8, hp1, hp2, hp3, smul_zero, sub_zero, add_zero]
    rw [hX, hproj] at h0
    have hc := Fintype.linearIndependent_iff.mp g2CartanBasis_linearIndependent
      (fun i : Fin 2 => match i with | 0 => (-2 / 3 : ℝ) | 1 => (1 / 3 : ℝ))
      (by simpa [Fin.sum_univ_two] using h0) 0
    norm_num at hc
  · intro h0
    have hproj : projMixed (e8SimpleH 5) =
        (1 / 6 : ℝ) • (zornE0 ⊗ₜ[ℝ] h3DiagZero₁) +
          (1 / 3 : ℝ) • (zornE0 ⊗ₜ[ℝ] h3DiagZero₂) := by
      rw [heq]
      simp [cartan8, projMixed, embedG2_apply, embedF4_apply, embedTensor_apply, embedMixed_apply]
    rw [hX, hproj] at h0
    let fOct : splitOctonionTraceZero →ₗ[ℝ] ℝ :=
      { toFun := fun a => a.1.a, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
    let fH3 : h3TraceZero →ₗ[ℝ] ℝ :=
      { toFun := fun x => x.1.α₁, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
    let phi : MixedCarrier →ₗ[ℝ] ℝ :=
      TensorProduct.lift (LinearMap.lsmul ℝ ℝ |>.compl₂ fH3 |>.comp fOct)
    have hp := congrArg phi h0
    have hv1 : phi (zornE0 ⊗ₜ[ℝ] h3DiagZero₁) = 1 := by
      change zornE0.1.a * h3DiagZero₁.1.α₁ = 1
      simp [zornE0, ZornVectorMatrix.diagonal, h3DiagZero₁, H3Zorn.sub_readback,
        h3_diag₁, h3_diag₂]
    have hv2 : phi (zornE0 ⊗ₜ[ℝ] h3DiagZero₂) = 0 := by
      change zornE0.1.a * h3DiagZero₂.1.α₁ = 0
      simp [zornE0, ZornVectorMatrix.diagonal, h3DiagZero₂, H3Zorn.sub_readback,
        h3_diag₂, h3_diag₃]
    rw [map_add, map_smul, map_smul, hv1, hv2, map_zero] at hp
    norm_num at hp
  · intro h0
    have hproj : projF4 (e8SimpleH 5) =
        -f4CartanBasis 0 - f4CartanBasis 1 - (1 / 2 : ℝ) • f4CartanBasis 3 := by
      rw [heq]
      simp only [map_add, map_sub, map_smul, cartan8]
      change (-2 / 3 : ℝ) • (0 : F4DerivationCarrier) + (1 / 3 : ℝ) • 0 -
        f4CartanBasis 0 - f4CartanBasis 1 - (1 / 2 : ℝ) • f4CartanBasis 3 +
        (1 / 6 : ℝ) • 0 + (1 / 3 : ℝ) • 0 = _
      module
    rw [hX, hproj] at h0
    have hlin : ∑ i : Fin 4,
        (match i with | 0 => (-1 : ℝ) | 1 => -1 | 2 => 0 | 3 => -1 / 2) • f4CartanBasis i =
        0 := by
      rw [Fin.sum_univ_four]
      convert h0 using 1
      module
    have hc := Fintype.linearIndependent_iff.mp f4CartanBasis_linearIndependent _ hlin 0
    norm_num at hc

theorem e8_traceless_boundary_and_self_annihilation
    (r : ℝ) (a : splitOctonionTraceZero) (x : h3TraceZero) :
    ZornVectorMatrix.one (R := ℝ) ∉ splitOctonionTraceZero ∧
    (1 : H3Zorn ℝ) ∉ h3TraceZero ∧
    h3Proj0 (1 : H3Zorn ℝ) = 0 ∧
    h3Proj0 (r • (1 : H3Zorn ℝ)) = 0 ∧
    zornComm0 a a = 0 ∧
    g2Inner a a = 0 ∧
    f4Inner x x = 0 :=
  ⟨traceless_octonion_excludes_one.1, traceless_albert_excludes_one.1,
    by simpa using h3Proj0_smul_one 1, h3Proj0_smul_one r,
    zornComm0_self a, g2Inner_self a, f4Inner_self x⟩

theorem e8_summand_projections_orthogonal
    (D : G2DerivationCarrier) (E : F4DerivationCarrier) (m : MixedCarrier)
    (a : splitOctonionTraceZero) (x : h3TraceZero) :
    projG2 (embedG2 D) = D ∧
    projMixed (embedG2 D) = 0 ∧
    projF4 (embedG2 D) = 0 ∧
    projG2 (embedMixed m) = 0 ∧
    projMixed (embedMixed m) = m ∧
    projF4 (embedMixed m) = 0 ∧
    projG2 (embedF4 E) = 0 ∧
    projMixed (embedF4 E) = 0 ∧
    projF4 (embedF4 E) = E ∧
    embedMixed ((0 : splitOctonionTraceZero) ⊗ₜ[ℝ] x) = 0 ∧
    embedMixed (a ⊗ₜ[ℝ] (0 : h3TraceZero)) = 0 := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
  · simp [TensorProduct.zero_tmul]; rfl
  · simp [TensorProduct.tmul_zero]; rfl

/-! ## `[M6-CONTRACT]` Feature 15: `𝔈₈(8)` 8D Cartan, `E₈` Root System, Simplicity (Tier 1–2) -/

theorem e8_cartan_8d_triangularizable_and_span :
    Module.finrank ℝ splitE8Cartan = 8 ∧
    splitE8Cartan.IsCartanSubalgebra ∧
    splitE8Cartan.toSubmodule = Submodule.span ℝ (Set.range e8SimpleH) ∧
    LieModule.IsTriangularizable ℝ splitE8Cartan SplitE8Lie ∧
    Module.finrank ℝ SplitE8Lie = Fintype.card (Fin 8 ⊕ Fin 240) := by
  refine ⟨finrank_splitE8Cartan, splitE8Cartan_isCartanSubalgebra,
    splitE8Cartan_eq_span_e8SimpleH, splitE8Cartan_isTriangularizable, ?_⟩
  rw [finrank_splitE8Lie, Fintype.card_sum, Fintype.card_fin, Fintype.card_fin]

theorem e8_roots_240_equiv_and_chevalley_basis (r : Fin 240) :
    Fintype.card splitE8Cartan.root = 240 ∧
    splitE8Cartan.root.card = 240 ∧
    Function.Bijective e8RootEquiv ∧
    Function.Bijective e8MathlibRootEquiv ∧
    Function.Bijective e8RootSystemEquiv ∧
    e8RootVec r ∈ LieAlgebra.rootSpace splitE8Cartan (e8RootWeight r) ∧
    Module.finrank ℝ SplitE8Lie = Fintype.card (Fin 8 ⊕ Fin 240) := by
  refine ⟨card_splitE8Cartan_root, splitE8Cartan_root_card, e8RootEquiv.bijective,
    e8MathlibRootEquiv.bijective, e8RootSystemEquiv.bijective, e8RootVec_mem_rootSpace r, ?_⟩
  rw [Module.finrank_eq_card_basis e8ChevalleyBasis]

theorem e8_isKilling_nondegenerate_simple_and_semisimple :
    LieAlgebra.IsKilling ℝ SplitE8Lie ∧
    (killingForm ℝ SplitE8Lie).Nondegenerate ∧
    LieAlgebra.IsSimple ℝ SplitE8Lie ∧
    LieAlgebra.IsSemisimple ℝ SplitE8Lie ∧
    LieAlgebra.HasTrivialRadical ℝ SplitE8Lie ∧
    LieAlgebra.center ℝ SplitE8Lie = ⊥ :=
  ⟨splitE8Lie_isKilling, splitE8Lie_killingForm_nondegenerate, splitE8Lie_isSimple,
    splitE8Lie_isSemisimple, splitE8Lie_hasTrivialRadical, center_splitE8Lie_eq_bot⟩

theorem e8_root_system_crystallographic_reduced_irreducible :
    splitE8RootSystem.IsRootSystem ∧
    splitE8RootSystem.IsCrystallographic ∧
    splitE8RootSystem.IsReduced ∧
    splitE8RootSystem.IsIrreducible :=
  ⟨splitE8RootSystem_isRootSystem, splitE8RootSystem_isCrystallographic,
    splitE8RootSystem_isReduced, splitE8RootSystem_isIrreducible⟩

theorem e8_root_system_base_cartan_matrix_and_sl2_triples (i j : Fin 8) :
    splitE8RootSystemBase.cartanMatrix.reindex
      splitE8BaseSupportEquiv.symm splitE8BaseSupportEquiv.symm = CartanMatrix.E 8 ∧
    splitE8RootSystem.pairing (e8SimpleMathlibRoot i) (e8SimpleMathlibRoot j) =
      (CartanMatrix.E 8 i j : ℝ) ∧
    Tag.cartan .E8 = CartanMatrix.E 8 ∧
    IsSl2Triple (e8SimpleH i) (e8SimpleE i) (e8SimpleF i) :=
  ⟨splitE8RootSystemBase_cartanMatrix_eq, splitE8RootSystem_pairing_simple i j,
    splitE8_cartan_eq_mathlib, e8Simple_isSl2Triple i⟩

theorem e8_cartan_isLieAbelian_and_generators_commute
    (h₁ h₂ : splitE8Cartan) (a b i j : Fin 8) :
    IsLieAbelian splitE8Cartan ∧
    ⁅h₁, h₂⁆ = 0 ∧
    ⁅cartan8 a, cartan8 b⁆ = 0 ∧
    ⁅e8SimpleH i, e8SimpleH j⁆ = 0 :=
  ⟨splitE8Cartan_isLieAbelian, splitE8Cartan_isLieAbelian.trivial h₁ h₂,
    cartan8_comm a b, e8SimpleH_comm i j⟩

theorem e8_roots_nonzero_and_opposite_negation (r : Fin 240) :
    e8RootVec r ≠ 0 ∧
    e8RootWeight r ≠ 0 ∧
    e8RootNeg (e8RootNeg r) = r ∧
    e8RootCoord (e8RootNeg r) = -e8RootCoord r ∧
    e8RootWeight (e8RootNeg r) = -e8RootWeight r ∧
    ⁅e8RootVec r, e8RootVec (e8RootNeg r)⁆ ≠ 0 ∧
    ⁅e8RootVec r, e8RootVec (e8RootNeg r)⁆ ∈ splitE8Cartan :=
  ⟨e8RootVec_ne_zero r, e8RootWeight_ne_zero r, e8RootNeg_involutive r,
    e8RootCoord_neg r, e8RootWeight_neg r, e8RootVec_bracket_neg_ne_zero r,
    e8RootVec_opposite_bracket_mem_cartan (by rw [e8RootCoord_neg, add_neg_cancel])⟩

theorem e8_no_abelian_ideal_and_g2_f4_not_ideals :
    (∀ I : LieIdeal ℝ SplitE8Lie, IsLieAbelian I → I = ⊥) ∧
    (∀ I : LieIdeal ℝ SplitE8Lie, I = ⊥ ∨ I = ⊤) ∧
    ¬ IsLieAbelian SplitE8Lie ∧
    (∃ D : G2DerivationCarrier, ∃ X : SplitE8Lie, ⁅embedG2 D, X⁆ ∉ Set.range embedG2) ∧
    (∃ E : F4DerivationCarrier, ∃ X : SplitE8Lie, ⁅embedF4 E, X⁆ ∉ Set.range embedF4) := by
  refine ⟨splitE8Lie_no_abelian_ideal, splitE8Lie_isSimple.eq_bot_or_eq_top, ?_, ?_, ?_⟩
  · intro hab
    exact e8_noncomm_witness (hab.trivial (e8SimpleH 0) (e8SimpleE 0))
  · refine ⟨g2CartanBasis 0, embedTensor (zornU 0) (h3EmbedJ23 (zorn_basis 0)), ?_⟩
    rintro ⟨D', hD'⟩
    have hm := congrArg projMixed hD'
    rw [bracket_g2_tensor, g2CartanBasis_apply_zornU 0 0, one_smul] at hm
    change (embedG2 D').mixed = (embedTensor (zornU 0) _).mixed at hm
    simp only [embedG2_apply, embedTensor_apply, embedMixed_apply] at hm
    have hnz : embedTensor (zornU 0) (h3EmbedJ23 (zorn_basis 0)) ≠ 0 := by
      intro h0
      exact e8_concrete_nonzero_mixed_bracket_witness.2.2 (by rw [h0, lie_zero])
    apply hnz
    apply SplitE8Lie.ext
    · rfl
    · exact hm.symm
    · rfl
  · have hE4_mem : e8SimpleH 4 =
        embedF4 (f4CartanBasis 0 + (2 : ℝ) • f4CartanBasis 1 + f4CartanBasis 3) := by
      rw [e8SimpleH_eq_linear_comb_cartan8 4]
      apply SplitE8Lie.ext <;> simp [cartan8, embedF4_apply]
    refine ⟨f4CartanBasis 0 + (2 : ℝ) • f4CartanBasis 1 + f4CartanBasis 3, e8SimpleE 5, ?_⟩
    rw [← hE4_mem, e8Simple_bracket_HE]
    have hc : Tag.cartan .E8 (4 : Fin 8) (5 : Fin 8) = -1 := by decide
    rw [hc]
    rintro ⟨E', hE'⟩
    have hm := congrArg projMixed hE'.symm
    have he5 : e8SimpleE 5 = embedTensor (zornU 1) (h3TraceZeroOff 1) := rfl
    rw [he5, Int.cast_neg, Int.cast_one, neg_smul, one_smul] at hm
    simp only [map_neg, projMixed, embedTensor_apply, embedMixed_apply, embedF4_apply] at hm
    have ht : (zornU 1) ⊗ₜ[ℝ] (h3TraceZeroOff 1) = 0 := neg_eq_zero.mp hm
    have he5_zero : e8SimpleE 5 = 0 := by
      rw [he5, embedTensor_apply, ht]
      apply SplitE8Lie.ext <;> simp [embedMixed_apply]
    exact e8RootVec_ne_zero (e8ESimpleIdx 5) he5_zero

theorem e8_noncomm_rootSpace_1d_and_simple_cross_vanish
    (α : splitE8Cartan.root) {i j : Fin 8} (hij : i ≠ j) :
    ⁅e8SimpleH 0, e8SimpleE 0⁆ ≠ 0 ∧
    Module.finrank ℝ (LieAlgebra.rootSpace splitE8Cartan α) = 1 ∧
    ⁅e8SimpleE i, e8SimpleF j⁆ = 0 ∧
    ⁅e8SimpleE i, e8SimpleF i⁆ = e8SimpleH i :=
  ⟨e8_noncomm_witness, finrank_splitE8Cartan_rootSpace_eq_one α,
    e8Simple_bracket_EF_ne hij, e8Simple_bracket_EF_same i⟩

theorem e8_highest_root_and_simple_weights (i j : Fin 8) :
    e8RootCoord e8HighestRootIdx = ![2, 3, 4, 6, 5, 4, 3, 2] ∧
    IsRoot .E8 (e8RootCoord e8HighestRootIdx) ∧
    e8RootEigenvalue i (e8ESimpleIdx j) = CartanMatrix.E 8 i j ∧
    e8RootEigenvalue i (e8FSimpleIdx j) = -CartanMatrix.E 8 i j ∧
    e8RootVec e8HighestRootIdx ≠ 0 ∧
    ⁅e8RootVec e8HighestRootIdx, e8RootVec (e8RootNeg e8HighestRootIdx)⁆ ≠ 0 := by
  refine ⟨?_, e8RootCoord_isRoot e8HighestRootIdx, ?_, ?_,
    e8RootVec_ne_zero e8HighestRootIdx, e8RootVec_bracket_neg_ne_zero e8HighestRootIdx⟩
  · ext k; fin_cases k <;> decide
  · rw [e8RootEigenvalue_simpleE, splitE8_cartan_eq_mathlib]
  · rw [e8RootEigenvalue_simpleF, splitE8_cartan_eq_mathlib]

end M6MagicSquareAndRootSystem

end InfoGeometry.Tests.E8MagicSquare
