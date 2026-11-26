/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.H3ZornE6RootSystem
import InfoGeometry.Algebra.H3ZornE6Simplicity
import InfoGeometry.Algebra.H3ZornE6SerreHom
import InfoGeometry.Algebra.H3ZornE6ChevalleyBruhat
import InfoGeometry.Algebra.H3ZornMinusculeCFSGBridge
import InfoGeometry.Algebra.H3ZornF4DimensionClosure
import InfoGeometry.Algebra.H3OctonionZornComplexification
import InfoGeometry.Algebra.H3ZornF4Simplicity
import InfoGeometry.Algebra.H3OctonionSimplicity
import InfoGeometry.Algebra.CompactOctonion
import InfoGeometry.Algebra.H3Octonion
import InfoGeometry.Algebra.H3OctonionStructureGroup
import InfoGeometry.Algebra.H3OctonionLieAlgebra

/-!
# E2E Baseline Tests for `E₆` / `F₄` Closure & Compact/Split Albert Algebras (R1 & R4)

Covers all `[IMMEDIATE]` Tier 1 (happy-path) and Tier 2 (boundary / corner /
non-commutativity / real-form separation) requirements across:
- Split `E₆(6)` (`h3zornCubicStabilizer`), 6D Cartan, 72 roots, Chevalley/Weyl/torus bridge
- Split `F₄(4)` (`H3ZornF4Derivations`), 52D dimension closure, 28D triality span
- Compact `𝕆`, `H₃(𝕆)`, `F₄(-52)`, `E₆(-26)`, `Str(H₃(𝕆))`, and Killing trace-square signatures

`[M1-CONTRACT]` covers Milestone M1 (`H3ZornE6SerreHom.lean`) Tier 1 & Tier 2 verification.
`[M2-CONTRACT]` covers Milestone M2 (`H3OctonionZornComplexification.lean`, `H3ZornF4Simplicity.lean`,
`H3OctonionSimplicity.lean`) Tier 1 & Tier 2 verification (Features 4, 5, 6).
`[M3-CONTRACT]` covers Milestone M3 (`H3ZornE6ChevalleyBruhat.lean`, `H3ZornMinusculeCFSGBridge.lean`)
Tier 1 & Tier 2 verification (Feature 7: `E₆(6)` group generation & native signed Bruhat closure).
-/

set_option autoImplicit false

namespace InfoGeometry.Tests.E6Closure

open InfoGeometry.Algebra
open InfoGeometry.Exceptional.CFSGPort.Chevalley
open InfoGeometry.Canonical.H3ZornF4PeirceTrialitySplit

attribute [local instance 100] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

/-! ## Split `E₆(6)` (`h3zornCubicStabilizer`): Tier 1 Happy-Path -/

theorem e6_split_finrank_78 : Module.finrank ℝ h3zornCubicStabilizer = 78 := by
  rw [Module.finrank_eq_card_basis e6ChevalleyBasis]
  simp

theorem e6_split_cartan_finrank_6 : Module.finrank ℝ h3zornCartan = 6 :=
  finrank_h3zornCartan

theorem e6_split_cartan_isCartanSubalgebra : h3zornCartan.IsCartanSubalgebra :=
  h3zornCartan_isCartanSubalgebra

theorem e6_split_root_card_72 :
    Fintype.card {v : Fin (Tag.rank .E6) → ℤ // IsRoot .E6 v} = 72 :=
  card_isRoot .E6

theorem e6_split_root_equiv_bijective :
    Function.Bijective (fun r : Fin 72 =>
      (⟨e6RootCoord r, e6RootCoord_isRoot r⟩ : {v : Fin 6 → ℤ // IsRoot .E6 v})) :=
  e6RootEquiv.bijective

theorem e6_split_root_vecs_nilpotent_sq_zero (r : Fin 72) :
    (e6RootVec r : Module.End ℝ (H3Zorn ℝ)) ^ 2 = 0 :=
  e6RootVec_sq_zero r

theorem e6_split_root_vecs_ne_zero (r : Fin 72) : e6RootVec r ≠ 0 :=
  e6RootVec_ne_zero r

theorem e6_split_isSimple : LieAlgebra.IsSimple ℝ h3zornCubicStabilizer :=
  h3zornCubicStabilizer_isSimple

theorem e6_split_isSemisimple_and_trivial_radical :
    LieAlgebra.IsSemisimple ℝ h3zornCubicStabilizer ∧
      LieAlgebra.HasTrivialRadical ℝ h3zornCubicStabilizer :=
  ⟨h3zornCubicStabilizer_isSemisimple, h3zornCubicStabilizer_hasTrivialRadical⟩

theorem e6_split_center_eq_bot : LieAlgebra.center ℝ h3zornCubicStabilizer = ⊥ :=
  center_h3zornCubicStabilizer_eq_bot

noncomputable def e6_split_chevalley_equiv :
    RootModule .E6 ℝ ≃ₗ[ℝ] h3zornCubicStabilizer :=
  h3zornChevalleyEquiv

theorem e6_split_chevalleyEquiv_generators (i : Fin 6) (r : Fin 72) :
    h3zornChevalleyEquiv (hVec .E6 ℝ i) = e6SimpleH i ∧
      h3zornChevalleyEquiv (rootVec .E6 ℝ (e6RootCoord r)) = e6RootVec r :=
  ⟨h3zornChevalleyEquiv_hVec i, h3zornChevalleyEquiv_rootVec r⟩

theorem e6_split_chevalleyE6_le_reducedStr :
    h3zornChevalleyE6 ≤ (⊤ : Subgroup h3zornReducedStructureGroup) :=
  h3zornChevalleyE6_le_reducedStructureGroup

theorem e6_split_rootSubgroupHom_injective (r : Fin 72) :
    Function.Injective (h3zornRootSubgroupHom r) :=
  h3zornRootSubgroupHom_injective r

theorem e6_split_weyl_braid_all :
    (h3zornWeylElt 0 1 * h3zornWeylElt 2 1 * h3zornWeylElt 0 1 =
      h3zornWeylElt 2 1 * h3zornWeylElt 0 1 * h3zornWeylElt 2 1) ∧
    (h3zornWeylElt 1 1 * h3zornWeylElt 3 1 * h3zornWeylElt 1 1 =
      h3zornWeylElt 3 1 * h3zornWeylElt 1 1 * h3zornWeylElt 3 1) ∧
    (h3zornWeylElt 2 1 * h3zornWeylElt 3 1 * h3zornWeylElt 2 1 =
      h3zornWeylElt 3 1 * h3zornWeylElt 2 1 * h3zornWeylElt 3 1) ∧
    (h3zornWeylElt 3 1 * h3zornWeylElt 4 1 * h3zornWeylElt 3 1 =
      h3zornWeylElt 4 1 * h3zornWeylElt 3 1 * h3zornWeylElt 4 1) ∧
    (h3zornWeylElt 4 1 * h3zornWeylElt 5 1 * h3zornWeylElt 4 1 =
      h3zornWeylElt 5 1 * h3zornWeylElt 4 1 * h3zornWeylElt 5 1) :=
  ⟨h3zornWeylElt_braid_0_2, h3zornWeylElt_braid_1_3, h3zornWeylElt_braid_2_3,
    h3zornWeylElt_braid_3_4, h3zornWeylElt_braid_4_5⟩

theorem e6_split_adjointAction_torus_and_chevalley (i j : Fin 6) (t : ℝˣ) (r : Fin 72)
    (v : RootModule .E6 ℝ) :
    h3zornAdjointAction (h3zornTorusElt i t) (e6SimpleH j) = e6SimpleH j ∧
    h3zornAdjointAction (h3zornTorusElt i t) (e6RootVec r) =
      ((t ^ rootEigenvalue i r : ℝˣ) : ℝ) • e6RootVec r ∧
    h3zornChevalleyEquiv ((torusElt .E6 ℝ i t : Module.End ℝ (RootModule .E6 ℝ)) v) =
      h3zornAdjointAction (h3zornTorusElt i t) (h3zornChevalleyEquiv v) :=
  ⟨h3zornAdjointAction_torusElt_hVec i j t,
    h3zornAdjointAction_torusElt_rootVec i t r,
    h3zornChevalleyEquiv_torusElt i t v⟩

theorem e6_split_adjointAction_simpleX_deg2 (i : Fin 6) (c : ℝ) (Y : h3zornCubicStabilizer) :
    h3zornAdjointAction (h3zornSimpleX i c) Y =
      Y + c • ⁅e6SimpleE i, Y⁆ + (c ^ 2 / 2) • ⁅e6SimpleE i, ⁅e6SimpleE i, Y⁆⁆ :=
  h3zornAdjointAction_simpleX i c Y

/-! ## Split `E₆(6)`: Tier 2 Boundary, Serre, Degeneracy & Non-Commutativity -/

theorem e6_split_cartan_abelian (i j : Fin 6) :
    ⁅e6SimpleH i, e6SimpleH j⁆ = 0 :=
  e6SimpleH_comm i j

theorem e6_split_root_eigenvalue_action (i : Fin 6) (r : Fin 72) :
    ⁅e6SimpleH i, e6RootVec r⁆ = (rootEigenvalue i r : ℝ) • e6RootVec r :=
  e6RootVec_bracket_H i r

theorem e6_split_simple_EF_diagonal_and_offdiag {i j : Fin 6} (hij : i ≠ j) :
    ⁅e6SimpleE i, e6SimpleF i⁆ = e6SimpleH i ∧ ⁅e6SimpleE i, e6SimpleF j⁆ = 0 :=
  ⟨e6Simple_bracket_EF_same i, e6Simple_bracket_EF_ne hij⟩

theorem e6_split_simple_HE_HF_and_serre {i j : Fin 6} (hij : i ≠ j) :
    ⁅e6SimpleH i, e6SimpleE j⁆ = ((Tag.cartan .E6 i j : ℤ) : ℝ) • e6SimpleE j ∧
    ⁅e6SimpleH i, e6SimpleF j⁆ = (-(Tag.cartan .E6 i j : ℤ) : ℝ) • e6SimpleF j ∧
    (Nat.iterate (fun x => ⁅e6SimpleE i, x⁆) (1 - Tag.cartan .E6 i j).toNat) (e6SimpleE j) = 0 ∧
    (Nat.iterate (fun x => ⁅e6SimpleF i, x⁆) (1 - Tag.cartan .E6 i j).toNat) (e6SimpleF j) = 0 :=
  ⟨e6Simple_bracket_HE i j, e6Simple_bracket_HF i j,
    e6Simple_serre_E hij, e6Simple_serre_F hij⟩

theorem e6_split_weyl_noncomm_and_comm_pair :
    h3zornWeylElt 0 1 * h3zornWeylElt 2 1 ≠ h3zornWeylElt 2 1 * h3zornWeylElt 0 1 ∧
    h3zornWeylElt 0 1 * h3zornWeylElt 1 1 = h3zornWeylElt 1 1 * h3zornWeylElt 0 1 :=
  ⟨h3zornWeylElt_noncomm_witness, h3zornWeylElt_comm_0_1⟩

theorem e6_split_lie_nonabelian_witness :
    ⁅e6SimpleH 0, e6SimpleE 0⁆ ≠ 0 := by
  rw [e6Simple_bracket_HE]
  have hc : Tag.cartan .E6 (0 : Fin 6) (0 : Fin 6) = 2 := by decide
  rw [hc]
  intro h0
  have he := (smul_eq_zero.mp h0).resolve_left (by norm_num)
  exact e6RootVec_ne_zero (eSimpleIdx 0) he

theorem e6_split_matrix27_noncomm_witnesses :
    (∃ A B : Matrix (Fin 27) (Fin 27) ℝ, A * B ≠ B * A) ∧
    (∃ A B : Matrix (Fin 27) (Fin 27) ℤ, A * B ≠ B * A) :=
  ⟨matrix27_real_noncomm_witness, matrix27_int_noncomm_witness⟩

theorem e6_split_simple_generators_span_top (S : LieSubalgebra ℝ h3zornCubicStabilizer)
    (hH : ∀ i : Fin 6, e6SimpleH i ∈ S)
    (hE : ∀ i : Fin 6, e6SimpleE i ∈ S)
    (hF : ∀ i : Fin 6, e6SimpleF i ∈ S) : S = ⊤ :=
  h3zornE6_simple_generators_generate S hH hE hF

/-! ## Split `F₄(4)` (`H3ZornF4Derivations`): Tier 1 & Tier 2 -/

theorem f4_split_finrank_52 : Module.finrank ℝ H3ZornF4Derivations = 52 :=
  finrank_H3ZornF4Derivations

theorem f4_split_basisSpan_eq_top :
    f4BasisSpan = H3ZornF4Derivations.toSubmodule :=
  f4BasisSpan_eq_H3ZornF4Derivations

theorem f4_split_triality_finrank_28 :
    Module.finrank ℝ trialityBasisSpan = 28 :=
  trialityBasisSpan_finrank

theorem f4_split_le_e6_stabilizer :
    H3ZornF4Derivations ≤ h3zornCubicStabilizer :=
  H3ZornF4Derivations_le_h3zornCubicStabilizer

theorem f4_split_trace_sq_pos_witness :
    LinearMap.trace ℝ (H3Zorn ℝ) (splitF4TracePosWitness.1 * splitF4TracePosWitness.1) = 3 / 2 ∧
    0 < LinearMap.trace ℝ (H3Zorn ℝ) (splitF4TracePosWitness.1 * splitF4TracePosWitness.1) ∧
    splitF4TracePosWitness ≠ 0 := by
  refine ⟨splitF4TracePosWitness_trace_sq, splitF4TracePosWitness_trace_sq_pos, ?_⟩
  intro hz
  have htr := splitF4TracePosWitness_trace_sq
  rw [hz] at htr
  simp at htr
  norm_num at htr

/-! ## Compact `𝕆`, `H₃(𝕆)`, `F₄(-52)`, `E₆(-26)`, `Str(H₃(𝕆))`: Tier 1 & Tier 2 -/

theorem compact_octonion_finrank_8 : Module.finrank ℝ (CompactOctonion ℝ) = 8 :=
  CompactOctonion.finrank_compactOctonion

theorem compact_octonion_norm_mul_and_division (x y : CompactOctonion ℝ) :
    CompactOctonion.norm (CompactOctonion.mul x y) =
      CompactOctonion.norm x * CompactOctonion.norm y ∧
    (CompactOctonion.mul x y = 0 ↔ x = 0 ∨ y = 0) :=
  ⟨CompactOctonion.norm_mul x y, CompactOctonion.mul_eq_zero_iff x y⟩

theorem compact_octonion_two_sided_inverse {x : CompactOctonion ℝ} (hx : x ≠ 0) :
    CompactOctonion.mul x (CompactOctonion.inv x) = 1 ∧
      CompactOctonion.mul (CompactOctonion.inv x) x = 1 :=
  ⟨CompactOctonion.mul_inv_cancel hx, CompactOctonion.inv_mul_cancel hx⟩

theorem compact_octonion_noncomm_witness :
    CompactOctonion.mul (CompactOctonion.basisVec 1) (CompactOctonion.basisVec 2) ≠
      CompactOctonion.mul (CompactOctonion.basisVec 2) (CompactOctonion.basisVec 1) := by
  intro h
  have he := congrArg CompactOctonion.e4 h
  simp [CompactOctonion.basisVec, CompactOctonion.mul] at he
  norm_num at he

theorem compact_octonion_nonassoc_witness :
    ∃ x y : CompactOctonion ℝ,
      CompactOctonion.mul (CompactOctonion.mul (CompactOctonion.basisVec 1) x) y ≠
        CompactOctonion.mul (CompactOctonion.basisVec 1) (CompactOctonion.mul x y) := by
  by_contra h
  push Not at h
  have htr : CompactOctonion.trace (CompactOctonion.basisVec 1) = 0 := by
    simp [CompactOctonion.trace, CompactOctonion.basisVec]
  have hb0 := CompactOctonion.pureImaginary_left_nucleus_eq_zero (CompactOctonion.basisVec 1) htr h
  have he1 := congrArg CompactOctonion.e1 hb0
  simp [CompactOctonion.basisVec] at he1

theorem compact_albert_finrank_27_jordan_and_formal_reality :
    Module.finrank ℝ (H3Octonion ℝ) = 27 ∧
    IsCommJordan (H3Octonion ℝ) ∧
    (∀ x y : H3Octonion ℝ, x * x + y * y = 0 → x = 0 ∧ y = 0) :=
  ⟨H3Octonion.finrank_h3Octonion, inferInstance, H3Octonion.formal_reality⟩

theorem compact_albert_trace_nondegenerate_and_split_noniso (x : H3Octonion ℝ)
    (hx : ∀ y : H3Octonion ℝ, H3Octonion.traceBilin x y = 0) :
    x = 0 ∧ IsEmpty (H3Octonion ℝ ≃+* H3Zorn ℝ) :=
  ⟨H3Octonion.traceBilin_nondegenerate x hx, H3Octonion.no_jordanIso_H3Octonion_H3Zorn⟩

theorem compact_f4_e6_str_dimensions :
    Module.finrank ℝ H3OctonionF4Derivations = 52 ∧
    Module.finrank ℝ h3OctonionCubicStabilizer = 78 ∧
    Module.finrank ℝ h3OctonionStructureLieSubalgebra = 79 :=
  ⟨finrank_H3OctonionF4Derivations,
    finrank_h3OctonionCubicStabilizer,
    finrank_h3OctonionStructureLieSubalgebra⟩

theorem compact_f4_trace_sq_neg_definite (D : H3OctonionF4Derivations) :
    LinearMap.trace ℝ (H3Octonion ℝ) (D.1 * D.1) ≤ 0 ∧
      (LinearMap.trace ℝ (H3Octonion ℝ) (D.1 * D.1) = 0 ↔ D = 0) :=
  ⟨compactF4_trace_sq_nonpos D, compactF4_trace_sq_eq_zero_iff D⟩

theorem compact_lmul_trace_sq_pos_definite (a : H3Octonion ℝ) :
    0 ≤ LinearMap.trace ℝ (H3Octonion ℝ) (jordanLmul (R := ℝ) a * jordanLmul (R := ℝ) a) ∧
      (LinearMap.trace ℝ (H3Octonion ℝ) (jordanLmul (R := ℝ) a * jordanLmul (R := ℝ) a) = 0 ↔ a = 0) :=
  ⟨compactLmul_trace_sq_nonneg a, compactLmul_trace_sq_eq_zero_iff a⟩

theorem compact_structure_group_fundamental_and_fix_one (X Y Z : H3Octonion ℝ)
    (g : H3Octonion ℝ ≃ₗ[ℝ] H3Octonion ℝ) :
    H3Octonion.U (H3Octonion.U X Y) Z = H3Octonion.U X (H3Octonion.U Y (H3Octonion.U X Z)) ∧
    (g ∈ StructureGroup ℝ (H3Octonion ℝ) ↔
      ∃ u : ℝˣ, ∀ x : H3Octonion ℝ,
        H3Octonion.normCubic (g x) = (u : ℝ) * H3Octonion.normCubic x) :=
  ⟨h3Octonion_U_fundamental X Y Z, h3Octonion_mem_StructureGroup_iff_similitude g⟩

noncomputable def compact_aut_fix_one_equiv :
    H3OctonionJordanAut ≃* h3OctonionReducedStructureFixOne :=
  h3OctonionJordanAutMulEquivReducedStructureFixOne

/-! ## `[M1-CONTRACT]` `E₆` Serre Isomorphism Closure (`H3ZornE6SerreHom`): Tier 1 Happy-Path -/

theorem e6_serre_finite_dimensional_and_finrank_78 :
    FiniteDimensional ℝ (LieAlgebra.e₆ ℝ) ∧
    Module.finrank ℝ (LieAlgebra.e₆ ℝ) ≤ 78 ∧
    Module.finrank ℝ (LieAlgebra.e₆ ℝ) = 78 :=
  ⟨e6Serre_finiteDimensional, finrank_e6_serre_le, finrank_e6_serre⟩

theorem e6_serre_quotient_bijective_and_equiv :
    Function.Injective ⇑h3zornE6SerreQuotientMap ∧
    Function.Surjective ⇑h3zornE6SerreQuotientMap ∧
    Function.Bijective ⇑(h3zornE6SerreEquiv : LieAlgebra.e₆ ℝ ≃ₗ⁅ℝ⁆ h3zornCubicStabilizer) ∧
    (∀ x : LieAlgebra.e₆ ℝ, h3zornE6SerreEquiv x = h3zornE6SerreQuotientMap x) :=
  ⟨h3zornE6SerreQuotientMap_injective, h3zornE6SerreQuotientMap_surjective,
    h3zornE6SerreEquiv.bijective, fun _ => rfl⟩

theorem e6_serre_isSimple_and_semisimple :
    LieAlgebra.IsSimple ℝ (LieAlgebra.e₆ ℝ) ∧
    LieAlgebra.IsSemisimple ℝ (LieAlgebra.e₆ ℝ) ∧
    LieAlgebra.HasTrivialRadical ℝ (LieAlgebra.e₆ ℝ) ∧
    LieAlgebra.center ℝ (LieAlgebra.e₆ ℝ) = ⊥ :=
  ⟨e6Serre_isSimple, inferInstance, inferInstance,
    le_antisymm (LieAlgebra.center_le_radical _ _ |>.trans (by simp)) bot_le⟩

private theorem e6_serre_equiv_H (i : Fin 6) :
    h3zornE6SerreEquiv (e6SerreH i) = e6SimpleH i :=
  h3zornE6SerreQuotientMap_H i

private theorem e6_serre_equiv_E (i : Fin 6) :
    h3zornE6SerreEquiv (e6SerreE i) = e6SimpleE i :=
  h3zornE6SerreQuotientMap_E i

private theorem e6_serre_equiv_F (i : Fin 6) :
    h3zornE6SerreEquiv (e6SerreF i) = e6SimpleF i :=
  h3zornE6SerreQuotientMap_F i

theorem e6_serre_generator_roundtrips (i : Fin 6) :
    h3zornE6SerreEquiv (e6SerreH i) = e6SimpleH i ∧
    h3zornE6SerreEquiv (e6SerreE i) = e6SimpleE i ∧
    h3zornE6SerreEquiv (e6SerreF i) = e6SimpleF i ∧
    h3zornE6SerreEquiv.symm (e6SimpleH i) = e6SerreH i ∧
    h3zornE6SerreEquiv.symm (e6SimpleE i) = e6SerreE i ∧
    h3zornE6SerreEquiv.symm (e6SimpleF i) = e6SerreF i ∧
    ⁅h3zornE6SerreEquiv.symm (e6SimpleH 0), h3zornE6SerreEquiv.symm (e6SimpleE 0)⁆ =
      (2 : ℝ) • h3zornE6SerreEquiv.symm (e6SimpleE 0) ∧
    ⁅h3zornE6SerreEquiv.symm (e6SimpleE 0), h3zornE6SerreEquiv.symm (e6SimpleF 0)⁆ =
      h3zornE6SerreEquiv.symm (e6SimpleH 0) := by
  refine ⟨e6_serre_equiv_H i, e6_serre_equiv_E i, e6_serre_equiv_F i, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← e6_serre_equiv_H i, h3zornE6SerreEquiv.symm_apply_apply]
  · rw [← e6_serre_equiv_E i, h3zornE6SerreEquiv.symm_apply_apply]
  · rw [← e6_serre_equiv_F i, h3zornE6SerreEquiv.symm_apply_apply]
  · rw [← LieEquiv.map_lie, e6Simple_bracket_HE]
    have hc : Tag.cartan .E6 (0 : Fin 6) (0 : Fin 6) = 2 := by decide
    rw [hc]
    simp
  · rw [← LieEquiv.map_lie, e6Simple_bracket_EF_same]

noncomputable def e6_serre_chevalley_root_equiv :
    LieAlgebra.e₆ ℝ ≃ₗ[ℝ] RootModule .E6 ℝ :=
  h3zornE6SerreEquiv.toLinearEquiv.trans h3zornChevalleyEquiv.symm

theorem e6_serre_chevalley_composition_78d (i : Fin 6) (x y : LieAlgebra.e₆ ℝ) :
    Function.Bijective
      (h3zornChevalleyEquiv.symm.toLinearMap.comp
        h3zornE6SerreEquiv.toLinearEquiv.toLinearMap) ∧
    Module.finrank ℝ (RootModule .E6 ℝ) = 78 ∧
    e6_serre_chevalley_root_equiv (e6SerreH i) = hVec .E6 ℝ i ∧
    e6_serre_chevalley_root_equiv (e6SerreE i) = rootVec .E6 ℝ (e6RootCoord (eSimpleIdx i)) ∧
    Function.Bijective (e6SerreChevalleyInv : LieAlgebra.e₆ ℝ → LieAlgebra.e₆ ℝ) ∧
    e6SerreChevalleyInv ⁅x, y⁆ = ⁅e6SerreChevalleyInv x, e6SerreChevalleyInv y⁆ := by
  refine ⟨(h3zornE6SerreEquiv.toLinearEquiv.trans h3zornChevalleyEquiv.symm).bijective,
    ?_, ?_, ?_, e6SerreChevalleyInv.bijective, LieEquiv.map_lie e6SerreChevalleyInv x y⟩
  · rw [LinearEquiv.finrank_eq h3zornChevalleyEquiv, e6_split_finrank_78]
  · simp [e6_serre_chevalley_root_equiv, e6_serre_equiv_H, ← h3zornChevalleyEquiv_hVec i]
  · simp [e6_serre_chevalley_root_equiv, e6_serre_equiv_E, e6SimpleE,
      ← h3zornChevalleyEquiv_rootVec (eSimpleIdx i)]

/-! ## `[M1-CONTRACT]` `E₆` Serre Isomorphism Closure: Tier 2 Boundary, Involution & Non-Abelian -/

private theorem e6_simpleE_ne_zero (i : Fin 6) : e6SimpleE i ≠ 0 := by
  change e6RootVec (eSimpleIdx i) ≠ 0
  exact e6RootVec_ne_zero (eSimpleIdx i)

private theorem e6_simpleF_ne_zero (i : Fin 6) : e6SimpleF i ≠ 0 := by
  intro h0
  have h1 : ⁅e6SimpleE i, e6SimpleF i⁆ = 0 := by rw [h0, lie_zero]
  rw [e6Simple_bracket_EF_same] at h1
  have h2 : ⁅e6SimpleH i, e6SimpleE i⁆ = 0 := by rw [h1, zero_lie]
  rw [e6Simple_bracket_HE] at h2
  have hc : Tag.cartan .E6 i i = 2 := by fin_cases i <;> decide
  rw [hc] at h2
  have he := (smul_eq_zero.mp h2).resolve_left (by norm_num)
  exact e6_simpleE_ne_zero i he

theorem e6_serre_nonabelian_witness (i : Fin 6) :
    ⁅h3zornE6SerreEquiv.symm (e6SimpleH 0), h3zornE6SerreEquiv.symm (e6SimpleE 0)⁆ ≠ 0 ∧
    h3zornE6SerreEquiv.symm (e6SimpleE i) ≠ 0 ∧
    h3zornE6SerreEquiv.symm (e6SimpleF i) ≠ 0 ∧
    ¬ IsLieAbelian (LieAlgebra.e₆ ℝ) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h0
    have h1 := congrArg h3zornE6SerreEquiv h0
    rw [LieEquiv.map_lie, h3zornE6SerreEquiv.apply_symm_apply,
      h3zornE6SerreEquiv.apply_symm_apply, map_zero] at h1
    exact e6_split_lie_nonabelian_witness h1
  · intro h0
    have h1 := congrArg h3zornE6SerreEquiv h0
    rw [h3zornE6SerreEquiv.apply_symm_apply, map_zero] at h1
    exact e6_simpleE_ne_zero i h1
  · intro h0
    have h1 := congrArg h3zornE6SerreEquiv h0
    rw [h3zornE6SerreEquiv.apply_symm_apply, map_zero] at h1
    exact e6_simpleF_ne_zero i h1
  · exact LieAlgebra.IsSimple.non_abelian ℝ

theorem e6_serre_cartan_comm_and_offdiag_EF {i j : Fin 6} (hij : i ≠ j) :
    ⁅h3zornE6SerreEquiv.symm (e6SimpleH i), h3zornE6SerreEquiv.symm (e6SimpleH j)⁆ = 0 ∧
    ⁅h3zornE6SerreEquiv.symm (e6SimpleE i), h3zornE6SerreEquiv.symm (e6SimpleF j)⁆ = 0 ∧
    ⁅h3zornE6SerreEquiv.symm (e6SimpleE i), h3zornE6SerreEquiv.symm (e6SimpleF i)⁆ =
      h3zornE6SerreEquiv.symm (e6SimpleH i) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [← LieEquiv.map_lie, e6SimpleH_comm i j, map_zero]
  · rw [← LieEquiv.map_lie, e6Simple_bracket_EF_ne hij, map_zero]
  · rw [← LieEquiv.map_lie, e6Simple_bracket_EF_same]

theorem e6_serre_zero_and_self_bracket_vanish :
    let X := h3zornE6SerreEquiv.symm (e6SimpleE 0)
    X ≠ 0 ∧ ⁅X, X⁆ = 0 ∧ ⁅X, (0 : LieAlgebra.e₆ ℝ)⁆ = 0 ∧
      ⁅(0 : LieAlgebra.e₆ ℝ), X⁆ = 0 ∧ h3zornE6SerreEquiv 0 = 0 := by
  intro X
  refine ⟨(e6_serre_nonabelian_witness 0).2.1, lie_self X, lie_zero X, zero_lie X, map_zero _⟩

private theorem e6_serre_chevalleyInv_H (i : Fin 6) :
    e6SerreChevalleyInv (e6SerreH i) = -e6SerreH i := by
  change FreeLieAlgebra.lift ℝ _ (FreeLieAlgebra.of ℝ (CartanMatrix.Generators.H i)) = _
  simp; rfl

private theorem e6_serre_chevalleyInv_E (i : Fin 6) :
    e6SerreChevalleyInv (e6SerreE i) = e6SerreF i := by
  change FreeLieAlgebra.lift ℝ _ (FreeLieAlgebra.of ℝ (CartanMatrix.Generators.E i)) = _
  simp; rfl

private theorem e6_serre_chevalleyInv_F (i : Fin 6) :
    e6SerreChevalleyInv (e6SerreF i) = e6SerreE i := by
  change FreeLieAlgebra.lift ℝ _ (FreeLieAlgebra.of ℝ (CartanMatrix.Generators.F i)) = _
  simp; rfl

theorem e6_serre_chevalley_involution_sq_and_nontrivial (x : LieAlgebra.e₆ ℝ) :
    e6SerreChevalleyInv (e6SerreChevalleyInv x) = x ∧
    e6SerreChevalleyInv (h3zornE6SerreEquiv.symm (e6SimpleE 0)) =
      h3zornE6SerreEquiv.symm (e6SimpleF 0) ∧
    e6SerreChevalleyInv (h3zornE6SerreEquiv.symm (e6SimpleE 0)) ≠
      h3zornE6SerreEquiv.symm (e6SimpleE 0) := by
  have hsq : ∀ y : LieAlgebra.e₆ ℝ, e6SerreChevalleyInv (e6SerreChevalleyInv y) = y := by
    let S : LieSubalgebra ℝ (LieAlgebra.e₆ ℝ) :=
      { carrier := {y | e6SerreChevalleyInv (e6SerreChevalleyInv y) = y}
        add_mem' := fun {a b} ha hb => by
          change e6SerreChevalleyInv (e6SerreChevalleyInv (a + b)) = a + b
          rw [map_add, map_add, ha, hb]
        zero_mem' := by
          change e6SerreChevalleyInv (e6SerreChevalleyInv 0) = 0
          simp
        smul_mem' := fun c {a} ha => by
          change e6SerreChevalleyInv (e6SerreChevalleyInv (c • a)) = c • a
          rw [map_smul, map_smul, ha]
        lie_mem' := fun {a b} ha hb => by
          change e6SerreChevalleyInv (e6SerreChevalleyInv ⁅a, b⁆) = ⁅a, b⁆
          rw [LieEquiv.map_lie, LieEquiv.map_lie, ha, hb] }
    have htop : S = ⊤ := e6Serre_generators_generate S
      (fun i => by
        change e6SerreChevalleyInv (e6SerreChevalleyInv (e6SerreH i)) = e6SerreH i
        rw [e6_serre_chevalleyInv_H, map_neg, e6_serre_chevalleyInv_H, neg_neg])
      (fun i => by
        change e6SerreChevalleyInv (e6SerreChevalleyInv (e6SerreE i)) = e6SerreE i
        rw [e6_serre_chevalleyInv_E, e6_serre_chevalleyInv_F])
      (fun i => by
        change e6SerreChevalleyInv (e6SerreChevalleyInv (e6SerreF i)) = e6SerreF i
        rw [e6_serre_chevalleyInv_F, e6_serre_chevalleyInv_E])
    intro y
    have hy : y ∈ S := by rw [htop]; trivial
    exact hy
  refine ⟨hsq x, ?_, ?_⟩
  · rw [← e6_serre_equiv_E 0, h3zornE6SerreEquiv.symm_apply_apply,
      e6_serre_chevalleyInv_E, ← e6_serre_equiv_F 0, h3zornE6SerreEquiv.symm_apply_apply]
  · rw [← e6_serre_equiv_E 0, h3zornE6SerreEquiv.symm_apply_apply, e6_serre_chevalleyInv_E]
    intro heq
    have hmap := congrArg h3zornE6SerreEquiv heq
    rw [e6_serre_equiv_F 0, e6_serre_equiv_E 0] at hmap
    have hbr : ⁅e6SimpleH 0, e6SimpleF 0⁆ = ⁅e6SimpleH 0, e6SimpleE 0⁆ := by rw [hmap]
    rw [e6Simple_bracket_HF, e6Simple_bracket_HE] at hbr
    have hc : Tag.cartan .E6 (0 : Fin 6) (0 : Fin 6) = 2 := by decide
    rw [hc, hmap] at hbr
    have h4 : (4 : ℝ) • e6SimpleE 0 = 0 := by
      have hsub := sub_eq_zero.mpr hbr.symm
      norm_num at hsub
      rw [← show (2 : ℝ) + 2 = 4 by norm_num, add_smul]
      exact hsub
    have he := (smul_eq_zero.mp h4).resolve_left (by norm_num)
    exact e6_simpleE_ne_zero 0 he

theorem e6_serre_cartan_matrix_agreement :
    (fun i j : Fin 6 => Tag.cartan .E6 i j) = CartanMatrix.E 6 ∧
    ⁅h3zornE6SerreEquiv.symm (e6SimpleE 0), h3zornE6SerreEquiv.symm (e6SimpleE 2)⁆ ≠ 0 ∧
    ⁅h3zornE6SerreEquiv.symm (e6SimpleE 0), h3zornE6SerreEquiv.symm (e6SimpleE 1)⁆ = 0 ∧
    ⁅h3zornE6SerreEquiv.symm (e6SimpleE 0),
      ⁅h3zornE6SerreEquiv.symm (e6SimpleE 0), h3zornE6SerreEquiv.symm (e6SimpleE 2)⁆⁆ = 0 := by
  refine ⟨h3zornE6_cartan_eq_mathlib, ?_, ?_, ?_⟩
  · intro h0
    have hm := congrArg h3zornE6SerreEquiv h0
    rw [LieEquiv.map_lie, h3zornE6SerreEquiv.apply_symm_apply,
      h3zornE6SerreEquiv.apply_symm_apply, map_zero] at hm
    have hj : ⁅e6SimpleF 2, ⁅e6SimpleE 0, e6SimpleE 2⁆⁆ = 0 := by rw [hm, lie_zero]
    rw [leibniz_lie] at hj
    have hfe : ⁅e6SimpleF 2, e6SimpleE 0⁆ = 0 := by
      rw [← lie_skew, e6Simple_bracket_EF_ne (by decide : (0 : Fin 6) ≠ 2), neg_zero]
    have hfe2 : ⁅e6SimpleF 2, e6SimpleE 2⁆ = -e6SimpleH 2 := by
      rw [← lie_skew, e6Simple_bracket_EF_same]
    rw [hfe, zero_lie, zero_add, hfe2, lie_neg, ← lie_skew, neg_neg,
      e6Simple_bracket_HE] at hj
    have hc : Tag.cartan .E6 (2 : Fin 6) (0 : Fin 6) = -1 := by decide
    rw [hc] at hj
    norm_num at hj
    exact e6_simpleE_ne_zero 0 hj
  · rw [← LieEquiv.map_lie]
    have hs := e6Simple_serre_E (by decide : (0 : Fin 6) ≠ 1)
    have hc : Tag.cartan .E6 (0 : Fin 6) (1 : Fin 6) = 0 := by decide
    rw [hc] at hs
    simp only [Int.sub_zero, Int.toNat_one, Function.iterate_one] at hs
    rw [hs, map_zero]
  · rw [← LieEquiv.map_lie, ← LieEquiv.map_lie]
    have hs := e6Simple_serre_E (by decide : (0 : Fin 6) ≠ 2)
    have hc : Tag.cartan .E6 (0 : Fin 6) (2 : Fin 6) = -1 := by decide
    rw [hc] at hs
    simp only [Int.reduceSub, Int.reduceToNat, Function.iterate_succ, Function.iterate_zero,
      Function.comp_apply, id_eq] at hs
    rw [hs, map_zero]

section M2Contract

open scoped TensorProduct

/-! ## `[M2-CONTRACT]` Feature 4: Octonion & Albert Complexification — Tier 1 Happy-Path -/

theorem m2_f4_octonion_complex_equiv_preserves_ops (x y : CompactOctonion ℂ)
    (X Y : ZornVectorMatrix ℂ) :
    octonionComplexEquiv 1 = ZornVectorMatrix.one ∧
    octonionComplexEquiv (CompactOctonion.conj x) =
      ZornVectorMatrix.conj (octonionComplexEquiv x) ∧
    ZornVectorMatrix.trace (octonionComplexEquiv x) = CompactOctonion.trace x ∧
    ZornVectorMatrix.norm (octonionComplexEquiv x) = CompactOctonion.norm x ∧
    octonionComplexEquiv (CompactOctonion.mul x y) =
      ZornVectorMatrix.mul (octonionComplexEquiv x) (octonionComplexEquiv y) ∧
    octonionComplexEquiv.symm ZornVectorMatrix.one = 1 ∧
    octonionComplexEquiv.symm (ZornVectorMatrix.conj X) =
      CompactOctonion.conj (octonionComplexEquiv.symm X) ∧
    CompactOctonion.trace (octonionComplexEquiv.symm X) = ZornVectorMatrix.trace X ∧
    CompactOctonion.norm (octonionComplexEquiv.symm X) = ZornVectorMatrix.norm X ∧
    octonionComplexEquiv.symm (ZornVectorMatrix.mul X Y) =
      CompactOctonion.mul (octonionComplexEquiv.symm X) (octonionComplexEquiv.symm Y) ∧
    octonionComplexEquiv.symm (octonionComplexEquiv x) = x ∧
    octonionComplexEquiv (octonionComplexEquiv.symm X) = X :=
  ⟨octonionComplexEquiv_one, octonionComplexEquiv_conj x, octonionComplexEquiv_trace x,
    octonionComplexEquiv_norm x, octonionComplexEquiv_mul x y, octonionComplexEquiv_symm_one,
    octonionComplexEquiv_symm_conj X, octonionComplexEquiv_symm_trace X,
    octonionComplexEquiv_symm_norm X, octonionComplexEquiv_symm_mul X Y,
    octonionComplexEquiv.symm_apply_apply x, octonionComplexEquiv.apply_symm_apply X⟩

theorem m2_f4_octonion_complex_finrank_8 :
    Module.finrank ℂ (CompactOctonion ℂ) = 8 ∧
    Module.finrank ℂ (ZornVectorMatrix ℂ) = 8 := by
  let coordℂ : CompactOctonion ℂ ≃ₗ[ℂ] (Fin 8 → ℂ) :=
    { toFun := fun x i => match i with
        | 0 => x.e0 | 1 => x.e1 | 2 => x.e2 | 3 => x.e3
        | 4 => x.e4 | 5 => x.e5 | 6 => x.e6 | 7 => x.e7
      invFun := fun f => ⟨f 0, f 1, f 2, f 3, f 4, f 5, f 6, f 7⟩
      left_inv := fun x => by ext <;> rfl
      right_inv := fun f => by ext i; fin_cases i <;> rfl
      map_add' := fun x y => by ext i; fin_cases i <;> rfl
      map_smul' := fun r x => by ext i; fin_cases i <;> rfl }
  have hoct : Module.finrank ℂ (CompactOctonion ℂ) = 8 := by
    rw [coordℂ.finrank_eq, Module.finrank_fin_fun]
  have hzorn : Module.finrank ℂ (ZornVectorMatrix ℂ) = 8 := by
    rw [← octonionComplexEquiv.finrank_eq, hoct]
  exact ⟨hoct, hzorn⟩

theorem m2_f4_h3octonion_complex_equiv_preserves_all (x y z : H3Octonion ℂ) :
    h3OctonionComplexEquiv (1 : H3Octonion ℂ) = (1 : H3Zorn ℂ) ∧
    H3Zorn.linearTrace (h3OctonionComplexEquiv x) = H3Octonion.linearTrace x ∧
    H3Zorn.traceBilin (h3OctonionComplexEquiv x) (h3OctonionComplexEquiv y) =
      H3Octonion.traceBilin x y ∧
    H3Zorn.normCubic (h3OctonionComplexEquiv x) = H3Octonion.normCubic x ∧
    h3OctonionComplexEquiv (H3Octonion.adjointQuad x) =
      H3Zorn.adjointQuad (h3OctonionComplexEquiv x) ∧
    h3OctonionComplexEquiv (H3Octonion.crossProduct x y) =
      H3Zorn.crossProduct (h3OctonionComplexEquiv x) (h3OctonionComplexEquiv y) ∧
    h3OctonionComplexEquiv (H3Octonion.U x y) =
      H3Zorn.U (h3OctonionComplexEquiv x) (h3OctonionComplexEquiv y) ∧
    h3OctonionComplexEquiv (H3Octonion.T x y z) =
      H3Zorn.T (h3OctonionComplexEquiv x) (h3OctonionComplexEquiv y)
        (h3OctonionComplexEquiv z) ∧
    h3zornNormTrilinℂ (h3OctonionComplexEquiv x) (h3OctonionComplexEquiv y)
        (h3OctonionComplexEquiv z) =
      h3OctonionNormTrilinℂ x y z ∧
    h3OctonionComplexEquiv (candidateJordanMulOctℂ x y) =
      candidateJordanMulZornℂ (h3OctonionComplexEquiv x) (h3OctonionComplexEquiv y) :=
  ⟨h3OctonionComplexEquiv_one, h3OctonionComplexEquiv_linearTrace x,
    h3OctonionComplexEquiv_traceBilin x y, h3OctonionComplexEquiv_normCubic x,
    h3OctonionComplexEquiv_adjointQuad x, h3OctonionComplexEquiv_crossProduct x y,
    h3OctonionComplexEquiv_U x y, h3OctonionComplexEquiv_T x y z,
    h3OctonionComplexEquiv_normTrilin x y z, h3OctonionComplexEquiv_jordanMul x y⟩

theorem m2_f4_h3_tensor_equiv_invariants (u v w : ℂ ⊗[ℝ] H3Octonion ℝ) :
    h3OctonionTensorEquivH3Zorn ((1 : ℂ) ⊗ₜ[ℝ] (1 : H3Octonion ℝ)) =
      (1 : ℂ) ⊗ₜ[ℝ] (1 : H3Zorn ℝ) ∧
    H3Zorn.traceBilin (tensorEquivH3Zorn (h3OctonionTensorEquivH3Zorn u))
        (tensorEquivH3Zorn (h3OctonionTensorEquivH3Zorn v)) =
      H3Octonion.traceBilin (tensorEquivH3Octonion u) (tensorEquivH3Octonion v) ∧
    H3Zorn.normCubic (tensorEquivH3Zorn (h3OctonionTensorEquivH3Zorn u)) =
      H3Octonion.normCubic (tensorEquivH3Octonion u) ∧
    h3zornNormTrilinℂ (tensorEquivH3Zorn (h3OctonionTensorEquivH3Zorn u))
        (tensorEquivH3Zorn (h3OctonionTensorEquivH3Zorn v))
        (tensorEquivH3Zorn (h3OctonionTensorEquivH3Zorn w)) =
      h3OctonionNormTrilinℂ (tensorEquivH3Octonion u) (tensorEquivH3Octonion v)
        (tensorEquivH3Octonion w) ∧
    h3OctonionTensorEquivH3Zorn.symm (h3OctonionTensorEquivH3Zorn u) = u :=
  ⟨h3OctonionTensorEquivH3Zorn_one, h3OctonionTensorEquivH3Zorn_traceBilin u v,
    h3OctonionTensorEquivH3Zorn_normCubic u, h3OctonionTensorEquivH3Zorn_normTrilin u v w,
    h3OctonionTensorEquivH3Zorn.symm_apply_apply u⟩

theorem m2_f4_h3_complex_finrank_27 :
    Module.finrank ℂ (ℂ ⊗[ℝ] H3Octonion ℝ) = 27 ∧
    Module.finrank ℂ (ℂ ⊗[ℝ] H3Zorn ℝ) = 27 ∧
    Module.finrank ℂ (H3Octonion ℂ) = 27 ∧
    Module.finrank ℂ (H3Zorn ℂ) = 27 := by
  have hto : Module.finrank ℂ (ℂ ⊗[ℝ] H3Octonion ℝ) = 27 := by
    rw [Module.finrank_eq_card_basis (H3Octonion.h3OctonionBasis.baseChange ℂ), Fintype.card_fin]
  have htz : Module.finrank ℂ (ℂ ⊗[ℝ] H3Zorn ℝ) = 27 := by
    rw [← h3OctonionTensorEquivH3Zorn.finrank_eq, hto]
  have ho : Module.finrank ℂ (H3Octonion ℂ) = 27 := by
    rw [← tensorEquivH3Octonion.finrank_eq, hto]
  have hz : Module.finrank ℂ (H3Zorn ℂ) = 27 := by
    rw [← tensorEquivH3Zorn.finrank_eq, htz]
  exact ⟨hto, htz, ho, hz⟩

/-! ## `[M2-CONTRACT]` Feature 4: Octonion & Albert Complexification — Tier 2 Boundary & Separation -/

private def octℂ (i : Fin 8) : CompactOctonion ℂ :=
  match i with
  | 0 => ⟨1, 0, 0, 0, 0, 0, 0, 0⟩
  | 1 => ⟨0, 1, 0, 0, 0, 0, 0, 0⟩
  | 2 => ⟨0, 0, 1, 0, 0, 0, 0, 0⟩
  | 3 => ⟨0, 0, 0, 1, 0, 0, 0, 0⟩
  | 4 => ⟨0, 0, 0, 0, 1, 0, 0, 0⟩
  | 5 => ⟨0, 0, 0, 0, 0, 1, 0, 0⟩
  | 6 => ⟨0, 0, 0, 0, 0, 0, 1, 0⟩
  | 7 => ⟨0, 0, 0, 0, 0, 0, 0, 1⟩

theorem m2_f4_octonion_complex_noncomm_transport :
    CompactOctonion.mul (octℂ 1) (octℂ 2) ≠ CompactOctonion.mul (octℂ 2) (octℂ 1) ∧
    ZornVectorMatrix.mul (octonionComplexEquiv (octℂ 1)) (octonionComplexEquiv (octℂ 2)) ≠
      ZornVectorMatrix.mul (octonionComplexEquiv (octℂ 2)) (octonionComplexEquiv (octℂ 1)) ∧
    ZornVectorMatrix.mul (octonionComplexEquiv (octℂ 1)) (octonionComplexEquiv (octℂ 2)) =
      octonionComplexEquiv (octℂ 4) := by
  have hnc : CompactOctonion.mul (octℂ 1) (octℂ 2) ≠ CompactOctonion.mul (octℂ 2) (octℂ 1) := by
    intro h
    have he4 := congrArg CompactOctonion.e4 h
    simp [octℂ, CompactOctonion.mul] at he4
    norm_num at he4
  have hncZ : ZornVectorMatrix.mul (octonionComplexEquiv (octℂ 1))
        (octonionComplexEquiv (octℂ 2)) ≠
      ZornVectorMatrix.mul (octonionComplexEquiv (octℂ 2))
        (octonionComplexEquiv (octℂ 1)) := by
    rw [← octonionComplexEquiv_mul, ← octonionComplexEquiv_mul]
    intro h
    exact hnc (octonionComplexEquiv.injective h)
  have hfano : ZornVectorMatrix.mul (octonionComplexEquiv (octℂ 1))
        (octonionComplexEquiv (octℂ 2)) =
      octonionComplexEquiv (octℂ 4) := by
    rw [← octonionComplexEquiv_mul]
    congr 1
    ext <;> simp [octℂ, CompactOctonion.mul]
  exact ⟨hnc, hncZ, hfano⟩

theorem m2_f4_octonion_complex_nonassoc_and_isotropic :
    let x : CompactOctonion ℂ := ⟨0, 1, 0, Complex.I, 0, 0, 0, 0⟩
    let y : CompactOctonion ℂ := ⟨0, 0, 1, 0, 0, 1, 0, 0⟩
    let z : CompactOctonion ℂ := ⟨0, 0, 0, 0, 1, 0, 0, Complex.I⟩
    let iso : CompactOctonion ℂ := ⟨1, 0, 0, 0, 0, 0, 0, Complex.I⟩
    CompactOctonion.mul (CompactOctonion.mul x y) z ≠
      CompactOctonion.mul x (CompactOctonion.mul y z) ∧
    ZornVectorMatrix.mul (ZornVectorMatrix.mul (octonionComplexEquiv x) (octonionComplexEquiv y))
        (octonionComplexEquiv z) ≠
      ZornVectorMatrix.mul (octonionComplexEquiv x)
        (ZornVectorMatrix.mul (octonionComplexEquiv y) (octonionComplexEquiv z)) ∧
    iso ≠ 0 ∧ CompactOctonion.norm iso = 0 ∧
    ZornVectorMatrix.norm (octonionComplexEquiv iso) = 0 := by
  intro x y z iso
  have hna : CompactOctonion.mul (CompactOctonion.mul x y) z ≠
      CompactOctonion.mul x (CompactOctonion.mul y z) := by
    intro h
    have he7 := congrArg CompactOctonion.e7 h
    simp [x, y, z, CompactOctonion.mul] at he7
    have h2 : (2 : ℂ) * Complex.I = 0 := by linear_combination he7
    simp [Complex.I_ne_zero] at h2
  have hnaZ : ZornVectorMatrix.mul
        (ZornVectorMatrix.mul (octonionComplexEquiv x) (octonionComplexEquiv y))
        (octonionComplexEquiv z) ≠
      ZornVectorMatrix.mul (octonionComplexEquiv x)
        (ZornVectorMatrix.mul (octonionComplexEquiv y) (octonionComplexEquiv z)) := by
    simp only [← octonionComplexEquiv_mul]
    intro h
    exact hna (octonionComplexEquiv.injective h)
  have hiso_ne : iso ≠ 0 := by
    intro h
    have h0 := congrArg CompactOctonion.e0 h
    simp [iso] at h0
  have hiso_norm : CompactOctonion.norm iso = 0 := by
    simp [iso, CompactOctonion.norm]
  have hiso_znorm : ZornVectorMatrix.norm (octonionComplexEquiv iso) = 0 := by
    rw [octonionComplexEquiv_norm, hiso_norm]
  exact ⟨hna, hnaZ, hiso_ne, hiso_norm, hiso_znorm⟩

theorem m2_f4_h3_complex_zero_and_one_corners :
    octonionComplexEquiv 0 = 0 ∧
    octonionComplexEquiv.symm 0 = 0 ∧
    h3OctonionComplexEquiv 0 = 0 ∧
    h3OctonionComplexEquiv.symm 0 = 0 ∧
    H3Octonion.normCubic (1 : H3Octonion ℂ) = 1 ∧
    H3Zorn.normCubic (h3OctonionComplexEquiv (1 : H3Octonion ℂ)) = 1 ∧
    H3Zorn.linearTrace (h3OctonionComplexEquiv (1 : H3Octonion ℂ)) = 3 := by
  refine ⟨map_zero _, map_zero _, map_zero _, map_zero _, ?_, ?_, ?_⟩
  · simp [H3Octonion.normCubic, CompactOctonion.norm, CompactOctonion.trace, CompactOctonion.mul]
  · rw [h3OctonionComplexEquiv_normCubic]
    simp [H3Octonion.normCubic, CompactOctonion.norm, CompactOctonion.trace, CompactOctonion.mul]
  · rw [h3OctonionComplexEquiv_linearTrace]
    simp [H3Octonion.linearTrace]
    norm_num

theorem m2_f4_h3_complex_jordanMul_nonassoc_transport :
    let a : H3Octonion ℂ := ⟨Complex.I, 0, 0, 0, 0, 0⟩
    let b : H3Octonion ℂ := ⟨0, 0, 0, octℂ 1, 0, 0⟩
    candidateJordanMulOctℂ (candidateJordanMulOctℂ a b) b ≠
      candidateJordanMulOctℂ a (candidateJordanMulOctℂ b b) ∧
    candidateJordanMulZornℂ
        (candidateJordanMulZornℂ (h3OctonionComplexEquiv a) (h3OctonionComplexEquiv b))
        (h3OctonionComplexEquiv b) ≠
      candidateJordanMulZornℂ (h3OctonionComplexEquiv a)
        (candidateJordanMulZornℂ (h3OctonionComplexEquiv b) (h3OctonionComplexEquiv b)) := by
  intro a b
  have hcr_ab : H3Octonion.crossProduct a b = 0 := by
    apply H3Octonion.ext_h3
    · simp [H3Octonion.crossProduct, a, b]
    · simp [H3Octonion.crossProduct, a, b]
    · simp [H3Octonion.crossProduct, a, b]
    · simp [H3Octonion.crossProduct, a, b]
    · simp [H3Octonion.crossProduct, a, b]
    · simp [H3Octonion.crossProduct, a, b]
  have hcr_bb : H3Octonion.crossProduct b b = ⟨0, 0, -2, 0, 0, 0⟩ := by
    apply H3Octonion.ext_h3
    · simp [H3Octonion.crossProduct, b]
    · simp [H3Octonion.crossProduct, b]
    · simp [H3Octonion.crossProduct, b, octℂ, CompactOctonion.trace, CompactOctonion.mul,
        CompactOctonion.conj]
      norm_num
    · simp [H3Octonion.crossProduct, b]
    · simp [H3Octonion.crossProduct, b]
    · simp [H3Octonion.crossProduct, b]
  have hab : candidateJordanMulOctℂ a b =
      ⟨0, 0, 0, (Complex.I / 2) • octℂ 1, 0, 0⟩ := by
    rw [candidateJordanMulOctℂ, H3Octonion.T_one_formula, hcr_ab]
    apply H3Octonion.ext_h3
    · simp [a, b, H3Octonion.linearTrace]
    · simp [a, b, H3Octonion.linearTrace]
    · simp [a, b, H3Octonion.linearTrace]
    · simp [a, b, H3Octonion.linearTrace, smul_smul]; ring_nf
    · simp [a, b, H3Octonion.linearTrace]
    · simp [a, b, H3Octonion.linearTrace]
  have hbb : candidateJordanMulOctℂ b b = ⟨1, 1, 0, 0, 0, 0⟩ := by
    rw [candidateJordanMulOctℂ, H3Octonion.T_one_formula, hcr_bb]
    apply H3Octonion.ext_h3 <;> simp [b, H3Octonion.linearTrace]
  have hcr_abb : H3Octonion.crossProduct ⟨0, 0, 0, (Complex.I / 2) • octℂ 1, 0, 0⟩ b =
      ⟨0, 0, -Complex.I, 0, 0, 0⟩ := by
    apply H3Octonion.ext_h3
    · simp [H3Octonion.crossProduct, b]
    · simp [H3Octonion.crossProduct, b]
    · simp [H3Octonion.crossProduct, b, octℂ, CompactOctonion.trace, CompactOctonion.mul,
        CompactOctonion.conj]
    · simp [H3Octonion.crossProduct, b]
    · simp [H3Octonion.crossProduct, b]
    · simp [H3Octonion.crossProduct, b]
  have hcr_abb' : H3Octonion.crossProduct a ⟨1, 1, 0, 0, 0, 0⟩ =
      ⟨0, 0, Complex.I, 0, 0, 0⟩ := by
    apply H3Octonion.ext_h3 <;> simp [H3Octonion.crossProduct, a]
  have h_lhs : (candidateJordanMulOctℂ (candidateJordanMulOctℂ a b) b).α₂ =
      Complex.I / 2 := by
    rw [hab, candidateJordanMulOctℂ, H3Octonion.T_one_formula, hcr_abb]
    simp [b, H3Octonion.linearTrace]
    ring
  have h_rhs : (candidateJordanMulOctℂ a (candidateJordanMulOctℂ b b)).α₂ = 0 := by
    rw [hbb, candidateJordanMulOctℂ, H3Octonion.T_one_formula, hcr_abb']
    simp [a, H3Octonion.linearTrace]
  have hna : candidateJordanMulOctℂ (candidateJordanMulOctℂ a b) b ≠
      candidateJordanMulOctℂ a (candidateJordanMulOctℂ b b) := by
    intro h
    have hα₂ := congrArg H3Octonion.α₂ h
    rw [h_lhs, h_rhs] at hα₂
    have h2 : Complex.I = 0 := by linear_combination 2 * hα₂
    exact Complex.I_ne_zero h2
  have hnaZ : candidateJordanMulZornℂ
        (candidateJordanMulZornℂ (h3OctonionComplexEquiv a) (h3OctonionComplexEquiv b))
        (h3OctonionComplexEquiv b) ≠
      candidateJordanMulZornℂ (h3OctonionComplexEquiv a)
        (candidateJordanMulZornℂ (h3OctonionComplexEquiv b) (h3OctonionComplexEquiv b)) := by
    simp only [← h3OctonionComplexEquiv_jordanMul]
    intro h
    exact hna (h3OctonionComplexEquiv.injective h)
  exact ⟨hna, hnaZ⟩

theorem m2_f4_real_form_noniso_vs_complex_equiv :
    IsEmpty (H3Octonion ℝ ≃+* H3Zorn ℝ) ∧
    Nonempty (H3Octonion ℂ ≃ₗ[ℂ] H3Zorn ℂ) ∧
    Nonempty (ℂ ⊗[ℝ] H3Octonion ℝ ≃ₗ[ℂ] ℂ ⊗[ℝ] H3Zorn ℝ) :=
  ⟨H3Octonion.no_jordanIso_H3Octonion_H3Zorn, ⟨h3OctonionComplexEquiv⟩,
    ⟨h3OctonionTensorEquivH3Zorn⟩⟩

/-! ## `[M2-CONTRACT]` Feature 5: Complexified `E₆(ℂ)` and `F₄(ℂ)` — Tier 1 Happy-Path -/

theorem m2_f5_e6_baseChange_equiv_and_bracket (x y : ℂ ⊗[ℝ] h3OctonionCubicStabilizer)
    (X Y : ℂ ⊗[ℝ] h3zornCubicStabilizer) :
    Function.Bijective h3OctonionCubicStabilizerBaseChangeEquiv ∧
    h3OctonionCubicStabilizerBaseChangeEquiv ⁅x, y⁆ =
      ⁅h3OctonionCubicStabilizerBaseChangeEquiv x,
        h3OctonionCubicStabilizerBaseChangeEquiv y⁆ ∧
    h3OctonionCubicStabilizerBaseChangeEquiv.symm ⁅X, Y⁆ =
      ⁅h3OctonionCubicStabilizerBaseChangeEquiv.symm X,
        h3OctonionCubicStabilizerBaseChangeEquiv.symm Y⁆ ∧
    h3OctonionCubicStabilizerBaseChangeEquiv.symm
      (h3OctonionCubicStabilizerBaseChangeEquiv x) = x ∧
    h3OctonionCubicStabilizerBaseChangeEquiv
      (h3OctonionCubicStabilizerBaseChangeEquiv.symm X) = X :=
  ⟨h3OctonionCubicStabilizerBaseChangeEquiv.bijective,
    h3OctonionCubicStabilizerBaseChangeEquiv.map_lie x y,
    h3OctonionCubicStabilizerBaseChangeEquiv.symm.map_lie X Y,
    h3OctonionCubicStabilizerBaseChangeEquiv.symm_apply_apply x,
    h3OctonionCubicStabilizerBaseChangeEquiv.apply_symm_apply X⟩

theorem m2_f5_f4_baseChange_equiv_and_bracket (x y : ℂ ⊗[ℝ] H3OctonionF4Derivations)
    (X Y : ℂ ⊗[ℝ] H3ZornF4Derivations) :
    Function.Bijective h3OctonionF4DerivationsBaseChangeEquiv ∧
    h3OctonionF4DerivationsBaseChangeEquiv ⁅x, y⁆ =
      ⁅h3OctonionF4DerivationsBaseChangeEquiv x,
        h3OctonionF4DerivationsBaseChangeEquiv y⁆ ∧
    h3OctonionF4DerivationsBaseChangeEquiv.symm ⁅X, Y⁆ =
      ⁅h3OctonionF4DerivationsBaseChangeEquiv.symm X,
        h3OctonionF4DerivationsBaseChangeEquiv.symm Y⁆ ∧
    h3OctonionF4DerivationsBaseChangeEquiv.symm
      (h3OctonionF4DerivationsBaseChangeEquiv x) = x ∧
    h3OctonionF4DerivationsBaseChangeEquiv
      (h3OctonionF4DerivationsBaseChangeEquiv.symm X) = X :=
  ⟨h3OctonionF4DerivationsBaseChangeEquiv.bijective,
    h3OctonionF4DerivationsBaseChangeEquiv.map_lie x y,
    h3OctonionF4DerivationsBaseChangeEquiv.symm.map_lie X Y,
    h3OctonionF4DerivationsBaseChangeEquiv.symm_apply_apply x,
    h3OctonionF4DerivationsBaseChangeEquiv.apply_symm_apply X⟩

theorem m2_f5_complex_e6_finrank_78 :
    Module.finrank ℂ (ℂ ⊗[ℝ] h3zornCubicStabilizer) = 78 ∧
    Module.finrank ℂ (ℂ ⊗[ℝ] h3OctonionCubicStabilizer) = 78 := by
  have hz : Module.finrank ℂ (ℂ ⊗[ℝ] h3zornCubicStabilizer) = 78 := by
    rw [Module.finrank_eq_card_basis (e6ChevalleyBasis.baseChange ℂ), Fintype.card_sum,
      Fintype.card_fin, Fintype.card_fin]
  have ho : Module.finrank ℂ (ℂ ⊗[ℝ] h3OctonionCubicStabilizer) = 78 := by
    rw [h3OctonionCubicStabilizerBaseChangeEquiv.toLinearEquiv.finrank_eq, hz]
  exact ⟨hz, ho⟩

theorem m2_f5_complex_f4_finrank_52 :
    Module.finrank ℂ (ℂ ⊗[ℝ] H3ZornF4Derivations) = 52 ∧
    Module.finrank ℂ (ℂ ⊗[ℝ] H3OctonionF4Derivations) = 52 := by
  have hz : Module.finrank ℂ (ℂ ⊗[ℝ] H3ZornF4Derivations) = 52 := by
    rw [Module.finrank_eq_card_basis (f4ChevalleyBasis.baseChange ℂ), Fintype.card_sum,
      Fintype.card_fin, Fintype.card_fin]
  have ho : Module.finrank ℂ (ℂ ⊗[ℝ] H3OctonionF4Derivations) = 52 := by
    rw [h3OctonionF4DerivationsBaseChangeEquiv.toLinearEquiv.finrank_eq, hz]
  exact ⟨hz, ho⟩

theorem m2_f5_complex_e6_and_f4_isSimple :
    LieAlgebra.IsSimple ℂ (ℂ ⊗[ℝ] h3zornCubicStabilizer) ∧
    LieAlgebra.IsSimple ℂ (ℂ ⊗[ℝ] h3OctonionCubicStabilizer) ∧
    LieAlgebra.IsSimple ℂ (ℂ ⊗[ℝ] H3ZornF4Derivations) ∧
    LieAlgebra.IsSimple ℂ (ℂ ⊗[ℝ] H3OctonionF4Derivations) :=
  ⟨complexH3zornCubicStabilizer_isSimple, complexH3OctonionCubicStabilizer_isSimple,
    complexH3ZornF4Derivations_isSimple, complexH3OctonionF4Derivations_isSimple⟩

/-! ## `[M2-CONTRACT]` Feature 5: Complexified `E₆(ℂ)` and `F₄(ℂ)` — Tier 2 Boundary & Separation -/

theorem m2_f5_complex_e6_nonabelian_witness :
    let uZ : ℂ ⊗[ℝ] h3zornCubicStabilizer := (1 : ℂ) ⊗ₜ[ℝ] e6SimpleH 0
    let vZ : ℂ ⊗[ℝ] h3zornCubicStabilizer :=
      (1 : ℂ) ⊗ₜ[ℝ] e6SimpleE 0 + Complex.I ⊗ₜ[ℝ] e6SimpleH 1
    let uO := h3OctonionCubicStabilizerBaseChangeEquiv.symm uZ
    let vO := h3OctonionCubicStabilizerBaseChangeEquiv.symm vZ
    ⁅uZ, vZ⁆ ≠ 0 ∧ ⁅uO, vO⁆ ≠ 0 ∧
    ¬ IsLieAbelian (ℂ ⊗[ℝ] h3zornCubicStabilizer) ∧
    ¬ IsLieAbelian (ℂ ⊗[ℝ] h3OctonionCubicStabilizer) := by
  intro uZ vZ uO vO
  have hbrZ : ⁅uZ, vZ⁆ = (2 : ℂ) • ((1 : ℂ) ⊗ₜ[ℝ] e6SimpleE 0) := by
    dsimp [uZ, vZ]
    rw [lie_add (L := ℂ ⊗[ℝ] h3zornCubicStabilizer),
      LieAlgebra.ExtendScalars.bracket_tmul, LieAlgebra.ExtendScalars.bracket_tmul,
      e6SimpleH_comm 0 1, TensorProduct.tmul_zero, add_zero, one_mul, e6Simple_bracket_HE]
    have hc : Tag.cartan .E6 (0 : Fin 6) (0 : Fin 6) = 2 := by decide
    rw [hc, TensorProduct.tmul_smul, ← IsScalarTower.algebraMap_smul ℂ ((2 : ℤ) : ℝ)]
    simp
  have hneZ : ⁅uZ, vZ⁆ ≠ 0 := by
    rw [hbrZ]
    intro h0
    have hsm := (smul_eq_zero.mp h0).resolve_left (by norm_num)
    have hbas : (1 : ℂ) ⊗ₜ[ℝ] e6SimpleE 0 =
        (e6ChevalleyBasis.baseChange ℂ) (Sum.inr (eSimpleIdx 0)) := by
      simp [e6SimpleE]
    rw [hbas] at hsm
    exact (e6ChevalleyBasis.baseChange ℂ).ne_zero _ hsm
  have hneO : ⁅uO, vO⁆ ≠ 0 := by
    intro h0
    have h1 := congrArg h3OctonionCubicStabilizerBaseChangeEquiv h0
    rw [LieEquiv.map_lie, h3OctonionCubicStabilizerBaseChangeEquiv.apply_symm_apply,
      h3OctonionCubicStabilizerBaseChangeEquiv.apply_symm_apply, map_zero] at h1
    exact hneZ h1
  exact ⟨hneZ, hneO, LieAlgebra.IsSimple.non_abelian ℂ, LieAlgebra.IsSimple.non_abelian ℂ⟩

theorem m2_f5_complex_f4_nonabelian_witness :
    let uZ : ℂ ⊗[ℝ] H3ZornF4Derivations := (1 : ℂ) ⊗ₜ[ℝ] f4SimpleH 0
    let vZ : ℂ ⊗[ℝ] H3ZornF4Derivations :=
      (1 : ℂ) ⊗ₜ[ℝ] f4SimpleE 0 + Complex.I ⊗ₜ[ℝ] f4SimpleH 1
    let uO := h3OctonionF4DerivationsBaseChangeEquiv.symm uZ
    let vO := h3OctonionF4DerivationsBaseChangeEquiv.symm vZ
    ⁅uZ, vZ⁆ ≠ 0 ∧ ⁅uO, vO⁆ ≠ 0 ∧
    ¬ IsLieAbelian (ℂ ⊗[ℝ] H3ZornF4Derivations) ∧
    ¬ IsLieAbelian (ℂ ⊗[ℝ] H3OctonionF4Derivations) := by
  intro uZ vZ uO vO
  have hbrZ : ⁅uZ, vZ⁆ = (2 : ℂ) • ((1 : ℂ) ⊗ₜ[ℝ] f4SimpleE 0) := by
    dsimp [uZ, vZ]
    rw [lie_add (L := ℂ ⊗[ℝ] H3ZornF4Derivations),
      LieAlgebra.ExtendScalars.bracket_tmul, LieAlgebra.ExtendScalars.bracket_tmul,
      f4SimpleH_comm 0 1, TensorProduct.tmul_zero, add_zero, one_mul, f4Simple_bracket_HE]
    have hc : Tag.cartan .F4 (0 : Fin 4) (0 : Fin 4) = 2 := by decide
    rw [hc, TensorProduct.tmul_smul, ← IsScalarTower.algebraMap_smul ℂ ((2 : ℤ) : ℝ)]
    simp
  have hneZ : ⁅uZ, vZ⁆ ≠ 0 := by
    rw [hbrZ]
    intro h0
    have hsm := (smul_eq_zero.mp h0).resolve_left (by norm_num)
    have hbas : (1 : ℂ) ⊗ₜ[ℝ] f4SimpleE 0 =
        (f4ChevalleyBasis.baseChange ℂ) (Sum.inr (f4ESimpleIdx 0)) := by
      simp [f4SimpleE, f4ESimpleSign]
    rw [hbas] at hsm
    exact (f4ChevalleyBasis.baseChange ℂ).ne_zero _ hsm
  have hneO : ⁅uO, vO⁆ ≠ 0 := by
    intro h0
    have h1 := congrArg h3OctonionF4DerivationsBaseChangeEquiv h0
    rw [LieEquiv.map_lie, h3OctonionF4DerivationsBaseChangeEquiv.apply_symm_apply,
      h3OctonionF4DerivationsBaseChangeEquiv.apply_symm_apply, map_zero] at h1
    exact hneZ h1
  exact ⟨hneZ, hneO, LieAlgebra.IsSimple.non_abelian ℂ, LieAlgebra.IsSimple.non_abelian ℂ⟩

theorem m2_f5_complex_e6_zero_and_self_bracket_vanish (x : ℂ ⊗[ℝ] h3OctonionCubicStabilizer) :
    h3OctonionCubicStabilizerBaseChangeEquiv 0 = 0 ∧
    h3OctonionCubicStabilizerBaseChangeEquiv.symm 0 = 0 ∧
    ⁅x, x⁆ = 0 ∧
    ⁅x, (0 : ℂ ⊗[ℝ] h3OctonionCubicStabilizer)⁆ = 0 ∧
    ⁅(0 : ℂ ⊗[ℝ] h3OctonionCubicStabilizer), x⁆ = 0 :=
  ⟨map_zero _, map_zero _, lie_self x, lie_zero x, zero_lie x⟩

theorem m2_f5_complex_f4_zero_and_self_bracket_vanish (x : ℂ ⊗[ℝ] H3OctonionF4Derivations) :
    h3OctonionF4DerivationsBaseChangeEquiv 0 = 0 ∧
    h3OctonionF4DerivationsBaseChangeEquiv.symm 0 = 0 ∧
    ⁅x, x⁆ = 0 ∧
    ⁅x, (0 : ℂ ⊗[ℝ] H3OctonionF4Derivations)⁆ = 0 ∧
    ⁅(0 : ℂ ⊗[ℝ] H3OctonionF4Derivations), x⁆ = 0 :=
  ⟨map_zero _, map_zero _, lie_self x, lie_zero x, zero_lie x⟩

theorem m2_f5_real_form_trace_sq_separation_vs_complex_iso (D : H3OctonionF4Derivations) :
    LinearMap.trace ℝ (H3Octonion ℝ) (D.1 * D.1) ≤ 0 ∧
    0 < LinearMap.trace ℝ (H3Zorn ℝ) (splitF4TracePosWitness.1 * splitF4TracePosWitness.1) ∧
    Nonempty (ℂ ⊗[ℝ] H3OctonionF4Derivations ≃ₗ⁅ℂ⁆ ℂ ⊗[ℝ] H3ZornF4Derivations) ∧
    Nonempty (ℂ ⊗[ℝ] h3OctonionCubicStabilizer ≃ₗ⁅ℂ⁆ ℂ ⊗[ℝ] h3zornCubicStabilizer) :=
  ⟨compactF4_trace_sq_nonpos D, splitF4TracePosWitness_trace_sq_pos,
    ⟨h3OctonionF4DerivationsBaseChangeEquiv⟩, ⟨h3OctonionCubicStabilizerBaseChangeEquiv⟩⟩

/-! ## `[M2-CONTRACT]` Feature 6: Simplicity of `F₄(4)`, `E₆(-26)`, `F₄(-52)` — Tier 1 Happy-Path -/

theorem m2_f6_split_f4_isSimple_semisimple_center :
    LieAlgebra.IsSimple ℝ H3ZornF4Derivations ∧
    LieAlgebra.IsSemisimple ℝ H3ZornF4Derivations ∧
    LieAlgebra.HasTrivialRadical ℝ H3ZornF4Derivations ∧
    LieAlgebra.center ℝ H3ZornF4Derivations = ⊥ :=
  ⟨h3ZornF4Derivations_isSimple, h3ZornF4Derivations_isSemisimple,
    h3ZornF4Derivations_hasTrivialRadical, center_h3ZornF4Derivations_eq_bot⟩

theorem m2_f6_split_f4_cartan_and_roots :
    f4Cartan.IsCartanSubalgebra ∧
    Module.finrank ℝ f4Cartan = 4 ∧
    Fintype.card {v : Fin (Tag.rank .F4) → ℤ // IsRoot .F4 v} = 48 ∧
    Function.Bijective f4RootEquiv ∧
    Module.finrank ℝ H3ZornF4Derivations = 52 := by
  refine ⟨f4Cartan_isCartanSubalgebra, finrank_f4Cartan, card_isRoot .F4,
    f4RootEquiv.bijective, ?_⟩
  rw [Module.finrank_eq_card_basis f4ChevalleyBasis, Fintype.card_sum,
    Fintype.card_fin, Fintype.card_fin]

theorem m2_f6_split_f4_chevalleyBasis_generators (i : Fin 4) (r : Fin 48) :
    f4ChevalleyBasis (Sum.inl i) = f4SimpleH i ∧
    f4ChevalleyBasis (Sum.inr r) = f4RootVec r ∧
    ⁅f4SimpleH i, f4RootVec r⁆ = (f4RootEigenvalue i r : ℝ) • f4RootVec r ∧
    ⁅f4SimpleE i, f4SimpleF i⁆ = f4SimpleH i :=
  ⟨f4ChevalleyBasis_inl i, f4ChevalleyBasis_inr r, f4RootVec_bracket_H i r,
    f4Simple_bracket_EF_same i⟩

theorem m2_f6_compact_e6_isSimple_semisimple_center :
    LieAlgebra.IsSimple ℝ h3OctonionCubicStabilizer ∧
    LieAlgebra.IsSemisimple ℝ h3OctonionCubicStabilizer ∧
    LieAlgebra.HasTrivialRadical ℝ h3OctonionCubicStabilizer ∧
    LieAlgebra.center ℝ h3OctonionCubicStabilizer = ⊥ :=
  ⟨h3OctonionCubicStabilizer_isSimple, h3OctonionCubicStabilizer_isSemisimple,
    h3OctonionCubicStabilizer_hasTrivialRadical, center_h3OctonionCubicStabilizer_eq_bot⟩

theorem m2_f6_compact_f4_isSimple_semisimple_center :
    LieAlgebra.IsSimple ℝ H3OctonionF4Derivations ∧
    LieAlgebra.IsSemisimple ℝ H3OctonionF4Derivations ∧
    LieAlgebra.HasTrivialRadical ℝ H3OctonionF4Derivations ∧
    LieAlgebra.center ℝ H3OctonionF4Derivations = ⊥ :=
  ⟨h3OctonionF4Derivations_isSimple, h3OctonionF4Derivations_isSemisimple,
    h3OctonionF4Derivations_hasTrivialRadical, center_h3OctonionF4Derivations_eq_bot⟩

/-! ## `[M2-CONTRACT]` Feature 6: Simplicity of `F₄(4)`, `E₆(-26)`, `F₄(-52)` — Tier 2 Boundary & Non-Abelian -/

theorem m2_f6_all_three_nonabelian_and_matrix27_witness :
    (∃ A B : Matrix (Fin 27) (Fin 27) ℝ, A * B ≠ B * A) ∧
    ¬ IsLieAbelian H3ZornF4Derivations ∧
    ¬ IsLieAbelian h3OctonionCubicStabilizer ∧
    ¬ IsLieAbelian H3OctonionF4Derivations ∧
    ⁅f4SimpleH 0, f4SimpleE 0⁆ ≠ 0 := by
  refine ⟨f4_matrix27_real_noncomm_witness, LieAlgebra.IsSimple.non_abelian ℝ,
    LieAlgebra.IsSimple.non_abelian ℝ, LieAlgebra.IsSimple.non_abelian ℝ, ?_⟩
  rw [f4Simple_bracket_HE]
  have hc : Tag.cartan .F4 (0 : Fin 4) (0 : Fin 4) = 2 := by decide
  rw [hc]
  intro h0
  have he := (smul_eq_zero.mp h0).resolve_left (by norm_num)
  dsimp [f4SimpleE, f4ESimpleSign] at he
  norm_num at he
  exact f4RootVec_ne_zero (f4ESimpleIdx 0) he

theorem m2_f6_compact_f4_and_e6_concrete_noncomm_brackets :
    let e0 := CompactOctonion.basisVec 0
    let e1 := CompactOctonion.basisVec 1
    let e2 := CompactOctonion.basisVec 2
    let d1 : H3OctonionF4Derivations :=
      h3OctonionJordanInnerDerivation (H3Octonion.embedJ12 e0) (H3Octonion.embedJ12 e1)
    let d2 : H3OctonionF4Derivations :=
      h3OctonionJordanInnerDerivation (H3Octonion.embedJ12 e1) (H3Octonion.embedJ12 e2)
    let e1_lie : h3OctonionCubicStabilizer :=
      ⟨d1.1, H3OctonionF4Derivations_le_h3OctonionCubicStabilizer d1.2⟩
    let e2_lie : h3OctonionCubicStabilizer :=
      ⟨d2.1, H3OctonionF4Derivations_le_h3OctonionCubicStabilizer d2.2⟩
    ⁅d1, d2⁆ ≠ 0 ∧ ⁅e1_lie, e2_lie⁆ ≠ 0 := by
  intro e0 e1 e2 d1 d2 e1_lie e2_lie
  have hb10 : CompactOctonion.bilin e1 e0 = 0 :=
    (CompactOctonion.bilin_basis 1 0).trans (by simp)
  have hb20 : CompactOctonion.bilin e2 e0 = 0 :=
    (CompactOctonion.bilin_basis 2 0).trans (by simp)
  have hb00 : CompactOctonion.bilin e0 e0 = 2 :=
    (CompactOctonion.bilin_basis 0 0).trans (by simp)
  have hb11 : CompactOctonion.bilin e1 e1 = 2 :=
    (CompactOctonion.bilin_basis 1 1).trans (by simp)
  have hb21 : CompactOctonion.bilin e2 e1 = 0 :=
    (CompactOctonion.bilin_basis 2 1).trans (by simp)
  have h_j12_mul : ∀ x y : CompactOctonion ℝ,
      H3Octonion.embedJ12 x * H3Octonion.embedJ12 y =
        ((1 / 2 : ℝ) * CompactOctonion.bilin x y) •
          (H3Octonion.diagCartan 1 0 0 + H3Octonion.diagCartan 0 1 0) := by
    intro x y
    rw [H3Octonion.mul_trace_formula]
    have hlt1 : H3Octonion.linearTrace (H3Octonion.embedJ12 x) = 0 := by
      simp [H3Octonion.linearTrace, H3Octonion.embedJ12]
    have hlt2 : H3Octonion.linearTrace (H3Octonion.embedJ12 y) = 0 := by
      simp [H3Octonion.linearTrace, H3Octonion.embedJ12]
    have hcr : H3Octonion.crossProduct (H3Octonion.embedJ12 x) (H3Octonion.embedJ12 y) =
        ⟨0, 0, -CompactOctonion.bilin x y, 0, 0, 0⟩ := by
      apply H3Octonion.ext_h3 <;>
        simp [H3Octonion.crossProduct, H3Octonion.embedJ12, CompactOctonion.bilin]
    rw [hlt1, hlt2, hcr]
    apply H3Octonion.ext_h3 <;>
      simp [H3Octonion.linearTrace, H3Octonion.diagCartan]
  have hd2_e0 : d2.1 (H3Octonion.embedJ12 e0) = 0 := by
    change H3Octonion.embedJ12 e1 * (H3Octonion.embedJ12 e2 * H3Octonion.embedJ12 e0) -
      H3Octonion.embedJ12 e2 * (H3Octonion.embedJ12 e1 * H3Octonion.embedJ12 e0) = 0
    rw [h_j12_mul e2 e0, h_j12_mul e1 e0, hb20, hb10]
    simp
  have hdiag12_mul : ∀ x : CompactOctonion ℝ,
      (H3Octonion.diagCartan 1 0 0 + H3Octonion.diagCartan 0 1 0) * H3Octonion.embedJ12 x =
        H3Octonion.embedJ12 x := by
    intro x
    rw [H3Octonion.mul_trace_formula]
    have hlt : H3Octonion.linearTrace (H3Octonion.diagCartan (1 : ℝ) 0 0 +
        H3Octonion.diagCartan 0 1 0) = 2 := by
      simp [H3Octonion.linearTrace, H3Octonion.diagCartan]; norm_num
    have hlt2 : H3Octonion.linearTrace (H3Octonion.embedJ12 x) = 0 := by
      simp [H3Octonion.linearTrace, H3Octonion.embedJ12]
    have hcr : H3Octonion.crossProduct (H3Octonion.diagCartan (1 : ℝ) 0 0 +
        H3Octonion.diagCartan 0 1 0) (H3Octonion.embedJ12 x) = 0 := by
      apply H3Octonion.ext_h3 <;>
        simp [H3Octonion.crossProduct, H3Octonion.diagCartan, H3Octonion.embedJ12]
    rw [hlt, hlt2, hcr]
    apply H3Octonion.ext_h3 <;>
      simp [H3Octonion.diagCartan, H3Octonion.embedJ12]
  have hd1_e0 : d1.1 (H3Octonion.embedJ12 e0) = -H3Octonion.embedJ12 e1 := by
    change H3Octonion.embedJ12 e0 * (H3Octonion.embedJ12 e1 * H3Octonion.embedJ12 e0) -
      H3Octonion.embedJ12 e1 * (H3Octonion.embedJ12 e0 * H3Octonion.embedJ12 e0) =
        -H3Octonion.embedJ12 e1
    rw [h_j12_mul e1 e0, h_j12_mul e0 e0, hb10, hb00]
    simp only [mul_zero, zero_smul, zero_sub]
    rw [show (1 / 2 : ℝ) * 2 = 1 by norm_num, one_smul, _root_.mul_comm (H3Octonion.embedJ12 e1),
      hdiag12_mul e1]
  have hd : ⁅d1, d2⁆ ≠ 0 := by
    intro h0
    have heval := congrArg
      (fun D : H3OctonionF4Derivations => (D.1 (H3Octonion.embedJ12 e0)).a.e2) h0
    have hcomp : ((⁅d1, d2⁆ : H3OctonionF4Derivations).1 (H3Octonion.embedJ12 e0)).a.e2 =
        (-1 : ℝ) := by
      change (d1.1 (d2.1 (H3Octonion.embedJ12 e0)) -
        d2.1 (d1.1 (H3Octonion.embedJ12 e0))).a.e2 = (-1 : ℝ)
      rw [hd2_e0, map_zero, zero_sub, hd1_e0, map_neg, neg_neg]
      rw [show (d2.1 (H3Octonion.embedJ12 e1)).a =
          (1 / 2 : ℝ) • (CompactOctonion.bilin e2 e1 • e1 - CompactOctonion.bilin e1 e1 • e2) from
        oct_inner12_embedJ12_a e1 e2 e1]
      rw [hb21, hb11]
      simp [e2, CompactOctonion.basisVec, sub_eq_add_neg]
    rw [hcomp] at heval
    simp at heval
  have he : ⁅e1_lie, e2_lie⁆ ≠ 0 := by
    intro h0
    apply hd
    apply Subtype.ext
    exact (congrArg Subtype.val h0 : (⁅e1_lie, e2_lie⁆ : h3OctonionCubicStabilizer).1 = 0)
  exact ⟨hd, he⟩

theorem m2_f6_split_f4_cartan_comm_and_offdiag_EF {i j : Fin 4} (hij : i ≠ j) :
    ⁅f4SimpleH i, f4SimpleH j⁆ = 0 ∧
    ⁅f4SimpleE i, f4SimpleF j⁆ = 0 ∧
    ⁅f4SimpleE i, f4SimpleF i⁆ = f4SimpleH i := by
  refine ⟨f4SimpleH_comm i j, ?_, f4Simple_bracket_EF_same i⟩
  have hchk : (List.finRange 4).all (fun a => (List.finRange 4).all (fun b =>
      if a = b then true else
        sparseZeroCheck (sparseComm (f4SimpleESparse a) (f4SimpleFSparse b)))) = true := by
    decide
  simp only [List.all_eq_true, List.mem_finRange, true_implies] at hchk
  have hijchk := hchk i j
  simp only [hij, ↓reduceIte] at hijchk
  apply Subtype.ext
  apply h3zornToMatrix.injective
  change h3zornToMatrix (⁅f4SimpleE i, f4SimpleF j⁆ : Module.End ℝ (H3Zorn ℝ)) =
    h3zornToMatrix (0 : Module.End ℝ (H3Zorn ℝ))
  rw [h3zornToMatrix_f4_lie, h3zornToMatrix_f4SimpleE, h3zornToMatrix_f4SimpleF, map_zero]
  have hcomm : (sparseToMat (f4SimpleESparse i)).map (Int.cast : ℤ → ℝ) *
        (sparseToMat (f4SimpleFSparse j)).map Int.cast -
      (sparseToMat (f4SimpleFSparse j)).map Int.cast *
        (sparseToMat (f4SimpleESparse i)).map Int.cast =
      (sparseToMat (sparseComm (f4SimpleESparse i) (f4SimpleFSparse j))).map Int.cast := by
    rw [sparseToMat_comm]
    ext a b; simp [Matrix.mul_apply]
  rw [hcomm, sparseToMat_eq_zero_of_sparseZeroCheck hijchk]
  ext a b; simp

theorem m2_f6_split_f4_rootVec_ne_zero_and_simple_EF (i : Fin 4) (r : Fin 48) :
    f4RootVec r ≠ 0 ∧
    f4SimpleE i ≠ 0 ∧
    f4SimpleF i ≠ 0 ∧
    f4SimpleH i ≠ 0 := by
  refine ⟨f4RootVec_ne_zero r, ?_, ?_, ?_⟩
  · intro h0
    have hsm := (smul_eq_zero.mp h0).resolve_left (Int.cast_ne_zero.mpr (by
      fin_cases i <;> decide : f4ESimpleSign i ≠ 0))
    exact f4RootVec_ne_zero (f4ESimpleIdx i) hsm
  · intro h0
    have hsm := (smul_eq_zero.mp h0).resolve_left (Int.cast_ne_zero.mpr (by
      fin_cases i <;> decide : f4FSimpleSign i ≠ 0))
    exact f4RootVec_ne_zero (f4FSimpleIdx i) hsm
  · rw [← f4ChevalleyBasis_inl i]
    exact f4ChevalleyBasis.ne_zero (Sum.inl i)

theorem m2_f6_split_f4_bracket_HE_HF_and_height (i j : Fin 4) (r : Fin 48) :
    ⁅f4SimpleH i, f4SimpleE j⁆ = ((Tag.cartan .F4 i j : ℤ) : ℝ) • f4SimpleE j ∧
    ⁅f4SimpleH i, f4SimpleF j⁆ = (-(Tag.cartan .F4 i j : ℤ) : ℝ) • f4SimpleF j ∧
    f4RootHeight r ≠ 0 ∧ -11 ≤ f4RootHeight r ∧ f4RootHeight r ≤ 11 :=
  ⟨f4Simple_bracket_HE i j, f4Simple_bracket_HF i j, f4RootHeight_bounds r⟩

theorem m2_f6_simple_ideals_dichotomy
    (I_f4 : LieIdeal ℝ H3ZornF4Derivations)
    (I_ce6 : LieIdeal ℝ h3OctonionCubicStabilizer)
    (I_cf4 : LieIdeal ℝ H3OctonionF4Derivations) :
    (I_f4 = ⊥ ∨ I_f4 = ⊤) ∧
    (I_ce6 = ⊥ ∨ I_ce6 = ⊤) ∧
    (I_cf4 = ⊥ ∨ I_cf4 = ⊤) ∧
    (⊥ : LieIdeal ℝ H3ZornF4Derivations) ≠ ⊤ ∧
    (⊥ : LieIdeal ℝ h3OctonionCubicStabilizer) ≠ ⊤ ∧
    (⊥ : LieIdeal ℝ H3OctonionF4Derivations) ≠ ⊤ :=
  ⟨h3ZornF4Derivations_isSimple.eq_bot_or_eq_top I_f4,
    h3OctonionCubicStabilizer_isSimple.eq_bot_or_eq_top I_ce6,
    h3OctonionF4Derivations_isSimple.eq_bot_or_eq_top I_cf4,
    bot_ne_top, bot_ne_top, bot_ne_top⟩

end M2Contract

section M3GroupGenerationAndBruhat

/-! ## `[M3-CONTRACT]` Feature 7: `E₆(6)` Chevalley Generation & Bruhat Closure — Tier 1 Happy-Path -/

private noncomputable def m3NondiagNormOneX : H3Zorn ℝ :=
  ⟨1, 2, 1, ZornVectorMatrix.one, ZornVectorMatrix.zero, ZornVectorMatrix.zero⟩

private theorem m3NondiagNormOneX_normCubic : H3Zorn.normCubic m3NondiagNormOneX = 1 := by
  simp [H3Zorn.normCubic, m3NondiagNormOneX, ZornVectorMatrix.norm, ZornVectorMatrix.trace,
    ZornVectorMatrix.mul, ZornVectorMatrix.one, ZornVectorMatrix.zero, ZornVec3.dot]
  norm_num

private theorem m3NondiagNormOneX_norm_ne_zero : H3Zorn.normCubic m3NondiagNormOneX ≠ 0 := by
  rw [m3NondiagNormOneX_normCubic]
  norm_num

private noncomputable def m3NondiagIdemE : H3Zorn ℝ :=
  (1 / 2 : ℝ) • (h3_diag₁ + h3_diag₂ + embedJ12 ZornVectorMatrix.one)

private theorem m3_diag1_isRankOne : isRankOneIdem h3_diag₁ := by
  refine ⟨h3_diag₁_mul_h3_diag₁, ?_, ?_⟩
  · simp [h3_diag₁, H3Zorn.linearTrace]
  · apply H3Zorn.ext_h3 <;>
      simp [H3Zorn.adjointQuad, h3_diag₁, ZornVectorMatrix.zero, ZornVectorMatrix.norm,
        ZornVectorMatrix.mul, ZornVectorMatrix.conj, ZornVectorMatrix.add,
        ZornVectorMatrix.sub, ZornVectorMatrix.smul, ZornVectorMatrix.neg, ZornVec3.dot]

private theorem m3NondiagIdemE_isRankOne : isRankOneIdem m3NondiagIdemE := by
  have hbilin : zornBilin ZornVectorMatrix.one ZornVectorMatrix.one = 2 := by
    simp [zornBilin, ZornVectorMatrix.one,
      ZornVectorMatrix.mul, ZornVectorMatrix.conj, ZornVectorMatrix.trace, ZornVec3.dot]
    norm_num
  have hsum : h3_diag₁ + h3_diag₂ + embedJ12 ZornVectorMatrix.one =
      ({ α₁ := 1, α₂ := 1, α₃ := 0, a := ZornVectorMatrix.one,
         b := ZornVectorMatrix.zero, c := ZornVectorMatrix.zero } : H3Zorn ℝ) := by
    apply H3Zorn.ext_h3 <;> simp [h3_diag₁, h3_diag₂, embedJ12, ZornVectorMatrix.add_zero]
  refine ⟨?_, ?_, ?_⟩
  · dsimp [m3NondiagIdemE]
    rw [smul_mul_smul_comm]
    simp only [add_mul, mul_add, h3_diag₁_mul_h3_diag₁, h3_diag₁_mul_h3_diag₂,
      h3_diag₂_mul_h3_diag₂, h3_diag₁_mul_embedJ12, h3_diag₂_mul_embedJ12,
      embedJ12_mul_embedJ12, hbilin]
    rw [mul_comm h3_diag₂ h3_diag₁, h3_diag₁_mul_h3_diag₂,
      mul_comm (embedJ12 ZornVectorMatrix.one) h3_diag₁, h3_diag₁_mul_embedJ12,
      mul_comm (embedJ12 ZornVectorMatrix.one) h3_diag₂, h3_diag₂_mul_embedJ12]
    module
  · dsimp [m3NondiagIdemE]
    rw [hsum]
    simp [H3Zorn.linearTrace, H3Zorn.smul_readback]
    norm_num
  · dsimp [m3NondiagIdemE]
    rw [H3Zorn.adjointQuad_smul, hsum]
    have hadj0 : H3Zorn.adjointQuad
        ({ α₁ := 1, α₂ := 1, α₃ := 0, a := ZornVectorMatrix.one,
           b := ZornVectorMatrix.zero, c := ZornVectorMatrix.zero } : H3Zorn ℝ) = 0 := by
      apply H3Zorn.ext_h3
      · simp [H3Zorn.adjointQuad, ZornVectorMatrix.zero, ZornVectorMatrix.norm, ZornVec3.dot]
      · simp [H3Zorn.adjointQuad, ZornVectorMatrix.zero, ZornVectorMatrix.norm, ZornVec3.dot]
      · simp [H3Zorn.adjointQuad, ZornVectorMatrix.one, ZornVectorMatrix.norm, ZornVec3.dot]
      · ext i <;> simp [H3Zorn.adjointQuad, ZornVectorMatrix.zero, ZornVectorMatrix.one,
          ZornVectorMatrix.sub, ZornVectorMatrix.smul, ZornVectorMatrix.add,
          ZornVectorMatrix.mul, ZornVectorMatrix.conj, ZornVectorMatrix.neg, ZornVec3.dot]
      · ext i <;> simp [H3Zorn.adjointQuad, ZornVectorMatrix.zero, ZornVectorMatrix.one,
          ZornVectorMatrix.sub, ZornVectorMatrix.smul, ZornVectorMatrix.add,
          ZornVectorMatrix.mul, ZornVectorMatrix.conj, ZornVectorMatrix.neg, ZornVec3.dot]
      · ext i <;> simp [H3Zorn.adjointQuad, ZornVectorMatrix.zero, ZornVectorMatrix.one,
          ZornVectorMatrix.sub, ZornVectorMatrix.smul, ZornVectorMatrix.add,
          ZornVectorMatrix.mul, ZornVectorMatrix.conj, ZornVectorMatrix.neg, ZornVec3.dot]
    rw [hadj0, smul_zero]
    rfl

theorem m3_chevalley_eq_top_and_simple_closure (g : h3zornReducedStructureGroup) :
    h3zornChevalleyE6 = ⊤ ∧
    h3zornChevalleyE6 = e6ChevalleySubgroup ∧
    e6ChevalleySubgroup = ⊤ ∧
    h3zornChevalleyE6 = h3zornSimpleClosure ∧
    h3zornSimpleClosure =
      Subgroup.closure ({ x | ∃ (i : Fin 6) (c : ℝ), x = h3zornSimpleX i c } ∪
        { x | ∃ (i : Fin 6) (c : ℝ), x = h3zornSimpleY i c }) ∧
    g ∈ h3zornChevalleyE6 :=
  ⟨h3zornChevalleyE6_eq_top, h3zornChevalleyE6_eq_e6ChevalleySubgroup, e6ChevalleySubgroup_eq_top,
    h3zornChevalleyE6_eq_simpleClosure, h3zornSimpleClosure_eq_closure_simple,
    by rw [h3zornChevalleyE6_eq_top]; trivial⟩

theorem m3_transitivity_normCubic_one_and_rankOneIdem (X e₁ e₂ : H3Zorn ℝ)
    (hX : H3Zorn.normCubic X = 1) (he₁ : isRankOneIdem e₁) (he₂ : isRankOneIdem e₂) :
    (∃ h ∈ h3zornChevalleyE6, h.1 X = 1) ∧
    (∃ h ∈ h3zornChevalleyE6, h.1 1 = X) ∧
    (∃ g ∈ h3zornChevalleyE6, g.1 e₁ = e₂) ∧
    (∃ h ∈ h3zornChevalleyE6, h.1 m3NondiagNormOneX = 1) ∧
    (∃ h ∈ h3zornChevalleyE6, h.1 1 = m3NondiagNormOneX) ∧
    (∃ g ∈ h3zornChevalleyE6, g.1 m3NondiagIdemE = h3_diag₁) :=
  ⟨h3zornChevalleyE6_move_normCubic_one_to_one X hX,
    h3zornChevalleyE6_transitive_normCubic_one X hX,
    h3zornChevalleyE6_transitive_rankOneIdempotent e₁ e₂ he₁ he₂,
    h3zornChevalleyE6_move_normCubic_one_to_one m3NondiagNormOneX m3NondiagNormOneX_normCubic,
    h3zornChevalleyE6_transitive_normCubic_one m3NondiagNormOneX m3NondiagNormOneX_normCubic,
    h3zornChevalleyE6_transitive_rankOneIdempotent m3NondiagIdemE h3_diag₁
      m3NondiagIdemE_isRankOne m3_diag1_isRankOne⟩

theorem m3_aut_and_ULinearEquiv_mem_chevalley
    (f : h3zornReducedStructureGroup) (hf : f.1 1 = 1) (A : H3ZornJordanAut)
    (X Y : H3Zorn ℝ) (hNX : H3Zorn.normCubic X ≠ 0)
    (hpm : H3Zorn.normCubic X = 1 ∨ H3Zorn.normCubic X = -1)
    (hNY : H3Zorn.normCubic Y ≠ 0) (h1 : H3Zorn.normCubic Y = 1) :
    f ∈ h3zornChevalleyE6 ∧
    (⟨A.toLinearEquiv, A.mem_reducedStructureGroup⟩ : h3zornReducedStructureGroup) ∈
      h3zornChevalleyE6 ∧
    (⟨h3zornULinearEquiv X hNX, h3zornULinearEquiv_mem_reducedStructureGroup X hNX hpm⟩ :
      h3zornReducedStructureGroup) ∈ h3zornChevalleyE6 ∧
    (⟨h3zornULinearEquiv Y hNY, h3zornULinearEquiv_mem_reducedStructureGroup Y hNY (Or.inl h1)⟩ :
      h3zornReducedStructureGroup) ∈ h3zornChevalleyE6 :=
  ⟨h3zornReducedStructureFixOne_le_chevalleyE6 hf,
    h3zornJordanAut_mem_chevalleyE6 A,
    h3zornULinearEquiv_mem_chevalleyE6 X hNX hpm,
    h3zornULinearEquiv_one_mem_chevalleyE6 Y hNY h1⟩

theorem m3_bruhat_and_borel_decomposition (g b : h3zornReducedStructureGroup) (r : Fin 72) :
    (∃ b₁ ∈ h3zornBorel, ∃ w ∈ h3zornWeylSubgroup, ∃ b₂ ∈ h3zornBorel, g = b₁ * w * b₂) ∧
    (b ∈ h3zornBorel ↔ ∃ t ∈ h3zornTorus, ∃ u ∈ h3zornPosUnipotent, b = t * u) ∧
    h3zornTorus =
      Subgroup.closure { x | ∃ (i : Fin 6) (t : ℝˣ), x = h3zornTorusElt i t } ∧
    h3zornWeylSubgroup = Subgroup.closure (Set.range fun i : Fin 6 => h3zornWeylElt i 1) ∧
    h3zornRootSubgroup r =
      Subgroup.closure (Set.range fun c : ℝ => h3zornRootSubgroupHom r (Multiplicative.ofAdd c)) :=
  ⟨h3zornBruhat_decomposition g,
    h3zornBorel_eq_torus_mul_posUnipotent b,
    h3zornTorus_eq_closure_torusElt,
    h3zornWeylSubgroup_eq_closure_weylElt,
    h3zornRootSubgroup_eq_closure_hom r⟩

theorem m3_adjoint_action_injective (g₁ g₂ : h3zornReducedStructureGroup)
    (X Y : h3zornCubicStabilizer) :
    Function.Injective h3zornAdjointAction ∧
    (h3zornAdjointAction g₁ = h3zornAdjointAction g₂ → g₁ = g₂) ∧
    h3zornAdjointAction g₁ ⁅X, Y⁆ = ⁅h3zornAdjointAction g₁ X, h3zornAdjointAction g₁ Y⁆ :=
  ⟨h3zornAdjointAction_injective,
    fun h => h3zornAdjointAction_injective h,
    LieEquiv.map_lie (h3zornAdjointAction g₁) X Y⟩

/-! ## `[M3-CONTRACT]` Feature 7: `E₆(6)` Chevalley & Bruhat — Tier 2 Boundary, Disjointness & Separation -/

theorem m3_subgroup_disjointness_corners (g : h3zornReducedStructureGroup) :
    h3zornTorus ⊓ h3zornPosUnipotent = ⊥ ∧
    h3zornBorel ⊓ h3zornNegUnipotent = ⊥ ∧
    h3zornPosUnipotent ⊓ h3zornNegUnipotent = ⊥ ∧
    (g ∈ h3zornTorus → g ∈ h3zornPosUnipotent → g = 1) ∧
    (g ∈ h3zornBorel → g ∈ h3zornNegUnipotent → g = 1) :=
  ⟨h3zornTorus_inf_posUnipotent_eq_bot,
    h3zornBorel_inf_negUnipotent_eq_bot,
    h3zornPosUnipotent_inf_negUnipotent_eq_bot,
    fun ht hu => (Subgroup.eq_bot_iff_forall _).mp h3zornTorus_inf_posUnipotent_eq_bot g ⟨ht, hu⟩,
    fun hb hn => (Subgroup.eq_bot_iff_forall _).mp h3zornBorel_inf_negUnipotent_eq_bot g ⟨hb, hn⟩⟩

theorem m3_concrete_nondiag_U_in_chevalley_moves_one :
    let uPos : h3zornReducedStructureGroup :=
      ⟨h3zornULinearEquiv m3NondiagNormOneX m3NondiagNormOneX_norm_ne_zero,
        h3zornULinearEquiv_mem_reducedStructureGroup m3NondiagNormOneX
          m3NondiagNormOneX_norm_ne_zero (Or.inl m3NondiagNormOneX_normCubic)⟩
    m3NondiagNormOneX ≠ 1 ∧
    uPos ∈ h3zornChevalleyE6 ∧
    uPos ∉ h3zornReducedStructureFixOne ∧
    uPos.1 1 ≠ 1 ∧
    h3zornReducedStructureFixOne < h3zornChevalleyE6 := by
  intro uPos
  have hx_ne : m3NondiagNormOneX ≠ 1 := by
    intro h
    have ha := congrArg (fun W : H3Zorn ℝ => W.a.a) h
    have h1 : (1 : H3Zorn ℝ).a.a = 0 := rfl
    rw [h1] at ha
    change (1 : ℝ) = 0 at ha
    norm_num at ha
  have hu_mem : uPos ∈ h3zornChevalleyE6 :=
    h3zornULinearEquiv_one_mem_chevalleyE6 m3NondiagNormOneX
      m3NondiagNormOneX_norm_ne_zero m3NondiagNormOneX_normCubic
  have hu_one : uPos.1 1 ≠ 1 := by
    intro h
    have hU : H3Zorn.U m3NondiagNormOneX 1 = 1 := by
      simpa [uPos, h3zornULinearEquiv_apply] using h
    have h1eq : (1 : H3Zorn ℝ) =
        ⟨1, 1, 1, ZornVectorMatrix.zero, ZornVectorMatrix.zero, ZornVectorMatrix.zero⟩ := rfl
    rw [h1eq] at hU
    have ha := congrArg (fun W : H3Zorn ℝ => W.a.a) hU
    simp [H3Zorn.U, H3Zorn.traceBilin, H3Zorn.crossProduct, H3Zorn.adjointQuad,
      m3NondiagNormOneX, ZornVectorMatrix.mul, ZornVectorMatrix.conj,
      ZornVectorMatrix.trace, ZornVectorMatrix.norm, ZornVectorMatrix.one, ZornVectorMatrix.zero,
      ZornVectorMatrix.add, ZornVectorMatrix.sub, ZornVectorMatrix.smul, ZornVectorMatrix.neg,
      ZornVec3.dot] at ha
    change (1 + 2 + 1 : ℝ) * 1 - (2 - (2 - 1) - 0) = 0 at ha
    norm_num at ha
  have hu_not_fix : uPos ∉ h3zornReducedStructureFixOne := fun hf => hu_one hf
  have hle : h3zornReducedStructureFixOne ≤ h3zornChevalleyE6 :=
    fun f hf => h3zornReducedStructureFixOne_le_chevalleyE6 hf
  exact ⟨hx_ne, hu_mem, hu_not_fix, hu_one, lt_of_le_of_ne hle (fun heq => hu_not_fix (heq ▸ hu_mem))⟩

private def m3WeightHeight (k : Fin 27) : ℕ :=
  ![8, 8, 8, 16, 5, 6, 7, 11, 10, 9, 0, 1, 4, 5, 6, 12, 11, 10, 15, 7, 12, 13, 14, 4, 3, 2, 9] k

private theorem m3_torusElt_inv (j : Fin 6) (t : ℝˣ) :
    (h3zornTorusElt j t)⁻¹ = h3zornTorusElt j t⁻¹ := by
  rw [h3zornTorusElt_eq_e6TorusElt, h3zornTorusElt_eq_e6TorusElt]
  apply inv_eq_of_mul_eq_one_left
  apply Subtype.ext
  apply LinearEquiv.toLinearMap_injective
  change (e6TorusElt j t⁻¹).1.toLinearMap.comp (e6TorusElt j t).1.toLinearMap = LinearMap.id
  apply h3ZornBasis.ext
  intro k
  simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, LinearMap.id_apply]
  rw [e6TorusElt_apply_basis, map_smul, e6TorusElt_apply_basis, smul_smul,
    Units.val_zpow_eq_zpow_val, Units.val_zpow_eq_zpow_val, Units.val_inv_eq_inv_val, inv_zpow,
    mul_inv_cancel₀ (zpow_ne_zero _ t.ne_zero), one_smul]

private theorem m3_torus_diag (t : h3zornReducedStructureGroup) (ht : t ∈ h3zornTorus) :
    ∀ a b : Fin 27, a ≠ b → h3zornToMatrix t.1.toLinearMap a b = 0 := by
  let D : Submonoid h3zornReducedStructureGroup :=
    { carrier := { x | ∀ a b : Fin 27, a ≠ b → h3zornToMatrix x.1.toLinearMap a b = 0 }
      one_mem' := fun a b hab => by
        change h3zornToMatrix (1 : Module.End ℝ (H3Zorn ℝ)) a b = 0
        rw [_root_.map_one, Matrix.one_apply_ne hab]
      mul_mem' := fun {x y} hx hy a b hab => by
        change h3zornToMatrix (x.1.toLinearMap * y.1.toLinearMap) a b = 0
        rw [_root_.map_mul, Matrix.mul_apply]
        refine Finset.sum_eq_zero fun k _ => ?_
        by_cases hak : a = k
        · subst hak; rw [hy a b hab, mul_zero]
        · rw [hx a k hak, zero_mul] }
  let H : Subgroup h3zornReducedStructureGroup :=
    { carrier := { x | x ∈ D ∧ x⁻¹ ∈ D }
      one_mem' := ⟨D.one_mem, by simp [D.one_mem]⟩
      mul_mem' := fun {x y} hx hy => ⟨D.mul_mem hx.1 hy.1, by rw [mul_inv_rev]; exact D.mul_mem hy.2 hx.2⟩
      inv_mem' := fun {x} hx => ⟨hx.2, by simp [hx.1]⟩ }
  have hgen : ∀ (i : Fin 6) (s : ℝˣ), h3zornTorusElt i s ∈ D := by
    intro i s a b hab
    rw [h3zornToMatrix_apply]
    change h3ZornBasis.repr ((h3zornTorusElt i s).1 (h3ZornBasis b)) a = 0
    rw [h3zornTorusElt_eq_e6TorusElt, e6TorusElt_apply_basis, map_smul, Finsupp.smul_apply,
      h3ZornBasis.repr_self, Finsupp.single_apply]
    simp [hab.symm]
  have hle : h3zornTorus ≤ H := by
    rw [h3zornTorus_eq_closure_torusElt, Subgroup.closure_le]
    rintro _ ⟨i, s, rfl⟩
    refine ⟨hgen i s, ?_⟩
    rw [m3_torusElt_inv]
    exact hgen i s⁻¹
  exact (hle ht).1

private theorem m3_posUnipotent_height_tri (u : h3zornReducedStructureGroup)
    (hu : u ∈ h3zornPosUnipotent) :
    ∀ a b : Fin 27, m3WeightHeight a < m3WeightHeight b →
      h3zornToMatrix u.1.toLinearMap a b = 0 := by
  let M : Submonoid h3zornReducedStructureGroup :=
    { carrier := { x | ∀ a b : Fin 27, m3WeightHeight a < m3WeightHeight b →
        h3zornToMatrix x.1.toLinearMap a b = 0 }
      one_mem' := fun a b hab => by
        have hne : a ≠ b := fun h => by subst h; exact Nat.lt_irrefl _ hab
        change h3zornToMatrix (1 : Module.End ℝ (H3Zorn ℝ)) a b = 0
        rw [_root_.map_one, Matrix.one_apply_ne hne]
      mul_mem' := fun {x y} hx hy a b hab => by
        change h3zornToMatrix (x.1.toLinearMap * y.1.toLinearMap) a b = 0
        rw [_root_.map_mul, Matrix.mul_apply]
        refine Finset.sum_eq_zero fun k _ => ?_
        by_cases hak : m3WeightHeight a < m3WeightHeight k
        · rw [hx a k hak, zero_mul]
        · have hkb : m3WeightHeight k < m3WeightHeight b :=
            lt_of_le_of_lt (Nat.le_of_not_lt hak) hab
          rw [hy k b hkb, mul_zero] }
  let H : Subgroup h3zornReducedStructureGroup :=
    { carrier := { x | x ∈ M ∧ x⁻¹ ∈ M }
      one_mem' := ⟨M.one_mem, by simp [M.one_mem]⟩
      mul_mem' := fun {x y} hx hy => ⟨M.mul_mem hx.1 hy.1, by rw [mul_inv_rev]; exact M.mul_mem hy.2 hx.2⟩
      inv_mem' := fun {x} hx => ⟨hx.2, by simp [hx.1]⟩ }
  have hchk : ∀ r : Fin 72, ∀ p ∈ e6RootSparse r,
      e6IsPosRoot r = true → m3WeightHeight p.2.1 < m3WeightHeight p.1 := by
    have hall : (List.finRange 72).all (fun r =>
        if e6IsPosRoot r then
          (e6RootSparse r).all (fun p => decide (m3WeightHeight p.2.1 < m3WeightHeight p.1))
        else true) = true := by
      decide
    intro r p hp hpos
    simp only [List.all_eq_true, List.mem_finRange, true_implies] at hall
    have hr := hall r
    simp only [hpos, ↓reduceIte, List.all_eq_true, decide_eq_true_eq] at hr
    exact hr p hp
  have hgen : ∀ (r : Fin 72) (hpos : e6IsPosRoot r = true) (c : ℝ), e6RootExp r c ∈ M := by
    intro r hpos c a b hab
    have hne : a ≠ b := fun h => by subst h; exact Nat.lt_irrefl _ hab
    change h3zornToMatrix ((1 : Module.End ℝ (H3Zorn ℝ)) + c • (e6RootVec r).1) a b = 0
    rw [map_add, _root_.map_one, map_smul, h3zornToMatrix_e6RootVec]
    simp only [Matrix.add_apply, Matrix.one_apply_ne hne, Matrix.smul_apply, Matrix.map_apply,
      smul_eq_mul, zero_add]
    have hsp : sparseVal (e6RootSparse r) a b = 0 := by
      have hL : ∀ p ∈ e6RootSparse r, m3WeightHeight p.2.1 < m3WeightHeight p.1 :=
        fun p hp => hchk r p hp hpos
      generalize e6RootSparse r = L at hL ⊢
      induction L with
      | nil => rfl
      | cons p t ih =>
        rw [sparseVal_cons]
        by_cases hp : (p.1 == a && p.2.1 == b) = true
        · simp only [Bool.and_eq_true, beq_iff_eq] at hp
          have hlt := hL p List.mem_cons_self
          rw [hp.1, hp.2] at hlt
          exact absurd (lt_trans hlt hab) (Nat.lt_irrefl _)
        · have hp' : (p.1 == a && p.2.1 == b) = false := Bool.eq_false_iff.mpr hp
          rw [hp']
          simp only [Bool.false_eq_true, ite_false, zero_add]
          exact ih (fun q hq => hL q (List.mem_cons_of_mem _ hq))
    change c * (sparseVal (e6RootSparse r) a b : ℝ) = 0
    rw [hsp, Int.cast_zero, mul_zero]
  have hle : h3zornPosUnipotent ≤ H := by
    change e6PosUnipotent ≤ H
    rw [e6PosUnipotent, Subgroup.closure_le]
    rintro _ ⟨r, hpos, c, rfl⟩
    refine ⟨hgen r hpos c, ?_⟩
    rw [e6RootExp_inv]
    exact hgen r hpos (-c)
  exact (hle hu).1

theorem m3_negative_root_and_weyl_not_in_borel :
    h3zornSimpleY 0 1 ∉ h3zornBorel ∧
    h3zornWeylElt 0 1 ∉ h3zornBorel ∧
    h3zornBorel ≠ ⊤ ∧
    h3zornChevalleyE6 ≠ h3zornBorel := by
  have hy_neg : h3zornSimpleY 0 1 ∈ h3zornNegUnipotent := by
    change e6SimpleY 0 1 ∈ e6NegUnipotent
    rw [e6SimpleY_eq_rootExp]
    exact Subgroup.subset_closure ⟨fSimpleIdx 0, by decide, (fSimpleSign 0 : ℝ) * 1, rfl⟩
  have hy_ne_one : h3zornSimpleY 0 1 ≠ 1 := by
    intro h
    have hmat := congrArg (fun g : h3zornReducedStructureGroup =>
      h3zornToMatrix g.1.toLinearMap 19 0) h
    have hL : h3zornToMatrix (h3zornSimpleY 0 1).1.toLinearMap 19 0 = 1 := by
      change h3zornToMatrix ((1 : Module.End ℝ (H3Zorn ℝ)) + (1 : ℝ) • (e6SimpleF 0).1) 19 0 = 1
      rw [map_add, _root_.map_one, map_smul, h3zornToMatrix_e6SimpleF]
      have h190 : sparseVal (e6SimpleFSparse 0) 19 0 = 1 := by decide
      simp [sparseToMat, h190]
    have hR : h3zornToMatrix (1 : h3zornReducedStructureGroup).1.toLinearMap 19 0 = 0 := by
      change h3zornToMatrix (1 : Module.End ℝ (H3Zorn ℝ)) 19 0 = 0
      rw [_root_.map_one, Matrix.one_apply_ne (by decide : (19 : Fin 27) ≠ 0)]
    rw [hL, hR] at hmat
    norm_num at hmat
  have hy_not_borel : h3zornSimpleY 0 1 ∉ h3zornBorel := by
    intro hb
    have h1 : h3zornSimpleY 0 1 = 1 :=
      (Subgroup.eq_bot_iff_forall _).mp h3zornBorel_inf_negUnipotent_eq_bot _ ⟨hb, hy_neg⟩
    exact hy_ne_one h1
  have hw_not_borel : h3zornWeylElt 0 1 ∉ h3zornBorel := by
    intro hb
    obtain ⟨t, ht, u, hu, htu⟩ := (h3zornBorel_eq_torus_mul_posUnipotent (h3zornWeylElt 0 1)).mp hb
    have hmat_tu : h3zornToMatrix (t * u).1.toLinearMap 19 0 = 0 := by
      change h3zornToMatrix (t.1.toLinearMap * u.1.toLinearMap) 19 0 = 0
      rw [_root_.map_mul, Matrix.mul_apply]
      refine Finset.sum_eq_zero fun k _ => ?_
      by_cases hk : (19 : Fin 27) = k
      · subst hk
        have hlt : m3WeightHeight 19 < m3WeightHeight 0 := by decide
        rw [m3_posUnipotent_height_tri u hu 19 0 hlt, mul_zero]
      · rw [m3_torus_diag t ht 19 k hk, zero_mul]
    have hmat_w : h3zornToMatrix (h3zornWeylElt 0 1).1.toLinearMap 19 0 = -1 := by
      rw [h3zornWeylElt_eq_e6WeylElt]
      have hw : e6WeylElt 0 1 = e6SimpleX 0 1 * e6SimpleY 0 (-1) * e6SimpleX 0 1 := by
        simp [e6WeylElt]
      rw [hw]
      have hX : h3zornToMatrix (e6SimpleX 0 1).1.toLinearMap =
          (1 : Matrix (Fin 27) (Fin 27) ℝ) + (sparseToMat (e6SimpleESparse 0)).map Int.cast := by
        change h3zornToMatrix ((1 : Module.End ℝ (H3Zorn ℝ)) + (1 : ℝ) • (e6SimpleE 0).1) = _
        rw [map_add, _root_.map_one, map_smul, h3zornToMatrix_e6SimpleE, one_smul]
      have hY : h3zornToMatrix (e6SimpleY 0 (-1)).1.toLinearMap =
          (1 : Matrix (Fin 27) (Fin 27) ℝ) - (sparseToMat (e6SimpleFSparse 0)).map Int.cast := by
        change h3zornToMatrix ((1 : Module.End ℝ (H3Zorn ℝ)) + (-1 : ℝ) • (e6SimpleF 0).1) = _
        rw [map_add, _root_.map_one, map_smul, h3zornToMatrix_e6SimpleF, neg_one_smul, sub_eq_add_neg]
      have hmul : h3zornToMatrix (e6SimpleX 0 1 * e6SimpleY 0 (-1) * e6SimpleX 0 1).1.toLinearMap =
          (((1 + sparseToMat (e6SimpleESparse 0)) * (1 - sparseToMat (e6SimpleFSparse 0)) *
            (1 + sparseToMat (e6SimpleESparse 0))).map Int.cast) := by
        change h3zornToMatrix ((e6SimpleX 0 1).1.toLinearMap *
          (e6SimpleY 0 (-1)).1.toLinearMap * (e6SimpleX 0 1).1.toLinearMap) = _
        rw [_root_.map_mul, _root_.map_mul, hX, hY]
        ext a b
        simp only [Matrix.mul_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.one_apply,
          Matrix.map_apply, Int.cast_sum, Int.cast_mul, Int.cast_add, Int.cast_sub,
          Int.cast_ite, Int.cast_one, Int.cast_zero]
      have hchk :
          ((1 + sparseToMat (e6SimpleESparse 0)) * (1 - sparseToMat (e6SimpleFSparse 0)) *
            (1 + sparseToMat (e6SimpleESparse 0))) 19 0 = -1 := by
        decide
      rw [hmul, Matrix.map_apply, hchk]
      norm_num
    rw [← htu, hmat_w] at hmat_tu
    norm_num at hmat_tu
  have hborel_ne_top : h3zornBorel ≠ ⊤ := fun h => hy_not_borel (h ▸ Subgroup.mem_top _)
  have hche_ne_borel : h3zornChevalleyE6 ≠ h3zornBorel := by
    intro h
    rw [h3zornChevalleyE6_eq_top] at h
    exact hborel_ne_top h.symm
  exact ⟨hy_not_borel, hw_not_borel, hborel_ne_top, hche_ne_borel⟩

theorem m3_group_nonabelian_and_nontrivial_corners (i : Fin 6) :
    h3zornChevalleyE6 ≠ ⊥ ∧
    h3zornBorel ≠ ⊥ ∧
    h3zornTorus ≠ ⊥ ∧
    h3zornPosUnipotent ≠ ⊥ ∧
    h3zornNegUnipotent ≠ ⊥ ∧
    h3zornWeylSubgroup ≠ ⊥ ∧
    h3zornSimpleX 0 1 * h3zornSimpleY 0 1 ≠ h3zornSimpleY 0 1 * h3zornSimpleX 0 1 ∧
    h3zornSimpleX i 0 = 1 ∧
    h3zornSimpleY i 0 = 1 ∧
    h3zornTorusElt i 1 = 1 := by
  have hx_ne : h3zornSimpleX 0 1 ≠ 1 := by
    intro h
    have hm := congrArg (fun g : h3zornReducedStructureGroup =>
      h3zornToMatrix g.1.toLinearMap 0 19) h
    have hL : h3zornToMatrix (h3zornSimpleX 0 1).1.toLinearMap 0 19 = 1 := by
      change h3zornToMatrix ((1 : Module.End ℝ (H3Zorn ℝ)) + (1 : ℝ) • (e6SimpleE 0).1) 0 19 = 1
      rw [map_add, _root_.map_one, map_smul, h3zornToMatrix_e6SimpleE]
      have h019 : sparseVal (e6SimpleESparse 0) 0 19 = 1 := by decide
      simp [sparseToMat, h019]
    have hR : h3zornToMatrix (1 : h3zornReducedStructureGroup).1.toLinearMap 0 19 = 0 := by
      change h3zornToMatrix (1 : Module.End ℝ (H3Zorn ℝ)) 0 19 = 0
      rw [_root_.map_one, Matrix.one_apply_ne (by decide : (0 : Fin 27) ≠ 19)]
    rw [hL, hR] at hm
    norm_num at hm
  have hy_ne : h3zornSimpleY 0 1 ≠ 1 := by
    intro h
    have hm := congrArg (fun g : h3zornReducedStructureGroup =>
      h3zornToMatrix g.1.toLinearMap 19 0) h
    have hL : h3zornToMatrix (h3zornSimpleY 0 1).1.toLinearMap 19 0 = 1 := by
      change h3zornToMatrix ((1 : Module.End ℝ (H3Zorn ℝ)) + (1 : ℝ) • (e6SimpleF 0).1) 19 0 = 1
      rw [map_add, _root_.map_one, map_smul, h3zornToMatrix_e6SimpleF]
      have h190 : sparseVal (e6SimpleFSparse 0) 19 0 = 1 := by decide
      simp [sparseToMat, h190]
    have hR : h3zornToMatrix (1 : h3zornReducedStructureGroup).1.toLinearMap 19 0 = 0 := by
      change h3zornToMatrix (1 : Module.End ℝ (H3Zorn ℝ)) 19 0 = 0
      rw [_root_.map_one, Matrix.one_apply_ne (by decide : (19 : Fin 27) ≠ 0)]
    rw [hL, hR] at hm
    norm_num at hm
  have htor_ne : h3zornTorusElt 0 (-1) ≠ 1 := by
    intro h
    have hv := congrArg (fun g : h3zornReducedStructureGroup =>
      h3ZornBasis.repr (g.1 (h3ZornBasis 0)) 0) h
    rw [h3zornTorusElt_eq_e6TorusElt, e6TorusElt_apply_basis] at hv
    have hw : h3zornWeight 0 0 = 1 := by decide
    rw [hw, zpow_one, map_smul, h3ZornBasis.repr_self] at hv
    simp at hv
    norm_num at hv
  have hx_pos : h3zornSimpleX 0 1 ∈ h3zornPosUnipotent := by
    change e6SimpleX 0 1 ∈ e6PosUnipotent
    rw [e6SimpleX_eq_rootExp]
    exact Subgroup.subset_closure ⟨eSimpleIdx 0, by decide, 1, rfl⟩
  have hy_neg : h3zornSimpleY 0 1 ∈ h3zornNegUnipotent := by
    change e6SimpleY 0 1 ∈ e6NegUnipotent
    rw [e6SimpleY_eq_rootExp]
    exact Subgroup.subset_closure ⟨fSimpleIdx 0, by decide, (fSimpleSign 0 : ℝ) * 1, rfl⟩
  have ht_mem : h3zornTorusElt 0 (-1) ∈ h3zornTorus := by
    rw [h3zornTorus_eq_closure_torusElt]
    exact Subgroup.subset_closure ⟨0, -1, rfl⟩
  have hpos_ne_bot : h3zornPosUnipotent ≠ ⊥ := fun h =>
    hx_ne ((Subgroup.eq_bot_iff_forall _).mp h _ hx_pos)
  have hneg_ne_bot : h3zornNegUnipotent ≠ ⊥ := fun h =>
    hy_ne ((Subgroup.eq_bot_iff_forall _).mp h _ hy_neg)
  have htor_ne_bot : h3zornTorus ≠ ⊥ := fun h =>
    htor_ne ((Subgroup.eq_bot_iff_forall _).mp h _ ht_mem)
  have hborel_ne_bot : h3zornBorel ≠ ⊥ := fun h =>
    htor_ne ((Subgroup.eq_bot_iff_forall _).mp h _
      ((h3zornBorel_eq_torus_mul_posUnipotent _).mpr ⟨_, ht_mem, 1, h3zornPosUnipotent.one_mem, by simp⟩))
  have hweyl_ne_bot : h3zornWeylSubgroup ≠ ⊥ := by
    intro h
    have hw0 : h3zornWeylElt 0 1 ∈ h3zornWeylSubgroup := by
      rw [h3zornWeylSubgroup_eq_closure_weylElt]
      exact Subgroup.subset_closure ⟨0, rfl⟩
    have hw1 := (Subgroup.eq_bot_iff_forall _).mp h _ hw0
    exact m3_negative_root_and_weyl_not_in_borel.2.1 (hw1 ▸ h3zornBorel.one_mem)
  have hche_ne_bot : h3zornChevalleyE6 ≠ ⊥ := fun h =>
    hx_ne ((Subgroup.eq_bot_iff_forall _).mp h _ (h3zornSimpleX_mem_chevalleyE6 0 1))
  have hnc : h3zornSimpleX 0 1 * h3zornSimpleY 0 1 ≠ h3zornSimpleY 0 1 * h3zornSimpleX 0 1 := by
    intro h
    have hm := congrArg (fun g : h3zornReducedStructureGroup =>
      h3zornToMatrix g.1.toLinearMap 0 0) h
    have hX : h3zornToMatrix (h3zornSimpleX 0 1).1.toLinearMap =
        (1 : Matrix (Fin 27) (Fin 27) ℝ) + (sparseToMat (e6SimpleESparse 0)).map (Int.cast : ℤ → ℝ) := by
      change h3zornToMatrix ((1 : Module.End ℝ (H3Zorn ℝ)) + (1 : ℝ) • (e6SimpleE 0).1) = _
      rw [map_add, _root_.map_one, map_smul, h3zornToMatrix_e6SimpleE, one_smul]
    have hY : h3zornToMatrix (h3zornSimpleY 0 1).1.toLinearMap =
        (1 : Matrix (Fin 27) (Fin 27) ℝ) + (sparseToMat (e6SimpleFSparse 0)).map (Int.cast : ℤ → ℝ) := by
      change h3zornToMatrix ((1 : Module.End ℝ (H3Zorn ℝ)) + (1 : ℝ) • (e6SimpleF 0).1) = _
      rw [map_add, _root_.map_one, map_smul, h3zornToMatrix_e6SimpleF, one_smul]
    change h3zornToMatrix ((h3zornSimpleX 0 1).1.toLinearMap *
        (h3zornSimpleY 0 1).1.toLinearMap) 0 0 =
      h3zornToMatrix ((h3zornSimpleY 0 1).1.toLinearMap *
        (h3zornSimpleX 0 1).1.toLinearMap) 0 0 at hm
    rw [_root_.map_mul, _root_.map_mul, hX, hY] at hm
    have hL :
        ((1 + sparseToMat (e6SimpleESparse 0)) * (1 + sparseToMat (e6SimpleFSparse 0))) 0 0 = 2 := by
      decide
    have hR :
        ((1 + sparseToMat (e6SimpleFSparse 0)) * (1 + sparseToMat (e6SimpleESparse 0))) 0 0 = 1 := by
      decide
    have hcastL :
        (((1 : Matrix (Fin 27) (Fin 27) ℝ) +
            (sparseToMat (e6SimpleESparse 0)).map (Int.cast : ℤ → ℝ)) *
          ((1 : Matrix (Fin 27) (Fin 27) ℝ) +
            (sparseToMat (e6SimpleFSparse 0)).map (Int.cast : ℤ → ℝ))) 0 0 =
        ((((1 + sparseToMat (e6SimpleESparse 0)) *
          (1 + sparseToMat (e6SimpleFSparse 0))) 0 0 : ℤ) : ℝ) := by
      simp only [Matrix.mul_apply, Matrix.add_apply, Matrix.one_apply, Matrix.map_apply,
        Int.cast_sum, Int.cast_mul, Int.cast_add, Int.cast_ite, Int.cast_one, Int.cast_zero]
    have hcastR :
        (((1 : Matrix (Fin 27) (Fin 27) ℝ) +
            (sparseToMat (e6SimpleFSparse 0)).map (Int.cast : ℤ → ℝ)) *
          ((1 : Matrix (Fin 27) (Fin 27) ℝ) +
            (sparseToMat (e6SimpleESparse 0)).map (Int.cast : ℤ → ℝ))) 0 0 =
        ((((1 + sparseToMat (e6SimpleFSparse 0)) *
          (1 + sparseToMat (e6SimpleESparse 0))) 0 0 : ℤ) : ℝ) := by
      simp only [Matrix.mul_apply, Matrix.add_apply, Matrix.one_apply, Matrix.map_apply,
        Int.cast_sum, Int.cast_mul, Int.cast_add, Int.cast_ite, Int.cast_one, Int.cast_zero]
    rw [hcastL, hL, hcastR, hR] at hm
    norm_num at hm
  have hx0 : h3zornSimpleX i 0 = 1 := by
    apply Subtype.ext; apply LinearEquiv.toLinearMap_injective
    change (1 : Module.End ℝ (H3Zorn ℝ)) + (0 : ℝ) • (e6RootVec (eSimpleIdx i)).1 = 1
    simp
  have hy0 : h3zornSimpleY i 0 = 1 := by
    apply Subtype.ext; apply LinearEquiv.toLinearMap_injective
    change (1 : Module.End ℝ (H3Zorn ℝ)) + (0 : ℝ) • (e6SimpleF i).1 = 1
    simp
  have ht1 : h3zornTorusElt i 1 = 1 := by
    apply Subtype.ext; apply LinearEquiv.toLinearMap_injective; apply h3ZornBasis.ext; intro k
    change (h3zornTorusElt i 1).1 (h3ZornBasis k) = h3ZornBasis k
    rw [h3zornTorusElt_eq_e6TorusElt, e6TorusElt_apply_basis]
    simp
  exact ⟨hche_ne_bot, hborel_ne_bot, htor_ne_bot, hpos_ne_bot, hneg_ne_bot, hweyl_ne_bot,
    hnc, hx0, hy0, ht1⟩

theorem m3_signed_chevalley_conjugation_laws (j : Fin 6) (t : ℝˣ) (r : Fin 72)
    (i : Fin 6) (c : ℝ) :
    (∃ e : ℤ, e6TorusElt j t * e6RootExp r c * (e6TorusElt j t)⁻¹ =
      e6RootExp r ((t : ℝ) ^ e * c)) ∧
    (∃ r' : Fin 72, ∃ s : ℤ,
      e6WeylElt i 1 * e6RootExp r c * (e6WeylElt i 1)⁻¹ =
        e6RootExp r' ((s : ℝ) * c)) ∧
    h3zornAdjointAction (h3zornSimpleX 2 1) (e6SimpleH 2) =
      e6SimpleH 2 - (2 : ℝ) • e6SimpleE 2 ∧
    h3zornChevalleyEquiv ((xOp .E6 ℝ (2 : Fin 6) 1) (hVec .E6 ℝ (2 : Fin 6))) ≠
      h3zornAdjointAction (h3zornSimpleX 2 1) (e6SimpleH 2) ∧
    h3zornReducedStructureGroup ≠ ⊤ := by
  have hadj : h3zornAdjointAction (h3zornSimpleX 2 1) (e6SimpleH 2) =
      e6SimpleH 2 - (2 : ℝ) • e6SimpleE 2 := by
    rw [h3zornAdjointAction_simpleX, one_smul, one_pow]
    have h1 : ⁅e6SimpleE 2, e6SimpleH 2⁆ = (-2 : ℝ) • e6SimpleE 2 := by
      rw [← lie_skew, e6Simple_bracket_HE]
      have hc : Tag.cartan .E6 (2 : Fin 6) (2 : Fin 6) = 2 := by decide
      rw [hc]
      module
    rw [h1, lie_smul, lie_self, smul_zero, smul_zero, add_zero]
    module
  have hxop_ne : h3zornChevalleyEquiv ((xOp .E6 ℝ (2 : Fin 6) 1) (hVec .E6 ℝ (2 : Fin 6))) ≠
      h3zornAdjointAction (h3zornSimpleX 2 1) (e6SimpleH 2) := by
    rw [hadj]
    have hxop : h3zornChevalleyEquiv ((xOp .E6 ℝ (2 : Fin 6) 1) (hVec .E6 ℝ (2 : Fin 6))) =
        e6SimpleH 2 + (2 : ℝ) • e6SimpleE 2 := by
      have hx : (xOp .E6 ℝ (2 : Fin 6) 1) (hVec .E6 ℝ (2 : Fin 6)) =
          hVec .E6 ℝ (2 : Fin 6) + (2 : ℝ) • rootVec .E6 ℝ (e6RootCoord (eSimpleIdx 2)) := by
        change (xOp .E6 ℝ (2 : Fin 6) 1) (Finsupp.single (Sum.inl (2 : Fin 6)) 1) = _
        unfold xOp
        rw [Finsupp.linearCombination_single, one_smul]
        have hc : (Tag.cartan .E6 (⟨2, by decide⟩ : Fin (Tag.rank .E6))
            (⟨2, by decide⟩ : Fin (Tag.rank .E6))).natAbs = 2 := by decide
        have hr : (Pi.single (⟨2, by decide⟩ : Fin (Tag.rank .E6)) (1 : ℤ) :
            Fin (Tag.rank .E6) → ℤ) = e6RootCoord (eSimpleIdx 2) := by
          ext k; fin_cases k <;> decide
        change hVec .E6 ℝ (⟨2, by decide⟩ : Fin (Tag.rank .E6)) +
            (((Tag.cartan .E6 (⟨2, by decide⟩ : Fin (Tag.rank .E6))
              (⟨2, by decide⟩ : Fin (Tag.rank .E6))).natAbs : ℝ) * 1) •
              rootVec .E6 ℝ (Pi.single (⟨2, by decide⟩ : Fin (Tag.rank .E6)) (1 : ℤ)) = _
        rw [hc, hr]
        norm_num
        rfl
      rw [hx, map_add, map_smul, h3zornChevalleyEquiv_hVec 2,
        h3zornChevalleyEquiv_rootVec (eSimpleIdx 2)]
      rfl
    rw [hxop]
    intro h
    have hsub : (4 : ℝ) • e6SimpleE 2 = 0 := by
      have hd := sub_eq_zero.mpr h
      have h4 : (4 : ℝ) • e6SimpleE 2 =
          (e6SimpleH 2 + (2 : ℝ) • e6SimpleE 2) - (e6SimpleH 2 - (2 : ℝ) • e6SimpleE 2) := by
        module
      rw [h4, hd]
    have he := (smul_eq_zero.mp hsub).resolve_left (by norm_num)
    exact e6RootVec_ne_zero (eSimpleIdx 2) he
  have hstr_ne_top : h3zornReducedStructureGroup ≠ ⊤ := by
    intro h
    have h2 : LinearEquiv.smulOfUnit (Units.mk0 (2 : ℝ) (by norm_num)) ∈
        h3zornReducedStructureGroup := by
      rw [h]; trivial
    have hn := h2 (1 : H3Zorn ℝ)
    change H3Zorn.normCubic ((2 : ℝ) • (1 : H3Zorn ℝ)) = H3Zorn.normCubic (1 : H3Zorn ℝ) at hn
    rw [H3Zorn.normCubic_smul, H3Zorn.normCubic_one] at hn
    norm_num at hn
  exact ⟨⟨_, e6TorusElt_conj_e6RootExp j t r c⟩,
    ⟨_, _, e6WeylElt_one_conj_e6RootExp i r c⟩,
    hadj, hxop_ne, hstr_ne_top⟩

end M3GroupGenerationAndBruhat

end InfoGeometry.Tests.E6Closure
