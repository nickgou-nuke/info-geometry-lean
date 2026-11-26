/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.H3ZornE6RootSystem
import InfoGeometry.Algebra.H3ZornE6Simplicity
import InfoGeometry.Algebra.H3ZornMinusculeCFSGBridge
import InfoGeometry.Algebra.CompactOctonion
import InfoGeometry.Algebra.H3Octonion
import InfoGeometry.Algebra.H3OctonionStructureGroup
import InfoGeometry.Algebra.H3OctonionLieAlgebra

/-!
Complete regression tests covering both the split Albert Jordan algebra
`H₃(𝕆_s)` (`H3Zorn ℝ`, with 78D `E₆(6)` root system, simplicity, and CFSG
minuscule / adjoint bridge) and the compact Albert Jordan algebra `H₃(𝕆)`
(`H3Octonion ℝ`, with `F₄(-52)`, `E₆(-26)`, `Str(H₃(𝕆))`, and Killing
trace-square real-form separation).
-/

namespace InfoGeometry.Tests.JordanE6Complete

open InfoGeometry.Algebra
open InfoGeometry.Exceptional.CFSGPort.Chevalley

/-! ### Split `H₃(𝕆_s)`: `E₆(6)` Root System, Chevalley Basis, and Simplicity -/

theorem split_cartan_dim_eq_six : Module.finrank ℝ h3zornCartan = 6 :=
  finrank_h3zornCartan

theorem split_e6_dim_eq_seventyEight : Module.finrank ℝ h3zornCubicStabilizer = 78 := by
  rw [Module.finrank_eq_card_basis e6ChevalleyBasis]
  simp

theorem split_e6_root_cert (r : Fin 72) : IsRoot .E6 (e6RootCoord r) :=
  e6RootCoord_isRoot r

theorem split_e6_isSimple : LieAlgebra.IsSimple ℝ h3zornCubicStabilizer :=
  h3zornCubicStabilizer_isSimple

theorem split_e6_isSemisimple : LieAlgebra.IsSemisimple ℝ h3zornCubicStabilizer :=
  h3zornCubicStabilizer_isSemisimple

theorem split_e6_center_trivial : LieAlgebra.center ℝ h3zornCubicStabilizer = ⊥ :=
  center_h3zornCubicStabilizer_eq_bot

theorem split_e6_cartan_subalgebra : h3zornCartan.IsCartanSubalgebra :=
  h3zornCartan_isCartanSubalgebra

noncomputable def split_e6_chevalley_iso : RootModule .E6 ℝ ≃ₗ[ℝ] h3zornCubicStabilizer :=
  h3zornChevalleyEquiv

/-! ### Split `H₃(𝕆_s)`: CFSG Minuscule Bridge, Weyl Braid, and Adjoint Intertwiners -/

theorem split_chevalleyE6_in_reducedStr :
    h3zornChevalleyE6 ≤ (⊤ : Subgroup h3zornReducedStructureGroup) :=
  h3zornChevalleyE6_le_reducedStructureGroup

theorem split_weyl_noncomm :
    h3zornWeylElt 0 1 * h3zornWeylElt 2 1 ≠ h3zornWeylElt 2 1 * h3zornWeylElt 0 1 :=
  h3zornWeylElt_noncomm_witness

theorem split_weyl_braid :
    h3zornWeylElt 0 1 * h3zornWeylElt 2 1 * h3zornWeylElt 0 1 =
      h3zornWeylElt 2 1 * h3zornWeylElt 0 1 * h3zornWeylElt 2 1 :=
  h3zornWeylElt_braid_0_2

theorem split_minuscule_weights_aligned (k : Fin 27) (i : Fin 6) :
    h3zornWeight (permToMinuscule k) i = cfsgMinusculeWeight k i :=
  h3zornWeight_perm_eq_cfsgMinusculeWeight k i

theorem split_adjoint_torus_intertwines (i : Fin 6) (t : ℝˣ) (v : RootModule .E6 ℝ) :
    h3zornChevalleyEquiv ((torusElt .E6 ℝ i t : Module.End ℝ (RootModule .E6 ℝ)) v) =
      h3zornAdjointAction (h3zornTorusElt i t) (h3zornChevalleyEquiv v) :=
  h3zornChevalleyEquiv_torusElt i t v

theorem split_adjoint_simpleX_exp (i : Fin 6) (c : ℝ) (Y : h3zornCubicStabilizer) :
    h3zornAdjointAction (h3zornSimpleX i c) Y =
      Y + c • ⁅e6SimpleE i, Y⁆ + (c ^ 2 / 2) • ⁅e6SimpleE i, ⁅e6SimpleE i, Y⁆⁆ :=
  h3zornAdjointAction_simpleX i c Y

/-! ### Compact `𝕆` and Compact Albert Algebra `H₃(𝕆)` -/

theorem compact_octonion_dim_eq_eight : Module.finrank ℝ (CompactOctonion ℝ) = 8 :=
  CompactOctonion.finrank_compactOctonion

theorem compact_octonion_norm_mult (x y : CompactOctonion ℝ) :
    CompactOctonion.norm (CompactOctonion.mul x y) =
      CompactOctonion.norm x * CompactOctonion.norm y :=
  CompactOctonion.norm_mul x y

theorem compact_octonion_div_inv {x : CompactOctonion ℝ} (hx : x ≠ 0) :
    CompactOctonion.mul x (CompactOctonion.inv x) = 1 :=
  CompactOctonion.mul_inv_cancel hx

theorem compact_octonion_noncomm :
    CompactOctonion.mul (CompactOctonion.basisVec 1) (CompactOctonion.basisVec 2) ≠
      CompactOctonion.mul (CompactOctonion.basisVec 2) (CompactOctonion.basisVec 1) := by
  intro h
  have he := congrArg CompactOctonion.e4 h
  simp [CompactOctonion.basisVec, CompactOctonion.mul] at he
  norm_num at he

theorem compact_albert_dim_eq_twentySeven : Module.finrank ℝ (H3Octonion ℝ) = 27 :=
  H3Octonion.finrank_h3Octonion

theorem compact_albert_isCommJordan : IsCommJordan (H3Octonion ℝ) :=
  inferInstance

theorem compact_albert_formally_real (x y : H3Octonion ℝ) (h : x * x + y * y = 0) :
    x = 0 ∧ y = 0 :=
  H3Octonion.formal_reality x y h

theorem compact_split_albert_nonisomorphic : IsEmpty (H3Octonion ℝ ≃+* H3Zorn ℝ) :=
  H3Octonion.no_jordanIso_H3Octonion_H3Zorn

/-! ### Compact `F₄(-52)`, `E₆(-26)`, `Str(H₃(𝕆))`, and Universal Fundamental Formula -/

theorem compact_aut_in_str (e : H3OctonionJordanAut) :
    e.toLinearEquiv ∈ StructureGroup ℝ (H3Octonion ℝ) :=
  e.mem_StructureGroup

theorem compact_jordan_fundamental_formula (X Y Z : H3Octonion ℝ) :
    H3Octonion.U (H3Octonion.U X Y) Z = H3Octonion.U X (H3Octonion.U Y (H3Octonion.U X Z)) :=
  h3Octonion_U_fundamental X Y Z

theorem compact_str_iff_similitude (g : H3Octonion ℝ ≃ₗ[ℝ] H3Octonion ℝ) :
    g ∈ StructureGroup ℝ (H3Octonion ℝ) ↔
      ∃ u : ℝˣ, ∀ x : H3Octonion ℝ, H3Octonion.normCubic (g x) = (u : ℝ) * H3Octonion.normCubic x :=
  h3Octonion_mem_StructureGroup_iff_similitude g

noncomputable def compact_e6_str_ker_equiv :
    h3OctonionReducedStructureGroup ≃* h3OctonionStructureGroupMultiplier.ker :=
  h3OctonionReducedStructureGroupMulEquivStructureKer

noncomputable def compact_f4_fix_one_equiv :
    H3OctonionJordanAut ≃* h3OctonionReducedStructureFixOne :=
  h3OctonionJordanAutMulEquivReducedStructureFixOne

/-! ### Compact Lie Algebras (52D / 78D / 79D) and Real-Form Signature Separation -/

theorem compact_f4_dim_eq_fiftyTwo : Module.finrank ℝ H3OctonionF4Derivations = 52 :=
  finrank_H3OctonionF4Derivations

theorem compact_e6_dim_eq_seventyEight : Module.finrank ℝ h3OctonionCubicStabilizer = 78 :=
  finrank_h3OctonionCubicStabilizer

theorem compact_str_dim_eq_seventyNine : Module.finrank ℝ h3OctonionStructureLieSubalgebra = 79 :=
  finrank_h3OctonionStructureLieSubalgebra

theorem compact_f4_killing_trace_sq_nonpos (D : H3OctonionF4Derivations) :
    LinearMap.trace ℝ (H3Octonion ℝ) (D.1 * D.1) ≤ 0 :=
  compactF4_trace_sq_nonpos D

theorem compact_f4_killing_trace_sq_definite (D : H3OctonionF4Derivations) :
    LinearMap.trace ℝ (H3Octonion ℝ) (D.1 * D.1) = 0 ↔ D = 0 :=
  compactF4_trace_sq_eq_zero_iff D

theorem compact_lmul_killing_trace_sq_nonneg (a : H3Octonion ℝ) :
    0 ≤ LinearMap.trace ℝ (H3Octonion ℝ) (jordanLmul (R := ℝ) a * jordanLmul (R := ℝ) a) :=
  compactLmul_trace_sq_nonneg a

theorem split_f4_killing_trace_sq_witness_val :
    LinearMap.trace ℝ (H3Zorn ℝ) (splitF4TracePosWitness.1 * splitF4TracePosWitness.1) = 3 / 2 :=
  splitF4TracePosWitness_trace_sq

theorem split_f4_killing_trace_sq_witness_pos :
    0 < LinearMap.trace ℝ (H3Zorn ℝ) (splitF4TracePosWitness.1 * splitF4TracePosWitness.1) :=
  splitF4TracePosWitness_trace_sq_pos

end InfoGeometry.Tests.JordanE6Complete
