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
import InfoGeometry.Canonical.H3ZornJordanTripleBridge
import InfoGeometry.Canonical.H3ZornTKKNative
import InfoGeometry.Canonical.H3ZornTKKLieAlgebra
import InfoGeometry.Algebra.JordanTKKLieAlgebra
import InfoGeometry.Algebra.H3OctonionTKKLieAlgebra
import InfoGeometry.Algebra.H3ZornE7RootSystem
import InfoGeometry.Algebra.H3ZornE7Simplicity
import InfoGeometry.Algebra.H3ZornFreudenthalQuartic
import InfoGeometry.Algebra.H3ZornFreudenthalLeviAction
import InfoGeometry.Algebra.H3ZornFreudenthalE7Group
import InfoGeometry.Canonical.NativeTitsE8Carrier
import InfoGeometry.Algebra.MagicSquareTitsBracket
import InfoGeometry.Algebra.SplitE8RootSystem
import InfoGeometry.Algebra.SplitE8Simplicity

/-!
# E2E Tier 5 Adversarial Tests for Exceptional Algebras (`E₆`, `E₇`, `E₈`)

Adversarial white-box coverage hardening across all 6 mathematical areas:
1. `E₆` Serre isomorphism (`H3ZornE6SerreHom`): branch-node Serre relations, non-simple height ≥ 2
   root transport & Cartan eigenvalues, Serre-to-TKK compatibility on non-simple elements.
2. `E₆` Complexification & Compact Simplicity (`H3OctonionZornComplexification`, `H3OctonionSimplicity`):
   all 3 off-diagonal octonionic slots under `h3OctonionComplexEquiv`, forward `BaseChangeEquiv`
   bracket preservation on compact `H3Octonion ℝ` derivations/stabilizers, compact vs split
   trace-square separation.
3. `E₆(6)` Chevalley / Bruhat (`H3ZornE6ChevalleyBruhat`, `H3ZornMinusculeCFSGBridge`):
   genuine non-Borel Bruhat `b₁ * w * b₂` decomposition with all three factors `≠ 1`,
   non-commuting root subgroups, non-diagonal rank-1 & norm-1 transitivity, `Fix(1)` vs `Str₀`.
4. `E₇` TKK (`JordanTKKLieAlgebra`, `H3ZornTKKLieAlgebra`, `H3OctonionTKKLieAlgebra`, `H3ZornE7RootSystem`):
   cross-grade `[e₊, e₋]` with simultaneous non-zero `jordanLmul` & `F₄` derivation parts,
   3-grade mixed `h3zornTKKToNative` bracket faithfulness, `E₇` `5↔6` junction & highest root,
   `𝔈₇(-25)` Cartan involution & Killing sign separation on off-diagonal `H3Octonion` vectors.
5. `E₇(7)` 56D Freudenthal (`H3ZornFreudenthalQuartic`, `H3ZornFreudenthalLeviAction`,
   `H3ZornFreudenthalE7Group`): sign-sensitive `+ ⟨x#, y#⟩` quartic cross-term witnesses,
   rank-1 / rank-2 / regular `I₄ > 0` / regular `I₄ < 0` strata separation, non-diagonal
   `t₊(A) * t₋(B) * J` composition & concrete Levi/inversion conjugation evaluations.
6. `E₈` 248D Magic Square (`NativeTitsE8Carrier`, `MagicSquareTitsBracket`, `SplitE8RootSystem`):
   all-sector `nativeToSplitTitsE8Equiv` non-triviality, simultaneous non-zero `G₂ ⊕ Mixed ⊕ F₄`
   components from `[Mixed, Mixed]`, `[G₂, Mixed]`, `[F₄, Mixed]`, `F₄–Mix–G₂` Chevalley
   junction (`4↔5↔6`), and non-vanishing `killingForm ℝ SplitE8Lie`.
-/

set_option autoImplicit false

namespace InfoGeometry.Tests.E6E7E8Tier5Adversarial

open scoped TensorProduct BigOperators
open InfoGeometry.Algebra
open InfoGeometry.Algebra.H3Zorn
open InfoGeometry.Algebra.SplitAlbertStructureOperators
open InfoGeometry.Algebra.MagicSquareTitsBracket
open InfoGeometry.Canonical.H3ZornBasis
open InfoGeometry.Canonical.H3ZornF4PeirceTrialitySplit
open InfoGeometry.Canonical.H3ZornJordanTripleBridge
open InfoGeometry.Canonical.H3ZornTKKNative
open InfoGeometry.Canonical.H3ZornTKKLieAlgebra
open InfoGeometry.Canonical.NativeTitsE8Carrier
open InfoGeometry.Exceptional.CFSGPort.Chevalley
open InfoGeometry.Lie.CanonicalZornDerivationDimension

attribute [local instance 100] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

/-! ## Shared Helpers -/

private theorem h3zornCubicStabilizer_ne_zero_of_sparse {x : h3zornCubicStabilizer}
    {s : SparseMat27}
    (hs : h3zornToMatrix (x.1 : Module.End ℝ (H3Zorn ℝ)) = (sparseToMat s).map Int.cast)
    (hnz : sparseZeroCheck s = false) : x ≠ 0 := by
  intro h0
  have hm := congrArg (fun y : h3zornCubicStabilizer =>
    h3zornToMatrix (y.1 : Module.End ℝ (H3Zorn ℝ))) h0
  rw [hs, ZeroMemClass.coe_zero, map_zero] at hm
  have hzc : sparseZeroCheck s = true := by
    simp only [sparseZeroCheck, List.all_eq_true, beq_iff_eq]
    intro p _
    have hp := congrFun (congrFun hm p.1) p.2.1
    simp only [Matrix.map_apply, Matrix.zero_apply, Int.cast_eq_zero] at hp
    exact hp
  rw [hnz] at hzc
  cases hzc

private theorem sparseToMat_comm_eq (a b : SparseMat27) :
    (sparseToMat a).map (Int.cast : ℤ → ℝ) * (sparseToMat b).map Int.cast -
      (sparseToMat b).map Int.cast * (sparseToMat a).map Int.cast =
    (sparseToMat (sparseComm a b)).map Int.cast := by
  rw [sparseToMat_comm]
  ext r c
  simp [Matrix.mul_apply]

private theorem h3zornToMatrix_coe_lie (X Y : h3zornCubicStabilizer) :
    h3zornToMatrix (⁅X, Y⁆ : h3zornCubicStabilizer).1 =
      h3zornToMatrix X.1 * h3zornToMatrix Y.1 - h3zornToMatrix Y.1 * h3zornToMatrix X.1 :=
  h3zornToMatrix_lie X Y

/-! ## Area 1: `E₆` Serre Isomorphism — Non-Simple Roots, Branch Serre & TKK Compatibility -/

section Area1Serre

private theorem serreEquiv_H (i : Fin 6) : h3zornE6SerreEquiv (e6SerreH i) = e6SimpleH i :=
  h3zornE6SerreQuotientMap_H i

private theorem serreEquiv_E (i : Fin 6) : h3zornE6SerreEquiv (e6SerreE i) = e6SimpleE i :=
  h3zornE6SerreQuotientMap_E i

private theorem serreEquiv_F (i : Fin 6) : h3zornE6SerreEquiv (e6SerreF i) = e6SimpleF i :=
  h3zornE6SerreQuotientMap_F i

/-- Branch node `3` and neighbors `1, 2, 4` satisfy exact Serre relations and non-zero
height-2 and height-3 root brackets in `LieAlgebra.e₆ ℝ`. -/
theorem e6_serre_branch_node_and_nonsimple_brackets :
    ⁅e6SerreE 1, e6SerreE 3⁆ ≠ 0 ∧
    ⁅e6SerreE 2, e6SerreE 3⁆ ≠ 0 ∧
    ⁅e6SerreE 3, e6SerreE 4⁆ ≠ 0 ∧
    ⁅e6SerreE 1, e6SerreE 2⁆ = 0 ∧
    ⁅e6SerreE 1, e6SerreE 4⁆ = 0 ∧
    ⁅e6SerreE 2, ⁅e6SerreE 1, e6SerreE 3⁆⁆ ≠ 0 ∧
    ⁅e6SerreF 2, ⁅e6SerreF 1, e6SerreF 3⁆⁆ ≠ 0 ∧
    ⁅e6SerreE 1, ⁅e6SerreE 1, e6SerreE 3⁆⁆ = 0 := by
  have he13 : h3zornE6SerreEquiv ⁅e6SerreE 1, e6SerreE 3⁆ ≠ 0 := by
    rw [LieEquiv.map_lie, serreEquiv_E, serreEquiv_E]
    refine h3zornCubicStabilizer_ne_zero_of_sparse (s := sparseComm (e6SimpleESparse 1) (e6SimpleESparse 3))
      ?_ (by decide)
    rw [h3zornToMatrix_coe_lie, h3zornToMatrix_e6SimpleE, h3zornToMatrix_e6SimpleE, sparseToMat_comm_eq]
  have he23 : h3zornE6SerreEquiv ⁅e6SerreE 2, e6SerreE 3⁆ ≠ 0 := by
    rw [LieEquiv.map_lie, serreEquiv_E, serreEquiv_E]
    refine h3zornCubicStabilizer_ne_zero_of_sparse (s := sparseComm (e6SimpleESparse 2) (e6SimpleESparse 3))
      ?_ (by decide)
    rw [h3zornToMatrix_coe_lie, h3zornToMatrix_e6SimpleE, h3zornToMatrix_e6SimpleE, sparseToMat_comm_eq]
  have he34 : h3zornE6SerreEquiv ⁅e6SerreE 3, e6SerreE 4⁆ ≠ 0 := by
    rw [LieEquiv.map_lie, serreEquiv_E, serreEquiv_E]
    refine h3zornCubicStabilizer_ne_zero_of_sparse (s := sparseComm (e6SimpleESparse 3) (e6SimpleESparse 4))
      ?_ (by decide)
    rw [h3zornToMatrix_coe_lie, h3zornToMatrix_e6SimpleE, h3zornToMatrix_e6SimpleE, sparseToMat_comm_eq]
  have he213 : h3zornE6SerreEquiv ⁅e6SerreE 2, ⁅e6SerreE 1, e6SerreE 3⁆⁆ ≠ 0 := by
    rw [LieEquiv.map_lie, LieEquiv.map_lie, serreEquiv_E, serreEquiv_E, serreEquiv_E]
    refine h3zornCubicStabilizer_ne_zero_of_sparse
      (s := sparseComm (e6SimpleESparse 2) (sparseComm (e6SimpleESparse 1) (e6SimpleESparse 3)))
      ?_ (by decide)
    rw [h3zornToMatrix_coe_lie, h3zornToMatrix_coe_lie, h3zornToMatrix_e6SimpleE,
      h3zornToMatrix_e6SimpleE, h3zornToMatrix_e6SimpleE, sparseToMat_comm_eq, sparseToMat_comm_eq]
  have hf213 : h3zornE6SerreEquiv ⁅e6SerreF 2, ⁅e6SerreF 1, e6SerreF 3⁆⁆ ≠ 0 := by
    rw [LieEquiv.map_lie, LieEquiv.map_lie, serreEquiv_F, serreEquiv_F, serreEquiv_F]
    refine h3zornCubicStabilizer_ne_zero_of_sparse
      (s := sparseComm (e6SimpleFSparse 2) (sparseComm (e6SimpleFSparse 1) (e6SimpleFSparse 3)))
      ?_ (by decide)
    rw [h3zornToMatrix_coe_lie, h3zornToMatrix_coe_lie, h3zornToMatrix_e6SimpleF,
      h3zornToMatrix_e6SimpleF, h3zornToMatrix_e6SimpleF, sparseToMat_comm_eq, sparseToMat_comm_eq]
  refine ⟨fun h => he13 (by rw [h, map_zero]),
    fun h => he23 (by rw [h, map_zero]),
    fun h => he34 (by rw [h, map_zero]), ?_, ?_,
    fun h => he213 (by rw [h, map_zero]),
    fun h => hf213 (by rw [h, map_zero]), ?_⟩
  · apply h3zornE6SerreEquiv.injective
    change h3zornE6SerreEquiv ⁅e6SerreE 1, e6SerreE 2⁆ = h3zornE6SerreEquiv 0
    rw [LieEquiv.map_lie, serreEquiv_E, serreEquiv_E, map_zero]
    have hs := e6Simple_serre_E (i := 1) (j := 2) (by decide)
    have hc : (1 - Tag.cartan .E6 (1 : Fin 6) (2 : Fin 6)).toNat = 1 := by decide
    simpa [hc] using hs
  · apply h3zornE6SerreEquiv.injective
    change h3zornE6SerreEquiv ⁅e6SerreE 1, e6SerreE 4⁆ = h3zornE6SerreEquiv 0
    rw [LieEquiv.map_lie, serreEquiv_E, serreEquiv_E, map_zero]
    have hs := e6Simple_serre_E (i := 1) (j := 4) (by decide)
    have hc : (1 - Tag.cartan .E6 (1 : Fin 6) (4 : Fin 6)).toNat = 1 := by decide
    simpa [hc] using hs
  · apply h3zornE6SerreEquiv.injective
    change h3zornE6SerreEquiv ⁅e6SerreE 1, ⁅e6SerreE 1, e6SerreE 3⁆⁆ = h3zornE6SerreEquiv 0
    rw [LieEquiv.map_lie, LieEquiv.map_lie, serreEquiv_E, serreEquiv_E, map_zero]
    have hs := e6Simple_serre_E (i := 1) (j := 3) (by decide)
    have hc : (1 - Tag.cartan .E6 (1 : Fin 6) (3 : Fin 6)).toNat = 2 := by decide
    simpa [hc] using hs

/-- Non-simple height-2 root `⁅e6SerreE 1, e6SerreE 3⁆` has exact Cartan eigenvalues
(`1` on `H 1`, `-1` on `H 2`, `1` on `H 3`), and `h3zornE6SerreEquiv.symm` on
`e6RootVec e6HighestRootIdx` preserves non-vanishing opposite-root Cartan bracket. -/
theorem e6_serre_nonsimple_cartan_eigenvalues_and_highest_root :
    ⁅e6SerreH 1, ⁅e6SerreE 1, e6SerreE 3⁆⁆ = ⁅e6SerreE 1, e6SerreE 3⁆ ∧
    ⁅e6SerreH 2, ⁅e6SerreE 1, e6SerreE 3⁆⁆ = -⁅e6SerreE 1, e6SerreE 3⁆ ∧
    ⁅e6SerreH 3, ⁅e6SerreE 1, e6SerreE 3⁆⁆ = ⁅e6SerreE 1, e6SerreE 3⁆ ∧
    h3zornE6SerreEquiv.symm (e6RootVec e6HighestRootIdx) ≠ 0 ∧
    ⁅h3zornE6SerreEquiv.symm (e6RootVec e6HighestRootIdx),
      h3zornE6SerreEquiv.symm (e6RootVec (e6RootOpp e6HighestRootIdx))⁆ ≠ 0 := by
  have h1 : ⁅e6SerreH 1, ⁅e6SerreE 1, e6SerreE 3⁆⁆ = ⁅e6SerreE 1, e6SerreE 3⁆ := by
    apply h3zornE6SerreEquiv.injective
    change h3zornE6SerreEquiv ⁅e6SerreH 1, ⁅e6SerreE 1, e6SerreE 3⁆⁆ =
      h3zornE6SerreEquiv ⁅e6SerreE 1, e6SerreE 3⁆
    simp only [LieEquiv.map_lie, serreEquiv_H, serreEquiv_E]
    rw [leibniz_lie, e6Simple_bracket_HE, e6Simple_bracket_HE]
    have c11 : Tag.cartan .E6 (1 : Fin 6) (1 : Fin 6) = 2 := by decide
    have c13 : Tag.cartan .E6 (1 : Fin 6) (3 : Fin 6) = -1 := by decide
    rw [c11, c13]
    push_cast
    simp only [smul_lie, lie_smul]
    module
  have h2 : ⁅e6SerreH 2, ⁅e6SerreE 1, e6SerreE 3⁆⁆ = -⁅e6SerreE 1, e6SerreE 3⁆ := by
    apply h3zornE6SerreEquiv.injective
    change h3zornE6SerreEquiv ⁅e6SerreH 2, ⁅e6SerreE 1, e6SerreE 3⁆⁆ =
      h3zornE6SerreEquiv (-⁅e6SerreE 1, e6SerreE 3⁆)
    simp only [map_neg, LieEquiv.map_lie, serreEquiv_H, serreEquiv_E]
    rw [leibniz_lie, e6Simple_bracket_HE, e6Simple_bracket_HE]
    have c21 : Tag.cartan .E6 (2 : Fin 6) (1 : Fin 6) = 0 := by decide
    have c23 : Tag.cartan .E6 (2 : Fin 6) (3 : Fin 6) = -1 := by decide
    rw [c21, c23]
    simp
  have h3 : ⁅e6SerreH 3, ⁅e6SerreE 1, e6SerreE 3⁆⁆ = ⁅e6SerreE 1, e6SerreE 3⁆ := by
    apply h3zornE6SerreEquiv.injective
    change h3zornE6SerreEquiv ⁅e6SerreH 3, ⁅e6SerreE 1, e6SerreE 3⁆⁆ =
      h3zornE6SerreEquiv ⁅e6SerreE 1, e6SerreE 3⁆
    simp only [LieEquiv.map_lie, serreEquiv_H, serreEquiv_E]
    rw [leibniz_lie, e6Simple_bracket_HE, e6Simple_bracket_HE]
    have c31 : Tag.cartan .E6 (3 : Fin 6) (1 : Fin 6) = -1 := by decide
    have c33 : Tag.cartan .E6 (3 : Fin 6) (3 : Fin 6) = 2 := by decide
    rw [c31, c33]
    push_cast
    simp only [smul_lie, lie_smul]
    module
  refine ⟨h1, h2, h3, ?_, ?_⟩
  · intro h0
    have h1' := congrArg h3zornE6SerreEquiv h0
    rw [LieEquiv.apply_symm_apply, map_zero] at h1'
    exact e6RootVec_ne_zero e6HighestRootIdx h1'
  · intro h0
    have h1' := congrArg h3zornE6SerreEquiv h0
    rw [LieEquiv.map_lie, LieEquiv.apply_symm_apply, LieEquiv.apply_symm_apply, map_zero] at h1'
    exact e6RootVec_opposite_bracket_ne_zero e6HighestRootIdx h1'

/-- Non-simple Serre-to-TKK compatibility: pushing `⁅e6SerreE 1, e6SerreE 3⁆` through
`h3zornE6SerreEquiv` and `h3zornCubicStabilizerToTKK` into `H3ZornTKKLie` acts non-trivially
on grade `-1` (`negInj (h3ZornBasis 4)`). -/
theorem e6_serre_nonsimple_to_tkk_action_ne_zero :
    let X := h3zornCubicStabilizerToTKK (h3zornE6SerreEquiv ⁅e6SerreE 1, e6SerreE 3⁆)
    ⁅X, negInj (h3ZornBasis 4)⁆ ≠ 0 := by
  intro X h0
  have heq : (X : H3ZornTKKLie) =
      zeroInj ⟨(⁅e6SimpleE 1, e6SimpleE 3⁆ : h3zornCubicStabilizer).1,
        h3zornCubicStabilizer_le_structureOperatorLieSubalgebra
          ⁅e6SimpleE 1, e6SimpleE 3⁆.2⟩ := by
    dsimp [X]
    rw [LieEquiv.map_lie, serreEquiv_E, serreEquiv_E]
    rfl
  rw [heq, zeroInj_bracket_negInj] at h0
  have hv := congrArg (fun Y : H3ZornTKKLie => Y.neg) h0
  change (⁅e6SimpleE 1, e6SimpleE 3⁆ : Module.End ℝ (H3Zorn ℝ)) (h3ZornBasis 4) = 0 at hv
  have hrep : h3ZornBasis.repr ((⁅e6SimpleE 1, e6SimpleE 3⁆ : Module.End ℝ (H3Zorn ℝ))
      (h3ZornBasis 4)) = 0 := by rw [hv, map_zero]
  have hchk : sparseVal (sparseComm (e6SimpleESparse 1) (e6SimpleESparse 3)) 6 4 = -1 := by
    decide
  have hmat : h3zornToMatrix (⁅e6SimpleE 1, e6SimpleE 3⁆ : h3zornCubicStabilizer).1 =
      (sparseToMat (sparseComm (e6SimpleESparse 1) (e6SimpleESparse 3))).map Int.cast := by
    rw [h3zornToMatrix_coe_lie, h3zornToMatrix_e6SimpleE, h3zornToMatrix_e6SimpleE,
      sparseToMat_comm_eq]
  have hcoeff := congrArg (fun f : Fin 27 →₀ ℝ => f 6) hrep
  have hre : h3ZornBasis.repr ((⁅e6SimpleE 1, e6SimpleE 3⁆ : Module.End ℝ (H3Zorn ℝ))
      (h3ZornBasis 4)) 6 =
      h3zornToMatrix (⁅e6SimpleE 1, e6SimpleE 3⁆ : h3zornCubicStabilizer).1 6 4 := by
    rw [h3zornToMatrix_apply]; rfl
  rw [hre, hmat, Matrix.map_apply] at hcoeff
  change ((sparseVal (sparseComm (e6SimpleESparse 1) (e6SimpleESparse 3)) 6 4 : ℤ) : ℝ) = 0
    at hcoeff
  rw [hchk] at hcoeff
  norm_num at hcoeff

end Area1Serre

/-! ## Area 2: `E₆` Complexification & Compact Simplicity -/

section Area2Complexification

private noncomputable def complexOctMix : CompactOctonion ℂ :=
  ⟨0, 1, Complex.I, 0, 0, 2, 0, 0⟩

private noncomputable def complexOctMix2 : CompactOctonion ℂ :=
  ⟨0, 0, 0, 1, -Complex.I, 0, 0, 1⟩

private noncomputable def compactMixX12 : H3Octonion ℝ :=
  ⟨0, 0, 0, ⟨0, 1, 0, 0, 0, 0, 0, 0⟩, 0, 0⟩

private noncomputable def compactMixX23 : H3Octonion ℝ :=
  ⟨0, 0, 0, 0, ⟨0, 0, 1, 0, 0, 0, 0, 0⟩, 0⟩

private noncomputable def compactMixD : h3OctonionCubicStabilizer :=
  ⟨(h3OctonionJordanInnerDerivation compactMixX12 compactMixX23).1,
    H3OctonionF4Derivations_le_h3OctonionCubicStabilizer
      (h3OctonionJordanInnerDerivation compactMixX12 compactMixX23).2⟩

private noncomputable def compactMixL : h3OctonionCubicStabilizer :=
  ⟨jordanLmul (R := ℝ) (H3Octonion.diagCartan 1 (-1) 0),
    (jordanLmul_mem_h3OctonionCubicStabilizer_iff _).mpr (by
      simp [H3Octonion.linearTrace, H3Octonion.diagCartan])⟩

private theorem compactMix_bracket_e4 :
    (compactMixX12 * (compactMixX23 * H3Octonion.diagCartan 1 (-1) 0) -
      compactMixX23 * (compactMixX12 * H3Octonion.diagCartan 1 (-1) 0)).c.e4 = (1 / 4 : ℝ) := by
  have hx12_diag : compactMixX12 * H3Octonion.diagCartan 1 (-1) 0 = 0 := by
    rw [H3Octonion.mul_trace_formula]
    have hl1 : H3Octonion.linearTrace compactMixX12 = 0 := by
      simp [H3Octonion.linearTrace, compactMixX12]
    have hl2 : H3Octonion.linearTrace (H3Octonion.diagCartan (1 : ℝ) (-1) 0) = 0 := by
      simp [H3Octonion.linearTrace, H3Octonion.diagCartan]
    have hcr : H3Octonion.crossProduct compactMixX12 (H3Octonion.diagCartan (1 : ℝ) (-1) 0) = 0 := by
      apply H3Octonion.ext_h3 <;> (try apply CompactOctonion.ext) <;>
        simp [H3Octonion.crossProduct, compactMixX12, H3Octonion.diagCartan]
    rw [hl1, hl2, hcr]
    simp
  have hx23_diag : compactMixX23 * H3Octonion.diagCartan 1 (-1) 0 =
      (-(1 / 2 : ℝ)) • compactMixX23 := by
    rw [H3Octonion.mul_trace_formula]
    have hl1 : H3Octonion.linearTrace compactMixX23 = 0 := by
      simp [H3Octonion.linearTrace, compactMixX23]
    have hl2 : H3Octonion.linearTrace (H3Octonion.diagCartan (1 : ℝ) (-1) 0) = 0 := by
      simp [H3Octonion.linearTrace, H3Octonion.diagCartan]
    have hcr : H3Octonion.crossProduct compactMixX23 (H3Octonion.diagCartan (1 : ℝ) (-1) 0) =
        -compactMixX23 := by
      apply H3Octonion.ext_h3 <;> (try apply CompactOctonion.ext) <;>
        simp [H3Octonion.crossProduct, compactMixX23, H3Octonion.diagCartan]
    rw [hl1, hl2, hcr]
    have htr_cr : H3Octonion.linearTrace (-compactMixX23) = 0 := by
      simp [H3Octonion.linearTrace, compactMixX23]
    rw [htr_cr]
    apply H3Octonion.ext_h3 <;> (try apply CompactOctonion.ext) <;>
      simp [compactMixX23]
  rw [hx12_diag, hx23_diag, mul_zero, sub_zero, mul_smul_comm]
  have h12 : compactMixX12 = H3Octonion.embedJ12 ⟨0, 1, 0, 0, 0, 0, 0, 0⟩ := rfl
  have h23 : compactMixX23 = H3Octonion.embedJ23 ⟨0, 0, 1, 0, 0, 0, 0, 0⟩ := rfl
  rw [h12, h23, oct_embedJ12_mul_embedJ23]
  simp [H3Octonion.embedJ31, CompactOctonion.conj, CompactOctonion.mul]
  norm_num

/-- `h3OctonionComplexEquiv` preserves Jordan multiplication and cubic norm on an element
with complex non-commuting octonionic entries in ALL THREE off-diagonal slots `(a, b, c)`. -/
theorem complexification_all_three_offdiag_slots_preserved :
    let x : H3Octonion ℂ := ⟨1, 2, 3, complexOctMix, complexOctMix2, complexOctMix⟩
    let y : H3Octonion ℂ := ⟨2, -1, 1, complexOctMix2, complexOctMix, complexOctMix2⟩
    h3OctonionComplexEquiv (candidateJordanMulOctℂ x y) =
      candidateJordanMulZornℂ (h3OctonionComplexEquiv x) (h3OctonionComplexEquiv y) ∧
    H3Zorn.normCubic (h3OctonionComplexEquiv x) = H3Octonion.normCubic x ∧
    (h3OctonionComplexEquiv x).a ≠ 0 ∧
    (h3OctonionComplexEquiv x).b ≠ 0 ∧
    (h3OctonionComplexEquiv x).c ≠ 0 := by
  intro x y
  refine ⟨h3OctonionComplexEquiv_jordanMul x y, h3OctonionComplexEquiv_normCubic x, ?_, ?_, ?_⟩
  · intro h0
    have hv := congrArg (fun w : ZornVectorMatrix ℂ => w.v 0) h0
    change (octonionComplexEquiv complexOctMix).v 0 = 0 at hv
    simp [octonionComplexEquiv, octonionComplexToZornFun, complexOctMix] at hv
  · intro h0
    have hv := congrArg (fun w : ZornVectorMatrix ℂ => w.v 2) h0
    change (octonionComplexEquiv complexOctMix2).v 2 = 0 at hv
    simp [octonionComplexEquiv, octonionComplexToZornFun, complexOctMix2] at hv
  · intro h0
    have hv := congrArg (fun w : ZornVectorMatrix ℂ => w.v 0) h0
    change (octonionComplexEquiv complexOctMix).v 0 = 0 at hv
    simp [octonionComplexEquiv, octonionComplexToZornFun, complexOctMix] at hv

/-- Forward transport of concrete non-commuting `H3Octonion ℝ` derivations and trace-zero
`jordanLmul` operators under `h3OctonionCubicStabilizerBaseChangeEquiv` preserves Lie brackets
and produces a non-zero commutator in `ℂ ⊗[ℝ] h3zornCubicStabilizer`. -/
theorem complexification_forward_compact_to_split_bracket_nonzero :
    h3OctonionCubicStabilizerBaseChangeEquiv ((1 : ℂ) ⊗ₜ[ℝ] ⁅compactMixD, compactMixL⁆) =
      ⁅h3OctonionCubicStabilizerBaseChangeEquiv ((1 : ℂ) ⊗ₜ[ℝ] compactMixD),
        h3OctonionCubicStabilizerBaseChangeEquiv ((1 : ℂ) ⊗ₜ[ℝ] compactMixL)⁆ ∧
    h3OctonionCubicStabilizerBaseChangeEquiv ((1 : ℂ) ⊗ₜ[ℝ] ⁅compactMixD, compactMixL⁆) ≠ 0 := by
  have htmul : ((1 : ℂ) ⊗ₜ[ℝ] ⁅compactMixD, compactMixL⁆) =
      ⁅((1 : ℂ) ⊗ₜ[ℝ] compactMixD), ((1 : ℂ) ⊗ₜ[ℝ] compactMixL)⁆ := by
    rw [LieAlgebra.ExtendScalars.bracket_tmul, one_mul]
  refine ⟨?_, ?_⟩
  · rw [htmul]
    exact h3OctonionCubicStabilizerBaseChangeEquiv.map_lie
      ((1 : ℂ) ⊗ₜ[ℝ] compactMixD) ((1 : ℂ) ⊗ₜ[ℝ] compactMixL)
  intro h0
  have hDL0 : ((1 : ℂ) ⊗ₜ[ℝ] ⁅compactMixD, compactMixL⁆) = 0 :=
    h3OctonionCubicStabilizerBaseChangeEquiv.injective (h0.trans (map_zero _).symm)
  have hbr0 : ⁅compactMixD, compactMixL⁆ = 0 := by
    let reLM : ℂ →ₗ[ℝ] ℝ := Complex.reCLM.toLinearMap
    let proj : (ℂ ⊗[ℝ] h3OctonionCubicStabilizer) →ₗ[ℝ] h3OctonionCubicStabilizer :=
      (TensorProduct.lid ℝ h3OctonionCubicStabilizer).toLinearMap.comp
        (TensorProduct.map reLM LinearMap.id)
    have hmap := congrArg proj hDL0
    simpa [proj, reLM] using hmap
  have h1 : (⁅compactMixD, compactMixL⁆ : h3OctonionCubicStabilizer).1 (1 : H3Octonion ℝ) = 0 := by
    rw [hbr0]; rfl
  have hval : (⁅compactMixD, compactMixL⁆ : h3OctonionCubicStabilizer).1 (1 : H3Octonion ℝ) =
      compactMixD.1 (H3Octonion.diagCartan 1 (-1) 0) := by
    change compactMixD.1 (H3Octonion.diagCartan 1 (-1) 0 * (1 : H3Octonion ℝ)) -
      H3Octonion.diagCartan 1 (-1) 0 * compactMixD.1 (1 : H3Octonion ℝ) = _
    have hd1 : compactMixD.1 (1 : H3Octonion ℝ) = 0 :=
      h3Octonion_derivation_apply_one_eq_zero
        (h3OctonionJordanInnerDerivation compactMixX12 compactMixX23)
    rw [mul_comm _ (1 : H3Octonion ℝ), H3Octonion.one_mul_h3Octonion, hd1, mul_zero, sub_zero]
  rw [hval] at h1
  have hc := congrArg (fun w : H3Octonion ℝ => w.c.e4) h1
  change (compactMixX12 * (compactMixX23 * H3Octonion.diagCartan 1 (-1) 0) -
    compactMixX23 * (compactMixX12 * H3Octonion.diagCartan 1 (-1) 0)).c.e4 = 0 at hc
  rw [compactMix_bracket_e4] at hc
  norm_num at hc

/-- Compact `𝔣₄(-52)` vs split `𝔣₄(4)` trace-square signature separation on concrete off-diagonal
operators. -/
theorem compact_f4_vs_split_f4_trace_sq_witness :
    let D := h3OctonionJordanInnerDerivation compactMixX12 compactMixX23
    LinearMap.trace ℝ (H3Octonion ℝ) (D.1 * D.1) < 0 ∧
    0 < LinearMap.trace ℝ (H3Zorn ℝ) (splitF4TracePosWitness.1 * splitF4TracePosWitness.1) ∧
    0 < LinearMap.trace ℝ (H3Octonion ℝ)
      (jordanLmul (R := ℝ) compactMixX12 * jordanLmul (R := ℝ) compactMixX12) := by
  intro D
  refine ⟨?_, ?_, ?_⟩
  · refine lt_of_le_of_ne (compactF4_trace_sq_nonpos D) ?_
    intro htr
    have hD0 := (compactF4_trace_sq_eq_zero_iff D).mp htr
    have h1 := LinearMap.ext_iff.mp (congrArg Subtype.val hD0) (H3Octonion.diagCartan 1 (-1) 0)
    have hc := congrArg (fun w : H3Octonion ℝ => w.c.e4) h1
    change (compactMixX12 * (compactMixX23 * H3Octonion.diagCartan 1 (-1) 0) -
      compactMixX23 * (compactMixX12 * H3Octonion.diagCartan 1 (-1) 0)).c.e4 = 0 at hc
    rw [compactMix_bracket_e4] at hc
    norm_num at hc
  · rw [splitF4TracePosWitness_trace_sq]; norm_num
  · refine lt_of_le_of_ne (compactLmul_trace_sq_nonneg compactMixX12) ?_
    intro htr
    have hx0 := (compactLmul_trace_sq_eq_zero_iff compactMixX12).mp htr.symm
    have ha := congrArg (fun w : H3Octonion ℝ => w.a.e1) hx0
    change (1 : ℝ) = 0 at ha
    norm_num at ha

end Area2Complexification

/-! ## Area 3: `E₆(6)` Chevalley / Bruhat — Non-Borel Bruhat, Commutators & Transitivity -/

section Area3ChevalleyBruhat

/-- Explicit non-Borel Bruhat witness: `g = h3zornSimpleY 0 1 ∉ h3zornBorel`, yet admits an
explicit decomposition `g = b₁ * w * b₂` with `b₁ ∈ h3zornBorel`, `w ∈ h3zornWeylSubgroup`,
`b₂ ∈ h3zornBorel`, and ALL THREE factors strictly `≠ 1`. -/
theorem e6_nontrivial_bruhat_b1_w_b2_witness :
    let g := h3zornSimpleY 0 1
    let b₁ := h3zornSimpleX 0 1
    let w := (h3zornWeylElt 0 1)⁻¹
    let b₂ := h3zornSimpleX 0 1
    g ∉ h3zornBorel ∧
    b₁ ∈ h3zornBorel ∧ w ∈ h3zornWeylSubgroup ∧ b₂ ∈ h3zornBorel ∧
    b₁ ≠ 1 ∧ w ≠ 1 ∧ b₂ ≠ 1 ∧
    g = b₁ * w * b₂ := by
  intro g b₁ w b₂
  have hg_neg : g ∈ h3zornNegUnipotent := by
    change e6SimpleY 0 1 ∈ e6NegUnipotent
    rw [e6SimpleY_eq_rootExp]
    exact Subgroup.subset_closure ⟨fSimpleIdx 0, by decide, (fSimpleSign 0 : ℝ) * 1, rfl⟩
  have hg_ne1 : g ≠ 1 := by
    intro h1
    have hm := congrArg (fun h : h3zornReducedStructureGroup => h3zornToMatrix h.1.toLinearMap) h1
    have hmy : h3zornToMatrix (h3zornSimpleY 0 1).1.toLinearMap =
        1 + (sparseToMat (e6SimpleFSparse 0)).map Int.cast := by
      ext r c
      rw [h3zornToMatrix_apply]
      change h3ZornBasis.repr (h3ZornBasis c + (1 : ℝ) • (e6SimpleF 0).1 (h3ZornBasis c)) r = _
      have hre : h3ZornBasis.repr ((e6SimpleF 0).1 (h3ZornBasis c)) r =
          h3zornToMatrix (e6SimpleF 0).1 r c := by
        rw [h3zornToMatrix_apply]; rfl
      rw [map_add, map_smul, one_smul, Finsupp.add_apply, Module.Basis.repr_self,
        Finsupp.single_apply, hre, h3zornToMatrix_e6SimpleF]
      simp [Matrix.one_apply, eq_comm]
    have hm1 : h3zornToMatrix (1 : h3zornReducedStructureGroup).1.toLinearMap = 1 := by
      show h3zornToMatrix (1 : Module.End ℝ (H3Zorn ℝ)) = 1
      exact _root_.map_one h3zornToMatrix
    rw [hmy, hm1] at hm
    have hnz : sparseZeroCheck (e6SimpleFSparse 0) = false := by decide
    have hzm : sparseZeroCheck (e6SimpleFSparse 0) = true := by
      simp only [sparseZeroCheck, List.all_eq_true, beq_iff_eq]
      intro p _
      have hp := congrFun (congrFun hm p.1) p.2.1
      simp only [Matrix.add_apply, Matrix.one_apply, Matrix.map_apply] at hp
      have hp0 : ((sparseToMat (e6SimpleFSparse 0) p.1 p.2.1 : ℤ) : ℝ) = 0 := by linarith
      exact Int.cast_eq_zero.mp hp0
    rw [hnz] at hzm; cases hzm
  have hb₁ : b₁ ∈ h3zornBorel := by
    have hb_pos : b₁ ∈ h3zornPosUnipotent := by
      change e6SimpleX 0 1 ∈ e6PosUnipotent
      rw [e6SimpleX_eq_rootExp]
      exact Subgroup.subset_closure ⟨eSimpleIdx 0, by decide, 1, rfl⟩
    exact (h3zornBorel_eq_torus_mul_posUnipotent b₁).mpr ⟨1, h3zornTorus.one_mem, b₁, hb_pos,
      (one_mul b₁).symm⟩
  have hw : w ∈ h3zornWeylSubgroup :=
    h3zornWeylSubgroup.inv_mem (Subgroup.subset_closure ⟨0, rfl⟩)
  have hb₁_ne1 : b₁ ≠ 1 := by
    intro h1
    have hm := congrArg (fun h : h3zornReducedStructureGroup => h3zornToMatrix h.1.toLinearMap) h1
    have hmx : h3zornToMatrix (h3zornSimpleX 0 1).1.toLinearMap =
        1 + (sparseToMat (e6SimpleESparse 0)).map Int.cast := by
      ext r c
      rw [h3zornToMatrix_apply]
      change h3ZornBasis.repr (h3ZornBasis c + (1 : ℝ) • (e6SimpleE 0).1 (h3ZornBasis c)) r = _
      have hre : h3ZornBasis.repr ((e6SimpleE 0).1 (h3ZornBasis c)) r =
          h3zornToMatrix (e6SimpleE 0).1 r c := by
        rw [h3zornToMatrix_apply]; rfl
      rw [map_add, map_smul, one_smul, Finsupp.add_apply, Module.Basis.repr_self,
        Finsupp.single_apply, hre, h3zornToMatrix_e6SimpleE]
      simp [Matrix.one_apply, eq_comm]
    have hm1 : h3zornToMatrix (1 : h3zornReducedStructureGroup).1.toLinearMap = 1 := by
      show h3zornToMatrix (1 : Module.End ℝ (H3Zorn ℝ)) = 1
      exact _root_.map_one h3zornToMatrix
    rw [hmx, hm1] at hm
    have hnz : sparseZeroCheck (e6SimpleESparse 0) = false := by decide
    have hzm : sparseZeroCheck (e6SimpleESparse 0) = true := by
      simp only [sparseZeroCheck, List.all_eq_true, beq_iff_eq]
      intro p _
      have hp := congrFun (congrFun hm p.1) p.2.1
      simp only [Matrix.add_apply, Matrix.one_apply, Matrix.map_apply] at hp
      have hp0 : ((sparseToMat (e6SimpleESparse 0) p.1 p.2.1 : ℤ) : ℝ) = 0 := by linarith
      exact Int.cast_eq_zero.mp hp0
    rw [hnz] at hzm; cases hzm
  have hw_ne1 : w ≠ 1 := by
    intro h1
    have hwe : h3zornWeylElt 0 1 = 1 := inv_eq_one.mp h1
    apply h3zornWeylElt_noncomm_witness
    rw [hwe, one_mul, mul_one]
  have hbruhat : g = b₁ * w * b₂ := by
    have hdef : h3zornWeylElt 0 1 =
        h3zornSimpleX 0 1 * h3zornSimpleY 0 (-1) * h3zornSimpleX 0 1 := by
      rw [h3zornWeylElt_eq_e6WeylElt, h3zornSimpleX_eq_e6SimpleX, h3zornSimpleY_eq_e6SimpleY]
      rfl
    have hinv : (h3zornWeylElt 0 1)⁻¹ =
        (h3zornSimpleX 0 1)⁻¹ * (h3zornSimpleY 0 (-1))⁻¹ * (h3zornSimpleX 0 1)⁻¹ := by
      rw [hdef, mul_inv_rev, mul_inv_rev, mul_assoc]
    have hx_inv : (h3zornSimpleX 0 1)⁻¹ = h3zornSimpleX 0 (-1) := by
      rw [h3zornSimpleX_eq_e6SimpleX, h3zornSimpleX_eq_e6SimpleX,
        e6SimpleX_eq_rootExp, e6SimpleX_eq_rootExp, e6RootExp_inv]
    have hy_inv : (h3zornSimpleY 0 (-1))⁻¹ = h3zornSimpleY 0 1 := by
      rw [h3zornSimpleY_eq_e6SimpleY, h3zornSimpleY_eq_e6SimpleY,
        e6SimpleY_eq_rootExp, e6SimpleY_eq_rootExp, e6RootExp_inv]
      simp
    have hmul_x : h3zornSimpleX 0 1 * (h3zornSimpleX 0 1)⁻¹ = 1 := mul_inv_cancel _
    have hmul_x' : (h3zornSimpleX 0 1)⁻¹ * h3zornSimpleX 0 1 = 1 := inv_mul_cancel _
    dsimp [g, b₁, w, b₂]
    calc
      h3zornSimpleY 0 1
          = (h3zornSimpleY 0 (-1))⁻¹ := hy_inv.symm
      _ = (h3zornSimpleX 0 1 * (h3zornSimpleX 0 1)⁻¹) * (h3zornSimpleY 0 (-1))⁻¹ *
            ((h3zornSimpleX 0 1)⁻¹ * h3zornSimpleX 0 1) := by
          rw [hmul_x, hmul_x', one_mul, mul_one]
      _ = h3zornSimpleX 0 1 *
            ((h3zornSimpleX 0 1)⁻¹ * (h3zornSimpleY 0 (-1))⁻¹ * (h3zornSimpleX 0 1)⁻¹) *
            h3zornSimpleX 0 1 := by
          group
      _ = h3zornSimpleX 0 1 * (h3zornWeylElt 0 1)⁻¹ * h3zornSimpleX 0 1 := by
          rw [← hinv]
  refine ⟨?_, hb₁, hw, hb₁, hb₁_ne1, hw_ne1, hb₁_ne1, hbruhat⟩
  intro hmem
  have hm : g ∈ h3zornBorel ⊓ h3zornNegUnipotent := ⟨hmem, hg_neg⟩
  rw [h3zornBorel_inf_negUnipotent_eq_bot, Subgroup.mem_bot] at hm
  exact hg_ne1 hm

/-- Adjacent root-subgroup generators `x_1(1)` and `x_3(1)` do NOT commute in `Str₀(H₃(𝕆_s))`. -/
theorem e6_chevalley_simple_root_subgroups_noncommute :
    h3zornSimpleX 1 1 * h3zornSimpleX 3 1 ≠ h3zornSimpleX 3 1 * h3zornSimpleX 1 1 := by
  intro heq
  have hm := congrArg (fun g : h3zornReducedStructureGroup => h3zornToMatrix g.1.toLinearMap) heq
  have hmx : ∀ i : Fin 6, h3zornToMatrix (h3zornSimpleX i 1).1.toLinearMap =
      1 + (sparseToMat (e6SimpleESparse i)).map Int.cast := by
    intro i
    ext r c
    rw [h3zornToMatrix_apply]
    change h3ZornBasis.repr (h3ZornBasis c + (1 : ℝ) • (e6SimpleE i).1 (h3ZornBasis c)) r = _
    have hre : h3ZornBasis.repr ((e6SimpleE i).1 (h3ZornBasis c)) r =
        h3zornToMatrix (e6SimpleE i).1 r c := by
      rw [h3zornToMatrix_apply]; rfl
    rw [map_add, map_smul, one_smul, Finsupp.add_apply, Module.Basis.repr_self, Finsupp.single_apply,
      hre, h3zornToMatrix_e6SimpleE]
    simp [Matrix.one_apply, eq_comm]
  change h3zornToMatrix ((h3zornSimpleX 1 1).1.toLinearMap * (h3zornSimpleX 3 1).1.toLinearMap) =
    h3zornToMatrix ((h3zornSimpleX 3 1).1.toLinearMap * (h3zornSimpleX 1 1).1.toLinearMap) at hm
  rw [map_mul, map_mul, hmx 1, hmx 3] at hm
  have hcomm :
      ((1 + (sparseToMat (e6SimpleESparse 1)).map (Int.cast : ℤ → ℝ)) *
        (1 + (sparseToMat (e6SimpleESparse 3)).map Int.cast)) -
      ((1 + (sparseToMat (e6SimpleESparse 3)).map Int.cast) *
        (1 + (sparseToMat (e6SimpleESparse 1)).map Int.cast)) =
      (sparseToMat (sparseComm (e6SimpleESparse 1) (e6SimpleESparse 3))).map Int.cast := by
    rw [← sparseToMat_comm_eq]
    noncomm_ring
  have h0 : (sparseToMat (sparseComm (e6SimpleESparse 1) (e6SimpleESparse 3))).map
      (Int.cast : ℤ → ℝ) = 0 := by
    rw [← hcomm, hm, sub_self]
  have hnz : sparseZeroCheck (sparseComm (e6SimpleESparse 1) (e6SimpleESparse 3)) = false := by
    decide
  have hzm : sparseZeroCheck (sparseComm (e6SimpleESparse 1) (e6SimpleESparse 3)) = true := by
    simp only [sparseZeroCheck, List.all_eq_true, beq_iff_eq]
    intro p _
    have hp := congrFun (congrFun h0 p.1) p.2.1
    simp only [Matrix.map_apply, Matrix.zero_apply, Int.cast_eq_zero] at hp
    exact hp
  rw [hnz] at hzm; cases hzm

private theorem h3_one_eq_sum_diag :
    (1 : H3Zorn ℝ) = h3_diag₁ + h3_diag₂ + h3_diag₃ := by
  apply H3Zorn.ext_h3 <;>
    simp [h3_diag₁, h3_diag₂, h3_diag₃, H3Zorn.add_readback, H3Zorn.one_readback]

/-- Non-diagonal rank-1 idempotent transitivity and `F₄(4) = Fix(1)` vs `Str₀` separation
on concrete non-identity witnesses. -/
theorem e6_nondiag_rank1_transitivity_and_fixOne_separation :
    let xRank1 : H3Zorn ℝ := ⟨1, 0, 0, ZornVectorMatrix.E11, 0, 0⟩
    isRankOneIdem xRank1 ∧ xRank1.a ≠ 0 ∧
    (∃ g ∈ h3zornChevalleyE6, g.1 h3_diag₁ = xRank1) ∧
    h3zornWeylElt 1 1 ∈ h3zornReducedStructureFixOne ∧
    h3zornWeylElt 1 1 ≠ 1 ∧
    (⟨h3zornULinearEquiv (⟨1, 1, 1, ZornVectorMatrix.E11, 0, 0⟩ : H3Zorn ℝ) (by
        have h : normCubic (⟨1, 1, 1, ZornVectorMatrix.E11, 0, 0⟩ : H3Zorn ℝ) = 1 := by
          simp [normCubic, ZornVectorMatrix.norm, ZornVectorMatrix.E11,
            ZornVectorMatrix.trace, ZornVectorMatrix.mul, ZornVec3.dot]
        rw [h]; norm_num),
      h3zornULinearEquiv_mem_reducedStructureGroup _ _ (Or.inl (by
        simp [normCubic, ZornVectorMatrix.norm, ZornVectorMatrix.E11,
          ZornVectorMatrix.trace, ZornVectorMatrix.mul, ZornVec3.dot]))⟩ :
        h3zornReducedStructureGroup) ∉ h3zornReducedStructureFixOne := by
  intro xRank1
  have hrk : isRankOneIdem xRank1 := by
    have htr : linearTrace xRank1 = 1 := by simp [xRank1, linearTrace]
    have hadj : H3Zorn.adjointQuad xRank1 = 0 := by
      apply H3Zorn.ext_h3 <;> (try ext i) <;>
        simp [xRank1, H3Zorn.adjointQuad, ZornVectorMatrix.norm, ZornVectorMatrix.E11,
          ZornVectorMatrix.mul, ZornVectorMatrix.conj, ZornVectorMatrix.smul,
          ZornVectorMatrix.sub, ZornVectorMatrix.neg, ZornVectorMatrix.zero,
          ZornVec3.dot, ZornVec3.cross]
    have hmul : xRank1 * xRank1 = xRank1 := by
      change candidateJordanMul xRank1 xRank1 = xRank1
      rw [candidateJordanMul_trace_formula, htr, crossProduct_self, hadj, smul_zero]
      have htr0 : linearTrace (0 : H3Zorn ℝ) = 0 := by simp [linearTrace]
      rw [htr0]
      apply H3Zorn.ext_h3 <;> (try ext i) <;>
        simp [H3Zorn.add_readback, H3Zorn.sub_readback, H3Zorn.smul_readback, H3Zorn.one_readback,
          H3Zorn.zero_readback, ZornVectorMatrix.add, ZornVectorMatrix.sub,
          ZornVectorMatrix.neg, ZornVectorMatrix.smul,
          xRank1, ZornVectorMatrix.E11, ZornVectorMatrix.zero] <;> norm_num
    exact ⟨hmul, htr, hadj⟩
  have hdiag1_idem : isRankOneIdem h3_diag₁ := by
    have htr : linearTrace h3_diag₁ = 1 := by simp [h3_diag₁, linearTrace]
    have hdx : h3_diag₁ = diagCartan 1 0 0 := rfl
    have hadj : H3Zorn.adjointQuad h3_diag₁ = 0 := by
      rw [hdx, adjointQuad_diagCartan]
      apply H3Zorn.ext_h3 <;> (try ext i) <;>
        simp [diagCartan, H3Zorn.zero_readback, ZornVectorMatrix.zero]
    have hmul : h3_diag₁ * h3_diag₁ = h3_diag₁ := by
      change candidateJordanMul h3_diag₁ h3_diag₁ = h3_diag₁
      rw [candidateJordanMul_trace_formula, htr, crossProduct_self, hadj, smul_zero]
      have htr0 : linearTrace (0 : H3Zorn ℝ) = 0 := by simp [linearTrace]
      rw [htr0]
      apply H3Zorn.ext_h3
      all_goals try ext i
      all_goals
        simp [H3Zorn.add_readback, H3Zorn.sub_readback, H3Zorn.smul_readback, H3Zorn.one_readback,
          H3Zorn.zero_readback, ZornVectorMatrix.add, ZornVectorMatrix.sub,
          ZornVectorMatrix.neg, ZornVectorMatrix.smul,
          h3_diag₁, ZornVectorMatrix.zero]
        try norm_num
    exact ⟨hmul, htr, hadj⟩
  have hxa : xRank1.a ≠ 0 := by
    intro h0
    have ha := congrArg ZornVectorMatrix.a h0
    change (1 : ℝ) = 0 at ha
    norm_num at ha
  have hw_fix : h3zornWeylElt 1 1 ∈ h3zornReducedStructureFixOne := by
    have hE1 : ∀ k : Fin 27, k = 0 ∨ k = 1 ∨ k = 2 →
        (e6SimpleE 1).1 (h3ZornBasis k) = 0 := by
      intro k hk
      apply h3ZornBasis.repr.injective
      ext r
      rw [map_zero, Finsupp.zero_apply]
      have hre : h3ZornBasis.repr ((e6SimpleE 1).1 (h3ZornBasis k)) r =
          h3zornToMatrix (e6SimpleE 1 : Module.End ℝ (H3Zorn ℝ)) r k := by
        rw [h3zornToMatrix_apply]; rfl
      rw [hre, h3zornToMatrix_e6SimpleE, Matrix.map_apply]
      have h0 : sparseVal (e6SimpleESparse 1) r k = 0 := by
        rcases hk with rfl | rfl | rfl <;> fin_cases r <;> decide
      change ((sparseVal (e6SimpleESparse 1) r k : ℤ) : ℝ) = 0
      rw [h0, Int.cast_zero]
    have hF1 : ∀ k : Fin 27, k = 0 ∨ k = 1 ∨ k = 2 →
        (e6SimpleF 1).1 (h3ZornBasis k) = 0 := by
      intro k hk
      apply h3ZornBasis.repr.injective
      ext r
      rw [map_zero, Finsupp.zero_apply]
      have hre : h3ZornBasis.repr ((e6SimpleF 1).1 (h3ZornBasis k)) r =
          h3zornToMatrix (e6SimpleF 1 : Module.End ℝ (H3Zorn ℝ)) r k := by
        rw [h3zornToMatrix_apply]; rfl
      rw [hre, h3zornToMatrix_e6SimpleF, Matrix.map_apply]
      have h0 : sparseVal (e6SimpleFSparse 1) r k = 0 := by
        rcases hk with rfl | rfl | rfl <;> fin_cases r <;> decide
      change ((sparseVal (e6SimpleFSparse 1) r k : ℤ) : ℝ) = 0
      rw [h0, Int.cast_zero]
    have hE_one : (e6SimpleE 1).1 (1 : H3Zorn ℝ) = 0 := by
      rw [h3_one_eq_sum_diag, map_add, map_add,
        ← h3ZornBasis_zero, ← h3ZornBasis_one, ← h3ZornBasis_two,
        hE1 0 (Or.inl rfl), hE1 1 (Or.inr (Or.inl rfl)), hE1 2 (Or.inr (Or.inr rfl)),
        add_zero, add_zero]
    have hF_one : (e6SimpleF 1).1 (1 : H3Zorn ℝ) = 0 := by
      rw [h3_one_eq_sum_diag, map_add, map_add,
        ← h3ZornBasis_zero, ← h3ZornBasis_one, ← h3ZornBasis_two,
        hF1 0 (Or.inl rfl), hF1 1 (Or.inr (Or.inl rfl)), hF1 2 (Or.inr (Or.inr rfl)),
        add_zero, add_zero]
    have hx_one : (h3zornSimpleX 1 1).1 (1 : H3Zorn ℝ) = 1 := by
      change (1 : H3Zorn ℝ) + (1 : ℝ) • (e6SimpleE 1).1 1 = 1
      rw [hE_one, smul_zero, add_zero]
    have hy_one : (h3zornSimpleY 1 (-1)).1 (1 : H3Zorn ℝ) = 1 := by
      change (1 : H3Zorn ℝ) + (-1 : ℝ) • (e6SimpleF 1).1 1 = 1
      rw [hF_one, smul_zero, add_zero]
    change (h3zornWeylElt 1 1).1 1 = 1
    have hmul : (h3zornWeylElt 1 1).1 1 =
        (h3zornSimpleX 1 1).1 ((h3zornSimpleY 1 (-1)).1 ((h3zornSimpleX 1 1).1 1)) := by
      simp [h3zornWeylElt, mul_assoc]
    rw [hmul, hx_one, hy_one, hx_one]
  have hw_ne1 : h3zornWeylElt 1 1 ≠ 1 := by
    intro h1
    have hm := congrArg (fun h : h3zornReducedStructureGroup => h3zornToMatrix h.1.toLinearMap) h1
    have hmx : h3zornToMatrix (h3zornSimpleX 1 1).1.toLinearMap =
        ((1 : Matrix (Fin 27) (Fin 27) ℤ) + sparseToMat (e6SimpleESparse 1)).map Int.cast := by
      ext r c
      rw [h3zornToMatrix_apply]
      change h3ZornBasis.repr (h3ZornBasis c + (1 : ℝ) • (e6SimpleE 1).1 (h3ZornBasis c)) r = _
      have hre : h3ZornBasis.repr ((e6SimpleE 1).1 (h3ZornBasis c)) r =
          h3zornToMatrix (e6SimpleE 1).1 r c := by
        rw [h3zornToMatrix_apply]; rfl
      rw [map_add, map_smul, one_smul, Finsupp.add_apply, Module.Basis.repr_self,
        Finsupp.single_apply, hre, h3zornToMatrix_e6SimpleE]
      simp [Matrix.one_apply, eq_comm]
    have hmy : h3zornToMatrix (h3zornSimpleY 1 (-1)).1.toLinearMap =
        ((1 : Matrix (Fin 27) (Fin 27) ℤ) - sparseToMat (e6SimpleFSparse 1)).map Int.cast := by
      ext r c
      rw [h3zornToMatrix_apply]
      change h3ZornBasis.repr (h3ZornBasis c + (-1 : ℝ) • (e6SimpleF 1).1 (h3ZornBasis c)) r = _
      have hre : h3ZornBasis.repr ((e6SimpleF 1).1 (h3ZornBasis c)) r =
          h3zornToMatrix (e6SimpleF 1).1 r c := by
        rw [h3zornToMatrix_apply]; rfl
      rw [map_add, map_smul, neg_one_smul, Finsupp.add_apply, Finsupp.neg_apply,
        Module.Basis.repr_self, Finsupp.single_apply, hre,
        h3zornToMatrix_e6SimpleF]
      simp [Matrix.one_apply, eq_comm, sub_eq_add_neg]
    have hwm : (h3zornWeylElt 1 1).1.toLinearMap =
        (h3zornSimpleX 1 1).1.toLinearMap *
          ((h3zornSimpleY 1 (-1)).1.toLinearMap * (h3zornSimpleX 1 1).1.toLinearMap) := by
      simp [h3zornWeylElt, mul_assoc]
    have hm1 : h3zornToMatrix (1 : h3zornReducedStructureGroup).1.toLinearMap = 1 := by
      show h3zornToMatrix (1 : Module.End ℝ (H3Zorn ℝ)) = 1
      exact _root_.map_one h3zornToMatrix
    rw [hwm, map_mul, map_mul, hmx, hmy, hm1] at hm
    have hv := congrFun (congrFun hm 5) 4
    have h44 : (((((1 : Matrix (Fin 27) (Fin 27) ℤ) + sparseToMat (e6SimpleESparse 1)) *
        (((1 : Matrix (Fin 27) (Fin 27) ℤ) - sparseToMat (e6SimpleFSparse 1)) *
          ((1 : Matrix (Fin 27) (Fin 27) ℤ) + sparseToMat (e6SimpleESparse 1)))).map
            (Int.cast : ℤ → ℝ)) 5 4) = -1 := by
      simp only [Matrix.map_apply, Matrix.mul_apply, Matrix.add_apply, Matrix.sub_apply,
        Matrix.one_apply]
      change ((∑ x : Fin 27, ((if (5 : Fin 27) = x then (1 : ℤ) else 0) +
          sparseVal (e6SimpleESparse 1) 5 x) *
        (∑ x₁ : Fin 27, ((if x = x₁ then (1 : ℤ) else 0) -
          sparseVal (e6SimpleFSparse 1) x x₁) *
          ((if x₁ = 4 then (1 : ℤ) else 0) + sparseVal (e6SimpleESparse 1) x₁ 4)) : ℤ) : ℝ) = -1
      have hchk : (∑ x : Fin 27, ((if (5 : Fin 27) = x then (1 : ℤ) else 0) +
          sparseVal (e6SimpleESparse 1) 5 x) *
        (∑ x₁ : Fin 27, ((if x = x₁ then (1 : ℤ) else 0) -
          sparseVal (e6SimpleFSparse 1) x x₁) *
          ((if x₁ = 4 then (1 : ℤ) else 0) + sparseVal (e6SimpleESparse 1) x₁ 4))) = -1 := by
        decide
      rw [hchk]; norm_num
    have hmulmap : ∀ A B : Matrix (Fin 27) (Fin 27) ℤ,
        A.map (Int.cast : ℤ → ℝ) * B.map Int.cast = (A * B).map Int.cast := by
      intro A B; ext r c; simp [Matrix.mul_apply]
    rw [hmulmap, hmulmap] at hv
    rw [hv] at h44
    simp only [Matrix.one_apply] at h44
    norm_num at h44
  refine ⟨hrk, hxa, h3zornChevalleyE6_transitive_rankOneIdempotent h3_diag₁ xRank1 hdiag1_idem hrk,
    hw_fix, hw_ne1, ?_⟩
  intro hfix
  have hxPosN : normCubic (⟨1, 1, 1, ZornVectorMatrix.E11, 0, 0⟩ : H3Zorn ℝ) ≠ 0 := by
    have h : normCubic (⟨1, 1, 1, ZornVectorMatrix.E11, 0, 0⟩ : H3Zorn ℝ) = 1 := by
      simp [normCubic, ZornVectorMatrix.norm, ZornVectorMatrix.E11,
        ZornVectorMatrix.trace, ZornVectorMatrix.mul, ZornVectorMatrix.zero, ZornVec3.dot]
    rw [h]; norm_num
  have h1 := congrArg (fun w : H3Zorn ℝ => w.a.a)
    (show h3zornULinearEquiv (⟨1, 1, 1, ZornVectorMatrix.E11, 0, 0⟩ : H3Zorn ℝ) hxPosN
      (1 : H3Zorn ℝ) = 1 from hfix)
  rw [h3zornULinearEquiv_apply] at h1
  have hval : (U (⟨1, 1, 1, ZornVectorMatrix.E11, 0, 0⟩ : H3Zorn ℝ) (1 : H3Zorn ℝ)).a.a = 2 := by
    simp [U, traceBilin, H3Zorn.crossProduct, adjointQuad,
      H3Zorn.sub_readback, H3Zorn.add_readback, H3Zorn.smul_readback, H3Zorn.one_readback,
      ZornVectorMatrix.E11, ZornVectorMatrix.norm, ZornVectorMatrix.conj,
      ZornVectorMatrix.mul, ZornVectorMatrix.sub, ZornVectorMatrix.add,
      ZornVectorMatrix.smul, ZornVectorMatrix.neg, ZornVectorMatrix.trace,
      ZornVectorMatrix.zero, ZornVec3.dot, ZornVec3.cross]
    norm_num
  rw [hval] at h1
  change (2 : ℝ) = 0 at h1
  norm_num at h1

end Area3ChevalleyBruhat

/-! ## Area 4: `E₇` TKK — Cross-Grade Brackets, Mixed-Grade Native Faithfulness & `𝔈₇(-25)` -/

section Area4TKK

private theorem h3_off12_one_mul_off23_one :
    embedJ12 (ZornVectorMatrix.one (R := ℝ)) * embedJ23 (ZornVectorMatrix.one (R := ℝ)) =
      (1 / 2 : ℝ) • embedJ31 (ZornVectorMatrix.one (R := ℝ)) := by
  rw [embedJ12_mul_embedJ23]
  have hmul : ZornVectorMatrix.mul (ZornVectorMatrix.conj (ZornVectorMatrix.one (R := ℝ)))
      (ZornVectorMatrix.conj (ZornVectorMatrix.one (R := ℝ))) = ZornVectorMatrix.one := by
    apply ZornVectorMatrix.ext <;>
      simp [ZornVectorMatrix.conj, ZornVectorMatrix.one, ZornVectorMatrix.mul, ZornVec3.dot]
  rw [hmul]

private theorem h3_off12_one_mul_diag1 :
    embedJ12 (ZornVectorMatrix.one (R := ℝ)) * h3_diag₁ =
      (1 / 2 : ℝ) • embedJ12 (ZornVectorMatrix.one (R := ℝ)) := by
  change candidateJordanMul (embedJ12 (ZornVectorMatrix.one (R := ℝ))) h3_diag₁ = _
  rw [candidateJordanMul_trace_formula]
  have hl1 : linearTrace (embedJ12 (ZornVectorMatrix.one (R := ℝ))) = 0 := by
    simp [linearTrace, embedJ12]
  have hl2 : linearTrace h3_diag₁ = 1 := by
    simp [linearTrace, h3_diag₁]
  have hcr : H3Zorn.crossProduct (embedJ12 (ZornVectorMatrix.one (R := ℝ))) h3_diag₁ = 0 := by
    have hdx : h3_diag₁ = diagCartan 1 0 0 := rfl
    rw [H3Zorn.crossProduct_symm, hdx, crossProduct_diagCartan_left]
    apply H3Zorn.ext_h3 <;> (try ext i) <;>
      simp [embedJ12, ZornVectorMatrix.neg, ZornVectorMatrix.smul, ZornVectorMatrix.zero]
  have htr0 : linearTrace (0 : H3Zorn ℝ) = 0 := by simp [linearTrace]
  rw [hl1, hl2, hcr, htr0]
  apply H3Zorn.ext_h3 <;> (try ext i) <;>
    simp [H3Zorn.add_readback, H3Zorn.sub_readback, H3Zorn.smul_readback, H3Zorn.one_readback,
      H3Zorn.zero_readback, ZornVectorMatrix.add, ZornVectorMatrix.sub,
      ZornVectorMatrix.neg, ZornVectorMatrix.smul,
      embedJ12, ZornVectorMatrix.one, ZornVectorMatrix.zero]

private theorem h3_off23_one_mul_diag1 :
    embedJ23 (ZornVectorMatrix.one (R := ℝ)) * h3_diag₁ = 0 := by
  change candidateJordanMul (embedJ23 (ZornVectorMatrix.one (R := ℝ))) h3_diag₁ = 0
  rw [candidateJordanMul_trace_formula]
  have hl1 : linearTrace (embedJ23 (ZornVectorMatrix.one (R := ℝ))) = 0 := by
    simp [linearTrace, embedJ23]
  have hl2 : linearTrace h3_diag₁ = 1 := by
    simp [linearTrace, h3_diag₁]
  have hcr : H3Zorn.crossProduct (embedJ23 (ZornVectorMatrix.one (R := ℝ))) h3_diag₁ =
      -embedJ23 (ZornVectorMatrix.one (R := ℝ)) := by
    have hdx : h3_diag₁ = diagCartan 1 0 0 := rfl
    rw [H3Zorn.crossProduct_symm, hdx, crossProduct_diagCartan_left]
    apply H3Zorn.ext_h3 <;> (try ext i) <;>
      simp [embedJ23, H3Zorn.neg_readback, ZornVectorMatrix.neg, ZornVectorMatrix.smul,
        ZornVectorMatrix.zero]
  have htr23 : linearTrace (-embedJ23 (ZornVectorMatrix.one (R := ℝ))) = 0 := by
    simp [linearTrace, H3Zorn.neg_readback, embedJ23]
  rw [hl1, hl2, hcr, htr23]
  apply H3Zorn.ext_h3 <;> (try ext i) <;>
    simp [H3Zorn.add_readback, H3Zorn.sub_readback, H3Zorn.smul_readback, H3Zorn.one_readback,
      H3Zorn.zero_readback, H3Zorn.neg_readback, ZornVectorMatrix.add, ZornVectorMatrix.sub,
      ZornVectorMatrix.neg, ZornVectorMatrix.smul, embedJ23, ZornVectorMatrix.one,
      ZornVectorMatrix.zero]

/-- Cross-grade bracket `⁅negInj x, posInj y⁆` for non-orthogonal off-diagonal `x, y` produces a
`str` operator with BOTH non-zero `jordanLmul` AND non-zero `F₄` inner derivation components. -/
theorem e7_tkk_cross_grade_both_str_parts_nonzero :
    let x := embedJ12 (ZornVectorMatrix.one (R := ℝ))
    let y := embedJ23 (ZornVectorMatrix.one (R := ℝ))
    let br := ⁅negInj x, posInj y⁆
    br.zero.1 1 ≠ 0 ∧
    (br.zero.1 - jordanLmul (R := ℝ) (br.zero.1 1)) ≠ 0 := by
  intro x y br
  have hbr : br.zero.1 = JordanTKK.tripleD ℝ x y := by
    dsimp [br]; rw [negInj_bracket_posInj]; rfl
  refine ⟨?_, ?_⟩
  · intro h0
    rw [hbr, JordanTKK.tripleD_eq_left_add_inner, LinearMap.add_apply, jordanLmul_apply] at h0
    change x * y * 1 + (jordanInnerDerivationBundled (R := ℝ) x y : Module.End ℝ (H3Zorn ℝ)) 1 = 0 at h0
    have hm1 : ∀ u : H3Zorn ℝ, u * (1 : H3Zorn ℝ) = u := fun u => candidateJordanMul_one_right u
    have hder1 : (jordanInnerDerivationBundled (R := ℝ) x y : Module.End ℝ (H3Zorn ℝ)) 1 = 0 := by
      change x * (y * (1 : H3Zorn ℝ)) - y * (x * (1 : H3Zorn ℝ)) = 0
      rw [hm1, hm1, mul_comm, sub_self]
    rw [hm1, hder1, add_zero] at h0
    have hc := congrArg (fun w : H3Zorn ℝ => w.c.a) h0
    have hmul : (x * y).c.a = (1 / 2 : ℝ) := by
      dsimp [x, y]; rw [h3_off12_one_mul_off23_one]
      simp [H3Zorn.smul_readback, ZornVectorMatrix.smul, embedJ31, ZornVectorMatrix.one]
    rw [hmul] at hc
    change (1 / 2 : ℝ) = 0 at hc
    norm_num at hc
  · intro h0
    rw [hbr, JordanTKK.tripleD_eq_left_add_inner, LinearMap.add_apply, jordanLmul_apply] at h0
    have hm1 : ∀ u : H3Zorn ℝ, u * (1 : H3Zorn ℝ) = u := fun u => candidateJordanMul_one_right u
    have hder1 : (jordanInnerDerivationBundled (R := ℝ) x y : Module.End ℝ (H3Zorn ℝ)) 1 = 0 := by
      change x * (y * (1 : H3Zorn ℝ)) - y * (x * (1 : H3Zorn ℝ)) = 0
      rw [hm1, hm1, mul_comm, sub_self]
    rw [hm1, hder1, add_zero, add_sub_cancel_left] at h0
    have h1 := LinearMap.ext_iff.mp h0 h3_diag₁
    have hc := congrArg (fun w : H3Zorn ℝ => w.c.a) h1
    change (x * (y * h3_diag₁) - y * (x * h3_diag₁)).c.a = 0 at hc
    have hmul : (x * (y * h3_diag₁) - y * (x * h3_diag₁)).c.a = -(1 / 4 : ℝ) := by
      dsimp [x, y]
      rw [h3_off23_one_mul_diag1, h3_off12_one_mul_diag1, mul_zero, zero_sub,
        mul_smul_comm, mul_comm (embedJ23 (ZornVectorMatrix.one (R := ℝ))), h3_off12_one_mul_off23_one]
      simp [H3Zorn.neg_readback, H3Zorn.smul_readback, ZornVectorMatrix.neg, ZornVectorMatrix.smul,
        embedJ31, ZornVectorMatrix.one]
      norm_num
    rw [hmul] at hc
    norm_num at hc

private theorem h3_diag1_mul_diag1 : h3_diag₁ * h3_diag₁ = h3_diag₁ := by
  change candidateJordanMul h3_diag₁ h3_diag₁ = h3_diag₁
  rw [candidateJordanMul_trace_formula]
  have hl1 : linearTrace h3_diag₁ = 1 := by simp [linearTrace, h3_diag₁]
  have hdx : h3_diag₁ = diagCartan 1 0 0 := rfl
  have hadj : H3Zorn.adjointQuad h3_diag₁ = 0 := by
    rw [hdx, adjointQuad_diagCartan]
    apply H3Zorn.ext_h3 <;> (try ext i) <;>
      simp [diagCartan, H3Zorn.zero_readback, ZornVectorMatrix.zero]
  have htr0 : linearTrace (0 : H3Zorn ℝ) = 0 := by simp [linearTrace]
  rw [hl1, crossProduct_self, hadj, smul_zero, htr0]
  apply H3Zorn.ext_h3
  all_goals try ext i
  all_goals
    simp [H3Zorn.add_readback, H3Zorn.sub_readback, H3Zorn.smul_readback, H3Zorn.one_readback,
      H3Zorn.zero_readback, ZornVectorMatrix.add, ZornVectorMatrix.sub,
      ZornVectorMatrix.neg, ZornVectorMatrix.smul,
      h3_diag₁, ZornVectorMatrix.zero]
    try norm_num

private theorem h3_diag2_mul_diag1 : h3_diag₂ * h3_diag₁ = 0 := by
  change candidateJordanMul h3_diag₂ h3_diag₁ = 0
  rw [candidateJordanMul_trace_formula]
  have hl1 : linearTrace h3_diag₂ = 1 := by simp [linearTrace, h3_diag₂]
  have hl2 : linearTrace h3_diag₁ = 1 := by simp [linearTrace, h3_diag₁]
  have hcr : H3Zorn.crossProduct h3_diag₂ h3_diag₁ = h3_diag₃ := by
    have hdx : h3_diag₁ = diagCartan 1 0 0 := rfl
    rw [H3Zorn.crossProduct_symm, hdx, crossProduct_diagCartan_left]
    apply H3Zorn.ext_h3 <;> (try ext i) <;>
      simp [h3_diag₂, h3_diag₃, ZornVectorMatrix.neg, ZornVectorMatrix.smul, ZornVectorMatrix.zero]
  have htr3 : linearTrace h3_diag₃ = 1 := by simp [linearTrace, h3_diag₃]
  rw [hl1, hl2, hcr, htr3]
  apply H3Zorn.ext_h3 <;> (try ext i) <;>
    simp [H3Zorn.add_readback, H3Zorn.sub_readback, H3Zorn.smul_readback, H3Zorn.one_readback,
      H3Zorn.zero_readback, ZornVectorMatrix.add, ZornVectorMatrix.sub,
      ZornVectorMatrix.neg, ZornVectorMatrix.smul,
      h3_diag₁, h3_diag₂, h3_diag₃, ZornVectorMatrix.zero]

/-- Mixed-grade faithfulness of `h3zornTKKToNative` on two elements having non-zero components in
all 3 grades, producing non-zero outputs in ALL THREE grades (`projNeg`, `projZero`, `projPos`). -/
theorem e7_tkk_to_native_faithful_all_three_grades_nonzero :
    let X : H3ZornTKKLie := negInj (1 : H3Zorn ℝ) + h3zornTKKGradeOp + posInj h3_diag₁
    let Y : H3ZornTKKLie := negInj h3_diag₂ + zeroInj ⟨jordanLmul (R := ℝ) h3_diag₁,
      h3zornTKKDatum.jordanLmul_mem_str h3_diag₁⟩ + posInj (1 : H3Zorn ℝ)
    h3zornTKKToNative ⁅X, Y⁆ = tkkBracket (h3zornTKKToNative X) (h3zornTKKToNative Y) ∧
    ⁅X, Y⁆.neg ≠ 0 ∧ ⁅X, Y⁆.zero ≠ 0 ∧ ⁅X, Y⁆.pos ≠ 0 := by
  intro X Y
  let L₁ : h3zornTKKDatum.str :=
    ⟨jordanLmul (R := ℝ) h3_diag₁, h3zornTKKDatum.jordanLmul_mem_str h3_diag₁⟩
  have hbr : ⁅X, Y⁆ =
      (zeroInj ⟨-JordanTKK.tripleD ℝ h3_diag₂ h3_diag₁,
          h3zornTKKDatum.str.neg_mem (h3zornTKKDatum.tripleD_mem_str h3_diag₂ h3_diag₁)⟩ +
        h3zornTKKGradeOp) +
      negInj (-h3_diag₁ + h3_diag₂) +
      posInj (-1 + h3_diag₁) := by
    have hL_comm : (⟨h3zornStrOne.1 ∘ₗ L₁.1 - L₁.1 ∘ₗ h3zornStrOne.1,
        h3zornTKKDatum.str_lie_mem h3zornStrOne.2 L₁.2⟩ : h3zornTKKDatum.str) = 0 := by
      apply Subtype.ext; apply LinearMap.ext; intro z; simp
    have h11 : JordanTKK.tripleD ℝ (1 : H3Zorn ℝ) 1 = LinearMap.id := by
      apply LinearMap.ext; intro z
      rw [JordanTKK.tripleD_apply, JordanTKK.triple]
      change ((1 : H3Zorn ℝ) * 1) * z + (z * 1) * 1 - (1 * z) * 1 = z
      have hm1 : (1 : H3Zorn ℝ) * 1 = 1 := candidateJordanMul_one_right 1
      have hm2 : (1 : H3Zorn ℝ) * z = z := candidateJordanMul_one_left z
      have hm3 : z * (1 : H3Zorn ℝ) = z := candidateJordanMul_one_right z
      rw [hm1, hm2, hm3, hm3]
      abel
    have hG_eq : (zeroInj ⟨JordanTKK.tripleD ℝ (1 : H3Zorn ℝ) 1,
        h3zornTKKDatum.tripleD_mem_str 1 1⟩ : H3ZornTKKLie) = h3zornTKKGradeOp := by
      rw [h3zornTKKGradeOp]
      congr 1; apply Subtype.ext; exact h11.trans h3zornStrOne_coe_eq_id.symm
    have hL1_1 : L₁.1 (1 : H3Zorn ℝ) = h3_diag₁ := by
      change h3_diag₁ * (1 : H3Zorn ℝ) = h3_diag₁
      exact candidateJordanMul_one_right h3_diag₁
    have hL1_adj : h3zornTraceAdjoint L₁.1 h3_diag₁ = h3_diag₁ := by
      change h3zornTraceAdjoint (jordanLmul (R := ℝ) h3_diag₁) h3_diag₁ = h3_diag₁
      rw [h3zornTraceAdjoint_jordanLmul]
      change h3_diag₁ * h3_diag₁ = h3_diag₁
      exact h3_diag1_mul_diag1
    have hG_adj : h3zornTraceAdjoint (h3zornStrOne : Module.End ℝ (H3Zorn ℝ)) 1 = 1 := by
      rw [h3zornStrOne_coe_eq_id, h3zornTraceAdjoint_id, LinearMap.id_apply]
    dsimp [X, Y]
    change ⁅negInj 1 + h3zornTKKGradeOp + posInj h3_diag₁,
        negInj h3_diag₂ + zeroInj L₁ + posInj 1⁆ = _
    simp only [add_lie, lie_add, negInj_bracket_negInj, posInj_bracket_posInj,
      negInj_bracket_zeroInj, negInj_bracket_posInj,
      h3zornTKKGradeOp_bracket_neg, h3zornTKKGradeOp_bracket_zero, h3zornTKKGradeOp_bracket_pos,
      posInj_bracket_negInj, posInj_bracket_zeroInj, hL1_1, hL1_adj, hG_eq]
    simp only [map_neg, map_add]
    abel
  refine ⟨h3zornTKKToNative_bracket X Y, ?_, ?_, ?_⟩
  · intro h0
    rw [hbr] at h0
    have ha := congrArg H3Zorn.α₁ h0
    simp only [JordanTKK.add_neg, JordanTKK.zeroLM_neg, JordanTKK.negLM_neg, JordanTKK.posLM_neg,
      h3zornTKKGradeOp, zeroInj, negInj, posInj, zero_add, add_zero,
      H3Zorn.add_readback, H3Zorn.neg_readback, H3Zorn.zero_readback, h3_diag₁, h3_diag₂] at ha
    norm_num at ha
  · intro h0
    rw [hbr] at h0
    have htd : JordanTKK.tripleD ℝ h3_diag₂ h3_diag₁ 1 = 0 := by
      rw [JordanTKK.tripleD_eq_left_add_inner, LinearMap.add_apply, jordanLmul_apply]
      change h3_diag₂ * h3_diag₁ * 1 +
        (jordanInnerDerivationBundled (R := ℝ) h3_diag₂ h3_diag₁ : Module.End ℝ (H3Zorn ℝ)) 1 = 0
      have hm1 : ∀ u : H3Zorn ℝ, u * (1 : H3Zorn ℝ) = u := fun u => candidateJordanMul_one_right u
      have hder1 : (jordanInnerDerivationBundled (R := ℝ) h3_diag₂ h3_diag₁ :
          Module.End ℝ (H3Zorn ℝ)) 1 = 0 := by
        change h3_diag₂ * (h3_diag₁ * 1) - h3_diag₁ * (h3_diag₂ * 1) = 0
        rw [hm1, hm1, mul_comm, sub_self]
      rw [h3_diag2_mul_diag1, hm1, hder1, add_zero]
    have hact2 : (h3zornStrOne.1 (1 : H3Zorn ℝ)).α₃ = 0 := by
      have hsub : (⟨-JordanTKK.tripleD ℝ h3_diag₂ h3_diag₁,
          h3zornTKKDatum.str.neg_mem (h3zornTKKDatum.tripleD_mem_str h3_diag₂ h3_diag₁)⟩ +
          h3zornStrOne : h3zornTKKDatum.str).1 (1 : H3Zorn ℝ) = 0 := by
        simpa [JordanTKK.add_zero_comp, JordanTKK.zeroLM_zero, JordanTKK.negLM_zero,
          JordanTKK.posLM_zero, h3zornTKKGradeOp, zeroInj, negInj, posInj] using
          LinearMap.ext_iff.mp (congrArg Subtype.val h0) 1
      have hv := congrArg H3Zorn.α₃ hsub
      rw [Submodule.coe_add, LinearMap.add_apply] at hv
      change (-(JordanTKK.tripleD ℝ h3_diag₂ h3_diag₁) 1 + h3zornStrOne.1 1).α₃ = (0 : H3Zorn ℝ).α₃
        at hv
      rw [htd, neg_zero, zero_add] at hv
      simpa [H3Zorn.zero_readback] using hv
    rw [h3zornStrOne_apply, H3Zorn.one_readback] at hact2
    norm_num at hact2
  · intro h0
    rw [hbr] at h0
    have ha := congrArg H3Zorn.α₂ h0
    simp only [JordanTKK.add_pos, JordanTKK.zeroLM_pos, JordanTKK.negLM_pos, JordanTKK.posLM_pos,
      h3zornTKKGradeOp, zeroInj, negInj, posInj, zero_add, add_zero,
      H3Zorn.add_readback, H3Zorn.neg_readback, H3Zorn.one_readback, H3Zorn.zero_readback,
      h3_diag₁] at ha
    norm_num at ha

/-- `E₇` Chevalley junction `5↔6` (`e7SimpleE 5` in `E₆` and `e7SimpleE 6` in grade `-1`) has
non-zero bracket, exact Cartan eigenvalues, and `e7HighestRootIdx` pairs non-trivially with its
opposite root. -/
theorem e7_chevalley_node5_6_and_highest_root_witness :
    ⁅e7SimpleE 5, e7SimpleE 6⁆ ≠ 0 ∧
    ⁅e7SimpleH 5, e7SimpleE 6⁆ = -e7SimpleE 6 ∧
    ⁅e7SimpleH 6, e7SimpleE 5⁆ = -e7SimpleE 5 ∧
    ⁅e7RootVec e7HighestRootIdx, e7RootVec ⟨102, by decide⟩⁆ ≠ 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h0
    have h0' : ⁅e7SimpleE (5 : Fin 6).castSucc, e7SimpleE 6⁆ = 0 := h0
    rw [e7SimpleE_castSucc, e7SimpleE_six] at h0'
    dsimp [h3zornCubicStabilizerToTKK, zeroLieHom] at h0'
    rw [zeroInj_bracket_negInj] at h0'
    have hv := congrArg (fun X : H3ZornTKKLie => X.neg) h0'
    change (e6SimpleE 5).1 (h3ZornBasis 10) = 0 at hv
    have hchk : (List.finRange 27).any (fun r =>
        sparseVal (e6SimpleESparse 5) r 10 != 0) = true := by decide
    rw [List.any_eq_true] at hchk
    rcases hchk with ⟨r, _, hr⟩
    have hr' : sparseVal (e6SimpleESparse 5) r 10 ≠ 0 := by simpa [bne_iff_ne] using hr
    have hrep : h3ZornBasis.repr ((e6SimpleE 5).1 (h3ZornBasis 10)) r = 0 := by
      rw [hv, map_zero, Finsupp.zero_apply]
    have hre : h3ZornBasis.repr ((e6SimpleE 5).1 (h3ZornBasis 10)) r =
        h3zornToMatrix (e6SimpleE 5).1 r 10 := by
      rw [h3zornToMatrix_apply]; rfl
    rw [hre, h3zornToMatrix_e6SimpleE, Matrix.map_apply] at hrep
    exact hr' (Int.cast_eq_zero.mp hrep)
  · rw [e7Simple_bracket_HE]
    have hc : Tag.cartan .E7 (5 : Fin 7) (6 : Fin 7) = -1 := by decide
    rw [hc]; simp
  · rw [e7Simple_bracket_HE]
    have hc : Tag.cartan .E7 (6 : Fin 7) (5 : Fin 7) = -1 := by decide
    rw [hc]; simp
  · have heq1 : e7RootVec e7HighestRootIdx = negInj (h3ZornBasis 3) := by
      simp [e7HighestRootIdx, e7RootVec]
    have heq2 : e7RootVec ⟨102, by decide⟩ = posInj (h3ZornBasis (traceDualIdx 3)) := rfl
    rw [heq1, heq2]
    exact negInj_bracket_posInj_traceDual_ne_zero 3

/-- Compact `𝔈₇(-25)` (`H3OctonionTKKLie`) Cartan involution preserves brackets on mixed-grade
off-diagonal `H3Octonion ℝ` elements, and the Killing form is strictly negative on concrete
compact elements, strictly positive on concrete non-compact elements, and zero across `k ⊥ p`. -/
theorem e7_compact_cartan_involution_and_killing_signs :
    let x12 : H3Octonion ℝ := ⟨0, 0, 0, ⟨0, 1, 0, 0, 0, 0, 0, 0⟩, 0, 0⟩
    let x23 : H3Octonion ℝ := ⟨0, 0, 0, 0, ⟨0, 0, 1, 0, 0, 0, 0, 0⟩, 0⟩
    let D := h3OctonionJordanInnerDerivation x12 x23
    let Xk := (h3OctonionCartanCompactEquiv (x12, D) : H3OctonionTKKLie)
    let Yp := (h3OctonionCartanNoncompactEquiv (x23, x23) : H3OctonionTKKLie)
    h3OctonionCartanInvolution ⁅Xk, Yp⁆ =
      ⁅h3OctonionCartanInvolution Xk, h3OctonionCartanInvolution Yp⁆ ∧
    killingForm ℝ H3OctonionTKKLie Xk Xk < 0 ∧
    0 < killingForm ℝ H3OctonionTKKLie Yp Yp ∧
    killingForm ℝ H3OctonionTKKLie Xk Yp = 0 := by
  intro x12 x23 D Xk Yp
  have hXk_mem : Xk ∈ h3OctonionCartanCompactSubalgebra := (h3OctonionCartanCompactEquiv (x12, D)).2
  have hYp_mem : Yp ∈ h3OctonionCartanNoncompactSubmodule := (h3OctonionCartanNoncompactEquiv (x23, x23)).2
  have hXk_ne : Xk ≠ 0 := by
    intro h0
    have hn := congrArg JordanTKK.neg h0
    have ha := congrArg (fun w : H3Octonion ℝ => w.a.e1) hn
    change (1 : ℝ) = 0 at ha
    norm_num at ha
  have hYp_ne : Yp ≠ 0 := by
    intro h0
    have hn := congrArg JordanTKK.neg h0
    have hb := congrArg (fun w : H3Octonion ℝ => w.b.e2) hn
    change (1 : ℝ) = 0 at hb
    norm_num at hb
  refine ⟨LieEquiv.map_lie h3OctonionCartanInvolution Xk Yp, ?_, ?_, ?_⟩
  · refine lt_of_le_of_ne (killingForm_cartanCompact_nonpos hXk_mem) ?_
    intro h0
    exact hXk_ne ((killingForm_cartanCompact_eq_zero_iff hXk_mem).mp h0)
  · refine lt_of_le_of_ne (killingForm_cartanNoncompact_nonneg hYp_mem) ?_
    intro h0
    exact hYp_ne ((killingForm_cartanNoncompact_eq_zero_iff hYp_mem).mp h0.symm)
  · exact killingForm_cartanCompact_noncompact_ortho hXk_mem hYp_mem

end Area4TKK

/-! ## Area 5: `E₇(7)` 56D Freudenthal — Quartic Cross-Term, Charge Strata & Group Word Tests -/

section Area5Freudenthal

open InfoGeometry.Algebra.H3ZornFreudenthal
open InfoGeometry.Exceptional.Freudenthal

/-- Sign-sensitive `+ ⟨x#, y#⟩` quartic cross-term witness: for `Q = ⟨0, 0, x, x⟩` where
`x = ⟨1, 1, 0, ZornVectorMatrix.E11, 0, 0⟩`, both `⟨x, x⟩ = 2 ≠ 0` and `⟨x#, x#⟩ = 1 ≠ 0`,
yielding `I₄(Q) = ⟨x, x⟩² - 4⟨x#, x#⟩ = 2² - 4·1 = 0` (the wrong `- ⟨x#, y#⟩` sign would give `8`). -/
theorem e7_freudenthal_quartic_cross_term_sign_sensitivity :
    let x : H3Zorn ℝ := ⟨1, 1, 0, ZornVectorMatrix.E11, 0, 0⟩
    let Q : Charge := ⟨0, 0, x, x⟩
    H3Zorn.traceBilin x x = 2 ∧
    H3Zorn.traceBilin (H3Zorn.adjointQuad x) (H3Zorn.adjointQuad x) = 1 ∧
    quarticInvariant Q = 0 := by
  intro x Q
  have hadj : H3Zorn.adjointQuad x = diagCartan 0 0 1 := by
    apply H3Zorn.ext_h3 <;> (try apply ZornVectorMatrix.ext) <;>
      simp [x, H3Zorn.adjointQuad, diagCartan, ZornVectorMatrix.norm, ZornVectorMatrix.E11,
        ZornVectorMatrix.mul, ZornVectorMatrix.zero, ZornVec3.dot,
        ZornVectorMatrix.conj, ZornVectorMatrix.smul, ZornVectorMatrix.sub,
        ZornVectorMatrix.add, ZornVectorMatrix.neg]
  have htx : H3Zorn.traceBilin x x = 2 := by
    simp [x, H3Zorn.traceBilin, ZornVectorMatrix.mul, ZornVectorMatrix.conj,
      ZornVectorMatrix.trace, ZornVectorMatrix.E11, ZornVectorMatrix.zero, ZornVec3.dot]
    norm_num
  have hta : H3Zorn.traceBilin (H3Zorn.adjointQuad x) (H3Zorn.adjointQuad x) = 1 := by
    rw [hadj]
    simp [H3Zorn.traceBilin, diagCartan]
  refine ⟨htx, hta, ?_⟩
  rw [quarticInvariant_expanded]
  dsimp [Q]
  have hnx : normCubic x = 0 := by
    simp [x, normCubic, ZornVectorMatrix.norm, ZornVectorMatrix.E11,
      ZornVectorMatrix.trace, ZornVectorMatrix.mul, ZornVectorMatrix.zero, ZornVec3.dot]
  rw [htx, hta, hnx]
  norm_num

/-- Concrete witnesses separating rank-1 boundary (`x# = 0`), rank-2 boundary (`x# ≠ 0`, `N(x)=0`),
regular `I₄ > 0`, and regular `I₄ < 0` charge strata in the 56D Freudenthal module. -/
theorem e7_freudenthal_charge_strata_separation :
    let Q₁ : Charge := ⟨0, 0, diagCartan 1 0 0, 0⟩
    let Q₂ : Charge := ⟨0, 0, diagCartan 1 1 0, 0⟩
    let Q₃ : Charge := ⟨2, 2, diagCartan 1 0 0, diagCartan 1 0 0⟩
    let Q₄ : Charge := ⟨1, 1, diagCartan 1 1 1, diagCartan 1 0 0⟩
    Boundary Q₁ ∧ H3Zorn.adjointQuad Q₁.x = 0 ∧
    Boundary Q₂ ∧ H3Zorn.adjointQuad Q₂.x ≠ 0 ∧ H3Zorn.normCubic Q₂.x = 0 ∧
    Regular Q₃ ∧ 0 < quarticInvariant Q₃ ∧
    Regular Q₄ ∧ quarticInvariant Q₄ < 0 := by
  intro Q₁ Q₂ Q₃ Q₄
  have hI1 : quarticInvariant Q₁ = 0 := by
    rw [quarticInvariant_expanded]; simp [Q₁]
  have hne1 : Q₁ ≠ 0 := by
    intro h0
    have hα := congrArg (fun q : Charge => q.x.α₁) h0
    change (1 : ℝ) = 0 at hα
    norm_num at hα
  have hax1 : H3Zorn.adjointQuad Q₁.x = 0 := by
    have hdx : Q₁.x = diagCartan 1 0 0 := rfl
    rw [hdx, adjointQuad_diagCartan]
    apply H3Zorn.ext_h3 <;> (try ext i) <;>
      simp [diagCartan, H3Zorn.zero_readback, ZornVectorMatrix.zero]
  have hI2 : quarticInvariant Q₂ = 0 := by
    rw [quarticInvariant_expanded]
    dsimp [Q₂]
    simp [diagCartan, H3Zorn.adjointQuad, H3Zorn.traceBilin,
      ZornVectorMatrix.norm, ZornVectorMatrix.mul, ZornVectorMatrix.conj, ZornVectorMatrix.smul,
      ZornVectorMatrix.sub, ZornVectorMatrix.neg, ZornVectorMatrix.trace, ZornVectorMatrix.zero,
      ZornVec3.dot, ZornVec3.cross]
  have hne2 : Q₂ ≠ 0 := by
    intro h0
    have hα := congrArg (fun q : Charge => q.x.α₁) h0
    change (1 : ℝ) = 0 at hα
    norm_num at hα
  have hax2 : H3Zorn.adjointQuad Q₂.x ≠ 0 := by
    intro h0
    have h3 := congrArg H3Zorn.α₃ h0
    simp [Q₂, diagCartan, H3Zorn.adjointQuad, H3Zorn.zero_readback] at h3
  have hnx2 : H3Zorn.normCubic Q₂.x = 0 := by
    simp [Q₂, diagCartan, normCubic]
  have hI3 : quarticInvariant Q₃ = 9 := by
    rw [quarticInvariant_expanded]
    have hadj : H3Zorn.adjointQuad (diagCartan (1 : ℝ) 0 0) = 0 := by
      rw [adjointQuad_diagCartan]
      apply H3Zorn.ext_h3 <;> (try ext i) <;>
        simp [diagCartan, H3Zorn.zero_readback, ZornVectorMatrix.zero]
    dsimp [Q₃]
    rw [hadj, traceBilin_zero_left]
    simp [diagCartan, H3Zorn.traceBilin, H3Zorn.normCubic]
    norm_num
  have hI4 : quarticInvariant Q₄ = -4 := by
    rw [quarticInvariant_expanded]
    have hadj : H3Zorn.adjointQuad (diagCartan (1 : ℝ) 0 0) = 0 := by
      rw [adjointQuad_diagCartan]
      apply H3Zorn.ext_h3 <;> (try ext i) <;>
        simp [diagCartan, H3Zorn.zero_readback, ZornVectorMatrix.zero]
    dsimp [Q₄]
    rw [hadj, traceBilin_zero_right]
    simp [diagCartan, H3Zorn.traceBilin, H3Zorn.normCubic]
  refine ⟨⟨hI1, hne1⟩, hax1, ⟨hI2, hne2⟩, hax2, hnx2, ?_, ?_, ?_, ?_⟩
  · change quarticInvariant Q₃ ≠ 0; rw [hI3]; norm_num
  · rw [hI3]; norm_num
  · change quarticInvariant Q₄ ≠ 0; rw [hI4]; norm_num
  · rw [hI4]; norm_num

/-- Non-diagonal composed word `g = glUpperTrans (ofAdd A) * glLowerTrans (ofAdd B) * glInversion`
in `freudenthalE7Group` preserves both `symplecticForm` and `quarticInvariant` while acting
non-trivially, and concrete non-identity Levi conjugation evaluations match `Str₀` action and
trace-inverse-adjoint. -/
theorem e7_freudenthal_nondiag_word_and_conjugation :
    let A : H3Zorn ℝ := embedJ12 (ZornVectorMatrix.one (R := ℝ))
    let B : H3Zorn ℝ := embedJ23 (ZornVectorMatrix.E11 (R := ℝ))
    let gWord : ChargeGL :=
      glUpperTrans (Multiplicative.ofAdd A) *
      glLowerTrans (Multiplicative.ofAdd B) *
      glInversion
    let xPos : H3Zorn ℝ := ⟨1, 1, 1, ZornVectorMatrix.E11, 0, 0⟩
    have hxPosN : H3Zorn.normCubic xPos ≠ 0 := by
      have h : H3Zorn.normCubic xPos = 1 := by
        simp [xPos, normCubic, ZornVectorMatrix.norm, ZornVectorMatrix.E11,
          ZornVectorMatrix.trace, ZornVectorMatrix.mul, ZornVectorMatrix.zero, ZornVec3.dot]
      rw [h]; norm_num
    let Lpos : h3zornReducedStructureGroup :=
      ⟨h3zornULinearEquiv xPos hxPosN,
        h3zornULinearEquiv_mem_reducedStructureGroup xPos hxPosN (Or.inl (by
          simp [xPos, normCubic, ZornVectorMatrix.norm, ZornVectorMatrix.E11,
            ZornVectorMatrix.trace, ZornVectorMatrix.mul, ZornVectorMatrix.zero, ZornVec3.dot]))⟩
    let Q₁ : Charge := ⟨1, 2, h3_diag₁, embedJ12 (ZornVectorMatrix.one (R := ℝ))⟩
    let Q₂ : Charge := ⟨-1, 1, B, A⟩
    gWord ∈ freudenthalE7Group ∧
    symplecticForm (gWord • Q₁) (gWord • Q₂) = symplecticForm Q₁ Q₂ ∧
    quarticInvariant (gWord • Q₁) = quarticInvariant Q₁ ∧
    gWord • Q₁ ≠ Q₁ ∧
    leviChargeEquiv Lpos * freudenthalUpperTrans A * (leviChargeEquiv Lpos)⁻¹ =
      freudenthalUpperTrans (Lpos.1 A) ∧
    freudenthalInversion * leviChargeEquiv Lpos * freudenthalInversion⁻¹ =
      leviChargeEquiv (h3zornTraceInverseAdjointReduced Lpos) ∧
    leviChargeEquiv Lpos * freudenthalLowerTrans B * (leviChargeEquiv Lpos)⁻¹ =
      freudenthalLowerTrans (h3zornTraceInverseAdjoint Lpos.1 B) ∧
    Lpos.1 (1 : H3Zorn ℝ) ≠ 1 := by
  intro A B gWord xPos hxPosN Lpos Q₁ Q₂
  have hgMem : gWord ∈ freudenthalE7Group :=
    freudenthalE7Group.mul_mem
      (freudenthalE7Group.mul_mem
        (glUpperTrans_mem_freudenthalE7Group A)
        (glLowerTrans_mem_freudenthalE7Group B))
      glInversion_mem_freudenthalE7Group
  have hinv := freudenthalE7Group_le_invariantSubgroup hgMem
  refine ⟨hgMem, hinv.1 Q₁ Q₂, hinv.2 Q₁, ?_,
    levi_conj_upperTrans Lpos A,
    inversion_conj_levi Lpos,
    levi_conj_lowerTrans Lpos B, ?_⟩
  · intro h0
    have hb := congrArg FreudenthalCharge.beta h0
    have hbeta : (gWord • Q₁).beta = 1 := by
      have h2 : (glInversion • Q₁).beta = 1 := rfl
      have hlow_beta :
          ((glLowerTrans (Multiplicative.ofAdd B) * glInversion) • Q₁).beta =
          (glInversion • Q₁).beta + H3Zorn.traceBilin B (glInversion • Q₁).x -
            H3Zorn.traceBilin (H3Zorn.adjointQuad B) (glInversion • Q₁).y -
            (glInversion • Q₁).alpha * H3Zorn.normCubic B := by
        rw [mul_smul]; exact freudenthalLowerTrans_beta B (glInversion • Q₁)
      have htb1 : H3Zorn.traceBilin B (glInversion • Q₁).x = 0 := by
        change H3Zorn.traceBilin B (-Q₁.y) = 0
        simp [B, Q₁, embedJ23, embedJ12, H3Zorn.traceBilin, H3Zorn.neg_readback,
          ZornVectorMatrix.neg, ZornVectorMatrix.mul, ZornVectorMatrix.conj,
          ZornVectorMatrix.trace, ZornVectorMatrix.zero, ZornVec3.dot]
      have hadjB : H3Zorn.adjointQuad B = 0 := by
        apply H3Zorn.ext_h3 <;> (try ext i) <;>
          simp [B, embedJ23, H3Zorn.adjointQuad, H3Zorn.zero_readback,
            ZornVectorMatrix.norm, ZornVectorMatrix.E11,
            ZornVectorMatrix.mul, ZornVectorMatrix.conj, ZornVectorMatrix.smul,
            ZornVectorMatrix.sub, ZornVectorMatrix.neg, ZornVectorMatrix.zero,
            ZornVec3.dot, ZornVec3.cross]
      have hnB : H3Zorn.normCubic B = 0 := by
        simp [B, embedJ23, normCubic, ZornVectorMatrix.norm, ZornVectorMatrix.E11,
          ZornVectorMatrix.mul, ZornVectorMatrix.trace, ZornVectorMatrix.zero, ZornVec3.dot]
      rw [h2, htb1, hadjB, hnB, traceBilin_zero_left] at hlow_beta
      have hup_beta : (gWord • Q₁).beta =
          ((glLowerTrans (Multiplicative.ofAdd B) * glInversion) • Q₁).beta := by
        dsimp [gWord]; rw [mul_assoc, mul_smul]; rfl
      rw [hup_beta, hlow_beta]
      norm_num
    rw [hbeta] at hb
    change (1 : ℝ) = 2 at hb
    norm_num at hb
  · intro h1
    change h3zornULinearEquiv xPos hxPosN (1 : H3Zorn ℝ) = 1 at h1
    rw [h3zornULinearEquiv_apply] at h1
    have ha := congrArg (fun w : H3Zorn ℝ => w.a.a) h1
    have hval : (U xPos (1 : H3Zorn ℝ)).a.a = 2 := by
      simp [xPos, U, traceBilin, H3Zorn.crossProduct, adjointQuad,
        H3Zorn.sub_readback, H3Zorn.add_readback, H3Zorn.smul_readback, H3Zorn.one_readback,
        ZornVectorMatrix.E11, ZornVectorMatrix.norm, ZornVectorMatrix.conj,
        ZornVectorMatrix.mul, ZornVectorMatrix.sub, ZornVectorMatrix.add,
        ZornVectorMatrix.smul, ZornVectorMatrix.neg, ZornVectorMatrix.trace,
        ZornVectorMatrix.zero, ZornVec3.dot, ZornVec3.cross]
      norm_num
    rw [hval] at ha
    change (2 : ℝ) = 0 at ha
    norm_num at ha

end Area5Freudenthal

/-! ## Area 6: `E₈` 248D Magic Square — All-Sector Equiv, Cross-Sector Brackets & Killing Form -/

section Area6MagicSquareE8

/-- `nativeToSplitTitsE8Equiv` preserves all 3 sectors (`G₂`, `Mixed`, `F₄`) simultaneously on
concrete non-zero elements. -/
theorem e8_native_equiv_all_three_sectors_nontrivial :
    let Dg : G2DerivationCarrier := g2Param 7
    let m : MixedCarrier := zornU 1 ⊗ₜ[ℝ] h3EmbedJ12 ZornVectorMatrix.E11
    let Df : F4DerivationCarrier := f4Inner h3DiagZero₁ (h3EmbedJ12 ZornVectorMatrix.E11)
    let p : NativeTitsCarrier := (Dg, m, Df)
    let q := nativeToSplitTitsE8Equiv p
    q.1 ≠ 0 ∧ q.2.1 ≠ 0 ∧ q.2.2 ≠ 0 ∧ nativeToSplitTitsE8Equiv.symm q = p := by
  intro Dg m Df p q
  refine ⟨?_, ?_, ?_, nativeToSplitTitsE8Equiv.symm_apply_apply p⟩
  · intro h0
    have hDg : Dg = 0 :=
      InfoGeometry.Lie.CanonicalZornDerivation.vectorCanonicalLinearEquiv.injective
        (h0.trans (map_zero _).symm)
    have hroot : e8SimpleE 6 = embedG2 Dg := by
      simp [e8SimpleE, e8ESimpleIdx, e8RootVec, g2LongIdx, Dg]
    have he : embedG2 Dg = 0 := by rw [hDg, map_zero]
    rw [← hroot] at he
    exact e8RootVec_ne_zero (e8ESimpleIdx 6) he
  · intro h0
    have hm0 : m = 0 :=
      mixedCarrierToCoordinateEquiv.injective (h0.trans (map_zero _).symm)
    let f1 : splitOctonionTraceZero →ₗ[ℝ] ℝ :=
      { toFun := fun u => zornBilin u.1 (zornV 1).1
        map_add' := fun _ _ => zornBilin_add_left _ _ _
        map_smul' := fun _ _ => zornBilin_smul_left _ _ _ }
    let f2 : h3TraceZero →ₗ[ℝ] ℝ :=
      { toFun := fun z => traceBilin z.1 (h3EmbedJ12 ZornVectorMatrix.E22).1
        map_add' := fun _ _ => traceBilin_add_left _ _ _
        map_smul' := fun _ _ => traceBilin_smul_left _ _ _ }
    let pair : MixedCarrier →ₗ[ℝ] ℝ :=
      TensorProduct.lift ((LinearMap.lsmul ℝ ℝ).compl₂ f2 ∘ₗ f1)
    have hp0 : pair m = 0 := by rw [hm0, map_zero]
    have hp1 : pair m = -1 := by
      change zornBilin (zornU 1).1 (zornV 1).1 *
        traceBilin (h3EmbedJ12 ZornVectorMatrix.E11).1 (h3EmbedJ12 ZornVectorMatrix.E22).1 = -1
      simp [zornU, zornV, h3EmbedJ12, embedJ12, ZornVectorMatrix.U, ZornVectorMatrix.V,
        ZornVectorMatrix.E11, ZornVectorMatrix.E22, zornBilin, traceBilin,
        ZornVectorMatrix.mul, ZornVectorMatrix.conj, ZornVectorMatrix.trace, ZornVec3.dot,
        ZornVec3.basis]
    rw [hp1] at hp0
    norm_num at hp0
  · intro h0
    have hDf : Df = 0 :=
      f4DerivationToCertifiedEquiv.injective (h0.trans (map_zero _).symm)
    have hact := congrArg (fun D : F4DerivationCarrier => (D : Module.End ℝ (H3Zorn ℝ)) h3_diag₁) hDf
    have ha := congrArg (fun w : H3Zorn ℝ => w.a.a) hact
    have hval : ((Df : Module.End ℝ (H3Zorn ℝ)) h3_diag₁).a.a = -(1 / 2 : ℝ) := by
      dsimp [Df, f4Inner]
      rw [h3ZornJordanInnerDerivation_apply]
      have h12_diag : (h3EmbedJ12 (ZornVectorMatrix.E11 (R := ℝ))).1 * h3_diag₁ =
          (1 / 2 : ℝ) • (h3EmbedJ12 (ZornVectorMatrix.E11 (R := ℝ))).1 := by
        change candidateJordanMul (embedJ12 ZornVectorMatrix.E11) h3_diag₁ = _
        rw [candidateJordanMul_trace_formula]
        have hl1 : linearTrace (embedJ12 (ZornVectorMatrix.E11 (R := ℝ))) = 0 := by
          simp [linearTrace, embedJ12]
        have hl2 : linearTrace h3_diag₁ = 1 := by simp [linearTrace, h3_diag₁]
        have hcr : H3Zorn.crossProduct (embedJ12 (ZornVectorMatrix.E11 (R := ℝ))) h3_diag₁ = 0 := by
          have hdx : h3_diag₁ = diagCartan 1 0 0 := rfl
          rw [H3Zorn.crossProduct_symm, hdx, crossProduct_diagCartan_left]
          apply H3Zorn.ext_h3 <;> (try ext i) <;>
            simp [embedJ12, ZornVectorMatrix.neg, ZornVectorMatrix.smul, ZornVectorMatrix.zero]
        have htr0 : linearTrace (0 : H3Zorn ℝ) = 0 := by simp [linearTrace]
        rw [hl1, hl2, hcr, htr0]
        apply H3Zorn.ext_h3 <;> (try ext i) <;>
          simp [H3Zorn.add_readback, H3Zorn.sub_readback, H3Zorn.smul_readback,
            H3Zorn.one_readback, H3Zorn.zero_readback, ZornVectorMatrix.add, ZornVectorMatrix.sub,
            ZornVectorMatrix.neg, ZornVectorMatrix.smul,
            embedJ12, ZornVectorMatrix.E11, ZornVectorMatrix.zero]
      have hdz_diag : (h3DiagZero₁ : H3Zorn ℝ) * h3_diag₁ = h3_diag₁ := by
        change candidateJordanMul (h3_diag₁ - h3_diag₂) h3_diag₁ = h3_diag₁
        rw [candidateJordanMul_trace_formula]
        have hl1 : linearTrace (h3_diag₁ - h3_diag₂) = 0 := by
          simp [linearTrace, h3_diag₁, h3_diag₂, H3Zorn.sub_readback]
        have hl2 : linearTrace h3_diag₁ = 1 := by simp [linearTrace, h3_diag₁]
        have hcr : H3Zorn.crossProduct (h3_diag₁ - h3_diag₂) h3_diag₁ = -h3_diag₃ := by
          have hdx : h3_diag₁ = diagCartan 1 0 0 := rfl
          rw [H3Zorn.crossProduct_symm, hdx, crossProduct_diagCartan_left]
          apply H3Zorn.ext_h3 <;> (try ext i) <;>
            simp [H3Zorn.sub_readback, H3Zorn.neg_readback, diagCartan, h3_diag₂, h3_diag₃,
              ZornVectorMatrix.neg, ZornVectorMatrix.smul, ZornVectorMatrix.zero]
        have htr3 : linearTrace (-h3_diag₃) = -1 := by
          simp [linearTrace, H3Zorn.neg_readback, h3_diag₃]
        rw [hl1, hl2, hcr, htr3]
        apply H3Zorn.ext_h3
        all_goals try ext i
        all_goals
          simp [H3Zorn.add_readback, H3Zorn.sub_readback, H3Zorn.neg_readback, H3Zorn.smul_readback,
            H3Zorn.one_readback, ZornVectorMatrix.add, ZornVectorMatrix.sub, ZornVectorMatrix.neg,
            ZornVectorMatrix.smul, h3_diag₁, h3_diag₂, h3_diag₃, ZornVectorMatrix.zero]
          try norm_num
      have hdz_12 : (h3DiagZero₁ : H3Zorn ℝ) * (h3EmbedJ12 (ZornVectorMatrix.E11 (R := ℝ))).1 = 0 := by
        change candidateJordanMul (h3_diag₁ - h3_diag₂) (embedJ12 ZornVectorMatrix.E11) = 0
        rw [candidateJordanMul_trace_formula]
        have hl1 : linearTrace (h3_diag₁ - h3_diag₂) = 0 := by
          simp [linearTrace, h3_diag₁, h3_diag₂, H3Zorn.sub_readback]
        have hl2 : linearTrace (embedJ12 (ZornVectorMatrix.E11 (R := ℝ))) = 0 := by
          simp [linearTrace, embedJ12]
        have hcr : H3Zorn.crossProduct (h3_diag₁ - h3_diag₂) (embedJ12 ZornVectorMatrix.E11) = 0 := by
          have hdx : h3_diag₁ - h3_diag₂ = diagCartan 1 (-1) 0 := by
            apply H3Zorn.ext_h3 <;> (try ext i) <;>
              simp [H3Zorn.sub_readback, h3_diag₁, h3_diag₂, diagCartan, ZornVectorMatrix.sub,
                ZornVectorMatrix.add, ZornVectorMatrix.neg, ZornVectorMatrix.zero]
          rw [hdx, crossProduct_diagCartan_left]
          apply H3Zorn.ext_h3 <;> (try ext i) <;>
            simp [embedJ12, ZornVectorMatrix.neg, ZornVectorMatrix.smul, ZornVectorMatrix.zero]
        have htr0 : linearTrace (0 : H3Zorn ℝ) = 0 := by simp [linearTrace]
        rw [hl1, hl2, hcr, htr0]
        apply H3Zorn.ext_h3 <;> (try ext i) <;>
          simp [H3Zorn.add_readback, H3Zorn.sub_readback, H3Zorn.smul_readback,
            H3Zorn.zero_readback, ZornVectorMatrix.add, ZornVectorMatrix.sub,
            ZornVectorMatrix.neg, ZornVectorMatrix.smul, ZornVectorMatrix.zero]
      have h12_mul : (h3EmbedJ12 (ZornVectorMatrix.E11 (R := ℝ))).1 * h3_diag₁ =
          (1 / 2 : ℝ) • (h3EmbedJ12 (ZornVectorMatrix.E11 (R := ℝ))).1 := h12_diag
      change ((h3DiagZero₁ : H3Zorn ℝ) * ((h3EmbedJ12 (ZornVectorMatrix.E11 (R := ℝ))).1 * h3_diag₁) -
        (h3EmbedJ12 (ZornVectorMatrix.E11 (R := ℝ))).1 * ((h3DiagZero₁ : H3Zorn ℝ) * h3_diag₁)).a.a =
        -(1 / 2 : ℝ)
      rw [h12_mul, mul_smul_comm, hdz_12, smul_zero, hdz_diag, zero_sub, h12_mul,
        H3Zorn.neg_readback, H3Zorn.smul_readback]
      simp [ZornVectorMatrix.neg, ZornVectorMatrix.smul, embedJ12, ZornVectorMatrix.E11]
    rw [hval, ZeroMemClass.coe_zero, LinearMap.zero_apply] at ha
    change -(1 / 2 : ℝ) = 0 at ha
    norm_num at ha

/-- `E₈` Magic Square cross-sector brackets: `[G₂, Mixed] ≠ 0`, `[F₄, Mixed] ≠ 0`, AND a
concrete `[Mixed, Mixed]` bracket having ALL THREE sector projections `.g2`, `.mixed`, `.f4`
simultaneously `≠ 0`! -/
theorem e8_magic_square_cross_sector_all_projections_nonzero :
    let Dg : G2DerivationCarrier := g2Param 7
    let Df : F4DerivationCarrier := f4Inner h3DiagZero₁ (h3EmbedJ12 ZornVectorMatrix.E11)
    let a : splitOctonionTraceZero := zornE0
    let b : splitOctonionTraceZero := zornE0 + zornU 0
    let x : h3TraceZero := h3EmbedJ12 ZornVectorMatrix.E11
    let y : h3TraceZero := h3EmbedJ12 ZornVectorMatrix.E22 + h3EmbedJ23 ZornVectorMatrix.E11
    let m₁ : MixedCarrier := a ⊗ₜ[ℝ] x
    let m₂ : MixedCarrier := b ⊗ₜ[ℝ] y
    ⁅embedG2 Dg, embedTensor (zornU 1) x⁆ ≠ 0 ∧
    ⁅embedF4 Df, embedTensor (zornU 0) (h3EmbedJ12 ZornVectorMatrix.E22)⁆ ≠ 0 ∧
    ⁅embedMixed m₁, embedMixed m₂⁆.g2 ≠ 0 ∧
    ⁅embedMixed m₁, embedMixed m₂⁆.mixed ≠ 0 ∧
    ⁅embedMixed m₁, embedMixed m₂⁆.f4 ≠ 0 := by
  intro Dg Df a b x y m₁ m₂
  have hE11_E22 : (embedJ12 (ZornVectorMatrix.E11 (R := ℝ))) *
      embedJ12 ZornVectorMatrix.E22 = (1 / 2 : ℝ) • (h3_diag₁ + h3_diag₂) := by
    rw [embedJ12_mul_embedJ12]
    have hzb : zornBilin (ZornVectorMatrix.E11 (R := ℝ)) ZornVectorMatrix.E22 = 1 := by
      simp [zornBilin, ZornVectorMatrix.E11, ZornVectorMatrix.E22, ZornVectorMatrix.mul,
        ZornVectorMatrix.conj, ZornVectorMatrix.trace, ZornVec3.dot]
    rw [hzb, mul_one]
  have hdz_E22 : (h3DiagZero₁ : H3Zorn ℝ) * embedJ12 (ZornVectorMatrix.E22 (R := ℝ)) = 0 := by
    change candidateJordanMul (h3_diag₁ - h3_diag₂) (embedJ12 ZornVectorMatrix.E22) = 0
    rw [candidateJordanMul_trace_formula]
    have hl1 : linearTrace (h3_diag₁ - h3_diag₂) = 0 := by
      simp [linearTrace, h3_diag₁, h3_diag₂, H3Zorn.sub_readback]
    have hl2 : linearTrace (embedJ12 (ZornVectorMatrix.E22 (R := ℝ))) = 0 := by
      simp [linearTrace, embedJ12]
    have hcr : H3Zorn.crossProduct (h3_diag₁ - h3_diag₂) (embedJ12 ZornVectorMatrix.E22) = 0 := by
      have hdx : h3_diag₁ - h3_diag₂ = diagCartan 1 (-1) 0 := by
        apply H3Zorn.ext_h3 <;> (try ext i) <;>
          simp [H3Zorn.sub_readback, h3_diag₁, h3_diag₂, diagCartan, ZornVectorMatrix.sub,
            ZornVectorMatrix.add, ZornVectorMatrix.neg, ZornVectorMatrix.zero]
      rw [hdx, crossProduct_diagCartan_left]
      apply H3Zorn.ext_h3 <;> (try ext i) <;>
        simp [embedJ12, ZornVectorMatrix.neg, ZornVectorMatrix.smul, ZornVectorMatrix.zero]
    have htr0 : linearTrace (0 : H3Zorn ℝ) = 0 := by simp [linearTrace]
    rw [hl1, hl2, hcr, htr0]
    apply H3Zorn.ext_h3 <;> (try ext i) <;>
      simp [H3Zorn.add_readback, H3Zorn.sub_readback, H3Zorn.smul_readback,
        H3Zorn.zero_readback, ZornVectorMatrix.add, ZornVectorMatrix.sub,
        ZornVectorMatrix.neg, ZornVectorMatrix.smul, ZornVectorMatrix.zero]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro h0
    have hm := congrArg projMixed h0
    rw [bracket_g2_tensor, map_zero] at hm
    let f1 : splitOctonionTraceZero →ₗ[ℝ] ℝ :=
      { toFun := fun u => u.1.v 2
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    let f2 : h3TraceZero →ₗ[ℝ] ℝ :=
      { toFun := fun z => z.1.a.a
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    let pair : MixedCarrier →ₗ[ℝ] ℝ :=
      TensorProduct.lift (LinearMap.lsmul ℝ ℝ |>.compl₂ f2 |>.comp f1)
    have hp0 := congrArg pair hm
    change pair ((g2Act Dg (zornU 1)) ⊗ₜ[ℝ] x) = 0 at hp0
    have hval : pair ((g2Act Dg (zornU 1)) ⊗ₜ[ℝ] x) = (g2Act Dg (zornU 1)).1.v 2 * x.1.a.a := rfl
    rw [hval] at hp0
    have hx1 : x.1.a.a = 1 := by simp [x, h3EmbedJ12, embedJ12, ZornVectorMatrix.E11]
    have hgv : (g2Act Dg (zornU 1)).1.v 2 = -1 := by
      simp [Dg, g2Param, g2Act, zornU, parameterDerivation, parameterAction,
        ZornVectorMatrix.U, ZornVec3.basis]
    rw [hx1, hgv] at hp0
    norm_num at hp0
  · intro h0
    have hm := congrArg projMixed h0
    rw [bracket_f4_tensor, map_zero] at hm
    let f1 : splitOctonionTraceZero →ₗ[ℝ] ℝ :=
      { toFun := fun u => u.1.v 0
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    let f2 : h3TraceZero →ₗ[ℝ] ℝ :=
      { toFun := fun z => z.1.α₁
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    let pair : MixedCarrier →ₗ[ℝ] ℝ :=
      TensorProduct.lift (LinearMap.lsmul ℝ ℝ |>.compl₂ f2 |>.comp f1)
    have hp0 := congrArg pair hm
    change (zornU 0).1.v 0 * (f4Act Df (h3EmbedJ12 ZornVectorMatrix.E22)).1.α₁ = 0 at hp0
    have hu : (zornU 0).1.v 0 = 1 := by simp [zornU, ZornVectorMatrix.U, ZornVec3.basis]
    have hfx : (f4Act Df (h3EmbedJ12 ZornVectorMatrix.E22)).1.α₁ = (1 / 2 : ℝ) := by
      change ((Df : Module.End ℝ (H3Zorn ℝ)) (embedJ12 ZornVectorMatrix.E22)).α₁ = (1 / 2 : ℝ)
      dsimp [Df, f4Inner]
      rw [h3ZornJordanInnerDerivation_apply]
      change ((h3DiagZero₁ : H3Zorn ℝ) * (embedJ12 ZornVectorMatrix.E11 * embedJ12 ZornVectorMatrix.E22) -
        embedJ12 ZornVectorMatrix.E11 * ((h3DiagZero₁ : H3Zorn ℝ) * embedJ12 ZornVectorMatrix.E22)).α₁ =
        (1 / 2 : ℝ)
      rw [hE11_E22, hdz_E22, mul_zero, sub_zero, mul_smul_comm]
      have hdz_sum : (h3DiagZero₁ : H3Zorn ℝ) * (h3_diag₁ + h3_diag₂) = h3DiagZero₁ := by
        change candidateJordanMul (h3_diag₁ - h3_diag₂) (h3_diag₁ + h3_diag₂) = h3_diag₁ - h3_diag₂
        rw [candidateJordanMul_trace_formula]
        have hl1 : linearTrace (h3_diag₁ - h3_diag₂) = 0 := by
          simp [linearTrace, h3_diag₁, h3_diag₂, H3Zorn.sub_readback]
        have hl2 : linearTrace (h3_diag₁ + h3_diag₂) = 2 := by
          simp [linearTrace, h3_diag₁, h3_diag₂, H3Zorn.add_readback]
          norm_num
        have hcr : H3Zorn.crossProduct (h3_diag₁ - h3_diag₂) (h3_diag₁ + h3_diag₂) = 0 := by
          have hdx : h3_diag₁ - h3_diag₂ = diagCartan 1 (-1) 0 := by
            apply H3Zorn.ext_h3 <;> (try ext i) <;>
              simp [H3Zorn.sub_readback, h3_diag₁, h3_diag₂, diagCartan, ZornVectorMatrix.sub,
                ZornVectorMatrix.add, ZornVectorMatrix.neg, ZornVectorMatrix.zero]
          rw [hdx, crossProduct_diagCartan_left]
          apply H3Zorn.ext_h3 <;> (try ext i) <;>
            simp [H3Zorn.add_readback, h3_diag₁, h3_diag₂, ZornVectorMatrix.neg, ZornVectorMatrix.smul,
              ZornVectorMatrix.zero]
        have htr0 : linearTrace (0 : H3Zorn ℝ) = 0 := by simp [linearTrace]
        rw [hl1, hl2, hcr, htr0]
        apply H3Zorn.ext_h3 <;> (try ext i) <;>
          simp [H3Zorn.add_readback, H3Zorn.sub_readback, H3Zorn.smul_readback,
            H3Zorn.one_readback, H3Zorn.zero_readback, ZornVectorMatrix.add, ZornVectorMatrix.sub,
            ZornVectorMatrix.neg, ZornVectorMatrix.smul, h3_diag₁, h3_diag₂,
            ZornVectorMatrix.zero]
      rw [hdz_sum, H3Zorn.smul_readback]
      simp [h3DiagZero₁, h3_diag₁, h3_diag₂, H3Zorn.sub_readback]
    rw [hu, hfx] at hp0
    norm_num at hp0
  · intro h0
    have heq : ⁅embedMixed m₁, embedMixed m₂⁆.g2 =
        ((1 / 3 : ℝ) * traceBilin x.1 y.1) • g2Inner a b := by
      dsimp [m₁, m₂]
      change ⁅embedMixed (a ⊗ₜ[ℝ] x), embedMixed (b ⊗ₜ[ℝ] y)⁆.g2 = _
      rw [← embedTensor_apply, ← embedTensor_apply, bracket_tensor_tensor]
      simp
    rw [heq] at h0
    have hact := congrArg (fun D : G2DerivationCarrier => (g2Act D zornE0).1.v 0) h0
    have htxy : traceBilin x.1 y.1 = 1 := by
      simp [x, y, h3EmbedJ12, h3EmbedJ23, embedJ12, embedJ23, traceBilin,
        H3Zorn.add_readback, ZornVectorMatrix.E11, ZornVectorMatrix.E22, ZornVectorMatrix.mul,
        ZornVectorMatrix.conj, ZornVectorMatrix.trace, ZornVectorMatrix.zero, ZornVec3.dot]
    have hgv : (g2Act (g2Inner a b) zornE0).1.v 0 = -4 := by
      have hg_eq : g2Inner a b = g2Inner zornE0 (zornU 0) := by
        dsimp [a, b]
        rw [← g2InnerLM_apply, map_add, g2InnerLM_apply, g2InnerLM_apply, g2Inner_self, zero_add]
      rw [hg_eq]
      change (zornStanDerivation zornE0.1 (zornU 0).1 zornE0.1).v 0 = -4
      rw [zornStanDerivation_apply_normal_form]
      change (((zornE0.1 * (zornU 0).1 - (zornU 0).1 * zornE0.1) * zornE0.1 -
          zornE0.1 * (zornE0.1 * (zornU 0).1 - (zornU 0).1 * zornE0.1)) -
        3 • ZornVectorMatrix.associator zornE0.1 (zornU 0).1 zornE0.1).v 0 = -4
      have h0z : (3 : ℕ) • (⟨0, fun _ => 0, fun _ => 0, 0⟩ : ZornVectorMatrix ℝ) = 0 :=
        nsmul_zero 3
      simp [zornE0, zornU, ZornVectorMatrix.diagonal, ZornVectorMatrix.U, ZornVec3.basis,
        ZornVectorMatrix.associator, ZornVectorMatrix.mul, ZornVectorMatrix.add,
        ZornVectorMatrix.sub, ZornVectorMatrix.neg, sub_eq_add_neg, h0z,
        ZornVec3.dot, ZornVec3.cross]
      norm_num
    change ((1 / 3 : ℝ) * traceBilin x.1 y.1) * (g2Act (g2Inner a b) zornE0).1.v 0 = 0 at hact
    rw [htxy, hgv] at hact
    norm_num at hact
  · intro h0
    have heq : ⁅embedMixed m₁, embedMixed m₂⁆.mixed = (zornComm0 a b) ⊗ₜ[ℝ] (h3Mul0 x y) := by
      dsimp [m₁, m₂]
      change ⁅embedMixed (a ⊗ₜ[ℝ] x), embedMixed (b ⊗ₜ[ℝ] y)⁆.mixed = _
      rw [← embedTensor_apply, ← embedTensor_apply, bracket_tensor_tensor]
      simp
    rw [heq] at h0
    let f1 : splitOctonionTraceZero →ₗ[ℝ] ℝ :=
      { toFun := fun u => u.1.v 0
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    let f2 : h3TraceZero →ₗ[ℝ] ℝ :=
      { toFun := fun z => z.1.c.b
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    let pair : MixedCarrier →ₗ[ℝ] ℝ :=
      TensorProduct.lift (LinearMap.lsmul ℝ ℝ |>.compl₂ f2 |>.comp f1)
    have hp0 := congrArg pair h0
    change (zornComm0 a b).1.v 0 * (h3Mul0 x y).1.c.b = 0 at hp0
    have hc : (zornComm0 a b).1.v 0 = 2 := by
      have hsub : zornComm0 a b = (2 : ℝ) • zornU 0 := by
        dsimp [a, b]
        rw [← zornComm0LM_apply, map_add, zornComm0LM_apply, zornComm0LM_apply,
          zornComm0_self, zornComm0_zornE0_zornU, zero_add]
      rw [hsub]
      simp [zornU, ZornVectorMatrix.U, ZornVec3.basis]
    have hm : (h3Mul0 x y).1.c.b = (1 / 2 : ℝ) := by
      rw [h3Mul0_coe]
      have hxy_mul : x.1 * y.1 =
          (1 / 2 : ℝ) • (h3_diag₁ + h3_diag₂) + (1 / 2 : ℝ) • embedJ31 ZornVectorMatrix.E22 := by
        dsimp [x, y]
        change embedJ12 ZornVectorMatrix.E11 *
            (embedJ12 ZornVectorMatrix.E22 + embedJ23 ZornVectorMatrix.E11) = _
        rw [mul_add, hE11_E22, embedJ12_mul_embedJ23]
        have hconj : ZornVectorMatrix.mul (ZornVectorMatrix.conj (ZornVectorMatrix.E11 (R := ℝ)))
            (ZornVectorMatrix.conj (ZornVectorMatrix.E11 (R := ℝ))) = ZornVectorMatrix.E22 := by
          apply ZornVectorMatrix.ext <;>
            simp [ZornVectorMatrix.conj, ZornVectorMatrix.E11, ZornVectorMatrix.E22,
              ZornVectorMatrix.mul, ZornVec3.dot]
        rw [hconj]
      have htxy : traceBilin x.1 y.1 = 1 := by
        simp [x, y, h3EmbedJ12, h3EmbedJ23, embedJ12, embedJ23, traceBilin,
          H3Zorn.add_readback, ZornVectorMatrix.E11, ZornVectorMatrix.E22, ZornVectorMatrix.mul,
          ZornVectorMatrix.conj, ZornVectorMatrix.trace, ZornVectorMatrix.zero, ZornVec3.dot]
      rw [hxy_mul, htxy]
      simp [H3Zorn.sub_readback, H3Zorn.add_readback, H3Zorn.smul_readback, H3Zorn.one_readback,
        ZornVectorMatrix.sub, ZornVectorMatrix.add, ZornVectorMatrix.neg, ZornVectorMatrix.smul,
        h3_diag₁, h3_diag₂, embedJ31, ZornVectorMatrix.E22, ZornVectorMatrix.zero]
    rw [hc, hm] at hp0
    norm_num at hp0
  · intro h0
    have heq : ⁅embedMixed m₁, embedMixed m₂⁆.f4 =
        ((-2 : ℝ) * zornBilin a.1 b.1) • f4Inner x y := by
      dsimp [m₁, m₂]
      change ⁅embedMixed (a ⊗ₜ[ℝ] x), embedMixed (b ⊗ₜ[ℝ] y)⁆.f4 = _
      rw [← embedTensor_apply, ← embedTensor_apply, bracket_tensor_tensor]
      simp
    rw [heq] at h0
    have hact := congrArg (fun D : F4DerivationCarrier =>
      ((D : Module.End ℝ (H3Zorn ℝ)) h3_diag₁).c.b) h0
    have hzb : zornBilin a.1 b.1 = -2 := by
      dsimp [a, b]
      simp [zornBilin, ZornVectorMatrix.diagonal, ZornVectorMatrix.U,
        ZornVectorMatrix.add, ZornVectorMatrix.conj, ZornVectorMatrix.mul, ZornVectorMatrix.trace,
        ZornVec3.dot, ZornVec3.basis]
    have hfv : ((f4Inner x y : Module.End ℝ (H3Zorn ℝ)) h3_diag₁).c.b = -(1 / 4 : ℝ) := by
      dsimp [x, y, f4Inner]
      rw [h3ZornJordanInnerDerivation_apply]
      have hy_d1 : (embedJ12 (ZornVectorMatrix.E22 (R := ℝ)) + embedJ23 ZornVectorMatrix.E11) *
          h3_diag₁ = (1 / 2 : ℝ) • embedJ12 ZornVectorMatrix.E22 := by
        rw [add_mul]
        have h12 : embedJ12 (ZornVectorMatrix.E22 (R := ℝ)) * h3_diag₁ =
            (1 / 2 : ℝ) • embedJ12 ZornVectorMatrix.E22 := by
          change candidateJordanMul (embedJ12 ZornVectorMatrix.E22) h3_diag₁ = _
          rw [candidateJordanMul_trace_formula]
          have hl1 : linearTrace (embedJ12 (ZornVectorMatrix.E22 (R := ℝ))) = 0 := by
            simp [linearTrace, embedJ12]
          have hl2 : linearTrace h3_diag₁ = 1 := by simp [linearTrace, h3_diag₁]
          have hcr : H3Zorn.crossProduct (embedJ12 (ZornVectorMatrix.E22 (R := ℝ))) h3_diag₁ = 0 := by
            have hdx : h3_diag₁ = diagCartan 1 0 0 := rfl
            rw [H3Zorn.crossProduct_symm, hdx, crossProduct_diagCartan_left]
            apply H3Zorn.ext_h3 <;> (try ext i) <;>
              simp [embedJ12, ZornVectorMatrix.neg, ZornVectorMatrix.smul, ZornVectorMatrix.zero]
          have htr0 : linearTrace (0 : H3Zorn ℝ) = 0 := by simp [linearTrace]
          rw [hl1, hl2, hcr, htr0]
          apply H3Zorn.ext_h3 <;> (try ext i) <;>
            simp [H3Zorn.add_readback, H3Zorn.sub_readback, H3Zorn.smul_readback,
              H3Zorn.one_readback, H3Zorn.zero_readback, ZornVectorMatrix.add, ZornVectorMatrix.sub,
              ZornVectorMatrix.neg, ZornVectorMatrix.smul, embedJ12, ZornVectorMatrix.E22,
              ZornVectorMatrix.zero]
        have h23 : embedJ23 (ZornVectorMatrix.E11 (R := ℝ)) * h3_diag₁ = 0 := by
          change candidateJordanMul (embedJ23 ZornVectorMatrix.E11) h3_diag₁ = 0
          rw [candidateJordanMul_trace_formula]
          have hl1 : linearTrace (embedJ23 (ZornVectorMatrix.E11 (R := ℝ))) = 0 := by
            simp [linearTrace, embedJ23]
          have hl2 : linearTrace h3_diag₁ = 1 := by simp [linearTrace, h3_diag₁]
          have hcr : H3Zorn.crossProduct (embedJ23 (ZornVectorMatrix.E11 (R := ℝ))) h3_diag₁ =
              -embedJ23 ZornVectorMatrix.E11 := by
            have hdx : h3_diag₁ = diagCartan 1 0 0 := rfl
            rw [H3Zorn.crossProduct_symm, hdx, crossProduct_diagCartan_left]
            apply H3Zorn.ext_h3 <;> (try ext i) <;>
              simp [embedJ23, H3Zorn.neg_readback, ZornVectorMatrix.neg, ZornVectorMatrix.smul,
                ZornVectorMatrix.zero]
          have htr23 : linearTrace (-embedJ23 (ZornVectorMatrix.E11 (R := ℝ))) = 0 := by
            simp [linearTrace, H3Zorn.neg_readback, embedJ23]
          rw [hl1, hl2, hcr, htr23]
          apply H3Zorn.ext_h3 <;> (try ext i) <;>
            simp [H3Zorn.add_readback, H3Zorn.sub_readback, H3Zorn.smul_readback,
              H3Zorn.one_readback, H3Zorn.zero_readback, H3Zorn.neg_readback,
              ZornVectorMatrix.add, ZornVectorMatrix.sub, ZornVectorMatrix.neg,
              ZornVectorMatrix.smul, embedJ23, ZornVectorMatrix.E11, ZornVectorMatrix.zero]
        rw [h12, h23, add_zero]
      have hx_d1 : embedJ12 (ZornVectorMatrix.E11 (R := ℝ)) * h3_diag₁ =
          (1 / 2 : ℝ) • embedJ12 ZornVectorMatrix.E11 := by
        change candidateJordanMul (embedJ12 ZornVectorMatrix.E11) h3_diag₁ = _
        rw [candidateJordanMul_trace_formula]
        have hl1 : linearTrace (embedJ12 (ZornVectorMatrix.E11 (R := ℝ))) = 0 := by
          simp [linearTrace, embedJ12]
        have hl2 : linearTrace h3_diag₁ = 1 := by simp [linearTrace, h3_diag₁]
        have hcr : H3Zorn.crossProduct (embedJ12 (ZornVectorMatrix.E11 (R := ℝ))) h3_diag₁ = 0 := by
          have hdx : h3_diag₁ = diagCartan 1 0 0 := rfl
          rw [H3Zorn.crossProduct_symm, hdx, crossProduct_diagCartan_left]
          apply H3Zorn.ext_h3 <;> (try ext i) <;>
            simp [embedJ12, ZornVectorMatrix.neg, ZornVectorMatrix.smul, ZornVectorMatrix.zero]
        have htr0 : linearTrace (0 : H3Zorn ℝ) = 0 := by simp [linearTrace]
        rw [hl1, hl2, hcr, htr0]
        apply H3Zorn.ext_h3 <;> (try ext i) <;>
          simp [H3Zorn.add_readback, H3Zorn.sub_readback, H3Zorn.smul_readback,
            H3Zorn.one_readback, H3Zorn.zero_readback, ZornVectorMatrix.add, ZornVectorMatrix.sub,
            ZornVectorMatrix.neg, ZornVectorMatrix.smul, embedJ12, ZornVectorMatrix.E11,
            ZornVectorMatrix.zero]
      change (embedJ12 ZornVectorMatrix.E11 *
            ((embedJ12 ZornVectorMatrix.E22 + embedJ23 ZornVectorMatrix.E11) * h3_diag₁) -
          (embedJ12 ZornVectorMatrix.E22 + embedJ23 ZornVectorMatrix.E11) *
            (embedJ12 ZornVectorMatrix.E11 * h3_diag₁)).c.b = -(1 / 4 : ℝ)
      rw [hy_d1, hx_d1, mul_smul_comm, mul_smul_comm, hE11_E22, add_mul,
        mul_comm (embedJ12 ZornVectorMatrix.E22), hE11_E22,
        mul_comm (embedJ23 ZornVectorMatrix.E11), embedJ12_mul_embedJ23]
      have hconj : ZornVectorMatrix.mul (ZornVectorMatrix.conj (ZornVectorMatrix.E11 (R := ℝ)))
          (ZornVectorMatrix.conj (ZornVectorMatrix.E11 (R := ℝ))) = ZornVectorMatrix.E22 := by
        apply ZornVectorMatrix.ext <;>
          simp [ZornVectorMatrix.conj, ZornVectorMatrix.E11, ZornVectorMatrix.E22,
            ZornVectorMatrix.mul, ZornVec3.dot]
      rw [hconj]
      simp [H3Zorn.sub_readback, H3Zorn.add_readback, H3Zorn.smul_readback,
        ZornVectorMatrix.sub, ZornVectorMatrix.add, ZornVectorMatrix.neg, ZornVectorMatrix.smul,
        h3_diag₁, h3_diag₂, embedJ31, ZornVectorMatrix.E22, ZornVectorMatrix.zero]
      norm_num
    change ((-2 : ℝ) * zornBilin a.1 b.1) *
      ((f4Inner x y : Module.End ℝ (H3Zorn ℝ)) h3_diag₁).c.b = 0 at hact
    rw [hzb, hfv] at hact
    norm_num at hact

/-- `E₈` Chevalley `F₄–Mix–G₂` junction (`e8SimpleE 4` in `F₄`, `e8SimpleE 5` in `Mixed`,
`e8SimpleE 6` in `G₂`) and non-vanishing `killingForm ℝ SplitE8Lie` on Cartan and root pairs. -/
theorem e8_chevalley_f4_mix_g2_junction_and_killing_nonzero :
    ⁅e8SimpleE 4, e8SimpleE 5⁆ ≠ 0 ∧
    ⁅e8SimpleE 5, e8SimpleE 6⁆ ≠ 0 ∧
    ⁅e8SimpleH 5, e8SimpleE 6⁆ = -e8SimpleE 6 ∧
    ⁅e8RootVec e8HighestRootIdx, e8RootVec (e8RootNeg e8HighestRootIdx)⁆ ≠ 0 ∧
    killingForm ℝ SplitE8Lie (e8SimpleH 0) (e8SimpleH 0) ≠ 0 ∧
    killingForm ℝ SplitE8Lie (e8SimpleE 0) (e8SimpleF 0) ≠ 0 := by
  have he5 : e8SimpleE 5 ≠ 0 := e8RootVec_ne_zero (e8ESimpleIdx 5)
  refine ⟨?_, ?_, ?_, e8RootVec_bracket_neg_ne_zero e8HighestRootIdx, ?_, ?_⟩
  · intro h0
    have hjac := congrArg (fun X => ⁅e8SimpleF 4, X⁆) h0
    rw [lie_zero, leibniz_lie, ← lie_skew (e8SimpleF 4) (e8SimpleE 4),
      e8Simple_bracket_EF_same 4] at hjac
    have h45 : ⁅e8SimpleF 4, e8SimpleE 5⁆ = 0 := by
      rw [← lie_skew, e8Simple_bracket_EF_ne (by decide : (5 : Fin 8) ≠ 4), neg_zero]
    rw [h45, lie_zero, add_zero, neg_lie, e8Simple_bracket_HE] at hjac
    have hc : Tag.cartan .E8 (4 : Fin 8) (5 : Fin 8) = -1 := by decide
    rw [hc] at hjac
    simp only [Int.cast_neg, Int.cast_one, neg_one_smul, neg_neg] at hjac
    exact he5 hjac
  · intro h0
    have hjac := congrArg (fun X => ⁅e8SimpleF 6, X⁆) h0
    rw [lie_zero, leibniz_lie, ← lie_skew (e8SimpleF 6) (e8SimpleE 5),
      e8Simple_bracket_EF_ne (by decide : (5 : Fin 8) ≠ 6), neg_zero, zero_lie, zero_add] at hjac
    rw [← lie_skew (e8SimpleF 6) (e8SimpleE 6), e8Simple_bracket_EF_same 6, lie_neg, ← lie_skew,
      neg_neg, e8Simple_bracket_HE] at hjac
    have hc : Tag.cartan .E8 (6 : Fin 8) (5 : Fin 8) = -1 := by decide
    rw [hc] at hjac
    simp only [Int.cast_neg, Int.cast_one, neg_one_smul, neg_eq_zero] at hjac
    exact he5 hjac
  · rw [e8Simple_bracket_HE]
    have hc : Tag.cartan .E8 (5 : Fin 8) (6 : Fin 8) = -1 := by decide
    rw [hc]; simp
  · intro h0
    rw [killingForm_apply_apply] at h0
    change LinearMap.trace ℝ SplitE8Lie
      (LieAlgebra.ad ℝ SplitE8Lie (e8SimpleH 0) * LieAlgebra.ad ℝ SplitE8Lie (e8SimpleH 0)) = 0
      at h0
    have htr : LinearMap.trace ℝ SplitE8Lie
        (LieAlgebra.ad ℝ SplitE8Lie (e8SimpleH 0) * LieAlgebra.ad ℝ SplitE8Lie (e8SimpleH 0)) =
        ∑ r : Fin 240, ((e8RootEigenvalue 0 r : ℝ) ^ 2) := by
      rw [LinearMap.trace_eq_matrix_trace ℝ e8ChevalleyBasis]
      have hH : ∀ i : Fin 8,
          LinearMap.toMatrix e8ChevalleyBasis e8ChevalleyBasis
            (LieAlgebra.ad ℝ SplitE8Lie (e8SimpleH 0) * LieAlgebra.ad ℝ SplitE8Lie (e8SimpleH 0))
            (Sum.inl i) (Sum.inl i) = 0 := by
        intro i
        have hc : ⁅e8SimpleH 0, e8SimpleH i⁆ = 0 := e8SimpleH_comm 0 i
        have had : (LieAlgebra.ad ℝ SplitE8Lie (e8SimpleH 0) *
            LieAlgebra.ad ℝ SplitE8Lie (e8SimpleH 0)) (e8ChevalleyBasis (Sum.inl i)) = 0 := by
          simp [Module.End.mul_apply, hc]
        rw [LinearMap.toMatrix_apply, had, map_zero, Finsupp.zero_apply]
      have hR : ∀ r : Fin 240,
          LinearMap.toMatrix e8ChevalleyBasis e8ChevalleyBasis
            (LieAlgebra.ad ℝ SplitE8Lie (e8SimpleH 0) * LieAlgebra.ad ℝ SplitE8Lie (e8SimpleH 0))
            (Sum.inr r) (Sum.inr r) = (e8RootEigenvalue 0 r : ℝ) ^ 2 := by
        intro r
        have had : (LieAlgebra.ad ℝ SplitE8Lie (e8SimpleH 0) *
            LieAlgebra.ad ℝ SplitE8Lie (e8SimpleH 0)) (e8ChevalleyBasis (Sum.inr r)) =
            ((e8RootEigenvalue 0 r : ℝ) ^ 2) • e8ChevalleyBasis (Sum.inr r) := by
          simp only [Module.End.mul_apply, LieAlgebra.ad_apply, e8ChevalleyBasis_inr,
            e8RootVec_bracket_H, lie_smul, smul_smul, sq]
        rw [LinearMap.toMatrix_apply, had, map_smul, Module.Basis.repr_self, Finsupp.smul_apply,
          Finsupp.single_eq_same, smul_eq_mul, mul_one]
      simp [Matrix.trace, Fintype.sum_sum_type, hH, hR]
    rw [htr] at h0
    have hnonneg : ∀ r : Fin 240, r ∈ (Finset.univ : Finset (Fin 240)) →
        (0 : ℝ) ≤ (e8RootEigenvalue 0 r : ℝ) ^ 2 := fun r _ => sq_nonneg _
    have hall := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp h0 (e8ESimpleIdx 0) (Finset.mem_univ _)
    rw [e8RootEigenvalue_simpleE] at hall
    have hc : Tag.cartan .E8 (0 : Fin 8) (0 : Fin 8) = 2 := by decide
    rw [hc] at hall
    norm_num at hall
  · -- `2 * B(E₀, F₀) = B([H₀, E₀], F₀) = B(H₀, [E₀, F₀]) = B(H₀, H₀) ≠ 0`
    intro h0
    have hinv : killingForm ℝ SplitE8Lie ⁅e8SimpleH 0, e8SimpleE 0⁆ (e8SimpleF 0) =
        killingForm ℝ SplitE8Lie (e8SimpleH 0) ⁅e8SimpleE 0, e8SimpleF 0⁆ :=
      LieModule.traceForm_apply_lie_apply ℝ SplitE8Lie SplitE8Lie
        (e8SimpleH 0) (e8SimpleE 0) (e8SimpleF 0)
    have hHE : ⁅e8SimpleH 0, e8SimpleE 0⁆ = (2 : ℝ) • e8SimpleE 0 := by
      rw [e8Simple_bracket_HE]
      have hc : Tag.cartan .E8 (0 : Fin 8) (0 : Fin 8) = 2 := by decide
      rw [hc]; norm_num
    rw [hHE, map_smul, LinearMap.smul_apply, smul_eq_mul, h0, mul_zero,
      e8Simple_bracket_EF_same 0] at hinv
    -- Reuse the exact non-vanishing proof of `killingForm (e8SimpleH 0) (e8SimpleH 0) ≠ 0`:
    have hHH : killingForm ℝ SplitE8Lie (e8SimpleH 0) (e8SimpleH 0) ≠ 0 := by
      intro h0'
      rw [killingForm_apply_apply] at h0'
      change LinearMap.trace ℝ SplitE8Lie
        (LieAlgebra.ad ℝ SplitE8Lie (e8SimpleH 0) * LieAlgebra.ad ℝ SplitE8Lie (e8SimpleH 0)) = 0
        at h0'
      have htr : LinearMap.trace ℝ SplitE8Lie
          (LieAlgebra.ad ℝ SplitE8Lie (e8SimpleH 0) * LieAlgebra.ad ℝ SplitE8Lie (e8SimpleH 0)) =
          ∑ r : Fin 240, ((e8RootEigenvalue 0 r : ℝ) ^ 2) := by
        rw [LinearMap.trace_eq_matrix_trace ℝ e8ChevalleyBasis]
        have hH : ∀ i : Fin 8,
            LinearMap.toMatrix e8ChevalleyBasis e8ChevalleyBasis
              (LieAlgebra.ad ℝ SplitE8Lie (e8SimpleH 0) * LieAlgebra.ad ℝ SplitE8Lie (e8SimpleH 0))
              (Sum.inl i) (Sum.inl i) = 0 := by
          intro i
          have hc : ⁅e8SimpleH 0, e8SimpleH i⁆ = 0 := e8SimpleH_comm 0 i
          have had : (LieAlgebra.ad ℝ SplitE8Lie (e8SimpleH 0) *
              LieAlgebra.ad ℝ SplitE8Lie (e8SimpleH 0)) (e8ChevalleyBasis (Sum.inl i)) = 0 := by
            simp [Module.End.mul_apply, hc]
          rw [LinearMap.toMatrix_apply, had, map_zero, Finsupp.zero_apply]
        have hR : ∀ r : Fin 240,
            LinearMap.toMatrix e8ChevalleyBasis e8ChevalleyBasis
              (LieAlgebra.ad ℝ SplitE8Lie (e8SimpleH 0) * LieAlgebra.ad ℝ SplitE8Lie (e8SimpleH 0))
              (Sum.inr r) (Sum.inr r) = (e8RootEigenvalue 0 r : ℝ) ^ 2 := by
          intro r
          have had : (LieAlgebra.ad ℝ SplitE8Lie (e8SimpleH 0) *
              LieAlgebra.ad ℝ SplitE8Lie (e8SimpleH 0)) (e8ChevalleyBasis (Sum.inr r)) =
              ((e8RootEigenvalue 0 r : ℝ) ^ 2) • e8ChevalleyBasis (Sum.inr r) := by
            simp only [Module.End.mul_apply, LieAlgebra.ad_apply, e8ChevalleyBasis_inr,
              e8RootVec_bracket_H, lie_smul, smul_smul, sq]
          rw [LinearMap.toMatrix_apply, had, map_smul, Module.Basis.repr_self, Finsupp.smul_apply,
            Finsupp.single_eq_same, smul_eq_mul, mul_one]
        simp [Matrix.trace, Fintype.sum_sum_type, hH, hR]
      rw [htr] at h0'
      have hnonneg : ∀ r : Fin 240, r ∈ (Finset.univ : Finset (Fin 240)) →
          (0 : ℝ) ≤ (e8RootEigenvalue 0 r : ℝ) ^ 2 := fun r _ => sq_nonneg _
      have hall := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp h0' (e8ESimpleIdx 0) (Finset.mem_univ _)
      rw [e8RootEigenvalue_simpleE] at hall
      have hc : Tag.cartan .E8 (0 : Fin 8) (0 : Fin 8) = 2 := by decide
      rw [hc] at hall
      norm_num at hall
    exact hHH hinv.symm

end Area6MagicSquareE8

end InfoGeometry.Tests.E6E7E8Tier5Adversarial
