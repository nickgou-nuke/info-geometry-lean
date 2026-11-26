/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.H3ZornJordanTripleBridge
import InfoGeometry.Canonical.H3ZornTKKNative
import InfoGeometry.Algebra.H3ZornReducedStructureLieAlgebra
import InfoGeometry.Algebra.H3ZornStructureGroup
import InfoGeometry.Algebra.H3ZornFreudenthalQuartic
import InfoGeometry.Algebra.H3ZornFreudenthalScaling
import InfoGeometry.Algebra.H3ZornFreudenthalQuarticPolarization
import InfoGeometry.Algebra.FreudenthalComplete
import InfoGeometry.Exceptional.Freudenthal
import InfoGeometry.Exceptional.FreudenthalAction
import InfoGeometry.Exceptional.FreudenthalChargeLinear
import InfoGeometry.Algebra.H3OctonionLieAlgebra
import InfoGeometry.Algebra.H3ZornFreudenthalLeviAction
import InfoGeometry.Algebra.H3ZornFreudenthalE7Group
import InfoGeometry.Algebra.JordanTKKLieAlgebra
import InfoGeometry.Canonical.H3ZornTKKLieAlgebra
import InfoGeometry.Algebra.H3OctonionTKKLieAlgebra
import InfoGeometry.Algebra.H3ZornE7RootSystem
import InfoGeometry.Algebra.H3ZornE7Simplicity

/-!
# E2E Tests for `E₇` 133D TKK & 56D Freudenthal Realization (R2)

Covers all `[IMMEDIATE]`, `[M4-CONTRACT]`, and `[M5-CONTRACT]` Tier 1 and Tier 2
requirements for Features 8–13:
- Feature 8 (`JordanTKKLieAlgebra`): Generic 3-graded Jordan-TKK `LieRing`/`LieAlgebra ℝ`,
  triple product identities, `strLieSubalgebra`, `bracketBilin_leibniz`, `zeroLieHom`,
  and `realJordanTKKDatum` (`sl₂` 3D check on `ℝ`)
- Feature 9 (`H3ZornTKKLieAlgebra`): 133D `𝔈₇(7)` on `H3Zorn ℝ`, faithful bracket
  embedding into `H3ZornTKKNative.TKKCarrier`, `78D ↪ 133D` Levi embedding, grading
  eigenvalues, 3-step nilpotency, and `h3zornTKKGradeOp ∉ range h3zornCubicStabilizerToTKK`
- Feature 10 (`H3OctonionTKKLieAlgebra`): 133D `𝔈₇(-25)` on `H3Octonion ℝ`, Cartan
  involution & signature `-25` (`54 - 79`), Killing sign separation, `IsKilling ℝ`
- Feature 11 (`H3ZornE7RootSystem` & `H3ZornE7Simplicity`): 7D split Cartan `h3zornE7Cartan`,
  126 roots (`e7RootEquiv`), 133D `e7ChevalleyBasis`, `IsTriangularizable`, `IsSimple ℝ`,
  `IsKilling ℝ`, `RootPairing` matching `CartanMatrix.E 7`, and Serre/sl₂ triples
- Feature 12 (`H3ZornFreudenthalLeviAction`): `E₆(6)` Levi action (`Str₀`) on 56D
  `FreudenthalCharge` preserving `symplecticForm` & `quarticInvariant`
- Feature 13 (`H3ZornFreudenthalE7Group`): Concrete `t₊(A)`, `t₋(B)`, and `J` group
  elements preserving `symplecticForm` & `quarticInvariant`
-/

set_option autoImplicit false

namespace InfoGeometry.Tests.E7TKKFreudenthal

open InfoGeometry.Algebra
open InfoGeometry.Algebra.H3Zorn
open InfoGeometry.Algebra.SplitAlbertStructureOperators
open InfoGeometry.Canonical.H3ZornJordanTripleBridge
open InfoGeometry.Canonical.H3ZornTKKNative
open InfoGeometry.Canonical.H3ZornF4PeirceTrialitySplit
open InfoGeometry.Exceptional.Freudenthal

attribute [local instance 100] LieRing.ofAssociativeRing

/-! ## Feature 8: Generic Jordan-TKK Building Blocks (Tier 1 & Tier 2) -/

theorem jordanTriple_outer_symm_and_K_zero_witness :
    let x : H3Zorn ℝ := h3_diag₁
    let y : H3Zorn ℝ := embedJ12 (zorn_basis 0)
    let z : H3Zorn ℝ := h3_diag₂
    jordanTriple x y z = jordanTriple z y x ∧
      jordanTriple x z y - jordanTriple y z x = 0 :=
  ⟨jordanTriple_outer_symm _ _ _, jordanTriple_K_expression_zero _ _ _⟩

theorem jordanTriple_derivation_by_F4 (x y z : H3Zorn ℝ) :
    (f4Basis 0).1 (jordanTriple x y z) =
      jordanTriple ((f4Basis 0).1 x) y z +
        jordanTriple x ((f4Basis 0).1 y) z +
        jordanTriple x y ((f4Basis 0).1 z) :=
  jordanTriple_derivation (f4Basis 0).1 (f4Basis 0).property x y z

theorem kantor_operator_identically_zero (x y : H3Zorn ℝ) :
    kantorOperator x y = 0 :=
  kantorOperator_zero x y

theorem tkk_native_bracket_antisymm_and_self_zero :
    let X : TKKCarrier :=
      { neg := h3_diag₁, zeroOp := jordanLmul (R := ℝ) (1 : H3Zorn ℝ),
        zeroAdj := jordanLmul (R := ℝ) (1 : H3Zorn ℝ), pos := h3_diag₂ }
    let Y : TKKCarrier :=
      { neg := embedJ12 (zorn_basis 0), zeroOp := (f4Basis 0).1,
        zeroAdj := -(f4Basis 0).1, pos := embedJ23 (zorn_basis 1) }
    tkkBracket Y X = tkkNeg (tkkBracket X Y) ∧
      tkkBracket X X = { neg := 0, zeroOp := 0, zeroAdj := 0, pos := 0 } :=
  ⟨tkkBracket_antisymm _ _, tkkBracket_self_zero _⟩

theorem tkk_native_jacobi_neg_neg_pos_nondiag :
    let x : H3Zorn ℝ := embedJ12 (zorn_basis 0)
    let z : H3Zorn ℝ := embedJ23 (zorn_basis 1)
    let xi : H3Zorn ℝ := embedJ31 (zorn_basis 2)
    let X : TKKCarrier := { neg := x, zeroOp := 0, zeroAdj := 0, pos := 0 }
    let Z : TKKCarrier := { neg := z, zeroOp := 0, zeroAdj := 0, pos := 0 }
    let Xi : TKKCarrier := { neg := 0, zeroOp := 0, zeroAdj := 0, pos := xi }
    (tkkBracket X (tkkBracket Z Xi)).neg +
      (tkkBracket Z (tkkBracket Xi X)).neg +
        (tkkBracket Xi (tkkBracket X Z)).neg = 0 :=
  tkk_jacobi_neg_neg_pos _ _ _

theorem structure_lie_subalgebra_79d_split :
    Module.finrank ℝ structureOperatorLieSubalgebra = 79 ∧
    Module.finrank ℝ (H3ZornF4Derivations × H3Zorn ℝ) = 79 := by
  refine ⟨finrank_structureOperatorLieSubalgebra, ?_⟩
  rw [LinearEquiv.finrank_eq structureOperatorDirectSumEquiv,
    finrank_structureOperatorLieSubalgebra]

/-! ## Feature 9: Split `𝔈₇(7)` Grade-0 `str(H₃(𝕆_s))` Building Blocks (Tier 1 & Tier 2) -/

theorem tkk_native_inner_jordanTripleD_bracket (u v : H3Zorn ℝ) :
    ⁅innerDerivation h3_diag₁ (embedJ12 (zorn_basis 0)), jordanTripleD u v⁆ =
      jordanTripleD (innerDerivation h3_diag₁ (embedJ12 (zorn_basis 0)) u) v +
        jordanTripleD u (innerDerivation h3_diag₁ (embedJ12 (zorn_basis 0)) v) ∧
    jordanTripleD u v = jordanLmul (R := ℝ) (u * v) + innerDerivation u v :=
  ⟨innerDerivation_lie_jordanTripleD h3_diag₁ (embedJ12 (zorn_basis 0)) u v,
    jordanTripleD_eq_left_add_inner u v⟩

theorem str_operator_trace_one_eq_27 :
    LinearMap.trace ℝ (H3Zorn ℝ) (jordanLmul (R := ℝ) (1 : H3Zorn ℝ)) = 27 := by
  have htr1 : linearTrace (1 : H3Zorn ℝ) = 3 := by
    simp [linearTrace, one_readback]
    norm_num
  rw [h3Zorn_jordanLmul_operatorTrace_eq_nine_linearTrace, htr1]
  norm_num

theorem str_disjoint_f4_lmul :
    Disjoint H3ZornF4Derivations.toSubmodule h3zornLmulSubmodule ∧
    Disjoint H3ZornF4Derivations.toSubmodule h3zornLmulTraceZeroSubmodule :=
  ⟨disjoint_H3ZornF4Derivations_h3zornLmulSubmodule,
    disjoint_H3ZornF4Derivations_h3zornLmulTraceZeroSubmodule⟩

theorem jordanLmul_one_not_in_str0 :
    jordanLmul (R := ℝ) (1 : H3Zorn ℝ) ∉ h3zornCubicStabilizer := by
  have htr1 : linearTrace (1 : H3Zorn ℝ) = 3 := by
    simp [linearTrace, one_readback]
    norm_num
  rw [jordanLmul_mem_h3zornCubicStabilizer_iff, htr1]
  norm_num

theorem str_coordinate_bracket_and_inner_skew (D E : H3ZornF4Derivations)
    (a b : h3zornTraceZero) :
    ⁅(h3zornCubicStabilizerDirectSumEquiv (D, a) : Module.End ℝ (H3Zorn ℝ)),
      (h3zornCubicStabilizerDirectSumEquiv (E, b) : Module.End ℝ (H3Zorn ℝ))⁆ =
      ⁅(D : Module.End ℝ (H3Zorn ℝ)), (E : Module.End ℝ (H3Zorn ℝ))⁆ +
        (h3ZornJordanInnerDerivation a.1 b.1 : Module.End ℝ (H3Zorn ℝ)) +
        jordanLmul (R := ℝ)
          ((D : Module.End ℝ (H3Zorn ℝ)) b.1 - (E : Module.End ℝ (H3Zorn ℝ)) a.1) ∧
    innerDerivation a.1 b.1 = -innerDerivation b.1 a.1 :=
  ⟨h3zornCubicStabilizer_bracket_coordinate_formula D E a b,
    innerDerivation_skew b.1 a.1⟩

/-! ## Feature 10: Compact `𝔈₇(-25)` Grade-0 `str(H₃(𝕆))` Building Blocks (Tier 1 & Tier 2) -/

theorem compact_str_79d_and_e6_78d_and_f4_52d :
    Module.finrank ℝ h3OctonionStructureLieSubalgebra = 79 ∧
    Module.finrank ℝ h3OctonionCubicStabilizer = 78 ∧
    Module.finrank ℝ H3OctonionF4Derivations = 52 :=
  ⟨finrank_h3OctonionStructureLieSubalgebra,
    finrank_h3OctonionCubicStabilizer,
    finrank_H3OctonionF4Derivations⟩

noncomputable def compact_str_direct_sum_equiv :
    (H3OctonionF4Derivations × H3Octonion ℝ) ≃ₗ[ℝ] h3OctonionStructureLieSubalgebra :=
  h3OctonionStructureDirectSumEquiv

theorem compact_jordan_formal_reality_boundary (x y : H3Octonion ℝ) (h : x * x + y * y = 0) :
    x = 0 ∧ y = 0 :=
  H3Octonion.formal_reality x y h

/-! ## Feature 11: 78D `str₀` vs 79D `str` & Quadratic `U` Identities (Tier 1 & Tier 2) -/

theorem e6_str0_78d_vs_str_79d_dimensions :
    Module.finrank ℝ h3zornCubicStabilizer = 78 ∧
    Module.finrank ℝ h3zornLmulSubmodule = 27 ∧
    Module.finrank ℝ h3zornTraceZero = 26 ∧
    Module.finrank ℝ h3zornLmulTraceZeroSubmodule = 26 :=
  ⟨finrank_h3zornCubicStabilizer, finrank_h3zornLmulSubmodule,
    finrank_h3zornTraceZero, finrank_h3zornLmulTraceZeroSubmodule⟩

theorem h3zorn_U_fundamental_and_cubic_identities (X Y Z : H3Zorn ℝ) :
    U (U X Y) Z = U X (U Y (U X Z)) ∧
    normCubic (U X Y) = normCubic X ^ 2 * normCubic Y ∧
    normCubic (adjointQuad X) = normCubic X ^ 2 ∧
    U (adjointQuad X) (U X Y) = normCubic X ^ 2 • Y ∧
    U X (U (adjointQuad X) Y) = normCubic X ^ 2 • Y :=
  ⟨h3zorn_U_fundamental X Y Z, normCubic_U X Y, normCubic_adjointQuad X,
    U_adjointQuad_U X Y, U_U_adjointQuad X Y⟩

/-! ## Feature 12: 56D `FreudenthalCharge`, `symplecticForm`, and `Str₀` Witnesses (Tier 1 & Tier 2) -/

theorem freudenthal_quartic_slices_concrete (α β : ℝ) (X Y : H3Zorn ℝ) :
    H3ZornFreudenthal.quarticInvariant (H3ZornFreudenthal.scalarCharge α β) = (α * β) ^ 2 ∧
    H3ZornFreudenthal.quarticInvariant (H3ZornFreudenthal.electricCharge α X) =
      -4 * (α * H3Zorn.normCubic X) ∧
    H3ZornFreudenthal.quarticInvariant (H3ZornFreudenthal.magneticCharge β Y) =
      -4 * (β * H3Zorn.normCubic Y) ∧
    H3Zorn.normCubic (1 : H3Zorn ℝ) ≠
      H3ZornFreudenthal.quarticInvariant (H3ZornFreudenthal.electricCharge 1 (1 : H3Zorn ℝ)) :=
  ⟨H3ZornFreudenthal.quarticInvariant_scalarCharge α β,
    H3ZornFreudenthal.quarticInvariant_electricCharge α X,
    H3ZornFreudenthal.quarticInvariant_magneticCharge β Y,
    H3ZornFreudenthal.unit_cubic_ne_unit_electric_quartic⟩

theorem freudenthal_quartic_concrete_values :
    H3ZornFreudenthal.quarticInvariant (H3ZornFreudenthal.scalarCharge 2 3) = 36 ∧
    H3ZornFreudenthal.quarticInvariant (H3ZornFreudenthal.electricCharge 1 1) = -4 ∧
    H3ZornFreudenthal.quarticInvariant (H3ZornFreudenthal.magneticCharge 1 1) = -4 := by
  rw [H3ZornFreudenthal.quarticInvariant_scalarCharge,
    H3ZornFreudenthal.quarticInvariant_electricCharge,
    H3ZornFreudenthal.quarticInvariant_magneticCharge, H3Zorn.normCubic_one]
  norm_num

private noncomputable def diagCartanUnitWitness : H3Zorn ℝ :=
  H3Zorn.diagCartan 1 2 (1 / 2 : ℝ)

private theorem normCubic_diagCartanUnitWitness : normCubic diagCartanUnitWitness = 1 := by
  have h := (H3Zorn.diagCartan_quadratic_U_peirce_laplace_mellin_and_semigroup
    (1 : ℝ) 2 (1 / 2) 1 1 1 1).2.1
  change normCubic diagCartanUnitWitness = 1 * 2 * (1 / 2) at h
  rw [h]
  norm_num

private theorem diagCartanUnitWitness_norm_ne_zero : normCubic diagCartanUnitWitness ≠ 0 := by
  rw [normCubic_diagCartanUnitWitness]
  norm_num

theorem freudenthal_u_reduced_str_witness :
    h3zornULinearEquiv diagCartanUnitWitness diagCartanUnitWitness_norm_ne_zero ∈
      h3zornReducedStructureGroup ∧
    h3zornULinearEquiv diagCartanUnitWitness diagCartanUnitWitness_norm_ne_zero 1 ≠ 1 := by
  refine ⟨h3zornULinearEquiv_mem_reducedStructureGroup diagCartanUnitWitness
    diagCartanUnitWitness_norm_ne_zero (Or.inl normCubic_diagCartanUnitWitness), ?_⟩
  intro h1
  have ha := congrArg (fun W : H3Zorn ℝ => W.α₂) h1
  rw [h3zornULinearEquiv_apply] at ha
  have hU := (H3Zorn.diagCartan_quadratic_U_peirce_laplace_mellin_and_semigroup
    (1 : ℝ) 2 (1 / 2) 1 1 1 (1 : H3Zorn ℝ)).2.2.1
  change U diagCartanUnitWitness (1 : H3Zorn ℝ) = _ at hU
  rw [hU] at ha
  change (2 : ℝ) * 2 * (1 : H3Zorn ℝ).α₂ = (1 : H3Zorn ℝ).α₂ at ha
  have h1a2 : (1 : H3Zorn ℝ).α₂ = 1 := rfl
  rw [h1a2] at ha
  norm_num at ha

theorem freudenthal_zero_charge_neither_regular_nor_boundary :
    H3ZornFreudenthal.quarticInvariant 0 = 0 ∧
    ¬ H3ZornFreudenthal.Regular 0 ∧
    ¬ H3ZornFreudenthal.Boundary 0 := by
  have h0 : (0 : H3ZornFreudenthal.Charge) = H3ZornFreudenthal.scalarCharge 0 0 := by
    ext <;> rfl
  have hq : H3ZornFreudenthal.quarticInvariant 0 = 0 := by
    rw [h0, H3ZornFreudenthal.quarticInvariant_scalarCharge]
    norm_num
  refine ⟨hq, ?_, ?_⟩
  · intro hreg
    exact hreg hq
  · intro hbd
    exact hbd.2 rfl

theorem freudenthal_symplectic_nondegenerate :
    ∀ Q : H3ZornFreudenthal.Charge,
      (∀ P : H3ZornFreudenthal.Charge, H3ZornFreudenthal.symplecticForm Q P = 0) → Q = 0 :=
  symplecticForm_nondegenerate_of_traceBilin_nondegenerate h3zornCubicJordanDatum
    H3Zorn.eq_zero_of_traceBilin_left

theorem freudenthal_symplectic_skew_alternating_and_nonzero
    (Q Q₁ Q₂ : H3ZornFreudenthal.Charge) :
    H3ZornFreudenthal.symplecticForm Q Q = 0 ∧
    H3ZornFreudenthal.symplecticForm Q₂ Q₁ = -H3ZornFreudenthal.symplecticForm Q₁ Q₂ ∧
    H3ZornFreudenthal.symplecticForm
      (H3ZornFreudenthal.scalarCharge 1 0) (H3ZornFreudenthal.scalarCharge 0 1) = 1 := by
  refine ⟨H3ZornFreudenthal.symplecticForm_self Q,
    H3ZornFreudenthal.symplecticForm_skew Q₁ Q₂, ?_⟩
  rw [H3ZornFreudenthal.symplecticForm_expanded]
  simp [H3ZornFreudenthal.scalarCharge]

/-! ## Feature 13: Quartic Scaling, Polarization, Rank-Two, & Strata (Tier 1 & Tier 2) -/

theorem freudenthal_quartic_scaling_and_neg (Q : H3ZornFreudenthal.Charge) :
    H3ZornFreudenthal.quarticInvariant ((2 : ℝ) • Q) =
      16 * H3ZornFreudenthal.quarticInvariant Q ∧
    H3ZornFreudenthal.quarticInvariant (-Q) = H3ZornFreudenthal.quarticInvariant Q := by
  refine ⟨?_, H3ZornFreudenthal.quarticInvariant_neg Q⟩
  rw [H3ZornFreudenthal.quarticInvariant_smul]
  norm_num

theorem freudenthal_quartic_polarization_diagonal (Q : H3ZornFreudenthal.Charge) :
    H3ZornFreudenthal.quarticPolarization (fun _ => Q) =
      H3ZornFreudenthal.quarticInvariant Q :=
  H3ZornFreudenthal.quarticPolarization_diagonal Q

theorem freudenthal_symplectic_rank_two_in_subalgebra
    (Q₁ Q₂ : H3ZornFreudenthal.Charge) :
    symplecticRankTwo h3zornCubicJordanDatum Q₁ Q₂ ∈
      symplecticOperatorLieSubalgebra h3zornCubicJordanDatum :=
  symplecticRankTwo_mem_subalgebra h3zornCubicJordanDatum Q₁ Q₂

theorem freudenthal_rank1_boundary_witness :
    let Q := H3ZornFreudenthal.electricCharge 1 (H3Zorn.diagCartan 1 0 0)
    H3ZornFreudenthal.Boundary Q ∧ Q ≠ 0 := by
  intro Q
  have hN : H3Zorn.normCubic (H3Zorn.diagCartan (1 : ℝ) 0 0) = 0 := by
    have h := (H3Zorn.diagCartan_quadratic_U_peirce_laplace_mellin_and_semigroup
      (1 : ℝ) 0 0 1 1 1 1).2.1
    rw [h]
    norm_num
  have hq : H3ZornFreudenthal.quarticInvariant Q = 0 := by
    dsimp [Q]
    rw [H3ZornFreudenthal.quarticInvariant_electricCharge, hN]
    norm_num
  have hnz : Q ≠ 0 := by
    intro hz
    have hα := congrArg FreudenthalCharge.alpha hz
    change (1 : ℝ) = 0 at hα
    norm_num at hα
  exact ⟨⟨hq, hnz⟩, hnz⟩

theorem freudenthal_regular_unit_electric_witness :
    H3ZornFreudenthal.Regular (H3ZornFreudenthal.electricCharge 1 (1 : H3Zorn ℝ)) := by
  change H3ZornFreudenthal.quarticInvariant (H3ZornFreudenthal.electricCharge 1 1) ≠ 0
  rw [H3ZornFreudenthal.unit_electric_quartic]
  norm_num

theorem freudenthal_complete_diagonal_and_jordan_law :
    InfoGeometry.Algebra.H3ZornJordanProductLaw ∧
    CubicJordanOs.AlbertMatrix.adjointQuad (CubicJordanOs.AlbertMatrix.adjointQuad
      { α₁ := (1 : ℝ), α₂ := (0 : ℝ), α₃ := (0 : ℝ)
        z₁ := InfoGeometry.OperatorAlgebra.SplitOctonions.Multiplication.zeroZ
        z₂ := InfoGeometry.OperatorAlgebra.SplitOctonions.Multiplication.zeroZ
        z₃ := InfoGeometry.OperatorAlgebra.SplitOctonions.Multiplication.zeroZ }) =
    (CubicJordanOs.AlbertMatrix.normCubic
      { α₁ := (1 : ℝ), α₂ := (0 : ℝ), α₃ := (0 : ℝ)
        z₁ := InfoGeometry.OperatorAlgebra.SplitOctonions.Multiplication.zeroZ
        z₂ := InfoGeometry.OperatorAlgebra.SplitOctonions.Multiplication.zeroZ
        z₃ := InfoGeometry.OperatorAlgebra.SplitOctonions.Multiplication.zeroZ } : ℝ) •
    { α₁ := (1 : ℝ), α₂ := (0 : ℝ), α₃ := (0 : ℝ)
      z₁ := InfoGeometry.OperatorAlgebra.SplitOctonions.Multiplication.zeroZ
      z₂ := InfoGeometry.OperatorAlgebra.SplitOctonions.Multiplication.zeroZ
      z₃ := InfoGeometry.OperatorAlgebra.SplitOctonions.Multiplication.zeroZ } :=
  ⟨FreudenthalComplete.freudenthal_jordan_product,
    FreudenthalComplete.freudenthal_diag_one_zero_zero⟩

section M4TKKAndE7

/-! ## [M4-CONTRACT] Feature 8: Generic Jordan-TKK `LieAlgebra ℝ` (Tier 1 & Tier 2) -/

section Feature8GenericJordanTKK

theorem m4_jordanTKK_triple_identities {R J : Type*} [CommRing R] [Invertible (2 : R)]
    [NonUnitalNonAssocCommRing J] [Module R J] [SMulCommClass R J J] [IsScalarTower R J J]
    [IsCommJordan J] (D : JordanTKKDatum R J) (d : NonAssocDerivation.derivations R J)
    (T : D.str) (a x y z : J) :
    JordanTKK.triple x y z = JordanTKK.triple z y x ∧
    JordanTKK.tripleD R x y =
      jordanLmul (R := R) (x * y) + (jordanInnerDerivationBundled (R := R) x y : Module.End R J) ∧
    (d : Module.End R J) ∘ₗ JordanTKK.tripleD R x y -
        JordanTKK.tripleD R x y ∘ₗ (d : Module.End R J) =
      JordanTKK.tripleD R ((d : Module.End R J) x) y +
        JordanTKK.tripleD R x ((d : Module.End R J) y) ∧
    jordanLmul (R := R) a ∘ₗ JordanTKK.tripleD R x y -
        JordanTKK.tripleD R x y ∘ₗ jordanLmul (R := R) a =
      JordanTKK.tripleD R (a * x) y - JordanTKK.tripleD R x (a * y) ∧
    D.adj (JordanTKK.tripleD R x y) = JordanTKK.tripleD R y x ∧
    T.1 ∘ₗ JordanTKK.tripleD R x y - JordanTKK.tripleD R x y ∘ₗ T.1 =
      JordanTKK.tripleD R (T.1 x) y - JordanTKK.tripleD R x (D.adj T.1 y) :=
  ⟨JordanTKK.triple_outer_symm x y z, JordanTKK.tripleD_eq_left_add_inner x y,
    JordanTKK.derivation_comm_tripleD d x y, JordanTKK.jordanLmul_comm_tripleD a x y,
    D.adj_tripleD x y, D.str_comm_tripleD T x y⟩

theorem m4_jordanTKK_datum_str_and_finrank {F J : Type*} [Field F] [Invertible (2 : F)]
    [NonUnitalNonAssocCommRing J] [Module F J] [SMulCommClass F J J] [IsScalarTower F J J]
    [IsCommJordan J] [Module.Finite F J] [Module.Finite F (Module.End F J)]
    (D : JordanTKKDatum F J) (x y : J) {T : Module.End F J} (hT : T ∈ D.str) :
    JordanTKK.tripleD F x y ∈ D.str ∧
    D.adj T ∈ D.str ∧
    (D.strLieSubalgebra.toSubmodule = D.str) ∧
    Module.finrank F (JordanTKK J D.str) = 2 * Module.finrank F J + Module.finrank F D.str :=
  ⟨D.tripleD_mem_str x y, D.adj_mem_str hT, rfl,
    JordanTKK.finrank_jordanTKK_two_mul (F := F) (J := J) (S := D.str)⟩

theorem m4_jordanTKK_bracket_leibniz_and_lieAlgebra {R J : Type*} [CommRing R] [Invertible (2 : R)]
    [NonUnitalNonAssocCommRing J] [Module R J] [SMulCommClass R J J] [IsScalarTower R J J]
    [IsCommJordan J] (D : JordanTKKDatum R J) (X Y Z : JordanTKK J D.str) :
    let _ : LieRing (JordanTKK J D.str) := JordanTKK.lieRing D
    let _ : LieAlgebra R (JordanTKK J D.str) := JordanTKK.lieAlgebra D
    JordanTKK.bracketBilin D X (JordanTKK.bracketBilin D Y Z) =
      JordanTKK.bracketBilin D (JordanTKK.bracketBilin D X Y) Z +
        JordanTKK.bracketBilin D Y (JordanTKK.bracketBilin D X Z) ∧
    ⁅X, ⁅Y, Z⁆⁆ = ⁅⁅X, Y⁆, Z⁆ + ⁅Y, ⁅X, Z⁆⁆ ∧
    (∑ i : JordanTKK.TKKGrade, JordanTKK.gradeProj (R := R) i X) = X := by
  let _ : LieRing (JordanTKK J D.str) := JordanTKK.lieRing D
  let _ : LieAlgebra R (JordanTKK J D.str) := JordanTKK.lieAlgebra D
  exact ⟨JordanTKK.bracketBilin_leibniz D X Y Z, leibniz_lie X Y Z,
    JordanTKK.gradeProj_sum (R := R) X⟩

theorem m4_jordanTKK_zeroLieHom_and_injections {R J : Type*} [CommRing R] [Invertible (2 : R)]
    [NonUnitalNonAssocCommRing J] [Module R J] [SMulCommClass R J J] [IsScalarTower R J J]
    [IsCommJordan J] (D : JordanTKKDatum R J) (T₁ T₂ : D.strLieSubalgebra) :
    let _ : LieRing (JordanTKK J D.str) := JordanTKK.lieRing D
    let _ : LieAlgebra R (JordanTKK J D.str) := JordanTKK.lieAlgebra D
    Function.Injective (JordanTKK.zeroLieHom D) ∧
    Function.Injective (JordanTKK.negLM (R := R) (J := J) (S := D.str)) ∧
    Function.Injective (JordanTKK.zeroLM (R := R) (J := J) (S := D.str)) ∧
    Function.Injective (JordanTKK.posLM (R := R) (J := J) (S := D.str)) ∧
    JordanTKK.zeroLieHom D ⁅T₁, T₂⁆ = ⁅JordanTKK.zeroLieHom D T₁, JordanTKK.zeroLieHom D T₂⁆ := by
  let _ : LieRing (JordanTKK J D.str) := JordanTKK.lieRing D
  let _ : LieAlgebra R (JordanTKK J D.str) := JordanTKK.lieAlgebra D
  exact ⟨JordanTKK.zeroLieHom_injective D, JordanTKK.negLM_injective,
    JordanTKK.zeroLM_injective, JordanTKK.posLM_injective,
    (JordanTKK.zeroLieHom D).map_lie (x := T₁) (y := T₂)⟩

theorem m4_real_jordanTKK_sl2_finrank_3 :
    let _ : Invertible (2 : ℝ) := invertibleOfNonzero two_ne_zero
    let _ : LieRing (JordanTKK ℝ realJordanTKKDatum.str) :=
      JordanTKK.lieRing realJordanTKKDatum
    let _ : LieAlgebra ℝ (JordanTKK ℝ realJordanTKKDatum.str) :=
      JordanTKK.lieAlgebra realJordanTKKDatum
    let e : JordanTKK ℝ realJordanTKKDatum.str :=
      JordanTKK.negLM (R := ℝ) (S := realJordanTKKDatum.str) (1 : ℝ)
    let f : JordanTKK ℝ realJordanTKKDatum.str :=
      JordanTKK.posLM (R := ℝ) (S := realJordanTKKDatum.str) (1 : ℝ)
    let h : JordanTKK ℝ realJordanTKKDatum.str :=
      JordanTKK.zeroLM (R := ℝ) (J := ℝ) (S := realJordanTKKDatum.str)
        ⟨LinearMap.id, Submodule.mem_top⟩
    Module.finrank ℝ (JordanTKK ℝ realJordanTKKDatum.str) = 3 ∧
    ⁅e, f⁆ = h ∧
    ⁅h, e⁆ = e ∧
    ⁅h, f⁆ = -f ∧
    ⁅e, f⁆ ≠ 0 := by
  let _ : Invertible (2 : ℝ) := invertibleOfNonzero two_ne_zero
  let _ : LieRing (JordanTKK ℝ realJordanTKKDatum.str) := JordanTKK.lieRing realJordanTKKDatum
  let _ : LieAlgebra ℝ (JordanTKK ℝ realJordanTKKDatum.str) :=
    JordanTKK.lieAlgebra realJordanTKKDatum
  have hstr : Module.finrank ℝ realJordanTKKDatum.str = 1 := by
    change Module.finrank ℝ (⊤ : Submodule ℝ (Module.End ℝ ℝ)) = 1
    rw [finrank_top]
    simp
  have hdim : Module.finrank ℝ (JordanTKK ℝ realJordanTKKDatum.str) = 3 := by
    rw [JordanTKK.finrank_jordanTKK_two_mul (F := ℝ) (J := ℝ) (S := realJordanTKKDatum.str),
      Module.finrank_self ℝ, hstr]
  have hef : ⁅JordanTKK.negLM (R := ℝ) (S := realJordanTKKDatum.str) (1 : ℝ),
      JordanTKK.posLM (R := ℝ) (S := realJordanTKKDatum.str) (1 : ℝ)⁆ =
      JordanTKK.zeroLM (R := ℝ) (J := ℝ) (S := realJordanTKKDatum.str)
        ⟨LinearMap.id, Submodule.mem_top⟩ := by
    rw [JordanTKK.neg_bracket_pos realJordanTKKDatum (1 : ℝ) (1 : ℝ)]
    congr 1
    apply Subtype.ext
    apply LinearMap.ext
    intro z
    simp [JordanTKK.tripleD, JordanTKK.triple]
  have hhe : ⁅JordanTKK.zeroLM (R := ℝ) (J := ℝ) (S := realJordanTKKDatum.str)
        ⟨LinearMap.id, Submodule.mem_top⟩,
      JordanTKK.negLM (R := ℝ) (S := realJordanTKKDatum.str) (1 : ℝ)⁆ =
      JordanTKK.negLM (R := ℝ) (S := realJordanTKKDatum.str) (1 : ℝ) := by
    rw [JordanTKK.zero_bracket_neg realJordanTKKDatum ⟨LinearMap.id, Submodule.mem_top⟩ (1 : ℝ)]
    simp
  have hhf : ⁅JordanTKK.zeroLM (R := ℝ) (J := ℝ) (S := realJordanTKKDatum.str)
        ⟨LinearMap.id, Submodule.mem_top⟩,
      JordanTKK.posLM (R := ℝ) (S := realJordanTKKDatum.str) (1 : ℝ)⁆ =
      -JordanTKK.posLM (R := ℝ) (S := realJordanTKKDatum.str) (1 : ℝ) := by
    rw [JordanTKK.zero_bracket_pos realJordanTKKDatum ⟨LinearMap.id, Submodule.mem_top⟩ (1 : ℝ)]
    change JordanTKK.posLM (R := ℝ) (S := realJordanTKKDatum.str)
        (-(LinearMap.id (1 : ℝ))) = _
    rw [LinearMap.id_apply, map_neg]
  have hne : ⁅JordanTKK.negLM (R := ℝ) (S := realJordanTKKDatum.str) (1 : ℝ),
      JordanTKK.posLM (R := ℝ) (S := realJordanTKKDatum.str) (1 : ℝ)⁆ ≠ 0 := by
    rw [hef]
    intro h0
    have h1 := congrArg (fun X : JordanTKK ℝ realJordanTKKDatum.str => X.zero.1 1) h0
    simp at h1
  exact ⟨hdim, hef, hhe, hhf, hne⟩

/-! Feature 8 Tier 2: Boundary, Zero, Antisymmetry, Grade Corners & Nilpotency -/

theorem m4_jordanTKK_bracket_zero_left_right {R J : Type*} [CommRing R] [Invertible (2 : R)]
    [NonUnitalNonAssocCommRing J] [Module R J] [SMulCommClass R J J] [IsScalarTower R J J]
    [IsCommJordan J] (D : JordanTKKDatum R J) (X : JordanTKK J D.str) (x : J) :
    let _ : LieRing (JordanTKK J D.str) := JordanTKK.lieRing D
    ⁅(0 : JordanTKK J D.str), X⁆ = 0 ∧
    ⁅X, (0 : JordanTKK J D.str)⁆ = 0 ∧
    JordanTKK.tripleD R (0 : J) x = 0 ∧
    JordanTKK.tripleD R x (0 : J) = 0 := by
  let _ : LieRing (JordanTKK J D.str) := JordanTKK.lieRing D
  exact ⟨zero_lie X, lie_zero X, JordanTKK.tripleD_zero_left (R := R) x,
    JordanTKK.tripleD_zero_right (R := R) x⟩

theorem m4_jordanTKK_bracket_self_zero {R J : Type*} [CommRing R] [Invertible (2 : R)]
    [NonUnitalNonAssocCommRing J] [Module R J] [SMulCommClass R J J] [IsScalarTower R J J]
    [IsCommJordan J] (D : JordanTKKDatum R J) (X : JordanTKK J D.str) :
    let _ : LieRing (JordanTKK J D.str) := JordanTKK.lieRing D
    ⁅X, X⁆ = 0 ∧ JordanTKK.bracketBilin D X X = 0 := by
  let _ : LieRing (JordanTKK J D.str) := JordanTKK.lieRing D
  exact ⟨lie_self X, JordanTKK.bracketBilin_self D X⟩

theorem m4_jordanTKK_bracket_antisymm_mixed {R J : Type*} [CommRing R] [Invertible (2 : R)]
    [NonUnitalNonAssocCommRing J] [Module R J] [SMulCommClass R J J] [IsScalarTower R J J]
    [IsCommJordan J] (D : JordanTKKDatum R J) (x₁ x₂ y₁ y₂ : J) (T₁ T₂ : D.str) :
    let _ : LieRing (JordanTKK J D.str) := JordanTKK.lieRing D
    let X : JordanTKK J D.str :=
      JordanTKK.negLM (R := R) x₁ + JordanTKK.zeroLM (R := R) T₁ + JordanTKK.posLM (R := R) y₁
    let Y : JordanTKK J D.str :=
      JordanTKK.negLM (R := R) x₂ + JordanTKK.zeroLM (R := R) T₂ + JordanTKK.posLM (R := R) y₂
    ⁅Y, X⁆ = -⁅X, Y⁆ := by
  let _ : LieRing (JordanTKK J D.str) := JordanTKK.lieRing D
  exact (lie_skew _ _).symm

theorem m4_jordanTKK_grade_corners_abelian {R J : Type*} [CommRing R] [Invertible (2 : R)]
    [NonUnitalNonAssocCommRing J] [Module R J] [SMulCommClass R J J] [IsScalarTower R J J]
    [IsCommJordan J] (D : JordanTKKDatum R J) (x₁ x₂ y₁ y₂ : J) :
    let _ : LieRing (JordanTKK J D.str) := JordanTKK.lieRing D
    ⁅JordanTKK.negLM (R := R) (S := D.str) x₁,
      JordanTKK.negLM (R := R) (S := D.str) x₂⁆ = 0 ∧
    ⁅JordanTKK.posLM (R := R) (S := D.str) y₁,
      JordanTKK.posLM (R := R) (S := D.str) y₂⁆ = 0 := by
  let _ : LieRing (JordanTKK J D.str) := JordanTKK.lieRing D
  exact ⟨JordanTKK.neg_bracket_neg D x₁ x₂, JordanTKK.pos_bracket_pos D y₁ y₂⟩

theorem m4_jordanTKK_cross_grade_and_nilpotency {R J : Type*} [CommRing R] [Invertible (2 : R)]
    [NonUnitalNonAssocCommRing J] [Module R J] [SMulCommClass R J J] [IsScalarTower R J J]
    [IsCommJordan J] (D : JordanTKKDatum R J) (a b c d : J) (T : D.str) :
    let _ : LieRing (JordanTKK J D.str) := JordanTKK.lieRing D
    ⁅JordanTKK.zeroLM (R := R) (J := J) T, JordanTKK.negLM (R := R) (S := D.str) a⁆ =
      JordanTKK.negLM (R := R) (S := D.str) (T.1 a) ∧
    ⁅JordanTKK.posLM (R := R) (S := D.str) b, JordanTKK.zeroLM (R := R) (J := J) T⁆ =
      JordanTKK.posLM (R := R) (S := D.str) (D.adj T.1 b) ∧
    ⁅JordanTKK.posLM (R := R) (S := D.str) a,
      ⁅JordanTKK.posLM (R := R) (S := D.str) b,
        ⁅JordanTKK.posLM (R := R) (S := D.str) c,
          JordanTKK.negLM (R := R) (S := D.str) d⁆⁆⁆ = 0 ∧
    ⁅JordanTKK.negLM (R := R) (S := D.str) a,
      ⁅JordanTKK.negLM (R := R) (S := D.str) b,
        ⁅JordanTKK.negLM (R := R) (S := D.str) c,
          JordanTKK.posLM (R := R) (S := D.str) d⁆⁆⁆ = 0 := by
  let _ : LieRing (JordanTKK J D.str) := JordanTKK.lieRing D
  refine ⟨JordanTKK.zero_bracket_neg D T a, JordanTKK.pos_bracket_zero D b T, ?_, ?_⟩
  · rw [JordanTKK.pos_bracket_neg, JordanTKK.pos_bracket_zero, JordanTKK.pos_bracket_pos]
  · rw [JordanTKK.neg_bracket_pos, JordanTKK.neg_bracket_zero, JordanTKK.neg_bracket_neg]

end Feature8GenericJordanTKK

/-! ## [M4-CONTRACT] Feature 9: 133D `𝔈₇(7)` on `H3Zorn ℝ` (Tier 1 & Tier 2) -/

section Feature9H3ZornTKK

open InfoGeometry.Canonical.H3ZornTKKLieAlgebra
open InfoGeometry.Canonical.H3ZornBasis

theorem m4_h3zorn_tkk_finrank_133_and_lie_instances :
    Module.finrank ℝ H3ZornTKKLie = 133 ∧
    2 * Module.finrank ℝ (H3Zorn ℝ) + Module.finrank ℝ h3zornTKKDatum.str = 133 ∧
    (∀ X : H3ZornTKKLie, X = negInj X.neg + zeroInj X.zero + posInj X.pos) := by
  refine ⟨finrank_H3ZornTKKLie, ?_, fun X => JordanTKK.eq_neg_add_zero_add_pos (R := ℝ) X⟩
  rw [← JordanTKK.finrank_jordanTKK_two_mul (F := ℝ) (J := H3Zorn ℝ) (S := h3zornTKKDatum.str)]
  exact finrank_H3ZornTKKLie

theorem m4_h3zorn_tkk_to_native_faithful_and_intertwines (X Y : H3ZornTKKLie) :
    Function.Injective h3zornTKKToNative ∧
    h3zornTKKToNative (-X) = tkkNeg (h3zornTKKToNative X) ∧
    h3zornTKKToNative ⁅X, Y⁆ = tkkBracket (h3zornTKKToNative X) (h3zornTKKToNative Y) ∧
    JordanTKK.tripleD ℝ X.neg Y.pos = jordanTripleD X.neg Y.pos :=
  ⟨h3zornTKKToNative_injective, h3zornTKKToNative_neg X, h3zornTKKToNative_bracket X Y,
    tripleD_eq_native X.neg Y.pos⟩

theorem m4_h3zorn_cubic_stabilizer_78d_embeds_in_133d
    (T₁ T₂ : h3zornCubicStabilizer) (U : structureOperatorLieSubalgebra) :
    h3zornCubicStabilizer ≤ structureOperatorLieSubalgebra ∧
    Function.Injective h3zornCubicStabilizerToTKK ∧
    Function.Injective InfoGeometry.Canonical.H3ZornTKKLieAlgebra.zeroLieHom ∧
    h3zornCubicStabilizerToTKK ⁅T₁, T₂⁆ =
      ⁅h3zornCubicStabilizerToTKK T₁, h3zornCubicStabilizerToTKK T₂⁆ ∧
    (InfoGeometry.Canonical.H3ZornTKKLieAlgebra.zeroLieHom U).zero.1 = U.1 :=
  ⟨h3zornCubicStabilizer_le_structureOperatorLieSubalgebra,
    h3zornCubicStabilizerToTKK_injective,
    InfoGeometry.Canonical.H3ZornTKKLieAlgebra.zeroLieHom_injective,
    h3zornCubicStabilizerToTKK.map_lie (x := T₁) (y := T₂), rfl⟩

theorem m4_h3zorn_tkk_grade_op_eigenvalues
    (x y : H3Zorn ℝ) (T : h3zornTKKDatum.str) :
    (h3zornStrOne : Module.End ℝ (H3Zorn ℝ)) = LinearMap.id ∧
    ⁅h3zornTKKGradeOp, negInj x⁆ = negInj x ∧
    ⁅h3zornTKKGradeOp, zeroInj T⁆ = 0 ∧
    ⁅h3zornTKKGradeOp, posInj y⁆ = -posInj y :=
  ⟨h3zornStrOne_coe_eq_id, h3zornTKKGradeOp_bracket_neg x,
    h3zornTKKGradeOp_bracket_zero T, h3zornTKKGradeOp_bracket_pos y⟩

theorem m4_h3zorn_tkk_nontrivial_mixed_brackets :
    ⁅negInj (1 : H3Zorn ℝ), posInj (1 : H3Zorn ℝ)⁆ = h3zornTKKGradeOp ∧
    ⁅negInj (1 : H3Zorn ℝ), posInj (1 : H3Zorn ℝ)⁆ ≠ 0 ∧
    ⁅h3zornTKKGradeOp, negInj (1 : H3Zorn ℝ)⁆ ≠ 0 ∧
    ⁅negInj (h3ZornBasis 10), posInj (h3ZornBasis 3)⁆ ≠ 0 :=
  ⟨negInj_one_bracket_posInj_one_eq_gradeOp, negInj_one_bracket_posInj_one_ne_zero,
    h3zornTKKGradeOp_bracket_neg_one_ne_zero, negInj_bracket_posInj_traceDual_ne_zero 10⟩

/-! Feature 9 Tier 2: Eigenvalue Signs, Antisymmetry, 3-Step Nilpotency & `str` vs `str₀` -/

theorem m4_h3zorn_tkk_grade_op_reversed_eigenvalues
    (x y : H3Zorn ℝ) (T : h3zornTKKDatum.str) :
    ⁅negInj x, h3zornTKKGradeOp⁆ = -negInj x ∧
    ⁅zeroInj T, h3zornTKKGradeOp⁆ = 0 ∧
    ⁅posInj y, h3zornTKKGradeOp⁆ = posInj y := by
  refine ⟨?_, ?_, ?_⟩
  · rw [← lie_skew, h3zornTKKGradeOp_bracket_neg]
  · rw [← lie_skew, h3zornTKKGradeOp_bracket_zero, neg_zero]
  · rw [← lie_skew, h3zornTKKGradeOp_bracket_pos, neg_neg]

theorem m4_h3zorn_tkk_antisymm_and_self_zero_mixed (X Y : H3ZornTKKLie) :
    ⁅X, X⁆ = 0 ∧
    ⁅Y, X⁆ = -⁅X, Y⁆ ∧
    ⁅(0 : H3ZornTKKLie), X⁆ = 0 ∧
    ⁅X, (0 : H3ZornTKKLie)⁆ = 0 :=
  ⟨lie_self X, (lie_skew Y X).symm, zero_lie X, lie_zero X⟩

theorem m4_h3zorn_tkk_three_step_nilpotency
    (a b c d : H3Zorn ℝ) (T : h3zornTKKDatum.str) :
    ⁅posInj a, ⁅posInj b, ⁅posInj c, negInj d⁆⁆⁆ = 0 ∧
    ⁅posInj a, ⁅posInj b, zeroInj T⁆⁆ = 0 ∧
    ⁅negInj a, ⁅negInj b, ⁅negInj c, posInj d⁆⁆⁆ = 0 ∧
    ⁅negInj a, ⁅negInj b, zeroInj T⁆⁆ = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [posInj_bracket_negInj, posInj_bracket_zeroInj, posInj_bracket_posInj]
  · rw [posInj_bracket_zeroInj, posInj_bracket_posInj]
  · rw [negInj_bracket_posInj, negInj_bracket_zeroInj, negInj_bracket_negInj]
  · rw [negInj_bracket_zeroInj, negInj_bracket_negInj]

theorem m4_h3zorn_tkk_grade_op_not_in_e6_range :
    (h3zornStrOne : Module.End ℝ (H3Zorn ℝ)) ∉ h3zornCubicStabilizer ∧
    h3zornTKKGradeOp ∉ Set.range h3zornCubicStabilizerToTKK := by
  refine ⟨h3zornStrOne_not_mem_cubicStabilizer, ?_⟩
  rintro ⟨T, hT⟩
  have h0 : (h3zornCubicStabilizerToTKK T).zero.1 = h3zornTKKGradeOp.zero.1 :=
    congrArg (fun X : H3ZornTKKLie => X.zero.1) hT
  change T.1 = h3zornStrOne.1 at h0
  exact h3zornStrOne_not_mem_cubicStabilizer (h0 ▸ T.2)

theorem m4_h3zorn_tkk_abelian_grade_corners_and_jacobi
    (x₁ x₂ y₁ y₂ : H3Zorn ℝ) (X Y Z : H3ZornTKKLie) :
    ⁅negInj x₁, negInj x₂⁆ = 0 ∧
    ⁅posInj y₁, posInj y₂⁆ = 0 ∧
    ⁅X, ⁅Y, Z⁆⁆ = ⁅⁅X, Y⁆, Z⁆ + ⁅Y, ⁅X, Z⁆⁆ :=
  ⟨negInj_bracket_negInj x₁ x₂, posInj_bracket_posInj y₁ y₂, leibniz_lie X Y Z⟩

end Feature9H3ZornTKK

/-! ## [M4-CONTRACT] Feature 10: 133D `𝔈₇(-25)` on `H3Octonion ℝ` (Tier 1 & Tier 2) -/

section Feature10H3OctonionTKK

theorem m4_h3octonion_tkk_finrank_133_and_lie_instances :
    Module.finrank ℝ H3OctonionTKKLie = 133 ∧
    2 * Module.finrank ℝ (H3Octonion ℝ) + Module.finrank ℝ h3OctonionTKKDatum.str = 133 ∧
    (∀ X : H3OctonionTKKLie,
      X = H3OctonionTKKLie.negInj X.neg + H3OctonionTKKLie.zeroInj X.zero +
        H3OctonionTKKLie.posInj X.pos) := by
  refine ⟨finrank_H3OctonionTKKLie, ?_, H3OctonionTKKLie.eq_neg_add_zero_add_pos⟩
  rw [← JordanTKK.finrank_jordanTKK_two_mul (F := ℝ) (J := H3Octonion ℝ)
    (S := h3OctonionTKKDatum.str)]
  exact finrank_H3OctonionTKKLie

theorem m4_h3octonion_cubic_stabilizer_embeds_and_center_bot
    (T₁ T₂ : h3OctonionCubicStabilizer) :
    h3OctonionCubicStabilizer ≤ h3OctonionStructureLieSubalgebra ∧
    Function.Injective h3OctonionCubicStabilizerToTKK ∧
    Function.Injective H3OctonionTKKLie.zeroLieHom ∧
    h3OctonionCubicStabilizerToTKK ⁅T₁, T₂⁆ =
      ⁅h3OctonionCubicStabilizerToTKK T₁, h3OctonionCubicStabilizerToTKK T₂⁆ ∧
    LieAlgebra.center ℝ H3OctonionTKKLie = ⊥ :=
  ⟨h3OctonionCubicStabilizer_le_structureLieSubalgebra,
    h3OctonionCubicStabilizerToTKK_injective, H3OctonionTKKLie.zeroLieHom_injective,
    h3OctonionCubicStabilizerToTKK.map_lie (x := T₁) (y := T₂), center_H3OctonionTKKLie_eq_bot⟩

theorem m4_h3octonion_cartan_involution_and_signature_neg_25 (X Y : H3OctonionTKKLie) :
    h3OctonionCartanInvolution (h3OctonionCartanInvolution X) = X ∧
    h3OctonionCartanInvolution ⁅X, Y⁆ =
      ⁅h3OctonionCartanInvolution X, h3OctonionCartanInvolution Y⁆ ∧
    Module.finrank ℝ h3OctonionCartanCompactSubalgebra = 79 ∧
    Module.finrank ℝ h3OctonionCartanNoncompactSubmodule = 54 ∧
    (Module.finrank ℝ h3OctonionCartanNoncompactSubmodule : ℤ) -
      Module.finrank ℝ h3OctonionCartanCompactSubalgebra = -25 :=
  ⟨h3OctonionCartanInvolution_involutive X,
    h3OctonionCartanInvolution.map_lie (x := X) (y := Y),
    finrank_h3OctonionCartanCompactSubalgebra, finrank_h3OctonionCartanNoncompactSubmodule,
    h3OctonionCartan_signature_eq_neg_25⟩

theorem m4_h3octonion_tkk_is_killing_and_semisimple :
    LieAlgebra.IsKilling ℝ H3OctonionTKKLie ∧
    LieAlgebra.IsSemisimple ℝ H3OctonionTKKLie ∧
    LieAlgebra.HasTrivialRadical ℝ H3OctonionTKKLie ∧
    (killingForm ℝ H3OctonionTKKLie).Nondegenerate :=
  ⟨instIsKillingH3OctonionTKKLie, inferInstance, inferInstance,
    LieAlgebra.IsKilling.killingForm_nondegenerate ℝ H3OctonionTKKLie⟩

theorem m4_h3octonion_tkk_jacobi_mixed_and_nontrivial
    (x y : H3Octonion ℝ) (T : h3OctonionTKKDatum.str) :
    ⁅H3OctonionTKKLie.negInj x, ⁅H3OctonionTKKLie.zeroInj T, H3OctonionTKKLie.posInj y⁆⁆ =
      ⁅⁅H3OctonionTKKLie.negInj x, H3OctonionTKKLie.zeroInj T⁆, H3OctonionTKKLie.posInj y⁆ +
        ⁅H3OctonionTKKLie.zeroInj T, ⁅H3OctonionTKKLie.negInj x, H3OctonionTKKLie.posInj y⁆⁆ ∧
    ⁅H3OctonionTKKLie.negInj (1 : H3Octonion ℝ),
      H3OctonionTKKLie.posInj (1 : H3Octonion ℝ)⁆ = h3OctonionTKKGradeOp ∧
    ⁅H3OctonionTKKLie.negInj (1 : H3Octonion ℝ),
      H3OctonionTKKLie.posInj (1 : H3Octonion ℝ)⁆ ≠ 0 ∧
    ⁅H3OctonionTKKLie.negInj (1 : H3Octonion ℝ) - H3OctonionTKKLie.posInj (1 : H3Octonion ℝ),
      ⁅H3OctonionTKKLie.negInj (1 : H3Octonion ℝ) - H3OctonionTKKLie.posInj (1 : H3Octonion ℝ),
        h3OctonionTKKGradeOp⁆⁆ = (-2 : ℝ) • h3OctonionTKKGradeOp ∧
    ⁅H3OctonionTKKLie.negInj (1 : H3Octonion ℝ) + H3OctonionTKKLie.posInj (1 : H3Octonion ℝ),
      ⁅H3OctonionTKKLie.negInj (1 : H3Octonion ℝ) + H3OctonionTKKLie.posInj (1 : H3Octonion ℝ),
        h3OctonionTKKGradeOp⁆⁆ = (2 : ℝ) • h3OctonionTKKGradeOp :=
  ⟨leibniz_lie _ _ _, negInj_one_bracket_posInj_one_eq_gradeOp,
    negInj_one_bracket_posInj_one_ne_zero, ad_sq_compact_witness_gradeOp,
    ad_sq_noncompact_witness_gradeOp⟩

/-! Feature 10 Tier 2: Grading, Corners, Cartan Complement, Killing Signs & Non-Abelian Witness -/

theorem m4_h3octonion_tkk_grade_op_and_str0_separation
    (x y : H3Octonion ℝ) (T : h3OctonionTKKDatum.str) :
    ⁅h3OctonionTKKGradeOp, H3OctonionTKKLie.negInj x⁆ = H3OctonionTKKLie.negInj x ∧
    ⁅h3OctonionTKKGradeOp, H3OctonionTKKLie.zeroInj T⁆ = 0 ∧
    ⁅h3OctonionTKKGradeOp, H3OctonionTKKLie.posInj y⁆ = -H3OctonionTKKLie.posInj y ∧
    (h3OctonionStrOne : Module.End ℝ (H3Octonion ℝ)) ∉ h3OctonionCubicStabilizer ∧
    h3OctonionTKKGradeOp ∉ Set.range h3OctonionCubicStabilizerToTKK := by
  refine ⟨h3OctonionTKKGradeOp_bracket_neg x, h3OctonionTKKGradeOp_bracket_zero T,
    h3OctonionTKKGradeOp_bracket_pos y, h3OctonionStrOne_not_mem_cubicStabilizer, ?_⟩
  rintro ⟨T₀, hT₀⟩
  have h0 : (h3OctonionCubicStabilizerToTKK T₀).zero.1 = h3OctonionTKKGradeOp.zero.1 :=
    congrArg (fun X : H3OctonionTKKLie => X.zero.1) hT₀
  change T₀.1 = h3OctonionStrOne.1 at h0
  exact h3OctonionStrOne_not_mem_cubicStabilizer (h0 ▸ T₀.2)

theorem m4_h3octonion_tkk_self_zero_antisymm_and_zero (X Y : H3OctonionTKKLie) :
    ⁅X, X⁆ = 0 ∧
    ⁅Y, X⁆ = -⁅X, Y⁆ ∧
    ⁅(0 : H3OctonionTKKLie), X⁆ = 0 ∧
    ⁅X, (0 : H3OctonionTKKLie)⁆ = 0 :=
  ⟨lie_self X, (lie_skew Y X).symm, zero_lie X, lie_zero X⟩

theorem m4_h3octonion_tkk_grade_corners_abelian_and_nilpotent
    (x₁ x₂ y₁ y₂ a b c d : H3Octonion ℝ) :
    ⁅H3OctonionTKKLie.negInj x₁, H3OctonionTKKLie.negInj x₂⁆ = 0 ∧
    ⁅H3OctonionTKKLie.posInj y₁, H3OctonionTKKLie.posInj y₂⁆ = 0 ∧
    ⁅H3OctonionTKKLie.posInj a,
      ⁅H3OctonionTKKLie.posInj b,
        ⁅H3OctonionTKKLie.posInj c, H3OctonionTKKLie.negInj d⁆⁆⁆ = 0 := by
  refine ⟨H3OctonionTKKLie.negInj_bracket_negInj x₁ x₂,
    H3OctonionTKKLie.posInj_bracket_posInj y₁ y₂, ?_⟩
  rw [H3OctonionTKKLie.posInj_bracket_negInj, H3OctonionTKKLie.posInj_bracket_zeroInj,
    H3OctonionTKKLie.posInj_bracket_posInj]

theorem m4_h3octonion_cartan_decomp_and_killing_signs
    {Xk Yk : H3OctonionTKKLie} (hXk : Xk ∈ h3OctonionCartanCompactSubalgebra)
    (hYk : Yk ∈ h3OctonionCartanNoncompactSubmodule) :
    IsCompl h3OctonionCartanCompactSubalgebra.toSubmodule
      h3OctonionCartanNoncompactSubmodule ∧
    killingForm ℝ H3OctonionTKKLie Xk Xk ≤ 0 ∧
    0 ≤ killingForm ℝ H3OctonionTKKLie Yk Yk ∧
    killingForm ℝ H3OctonionTKKLie Xk Yk = 0 ∧
    killingForm ℝ H3OctonionTKKLie
      (H3OctonionTKKLie.negInj (1 : H3Octonion ℝ) - H3OctonionTKKLie.posInj (1 : H3Octonion ℝ))
      (H3OctonionTKKLie.negInj (1 : H3Octonion ℝ) - H3OctonionTKKLie.posInj (1 : H3Octonion ℝ)) <
      0 ∧
    0 < killingForm ℝ H3OctonionTKKLie
      (H3OctonionTKKLie.negInj (1 : H3Octonion ℝ) + H3OctonionTKKLie.posInj (1 : H3Octonion ℝ))
      (H3OctonionTKKLie.negInj (1 : H3Octonion ℝ) + H3OctonionTKKLie.posInj (1 : H3Octonion ℝ)) :=
  ⟨h3OctonionCartan_decomposition_isCompl, killingForm_cartanCompact_nonpos hXk,
    killingForm_cartanNoncompact_nonneg hYk, killingForm_cartanCompact_noncompact_ortho hXk hYk,
    killingForm_compact_witness_neg, killingForm_noncompact_witness_pos⟩

theorem m4_h3octonion_tkk_nonabelian_and_cartan_parity
    {X₁ X₂ Y₁ Y₂ : H3OctonionTKKLie}
    (hX₁ : X₁ ∈ h3OctonionCartanCompactSubalgebra)
    (hX₂ : X₂ ∈ h3OctonionCartanCompactSubalgebra)
    (hY₁ : Y₁ ∈ h3OctonionCartanNoncompactSubmodule)
    (hY₂ : Y₂ ∈ h3OctonionCartanNoncompactSubmodule) :
    ¬ IsLieAbelian H3OctonionTKKLie ∧
    ⁅X₁, X₂⁆ ∈ h3OctonionCartanCompactSubalgebra ∧
    ⁅X₁, Y₁⁆ ∈ h3OctonionCartanNoncompactSubmodule ∧
    ⁅Y₁, Y₂⁆ ∈ h3OctonionCartanCompactSubalgebra := by
  refine ⟨?_, h3OctonionCartanCompactSubalgebra.lie_mem hX₁ hX₂,
    h3OctonionCartanCompact_bracket_noncompact hX₁ hY₁,
    h3OctonionCartanNoncompact_bracket_noncompact hY₁ hY₂⟩
  intro hab
  exact negInj_one_bracket_posInj_one_ne_zero
    (hab.trivial (H3OctonionTKKLie.negInj 1) (H3OctonionTKKLie.posInj 1))

end Feature10H3OctonionTKK

/-! ## [M4-CONTRACT] Feature 11: `𝔈₇(7)` Root System & Simplicity (Tier 1 & Tier 2) -/

section Feature11H3ZornE7RootSystemAndSimplicity

open InfoGeometry.Canonical.H3ZornTKKLieAlgebra
open InfoGeometry.Exceptional.CFSGPort.Chevalley

theorem m4_h3zorn_e7_cartan_7d_and_triangularizable :
    Module.finrank ℝ h3zornE7Cartan = 7 ∧
    h3zornE7Cartan.IsCartanSubalgebra ∧
    LieModule.IsTriangularizable ℝ h3zornE7Cartan H3ZornTKKLie ∧
    h3zornE7Cartan.toSubmodule =
      h3zornCartan.toSubmodule.map h3zornCubicStabilizerToTKK.toLinearMap ⊔
        Submodule.span ℝ {h3zornTKKGradeOp} :=
  ⟨finrank_h3zornE7Cartan, h3zornE7Cartan_isCartanSubalgebra,
    h3zornE7Cartan_isTriangularizable, h3zornE7Cartan_eq_sup⟩

theorem m4_h3zorn_e7_126_roots_and_chevalley_basis_133 :
    Fintype.card h3zornE7Cartan.root = 126 ∧
    h3zornE7Cartan.root.card = 126 ∧
    Function.Bijective (fun r : Fin 126 =>
      (⟨e7RootCoord r, e7RootCoord_isRoot r⟩ : {v : Fin 7 → ℤ // IsRoot .E7 v})) ∧
    Function.Bijective e7MathlibRootEquiv ∧
    Function.Bijective e7RootSystemEquiv ∧
    Fintype.card (Fin 7 ⊕ Fin 126) = 133 ∧
    (∀ i : Fin 7, e7ChevalleyBasis (Sum.inl i) = e7SimpleH i) ∧
    (∀ r : Fin 126, e7ChevalleyBasis (Sum.inr r) = e7RootVec r) :=
  ⟨card_h3zornE7Cartan_root, h3zornE7Cartan_root_card, e7RootEquiv.bijective,
    e7MathlibRootEquiv.bijective, e7RootSystemEquiv.bijective, by simp,
    e7ChevalleyBasis_inl, e7ChevalleyBasis_inr⟩

theorem m4_h3zorn_e7_is_simple_and_killing :
    LieAlgebra.IsSimple ℝ H3ZornTKKLie ∧
    LieAlgebra.IsSemisimple ℝ H3ZornTKKLie ∧
    LieAlgebra.HasTrivialRadical ℝ H3ZornTKKLie ∧
    LieAlgebra.IsKilling ℝ H3ZornTKKLie ∧
    (killingForm ℝ H3ZornTKKLie).Nondegenerate :=
  ⟨h3zornTKKLie_isSimple, h3zornTKKLie_isSemisimple, h3zornTKKLie_hasTrivialRadical,
    h3zornTKKLie_isKilling, h3zornTKKLie_killingForm_nondegenerate⟩

theorem m4_h3zorn_e7_root_system_properties :
    h3zornE7RootSystem.IsRootSystem ∧
    h3zornE7RootSystem.IsCrystallographic ∧
    h3zornE7RootSystem.IsReduced ∧
    h3zornE7RootSystem.IsIrreducible :=
  ⟨h3zornE7RootSystem_isRootSystem, h3zornE7RootSystem_isCrystallographic,
    h3zornE7RootSystem_isReduced, h3zornE7RootSystem_isIrreducible⟩

theorem m4_h3zorn_e7_cartan_matrix_and_sl2_triples (i j : Fin 7) :
    h3zornE7RootSystemBase.cartanMatrix.reindex
      h3zornE7BaseSupportEquiv.symm h3zornE7BaseSupportEquiv.symm = CartanMatrix.E 7 ∧
    h3zornE7RootSystem.pairing (e7SimpleMathlibRoot i) (e7SimpleMathlibRoot j) =
      (CartanMatrix.E 7 i j : ℝ) ∧
    IsSl2Triple (e7SimpleH i) (e7SimpleE i) (e7SimpleF i) ∧
    (LieAlgebra.IsKilling.coroot (e7SimpleMathlibRoot i).1 : H3ZornTKKLie) = e7SimpleH i :=
  ⟨h3zornE7RootSystemBase_cartanMatrix_eq, h3zornE7RootSystem_pairing_simple i j,
    e7Simple_isSl2Triple i, e7Simple_coroot_eq i⟩

/-! Feature 11 Tier 2: Abelian Cartan, Root Negation/Nonzero, Ideal Dichotomy & Serre -/

theorem m4_h3zorn_e7_cartan_is_abelian (h₁ h₂ : h3zornE7Cartan) (i j : Fin 7) :
    IsLieAbelian h3zornE7Cartan ∧
    ⁅h₁, h₂⁆ = 0 ∧
    ⁅e7SimpleH i, e7SimpleH j⁆ = 0 :=
  ⟨inferInstance, (inferInstance : IsLieAbelian h3zornE7Cartan).trivial h₁ h₂, e7SimpleH_comm i j⟩

theorem m4_h3zorn_e7_roots_nonzero_and_neg_closed
    (α : h3zornE7Cartan.root) (r : Fin 126) :
    (α.1 : h3zornE7Cartan → ℝ) ≠ 0 ∧
    h3zornE7RootWeight r ≠ 0 ∧
    Function.Injective h3zornE7RootWeight ∧
    ∃ β : h3zornE7Cartan.root,
      h3zornE7RootSystem.root β = -h3zornE7RootSystem.root α := by
  refine ⟨LieSubalgebra.isNonZero_coe_root α, h3zornE7RootWeight_ne_zero r,
    h3zornE7RootWeight_injective, ?_⟩
  exact ⟨h3zornE7RootSystem.reflectionPerm α α,
    by simp⟩

theorem m4_h3zorn_e7_no_abelian_ideal_and_dichotomy
    (I : LieIdeal ℝ H3ZornTKKLie) [IsLieAbelian I] (J : LieIdeal ℝ H3ZornTKKLie) :
    I = ⊥ ∧
    LieAlgebra.center ℝ H3ZornTKKLie = ⊥ ∧
    (J = ⊥ ∨ J = ⊤) ∧
    (h3zornE7Cartan.toSubmodule ≤ ⊤) :=
  ⟨h3zornTKKLie_no_abelian_ideal I, center_h3zornTKKLie_eq_bot,
    h3zornTKKLie_isSimple.eq_bot_or_eq_top J, le_top⟩

theorem m4_h3zorn_e7_simple_chevalley_ef_and_serre {i j : Fin 7} (hij : i ≠ j) :
    ⁅e7SimpleE i, e7SimpleF i⁆ = e7SimpleH i ∧
    ⁅e7SimpleE i, e7SimpleF j⁆ = 0 ∧
    ⁅e7SimpleH i, e7SimpleE j⁆ = ((Tag.cartan .E7 i j : ℤ) : ℝ) • e7SimpleE j ∧
    ⁅e7SimpleH i, e7SimpleF j⁆ = (-(Tag.cartan .E7 i j : ℤ) : ℝ) • e7SimpleF j ∧
    (Nat.iterate (fun x => ⁅e7SimpleE i, x⁆)
      (1 - Tag.cartan .E7 i j).toNat) (e7SimpleE j) = 0 ∧
    (Nat.iterate (fun x => ⁅e7SimpleF i, x⁆)
      (1 - Tag.cartan .E7 i j).toNat) (e7SimpleF j) = 0 :=
  ⟨e7Simple_bracket_EF_same i, e7Simple_bracket_EF_ne hij,
    e7Simple_bracket_HE i j, e7Simple_bracket_HF i j,
    e7Simple_serre_E hij, e7Simple_serre_F hij⟩

theorem m4_h3zorn_e7_root_vecs_nonzero_and_nonabelian (r : Fin 126) :
    e7RootVec r ≠ 0 ∧
    ⁅e7SimpleH 0, e7SimpleE 0⁆ = (2 : ℝ) • e7SimpleE 0 ∧
    ⁅e7SimpleH 0, e7SimpleE 0⁆ ≠ 0 ∧
    ¬ IsLieAbelian H3ZornTKKLie := by
  have h2 : ⁅e7SimpleH 0, e7SimpleE 0⁆ = (2 : ℝ) • e7SimpleE 0 := by
    rw [e7Simple_bracket_HE]
    have hc : Tag.cartan .E7 (0 : Fin 7) (0 : Fin 7) = 2 := by decide
    rw [hc]
    norm_num
  refine ⟨e7RootVec_ne_zero r, h2, h3zornE7_noncomm_witness, ?_⟩
  intro hab
  exact h3zornE7_noncomm_witness (hab.trivial (e7SimpleH 0) (e7SimpleE 0))

end Feature11H3ZornE7RootSystemAndSimplicity

end M4TKKAndE7

section M5FreudenthalGroup

open InfoGeometry.Algebra.H3ZornFreudenthal

/-! ## [M5-CONTRACT] Feature 12: Levi `Str₀(H₃(𝕆_s)) = E₆(6)` Action on 56D (Tier 1 & Tier 2) -/

theorem freudenthal_charge_finrank_56 :
    Module.finrank ℝ Charge = 56 ∧
    Module.finrank ℝ (ℝ × ℝ × H3Zorn ℝ × H3Zorn ℝ) = 56 := by
  refine ⟨finrank_charge, ?_⟩
  rw [← LinearEquiv.finrank_eq chargeCoordinateLinearEquiv, finrank_charge]

theorem levi_charge_equiv_hom_and_injective
    (g₁ g₂ : h3zornReducedStructureGroup) :
    leviChargeEquiv 1 = 1 ∧
    leviChargeEquiv (g₁ * g₂) = leviChargeEquiv g₁ * leviChargeEquiv g₂ ∧
    Function.Injective leviChargeEquiv ∧
    Function.Injective leviChargeGL ∧
    Function.Injective chevalleyE6ChargeEquiv :=
  ⟨leviChargeEquiv.map_one, leviChargeEquiv.map_mul g₁ g₂,
    leviChargeEquiv_injective, leviChargeGL_injective, chevalleyE6ChargeEquiv_injective⟩

theorem chevalleyE6_subgroup_le_levi_and_invariance
    (g : h3zornReducedStructureGroup) (Q : Charge) (Q₁ Q₂ : Charge) :
    chevalleyE6ChargeSubgroup ≤ leviChargeSubgroup ∧
    Function.Injective chevalleyE6ChargeGL ∧
    symplecticForm (leviChargeEquiv g Q₁) (leviChargeEquiv g Q₂) = symplecticForm Q₁ Q₂ ∧
    quarticInvariant (leviChargeEquiv g Q) = quarticInvariant Q :=
  ⟨chevalleyE6ChargeSubgroup_le_leviChargeSubgroup, chevalleyE6ChargeGL_injective,
    leviChargeEquiv_symplecticForm g Q₁ Q₂, leviChargeEquiv_quarticInvariant g Q⟩

theorem levi_and_chevalleyE6_invariant_action_laws
    (g : h3zornReducedStructureGroup) (h : h3zornChevalleyE6)
    (Q : Charge) (Q₁ Q₂ : Charge) :
    leviInvariantAction.act g Q = leviChargeEquiv g Q ∧
    chevalleyE6InvariantAction.act h Q = chevalleyE6ChargeEquiv h Q ∧
    symplecticForm (leviInvariantAction.act g Q₁) (leviInvariantAction.act g Q₂) =
      symplecticForm Q₁ Q₂ ∧
    quarticInvariant (leviInvariantAction.act g Q) = quarticInvariant Q ∧
    symplecticForm (chevalleyE6InvariantAction.act h Q₁) (chevalleyE6InvariantAction.act h Q₂) =
      symplecticForm Q₁ Q₂ ∧
    quarticInvariant (chevalleyE6InvariantAction.act h Q) = quarticInvariant Q :=
  ⟨rfl, rfl, leviInvariantAction.preserves_symplecticForm g Q₁ Q₂,
    leviInvariantAction.preserves_quarticInvariant g Q,
    chevalleyE6InvariantAction.preserves_symplecticForm h Q₁ Q₂,
    chevalleyE6InvariantAction.preserves_quarticInvariant h Q⟩

theorem levi_adjointQuad_and_traceInverseAdjoint_intertwining
    (g : h3zornReducedStructureGroup) (x y : H3Zorn ℝ) :
    adjointQuad (g.1 x) = h3zornTraceInverseAdjoint g.1 (adjointQuad x) ∧
    adjointQuad (h3zornTraceInverseAdjoint g.1 y) = g.1 (adjointQuad y) ∧
    normCubic (h3zornTraceInverseAdjoint g.1 y) = normCubic y ∧
    traceBilin (g.1 x) (h3zornTraceInverseAdjoint g.1 y) = traceBilin x y :=
  ⟨adjointQuad_reducedStructure g x, adjointQuad_traceInverseAdjoint_reducedStructure g y,
    normCubic_traceInverseAdjoint_reducedStructure g y,
    traceBilin_reducedStructure_pair g.1 x y⟩

theorem levi_concrete_torus_weyl_and_U_witnesses :
    (let t2 : ℝˣ := Units.mk0 (2 : ℝ) (by norm_num)
     let gT : h3zornChevalleyE6 :=
       ⟨h3zornTorusElt 0 t2, h3zornTorusElt_mem_chevalleyE6 0 t2⟩
     let Q₀ : Charge := electricCharge 1 (h3ZornBasis 0)
     chevalleyE6ChargeEquiv gT Q₀ ≠ Q₀ ∧ chevalleyE6ChargeEquiv gT ≠ 1) ∧
    (let w0 : h3zornChevalleyE6 :=
       ⟨h3zornWeylElt 0 1, h3zornWeylElt_mem_chevalleyE6 0 1⟩
     let w2 : h3zornChevalleyE6 :=
       ⟨h3zornWeylElt 2 1, h3zornWeylElt_mem_chevalleyE6 2 1⟩
     chevalleyE6ChargeEquiv w0 * chevalleyE6ChargeEquiv w2 ≠
       chevalleyE6ChargeEquiv w2 * chevalleyE6ChargeEquiv w0 ∧
     chevalleyE6ChargeGL w0 * chevalleyE6ChargeGL w2 ≠
       chevalleyE6ChargeGL w2 * chevalleyE6ChargeGL w0) ∧
    (let d : H3Zorn ℝ := diagCartan 2 (1 / 2 : ℝ) 1
     have hd_norm : normCubic d = 1 := by
       have h := diagCartan_quadratic_U_peirce_laplace_mellin_and_semigroup
         (R := ℝ) 2 (1 / 2 : ℝ) 1 1 1 1 1
       rw [h.2.1]
       norm_num
     have hd_ne : normCubic d ≠ 0 := by
       rw [hd_norm]
       norm_num
     let uDiag : h3zornReducedStructureGroup :=
       ⟨h3zornULinearEquiv d hd_ne,
         h3zornULinearEquiv_mem_reducedStructureGroup d hd_ne (Or.inl hd_norm)⟩
     (leviChargeEquiv uDiag (electricCharge 1 1)).x = diagCartan 4 (1 / 4 : ℝ) 1 ∧
       leviChargeEquiv uDiag (electricCharge 1 1) ≠ electricCharge 1 1 ∧
       quarticInvariant (leviChargeEquiv uDiag (electricCharge 1 1)) = -4) :=
  ⟨chevalleyE6_torus_nontrivial_witness, chevalleyE6_weyl_noncomm_witness,
    levi_diagCartan_U_nontrivial_witness⟩

theorem levi_zero_and_scalar_charge_fixed
    (g g₁ g₂ : h3zornReducedStructureGroup) (α β : ℝ) (y : H3Zorn ℝ) :
    leviChargeEquiv g 0 = 0 ∧
    leviChargeEquiv g (scalarCharge α β) = scalarCharge α β ∧
    h3zornTraceInverseAdjoint (1 : H3Zorn ℝ ≃ₗ[ℝ] H3Zorn ℝ) y = y ∧
    h3zornTraceInverseAdjoint (g₁.1 * g₂.1) y =
      h3zornTraceInverseAdjoint g₁.1 (h3zornTraceInverseAdjoint g₂.1 y) := by
  refine ⟨(leviChargeEquiv g).map_zero, ?_, h3zornTraceInverseAdjoint_one y,
    h3zornTraceInverseAdjoint_mul g₁.1 g₂.1 y⟩
  apply FreudenthalCharge.ext
  · rfl
  · rfl
  · exact (g.1).map_zero
  · exact (h3zornTraceAdjointEquiv g.1).symm.map_zero

theorem levi_preserves_regular_and_boundary_strata
    (g : h3zornReducedStructureGroup) (Q : Charge) :
    Regular (leviChargeEquiv g (electricCharge 1 (1 : H3Zorn ℝ))) ∧
    Boundary (leviChargeEquiv g (electricCharge 0 (diagCartan 1 0 0))) ∧
    (Regular (leviInvariantAction.act g Q) ↔ Regular Q) ∧
    (Boundary (leviInvariantAction.act g Q) ↔ Boundary Q) := by
  have hreg0 : Regular (electricCharge 1 (1 : H3Zorn ℝ)) := by
    change quarticInvariant (electricCharge 1 1) ≠ 0
    rw [unit_electric_quartic]
    norm_num
  have hbd0 : Boundary (electricCharge 0 (diagCartan 1 0 0)) := by
    refine ⟨?_, ?_⟩
    · change quarticInvariant (electricCharge 0 (diagCartan 1 0 0)) = 0
      rw [quarticInvariant_electricCharge]
      norm_num
    · intro hz
      have hx := congrArg FreudenthalCharge.x hz
      have hα₁ := congrArg H3Zorn.α₁ hx
      change (1 : ℝ) = 0 at hα₁
      norm_num at hα₁
  exact ⟨(leviInvariantAction.regular_iff g (electricCharge 1 1)).2 hreg0,
    (leviInvariantAction.boundary_iff g (electricCharge 0 (diagCartan 1 0 0))).2 hbd0,
    leviInvariantAction.regular_iff g Q, leviInvariantAction.boundary_iff g Q⟩

theorem chevalleyE6_boundary_fixed_and_nonabelian
    (h : h3zornChevalleyE6) (α β : ℝ) :
    chevalleyE6ChargeEquiv h 0 = 0 ∧
    chevalleyE6ChargeEquiv h (scalarCharge α β) = scalarCharge α β ∧
    (let w0 : h3zornChevalleyE6 :=
       ⟨h3zornWeylElt 0 1, h3zornWeylElt_mem_chevalleyE6 0 1⟩
     let w2 : h3zornChevalleyE6 :=
       ⟨h3zornWeylElt 2 1, h3zornWeylElt_mem_chevalleyE6 2 1⟩
     chevalleyE6ChargeGL w0 * chevalleyE6ChargeGL w2 ≠
       chevalleyE6ChargeGL w2 * chevalleyE6ChargeGL w0) := by
  refine ⟨(chevalleyE6ChargeEquiv h).map_zero, ?_, chevalleyE6_weyl_noncomm_witness.2⟩
  exact (levi_zero_and_scalar_charge_fixed h.1 h.1 h.1 α β 0).2.1

/-! ## [M5-CONTRACT] Feature 13: Concrete `E₇(7)` Group Elements `t₊(A)`, `t₋(B)`, `J` (Tier 1 & Tier 2) -/

theorem freudenthal_upper_trans_group_and_invariance
    (A B : H3Zorn ℝ) (Q Q₁ Q₂ : Charge) :
    freudenthalUpperTrans (0 : H3Zorn ℝ) = 1 ∧
    freudenthalUpperTrans A * freudenthalUpperTrans B = freudenthalUpperTrans (A + B) ∧
    (freudenthalUpperTrans A)⁻¹ = freudenthalUpperTrans (-A) ∧
    symplecticForm (freudenthalUpperTrans A Q₁) (freudenthalUpperTrans A Q₂) =
      symplecticForm Q₁ Q₂ ∧
    quarticInvariant (freudenthalUpperTrans A Q) = quarticInvariant Q :=
  ⟨freudenthalUpperTrans_zero, freudenthalUpperTrans_mul A B, freudenthalUpperTrans_inv A,
    freudenthalUpperTrans_preserves_symplecticForm A Q₁ Q₂,
    freudenthalUpperTrans_preserves_quarticInvariant A Q⟩

theorem freudenthal_lower_trans_group_conj_and_invariance
    (B B₁ B₂ : H3Zorn ℝ) (Q Q₁ Q₂ : Charge) :
    freudenthalLowerTrans B =
      freudenthalInversion * freudenthalUpperTrans (-B) * freudenthalInversion⁻¹ ∧
    freudenthalLowerTrans (0 : H3Zorn ℝ) = 1 ∧
    freudenthalLowerTrans B₁ * freudenthalLowerTrans B₂ = freudenthalLowerTrans (B₁ + B₂) ∧
    (freudenthalLowerTrans B)⁻¹ = freudenthalLowerTrans (-B) ∧
    symplecticForm (freudenthalLowerTrans B Q₁) (freudenthalLowerTrans B Q₂) =
      symplecticForm Q₁ Q₂ ∧
    quarticInvariant (freudenthalLowerTrans B Q) = quarticInvariant Q :=
  ⟨freudenthalLowerTrans_eq_conj_upperTrans B, freudenthalLowerTrans_zero,
    freudenthalLowerTrans_mul B₁ B₂, freudenthalLowerTrans_inv B,
    freudenthalLowerTrans_preserves_symplecticForm B Q₁ Q₂,
    freudenthalLowerTrans_preserves_quarticInvariant B Q⟩

theorem freudenthal_inversion_order4_and_invariance
    (Q Q₁ Q₂ : Charge) :
    glInversion * glInversion = -1 ∧
    glInversion ^ 2 = -1 ∧
    glInversion ^ 4 = 1 ∧
    glInversion⁻¹ = -glInversion ∧
    symplecticForm (freudenthalInversion Q₁) (freudenthalInversion Q₂) = symplecticForm Q₁ Q₂ ∧
    quarticInvariant (freudenthalInversion Q) = quarticInvariant Q := by
  refine ⟨glInversion_sq, freudenthalInversion_sq_eq_neg_one, ?_, glInversion_inv,
    freudenthalInversion_preserves_symplecticForm Q₁ Q₂,
    freudenthalInversion_preserves_quarticInvariant Q⟩
  rw [show (4 : ℕ) = 2 * 2 by rfl, pow_mul, freudenthalInversion_sq_eq_neg_one, neg_one_sq]

theorem freudenthal_e7_group_subgroup_and_action
    (g : h3zornReducedStructureGroup) (A B : H3Zorn ℝ)
    (h : freudenthalE7Group) (Q Q₁ Q₂ : Charge) :
    freudenthalE7Group ≤ freudenthalInvariantSubgroup ∧
    leviChargeGL g ∈ freudenthalE7Group ∧
    glUpperTrans (Multiplicative.ofAdd A) ∈ freudenthalE7Group ∧
    glLowerTrans (Multiplicative.ofAdd B) ∈ freudenthalE7Group ∧
    glInversion ∈ freudenthalE7Group ∧
    symplecticForm (freudenthalE7GroupAction.act h Q₁) (freudenthalE7GroupAction.act h Q₂) =
      symplecticForm Q₁ Q₂ ∧
    quarticInvariant (freudenthalE7GroupAction.act h Q) = quarticInvariant Q :=
  ⟨freudenthalE7Group_le_invariantSubgroup, leviChargeGL_mem_freudenthalE7Group g,
    glUpperTrans_mem_freudenthalE7Group A, glLowerTrans_mem_freudenthalE7Group B,
    glInversion_mem_freudenthalE7Group,
    freudenthalE7GroupAction.preserves_symplecticForm h Q₁ Q₂,
    freudenthalE7GroupAction.preserves_quarticInvariant h Q⟩

theorem freudenthal_levi_and_inversion_conjugation_laws
    (g : h3zornReducedStructureGroup) (A B : H3Zorn ℝ) :
    leviChargeEquiv g * freudenthalUpperTrans A * (leviChargeEquiv g)⁻¹ =
      freudenthalUpperTrans (g.1 A) ∧
    freudenthalInversion * leviChargeEquiv g * freudenthalInversion⁻¹ =
      leviChargeEquiv (h3zornTraceInverseAdjointReduced g) ∧
    leviChargeEquiv g * freudenthalLowerTrans B * (leviChargeEquiv g)⁻¹ =
      freudenthalLowerTrans (h3zornTraceInverseAdjoint g.1 B) :=
  ⟨levi_conj_upperTrans g A, inversion_conj_levi g, levi_conj_lowerTrans g B⟩

theorem freudenthal_sign_sanity_unit_and_mixed_charge (α : ℝ) :
    quarticInvariant (freudenthalUpperTrans (1 : H3Zorn ℝ) ⟨α, 1, 0, 0⟩) = α ^ 2 ∧
    (let Qmix : Charge := ⟨1, 1, (1 : H3Zorn ℝ), (1 : H3Zorn ℝ)⟩
     quarticInvariant Qmix = -16 ∧
     quarticInvariant (freudenthalUpperTrans (1 : H3Zorn ℝ) Qmix) = -16 ∧
     quarticInvariant (freudenthalLowerTrans (1 : H3Zorn ℝ) Qmix) = -16 ∧
     quarticInvariant (freudenthalInversion Qmix) = -16) := by
  refine ⟨freudenthalUpperTrans_one_sign_sanity α, ?_⟩
  intro Qmix
  have htr1 : traceBilin (1 : H3Zorn ℝ) 1 = 3 := by
    rw [traceBilin_one]
    change (1 : ℝ) + 1 + 1 = 3
    norm_num
  have hmix : quarticInvariant Qmix = -16 := by
    dsimp [Qmix]
    rw [quarticInvariant_expanded]
    simp only [normCubic_one, adjointQuad_one, htr1]
    norm_num
  refine ⟨hmix, ?_, ?_, ?_⟩
  · rw [freudenthalUpperTrans_preserves_quarticInvariant, hmix]
  · rw [freudenthalLowerTrans_preserves_quarticInvariant, hmix]
  · rw [freudenthalInversion_preserves_quarticInvariant, hmix]

theorem freudenthal_e7_generators_nontrivial :
    freudenthalInversion ≠ 1 ∧
    freudenthalUpperTrans (1 : H3Zorn ℝ) (scalarCharge 0 1) = ⟨-1, 1, 1, -1⟩ ∧
    freudenthalUpperTrans (1 : H3Zorn ℝ) ≠ 1 ∧
    freudenthalLowerTrans (1 : H3Zorn ℝ) (scalarCharge 1 0) = ⟨1, -1, -1, 1⟩ ∧
    freudenthalLowerTrans (1 : H3Zorn ℝ) ≠ 1 :=
  ⟨freudenthalInversion_ne_one, freudenthalUpperTrans_one_ne_one.1,
    freudenthalUpperTrans_one_ne_one.2, freudenthalLowerTrans_one_ne_one.1,
    freudenthalLowerTrans_one_ne_one.2⟩

theorem freudenthal_e7_noncommutativity_corners :
    freudenthalUpperTrans (1 : H3Zorn ℝ) * freudenthalLowerTrans (1 : H3Zorn ℝ) ≠
      freudenthalLowerTrans (1 : H3Zorn ℝ) * freudenthalUpperTrans (1 : H3Zorn ℝ) ∧
    glUpperTrans (Multiplicative.ofAdd (1 : H3Zorn ℝ)) *
        glLowerTrans (Multiplicative.ofAdd (1 : H3Zorn ℝ)) *
        (glUpperTrans (Multiplicative.ofAdd (1 : H3Zorn ℝ)))⁻¹ *
        (glLowerTrans (Multiplicative.ofAdd (1 : H3Zorn ℝ)))⁻¹ ≠ 1 ∧
    freudenthalInversion * freudenthalUpperTrans (1 : H3Zorn ℝ) ≠
      freudenthalUpperTrans (1 : H3Zorn ℝ) * freudenthalInversion :=
  ⟨freudenthal_upper_lower_noncommute, glUpperTrans_glLowerTrans_commutator_ne_one,
    freudenthal_inversion_upper_noncommute⟩

theorem freudenthal_e7_zero_and_strata_preservation
    (g : freudenthalE7Group) (Q : Charge) :
    g.1 • (0 : Charge) = 0 ∧
    Regular (freudenthalE7GroupAction.act g (electricCharge 1 (1 : H3Zorn ℝ))) ∧
    Boundary (freudenthalE7GroupAction.act g (electricCharge 0 (diagCartan 1 0 0))) ∧
    (Regular (freudenthalE7GroupAction.act g Q) ↔ Regular Q) ∧
    (Boundary (freudenthalE7GroupAction.act g Q) ↔ Boundary Q) := by
  have hreg0 : Regular (electricCharge 1 (1 : H3Zorn ℝ)) := by
    change quarticInvariant (electricCharge 1 1) ≠ 0
    rw [unit_electric_quartic]
    norm_num
  have hbd0 : Boundary (electricCharge 0 (diagCartan 1 0 0)) := by
    refine ⟨?_, ?_⟩
    · change quarticInvariant (electricCharge 0 (diagCartan 1 0 0)) = 0
      rw [quarticInvariant_electricCharge]
      norm_num
    · intro hz
      have hx := congrArg FreudenthalCharge.x hz
      have hα₁ := congrArg H3Zorn.α₁ hx
      change (1 : ℝ) = 0 at hα₁
      norm_num at hα₁
  exact ⟨smul_zero g.1,
    (freudenthalE7GroupAction.regular_iff g (electricCharge 1 1)).2 hreg0,
    (freudenthalE7GroupAction.boundary_iff g (electricCharge 0 (diagCartan 1 0 0))).2 hbd0,
    freudenthalE7GroupAction.regular_iff g Q, freudenthalE7GroupAction.boundary_iff g Q⟩

theorem freudenthal_trans_degenerate_zero_element_laws
    (A B : H3Zorn ℝ) (α β : ℝ) (Q : Charge) :
    glUpperTrans (1 : Multiplicative (H3Zorn ℝ)) = 1 ∧
    glLowerTrans (1 : Multiplicative (H3Zorn ℝ)) = 1 ∧
    freudenthalUpperTrans (0 : H3Zorn ℝ) Q = Q ∧
    freudenthalLowerTrans (0 : H3Zorn ℝ) Q = Q ∧
    freudenthalUpperTrans A (scalarCharge α 0) = scalarCharge α 0 ∧
    freudenthalLowerTrans B (scalarCharge 0 β) = scalarCharge 0 β := by
  refine ⟨glUpperTrans.map_one, glLowerTrans.map_one, ?_, ?_, ?_, ?_⟩
  · rw [freudenthalUpperTrans_zero]
    rfl
  · rw [freudenthalLowerTrans_zero]
    rfl
  · apply FreudenthalCharge.ext
    · rw [freudenthalUpperTrans_alpha]
      simp only [scalarCharge, traceBilin_zero_right, zero_mul, sub_zero, add_zero]
    · rfl
    · rw [freudenthalUpperTrans_x]
      simp only [scalarCharge, zero_smul, add_zero]
    · rw [freudenthalUpperTrans_y]
      simp only [scalarCharge, H3Zorn.crossProduct, add_zero, adjointQuad_zero,
        sub_self, zero_smul]
  · apply FreudenthalCharge.ext
    · rw [freudenthalLowerTrans_alpha]
    · rw [freudenthalLowerTrans_beta]
      simp only [scalarCharge, traceBilin_zero_right, zero_mul, sub_zero, add_zero]
    · rw [freudenthalLowerTrans_x]
      simp only [scalarCharge, H3Zorn.crossProduct, add_zero, adjointQuad_zero,
        sub_self, zero_smul]
    · rw [freudenthalLowerTrans_y]
      simp only [scalarCharge, zero_smul, add_zero]

end M5FreudenthalGroup

end InfoGeometry.Tests.E7TKKFreudenthal
