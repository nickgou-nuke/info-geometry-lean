/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.Lie.OfAssociative
import InfoGeometry.Physics.NuclearTwoModeCARFiveGrade
import InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel
import InfoGeometry.Physics.NuclearFiveGradeGeneratorRepresentation
import InfoGeometry.Physics.NuclearFiveGradeBdGSolovievClosure
import InfoGeometry.Physics.NuclearFiveGradeSameCarrierClosure
import InfoGeometry.Physics.NuclearFiveGradeDegreeZeroSL2
import InfoGeometry.Physics.NuclearFiveGradeCircularPhase
import InfoGeometry.Nuclear.NuclearFiveGradedOperatorReexpression
import InfoGeometry.Physics.NuclearSolovievFiveGradedCommutantBridge
import InfoGeometry.SuperGrassmannian.NuclearQuasiphononSuperGrassmannian
import InfoGeometry.Nuclear.NuclearQuasiphononJordanPairBridge
import InfoGeometry.Nuclear.NuclearQuasiphononKreinSUSY
import InfoGeometry.Synthesis.SuperGrassmannianFiveGradedColorSupersymmetrySynthesis
import InfoGeometry.Synthesis.Cl55SuperGrassmannianKKTSynthesis
import InfoGeometry.Synthesis.Z2Z2KoszulOperadicHomologyShirokovSynthesis
import InfoGeometry.Algebra.CuntzMatrixUnitFiveGradingBridge
import InfoGeometry.Algebra.FiveGradedIwasawaNilpotency

/-!
# Seam A: Nuclear Two-Mode CAR–BdG–Soloviev ↔ Super-Grassmannian & Color-SUSY 5-Graded Intertwiner

This module constructs the explicit grade-preserving intertwiners and boundary-preserving bridges
across Seam A between:

1. **Concrete Nuclear Two-Mode CAR–BdG–Soloviev 5-Grading** (`ℝ` and `ℂ` layers):
   - `NuclearTwoModeCARFiveGrade` (`Op = Module.End ℂ Fock4`, `gradeCartan`, `HasGrade k`),
   - `NuclearTwoModeFiveGradeLieModel` (`M4R = Matrix (Fin 4) (Fin 4) ℝ`, `gradingOperator`, `sp(4, ℝ)`),
   - `NuclearFiveGradeGeneratorRepresentation` (`Generator`, `m4rToOp`, `carLieSubalgebra`, `carToFiveGraded`,
     `carToFiveGradedEquiv`, `pairSL2Subalgebra`),
   - `Nuclear.FiveGraded` (`Phi : FiveGradedCarrier punitCubicJordanDatum →ₗ[ℝ] M4R`, `m4rGrade_directSum`,
     and the mixed-Jacobi obstruction vs associative CAR Jacobi),
   - `NuclearFiveGradeDegreeZeroSL2`, `NuclearFiveGradeCircularPhase`, `NuclearFiveGradeBdGSolovievClosure`,
     and `NuclearFiveGradeSameCarrierClosure`.

2. **`(ι₀ ⊕ ι₁)` Super-Grassmannian, `(2|1)` OSp Jordan Pair, Krein SUSY & `Cuntz3` Iwasawa Layer**:
   - Explicit `ℝ`-algebra isomorphism `ospToSuperBlock3AlgEquiv : M₃ ≃ₐ[ℝ] Matrix (Fin 2 ⊕ Fin 1) (Fin 2 ⊕ Fin 1) ℝ`
     identifying `SuperconformalOSpJordanPair.supertrace`, `embed21Matrix`, and `Q_±` with
     `NuclearQuasiphononSuperGrassmannian.superTrace`, `volumeMode`, and `chiralMode`.
   - Exact Lie-algebra isomorphism `pairSL2ToOSpEvenEquiv : pairSL2Subalgebra ≃ₗ⁅ℝ⁆ ospEvenLieSubalgebra`
     intertwining `{pairCreation, gradingOperator, pairAnnihilation}` with `{E_gen ℝ, H_gen ℝ, F_gen ℝ}`
     at grades `{-2, 0, +2}` and landing in `evenCorner` / `bdgBlock` / `qpnmMatrix`.
   - Tripotent `IsFiveGraded` Iwasawa structure on `M₄(ℝ)`, `carLieSubalgebra`, and `M₃(ℝ)`, plus the
     grade-preserving Lie embedding `cuntzMatUnitToM3 : matrixUnitLieSubalgebra →ₗ⁅ℝ⁆ M₃`.

3. **$\mathbb{Z}_2 \times \mathbb{Z}_2$ Super-Grassmannian / Günaydin–Gürsey Color-SUSY & `Cl(5,5)` KKT Layer**:
   - Equivalence `superBlock23MatrixEquiv K : SuperBlock23 K ≃ Matrix (Fin 2 ⊕ Fin 3) (Fin 2 ⊕ Fin 3) K`
     matching `superTrace ↔ superTrace23` and `blockBerezinian ↔ fullBerezinian23`.
   - Explicit grade projections `fiveGradeToZ2 : ℤ → Bool` and `gunaydinGurseyZ2Z2Projection : ℤ → Z2Z2ColorGrade`.
   - Explicit `ℝ`-linear grade-preserving intertwiner `car5ToOpZornEuler : carLieSubalgebra →ₗ[ℝ] OpZornMatrix ℝ`
     (and `car5ToGunaydinGursey`) intertwining `ad gradingOperator` with `opEulerFiveGrading` across all
     five grades `{-2, -1, 0, +1, +2}`, while keeping associative (`M₃`, `M₄`, `SuperBlock23`) and
     non-associative (`OpZornMatrix ℝ`, `ZornSplitOctonion ℝ`, `fiveGradedBracket`) carriers strictly distinct.
   - Integration of `Cl55SuperGrassmannianKKTSynthesis`, `Z2Z2KoszulOperadicHomologyShirokovSynthesis`,
     the `32 × 32` Soloviev `MatStage 5` no-go (`solovievFiveGradedRealization_isEmpty`), and the Seam A↔D
     nonzero RPA commutator defect (`pair_rpa_square_defect_is_grade_zero_cartan`).
-/

set_option autoImplicit false

namespace InfoGeometry.Synthesis.NuclearFiveGradeSuperGrassmannianIntertwiner

noncomputable section

open Matrix

private abbrev M4R := InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.M4R
private abbrev M₃ := InfoGeometry.Nuclear.NuclearQuasiphononJordanPairBridge.M₃
private abbrev M₂ := InfoGeometry.Nuclear.NuclearQuasiphononJordanPairBridge.M₂
private abbrev Op := InfoGeometry.Physics.NuclearTwoModeCARFiveGrade.Op
private abbrev Fock4 := InfoGeometry.Physics.NuclearTwoModeCARFiveGrade.Fock4
private abbrev OpZornR := InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.OpZornMatrix ℝ

local instance : LieRing M4R := LieRing.ofAssociativeRing
local instance : LieAlgebra ℝ M4R := LieAlgebra.ofAssociativeAlgebra
local instance : LieRing M₃ := LieRing.ofAssociativeRing
local instance : LieAlgebra ℝ M₃ := LieAlgebra.ofAssociativeAlgebra
local instance : LieRing Op := LieRing.ofAssociativeRing
local instance : LieAlgebra ℝ Op := LieAlgebra.ofAssociativeAlgebra

/-!
## Section 1: Closed Non-Commutativity & Non-Associativity Boundary Witnesses (T16)
-/

theorem m4r_noncommutative_witness :
    ∃ A B : Matrix (Fin 4) (Fin 4) ℝ, A * B ≠ B * A := by
  refine ⟨InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.pairCreation,
    InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.pairAnnihilation, ?_⟩
  intro h
  have hsub : InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.comm
      InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.pairCreation
      InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.pairAnnihilation = 0 := by
    unfold InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.comm
    rw [h, sub_self]
  rw [InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.pair_extreme_bracket] at hsub
  exact InfoGeometry.Physics.NuclearFiveGradeSameCarrierClosure.pair_rpa_square_defect_is_grade_zero_cartan.2 hsub

theorem m3_noncommutative_witness :
    ∃ A B : Matrix (Fin 3) (Fin 3) ℝ, A * B ≠ B * A :=
  ⟨InfoGeometry.Synthesis.Z2Z2KoszulOperadicHomologyShirokovSynthesis.koszulColorJ12,
   InfoGeometry.Synthesis.Z2Z2KoszulOperadicHomologyShirokovSynthesis.koszulColorK13,
   InfoGeometry.Synthesis.Z2Z2KoszulOperadicHomologyShirokovSynthesis.koszul_peirce_mat3_noncomm⟩

theorem m2_noncommutative_witness :
    ∃ A B : Matrix (Fin 2) (Fin 2) ℝ, A * B ≠ B * A := by
  refine ⟨!![0, 1; 0, 0], !![0, 0; 1, 0], ?_⟩
  intro h
  have h00 := congr_fun (congr_fun h 0) 0
  norm_num [Matrix.mul_apply, Fin.sum_univ_two] at h00

theorem op_fock4_noncommutative_witness :
    ∃ A B : Module.End ℂ Fock4, A * B ≠ B * A := by
  refine ⟨InfoGeometry.Physics.NuclearTwoModeCARFiveGrade.pairCreation,
    InfoGeometry.Physics.NuclearTwoModeCARFiveGrade.pairAnnihilation, ?_⟩
  intro h
  have hcomm : InfoGeometry.Physics.NuclearTwoModeCARFiveGrade.commutator
      InfoGeometry.Physics.NuclearTwoModeCARFiveGrade.pairCreation
      InfoGeometry.Physics.NuclearTwoModeCARFiveGrade.pairAnnihilation = 0 := by
    unfold InfoGeometry.Physics.NuclearTwoModeCARFiveGrade.commutator
    rw [h, sub_self]
  rw [InfoGeometry.Physics.NuclearTwoModeCARFiveGrade.pairCreation_pairAnnihilation_commutator] at hcomm
  have hv := LinearMap.congr_fun hcomm ![1, 0, 0, 0]
  have h0 := congr_fun hv 0
  norm_num [InfoGeometry.Physics.NuclearTwoModeCARFiveGrade.gradeCartan,
    InfoGeometry.Physics.NuclearTwoModeCARFiveGrade.numberOne,
    InfoGeometry.Physics.NuclearTwoModeCARFiveGrade.numberTwo,
    InfoGeometry.Physics.NuclearTwoModeCARFiveGrade.creationOne,
    InfoGeometry.Physics.NuclearTwoModeCARFiveGrade.annihilationOne,
    InfoGeometry.Physics.NuclearTwoModeCARFiveGrade.creationTwo,
    InfoGeometry.Physics.NuclearTwoModeCARFiveGrade.annihilationTwo,
    Module.End.mul_apply] at h0

theorem superblock21_noncommutative_witness :
    ∃ A B : Matrix (Fin 2 ⊕ Fin 1) (Fin 2 ⊕ Fin 1) ℝ, A * B ≠ B * A := by
  refine ⟨Matrix.fromBlocks (0 : Matrix (Fin 2) (Fin 2) ℝ) !![1; 0] 0 0,
    Matrix.fromBlocks (0 : Matrix (Fin 2) (Fin 2) ℝ) 0 !![1, 0] 0, ?_⟩
  intro h
  have h00 := congr_fun (congr_fun h (Sum.inl 0)) (Sum.inl 0)
  norm_num [Matrix.fromBlocks_multiply] at h00

theorem superblock23_noncommutative_witness :
    ∃ A B : Matrix (Fin 2 ⊕ Fin 3) (Fin 2 ⊕ Fin 3) ℝ, A * B ≠ B * A := by
  refine ⟨Matrix.fromBlocks !![(0 : ℝ), 1; 0, 0] 0 0 0,
    Matrix.fromBlocks !![(0 : ℝ), 0; 1, 0] 0 0 0, ?_⟩
  intro h
  have h00 := congr_fun (congr_fun h (Sum.inl 0)) (Sum.inl 0)
  norm_num [Matrix.fromBlocks_multiply, Matrix.mul_apply, Fin.sum_univ_two] at h00

theorem opZorn_nonassociative_witness :
    ∃ X Y Z : OpZornR, (X * Y) * Z ≠ X * (Y * Z) := by
  refine ⟨⟨0, ⟨1, 0, 0⟩, 0, 0⟩, ⟨0, ⟨0, 1, 0⟩, 0, 0⟩, ⟨0, ⟨0, 0, 1⟩, 0, 0⟩, ?_⟩
  intro h
  have hb := congrArg (fun M : OpZornR => M.b) h
  simp only [InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.OpZornMatrix.mul_b,
    InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.OpZornMatrix.mul_v,
    InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.OpZornMatrix.mul_w,
    InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.OpVec3.dot,
    InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.OpVec3.skewCross,
    InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.OpVec3.naiveCross,
    InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.OpVec3.leftScale,
    InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.OpVec3.rightScale] at hb
  norm_num at hb

/-!
## Section 2: Concrete Nuclear 5-Grading, `IsFiveGraded` Iwasawa & Left-Inverse `Phi`
-/

/-- The grading Cartan element `gradingOperator` in `M₄(ℝ)` is tripotent (`H³ = H`). -/
theorem gradingOperator_cube :
    InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.gradingOperator *
      InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.gradingOperator *
      InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.gradingOperator =
      InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.gradingOperator := by
  rw [InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.gradingOperator_eq_diagonal]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_four]

/-- The Cartan grading element inside the `10D` 2-mode CAR Lie subalgebra `carLieSubalgebra`. -/
def gradingCartanSub : InfoGeometry.Physics.NuclearFiveGradeGeneratorRepresentation.carLieSubalgebra :=
  ⟨InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.gradingOperator,
    InfoGeometry.Physics.NuclearFiveGradeGeneratorRepresentation.representM4R_mem_carLieSubalgebra .cartan⟩

/-- `gradingOperator` induces a genuine `FiveGradedIwasawa.IsFiveGraded` 5-grading on `M₄(ℝ)`. -/
instance instIsFiveGraded_gradingOperator_M4R :
    InfoGeometry.Algebra.FiveGradedIwasawa.IsFiveGraded
      InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.gradingOperator :=
  InfoGeometry.Algebra.CuntzMatrixUnitFiveGradingBridge.isFiveGraded_of_tripotent
    (A := M4R) gradingOperator_cube

/-- `gradingCartanSub` induces a genuine `FiveGradedIwasawa.IsFiveGraded` 5-grading on `carLieSubalgebra`. -/
instance instIsFiveGraded_gradingCartanSub :
    InfoGeometry.Algebra.FiveGradedIwasawa.IsFiveGraded gradingCartanSub :=
  InfoGeometry.Algebra.CuntzMatrixUnitFiveGradingBridge.isFiveGraded_of_lieSubalgebra_tripotent
    InfoGeometry.Physics.NuclearFiveGradeGeneratorRepresentation.carLieSubalgebra
    (InfoGeometry.Physics.NuclearFiveGradeGeneratorRepresentation.representM4R_mem_carLieSubalgebra .cartan)
    gradingOperator_cube

/-- `FiveGradedIwasawa.InGrade gradingOperator (k : ℝ) X` coincides with
`NuclearTwoModeFiveGradeLieModel.HasGrade k X`. -/
theorem inGrade_gradingOperator_iff_hasGrade (k : ℤ) (X : M4R) :
    InfoGeometry.Algebra.FiveGradedIwasawa.InGrade
        InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.gradingOperator (k : ℝ) X ↔
      InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.HasGrade k X :=
  Iff.rfl

private lemma pairCreation_eq_mat4 :
    InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.pairCreation =
      !![(0 : ℝ), 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0; 1, 0, 0, 0] := by
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.pairCreation,
      InfoGeometry.Canonical.SplitCliffordTwoModeCAR.a1Dag,
      InfoGeometry.Canonical.SplitCliffordTwoModeCAR.a2Dag,
      Matrix.mul_apply, Fin.sum_univ_four]

private lemma pairAnnihilation_eq_mat4 :
    InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.pairAnnihilation =
      !![(0 : ℝ), 0, 0, 1; 0, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0] := by
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.pairAnnihilation,
      InfoGeometry.Canonical.SplitCliffordTwoModeCAR.a1,
      InfoGeometry.Canonical.SplitCliffordTwoModeCAR.a2,
      Matrix.mul_apply, Fin.sum_univ_four]

private lemma degreeZeroRaise_eq_mat4 :
    InfoGeometry.Physics.NuclearFiveGradeDegreeZeroSL2.degreeZeroRaise =
      !![(0 : ℝ), 0, 0, 0; 0, 0, 0, 0; 0, 1, 0, 0; 0, 0, 0, 0] := by
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [InfoGeometry.Physics.NuclearFiveGradeDegreeZeroSL2.degreeZeroRaise,
      InfoGeometry.Canonical.SplitCliffordTwoModeCAR.a1Dag,
      InfoGeometry.Canonical.SplitCliffordTwoModeCAR.a2,
      Matrix.mul_apply, Fin.sum_univ_four]

private lemma degreeZeroLower_eq_mat4 :
    InfoGeometry.Physics.NuclearFiveGradeDegreeZeroSL2.degreeZeroLower =
      !![(0 : ℝ), 0, 0, 0; 0, 0, 1, 0; 0, 0, 0, 0; 0, 0, 0, 0] := by
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [InfoGeometry.Physics.NuclearFiveGradeDegreeZeroSL2.degreeZeroLower,
      InfoGeometry.Canonical.SplitCliffordTwoModeCAR.a2Dag,
      InfoGeometry.Canonical.SplitCliffordTwoModeCAR.a1,
      Matrix.mul_apply, Fin.sum_univ_four]

private lemma degreeZeroCartan_eq_mat4 :
    InfoGeometry.Physics.NuclearFiveGradeDegreeZeroSL2.degreeZeroCartan =
      !![(0 : ℝ), 0, 0, 0; 0, -1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 0] := by
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [InfoGeometry.Physics.NuclearFiveGradeDegreeZeroSL2.degreeZeroCartan,
      InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.number1,
      InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.number2,
      InfoGeometry.Canonical.SplitCliffordTwoModeCAR.a1,
      InfoGeometry.Canonical.SplitCliffordTwoModeCAR.a2,
      InfoGeometry.Canonical.SplitCliffordTwoModeCAR.a1Dag,
      InfoGeometry.Canonical.SplitCliffordTwoModeCAR.a2Dag,
      Matrix.mul_apply, Fin.sum_univ_four]

private theorem sympOfM4R_punit_apply (e0 f0 h0 : ℝ)
    (Z : InfoGeometry.Exceptional.Freudenthal.FreudenthalCharge PUnit.{1}) :
    ((InfoGeometry.Physics.NuclearFiveGradeGeneratorRepresentation.sympOfM4R
        InfoGeometry.Nuclear.FiveGraded.punitCubicJordanDatum e0 f0 h0 :
        Module.End ℝ (InfoGeometry.Exceptional.Freudenthal.FreudenthalCharge PUnit.{1})) Z) =
      ⟨h0 * Z.alpha + e0 * Z.beta, f0 * Z.alpha - h0 * Z.beta, PUnit.unit, PUnit.unit⟩ := by
  have neg_alpha : ∀ Q : InfoGeometry.Exceptional.Freudenthal.FreudenthalCharge PUnit.{1},
      (-Q).alpha = -Q.alpha := fun _ => rfl
  have neg_beta : ∀ Q : InfoGeometry.Exceptional.Freudenthal.FreudenthalCharge PUnit.{1},
      (-Q).beta = -Q.beta := fun _ => rfl
  dsimp [InfoGeometry.Physics.NuclearFiveGradeGeneratorRepresentation.sympOfM4R]
  simp only [InfoGeometry.Exceptional.Freudenthal.symplecticRankTwo_apply,
    InfoGeometry.Exceptional.Freudenthal.FreudenthalCharge.symplecticForm,
    InfoGeometry.Physics.NuclearFiveGradeGeneratorRepresentation.q1Charge,
    InfoGeometry.Physics.NuclearFiveGradeGeneratorRepresentation.q2Charge,
    InfoGeometry.Nuclear.FiveGraded.punitCubicJordanDatum,
    map_zero, LinearMap.zero_apply]
  apply InfoGeometry.Exceptional.Freudenthal.FreudenthalCharge.ext
  · simp [InfoGeometry.Exceptional.Freudenthal.alpha_add,
      InfoGeometry.Exceptional.Freudenthal.alpha_smul, neg_alpha]; ring
  · simp [InfoGeometry.Exceptional.Freudenthal.beta_add,
      InfoGeometry.Exceptional.Freudenthal.beta_smul, neg_beta]; ring
  · rfl
  · rfl

private theorem sympOfM4R_punit_eq_mkMid4 (e0 f0 h0 : ℝ) :
    InfoGeometry.Nuclear.FiveGraded.sympToM4R
        (InfoGeometry.Physics.NuclearFiveGradeGeneratorRepresentation.sympOfM4R
          InfoGeometry.Nuclear.FiveGraded.punitCubicJordanDatum e0 f0 h0) =
      e0 • InfoGeometry.Physics.NuclearFiveGradeDegreeZeroSL2.degreeZeroRaise +
        f0 • InfoGeometry.Physics.NuclearFiveGradeDegreeZeroSL2.degreeZeroLower +
        h0 • InfoGeometry.Physics.NuclearFiveGradeDegreeZeroSL2.degreeZeroCartan := by
  rw [degreeZeroRaise_eq_mat4, degreeZeroLower_eq_mat4, degreeZeroCartan_eq_mat4]
  dsimp [InfoGeometry.Nuclear.FiveGraded.sympToM4R]
  let S := (InfoGeometry.Physics.NuclearFiveGradeGeneratorRepresentation.sympOfM4R
    InfoGeometry.Nuclear.FiveGraded.punitCubicJordanDatum e0 f0 h0 :
    Module.End ℝ (InfoGeometry.Exceptional.Freudenthal.FreudenthalCharge PUnit.{1}))
  let eA : InfoGeometry.Exceptional.Freudenthal.FreudenthalCharge PUnit.{1} :=
    ⟨1, 0, PUnit.unit, PUnit.unit⟩
  let eB : InfoGeometry.Exceptional.Freudenthal.FreudenthalCharge PUnit.{1} :=
    ⟨0, 1, PUnit.unit, PUnit.unit⟩
  change !![(0 : ℝ), 0, 0, 0;
      0, (S eB).beta, (S eA).beta, 0;
      0, (S eB).alpha, (S eA).alpha, 0;
      0, 0, 0, 0] = _
  have hB : S eB = ⟨h0 * 0 + e0 * 1, f0 * 0 - h0 * 1, PUnit.unit, PUnit.unit⟩ :=
    sympOfM4R_punit_apply e0 f0 h0 eB
  have hA : S eA = ⟨h0 * 1 + e0 * 0, f0 * 1 - h0 * 0, PUnit.unit, PUnit.unit⟩ :=
    sympOfM4R_punit_apply e0 f0 h0 eA
  rw [hB, hA]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

private theorem carLieSubalgebra_entry_decomp
    {X : M4R}
    (hX : X ∈ InfoGeometry.Physics.NuclearFiveGradeGeneratorRepresentation.carLieSubalgebra) :
    X = X 3 0 • InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.pairCreation +
      X 2 0 • InfoGeometry.Canonical.SplitCliffordTwoModeCAR.a1Dag +
      X 1 0 • InfoGeometry.Canonical.SplitCliffordTwoModeCAR.a2Dag +
      X 3 3 • InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.gradingOperator +
      X 2 1 • InfoGeometry.Physics.NuclearFiveGradeDegreeZeroSL2.degreeZeroRaise +
      X 1 2 • InfoGeometry.Physics.NuclearFiveGradeDegreeZeroSL2.degreeZeroLower +
      X 2 2 • InfoGeometry.Physics.NuclearFiveGradeDegreeZeroSL2.degreeZeroCartan +
      X 0 2 • InfoGeometry.Canonical.SplitCliffordTwoModeCAR.a1 +
      X 0 1 • InfoGeometry.Canonical.SplitCliffordTwoModeCAR.a2 +
      X 0 3 • InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.pairAnnihilation := by
  change InfoGeometry.Physics.NuclearFiveGradeGeneratorRepresentation.symplecticOmega4 * X +
      Xᵀ * InfoGeometry.Physics.NuclearFiveGradeGeneratorRepresentation.symplecticOmega4 = 0 at hX
  have h00_raw := congr_fun (congr_fun hX 0) 3
  have h11_raw := congr_fun (congr_fun hX 1) 2
  have h31_raw := congr_fun (congr_fun hX 0) 1
  have h32_raw := congr_fun (congr_fun hX 0) 2
  have h13_raw := congr_fun (congr_fun hX 2) 3
  have h23_raw := congr_fun (congr_fun hX 1) 3
  simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.zero_apply,
    Fin.sum_univ_four] at h00_raw h11_raw h31_raw h32_raw h13_raw h23_raw
  norm_num [InfoGeometry.Physics.NuclearFiveGradeGeneratorRepresentation.symplecticOmega4]
    at h00_raw h11_raw h31_raw h32_raw h13_raw h23_raw
  have h00 : X 0 0 = -X 3 3 := by linarith
  have h11 : X 1 1 = -X 2 2 := by linarith
  have h31 : X 3 1 = X 2 0 := by linarith
  have h32 : X 3 2 = -X 1 0 := by linarith
  have h13 : X 1 3 = X 0 2 := by linarith
  have h23 : X 2 3 = -X 0 1 := by linarith
  rw [pairCreation_eq_mat4, pairAnnihilation_eq_mat4,
    InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.gradingOperator_eq_diagonal,
    degreeZeroRaise_eq_mat4, degreeZeroLower_eq_mat4, degreeZeroCartan_eq_mat4]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [InfoGeometry.Canonical.SplitCliffordTwoModeCAR.a1,
      InfoGeometry.Canonical.SplitCliffordTwoModeCAR.a2,
      InfoGeometry.Canonical.SplitCliffordTwoModeCAR.a1Dag,
      InfoGeometry.Canonical.SplitCliffordTwoModeCAR.a2Dag,
      h00, h11, h31, h32, h13, h23]

/-- `InfoGeometry.Nuclear.FiveGraded.Phi` is an exact left-inverse to `carToFiveGraded punitCubicJordanDatum`
into `M₄(ℝ)`, uniting the forward Lie isomorphism `carLieSubalgebra →ₗ⁅ℝ⁆ FiveGradedCarrier` with the
reverse grade-preserving linear section `FiveGradedCarrier →ₗ[ℝ] M4R`. -/
theorem Phi_comp_carToFiveGraded
    (X : InfoGeometry.Physics.NuclearFiveGradeGeneratorRepresentation.carLieSubalgebra) :
    InfoGeometry.Nuclear.FiveGraded.Phi
        (InfoGeometry.Physics.NuclearFiveGradeGeneratorRepresentation.carToFiveGraded
          InfoGeometry.Nuclear.FiveGraded.punitCubicJordanDatum X) = X.1 := by
  dsimp only [InfoGeometry.Nuclear.FiveGraded.Phi, LinearMap.coe_mk, AddHom.coe_mk,
    InfoGeometry.Physics.NuclearFiveGradeGeneratorRepresentation.carToFiveGraded,
    LieHom.coe_mk]
  have hsymp := sympOfM4R_punit_eq_mkMid4 (X.1 2 1) (X.1 1 2) (X.1 2 2)
  have neg_alpha : ∀ Q : InfoGeometry.Exceptional.Freudenthal.FreudenthalCharge PUnit.{1},
      (-Q).alpha = -Q.alpha := fun _ => rfl
  have neg_beta : ∀ Q : InfoGeometry.Exceptional.Freudenthal.FreudenthalCharge PUnit.{1},
      (-Q).beta = -Q.beta := fun _ => rfl
  have hm1_a : (((-X.1 0 1) •
      (InfoGeometry.Physics.NuclearFiveGradeGeneratorRepresentation.q1Charge :
        InfoGeometry.Exceptional.Freudenthal.FreudenthalCharge PUnit.{1}) +
      X.1 0 2 • InfoGeometry.Physics.NuclearFiveGradeGeneratorRepresentation.q2Charge).alpha) =
      -X.1 0 1 := by
    simp [InfoGeometry.Exceptional.Freudenthal.alpha_add,
      InfoGeometry.Exceptional.Freudenthal.alpha_smul, neg_alpha,
      InfoGeometry.Physics.NuclearFiveGradeGeneratorRepresentation.q1Charge,
      InfoGeometry.Physics.NuclearFiveGradeGeneratorRepresentation.q2Charge]
  have hm1_b : (((-X.1 0 1) •
      (InfoGeometry.Physics.NuclearFiveGradeGeneratorRepresentation.q1Charge :
        InfoGeometry.Exceptional.Freudenthal.FreudenthalCharge PUnit.{1}) +
      X.1 0 2 • InfoGeometry.Physics.NuclearFiveGradeGeneratorRepresentation.q2Charge).beta) =
      X.1 0 2 := by
    simp [InfoGeometry.Exceptional.Freudenthal.beta_add,
      InfoGeometry.Exceptional.Freudenthal.beta_smul, neg_beta,
      InfoGeometry.Physics.NuclearFiveGradeGeneratorRepresentation.q1Charge,
      InfoGeometry.Physics.NuclearFiveGradeGeneratorRepresentation.q2Charge]
  have hp1_a : ((X.1 2 0 •
      (InfoGeometry.Physics.NuclearFiveGradeGeneratorRepresentation.q1Charge :
        InfoGeometry.Exceptional.Freudenthal.FreudenthalCharge PUnit.{1}) +
      X.1 1 0 • InfoGeometry.Physics.NuclearFiveGradeGeneratorRepresentation.q2Charge).alpha) =
      X.1 2 0 := by
    simp [InfoGeometry.Exceptional.Freudenthal.alpha_add,
      InfoGeometry.Exceptional.Freudenthal.alpha_smul,
      InfoGeometry.Physics.NuclearFiveGradeGeneratorRepresentation.q1Charge,
      InfoGeometry.Physics.NuclearFiveGradeGeneratorRepresentation.q2Charge]
  have hp1_b : ((X.1 2 0 •
      (InfoGeometry.Physics.NuclearFiveGradeGeneratorRepresentation.q1Charge :
        InfoGeometry.Exceptional.Freudenthal.FreudenthalCharge PUnit.{1}) +
      X.1 1 0 • InfoGeometry.Physics.NuclearFiveGradeGeneratorRepresentation.q2Charge).beta) =
      X.1 1 0 := by
    simp [InfoGeometry.Exceptional.Freudenthal.beta_add,
      InfoGeometry.Exceptional.Freudenthal.beta_smul,
      InfoGeometry.Physics.NuclearFiveGradeGeneratorRepresentation.q1Charge,
      InfoGeometry.Physics.NuclearFiveGradeGeneratorRepresentation.q2Charge]
  rw [hsymp, hm1_a, hm1_b, hp1_a, hp1_b, neg_smul, sub_neg_eq_add]
  conv_rhs => rw [carLieSubalgebra_entry_decomp X.2]
  abel

/-- Concrete nuclear CAR–BdG–Soloviev 5-grading coherence theorem integrating:
1. `m4rToOp` and `carToFiveGraded` grade preservation,
2. `Phi` left-inverse property, `m4rGrade` internal direct sum, and Freudenthal mixed-Jacobi obstruction,
3. `NuclearFiveGradeBdGSolovievClosure`, `NuclearFiveGradeDegreeZeroSL2`, and `NuclearFiveGradeCircularPhase`,
4. `FiveGradedIwasawa` 2-step nilpotency of the `+1/+2` N-sector inside `carLieSubalgebra`. -/
theorem nuclear_car_five_grade_chain_theorem
    (g : InfoGeometry.Physics.NuclearFiveGradeGeneratorRepresentation.Generator)
    (Eqp ω V ξ Δ E : ℂ)
    (c h : ℝ)
    (x y : InfoGeometry.Exceptional.Freudenthal.FreudenthalCharge PUnit.{1})
    (T : InfoGeometry.Exceptional.Freudenthal.SymplecticTKKZero
      InfoGeometry.Nuclear.FiveGraded.punitCubicJordanDatum)
    (X₁ X₂ Y₁ Y₂ Z₁ Z₂ :
      InfoGeometry.Physics.NuclearFiveGradeGeneratorRepresentation.carLieSubalgebra)
    (hX₁ : InfoGeometry.Algebra.FiveGradedIwasawa.InGrade gradingCartanSub 1 X₁)
    (hX₂ : InfoGeometry.Algebra.FiveGradedIwasawa.InGrade gradingCartanSub 2 X₂)
    (hY₁ : InfoGeometry.Algebra.FiveGradedIwasawa.InGrade gradingCartanSub 1 Y₁)
    (hY₂ : InfoGeometry.Algebra.FiveGradedIwasawa.InGrade gradingCartanSub 2 Y₂)
    (hZ₁ : InfoGeometry.Algebra.FiveGradedIwasawa.InGrade gradingCartanSub 1 Z₁)
    (hZ₂ : InfoGeometry.Algebra.FiveGradedIwasawa.InGrade gradingCartanSub 2 Z₂) :
    InfoGeometry.Physics.NuclearTwoModeCARFiveGrade.HasGrade
        (InfoGeometry.Physics.NuclearFiveGradeGeneratorRepresentation.degree g)
        (InfoGeometry.Physics.NuclearFiveGradeGeneratorRepresentation.m4rToOp
          (InfoGeometry.Physics.NuclearFiveGradeGeneratorRepresentation.representM4R g)) ∧
    InfoGeometry.Exceptional.Freudenthal.SymplecticContactHasGrade
        InfoGeometry.Nuclear.FiveGraded.punitCubicJordanDatum
        (InfoGeometry.Physics.NuclearFiveGradeGeneratorRepresentation.degree g)
        (InfoGeometry.Physics.NuclearFiveGradeGeneratorRepresentation.carToFiveGraded
          InfoGeometry.Nuclear.FiveGraded.punitCubicJordanDatum
          ⟨InfoGeometry.Physics.NuclearFiveGradeGeneratorRepresentation.representM4R g,
           InfoGeometry.Physics.NuclearFiveGradeGeneratorRepresentation.representM4R_mem_carLieSubalgebra g⟩) ∧
    DirectSum.IsInternal InfoGeometry.Nuclear.FiveGraded.m4rGrade ∧
    InfoGeometry.Nuclear.FiveGraded.Phi
        (InfoGeometry.Physics.NuclearFiveGradeGeneratorRepresentation.carToFiveGraded
          InfoGeometry.Nuclear.FiveGraded.punitCubicJordanDatum X₁) = X₁.1 ∧
    (InfoGeometry.Physics.NuclearFiveGradeGeneratorRepresentation.represent g =
        InfoGeometry.Physics.NuclearFiveGradeGeneratorRepresentation.m4rToOp
          (InfoGeometry.Physics.NuclearFiveGradeGeneratorRepresentation.representM4R g)) ∧
    (InfoGeometry.Physics.NuclearFiveGradeCircularPhase.quarterTurn ^ 4 = 1 ∧
      InfoGeometry.Physics.NuclearFiveGradeCircularPhase.circularCharacter g =
        Complex.I ^ InfoGeometry.Physics.NuclearFiveGradeGeneratorRepresentation.degree g ∧
      InfoGeometry.Physics.NuclearFiveGradeCircularPhase.quarterTurn *
          InfoGeometry.Physics.NuclearFiveGradeGeneratorRepresentation.represent g =
        InfoGeometry.Physics.NuclearFiveGradeCircularPhase.circularCharacter g •
          (InfoGeometry.Physics.NuclearFiveGradeGeneratorRepresentation.represent g *
            InfoGeometry.Physics.NuclearFiveGradeCircularPhase.quarterTurn)) ∧
    (InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.HasGrade 0
        InfoGeometry.Physics.NuclearFiveGradeDegreeZeroSL2.degreeZeroRaise ∧
      InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.HasGrade 0
        InfoGeometry.Physics.NuclearFiveGradeDegreeZeroSL2.degreeZeroLower ∧
      InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.HasGrade 0
        InfoGeometry.Physics.NuclearFiveGradeDegreeZeroSL2.degreeZeroCartan) ∧
    (Matrix.det (InfoGeometry.Physics.NuclearBdGSolovievCompression.solovievBlock Eqp ω V -
        E • (1 : InfoGeometry.Physics.NuclearBdGSolovievCompression.Mat2)) =
      (Eqp - E) * (Eqp + ω - E) - V ^ 2 ∧
      InfoGeometry.Physics.NuclearBdGSolovievCompression.bdgBlock ξ Δ *
        InfoGeometry.Physics.NuclearBdGSolovievCompression.bdgBlock ξ Δ =
        (ξ ^ 2 + Δ ^ 2) • (1 : InfoGeometry.Physics.NuclearBdGSolovievCompression.Mat2)) ∧
    (InfoGeometry.Nuclear.FiveGraded.Phi
        (InfoGeometry.Nuclear.FiveGraded.pairingCreation
          InfoGeometry.Nuclear.FiveGraded.punitCubicJordanDatum c) ∈
          InfoGeometry.Nuclear.FiveGraded.m4rGrade 4 ∧
      InfoGeometry.Nuclear.FiveGraded.Phi
        (InfoGeometry.Nuclear.FiveGraded.gradingOperator
          InfoGeometry.Nuclear.FiveGraded.punitCubicJordanDatum h) ∈
          InfoGeometry.Nuclear.FiveGraded.m4rGrade 2 ∧
      InfoGeometry.Nuclear.FiveGraded.Phi
        (InfoGeometry.Nuclear.FiveGraded.qpAnnihilation
          InfoGeometry.Nuclear.FiveGraded.punitCubicJordanDatum x) ∈
          InfoGeometry.Nuclear.FiveGraded.m4rGrade 1 ∧
      InfoGeometry.Nuclear.FiveGraded.Phi
        (InfoGeometry.Nuclear.FiveGraded.multipoleOperator
          InfoGeometry.Nuclear.FiveGraded.punitCubicJordanDatum T) ∈
          InfoGeometry.Nuclear.FiveGraded.m4rGrade 2 ∧
      InfoGeometry.Nuclear.FiveGraded.Phi
        (InfoGeometry.Nuclear.FiveGraded.qpCreation
          InfoGeometry.Nuclear.FiveGraded.punitCubicJordanDatum y) ∈
          InfoGeometry.Nuclear.FiveGraded.m4rGrade 3) ∧
    ⁅⁅X₁ + X₂, Y₁ + Y₂⁆, Z₁ + Z₂⁆ = 0 := by
  have hrep := InfoGeometry.Physics.NuclearFiveGradeGeneratorRepresentation.m4rToOp_representM4R g
  have hPhi := InfoGeometry.Nuclear.FiveGraded.Phi_preserves_grades c h x y T
  have hclo := InfoGeometry.Physics.NuclearFiveGradeBdGSolovievClosure.finite_nuclear_lane_closure
    Eqp ω V ξ Δ E
  have hdeg0 := InfoGeometry.Physics.NuclearFiveGradeDegreeZeroSL2.degree_zero_sl2_selection_packet
  refine ⟨?_, ?_, InfoGeometry.Nuclear.FiveGraded.m4rGrade_directSum,
    Phi_comp_carToFiveGraded X₁, hrep.symm, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hrep]
    exact InfoGeometry.Physics.NuclearFiveGradeGeneratorRepresentation.represent_hasGrade g
  · exact InfoGeometry.Physics.NuclearFiveGradeGeneratorRepresentation.carToFiveGraded_preserves_grade
      InfoGeometry.Nuclear.FiveGraded.punitCubicJordanDatum
      (InfoGeometry.Physics.NuclearFiveGradeGeneratorRepresentation.representM4R_hasGrade g)
  · exact ⟨InfoGeometry.Physics.NuclearFiveGradeCircularPhase.quarterTurn_fourth_power,
      InfoGeometry.Physics.NuclearFiveGradeCircularPhase.circularCharacter_eq_grade_phase g,
      InfoGeometry.Physics.NuclearFiveGradeCircularPhase.generator_quarterTurn_covariance g⟩
  · exact ⟨hdeg0.1, hdeg0.2.1, hdeg0.2.2.1⟩
  · exact ⟨hclo.2.2.2.2.2.2.2.1, hclo.2.2.2.2.2.1⟩
  · exact ⟨hPhi.2.2.2.2.2.1, hPhi.2.2.1.1, hPhi.2.1.1, hPhi.2.2.2.1.1, hPhi.2.2.2.2.1.1⟩
  · exact InfoGeometry.Algebra.FiveGradedIwasawa.iwasawa_n_sector_nilpotent
      gradingCartanSub X₁ X₂ Y₁ Y₂ Z₁ Z₂ hX₁ hX₂ hY₁ hY₂ hZ₁ hZ₂

/-!
## Section 3: `(Fin 2 ⊕ Fin 1) ≃ Fin 3` OSp Super-Grassmannian, Krein SUSY, `pairSL2 ≃ₗ⁅ℝ⁆ ospEvenLieSubalgebra`, & `Cuntz3` Embedding
-/

/-- Reindexing equivalence `(Fin 2 ⊕ Fin 1) ≃ Fin 3` matching the `2|1` OSp ordering `(0, 2 | 1)`. -/
def fin2SumFin1EquivFin3 : (Fin 2 ⊕ Fin 1) ≃ Fin 3 where
  toFun
    | .inl 0 => 0
    | .inl 1 => 2
    | .inr 0 => 1
  invFun
    | 0 => .inl 0
    | 1 => .inr 0
    | 2 => .inl 1
  left_inv x := by
    rcases x with i | j
    · fin_cases i <;> rfl
    · fin_cases j
      rfl
  right_inv k := by fin_cases k <;> rfl

/-- Explicit matrix reindexing from the `2|1` OSp carrier `M₃(ℝ)` to the `(Fin 2 ⊕ Fin 1)`
Super-Grassmannian carrier. -/
def ospToSuperBlock3 (X : M₃) : Matrix (Fin 2 ⊕ Fin 1) (Fin 2 ⊕ Fin 1) ℝ :=
  X.submatrix fin2SumFin1EquivFin3 fin2SumFin1EquivFin3

/-- Explicit associative `ℝ`-algebra isomorphism `M₃(ℝ) ≃ₐ[ℝ] Matrix (Fin 2 ⊕ Fin 1) (Fin 2 ⊕ Fin 1) ℝ`. -/
def ospToSuperBlock3AlgEquiv : M₃ ≃ₐ[ℝ] Matrix (Fin 2 ⊕ Fin 1) (Fin 2 ⊕ Fin 1) ℝ :=
  Matrix.reindexAlgEquiv ℝ ℝ fin2SumFin1EquivFin3.symm

@[simp] theorem ospToSuperBlock3AlgEquiv_apply (X : M₃) :
    ospToSuperBlock3AlgEquiv X = ospToSuperBlock3 X := by
  ext i j
  rfl

theorem superTrace_ospToSuperBlock3 (X : M₃) :
    InfoGeometry.SuperGrassmannian.NuclearQuasiphononSuperGrassmannian.superTrace
        (ospToSuperBlock3 X) =
      InfoGeometry.SuperGrassmannian.SuperconformalOSpJordanPair.supertrace X := by
  dsimp [InfoGeometry.SuperGrassmannian.NuclearQuasiphononSuperGrassmannian.superTrace,
    InfoGeometry.SuperGrassmannian.SuperconformalOSpJordanPair.supertrace,
    ospToSuperBlock3, Matrix.toBlocks₁₁, Matrix.toBlocks₂₂]
  simp [Matrix.trace, Matrix.diag, Fin.sum_univ_two, fin2SumFin1EquivFin3]
  ring

theorem ospToSuperBlock3_embed21 (A : M₂) (c : ℝ) :
    ospToSuperBlock3 (InfoGeometry.Nuclear.NuclearQuasiphononJordanPairBridge.embed21Matrix A c) =
      InfoGeometry.SuperGrassmannian.NuclearQuasiphononSuperGrassmannian.volumeMode A
        (Matrix.of fun _ _ : Fin 1 => c) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [ospToSuperBlock3, fin2SumFin1EquivFin3,
      InfoGeometry.Nuclear.NuclearQuasiphononJordanPairBridge.embed21Matrix,
      InfoGeometry.SuperGrassmannian.NuclearQuasiphononSuperGrassmannian.volumeMode]

theorem ospToSuperBlock3_scale (σ : ℝ) :
    ospToSuperBlock3
        (InfoGeometry.Nuclear.NuclearQuasiphononJordanPairBridge.embed21Matrix (σ • (1 : M₂)) σ) =
      InfoGeometry.SuperGrassmannian.NuclearQuasiphononSuperGrassmannian.scaleMode σ := by
  rw [ospToSuperBlock3_embed21]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [InfoGeometry.SuperGrassmannian.NuclearQuasiphononSuperGrassmannian.volumeMode,
      InfoGeometry.SuperGrassmannian.NuclearQuasiphononSuperGrassmannian.scaleMode]

theorem ospToSuperBlock3_Q_plus_chiral :
    ospToSuperBlock3 (InfoGeometry.SuperGrassmannian.SuperconformalOSpJordanPair.Q_plus ℝ) =
      InfoGeometry.SuperGrassmannian.NuclearQuasiphononSuperGrassmannian.chiralMode
        !![1; 0] !![0, 1] := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [ospToSuperBlock3, fin2SumFin1EquivFin3,
      InfoGeometry.SuperGrassmannian.SuperconformalOSpJordanPair.Q_plus,
      InfoGeometry.SuperGrassmannian.SuperconformalOSpJordanPair.E,
      InfoGeometry.SuperGrassmannian.NuclearQuasiphononSuperGrassmannian.chiralMode]

theorem ospToSuperBlock3_Q_minus_chiral :
    ospToSuperBlock3 (InfoGeometry.SuperGrassmannian.SuperconformalOSpJordanPair.Q_minus ℝ) =
      InfoGeometry.SuperGrassmannian.NuclearQuasiphononSuperGrassmannian.chiralMode
        !![0; -1] !![1, 0] := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [ospToSuperBlock3, fin2SumFin1EquivFin3,
      InfoGeometry.SuperGrassmannian.SuperconformalOSpJordanPair.Q_minus,
      InfoGeometry.SuperGrassmannian.SuperconformalOSpJordanPair.E,
      InfoGeometry.SuperGrassmannian.NuclearQuasiphononSuperGrassmannian.chiralMode]

theorem ospToSuperBlock3_H_gen :
    ospToSuperBlock3 (InfoGeometry.SuperGrassmannian.SuperconformalOSpJordanPair.H_gen ℝ) =
      InfoGeometry.SuperGrassmannian.NuclearQuasiphononSuperGrassmannian.volumeMode
        !![1, 0; 0, -1] (0 : Matrix (Fin 1) (Fin 1) ℝ) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [ospToSuperBlock3, fin2SumFin1EquivFin3,
      InfoGeometry.SuperGrassmannian.SuperconformalOSpJordanPair.H_gen,
      InfoGeometry.SuperGrassmannian.SuperconformalOSpJordanPair.E,
      InfoGeometry.SuperGrassmannian.NuclearQuasiphononSuperGrassmannian.volumeMode]

theorem ospToSuperBlock3_E_gen :
    ospToSuperBlock3 (InfoGeometry.SuperGrassmannian.SuperconformalOSpJordanPair.E_gen ℝ) =
      InfoGeometry.SuperGrassmannian.NuclearQuasiphononSuperGrassmannian.volumeMode
        !![0, 1; 0, 0] (0 : Matrix (Fin 1) (Fin 1) ℝ) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [ospToSuperBlock3, fin2SumFin1EquivFin3,
      InfoGeometry.SuperGrassmannian.SuperconformalOSpJordanPair.E_gen,
      InfoGeometry.SuperGrassmannian.SuperconformalOSpJordanPair.E,
      InfoGeometry.SuperGrassmannian.NuclearQuasiphononSuperGrassmannian.volumeMode]

theorem ospToSuperBlock3_F_gen :
    ospToSuperBlock3 (InfoGeometry.SuperGrassmannian.SuperconformalOSpJordanPair.F_gen ℝ) =
      InfoGeometry.SuperGrassmannian.NuclearQuasiphononSuperGrassmannian.volumeMode
        !![0, 0; 1, 0] (0 : Matrix (Fin 1) (Fin 1) ℝ) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [ospToSuperBlock3, fin2SumFin1EquivFin3,
      InfoGeometry.SuperGrassmannian.SuperconformalOSpJordanPair.F_gen,
      InfoGeometry.SuperGrassmannian.SuperconformalOSpJordanPair.E,
      InfoGeometry.SuperGrassmannian.NuclearQuasiphononSuperGrassmannian.volumeMode]

/-- Explicit `pairSL2 ↦ ospEven` coordinate map `M₄(ℝ) → M₃(ℝ)` matching
`(pairCreation, gradingOperator, pairAnnihilation) ↦ (E_gen ℝ, H_gen ℝ, F_gen ℝ)`. -/
def pairSL2ToM3 (X : M4R) : M₃ :=
  X 3 0 • InfoGeometry.SuperGrassmannian.SuperconformalOSpJordanPair.E_gen ℝ +
    X 3 3 • InfoGeometry.SuperGrassmannian.SuperconformalOSpJordanPair.H_gen ℝ +
    X 0 3 • InfoGeometry.SuperGrassmannian.SuperconformalOSpJordanPair.F_gen ℝ

/-- Explicit inverse `ospEven ↦ pairSL2` coordinate map `M₃(ℝ) → M₄(ℝ)`. -/
def m3ToPairSL2 (Y : M₃) : M4R :=
  Y 0 2 • InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.pairCreation +
    Y 0 0 • InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.gradingOperator +
    Y 2 0 • InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.pairAnnihilation

private lemma pairSL2_bracket_formula (a₁ h₁ f₁ a₂ h₂ f₂ : ℝ) :
    (a₁ • InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.pairCreation +
      h₁ • InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.gradingOperator +
      f₁ • InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.pairAnnihilation) *
    (a₂ • InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.pairCreation +
      h₂ • InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.gradingOperator +
      f₂ • InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.pairAnnihilation) -
    (a₂ • InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.pairCreation +
      h₂ • InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.gradingOperator +
      f₂ • InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.pairAnnihilation) *
    (a₁ • InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.pairCreation +
      h₁ • InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.gradingOperator +
      f₁ • InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.pairAnnihilation) =
    (2 * h₁ * a₂ - 2 * h₂ * a₁) • InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.pairCreation +
    (a₁ * f₂ - a₂ * f₁) • InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.gradingOperator +
    (2 * h₂ * f₁ - 2 * h₁ * f₂) • InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.pairAnnihilation := by
  have h1 : InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.gradingOperator *
      InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.pairCreation -
      InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.pairCreation *
      InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.gradingOperator =
      (2 : ℝ) • InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.pairCreation :=
    InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.grading_pairCreation
  have h2 : InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.gradingOperator *
      InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.pairAnnihilation -
      InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.pairAnnihilation *
      InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.gradingOperator =
      (-2 : ℝ) • InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.pairAnnihilation :=
    InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.grading_pairAnnihilation
  have h3 : InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.pairCreation *
      InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.pairAnnihilation -
      InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.pairAnnihilation *
      InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.pairCreation =
      InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.gradingOperator :=
    InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.pair_extreme_bracket
  have h1' : InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.pairCreation *
      InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.gradingOperator =
      InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.gradingOperator *
      InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.pairCreation -
      (2 : ℝ) • InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.pairCreation := by
    rw [← h1]; noncomm_ring
  have h2neg : (2 : ℝ) • InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.pairAnnihilation =
      -(InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.gradingOperator *
          InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.pairAnnihilation -
        InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.pairAnnihilation *
          InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.gradingOperator) := by
    rw [h2, neg_smul, neg_neg]
  have h2' : InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.pairAnnihilation *
      InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.gradingOperator =
      InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.gradingOperator *
      InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.pairAnnihilation +
      (2 : ℝ) • InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.pairAnnihilation := by
    rw [h2neg]; noncomm_ring
  have h3' : InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.pairAnnihilation *
      InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.pairCreation =
      InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.pairCreation *
      InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.pairAnnihilation -
      InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.gradingOperator := by
    rw [← h3]; noncomm_ring
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, h1', h2', h3']
  module

private lemma ospEven_bracket_formula (a₁ h₁ f₁ a₂ h₂ f₂ : ℝ) :
    (a₁ • InfoGeometry.SuperGrassmannian.SuperconformalOSpJordanPair.E_gen ℝ +
      h₁ • InfoGeometry.SuperGrassmannian.SuperconformalOSpJordanPair.H_gen ℝ +
      f₁ • InfoGeometry.SuperGrassmannian.SuperconformalOSpJordanPair.F_gen ℝ) *
    (a₂ • InfoGeometry.SuperGrassmannian.SuperconformalOSpJordanPair.E_gen ℝ +
      h₂ • InfoGeometry.SuperGrassmannian.SuperconformalOSpJordanPair.H_gen ℝ +
      f₂ • InfoGeometry.SuperGrassmannian.SuperconformalOSpJordanPair.F_gen ℝ) -
    (a₂ • InfoGeometry.SuperGrassmannian.SuperconformalOSpJordanPair.E_gen ℝ +
      h₂ • InfoGeometry.SuperGrassmannian.SuperconformalOSpJordanPair.H_gen ℝ +
      f₂ • InfoGeometry.SuperGrassmannian.SuperconformalOSpJordanPair.F_gen ℝ) *
    (a₁ • InfoGeometry.SuperGrassmannian.SuperconformalOSpJordanPair.E_gen ℝ +
      h₁ • InfoGeometry.SuperGrassmannian.SuperconformalOSpJordanPair.H_gen ℝ +
      f₁ • InfoGeometry.SuperGrassmannian.SuperconformalOSpJordanPair.F_gen ℝ) =
    (2 * h₁ * a₂ - 2 * h₂ * a₁) • InfoGeometry.SuperGrassmannian.SuperconformalOSpJordanPair.E_gen ℝ +
    (a₁ * f₂ - a₂ * f₁) • InfoGeometry.SuperGrassmannian.SuperconformalOSpJordanPair.H_gen ℝ +
    (2 * h₂ * f₁ - 2 * h₁ * f₂) • InfoGeometry.SuperGrassmannian.SuperconformalOSpJordanPair.F_gen ℝ := by
  have h1 : InfoGeometry.SuperGrassmannian.SuperconformalOSpJordanPair.H_gen ℝ *
      InfoGeometry.SuperGrassmannian.SuperconformalOSpJordanPair.E_gen ℝ -
      InfoGeometry.SuperGrassmannian.SuperconformalOSpJordanPair.E_gen ℝ *
      InfoGeometry.SuperGrassmannian.SuperconformalOSpJordanPair.H_gen ℝ =
      (2 : ℝ) • InfoGeometry.SuperGrassmannian.SuperconformalOSpJordanPair.E_gen ℝ := by
    have h := InfoGeometry.SuperGrassmannian.SuperconformalOSpJordanPair.osp_sl2_H_E (R := ℝ)
    change InfoGeometry.SuperGrassmannian.SuperconformalOSpJordanPair.H_gen ℝ *
        InfoGeometry.SuperGrassmannian.SuperconformalOSpJordanPair.E_gen ℝ -
        InfoGeometry.SuperGrassmannian.SuperconformalOSpJordanPair.E_gen ℝ *
        InfoGeometry.SuperGrassmannian.SuperconformalOSpJordanPair.H_gen ℝ =
      (2 : ℕ) • InfoGeometry.SuperGrassmannian.SuperconformalOSpJordanPair.E_gen ℝ at h
    rw [h, ← Nat.cast_smul_eq_nsmul ℝ 2]
    norm_num
  have h2 : InfoGeometry.SuperGrassmannian.SuperconformalOSpJordanPair.H_gen ℝ *
      InfoGeometry.SuperGrassmannian.SuperconformalOSpJordanPair.F_gen ℝ -
      InfoGeometry.SuperGrassmannian.SuperconformalOSpJordanPair.F_gen ℝ *
      InfoGeometry.SuperGrassmannian.SuperconformalOSpJordanPair.H_gen ℝ =
      (-2 : ℝ) • InfoGeometry.SuperGrassmannian.SuperconformalOSpJordanPair.F_gen ℝ := by
    have h := InfoGeometry.SuperGrassmannian.SuperconformalOSpJordanPair.osp_sl2_H_F (R := ℝ)
    change InfoGeometry.SuperGrassmannian.SuperconformalOSpJordanPair.H_gen ℝ *
        InfoGeometry.SuperGrassmannian.SuperconformalOSpJordanPair.F_gen ℝ -
        InfoGeometry.SuperGrassmannian.SuperconformalOSpJordanPair.F_gen ℝ *
        InfoGeometry.SuperGrassmannian.SuperconformalOSpJordanPair.H_gen ℝ =
      (-2 : ℤ) • InfoGeometry.SuperGrassmannian.SuperconformalOSpJordanPair.F_gen ℝ at h
    rw [h, ← Int.cast_smul_eq_zsmul ℝ (-2)]
    norm_num
  have h3 : InfoGeometry.SuperGrassmannian.SuperconformalOSpJordanPair.E_gen ℝ *
      InfoGeometry.SuperGrassmannian.SuperconformalOSpJordanPair.F_gen ℝ -
      InfoGeometry.SuperGrassmannian.SuperconformalOSpJordanPair.F_gen ℝ *
      InfoGeometry.SuperGrassmannian.SuperconformalOSpJordanPair.E_gen ℝ =
      InfoGeometry.SuperGrassmannian.SuperconformalOSpJordanPair.H_gen ℝ :=
    InfoGeometry.SuperGrassmannian.SuperconformalOSpJordanPair.osp_sl2_E_F
  have h1' : InfoGeometry.SuperGrassmannian.SuperconformalOSpJordanPair.E_gen ℝ *
      InfoGeometry.SuperGrassmannian.SuperconformalOSpJordanPair.H_gen ℝ =
      InfoGeometry.SuperGrassmannian.SuperconformalOSpJordanPair.H_gen ℝ *
      InfoGeometry.SuperGrassmannian.SuperconformalOSpJordanPair.E_gen ℝ -
      (2 : ℝ) • InfoGeometry.SuperGrassmannian.SuperconformalOSpJordanPair.E_gen ℝ := by
    rw [← h1]; noncomm_ring
  have h2neg : (2 : ℝ) • InfoGeometry.SuperGrassmannian.SuperconformalOSpJordanPair.F_gen ℝ =
      -(InfoGeometry.SuperGrassmannian.SuperconformalOSpJordanPair.H_gen ℝ *
          InfoGeometry.SuperGrassmannian.SuperconformalOSpJordanPair.F_gen ℝ -
        InfoGeometry.SuperGrassmannian.SuperconformalOSpJordanPair.F_gen ℝ *
          InfoGeometry.SuperGrassmannian.SuperconformalOSpJordanPair.H_gen ℝ) := by
    rw [h2, neg_smul, neg_neg]
  have h2' : InfoGeometry.SuperGrassmannian.SuperconformalOSpJordanPair.F_gen ℝ *
      InfoGeometry.SuperGrassmannian.SuperconformalOSpJordanPair.H_gen ℝ =
      InfoGeometry.SuperGrassmannian.SuperconformalOSpJordanPair.H_gen ℝ *
      InfoGeometry.SuperGrassmannian.SuperconformalOSpJordanPair.F_gen ℝ +
      (2 : ℝ) • InfoGeometry.SuperGrassmannian.SuperconformalOSpJordanPair.F_gen ℝ := by
    rw [h2neg]; noncomm_ring
  have h3' : InfoGeometry.SuperGrassmannian.SuperconformalOSpJordanPair.F_gen ℝ *
      InfoGeometry.SuperGrassmannian.SuperconformalOSpJordanPair.E_gen ℝ =
      InfoGeometry.SuperGrassmannian.SuperconformalOSpJordanPair.E_gen ℝ *
      InfoGeometry.SuperGrassmannian.SuperconformalOSpJordanPair.F_gen ℝ -
      InfoGeometry.SuperGrassmannian.SuperconformalOSpJordanPair.H_gen ℝ := by
    rw [← h3]; noncomm_ring
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, h1', h2', h3']
  module

private def pairSL2SpanSubalgebra : LieSubalgebra ℝ M4R where
  carrier := {X | X = X 3 0 • InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.pairCreation +
    X 3 3 • InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.gradingOperator +
    X 0 3 • InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.pairAnnihilation}
  zero_mem' := by simp
  add_mem' {X Y} hX hY := by
    change X + Y = (X + Y) 3 0 • _ + (X + Y) 3 3 • _ + (X + Y) 0 3 • _
    ext i j
    have hX' := congr_fun (congr_fun hX i) j
    have hY' := congr_fun (congr_fun hY i) j
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul] at hX' hY' ⊢
    rw [hX', hY']
    ring
  smul_mem' r {X} hX := by
    change r • X = (r • X) 3 0 • _ + (r • X) 3 3 • _ + (r • X) 0 3 • _
    ext i j
    have hX' := congr_fun (congr_fun hX i) j
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul] at hX' ⊢
    rw [hX']
    ring
  lie_mem' {X Y} hX hY := by
    change X * Y - Y * X = (X * Y - Y * X) 3 0 • _ + (X * Y - Y * X) 3 3 • _ + (X * Y - Y * X) 0 3 • _
    have hbr : X * Y - Y * X =
        (2 * X 3 3 * Y 3 0 - 2 * Y 3 3 * X 3 0) • InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.pairCreation +
        (X 3 0 * Y 0 3 - Y 3 0 * X 0 3) • InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.gradingOperator +
        (2 * Y 3 3 * X 0 3 - 2 * X 3 3 * Y 0 3) • InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.pairAnnihilation := by
      conv_lhs => rw [hX, hY]
      exact pairSL2_bracket_formula (X 3 0) (X 3 3) (X 0 3) (Y 3 0) (Y 3 3) (Y 0 3)
    rw [hbr, pairCreation_eq_mat4, pairAnnihilation_eq_mat4,
      InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.gradingOperator_eq_diagonal]
    ext i j
    fin_cases i <;> fin_cases j <;> simp

private theorem mem_pairSL2Subalgebra_eq {X : M4R}
    (hX : X ∈ InfoGeometry.Physics.NuclearFiveGradeGeneratorRepresentation.pairSL2Subalgebra) :
    X = X 3 0 • InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.pairCreation +
      X 3 3 • InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.gradingOperator +
      X 0 3 • InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.pairAnnihilation := by
  have hle : InfoGeometry.Physics.NuclearFiveGradeGeneratorRepresentation.pairSL2Subalgebra ≤
      pairSL2SpanSubalgebra := by
    rw [InfoGeometry.Physics.NuclearFiveGradeGeneratorRepresentation.pairSL2Subalgebra,
      LieSubalgebra.lieSpan_le]
    intro Z hZ
    rcases hZ with rfl | rfl | rfl
    · change InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.pairCreation = _
      rw [pairCreation_eq_mat4, pairAnnihilation_eq_mat4,
        InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.gradingOperator_eq_diagonal]
      ext i j; fin_cases i <;> fin_cases j <;> simp
    · change InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.gradingOperator = _
      rw [pairCreation_eq_mat4, pairAnnihilation_eq_mat4,
        InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.gradingOperator_eq_diagonal]
      ext i j; fin_cases i <;> fin_cases j <;> simp
    · change InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.pairAnnihilation = _
      rw [pairCreation_eq_mat4, pairAnnihilation_eq_mat4,
        InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.gradingOperator_eq_diagonal]
      ext i j; fin_cases i <;> fin_cases j <;> simp
  exact hle hX

private theorem mem_ospEvenLieSubalgebra_eq {Y : M₃}
    (hY : Y ∈ InfoGeometry.Nuclear.NuclearQuasiphononJordanPairBridge.ospEvenLieSubalgebra) :
    Y = Y 0 2 • InfoGeometry.SuperGrassmannian.SuperconformalOSpJordanPair.E_gen ℝ +
      Y 0 0 • InfoGeometry.SuperGrassmannian.SuperconformalOSpJordanPair.H_gen ℝ +
      Y 2 0 • InfoGeometry.SuperGrassmannian.SuperconformalOSpJordanPair.F_gen ℝ := by
  change Y ∈ InfoGeometry.SuperGrassmannian.SuperconformalOSpJordanPair.MatrixSpans.evenSpan at hY
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hY
  · rintro _ ⟨i, rfl⟩
    cases i <;> ext r c <;> fin_cases r <;> fin_cases c <;>
      simp [InfoGeometry.SuperGrassmannian.SuperconformalOSpJordanPair.MatrixSpans.evenBasis,
        InfoGeometry.SuperGrassmannian.SuperconformalOSpJordanPair.H_gen,
        InfoGeometry.SuperGrassmannian.SuperconformalOSpJordanPair.E_gen,
        InfoGeometry.SuperGrassmannian.SuperconformalOSpJordanPair.F_gen,
        InfoGeometry.SuperGrassmannian.SuperconformalOSpJordanPair.E]
  · simp
  · intro A B _ _ hA hB
    ext r c
    have hA' := congr_fun (congr_fun hA r) c
    have hB' := congr_fun (congr_fun hB r) c
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul] at hA' hB' ⊢
    rw [hA', hB']
    ring
  · intro r A _ hA
    ext i j
    have hA' := congr_fun (congr_fun hA i) j
    simp only [Matrix.smul_apply, smul_eq_mul] at hA' ⊢
    conv_lhs => rw [hA']
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    ring

private theorem pairSL2ToM3_mem_ospEven (X : M4R) :
    pairSL2ToM3 X ∈ InfoGeometry.Nuclear.NuclearQuasiphononJordanPairBridge.ospEvenLieSubalgebra := by
  dsimp [pairSL2ToM3, InfoGeometry.Nuclear.NuclearQuasiphononJordanPairBridge.ospEvenLieSubalgebra]
  exact Submodule.add_mem _
    (Submodule.add_mem _
      (Submodule.smul_mem _ _ InfoGeometry.SuperGrassmannian.SuperconformalOSpJordanPair.MatrixSpans.even_E_mem)
      (Submodule.smul_mem _ _ InfoGeometry.SuperGrassmannian.SuperconformalOSpJordanPair.MatrixSpans.even_H_mem))
    (Submodule.smul_mem _ _ InfoGeometry.SuperGrassmannian.SuperconformalOSpJordanPair.MatrixSpans.even_F_mem)

private theorem m3ToPairSL2_mem_pairSL2 (Y : M₃) :
    m3ToPairSL2 Y ∈ InfoGeometry.Physics.NuclearFiveGradeGeneratorRepresentation.pairSL2Subalgebra := by
  dsimp [m3ToPairSL2]
  refine Submodule.add_mem _
    (Submodule.add_mem _
      (Submodule.smul_mem _ _ (LieSubalgebra.subset_lieSpan (by simp)))
      (Submodule.smul_mem _ _ (LieSubalgebra.subset_lieSpan (by simp))))
    (Submodule.smul_mem _ _ (LieSubalgebra.subset_lieSpan (by simp)))

private lemma pairSL2ToM3_comb (u v w : ℝ) :
    pairSL2ToM3 (u • InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.pairCreation +
      v • InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.gradingOperator +
      w • InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.pairAnnihilation) =
    u • InfoGeometry.SuperGrassmannian.SuperconformalOSpJordanPair.E_gen ℝ +
      v • InfoGeometry.SuperGrassmannian.SuperconformalOSpJordanPair.H_gen ℝ +
      w • InfoGeometry.SuperGrassmannian.SuperconformalOSpJordanPair.F_gen ℝ := by
  dsimp [pairSL2ToM3]
  rw [pairCreation_eq_mat4, pairAnnihilation_eq_mat4,
    InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.gradingOperator_eq_diagonal]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [InfoGeometry.SuperGrassmannian.SuperconformalOSpJordanPair.E_gen,
      InfoGeometry.SuperGrassmannian.SuperconformalOSpJordanPair.H_gen,
      InfoGeometry.SuperGrassmannian.SuperconformalOSpJordanPair.F_gen,
      InfoGeometry.SuperGrassmannian.SuperconformalOSpJordanPair.E]

/-- Exact `ℝ`-Lie algebra isomorphism `pairSL2Subalgebra ≃ₗ⁅ℝ⁆ ospEvenLieSubalgebra`
intertwining `(pairCreation, gradingOperator, pairAnnihilation)` with `(E_gen ℝ, H_gen ℝ, F_gen ℝ)`. -/
def pairSL2ToOSpEvenEquiv :
    InfoGeometry.Physics.NuclearFiveGradeGeneratorRepresentation.pairSL2Subalgebra ≃ₗ⁅ℝ⁆
      InfoGeometry.Nuclear.NuclearQuasiphononJordanPairBridge.ospEvenLieSubalgebra where
  toFun X := ⟨pairSL2ToM3 X.1, pairSL2ToM3_mem_ospEven X.1⟩
  invFun Y := ⟨m3ToPairSL2 Y.1, m3ToPairSL2_mem_pairSL2 Y.1⟩
  map_add' X₁ X₂ := by
    apply Subtype.ext
    ext i j
    simp [pairSL2ToM3]
    ring
  map_smul' r X := by
    apply Subtype.ext
    ext i j
    simp [pairSL2ToM3]
    ring
  map_lie' {X₁ X₂} := by
    apply Subtype.ext
    have h1 := mem_pairSL2Subalgebra_eq X₁.2
    have h2 := mem_pairSL2Subalgebra_eq X₂.2
    change pairSL2ToM3 (X₁.1 * X₂.1 - X₂.1 * X₁.1) =
      pairSL2ToM3 X₁.1 * pairSL2ToM3 X₂.1 - pairSL2ToM3 X₂.1 * pairSL2ToM3 X₁.1
    have hbr : X₁.1 * X₂.1 - X₂.1 * X₁.1 =
        (2 * X₁.1 3 3 * X₂.1 3 0 - 2 * X₂.1 3 3 * X₁.1 3 0) •
          InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.pairCreation +
        (X₁.1 3 0 * X₂.1 0 3 - X₂.1 3 0 * X₁.1 0 3) •
          InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.gradingOperator +
        (2 * X₂.1 3 3 * X₁.1 0 3 - 2 * X₁.1 3 3 * X₂.1 0 3) •
          InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.pairAnnihilation := by
      conv_lhs => rw [h1, h2]
      exact pairSL2_bracket_formula (X₁.1 3 0) (X₁.1 3 3) (X₁.1 0 3)
        (X₂.1 3 0) (X₂.1 3 3) (X₂.1 0 3)
    have hrhs : pairSL2ToM3 X₁.1 * pairSL2ToM3 X₂.1 - pairSL2ToM3 X₂.1 * pairSL2ToM3 X₁.1 =
        (2 * X₁.1 3 3 * X₂.1 3 0 - 2 * X₂.1 3 3 * X₁.1 3 0) •
          InfoGeometry.SuperGrassmannian.SuperconformalOSpJordanPair.E_gen ℝ +
        (X₁.1 3 0 * X₂.1 0 3 - X₂.1 3 0 * X₁.1 0 3) •
          InfoGeometry.SuperGrassmannian.SuperconformalOSpJordanPair.H_gen ℝ +
        (2 * X₂.1 3 3 * X₁.1 0 3 - 2 * X₁.1 3 3 * X₂.1 0 3) •
          InfoGeometry.SuperGrassmannian.SuperconformalOSpJordanPair.F_gen ℝ :=
      ospEven_bracket_formula (X₁.1 3 0) (X₁.1 3 3) (X₁.1 0 3)
        (X₂.1 3 0) (X₂.1 3 3) (X₂.1 0 3)
    rw [hbr, hrhs, pairSL2ToM3_comb]
  left_inv X := by
    apply Subtype.ext
    conv_rhs => rw [mem_pairSL2Subalgebra_eq X.2]
    dsimp [m3ToPairSL2, pairSL2ToM3]
    rw [pairCreation_eq_mat4, pairAnnihilation_eq_mat4,
      InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.gradingOperator_eq_diagonal]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [InfoGeometry.SuperGrassmannian.SuperconformalOSpJordanPair.H_gen,
        InfoGeometry.SuperGrassmannian.SuperconformalOSpJordanPair.E_gen,
        InfoGeometry.SuperGrassmannian.SuperconformalOSpJordanPair.F_gen,
        InfoGeometry.SuperGrassmannian.SuperconformalOSpJordanPair.E]
  right_inv Y := by
    apply Subtype.ext
    conv_rhs => rw [mem_ospEvenLieSubalgebra_eq Y.2]
    dsimp [pairSL2ToM3, m3ToPairSL2]
    rw [pairCreation_eq_mat4, pairAnnihilation_eq_mat4,
      InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.gradingOperator_eq_diagonal]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [InfoGeometry.SuperGrassmannian.SuperconformalOSpJordanPair.H_gen,
        InfoGeometry.SuperGrassmannian.SuperconformalOSpJordanPair.E_gen,
        InfoGeometry.SuperGrassmannian.SuperconformalOSpJordanPair.F_gen,
        InfoGeometry.SuperGrassmannian.SuperconformalOSpJordanPair.E]

private def pairCreationSL2 :
    InfoGeometry.Physics.NuclearFiveGradeGeneratorRepresentation.pairSL2Subalgebra :=
  ⟨InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.pairCreation,
    LieSubalgebra.subset_lieSpan (by simp)⟩

private def gradingOpSL2 :
    InfoGeometry.Physics.NuclearFiveGradeGeneratorRepresentation.pairSL2Subalgebra :=
  ⟨InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.gradingOperator,
    LieSubalgebra.subset_lieSpan (by simp)⟩

private def pairAnnihilationSL2 :
    InfoGeometry.Physics.NuclearFiveGradeGeneratorRepresentation.pairSL2Subalgebra :=
  ⟨InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.pairAnnihilation,
    LieSubalgebra.subset_lieSpan (by simp)⟩

@[simp] theorem pairSL2ToOSpEvenEquiv_pairCreation :
    (pairSL2ToOSpEvenEquiv pairCreationSL2).1 =
      InfoGeometry.SuperGrassmannian.SuperconformalOSpJordanPair.E_gen ℝ := by
  change pairSL2ToM3 InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.pairCreation = _
  dsimp [pairSL2ToM3]
  rw [pairCreation_eq_mat4]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [InfoGeometry.SuperGrassmannian.SuperconformalOSpJordanPair.H_gen,
      InfoGeometry.SuperGrassmannian.SuperconformalOSpJordanPair.E_gen,
      InfoGeometry.SuperGrassmannian.SuperconformalOSpJordanPair.F_gen,
      InfoGeometry.SuperGrassmannian.SuperconformalOSpJordanPair.E]

@[simp] theorem pairSL2ToOSpEvenEquiv_gradingOperator :
    (pairSL2ToOSpEvenEquiv gradingOpSL2).1 =
      InfoGeometry.SuperGrassmannian.SuperconformalOSpJordanPair.H_gen ℝ := by
  change pairSL2ToM3 InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.gradingOperator = _
  dsimp [pairSL2ToM3]
  rw [InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.gradingOperator_eq_diagonal]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [InfoGeometry.SuperGrassmannian.SuperconformalOSpJordanPair.H_gen,
      InfoGeometry.SuperGrassmannian.SuperconformalOSpJordanPair.E_gen,
      InfoGeometry.SuperGrassmannian.SuperconformalOSpJordanPair.F_gen,
      InfoGeometry.SuperGrassmannian.SuperconformalOSpJordanPair.E]

@[simp] theorem pairSL2ToOSpEvenEquiv_pairAnnihilation :
    (pairSL2ToOSpEvenEquiv pairAnnihilationSL2).1 =
      InfoGeometry.SuperGrassmannian.SuperconformalOSpJordanPair.F_gen ℝ := by
  change pairSL2ToM3 InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.pairAnnihilation = _
  dsimp [pairSL2ToM3]
  rw [pairAnnihilation_eq_mat4]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [InfoGeometry.SuperGrassmannian.SuperconformalOSpJordanPair.H_gen,
      InfoGeometry.SuperGrassmannian.SuperconformalOSpJordanPair.E_gen,
      InfoGeometry.SuperGrassmannian.SuperconformalOSpJordanPair.F_gen,
      InfoGeometry.SuperGrassmannian.SuperconformalOSpJordanPair.E]

/-- `pairSL2ToOSpEvenEquiv` preserves all `sl₂` grades `k ∈ {-2, 0, +2}` and maps the CAR
pairing element `ε • gradingOperator + Δ • (pairCreation + pairAnnihilation)` onto `ospPairingElement ε Δ`
whose `evenCorner` is the exact nuclear `bdgBlock ε Δ`. -/
theorem pairSL2ToOSpEvenEquiv_preserves_grades_and_bdg
    (k : ℤ) (X : InfoGeometry.Physics.NuclearFiveGradeGeneratorRepresentation.pairSL2Subalgebra)
    (hX : InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.HasGrade k X.1)
    (ε Δ Eqp ω V C D : ℝ) :
    InfoGeometry.Algebra.FiveGradedIwasawa.InGrade
        (InfoGeometry.SuperGrassmannian.SuperconformalOSpJordanPair.H_gen ℝ)
        (k : ℝ) (pairSL2ToOSpEvenEquiv X).1 ∧
    (pairSL2ToOSpEvenEquiv
        (ε • gradingOpSL2 + Δ • (pairCreationSL2 + pairAnnihilationSL2))).1 =
      InfoGeometry.Nuclear.NuclearQuasiphononJordanPairBridge.ospPairingElement ε Δ ∧
    InfoGeometry.Nuclear.NuclearQuasiphononJordanPairBridge.evenCorner
        ((pairSL2ToOSpEvenEquiv
          (ε • gradingOpSL2 + Δ • (pairCreationSL2 + pairAnnihilationSL2))).1) =
      InfoGeometry.Physics.NuclearBdGTwoLevelExact.bdgBlock ε Δ ∧
    InfoGeometry.Physics.SolovievQPNMEigenproblem.qpnmMatrix Eqp ω V =
      InfoGeometry.Physics.NuclearBdGSolovievAffineBridge.solovievCenter Eqp ω • (1 : M₂) +
        InfoGeometry.Nuclear.NuclearQuasiphononJordanPairBridge.evenCorner
          ((pairSL2ToOSpEvenEquiv
            (InfoGeometry.Physics.NuclearBdGSolovievAffineBridge.solovievBdGCoordinate ω •
              gradingOpSL2 +
              V • (pairCreationSL2 + pairAnnihilationSL2))).1) ∧
    InfoGeometry.Physics.NuclearFiveGradeSolovievCommonCompression.compressedAction Eqp ω V ![C, D] =
      Matrix.mulVec
        (InfoGeometry.Physics.NuclearBdGSolovievAffineBridge.solovievCenter Eqp ω • (1 : M₂) +
          InfoGeometry.Nuclear.NuclearQuasiphononJordanPairBridge.evenCorner
            ((pairSL2ToOSpEvenEquiv
              (InfoGeometry.Physics.NuclearBdGSolovievAffineBridge.solovievBdGCoordinate ω •
                gradingOpSL2 +
                V • (pairCreationSL2 + pairAnnihilationSL2))).1))
        ![C, D] := by
  have hgrade : InfoGeometry.Algebra.FiveGradedIwasawa.InGrade
      (InfoGeometry.SuperGrassmannian.SuperconformalOSpJordanPair.H_gen ℝ)
      (k : ℝ) (pairSL2ToOSpEvenEquiv X).1 := by
    have hsub : ⁅gradingOpSL2, X⁆ = (k : ℝ) • X := by
      apply Subtype.ext
      exact hX
    have hlie := congrArg (fun u : InfoGeometry.Nuclear.NuclearQuasiphononJordanPairBridge.ospEvenLieSubalgebra => u.1)
      (LieEquiv.map_lie pairSL2ToOSpEvenEquiv gradingOpSL2 X).symm
    change ⁅(pairSL2ToOSpEvenEquiv gradingOpSL2).1, (pairSL2ToOSpEvenEquiv X).1⁆ =
        (pairSL2ToOSpEvenEquiv ⁅gradingOpSL2, X⁆).1 at hlie
    rw [pairSL2ToOSpEvenEquiv_gradingOperator] at hlie
    change ⁅InfoGeometry.SuperGrassmannian.SuperconformalOSpJordanPair.H_gen ℝ,
        (pairSL2ToOSpEvenEquiv X).1⁆ = _
    rw [hlie, hsub, map_smul]
    rfl
  have hcoe_add : ∀ A B : InfoGeometry.Nuclear.NuclearQuasiphononJordanPairBridge.ospEvenLieSubalgebra,
      (A + B).1 = A.1 + B.1 := fun _ _ => rfl
  have hcoe_smul : ∀ (r : ℝ) (A : InfoGeometry.Nuclear.NuclearQuasiphononJordanPairBridge.ospEvenLieSubalgebra),
      (r • A).1 = r • A.1 := fun _ _ => rfl
  have hosp : (pairSL2ToOSpEvenEquiv
        (ε • gradingOpSL2 + Δ • (pairCreationSL2 + pairAnnihilationSL2))).1 =
      InfoGeometry.Nuclear.NuclearQuasiphononJordanPairBridge.ospPairingElement ε Δ := by
    simp only [map_add, map_smul, hcoe_add, hcoe_smul,
      pairSL2ToOSpEvenEquiv_gradingOperator, pairSL2ToOSpEvenEquiv_pairCreation,
      pairSL2ToOSpEvenEquiv_pairAnnihilation]
    rfl
  refine ⟨hgrade, hosp, ?_, ?_, ?_⟩
  · rw [hosp]
    exact InfoGeometry.Nuclear.NuclearQuasiphononJordanPairBridge.evenCorner_ospPairingElement ε Δ
  · have hosp' : (pairSL2ToOSpEvenEquiv
        (InfoGeometry.Physics.NuclearBdGSolovievAffineBridge.solovievBdGCoordinate ω •
          gradingOpSL2 +
          V • (pairCreationSL2 + pairAnnihilationSL2))).1 =
        InfoGeometry.Nuclear.NuclearQuasiphononJordanPairBridge.ospPairingElement
          (InfoGeometry.Physics.NuclearBdGSolovievAffineBridge.solovievBdGCoordinate ω) V := by
      simp only [map_add, map_smul, hcoe_add, hcoe_smul,
        pairSL2ToOSpEvenEquiv_gradingOperator, pairSL2ToOSpEvenEquiv_pairCreation,
        pairSL2ToOSpEvenEquiv_pairAnnihilation]
      rfl
    rw [hosp']
    exact InfoGeometry.Nuclear.NuclearQuasiphononJordanPairBridge.qpnmMatrix_eq_center_add_ospCorner
      Eqp ω V
  · have hosp' : (pairSL2ToOSpEvenEquiv
        (InfoGeometry.Physics.NuclearBdGSolovievAffineBridge.solovievBdGCoordinate ω •
          gradingOpSL2 +
          V • (pairCreationSL2 + pairAnnihilationSL2))).1 =
        InfoGeometry.Nuclear.NuclearQuasiphononJordanPairBridge.ospPairingElement
          (InfoGeometry.Physics.NuclearBdGSolovievAffineBridge.solovievBdGCoordinate ω) V := by
      simp only [map_add, map_smul, hcoe_add, hcoe_smul,
        pairSL2ToOSpEvenEquiv_gradingOperator, pairSL2ToOSpEvenEquiv_pairCreation,
        pairSL2ToOSpEvenEquiv_pairAnnihilation]
      rfl
    rw [hosp']
    exact InfoGeometry.Nuclear.NuclearQuasiphononJordanPairBridge.compressedAction_eq_center_add_ospCorner
      Eqp ω V C D

/-- Identification of `NuclearQuasiphononKreinSUSY` supercharges and SUSY Hamiltonian with
`NuclearQuasiphononSuperGrassmannian` and Krein modular supertrace preservation. -/
theorem kreinSUSY_superGrassmannian_compatibility
    {ι₀ ι₁ : Type*} [DecidableEq ι₀] [Fintype ι₀] [DecidableEq ι₁] [Fintype ι₁]
    (V : Matrix ι₀ ι₁ ℝ) (t : ℝ) (M : Matrix (ι₀ ⊕ ι₁) (ι₀ ⊕ ι₁) ℂ)
    (Eqp ω c : ℝ) :
    InfoGeometry.Nuclear.NuclearQuasiphononKreinSUSY.superchargeQ V =
      InfoGeometry.SuperGrassmannian.NuclearQuasiphononSuperGrassmannian.susyQ V ∧
    InfoGeometry.Nuclear.NuclearQuasiphononKreinSUSY.superchargeQ_dag V =
      InfoGeometry.SuperGrassmannian.NuclearQuasiphononSuperGrassmannian.susyQ_dag V ∧
    InfoGeometry.Nuclear.NuclearQuasiphononKreinSUSY.susyHamiltonian V =
      InfoGeometry.SuperGrassmannian.NuclearQuasiphononSuperGrassmannian.susyH V ∧
    (InfoGeometry.Nuclear.NuclearQuasiphononKreinSUSY.kreinMetric ι₀ ι₀ ℝ *
        InfoGeometry.Nuclear.NuclearQuasiphononKreinSUSY.sheetSwap ι₀ ℝ +
      InfoGeometry.Nuclear.NuclearQuasiphononKreinSUSY.sheetSwap ι₀ ℝ *
        InfoGeometry.Nuclear.NuclearQuasiphononKreinSUSY.kreinMetric ι₀ ι₀ ℝ = 0) ∧
    InfoGeometry.SuperGrassmannian.NuclearQuasiphononSuperGrassmannian.superTrace M =
      (InfoGeometry.Nuclear.NuclearQuasiphononKreinSUSY.kreinMetric ι₀ ι₁ ℂ * M).trace ∧
    InfoGeometry.SuperGrassmannian.NuclearQuasiphononSuperGrassmannian.superTrace
      ((InfoGeometry.Nuclear.NuclearQuasiphononKreinSUSY.sumMatEquiv ι₀ ι₁).symm
        (InfoGeometry.Canonical.ComplexMatrixModularFlowAndCStarPolar.matrixModularFlow
          (InfoGeometry.Nuclear.NuclearQuasiphononKreinSUSY.susyH_fin V)
          (InfoGeometry.Nuclear.NuclearQuasiphononKreinSUSY.susyH_fin_isHermitian V)
          t (InfoGeometry.Nuclear.NuclearQuasiphononKreinSUSY.sumMatEquiv ι₀ ι₁ M))) =
      InfoGeometry.SuperGrassmannian.NuclearQuasiphononSuperGrassmannian.superTrace M ∧
    InfoGeometry.Nuclear.NuclearQuasiphononKreinSUSY.qpnmMatrix Eqp ω c =
      InfoGeometry.Nuclear.NuclearQuasiphononKreinSUSY.solovievCenter Eqp ω •
          (1 : Matrix (Fin 2) (Fin 2) ℝ) +
        InfoGeometry.Nuclear.NuclearQuasiphononKreinSUSY.bdgBlock (-⅟(2 : ℝ) * ω) c :=
  ⟨rfl, rfl, rfl,
   InfoGeometry.Nuclear.NuclearQuasiphononKreinSUSY.krein_sheetSwap_anticomm ι₀ ℝ,
   InfoGeometry.Nuclear.NuclearQuasiphononKreinSUSY.superTrace_eq_trace_kreinMetric M,
   InfoGeometry.Nuclear.NuclearQuasiphononKreinSUSY.matrixModularFlow_susyH_fin_preserves_superTrace V t M,
   InfoGeometry.Nuclear.NuclearQuasiphononKreinSUSY.qpnm_affine_bdg Eqp ω c⟩

/-- `H_gen ℝ = diag(1, 0, -1)` in `M₃(ℝ)` is tripotent (`H³ = H`) and coincides with
`FiveGradedLieSuperalgebra.H_grading`. -/
theorem hGen_eq_H_grading_and_cube :
    InfoGeometry.SuperGrassmannian.SuperconformalOSpJordanPair.H_gen ℝ =
      InfoGeometry.SuperGrassmannian.FiveGradedLieSuperalgebra.H_grading ∧
    InfoGeometry.SuperGrassmannian.SuperconformalOSpJordanPair.H_gen ℝ *
      InfoGeometry.SuperGrassmannian.SuperconformalOSpJordanPair.H_gen ℝ *
      InfoGeometry.SuperGrassmannian.SuperconformalOSpJordanPair.H_gen ℝ =
      InfoGeometry.SuperGrassmannian.SuperconformalOSpJordanPair.H_gen ℝ := by
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [InfoGeometry.SuperGrassmannian.SuperconformalOSpJordanPair.H_gen,
        InfoGeometry.SuperGrassmannian.SuperconformalOSpJordanPair.E,
        InfoGeometry.SuperGrassmannian.FiveGradedLieSuperalgebra.H_grading]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [InfoGeometry.SuperGrassmannian.SuperconformalOSpJordanPair.H_gen,
        InfoGeometry.SuperGrassmannian.SuperconformalOSpJordanPair.E,
        Matrix.mul_apply, Fin.sum_univ_three]

/-- `H_gen ℝ` induces a genuine `FiveGradedIwasawa.IsFiveGraded` 5-grading on `M₃(ℝ)`. -/
instance instIsFiveGraded_hGen_M3 :
    InfoGeometry.Algebra.FiveGradedIwasawa.IsFiveGraded
      (InfoGeometry.SuperGrassmannian.SuperconformalOSpJordanPair.H_gen ℝ) :=
  InfoGeometry.Algebra.CuntzMatrixUnitFiveGradingBridge.isFiveGraded_of_tripotent
    (A := M₃) hGen_eq_H_grading_and_cube.2

section CuntzBridge

open scoped InfoGeometry.Algebra.CuntzMatrixUnitFiveGradingBridge.ScopedCuntzInstances

/-- Index permutation `(0, 1, 2) ↦ (0, 2, 1)` aligning Cuntz color weights `(1, -1, 0)` with
`H_gen ℝ = diag(1, 0, -1)`. -/
def cuntzPerm : Fin 3 ≃ Fin 3 where
  toFun
    | 0 => 0
    | 1 => 2
    | 2 => 1
  invFun
    | 0 => 0
    | 1 => 2
    | 2 => 1
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

private def cuntzHopBasis : Fin 3 × Fin 3 →
    InfoGeometry.Algebra.CuntzMatrixUnitFiveGradingBridge.matrixUnitLieSubalgebra :=
  fun p => InfoGeometry.Algebra.CuntzMatrixUnitFiveGradingBridge.hopSub p.1 p.2

private theorem hop_cuntz_linear_decomp
    (x : InfoGeometry.Algebra.CuntzMatrixUnitFiveGradingBridge.matrixUnitLieSubalgebra) :
    ∃ c : Fin 3 × Fin 3 → ℝ,
      (x : InfoGeometry.Algebra.CuntzMatrixUnitFiveGradingBridge.Cuntz3) =
        ∑ p : Fin 3 × Fin 3, c p •
          InfoGeometry.Algebra.CuntzMatrixUnitFiveGradingBridge.hop p.1 p.2 := by
  have hx : (x : InfoGeometry.Algebra.CuntzMatrixUnitFiveGradingBridge.Cuntz3) ∈
      Submodule.span ℝ (Set.range fun p : Fin 3 × Fin 3 =>
        InfoGeometry.Algebra.CuntzMatrixUnitFiveGradingBridge.hop p.1 p.2) := x.2
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
  · rintro _ ⟨p, rfl⟩
    refine ⟨fun q => if q = p then 1 else 0, ?_⟩
    simp only [ite_smul]
    rw [Finset.sum_eq_single p]
    · simp only [↓reduceIte]
      exact (one_smul ℝ _).symm
    · intro q _ hqp
      simp only [hqp, ↓reduceIte]
      exact zero_smul ℝ _
    · intro hp
      exact False.elim (hp (Finset.mem_univ p))
  · refine ⟨fun _ => 0, ?_⟩
    exact (Finset.sum_eq_zero (fun p _ => zero_smul ℝ _)).symm
  · rintro a b _ _ ⟨ca, ha⟩ ⟨cb, hb⟩
    refine ⟨fun p => ca p + cb p, ?_⟩
    rw [ha, hb, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro p _
    exact (add_smul (ca p) (cb p) _).symm
  · rintro r a _ ⟨ca, ha⟩
    refine ⟨fun p => r * ca p, ?_⟩
    rw [ha, Finset.smul_sum]
    refine Finset.sum_congr rfl ?_
    intro p _
    exact smul_smul r (ca p) _

private noncomputable def shift3S (i : Fin 3) : Module.End ℂ (ℕ → ℂ) where
  toFun f n := if n % 3 = i.val then f (n / 3) else 0
  map_add' f g := by ext n; dsimp; split_ifs <;> simp
  map_smul' c f := by ext n; dsimp; split_ifs <;> simp

private noncomputable def shift3Sdag (i : Fin 3) : Module.End ℂ (ℕ → ℂ) where
  toFun f m := f (3 * m + i.val)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem shift3_orth (i j : Fin 3) :
    shift3Sdag i * shift3S j = if i = j then 1 else 0 := by
  ext f m
  change (if (3 * m + i.val) % 3 = j.val then f ((3 * m + i.val) / 3) else 0) = _
  have hmod : (3 * m + i.val) % 3 = i.val := by omega
  have hdiv : (3 * m + i.val) / 3 = m := by omega
  rw [hmod, hdiv]
  by_cases hij : i = j
  · subst hij; simp
  · have hval : i.val ≠ j.val := fun h => hij (Fin.ext h)
    simp [hij, hval]

private theorem shift3_partition :
    (∑ i : Fin 3, shift3S i * shift3Sdag i) = 1 := by
  ext f n
  simp only [Module.End.one_apply, shift3S, shift3Sdag, Fin.sum_univ_three]
  have hmod : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
  rcases hmod with h0 | h1 | h2
  · simp [h0]; exact congrArg f (by omega)
  · simp [h1]; exact congrArg f (by omega)
  · simp [h2]; exact congrArg f (by omega)

private theorem cuntz3_hop00_ne_zero :
    InfoGeometry.Algebra.CuntzMatrixUnitFiveGradingBridge.hop 0 0 ≠ 0 := by
  let rep : InfoGeometry.Algebra.CuntzTensorQuotient.CuntzAlg 3 →ₐ[ℂ] Module.End ℂ (ℕ → ℂ) :=
    InfoGeometry.Algebra.CuntzTensorQuotient.lift 3 shift3S shift3Sdag shift3_orth shift3_partition
  intro h0
  have hsum1 : (∑ k : Fin 3, InfoGeometry.Algebra.CuntzMatrixUnitFiveGradingBridge.hop k k) = 1 :=
    InfoGeometry.Algebra.CuntzMatrixUnits.matrix_unit_sum_diag_eq_one 3
  have h00_mul : ∀ k : Fin 3,
      InfoGeometry.Algebra.CuntzMatrixUnitFiveGradingBridge.hop k 0 *
        InfoGeometry.Algebra.CuntzMatrixUnitFiveGradingBridge.hop 0 0 *
        InfoGeometry.Algebra.CuntzMatrixUnitFiveGradingBridge.hop 0 k =
      InfoGeometry.Algebra.CuntzMatrixUnitFiveGradingBridge.hop k k := by
    intro k
    rw [InfoGeometry.Algebra.CuntzMatrixUnitFiveGradingBridge.hop_mul_hop]
    simp [InfoGeometry.Algebra.CuntzMatrixUnitFiveGradingBridge.hop_mul_hop]
  have hall0 : ∀ k : Fin 3, InfoGeometry.Algebra.CuntzMatrixUnitFiveGradingBridge.hop k k = 0 := by
    intro k
    rw [← h00_mul k, h0, mul_zero, zero_mul]
  have h10 : (1 : InfoGeometry.Algebra.CuntzMatrixUnitFiveGradingBridge.Cuntz3) = 0 := by
    rw [← hsum1]
    exact Finset.sum_eq_zero (fun k _ => hall0 k)
  have hrep := congrArg rep h10
  rw [map_one, map_zero] at hrep
  have hv := congrArg (fun T : Module.End ℂ (ℕ → ℂ) => T (fun _ => (1 : ℂ)) 0) hrep
  simp at hv

private noncomputable def cuntzHopRealBasis :
    Module.Basis (Fin 3 × Fin 3) ℝ
      InfoGeometry.Algebra.CuntzMatrixUnitFiveGradingBridge.matrixUnitLieSubalgebra := by
  let V := InfoGeometry.Algebra.CuntzMatrixUnitFiveGradingBridge.matrixUnitLieSubalgebra
  have hli : LinearIndependent ℝ cuntzHopBasis := by
    rw [Fintype.linearIndependent_iff]
    intro c hc i
    have hcoe : ∀ f : Fin 3 × Fin 3 → V,
        ((∑ p : Fin 3 × Fin 3, f p : V) : InfoGeometry.Algebra.CuntzMatrixUnitFiveGradingBridge.Cuntz3) =
          ∑ p : Fin 3 × Fin 3, (f p : InfoGeometry.Algebra.CuntzMatrixUnitFiveGradingBridge.Cuntz3) :=
      fun f => AddSubmonoidClass.coe_finsetSum (S := V) f Finset.univ
    have hcoeff : ∑ p : Fin 3 × Fin 3, (c p : ℂ) •
        InfoGeometry.Algebra.CuntzMatrixUnitFiveGradingBridge.hop p.1 p.2 = 0 := by
      have hcval := congrArg (fun u : V => (u : InfoGeometry.Algebra.CuntzMatrixUnitFiveGradingBridge.Cuntz3)) hc
      rw [hcoe] at hcval
      simp only [cuntzHopBasis, SetLike.val_smul] at hcval
      exact hcval
    have hzero := congrArg (fun z : InfoGeometry.Algebra.CuntzMatrixUnitFiveGradingBridge.Cuntz3 =>
      InfoGeometry.Algebra.CuntzMatrixUnitFiveGradingBridge.hop 0 i.1 * z *
        InfoGeometry.Algebra.CuntzMatrixUnitFiveGradingBridge.hop i.2 0) hcoeff
    simp only [Finset.mul_sum, Finset.sum_mul, mul_zero, smul_mul_assoc, mul_smul_comm] at hzero
    have hterm : ∀ p : Fin 3 × Fin 3,
        (c p : ℂ) • (InfoGeometry.Algebra.CuntzMatrixUnitFiveGradingBridge.hop 0 i.1 *
          InfoGeometry.Algebra.CuntzMatrixUnitFiveGradingBridge.hop p.1 p.2 *
          InfoGeometry.Algebra.CuntzMatrixUnitFiveGradingBridge.hop i.2 0) =
        if p = i then (c i : ℂ) • InfoGeometry.Algebra.CuntzMatrixUnitFiveGradingBridge.hop 0 0 else 0 := by
      intro p
      by_cases hp : p = i
      · subst hp
        rw [InfoGeometry.Algebra.CuntzMatrixUnitFiveGradingBridge.hop_mul_hop]
        simp [InfoGeometry.Algebra.CuntzMatrixUnitFiveGradingBridge.hop_mul_hop]
      · rw [InfoGeometry.Algebra.CuntzMatrixUnitFiveGradingBridge.hop_mul_hop]
        split_ifs with h1
        · rw [InfoGeometry.Algebra.CuntzMatrixUnitFiveGradingBridge.hop_mul_hop]
          split_ifs with h2
          · exact False.elim (hp (Prod.ext h1.symm h2))
          · simp
        · simp
    simp only [hterm, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte] at hzero
    rw [zero_mul] at hzero
    rcases smul_eq_zero.mp hzero with hci | hhop0
    · exact Complex.ofReal_eq_zero.mp hci
    · exact False.elim (cuntz3_hop00_ne_zero hhop0)
  have hsp : ⊤ ≤ Submodule.span ℝ (Set.range cuntzHopBasis) := by
    intro x _
    obtain ⟨c, hc⟩ := hop_cuntz_linear_decomp x
    have hx_eq : x = ∑ p : Fin 3 × Fin 3, c p • cuntzHopBasis p := by
      apply Subtype.ext
      have hcoe : ((∑ p : Fin 3 × Fin 3, c p • cuntzHopBasis p : V) :
          InfoGeometry.Algebra.CuntzMatrixUnitFiveGradingBridge.Cuntz3) =
          ∑ p : Fin 3 × Fin 3, c p •
            InfoGeometry.Algebra.CuntzMatrixUnitFiveGradingBridge.hop p.1 p.2 := by
        rw [AddSubmonoidClass.coe_finsetSum]
        rfl
      rw [hcoe]
      exact hc
    rw [hx_eq]
    exact Submodule.sum_mem _ (fun p _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨p, rfl⟩))
  exact Module.Basis.mk hli hsp

private noncomputable def cuntzLinearToM3 :
    InfoGeometry.Algebra.CuntzMatrixUnitFiveGradingBridge.matrixUnitLieSubalgebra →ₗ[ℝ] M₃ :=
  cuntzHopRealBasis.constr ℝ (fun p =>
    InfoGeometry.SuperGrassmannian.SuperconformalOSpJordanPair.E (cuntzPerm p.1) (cuntzPerm p.2))

@[simp] private theorem cuntzLinearToM3_hopSub (i j : Fin 3) :
    cuntzLinearToM3 (InfoGeometry.Algebra.CuntzMatrixUnitFiveGradingBridge.hopSub i j) =
      InfoGeometry.SuperGrassmannian.SuperconformalOSpJordanPair.E (cuntzPerm i) (cuntzPerm j) := by
  have hbasis : cuntzHopRealBasis (i, j) =
      InfoGeometry.Algebra.CuntzMatrixUnitFiveGradingBridge.hopSub i j := by
    dsimp [cuntzHopRealBasis]
    rw [Module.Basis.coe_mk]
    rfl
  rw [← hbasis, cuntzLinearToM3, Module.Basis.constr_basis]

/-- Exact grade-preserving `ℝ`-Lie algebra embedding `matrixUnitLieSubalgebra →ₗ⁅ℝ⁆ M₃(ℝ)`
sending `hopSub i j ↦ E (cuntzPerm i) (cuntzPerm j)` and `gradingOpSub ↦ H_gen ℝ`. -/
def cuntzMatUnitToM3 :
    InfoGeometry.Algebra.CuntzMatrixUnitFiveGradingBridge.matrixUnitLieSubalgebra →ₗ⁅ℝ⁆ M₃ where
  toLinearMap := cuntzLinearToM3
  map_lie' {x y} := by
    obtain ⟨cx, hcx⟩ := hop_cuntz_linear_decomp x
    obtain ⟨cy, hcy⟩ := hop_cuntz_linear_decomp y
    have hcoe : ∀ f : Fin 3 × Fin 3 → ℝ,
        ((∑ p : Fin 3 × Fin 3, f p •
          InfoGeometry.Algebra.CuntzMatrixUnitFiveGradingBridge.hopSub p.1 p.2 :
            InfoGeometry.Algebra.CuntzMatrixUnitFiveGradingBridge.matrixUnitLieSubalgebra) :
          InfoGeometry.Algebra.CuntzMatrixUnitFiveGradingBridge.Cuntz3) =
          ∑ p : Fin 3 × Fin 3, f p •
            InfoGeometry.Algebra.CuntzMatrixUnitFiveGradingBridge.hop p.1 p.2 := by
      intro f
      rw [AddSubmonoidClass.coe_finsetSum]
      rfl
    have hx : x = ∑ p : Fin 3 × Fin 3, cx p •
        InfoGeometry.Algebra.CuntzMatrixUnitFiveGradingBridge.hopSub p.1 p.2 := by
      apply Subtype.ext; rw [hcoe]; exact hcx
    have hy : y = ∑ q : Fin 3 × Fin 3, cy q •
        InfoGeometry.Algebra.CuntzMatrixUnitFiveGradingBridge.hopSub q.1 q.2 := by
      apply Subtype.ext; rw [hcoe]; exact hcy
    have hhop : ∀ p q : Fin 3 × Fin 3,
        cuntzLinearToM3
          ⁅InfoGeometry.Algebra.CuntzMatrixUnitFiveGradingBridge.hopSub p.1 p.2,
            InfoGeometry.Algebra.CuntzMatrixUnitFiveGradingBridge.hopSub q.1 q.2⁆ =
        ⁅cuntzLinearToM3 (InfoGeometry.Algebra.CuntzMatrixUnitFiveGradingBridge.hopSub p.1 p.2),
          cuntzLinearToM3 (InfoGeometry.Algebra.CuntzMatrixUnitFiveGradingBridge.hopSub q.1 q.2)⁆ := by
      intro p q
      have hbr : ⁅InfoGeometry.Algebra.CuntzMatrixUnitFiveGradingBridge.hopSub p.1 p.2,
            InfoGeometry.Algebra.CuntzMatrixUnitFiveGradingBridge.hopSub q.1 q.2⁆ =
          (if p.2 = q.1 then
            InfoGeometry.Algebra.CuntzMatrixUnitFiveGradingBridge.hopSub p.1 q.2 else 0) -
          (if q.2 = p.1 then
            InfoGeometry.Algebra.CuntzMatrixUnitFiveGradingBridge.hopSub q.1 p.2 else 0) := by
        apply Subtype.ext
        change InfoGeometry.Algebra.CuntzMatrixUnitFiveGradingBridge.hop p.1 p.2 *
            InfoGeometry.Algebra.CuntzMatrixUnitFiveGradingBridge.hop q.1 q.2 -
          InfoGeometry.Algebra.CuntzMatrixUnitFiveGradingBridge.hop q.1 q.2 *
            InfoGeometry.Algebra.CuntzMatrixUnitFiveGradingBridge.hop p.1 p.2 = _
        rw [InfoGeometry.Algebra.CuntzMatrixUnitFiveGradingBridge.hop_mul_hop,
          InfoGeometry.Algebra.CuntzMatrixUnitFiveGradingBridge.hop_mul_hop]
        congr 1 <;> split_ifs <;> rfl
      change cuntzLinearToM3
          ⁅InfoGeometry.Algebra.CuntzMatrixUnitFiveGradingBridge.hopSub p.1 p.2,
            InfoGeometry.Algebra.CuntzMatrixUnitFiveGradingBridge.hopSub q.1 q.2⁆ =
        cuntzLinearToM3 (InfoGeometry.Algebra.CuntzMatrixUnitFiveGradingBridge.hopSub p.1 p.2) *
          cuntzLinearToM3 (InfoGeometry.Algebra.CuntzMatrixUnitFiveGradingBridge.hopSub q.1 q.2) -
        cuntzLinearToM3 (InfoGeometry.Algebra.CuntzMatrixUnitFiveGradingBridge.hopSub q.1 q.2) *
          cuntzLinearToM3 (InfoGeometry.Algebra.CuntzMatrixUnitFiveGradingBridge.hopSub p.1 p.2)
      rw [hbr, map_sub, cuntzLinearToM3_hopSub, cuntzLinearToM3_hopSub]
      have hif1 : cuntzLinearToM3 (if p.2 = q.1 then
          InfoGeometry.Algebra.CuntzMatrixUnitFiveGradingBridge.hopSub p.1 q.2 else 0) =
          if p.2 = q.1 then
            InfoGeometry.SuperGrassmannian.SuperconformalOSpJordanPair.E (cuntzPerm p.1) (cuntzPerm q.2)
          else 0 := by
        split_ifs
        · exact cuntzLinearToM3_hopSub p.1 q.2
        · exact map_zero cuntzLinearToM3
      have hif2 : cuntzLinearToM3 (if q.2 = p.1 then
          InfoGeometry.Algebra.CuntzMatrixUnitFiveGradingBridge.hopSub q.1 p.2 else 0) =
          if q.2 = p.1 then
            InfoGeometry.SuperGrassmannian.SuperconformalOSpJordanPair.E (cuntzPerm q.1) (cuntzPerm p.2)
          else 0 := by
        split_ifs
        · exact cuntzLinearToM3_hopSub q.1 p.2
        · exact map_zero cuntzLinearToM3
      rw [hif1, hif2]
      ext a b
      simp only [Matrix.sub_apply, Matrix.mul_apply,
        InfoGeometry.SuperGrassmannian.SuperconformalOSpJordanPair.E, Matrix.of_apply]
      have hterm1 : (∑ k : Fin 3,
          (if a = cuntzPerm p.1 ∧ k = cuntzPerm p.2 then (1 : ℝ) else 0) *
          (if k = cuntzPerm q.1 ∧ b = cuntzPerm q.2 then (1 : ℝ) else 0)) =
          if p.2 = q.1 then (if a = cuntzPerm p.1 ∧ b = cuntzPerm q.2 then 1 else 0) else 0 := by
        by_cases hpq : p.2 = q.1
        · simp only [hpq, ↓reduceIte]
          rw [Finset.sum_eq_single (cuntzPerm q.1)]
          · by_cases ha : a = cuntzPerm p.1 <;> by_cases hb : b = cuntzPerm q.2 <;> simp [ha, hb]
          · intro k _ hk; simp [hk]
          · intro hk; exact False.elim (hk (Finset.mem_univ _))
        · simp only [hpq, ↓reduceIte]
          refine Finset.sum_eq_zero (fun k _ => ?_)
          by_cases hk : k = cuntzPerm p.2
          · subst hk
            have hne : cuntzPerm p.2 ≠ cuntzPerm q.1 := fun h => hpq (cuntzPerm.injective h)
            simp [hne]
          · simp [hk]
      have hterm2 : (∑ k : Fin 3,
          (if a = cuntzPerm q.1 ∧ k = cuntzPerm q.2 then (1 : ℝ) else 0) *
          (if k = cuntzPerm p.1 ∧ b = cuntzPerm p.2 then (1 : ℝ) else 0)) =
          if q.2 = p.1 then (if a = cuntzPerm q.1 ∧ b = cuntzPerm p.2 then 1 else 0) else 0 := by
        by_cases hqp : q.2 = p.1
        · simp only [hqp, ↓reduceIte]
          rw [Finset.sum_eq_single (cuntzPerm p.1)]
          · by_cases ha : a = cuntzPerm q.1 <;> by_cases hb : b = cuntzPerm p.2 <;> simp [ha, hb]
          · intro k _ hk; simp [hk]
          · intro hk; exact False.elim (hk (Finset.mem_univ _))
        · simp only [hqp, ↓reduceIte]
          refine Finset.sum_eq_zero (fun k _ => ?_)
          by_cases hk : k = cuntzPerm q.2
          · subst hk
            have hne : cuntzPerm q.2 ≠ cuntzPerm p.1 := fun h => hqp (cuntzPerm.injective h)
            simp [hne]
          · simp [hk]
      rw [hterm1, hterm2]
      by_cases h1 : p.2 = q.1 <;> by_cases h2 : q.2 = p.1 <;> simp [h1, h2]
    change cuntzLinearToM3 ⁅x, y⁆ = ⁅cuntzLinearToM3 x, cuntzLinearToM3 y⁆
    rw [hx, hy]
    simp only [sum_lie, lie_sum, smul_lie, lie_smul, map_sum, map_smul, hhop]

@[simp] theorem cuntzMatUnitToM3_hopSub (i j : Fin 3) :
    cuntzMatUnitToM3 (InfoGeometry.Algebra.CuntzMatrixUnitFiveGradingBridge.hopSub i j) =
      InfoGeometry.SuperGrassmannian.SuperconformalOSpJordanPair.E (cuntzPerm i) (cuntzPerm j) :=
  cuntzLinearToM3_hopSub i j

theorem cuntzMatUnitToM3_gradingOp :
    cuntzMatUnitToM3 InfoGeometry.Algebra.CuntzMatrixUnitFiveGradingBridge.gradingOpSub =
      InfoGeometry.SuperGrassmannian.SuperconformalOSpJordanPair.H_gen ℝ := by
  have hsub : InfoGeometry.Algebra.CuntzMatrixUnitFiveGradingBridge.gradingOpSub =
      InfoGeometry.Algebra.CuntzMatrixUnitFiveGradingBridge.hopSub 0 0 -
      InfoGeometry.Algebra.CuntzMatrixUnitFiveGradingBridge.hopSub 1 1 :=
    Subtype.ext rfl
  rw [hsub, map_sub, cuntzMatUnitToM3_hopSub, cuntzMatUnitToM3_hopSub]
  rfl

theorem cuntzMatUnitToM3_preserves_grade (k : ℝ)
    (x : InfoGeometry.Algebra.CuntzMatrixUnitFiveGradingBridge.matrixUnitLieSubalgebra)
    (hx : InfoGeometry.Algebra.FiveGradedIwasawa.InGrade
      InfoGeometry.Algebra.CuntzMatrixUnitFiveGradingBridge.gradingOpSub k x) :
    InfoGeometry.Algebra.FiveGradedIwasawa.InGrade
      (InfoGeometry.SuperGrassmannian.SuperconformalOSpJordanPair.H_gen ℝ)
      k (cuntzMatUnitToM3 x) := by
  unfold InfoGeometry.Algebra.FiveGradedIwasawa.InGrade at hx ⊢
  rw [← cuntzMatUnitToM3_gradingOp, ← cuntzMatUnitToM3.map_lie, hx, map_smul]

theorem cuntzMatUnitToM3_injective : Function.Injective cuntzMatUnitToM3 := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨c, hc⟩ := hop_cuntz_linear_decomp x
  have hcoe : ((∑ p : Fin 3 × Fin 3, c p •
        InfoGeometry.Algebra.CuntzMatrixUnitFiveGradingBridge.hopSub p.1 p.2 :
          InfoGeometry.Algebra.CuntzMatrixUnitFiveGradingBridge.matrixUnitLieSubalgebra) :
        InfoGeometry.Algebra.CuntzMatrixUnitFiveGradingBridge.Cuntz3) =
      ∑ p : Fin 3 × Fin 3, c p •
        InfoGeometry.Algebra.CuntzMatrixUnitFiveGradingBridge.hop p.1 p.2 := by
    rw [AddSubmonoidClass.coe_finsetSum]
    rfl
  have hxe : x = ∑ p : Fin 3 × Fin 3, c p •
      InfoGeometry.Algebra.CuntzMatrixUnitFiveGradingBridge.hopSub p.1 p.2 := by
    apply Subtype.ext; rw [hcoe]; exact hc
  rw [hxe, map_sum] at hx
  simp_rw [map_smul, cuntzMatUnitToM3_hopSub] at hx
  have hc0 : ∀ p : Fin 3 × Fin 3, c p = 0 := by
    intro p
    have hij := congr_fun (congr_fun hx (cuntzPerm p.1)) (cuntzPerm p.2)
    simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply,
      InfoGeometry.SuperGrassmannian.SuperconformalOSpJordanPair.E, Matrix.of_apply,
      Equiv.apply_eq_iff_eq] at hij
    have hsum : (∑ q : Fin 3 × Fin 3,
        c q * (if p.1 = q.1 ∧ p.2 = q.2 then (1 : ℝ) else 0)) =
        c p := by
      have hterm : ∀ q : Fin 3 × Fin 3,
          c q * (if p.1 = q.1 ∧ p.2 = q.2 then (1 : ℝ) else 0) =
            if q = p then c p else 0 := by
        intro q
        by_cases hqp : q = p
        · subst hqp; simp
        · have hne : ¬(p.1 = q.1 ∧ p.2 = q.2) := fun ⟨h1, h2⟩ =>
            hqp (Prod.ext h1.symm h2.symm)
          simp only [hne, ↓reduceIte, mul_zero, hqp]
      simp only [hterm, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    rw [hsum] at hij
    exact hij
  rw [hxe]
  exact Finset.sum_eq_zero (fun p _ => by rw [hc0 p, zero_smul])

end CuntzBridge

/-!
## Section 4: `(Fin 2 ⊕ Fin 3)` Super-Grassmannian ↔ `SuperBlock23` ↔ `Z2Z2ColorGrade` / `OpZornMatrix ℝ` / `Cl55` / Koszul-Shirokov 5-Grading
-/

/-- Embed `SuperBlock23 K` into `Matrix (Fin 2 ⊕ Fin 3) (Fin 2 ⊕ Fin 3) K`. -/
def superBlock23ToMatrix {K : Type*} (M : InfoGeometry.Synthesis.SuperGrassmannianFiveGradedColorSupersymmetrySynthesis.SuperBlock23 K) :
    Matrix (Fin 2 ⊕ Fin 3) (Fin 2 ⊕ Fin 3) K :=
  Matrix.fromBlocks M.A M.B M.C M.D

/-- Extract `SuperBlock23 K` from `Matrix (Fin 2 ⊕ Fin 3) (Fin 2 ⊕ Fin 3) K`. -/
def matrixToSuperBlock23 {K : Type*} (M : Matrix (Fin 2 ⊕ Fin 3) (Fin 2 ⊕ Fin 3) K) :
    InfoGeometry.Synthesis.SuperGrassmannianFiveGradedColorSupersymmetrySynthesis.SuperBlock23 K where
  A := M.toBlocks₁₁
  B := M.toBlocks₁₂
  C := M.toBlocks₂₁
  D := M.toBlocks₂₂

/-- Canonical equivalence `SuperBlock23 K ≃ Matrix (Fin 2 ⊕ Fin 3) (Fin 2 ⊕ Fin 3) K`. -/
def superBlock23MatrixEquiv (K : Type*) :
    InfoGeometry.Synthesis.SuperGrassmannianFiveGradedColorSupersymmetrySynthesis.SuperBlock23 K ≃
      Matrix (Fin 2 ⊕ Fin 3) (Fin 2 ⊕ Fin 3) K where
  toFun := superBlock23ToMatrix
  invFun := matrixToSuperBlock23
  left_inv M := by
    ext i j <;> rfl
  right_inv M := Matrix.fromBlocks_toBlocks M

theorem superBlock23ToMatrix_mul {K : Type*} [CommRing K]
    (M₁ M₂ : InfoGeometry.Synthesis.SuperGrassmannianFiveGradedColorSupersymmetrySynthesis.SuperBlock23 K) :
    superBlock23ToMatrix (M₁ * M₂) = superBlock23ToMatrix M₁ * superBlock23ToMatrix M₂ := by
  dsimp [superBlock23ToMatrix]
  rw [Matrix.fromBlocks_multiply]
  rfl

theorem superBlock23_superGrassmannian_compatibility
    (M : InfoGeometry.Synthesis.SuperGrassmannianFiveGradedColorSupersymmetrySynthesis.SuperBlock23 ℝ)
    (hD : M.D.det ≠ 0) (σ : ℝ)
    (A : Matrix (Fin 2) (Fin 2) ℝ) (B : Matrix (Fin 2) (Fin 3) ℝ)
    (C : Matrix (Fin 3) (Fin 2) ℝ) (D : Matrix (Fin 3) (Fin 3) ℝ) :
    InfoGeometry.SuperGrassmannian.NuclearQuasiphononSuperGrassmannian.superTrace
        (superBlock23ToMatrix M) =
      InfoGeometry.Synthesis.SuperGrassmannianFiveGradedColorSupersymmetrySynthesis.superTrace23
        M.A M.D ∧
    InfoGeometry.SuperGrassmannian.NuclearQuasiphononSuperGrassmannian.blockBerezinian
        (superBlock23ToMatrix M) M.D⁻¹ =
      InfoGeometry.Synthesis.SuperGrassmannianFiveGradedColorSupersymmetrySynthesis.SuperBlock23.fullBerezinian23 M ∧
    M.D.det * (M.D⁻¹).det = 1 ∧
    superBlock23ToMatrix
        (InfoGeometry.Synthesis.SuperGrassmannianFiveGradedColorSupersymmetrySynthesis.SuperBlock23.diagBlock A D) =
      InfoGeometry.SuperGrassmannian.NuclearQuasiphononSuperGrassmannian.volumeMode A D ∧
    superBlock23ToMatrix ⟨0, B, C, 0⟩ =
      InfoGeometry.SuperGrassmannian.NuclearQuasiphononSuperGrassmannian.chiralMode B C ∧
    superBlock23ToMatrix ⟨σ • 1, 0, 0, σ • 1⟩ =
      InfoGeometry.SuperGrassmannian.NuclearQuasiphononSuperGrassmannian.scaleMode σ := by
  refine ⟨rfl, ?_, ?_, rfl, rfl, rfl⟩
  · dsimp [InfoGeometry.SuperGrassmannian.NuclearQuasiphononSuperGrassmannian.blockBerezinian,
      InfoGeometry.Synthesis.SuperGrassmannianFiveGradedColorSupersymmetrySynthesis.SuperBlock23.fullBerezinian23,
      InfoGeometry.Algebra.BdGSchurBerezinianCompatibility.blockSchurComplement,
      superBlock23ToMatrix]
    simp [Matrix.det_nonsing_inv, Ring.inverse_eq_inv, div_eq_mul_inv]
  · rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv, mul_inv_cancel₀ hD]

/-- $\mathbb{Z}_2$ parity projection for `(2|1)` OSp (`±1` odd, `0, ±2` even). -/
def fiveGradeToZ2 (k : ℤ) : Bool :=
  decide (k % 2 ≠ 0)

/-- Explicit `ℤ → Z2Z2ColorGrade` Günaydin–Gürsey color-SUSY projection (`0 ↦ (0,0)`, `±1 ↦ (1,1)`, `±2 ↦ (1,0)`). -/
def gunaydinGurseyZ2Z2Projection : ℤ →
    InfoGeometry.Synthesis.SuperGrassmannianFiveGradedColorSupersymmetrySynthesis.Z2Z2ColorGrade
  | 0 => InfoGeometry.Synthesis.SuperGrassmannianFiveGradedColorSupersymmetrySynthesis.gradeGauge0
  | 1 => InfoGeometry.Synthesis.SuperGrassmannianFiveGradedColorSupersymmetrySynthesis.gradeQuark
  | -1 => InfoGeometry.Synthesis.SuperGrassmannianFiveGradedColorSupersymmetrySynthesis.gradeQuark
  | 2 => InfoGeometry.Synthesis.SuperGrassmannianFiveGradedColorSupersymmetrySynthesis.gradeLepton
  | -2 => InfoGeometry.Synthesis.SuperGrassmannianFiveGradedColorSupersymmetrySynthesis.gradeLepton
  | _ => InfoGeometry.Synthesis.SuperGrassmannianFiveGradedColorSupersymmetrySynthesis.gradeGauge0

theorem gunaydinGurseyZ2Z2Projection_laws :
    gunaydinGurseyZ2Z2Projection 0 =
      InfoGeometry.Synthesis.SuperGrassmannianFiveGradedColorSupersymmetrySynthesis.gradeGauge0 ∧
    gunaydinGurseyZ2Z2Projection 1 =
      InfoGeometry.Synthesis.SuperGrassmannianFiveGradedColorSupersymmetrySynthesis.gradeQuark ∧
    gunaydinGurseyZ2Z2Projection (-1) =
      InfoGeometry.Synthesis.SuperGrassmannianFiveGradedColorSupersymmetrySynthesis.gradeQuark ∧
    gunaydinGurseyZ2Z2Projection 2 =
      InfoGeometry.Synthesis.SuperGrassmannianFiveGradedColorSupersymmetrySynthesis.gradeLepton ∧
    gunaydinGurseyZ2Z2Projection (-2) =
      InfoGeometry.Synthesis.SuperGrassmannianFiveGradedColorSupersymmetrySynthesis.gradeLepton ∧
    InfoGeometry.Synthesis.SuperGrassmannianFiveGradedColorSupersymmetrySynthesis.z2z2KoszulSign
      (gunaydinGurseyZ2Z2Projection 1) (gunaydinGurseyZ2Z2Projection (-1)) = 1 ∧
    InfoGeometry.Synthesis.SuperGrassmannianFiveGradedColorSupersymmetrySynthesis.z2z2KoszulSign
      (gunaydinGurseyZ2Z2Projection 1) (gunaydinGurseyZ2Z2Projection 2) = -1 ∧
    InfoGeometry.Synthesis.SuperGrassmannianFiveGradedColorSupersymmetrySynthesis.z2z2KoszulSign
      (gunaydinGurseyZ2Z2Projection 2) (gunaydinGurseyZ2Z2Projection (-2)) = -1 := by
  have h1 := InfoGeometry.Synthesis.SuperGrassmannianFiveGradedColorSupersymmetrySynthesis.z2z2_color_supersymmetry_sign_laws
    InfoGeometry.Synthesis.SuperGrassmannianFiveGradedColorSupersymmetrySynthesis.gradeQuark
    InfoGeometry.Synthesis.SuperGrassmannianFiveGradedColorSupersymmetrySynthesis.gradeLepton
  exact ⟨rfl, rfl, rfl, rfl, rfl, h1.2.2.2.2.2, h1.2.2.2.1, h1.2.2.2.2.1⟩

namespace ScopedOpZornModule

scoped instance instSMulRealOpZornMatrix : SMul ℝ OpZornR where
  smul r X := ⟨r * X.a, ⟨r * X.v.x, r * X.v.y, r * X.v.z⟩,
    ⟨r * X.w.x, r * X.w.y, r * X.w.z⟩, r * X.b⟩

scoped instance instModuleRealOpZornMatrix : Module ℝ OpZornR where
  one_smul X := by
    rcases X with ⟨a, ⟨vx, vy, vz⟩, ⟨wx, wy, wz⟩, b⟩
    change (⟨1 * a, ⟨1 * vx, 1 * vy, 1 * vz⟩, ⟨1 * wx, 1 * wy, 1 * wz⟩, 1 * b⟩ : OpZornR) = _
    simp
  mul_smul r s X := by
    rcases X with ⟨a, ⟨vx, vy, vz⟩, ⟨wx, wy, wz⟩, b⟩
    change (⟨(r * s) * a, ⟨(r * s) * vx, (r * s) * vy, (r * s) * vz⟩,
        ⟨(r * s) * wx, (r * s) * wy, (r * s) * wz⟩, (r * s) * b⟩ : OpZornR) =
      ⟨r * (s * a), ⟨r * (s * vx), r * (s * vy), r * (s * vz)⟩,
        ⟨r * (s * wx), r * (s * wy), r * (s * wz)⟩, r * (s * b)⟩
    simp [mul_assoc]
  smul_zero r := by
    change (⟨r * 0, ⟨r * 0, r * 0, r * 0⟩, ⟨r * 0, r * 0, r * 0⟩, r * 0⟩ : OpZornR) = 0
    simp; rfl
  smul_add r X Y := by
    rcases X with ⟨a₁, ⟨vx₁, vy₁, vz₁⟩, ⟨wx₁, wy₁, wz₁⟩, b₁⟩
    rcases Y with ⟨a₂, ⟨vx₂, vy₂, vz₂⟩, ⟨wx₂, wy₂, wz₂⟩, b₂⟩
    change (⟨r * (a₁ + a₂), ⟨r * (vx₁ + vx₂), r * (vy₁ + vy₂), r * (vz₁ + vz₂)⟩,
        ⟨r * (wx₁ + wx₂), r * (wy₁ + wy₂), r * (wz₁ + wz₂)⟩, r * (b₁ + b₂)⟩ : OpZornR) =
      ⟨r * a₁ + r * a₂, ⟨r * vx₁ + r * vx₂, r * vy₁ + r * vy₂, r * vz₁ + r * vz₂⟩,
        ⟨r * wx₁ + r * wx₂, r * wy₁ + r * wy₂, r * wz₁ + r * wz₂⟩, r * b₁ + r * b₂⟩
    simp [mul_add]
  add_smul r s X := by
    rcases X with ⟨a, ⟨vx, vy, vz⟩, ⟨wx, wy, wz⟩, b⟩
    change (⟨(r + s) * a, ⟨(r + s) * vx, (r + s) * vy, (r + s) * vz⟩,
        ⟨(r + s) * wx, (r + s) * wy, (r + s) * wz⟩, (r + s) * b⟩ : OpZornR) =
      ⟨r * a + s * a, ⟨r * vx + s * vx, r * vy + s * vy, r * vz + s * vz⟩,
        ⟨r * wx + s * wx, r * wy + s * wy, r * wz + s * wz⟩, r * b + s * b⟩
    simp [add_mul]
  zero_smul X := by
    rcases X with ⟨a, ⟨vx, vy, vz⟩, ⟨wx, wy, wz⟩, b⟩
    change (⟨0 * a, ⟨0 * vx, 0 * vy, 0 * vz⟩, ⟨0 * wx, 0 * wy, 0 * wz⟩, 0 * b⟩ : OpZornR) = 0
    simp; rfl

end ScopedOpZornModule

/-- Explicit `ℝ`-linear map from the nuclear `sp(4, ℝ)` carrier `carLieSubalgebra` into the
Günaydin–Gürsey multiplet carrier `(Fin 2 → ℝ) × (Fin 3 → ℝ) × (Fin 3 → ℝ)`. -/
def car5ToGunaydinGursey :
    InfoGeometry.Physics.NuclearFiveGradeGeneratorRepresentation.carLieSubalgebra →ₗ[ℝ]
      InfoGeometry.Synthesis.Cl55SuperGrassmannianKKTSynthesis.GunaydinGurseyMultiplet ℝ where
  toFun X := (![X.1 3 3, X.1 2 2], ![X.1 0 3, X.1 2 0, X.1 1 0], ![X.1 3 0, -X.1 0 1, X.1 0 2])
  map_add' X Y := by
    refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> (ext i; fin_cases i <;> (simp; try abel))
  map_smul' r X := by
    refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> (ext i; fin_cases i <;> simp)

section OpZornIntertwiner

open scoped ScopedOpZornModule

/-- Explicit grade-preserving `ℝ`-linear intertwiner `carLieSubalgebra →ₗ[ℝ] OpZornMatrix ℝ`
sending the 5 Euler-grade spaces `(-2, -1, 0, +1, +2)` of `sp(4, ℝ)` into the 5 eigenspaces
of `opEulerFiveGrading` on `OpZornMatrix ℝ`. Note: `OpZornMatrix ℝ` is non-associative, so
`car5ToOpZornEuler` is `ℝ`-linear and Euler-grade-preserving (not a Lie-homomorphism). -/
def car5ToOpZornEuler :
    InfoGeometry.Physics.NuclearFiveGradeGeneratorRepresentation.carLieSubalgebra →ₗ[ℝ]
      OpZornR where
  toFun X := ⟨X.1 3 3, ⟨X.1 0 3, X.1 2 0, X.1 1 0⟩, ⟨X.1 3 0, -X.1 0 1, X.1 0 2⟩, X.1 2 2⟩
  map_add' X Y := by
    change (⟨(X.1 + Y.1) 3 3, ⟨(X.1 + Y.1) 0 3, (X.1 + Y.1) 2 0, (X.1 + Y.1) 1 0⟩,
        ⟨(X.1 + Y.1) 3 0, -(X.1 + Y.1) 0 1, (X.1 + Y.1) 0 2⟩, (X.1 + Y.1) 2 2⟩ : OpZornR) =
      ⟨X.1 3 3 + Y.1 3 3, ⟨X.1 0 3 + Y.1 0 3, X.1 2 0 + Y.1 2 0, X.1 1 0 + Y.1 1 0⟩,
        ⟨X.1 3 0 + Y.1 3 0, -X.1 0 1 + -Y.1 0 1, X.1 0 2 + Y.1 0 2⟩, X.1 2 2 + Y.1 2 2⟩
    simp only [Matrix.add_apply, neg_add]
  map_smul' r X := by
    change (⟨(r • X.1) 3 3, ⟨(r • X.1) 0 3, (r • X.1) 2 0, (r • X.1) 1 0⟩,
        ⟨(r • X.1) 3 0, -(r • X.1) 0 1, (r • X.1) 0 2⟩, (r • X.1) 2 2⟩ : OpZornR) =
      ⟨r * X.1 3 3, ⟨r * X.1 0 3, r * X.1 2 0, r * X.1 1 0⟩,
        ⟨r * X.1 3 0, r * -X.1 0 1, r * X.1 0 2⟩, r * X.1 2 2⟩
    simp only [Matrix.smul_apply, smul_eq_mul, mul_neg]

theorem car5ToGunaydinGursey_eq_opZornEquiv
    (X : InfoGeometry.Physics.NuclearFiveGradeGeneratorRepresentation.carLieSubalgebra) :
    InfoGeometry.Synthesis.SuperGrassmannianFiveGradedColorSupersymmetrySynthesis.opZornGunaydinGurseyEquiv ℝ
        (car5ToOpZornEuler X) =
      car5ToGunaydinGursey X := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> ext i <;> fin_cases i <;> rfl

/-- `car5ToOpZornEuler` strictly intertwines `ad gradingOperator` on `carLieSubalgebra` with
`opEulerFiveGrading` on `OpZornMatrix ℝ` across all five grades `{-2, -1, 0, +1, +2}`. -/
theorem opEulerFiveGrading_intertwines_car5
    (X : InfoGeometry.Physics.NuclearFiveGradeGeneratorRepresentation.carLieSubalgebra) :
    InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.opEulerFiveGrading
        (car5ToOpZornEuler X) =
      car5ToOpZornEuler ⁅gradingCartanSub, X⁆ := by
  have hbr : (⁅gradingCartanSub, X⁆).1 =
      InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.gradingOperator * X.1 -
      X.1 * InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.gradingOperator := rfl
  change InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.opEulerFiveGrading
      (car5ToOpZornEuler X) =
    (⟨(⁅gradingCartanSub, X⁆).1 3 3,
      ⟨(⁅gradingCartanSub, X⁆).1 0 3, (⁅gradingCartanSub, X⁆).1 2 0, (⁅gradingCartanSub, X⁆).1 1 0⟩,
      ⟨(⁅gradingCartanSub, X⁆).1 3 0, -(⁅gradingCartanSub, X⁆).1 0 1, (⁅gradingCartanSub, X⁆).1 0 2⟩,
      (⁅gradingCartanSub, X⁆).1 2 2⟩ : OpZornR)
  rw [hbr, InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.gradingOperator_eq_diagonal]
  dsimp [InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.opEulerFiveGrading,
    car5ToOpZornEuler]
  simp only [InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.OpZornMatrix.mk.injEq,
    InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.OpVec3.mk.injEq]
  refine ⟨?_, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ?_⟩ <;>
    (simp only [Matrix.mul_apply, Fin.sum_univ_four]; norm_num [Fin.isValue]; try ring)

/-- Grade preservation under `car5ToOpZornEuler`: any grade-`k` element of `carLieSubalgebra` maps
to an exact `k`-eigenvector of `opEulerFiveGrading`. -/
theorem car5ToOpZornEuler_preserves_grade {k : ℤ}
    {X : InfoGeometry.Physics.NuclearFiveGradeGeneratorRepresentation.carLieSubalgebra}
    (hX : InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.HasGrade k X.1) :
    InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.opEulerFiveGrading
        (car5ToOpZornEuler X) =
      (k : ℝ) • car5ToOpZornEuler X := by
  rw [opEulerFiveGrading_intertwines_car5]
  have hsub : ⁅gradingCartanSub, X⁆ = (k : ℝ) • X := Subtype.ext hX
  rw [hsub, map_smul]

/-- Explicit generator readout of `car5ToOpZornEuler` across all 5 Euler grades `{-2, -1, 0, +1, +2}`
together with the KKT quintic polynomial `E₅⁵ - 5 E₅³ + 4 E₅ = 0`. -/
theorem car5ToOpZornEuler_generators_and_kkt
    (X : InfoGeometry.Physics.NuclearFiveGradeGeneratorRepresentation.carLieSubalgebra) :
    car5ToOpZornEuler
        ⟨InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.pairAnnihilation,
          InfoGeometry.Physics.NuclearFiveGradeGeneratorRepresentation.representM4R_mem_carLieSubalgebra .pairAnnihilation⟩ =
      InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.opGradeMinus2 (1 : ℝ) ∧
    car5ToOpZornEuler
        ⟨InfoGeometry.Canonical.SplitCliffordTwoModeCAR.a1,
          InfoGeometry.Physics.NuclearFiveGradeGeneratorRepresentation.representM4R_mem_carLieSubalgebra .annihilationOne⟩ =
      InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.opGradeMinus1 (0 : ℝ) 1 ∧
    car5ToOpZornEuler
        ⟨InfoGeometry.Canonical.SplitCliffordTwoModeCAR.a2,
          InfoGeometry.Physics.NuclearFiveGradeGeneratorRepresentation.representM4R_mem_carLieSubalgebra .annihilationTwo⟩ =
      InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.opGradeMinus1 (-1 : ℝ) 0 ∧
    car5ToOpZornEuler gradingCartanSub =
      InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.opGradeZero (1 : ℝ) 0 ∧
    car5ToOpZornEuler
        ⟨InfoGeometry.Physics.NuclearFiveGradeDegreeZeroSL2.degreeZeroCartan,
          InfoGeometry.Physics.NuclearFiveGradeGeneratorRepresentation.degreeZeroSL2_mem_carLieSubalgebra.2.2⟩ =
      InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.opGradeZero (0 : ℝ) 1 ∧
    car5ToOpZornEuler
        ⟨InfoGeometry.Canonical.SplitCliffordTwoModeCAR.a1Dag,
          InfoGeometry.Physics.NuclearFiveGradeGeneratorRepresentation.representM4R_mem_carLieSubalgebra .creationOne⟩ =
      InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.opGradePlus1 (1 : ℝ) 0 ∧
    car5ToOpZornEuler
        ⟨InfoGeometry.Canonical.SplitCliffordTwoModeCAR.a2Dag,
          InfoGeometry.Physics.NuclearFiveGradeGeneratorRepresentation.representM4R_mem_carLieSubalgebra .creationTwo⟩ =
      InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.opGradePlus1 (0 : ℝ) 1 ∧
    car5ToOpZornEuler
        ⟨InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.pairCreation,
          InfoGeometry.Physics.NuclearFiveGradeGeneratorRepresentation.representM4R_mem_carLieSubalgebra .pairCreation⟩ =
      InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.opGradePlus2 (1 : ℝ) ∧
    (let E1 := InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.opEulerFiveGrading
        (car5ToOpZornEuler X)
     let E2 := InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.opEulerFiveGrading E1
     let E3 := InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.opEulerFiveGrading E2
     let E4 := InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.opEulerFiveGrading E3
     let E5 := InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.opEulerFiveGrading E4
     E5 - (E3 + E3 + E3 + E3 + E3) + (E1 + E1 + E1 + E1) = 0) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp [car5ToOpZornEuler]; rw [pairAnnihilation_eq_mat4]
    ext <;> norm_num [InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.opGradeMinus2]
  · ext <;> norm_num [car5ToOpZornEuler,
      InfoGeometry.Canonical.SplitCliffordTwoModeCAR.a1,
      InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.opGradeMinus1]
  · ext <;> norm_num [car5ToOpZornEuler,
      InfoGeometry.Canonical.SplitCliffordTwoModeCAR.a2,
      InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.opGradeMinus1]
  · ext <;> norm_num [car5ToOpZornEuler, gradingCartanSub,
      InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.gradingOperator_eq_diagonal,
      InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.opGradeZero,
      InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.opCartanDiag]
  · dsimp [car5ToOpZornEuler]; rw [degreeZeroCartan_eq_mat4]
    ext <;> norm_num [InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.opGradeZero,
      InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.opCartanDiag]
  · ext <;> norm_num [car5ToOpZornEuler,
      InfoGeometry.Canonical.SplitCliffordTwoModeCAR.a1Dag,
      InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.opGradePlus1]
  · ext <;> norm_num [car5ToOpZornEuler,
      InfoGeometry.Canonical.SplitCliffordTwoModeCAR.a2Dag,
      InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.opGradePlus1]
  · dsimp [car5ToOpZornEuler]; rw [pairCreation_eq_mat4]
    ext <;> norm_num [InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.opGradePlus2]
  · exact (InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.eulerFiveGrading_eigen_derivation_and_kkt_polynomial
      (car5ToOpZornEuler X) 0 0 0 0 0 0 0 0 0 0 0 0).2.2.2.2.2.2.2

end OpZornIntertwiner

/-- `Cl55SuperGrassmannianKKTSynthesis`, `SuperGrassmannianFiveGradedColorSupersymmetrySynthesis`,
and `Z2Z2KoszulOperadicHomologyShirokovSynthesis` synthesis linking `adH` on `M₃(ℝ)` to
`H_gen ℝ`, `Cl(5,5)` 5-graded ladders, Zorn split-octonion equivalences, `z2z2SuperBracket`,
and Koszul-Shirokov `(2|3)` supertrace/Berezinian invariants. -/
theorem color_susy_cl55_koszul_shirokov_link
    (i j : Fin 5) (g : InfoGeometry.Clifford.Clifford55.Spin55)
    (X : M₃)
    (g₁ g₂ : InfoGeometry.Synthesis.SuperGrassmannianFiveGradedColorSupersymmetrySynthesis.Z2Z2ColorGrade)
    (A_bos Q_bos M_bos : Matrix (Fin 2) (Fin 2) ℝ)
    (D_fer Q_fer M_fer : Matrix (Fin 3) (Fin 3) ℝ)
    (hQ_bos : Q_bos * Q_bos = 0) (hQ_fer : Q_fer * Q_fer = 0)
    (u0 u1 u2 u12 : ℝ)
    (h_match : InfoGeometry.Synthesis.ShirokovCliffordTraceDetInverseBridge.cl11DetScalar u0 u1 u2 u12 = D_fer.det)
    (hD_ne : D_fer.det ≠ 0) :
    InfoGeometry.SuperGrassmannian.FiveGradedLieSuperalgebra.adH X =
      ⁅InfoGeometry.SuperGrassmannian.SuperconformalOSpJordanPair.H_gen ℝ, X⁆ ∧
    (InfoGeometry.Clifford.Clifford55.creation55 i ∈
        InfoGeometry.Clifford.Clifford55.cl55GradeSubmodule 1 ∧
      InfoGeometry.Clifford.Clifford55.annihilation55 i ∈
        InfoGeometry.Clifford.Clifford55.cl55GradeSubmodule (-1) ∧
      InfoGeometry.Clifford.Clifford55.creation55 i *
        InfoGeometry.Clifford.Clifford55.creation55 j ∈
        InfoGeometry.Clifford.Clifford55.cl55GradeSubmodule 2 ∧
      InfoGeometry.Clifford.Clifford55.annihilation55 i *
        InfoGeometry.Clifford.Clifford55.annihilation55 j ∈
        InfoGeometry.Clifford.Clifford55.cl55GradeSubmodule (-2) ∧
      InfoGeometry.Clifford.Clifford55.creation55 i *
        InfoGeometry.Clifford.Clifford55.annihilation55 j ∈
        InfoGeometry.Clifford.Clifford55.cl55GradeSubmodule 0) ∧
    (InfoGeometry.SuperGrassmannian.FiveGradedLieSuperalgebra.adH
        (InfoGeometry.SuperGrassmannian.FiveGradedLieSuperalgebra.adH
          (InfoGeometry.SuperGrassmannian.FiveGradedLieSuperalgebra.adH
            (InfoGeometry.SuperGrassmannian.FiveGradedLieSuperalgebra.adH
              (InfoGeometry.SuperGrassmannian.FiveGradedLieSuperalgebra.adH X)))) -
      5 • InfoGeometry.SuperGrassmannian.FiveGradedLieSuperalgebra.adH
        (InfoGeometry.SuperGrassmannian.FiveGradedLieSuperalgebra.adH
          (InfoGeometry.SuperGrassmannian.FiveGradedLieSuperalgebra.adH X)) +
      4 • InfoGeometry.SuperGrassmannian.FiveGradedLieSuperalgebra.adH X = 0) ∧
    InfoGeometry.Synthesis.SuperGrassmannianFiveGradedColorSupersymmetrySynthesis.z2z2SuperBracket
      g₁ g₂ X X =
      -(InfoGeometry.Synthesis.SuperGrassmannianFiveGradedColorSupersymmetrySynthesis.z2z2KoszulSign g₁ g₂ •
        InfoGeometry.Synthesis.SuperGrassmannianFiveGradedColorSupersymmetrySynthesis.z2z2SuperBracket g₂ g₁ X X) ∧
    InfoGeometry.Synthesis.SuperGrassmannianFiveGradedColorSupersymmetrySynthesis.superTrace23
      (A_bos + (Q_bos * M_bos - M_bos * Q_bos))
      (D_fer + (Q_fer * M_fer - M_fer * Q_fer)) =
      InfoGeometry.Synthesis.SuperGrassmannianFiveGradedColorSupersymmetrySynthesis.superTrace23 A_bos D_fer ∧
    InfoGeometry.Synthesis.Z2Z2KoszulOperadicHomologyShirokovSynthesis.koszulDualGrade
      (InfoGeometry.Synthesis.Z2Z2KoszulOperadicHomologyShirokovSynthesis.koszulDualGrade g₁) = g₁ ∧
    InfoGeometry.Synthesis.SuperGrassmannianFiveGradedColorSupersymmetrySynthesis.superBerezinian23
      (InfoGeometry.Synthesis.ShirokovCliffordTraceDetInverseBridge.cl11Multivector u0 u1 u2 u12) D_fer =
      InfoGeometry.Synthesis.Z2Z2KoszulOperadicHomologyShirokovSynthesis.shirokovSuperBerezinian23
        u0 u1 u2 u12 D_fer ∧
    InfoGeometry.Synthesis.SuperGrassmannianFiveGradedColorSupersymmetrySynthesis.superBerezinian23
      (InfoGeometry.Synthesis.ShirokovCliffordTraceDetInverseBridge.cl11Multivector u0 u1 u2 u12) D_fer = 1 ∧
    Real.log (InfoGeometry.Synthesis.SuperGrassmannianFiveGradedColorSupersymmetrySynthesis.superBerezinian23
      (InfoGeometry.Synthesis.ShirokovCliffordTraceDetInverseBridge.cl11Multivector u0 u1 u2 u12) D_fer) = 0 ∧
    InfoGeometry.Clifford.Clifford55.spinCliffordRingEquiv g
      (InfoGeometry.Clifford.Clifford55.creation55 i *
          InfoGeometry.Clifford.Clifford55.annihilation55 j -
        InfoGeometry.Clifford.Clifford55.annihilation55 j *
          InfoGeometry.Clifford.Clifford55.creation55 i) ∈
      InfoGeometry.Clifford.Clifford55.spinTransportedCl55GradeSubmodule g (1 + (-1)) := by
  have hadH : InfoGeometry.SuperGrassmannian.FiveGradedLieSuperalgebra.adH X =
      ⁅InfoGeometry.SuperGrassmannian.SuperconformalOSpJordanPair.H_gen ℝ, X⁆ := by
    unfold InfoGeometry.SuperGrassmannian.FiveGradedLieSuperalgebra.adH
    rw [hGen_eq_H_grading_and_cube.1]
    rfl
  have hcl := InfoGeometry.Synthesis.Cl55SuperGrassmannianKKTSynthesis.cl55_kkt_five_graded_ladder_synthesis i j g
  have hkkt := InfoGeometry.Synthesis.Cl55SuperGrassmannianKKTSynthesis.kkt_quintic_characteristic_synthesis (1 : ℝ) X
  have hjac := InfoGeometry.Synthesis.SuperGrassmannianFiveGradedColorSupersymmetrySynthesis.z2z2_colored_super_jacobi
    g₁ g₂ g₁ X X X
  have hhom := InfoGeometry.Synthesis.Z2Z2KoszulOperadicHomologyShirokovSynthesis.homological_context_supertrace_invariance
    A_bos Q_bos M_bos D_fer Q_fer M_fer hQ_bos hQ_fer
  have hshir := InfoGeometry.Synthesis.Z2Z2KoszulOperadicHomologyShirokovSynthesis.shirokov_matrix_free_superBerezinian_horizon_synthesis
    u0 u1 u2 u12 D_fer h_match hD_ne
  exact ⟨hadH, ⟨hcl.1, hcl.2.1, hcl.2.2.1, hcl.2.2.2.1, hcl.2.2.2.2.1⟩, hkkt.2,
    hjac.1, hhom.2.2, rfl, hshir.2.1, hshir.2.2.1, hshir.2.2.2, hcl.2.2.2.2.2.2.2.2⟩

/-!
## Section 5: Unified Seam A Data Bundle (T17), `32×32` Soloviev No-Go, RPA Defect, & Carrier Boundaries
-/

section SeamABundle

open scoped ScopedOpZornModule

/-- Constructive `Type` bundle packaging all Seam A intertwiners across the concrete two-mode CAR,
`sp(4, ℝ)`, Freudenthal `FiveGradedCarrier`, `(2|1)` OSp / Super-Grassmannian, `Cuntz3`, `(2|3)`
`SuperBlock23`, and Günaydin–Gürsey / `OpZornMatrix ℝ` 5-graded carriers. (Uses `Type`, not `Prop`,
avoiding aggregate-Prop constructors.) -/
structure NuclearFiveGradeSuperGrassmannianIntertwinerData where
  carToComplexOp : M4R →ₗ⁅ℝ⁆ Op
  carToFreudenthal :
    InfoGeometry.Physics.NuclearFiveGradeGeneratorRepresentation.carLieSubalgebra →ₗ⁅ℝ⁆
      InfoGeometry.Exceptional.Freudenthal.FiveGradedCarrier
        InfoGeometry.Nuclear.FiveGraded.punitCubicJordanDatum
  carToFreudenthalEquiv :
    InfoGeometry.Physics.NuclearFiveGradeGeneratorRepresentation.carLieSubalgebra ≃ₗ⁅ℝ⁆
      InfoGeometry.Exceptional.Freudenthal.FiveGradedCarrier
        InfoGeometry.Physics.NuclearFiveGradeGeneratorRepresentation.zeroCubicJordanDatum.{0}
  freudenthalToM4R :
    InfoGeometry.Exceptional.Freudenthal.FiveGradedCarrier
      InfoGeometry.Nuclear.FiveGraded.punitCubicJordanDatum →ₗ[ℝ] M4R
  ospToSuperBlock3 : M₃ ≃ₐ[ℝ] Matrix (Fin 2 ⊕ Fin 1) (Fin 2 ⊕ Fin 1) ℝ
  pairSL2ToOSpEven :
    InfoGeometry.Physics.NuclearFiveGradeGeneratorRepresentation.pairSL2Subalgebra ≃ₗ⁅ℝ⁆
      InfoGeometry.Nuclear.NuclearQuasiphononJordanPairBridge.ospEvenLieSubalgebra
  cuntzToM3 :
    InfoGeometry.Algebra.CuntzMatrixUnitFiveGradingBridge.matrixUnitLieSubalgebra →ₗ⁅ℝ⁆ M₃
  superBlock23Equiv :
    InfoGeometry.Synthesis.SuperGrassmannianFiveGradedColorSupersymmetrySynthesis.SuperBlock23 ℝ ≃
      Matrix (Fin 2 ⊕ Fin 3) (Fin 2 ⊕ Fin 3) ℝ
  carToGunaydinGursey :
    InfoGeometry.Physics.NuclearFiveGradeGeneratorRepresentation.carLieSubalgebra →ₗ[ℝ]
      InfoGeometry.Synthesis.Cl55SuperGrassmannianKKTSynthesis.GunaydinGurseyMultiplet ℝ
  carToOpZorn :
    InfoGeometry.Physics.NuclearFiveGradeGeneratorRepresentation.carLieSubalgebra →ₗ[ℝ]
      OpZornR
  opZornToGunaydinGursey :
    OpZornR ≃
      InfoGeometry.Synthesis.Cl55SuperGrassmannianKKTSynthesis.GunaydinGurseyMultiplet ℝ

/-- Canonical constructive inhabitant of `NuclearFiveGradeSuperGrassmannianIntertwinerData` (T17). -/
def canonicalNuclearFiveGradeSuperGrassmannianIntertwiner :
    NuclearFiveGradeSuperGrassmannianIntertwinerData where
  carToComplexOp := InfoGeometry.Physics.NuclearFiveGradeGeneratorRepresentation.m4rToOp
  carToFreudenthal :=
    InfoGeometry.Physics.NuclearFiveGradeGeneratorRepresentation.carToFiveGraded
      InfoGeometry.Nuclear.FiveGraded.punitCubicJordanDatum
  carToFreudenthalEquiv :=
    InfoGeometry.Physics.NuclearFiveGradeGeneratorRepresentation.carToFiveGradedEquiv
  freudenthalToM4R := InfoGeometry.Nuclear.FiveGraded.Phi
  ospToSuperBlock3 := ospToSuperBlock3AlgEquiv
  pairSL2ToOSpEven := pairSL2ToOSpEvenEquiv
  cuntzToM3 := cuntzMatUnitToM3
  superBlock23Equiv := superBlock23MatrixEquiv ℝ
  carToGunaydinGursey := car5ToGunaydinGursey
  carToOpZorn := car5ToOpZornEuler
  opZornToGunaydinGursey :=
    InfoGeometry.Synthesis.SuperGrassmannianFiveGradedColorSupersymmetrySynthesis.opZornGunaydinGurseyEquiv ℝ

end SeamABundle

/-- **Seam A `32×32` Soloviev `MatStage 5` No-Go vs. Finite Compression Boundary**:
1. Simultaneous exact infinite `PhononRPA` + finite `A →ₐ[ℝ] FullHamiltonian` (`MatStage 5`, `32×32`)
   realization is impossible (`IsEmpty (SolovievFiveGradedRealization grade M sys)`).
2. Nevertheless, the projected `2×2` Soloviev QPNM Hamiltonian `projectedTotal` IS inhabited on
   `MatStage 5` (`projectedTotal_nonvacuous_matStage5_witness`), and the finite two-origin Soloviev
   packet (`soloviev_two_origin_packet`) holds on `EvenSector = Vec2C`. -/
theorem seamA_soloviev_matStage5_nogo
    {ιq ιph A : Type*} [DecidableEq ιq] [DecidableEq ιph] [Ring A] [Algebra ℝ A]
    {grade : ℤ → Submodule ℝ A}
    {M : InfoGeometry.Physics.NuclearGradedBathCommutant.ThermalQuasiparticleModel grade}
    {sys : InfoGeometry.Physics.NuclearPhononRPA.CoupledQuasiparticlePhononSystem ιq ιph A}
    (Eqp ω V : ℂ) :
    IsEmpty
        (InfoGeometry.Physics.NuclearSolovievFiveGradedCommutantBridge.SolovievFiveGradedRealization
          grade M sys) ∧
    (∃ (H_rep : InfoGeometry.Physics.NuclearSolovievStateProjection.FullHamiltonian)
       (channel : InfoGeometry.Physics.NuclearSolovievStateProjection.TwoSpinorChannel)
       (θ E : ℝ),
      H_repᵀ = H_rep ∧
      InfoGeometry.Physics.NuclearSolovievFiveGradedCommutantBridge.projectedTotal channel H_rep =
        !![1, 1; 1, 3] ∧
      channel.dressedEnergy H_rep - E ≠ 0 ∧
      channel.coupling H_rep * Real.cos (2 * θ) =
        ((channel.dressedEnergy H_rep - channel.qpEnergy H_rep) / 2) * Real.sin (2 * θ) ∧
      (InfoGeometry.Physics.NuclearSolovievFiveGradedCommutantBridge.rotatedChannel channel θ).dressedEnergy H_rep - E ≠ 0 ∧
      (InfoGeometry.Physics.NuclearSolovievFiveGradedCommutantBridge.rotatedChannel channel θ).coupling H_rep = 0 ∧
      ∀ ψ : Fin 2 → ℝ,
        ((InfoGeometry.Physics.NuclearSolovievFiveGradedCommutantBridge.projectedTotal
            (InfoGeometry.Physics.NuclearSolovievFiveGradedCommutantBridge.rotatedChannel channel θ) H_rep).mulVec ψ =
            E • ψ ↔
          (InfoGeometry.Physics.NuclearSolovievFiveGradedCommutantBridge.rotatedChannel channel θ).qpEnergy H_rep * ψ 0 =
            E * ψ 0 ∧ ψ 1 = 0)) ∧
    (InfoGeometry.Physics.NuclearBdGSolovievCompression.solovievBlock Eqp ω V =
        (Eqp + ω / 2) • (1 : InfoGeometry.Physics.NuclearBdGSolovievCompression.Mat2) +
          InfoGeometry.Physics.NuclearBdGSolovievCompression.bdgBlock (ω / 2) V ∧
      ∀ φ : InfoGeometry.Physics.NuclearBdGSolovievCompression.EvenSector,
        InfoGeometry.Physics.NuclearCARPhononCommonCarrier.compressedOscillatorHamiltonian Eqp ω V φ =
          Matrix.mulVec (InfoGeometry.Physics.NuclearBdGSolovievCompression.solovievBlock Eqp ω V) φ) :=
  ⟨InfoGeometry.Physics.NuclearSolovievFiveGradedCommutantBridge.solovievFiveGradedRealization_isEmpty,
   InfoGeometry.Physics.NuclearSolovievFiveGradedCommutantBridge.projectedTotal_nonvacuous_matStage5_witness,
   InfoGeometry.Physics.NuclearFiveGradeBdGSolovievClosure.soloviev_two_origin_packet Eqp ω V⟩

/-- **Seam A↔D Noncommutative RPA Commutator Defect Preservation**:
The off-diagonal RPA square defect `[pairCreation, pairAnnihilation] = gradingOperator ≠ 0` is
strictly preserved across `carLieSubalgebra`, `pairSL2ToOSpEvenEquiv` (mapping `gradingOperator ≠ 0`
to `H_gen ℝ ≠ 0`), and `car5ToOpZornEuler` (mapping `gradingOperator` to `opGradeZero 1 0 ≠ 0`). -/
theorem seamA_rpa_commutator_defect_preserved (α β : ℝ) :
    ((InfoGeometry.Physics.NuclearOperatorSuperSoloviev.blockHamiltonian
        InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.pairCreation
        (-InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.pairCreation)
        InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.pairAnnihilation
        (-InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.pairAnnihilation) *
      InfoGeometry.Physics.NuclearOperatorSuperSoloviev.blockHamiltonian
        InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.pairCreation
        (-InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.pairCreation)
        InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.pairAnnihilation
        (-InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.pairAnnihilation)) 0 1 =
      InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.gradingOperator ∧
      InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.gradingOperator ≠ 0) ∧
    ((∀ x : M4R,
      (InfoGeometry.Physics.NuclearOperatorSuperSoloviev.blockHamiltonian
        (α • InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.pairCreation)
        (-(α • InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.pairCreation))
        (β • InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.pairAnnihilation)
        (-(β • InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.pairAnnihilation))).mulVec ![x, 0] 1 = 0) ↔
      β = 0) ∧
    (InfoGeometry.Physics.NuclearOperatorSuperSoloviev.blockHamiltonian
        (α • InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.pairCreation)
        (-(α • InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.pairCreation))
        (β • InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.pairAnnihilation)
        (-(β • InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.pairAnnihilation)) *
      InfoGeometry.Physics.NuclearOperatorSuperSoloviev.blockHamiltonian
        (α • InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.pairCreation)
        (-(α • InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.pairCreation))
        (β • InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.pairAnnihilation)
        (-(β • InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.pairAnnihilation))) 0 1 =
      (α * β) • InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.gradingOperator ∧
    (pairSL2ToOSpEvenEquiv ⁅pairCreationSL2, pairAnnihilationSL2⁆).1 =
      InfoGeometry.SuperGrassmannian.SuperconformalOSpJordanPair.H_gen ℝ ∧
    InfoGeometry.SuperGrassmannian.SuperconformalOSpJordanPair.H_gen ℝ ≠ 0 ∧
    car5ToOpZornEuler
      ⁅(⟨InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.pairCreation,
          InfoGeometry.Physics.NuclearFiveGradeGeneratorRepresentation.representM4R_mem_carLieSubalgebra .pairCreation⟩ :
          InfoGeometry.Physics.NuclearFiveGradeGeneratorRepresentation.carLieSubalgebra),
        ⟨InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.pairAnnihilation,
          InfoGeometry.Physics.NuclearFiveGradeGeneratorRepresentation.representM4R_mem_carLieSubalgebra .pairAnnihilation⟩⁆ =
      InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.opGradeZero (1 : ℝ) 0 := by
  have hdef := InfoGeometry.Physics.NuclearFiveGradeSameCarrierClosure.pair_rpa_square_defect_is_grade_zero_cartan
  have htda := InfoGeometry.Physics.NuclearFiveGradeSameCarrierClosure.car_tda_forward_sector_iff_no_backward_pair α β
  have hwt := InfoGeometry.Physics.NuclearFiveGradeSameCarrierClosure.car_rpa_square_defect_is_amplitude_weighted_cartan α β
  have hpair : ⁅pairCreationSL2, pairAnnihilationSL2⁆ = gradingOpSL2 := by
    apply Subtype.ext
    exact InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.pair_extreme_bracket
  have hHne : InfoGeometry.SuperGrassmannian.SuperconformalOSpJordanPair.H_gen ℝ ≠ 0 := by
    intro h0
    have h00 := congr_fun (congr_fun h0 0) 0
    norm_num [InfoGeometry.SuperGrassmannian.SuperconformalOSpJordanPair.H_gen,
      InfoGeometry.SuperGrassmannian.SuperconformalOSpJordanPair.E] at h00
  have hcar :
      (⁅(⟨InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.pairCreation,
          InfoGeometry.Physics.NuclearFiveGradeGeneratorRepresentation.representM4R_mem_carLieSubalgebra .pairCreation⟩ :
          InfoGeometry.Physics.NuclearFiveGradeGeneratorRepresentation.carLieSubalgebra),
        ⟨InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.pairAnnihilation,
          InfoGeometry.Physics.NuclearFiveGradeGeneratorRepresentation.representM4R_mem_carLieSubalgebra .pairAnnihilation⟩⁆) =
      gradingCartanSub := by
    apply Subtype.ext
    exact InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.pair_extreme_bracket
  refine ⟨hdef, htda, hwt, ?_, hHne, ?_⟩
  · rw [hpair, pairSL2ToOSpEvenEquiv_gradingOperator]
  · rw [hcar]
    exact (car5ToOpZornEuler_generators_and_kkt gradingCartanSub).2.2.2.1

/-- **Carrier Boundary Preservation Theorem**:
Explicitly separates associative matrix/operator carriers (`M₄(ℝ)`, `M₃(ℝ)`, `Op = End_ℂ(ℂ⁴)`)
from non-associative carriers (`OpZornMatrix ℝ` and `fiveGradedBracket` on `FiveGradedCarrier`),
while retaining the exact Freudenthal mixed-Jacobi obstruction vs associative CAR Jacobi identity. -/
theorem seamA_carrier_boundaries
    {J : Type*} [AddCommGroup J] [Module ℝ J]
    (D : InfoGeometry.Exceptional.Freudenthal.CubicJordanDatum J)
    (y : InfoGeometry.Exceptional.Freudenthal.FreudenthalCharge J)
    (yp : InfoGeometry.Exceptional.Freudenthal.FreudenthalCharge PUnit.{1})
    (X Y Z : M4R) :
    (∃ A B : Matrix (Fin 4) (Fin 4) ℝ, A * B ≠ B * A) ∧
    (∃ A B : Matrix (Fin 3) (Fin 3) ℝ, A * B ≠ B * A) ∧
    (∃ A B : Module.End ℂ Fock4, A * B ≠ B * A) ∧
    (∃ P Q R : OpZornR, (P * Q) * R ≠ P * (Q * R)) ∧
    InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.comm X
        (InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.comm Y Z) +
      InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.comm Y
        (InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.comm Z X) +
      InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.comm Z
        (InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.comm X Y) = 0 ∧
    (InfoGeometry.Exceptional.Freudenthal.fiveGradedBracket D
        (InfoGeometry.Nuclear.FiveGraded.pairingCreation D 1)
        (InfoGeometry.Exceptional.Freudenthal.fiveGradedBracket D
          (InfoGeometry.Nuclear.FiveGraded.pairingAnnihilation D 1)
          (InfoGeometry.Nuclear.FiveGraded.qpCreation D y)) +
      InfoGeometry.Exceptional.Freudenthal.fiveGradedBracket D
        (InfoGeometry.Nuclear.FiveGraded.pairingAnnihilation D 1)
        (InfoGeometry.Exceptional.Freudenthal.fiveGradedBracket D
          (InfoGeometry.Nuclear.FiveGraded.qpCreation D y)
          (InfoGeometry.Nuclear.FiveGraded.pairingCreation D 1)) +
      InfoGeometry.Exceptional.Freudenthal.fiveGradedBracket D
        (InfoGeometry.Nuclear.FiveGraded.qpCreation D y)
        (InfoGeometry.Exceptional.Freudenthal.fiveGradedBracket D
          (InfoGeometry.Nuclear.FiveGraded.pairingCreation D 1)
          (InfoGeometry.Nuclear.FiveGraded.pairingAnnihilation D 1)) =
      InfoGeometry.Nuclear.FiveGraded.qpCreation D ((-2 : ℝ) • y)) ∧
    (InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.comm
        (InfoGeometry.Nuclear.FiveGraded.Phi
          (InfoGeometry.Nuclear.FiveGraded.pairingAnnihilation
            InfoGeometry.Nuclear.FiveGraded.punitCubicJordanDatum 1))
        (InfoGeometry.Nuclear.FiveGraded.Phi
          (InfoGeometry.Nuclear.FiveGraded.qpCreation
            InfoGeometry.Nuclear.FiveGraded.punitCubicJordanDatum yp)) =
      -InfoGeometry.Nuclear.FiveGraded.Phi
        (InfoGeometry.Exceptional.Freudenthal.fiveGradedBracket
          InfoGeometry.Nuclear.FiveGraded.punitCubicJordanDatum
          (InfoGeometry.Nuclear.FiveGraded.pairingAnnihilation
            InfoGeometry.Nuclear.FiveGraded.punitCubicJordanDatum 1)
          (InfoGeometry.Nuclear.FiveGraded.qpCreation
            InfoGeometry.Nuclear.FiveGraded.punitCubicJordanDatum yp))) := by
  have hobs := InfoGeometry.Nuclear.FiveGraded.freudenthal_mixed_jacobi_obstruction_vs_car_jacobi D y yp
  exact ⟨m4r_noncommutative_witness, m3_noncommutative_witness, op_fock4_noncommutative_witness,
    opZorn_nonassociative_witness,
    InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.comm_jacobi X Y Z,
    hobs.1, hobs.2.1⟩

/-- **Unified Supertrace, Feshbach–Schur Complement, and Berezinian Synthesis across `(2|1)` and `(2|3)`**:
Unites `(2|1)` OSp supertrace, `(ι₀ ⊕ ι₁)` deformation-triad supertrace and Feshbach–Schur elimination,
`susyH` Feshbach decomposition, and `(2|3)` `super_berezinian_gauge_invariance`. -/
theorem seamA_supertrace_and_berezinian_synthesis
    {ι₀ ι₁ : Type*} [DecidableEq ι₀] [Fintype ι₀] [DecidableEq ι₁] [Fintype ι₁]
    (X : M₃) (σ : ℝ) (A : Matrix ι₀ ι₀ ℝ) (B : Matrix ι₀ ι₁ ℝ) (C : Matrix ι₁ ι₀ ℝ)
    (D D_inv : Matrix ι₁ ι₁ ℝ) (hvol : Matrix.trace A = Matrix.trace D)
    (V : Matrix ι₀ ι₁ ℝ)
    (A₁ A₂ A_bos : Matrix (Fin 2) (Fin 2) ℝ)
    (D₁ D₂ D_fer U_C : Matrix (Fin 3) (Fin 3) ℝ)
    (M_color : InfoGeometry.Lie.CanonicalZornPeirceSL3Bridge.SL3)
    (lam invLam : ℝ)
    (h_weyl : lam * invLam = 1) (h_color_det : U_C.det = 1)
    (h_match_det : A₁.det = D₁.det) (hD₁_ne : D₁.det ≠ 0) :
    InfoGeometry.SuperGrassmannian.NuclearQuasiphononSuperGrassmannian.superTrace
        (ospToSuperBlock3 X) =
      InfoGeometry.SuperGrassmannian.SuperconformalOSpJordanPair.supertrace X ∧
    InfoGeometry.SuperGrassmannian.NuclearQuasiphononSuperGrassmannian.superTrace
        (InfoGeometry.SuperGrassmannian.NuclearQuasiphononSuperGrassmannian.scaleMode
            (ι₀ := ι₀) (ι₁ := ι₁) σ +
          InfoGeometry.SuperGrassmannian.NuclearQuasiphononSuperGrassmannian.chiralMode B C +
          InfoGeometry.SuperGrassmannian.NuclearQuasiphononSuperGrassmannian.volumeMode A D) =
      ((Fintype.card ι₀ : ℝ) - (Fintype.card ι₁ : ℝ)) * σ ∧
    InfoGeometry.SuperGrassmannian.NuclearQuasiphononSuperGrassmannian.superTrace
        (InfoGeometry.SuperGrassmannian.NuclearQuasiphononSuperGrassmannian.chiralMode B C *
          InfoGeometry.SuperGrassmannian.NuclearQuasiphononSuperGrassmannian.chiralMode B C) = 0 ∧
    InfoGeometry.Physics.NuclearFeshbachReduction.effectiveHamiltonian
        (InfoGeometry.Algebra.BdGSchurBerezinianCompatibility.blockProjectorP ι₀ ι₁ ℝ)
        (Matrix.toLinAlgEquiv'
          (InfoGeometry.SuperGrassmannian.NuclearQuasiphononSuperGrassmannian.scaleMode
              (ι₀ := ι₀) (ι₁ := ι₁) σ +
            InfoGeometry.SuperGrassmannian.NuclearQuasiphononSuperGrassmannian.chiralMode B C +
            InfoGeometry.SuperGrassmannian.NuclearQuasiphononSuperGrassmannian.volumeMode A D))
        (Matrix.toLinAlgEquiv' (Matrix.fromBlocks 0 0 0 (-D_inv))) =
      Matrix.toLinAlgEquiv'
        (Matrix.fromBlocks
          (InfoGeometry.Algebra.BdGSchurBerezinianCompatibility.blockSchurComplement
            (σ • 1 + A) B C D_inv) 0 0 0) ∧
    (let P := InfoGeometry.Algebra.BdGSchurBerezinianCompatibility.blockProjectorP ι₀ ι₁ ℝ
     let H_reg := InfoGeometry.SuperGrassmannian.NuclearQuasiphononSuperGrassmannian.susyQ V +
       InfoGeometry.SuperGrassmannian.NuclearQuasiphononSuperGrassmannian.susyQ_dag V -
       Matrix.fromBlocks (0 : Matrix ι₀ ι₀ ℝ) 0 0 1
     let H_reg' := InfoGeometry.SuperGrassmannian.NuclearQuasiphononSuperGrassmannian.susyQ V +
       InfoGeometry.SuperGrassmannian.NuclearQuasiphononSuperGrassmannian.susyQ_dag V -
       Matrix.fromBlocks (1 : Matrix ι₀ ι₀ ℝ) 0 0 0
     InfoGeometry.Physics.NuclearFeshbachReduction.effectiveHamiltonian P
         (Matrix.toLinAlgEquiv' H_reg) (1 - P) +
       InfoGeometry.Physics.NuclearFeshbachReduction.effectiveHamiltonian (1 - P)
         (Matrix.toLinAlgEquiv' H_reg') P =
       Matrix.toLinAlgEquiv'
         (InfoGeometry.SuperGrassmannian.NuclearQuasiphononSuperGrassmannian.susyH V)) ∧
    InfoGeometry.Synthesis.SuperGrassmannianFiveGradedColorSupersymmetrySynthesis.superBerezinian23
        (A₁ * A₂) (D₁ * D₂) =
      InfoGeometry.Synthesis.SuperGrassmannianFiveGradedColorSupersymmetrySynthesis.superBerezinian23 A₁ D₁ *
        InfoGeometry.Synthesis.SuperGrassmannianFiveGradedColorSupersymmetrySynthesis.superBerezinian23 A₂ D₂ ∧
    InfoGeometry.Synthesis.SuperGrassmannianFiveGradedColorSupersymmetrySynthesis.superBerezinian23
        (InfoGeometry.Synthesis.SuperGrassmannianFiveGradedColorSupersymmetrySynthesis.leptonWeylScaleMatrix
          lam invLam * A_bos) (U_C * D_fer) =
      InfoGeometry.Synthesis.SuperGrassmannianFiveGradedColorSupersymmetrySynthesis.superBerezinian23 A_bos D_fer ∧
    InfoGeometry.Synthesis.SuperGrassmannianFiveGradedColorSupersymmetrySynthesis.superTrace23
        A_bos (D_fer + M_color.1) =
      InfoGeometry.Synthesis.SuperGrassmannianFiveGradedColorSupersymmetrySynthesis.superTrace23 A_bos D_fer ∧
    Real.log (InfoGeometry.Synthesis.SuperGrassmannianFiveGradedColorSupersymmetrySynthesis.superBerezinian23 A₁ D₁) = 0 := by
  have hber :=
    InfoGeometry.Synthesis.SuperGrassmannianFiveGradedColorSupersymmetrySynthesis.super_berezinian_gauge_invariance
      A₁ A₂ A_bos D₁ D₂ D_fer U_C M_color lam invLam h_weyl h_color_det h_match_det hD₁_ne
  exact ⟨superTrace_ospToSuperBlock3 X,
    InfoGeometry.SuperGrassmannian.NuclearQuasiphononSuperGrassmannian.total_deformation_superTrace
      σ B C A D hvol,
    InfoGeometry.SuperGrassmannian.NuclearQuasiphononSuperGrassmannian.superTrace_chiralSquare B C,
    InfoGeometry.SuperGrassmannian.NuclearQuasiphononSuperGrassmannian.deformationTriad_feshbach_eq_schurComplement
      σ A B C D D_inv,
    InfoGeometry.SuperGrassmannian.NuclearQuasiphononSuperGrassmannian.susyH_eq_sum_feshbach V,
    hber.1, hber.2.1, hber.2.2.1, hber.2.2.2⟩

end

end InfoGeometry.Synthesis.NuclearFiveGradeSuperGrassmannianIntertwiner
