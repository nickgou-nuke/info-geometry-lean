/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib
import InfoGeometry.Canonical.ZornColorConfinementBaryonBridge
import InfoGeometry.Physics.Cl55WignerSU4Embedding
import InfoGeometry.Physics.QCDColorCARAnyonBridge
import InfoGeometry.Physics.ColorIsospinCharge
import InfoGeometry.Physics.ZornMatrixSU3
import InfoGeometry.Physics.ParafermionDefectBridge
import InfoGeometry.Physics.BogoliubovSU3ParafermionWeld
import InfoGeometry.Physics.BogoliubovSU3ParafermionProofChain
import InfoGeometry.Physics.ThreeStrandJonesRecoupling
import InfoGeometry.Algebra.FibonacciParafermion
import InfoGeometry.Canonical.FibonacciParafermionFusionBridge
import InfoGeometry.Categorical.Z3Parafermion
import InfoGeometry.Canonical.Z3TrialityCapstone
import InfoGeometry.Physics.QCDTwelveFoldSchurTrialityBridge
import InfoGeometry.Physics.NuclearExceptionalArtinGaloisBridge
import InfoGeometry.Physics.QCDArchitectureSynthesis

/-!
# Seam B Synthesis: Color Tripling, Zorn Confinement, Braided Parafermions & Conditional 4D QCD

This synthesis module reconciles and interconnects the Seam B carriers without silently collapsing
distinct types:

1. **Zorn-to-Zorn Equivalence & `ZornMatrixSU3` Defect Operator**:
   Explicit `ℝ`-linear, multiplication-preserving, and norm-preserving equivalence
   `zornGaugedEquivSU3 : GaugedZornDiracKahler.ZornMatrix ℝ ≃ₗ[ℝ] ZornMatrixSU3.ZornMatrix`,
   mapping `baryonState u v w` to `⟨0, scalarTriple u v w, 0, 0⟩`, together with
   `ZornMatrixSU3.gradingOperator` realized as a constructive `TopologicalDefectOperator`
   (`op ^ 3 = op`).
2. **Color & Isospin Idempotent Partitions → `Z₃` Parafermion `TopologicalDefectOperator` & Drazin**:
   `colorSectorTripotent := colorQuarkTripletProj - colorDiquarkAntitripletProj : MatStage 5`
   is a `TopologicalDefectOperator (MatStage 5)` whose `drazin_projector` satisfies
   `colorSU3Casimir = (4 / 3 : ℝ) • drazin_projector colorSectorTripotent` and whose
   `proj_vacancy` stabilizes `zornBaryonToCl55Singlet`. Generically in `ColorIsospinCharge`,
   `isospinTripotent` and `colorPolyTripotent` realize `TopologicalDefectOperator A` and satisfy
   `charge6 a b c u v = number a b c + (3 : ℕ) • isospinTripotent u v`, instantiated on both
   `MatStage 5` and `SpinPair` (alongside Wigner `SU(4)` Casimir `15/4 ≠ 33/16` and spin-orbit
   breaking).
3. **Zorn Baryon Singlet → `ColorSpinor4 ParafermionStage4` (`CuntzAlg ℂ (Fin 4)`)**:
   `zornBaryonSingletToColorSpinor4` embeds `GaugedZornDiracKahler.ZornMatrix ℝ` into the
   singlet slot of `ColorSpinor4 ParafermionStage4`, annihilated by `colorLieAction4 A` for all
   `A : M3C` and equivariant under `frameBraid4 F`, coexisting with `QCDColorCARAnyonBridge`.
4. **Real `FibonacciParafermion` → `FusionState` → `ThreeStrandState` Intertwiner**:
   `realSpinorToFusionState` intertwines `F_action a b` with `fibonacciFusionMatrix (a : ℂ) (b : ℂ)`,
   and `fusionStateToThreeStrand` intertwines `fusionProjector12` with `e12`, sending
   `WeylPlusProjector` into the `e12 = 1` singlet channel and `WeylMinusProjector` into `ker e12`
   while keeping `threeStrandB3Representation` (`q = I`) distinct from the Fibonacci `φ`-channel.
   `FibonacciParafermion.sl₂H` also constructs a `TopologicalDefectOperator (Matrix (Fin 2) (Fin 2) ℝ)`
   linked to `Z3TrialityCapstone`.
5. **Artin 12-Fold Monodromy, `G₂` Cyclotomic/Schur-Complement & `QCDArchitectureSynthesis`**:
   Packaged via `ColorParafermionMorphismPacket` (`Type*`) and standalone compatibility theorems,
   plus explicit non-commutativity witnesses on all matrix/operator carriers.
6. **Conditional 4D Continuum QCD Confinement & Mass Gap**:
   Explicit hypothesis-parameterized `Type*` structures `ContinuumQCDConfinementHypothesis` and
   `DynamicalQCDConfinementBridge` with constructive finite model witnesses and nontrivial
   conditional theorems combining finite algebraic Casimir/Zorn/monodromy laws with continuum axioms.
-/

set_option autoImplicit false

noncomputable section

namespace InfoGeometry.Synthesis.QCDColorConfinementParafermionSynthesis

open InfoGeometry.Clifford.Cl11TensorTower (MatStage)
open InfoGeometry.Canonical
open InfoGeometry.Canonical.GaugedZornDiracKahler (Vec3 dot3 cross3)
open InfoGeometry.Canonical.ZornColorConfinementBaryon
open InfoGeometry.Physics.Cl55SpinorCartanFock
open InfoGeometry.Physics.Cl55WignerSU4Embedding
open InfoGeometry.Physics.QCDColorCARAnyonBridge
open InfoGeometry.Physics.ColorIsospinCharge
open InfoGeometry.Physics.ColorOccupationPolynomials
open ChiralTensorRecoupling (SpinPair)
open InfoGeometry.Categorical.Z3Parafermion
open InfoGeometry.Physics.BogoliubovSU3ParafermionWeld
open InfoGeometry.Physics.BogoliubovSU3ParafermionProofChain
open InfoGeometry.Physics.ThreeStrandJonesRecoupling
open InfoGeometry.Canonical.FibonacciParafermionFusionBridge
open InfoGeometry.Canonical.Z3TrialityCapstone
open InfoGeometry.Physics.QCDTwelveFoldSchurTrialityBridge
open InfoGeometry.Physics.NuclearExceptionalArtinGaloisBridge
open InfoGeometry.Physics.QCDArchitectureSynthesis
open InfoGeometry.Exceptional.ArtinOperators
open InfoGeometry.Physics.B3PresentedGroup
open scoped Matrix Kronecker

/-! ## Section 1: Explicit Zorn-to-Zorn Equivalence & `ZornMatrixSU3` Defect Operator -/

section ZornEquivalence

scoped instance instZeroGaugedZornReal :
    Zero (GaugedZornDiracKahler.ZornMatrix ℝ) :=
  ⟨GaugedZornDiracKahler.ZornMatrix.zero⟩

scoped instance instAddGaugedZornReal :
    Add (GaugedZornDiracKahler.ZornMatrix ℝ) :=
  ⟨GaugedZornDiracKahler.ZornMatrix.add⟩

scoped instance instNegGaugedZornReal :
    Neg (GaugedZornDiracKahler.ZornMatrix ℝ) :=
  ⟨fun X => ⟨-X.a, -X.b, -X.u, -X.v⟩⟩

scoped instance instSMulGaugedZornReal :
    SMul ℝ (GaugedZornDiracKahler.ZornMatrix ℝ) :=
  ⟨GaugedZornDiracKahler.ZornMatrix.smul⟩

scoped instance instSubGaugedZornReal :
    Sub (GaugedZornDiracKahler.ZornMatrix ℝ) :=
  ⟨GaugedZornDiracKahler.ZornMatrix.sub⟩

scoped instance instAddCommGroupGaugedZornReal :
    AddCommGroup (GaugedZornDiracKahler.ZornMatrix ℝ) where
  add := GaugedZornDiracKahler.ZornMatrix.add
  zero := GaugedZornDiracKahler.ZornMatrix.zero
  neg := fun X => ⟨-X.a, -X.b, -X.u, -X.v⟩
  sub := GaugedZornDiracKahler.ZornMatrix.sub
  nsmul := nsmulRec
  zsmul := zsmulRec
  add_assoc X Y Z := by
    change GaugedZornDiracKahler.ZornMatrix.add
        (GaugedZornDiracKahler.ZornMatrix.add X Y) Z =
      GaugedZornDiracKahler.ZornMatrix.add X
        (GaugedZornDiracKahler.ZornMatrix.add Y Z)
    apply GaugedZornDiracKahler.ZornMatrix.ext <;>
      dsimp [GaugedZornDiracKahler.ZornMatrix.add] <;>
      simp only [add_assoc]
  zero_add X := by
    change GaugedZornDiracKahler.ZornMatrix.add
        GaugedZornDiracKahler.ZornMatrix.zero X = X
    apply GaugedZornDiracKahler.ZornMatrix.ext <;>
      dsimp [GaugedZornDiracKahler.ZornMatrix.zero, GaugedZornDiracKahler.ZornMatrix.add] <;>
      simp only [zero_add]
  add_zero X := by
    change GaugedZornDiracKahler.ZornMatrix.add
        X GaugedZornDiracKahler.ZornMatrix.zero = X
    apply GaugedZornDiracKahler.ZornMatrix.ext <;>
      dsimp [GaugedZornDiracKahler.ZornMatrix.zero, GaugedZornDiracKahler.ZornMatrix.add] <;>
      simp only [add_zero]
  neg_add_cancel X := by
    change GaugedZornDiracKahler.ZornMatrix.add
        ⟨-X.a, -X.b, -X.u, -X.v⟩ X = GaugedZornDiracKahler.ZornMatrix.zero
    apply GaugedZornDiracKahler.ZornMatrix.ext <;>
      dsimp [GaugedZornDiracKahler.ZornMatrix.zero, GaugedZornDiracKahler.ZornMatrix.add] <;>
      simp only [neg_add_cancel]
  sub_eq_add_neg X Y := by
    change GaugedZornDiracKahler.ZornMatrix.sub X Y =
      GaugedZornDiracKahler.ZornMatrix.add X ⟨-Y.a, -Y.b, -Y.u, -Y.v⟩
    apply GaugedZornDiracKahler.ZornMatrix.ext <;>
      dsimp [GaugedZornDiracKahler.ZornMatrix.sub, GaugedZornDiracKahler.ZornMatrix.add] <;>
      simp only [sub_eq_add_neg]
  add_comm X Y := by
    change GaugedZornDiracKahler.ZornMatrix.add X Y =
      GaugedZornDiracKahler.ZornMatrix.add Y X
    apply GaugedZornDiracKahler.ZornMatrix.ext <;>
      dsimp [GaugedZornDiracKahler.ZornMatrix.add] <;>
      simp only [add_comm]

scoped instance instModuleGaugedZornReal :
    Module ℝ (GaugedZornDiracKahler.ZornMatrix ℝ) where
  one_smul X := by
    change GaugedZornDiracKahler.ZornMatrix.smul 1 X = X
    apply GaugedZornDiracKahler.ZornMatrix.ext <;>
      dsimp [GaugedZornDiracKahler.ZornMatrix.smul] <;>
      simp only [one_mul, one_smul]
  mul_smul r s X := by
    change GaugedZornDiracKahler.ZornMatrix.smul (r * s) X =
      GaugedZornDiracKahler.ZornMatrix.smul r (GaugedZornDiracKahler.ZornMatrix.smul s X)
    apply GaugedZornDiracKahler.ZornMatrix.ext <;>
      dsimp [GaugedZornDiracKahler.ZornMatrix.smul] <;>
      simp only [mul_assoc, mul_smul]
  smul_zero r := by
    change GaugedZornDiracKahler.ZornMatrix.smul r
        GaugedZornDiracKahler.ZornMatrix.zero =
      GaugedZornDiracKahler.ZornMatrix.zero
    apply GaugedZornDiracKahler.ZornMatrix.ext <;>
      dsimp [GaugedZornDiracKahler.ZornMatrix.smul, GaugedZornDiracKahler.ZornMatrix.zero] <;>
      simp only [mul_zero, smul_zero]
  smul_add r X Y := by
    change GaugedZornDiracKahler.ZornMatrix.smul r
        (GaugedZornDiracKahler.ZornMatrix.add X Y) =
      GaugedZornDiracKahler.ZornMatrix.add
        (GaugedZornDiracKahler.ZornMatrix.smul r X)
        (GaugedZornDiracKahler.ZornMatrix.smul r Y)
    apply GaugedZornDiracKahler.ZornMatrix.ext <;>
      dsimp [GaugedZornDiracKahler.ZornMatrix.smul, GaugedZornDiracKahler.ZornMatrix.add] <;>
      simp only [mul_add, smul_add]
  add_smul r s X := by
    change GaugedZornDiracKahler.ZornMatrix.smul (r + s) X =
      GaugedZornDiracKahler.ZornMatrix.add
        (GaugedZornDiracKahler.ZornMatrix.smul r X)
        (GaugedZornDiracKahler.ZornMatrix.smul s X)
    apply GaugedZornDiracKahler.ZornMatrix.ext <;>
      dsimp [GaugedZornDiracKahler.ZornMatrix.smul, GaugedZornDiracKahler.ZornMatrix.add] <;>
      simp only [add_mul, add_smul]
  zero_smul X := by
    change GaugedZornDiracKahler.ZornMatrix.smul 0 X =
      GaugedZornDiracKahler.ZornMatrix.zero
    apply GaugedZornDiracKahler.ZornMatrix.ext <;>
      dsimp [GaugedZornDiracKahler.ZornMatrix.smul, GaugedZornDiracKahler.ZornMatrix.zero] <;>
      simp only [zero_mul, zero_smul]

/-- Explicit `ℝ`-linear equivalence between the gauged Dirac–Kähler Zorn carrier and
    `InfoGeometry.Physics.ZornMatrixSU3.ZornMatrix`. -/
def zornGaugedEquivSU3 :
    GaugedZornDiracKahler.ZornMatrix ℝ ≃ₗ[ℝ]
      InfoGeometry.Physics.ZornMatrixSU3.ZornMatrix where
  toFun X := ⟨X.a, X.b, X.u, X.v⟩
  invFun M := ⟨M.a, M.b, M.x, M.y⟩
  left_inv X := by cases X; rfl
  right_inv M := by cases M; rfl
  map_add' X Y := by rfl
  map_smul' r X := by rfl

private theorem zornGaugedEquivSU3_apply (X : GaugedZornDiracKahler.ZornMatrix ℝ) :
    zornGaugedEquivSU3 X = ⟨X.a, X.b, X.u, X.v⟩ := rfl

theorem zornGaugedEquivSU3_mul (X Y : GaugedZornDiracKahler.ZornMatrix ℝ) :
    zornGaugedEquivSU3 (GaugedZornDiracKahler.ZornMatrix.zornMul X Y) =
      zornGaugedEquivSU3 X * zornGaugedEquivSU3 Y := by
  simp only [zornGaugedEquivSU3_apply]
  ext i
  · dsimp [GaugedZornDiracKahler.ZornMatrix.zornMul,
      InfoGeometry.Physics.ZornMatrixSU3.mul,
      InfoGeometry.Physics.ZornMatrixSU3.dotProduct, dot3,
      InfoGeometry.Canonical.ZornVectorMatrixExplicit.dot3]
  · dsimp [GaugedZornDiracKahler.ZornMatrix.zornMul,
      InfoGeometry.Physics.ZornMatrixSU3.mul,
      InfoGeometry.Physics.ZornMatrixSU3.dotProduct, dot3,
      InfoGeometry.Canonical.ZornVectorMatrixExplicit.dot3]
  · fin_cases i <;>
      dsimp [GaugedZornDiracKahler.ZornMatrix.zornMul,
        InfoGeometry.Physics.ZornMatrixSU3.mul,
        InfoGeometry.Physics.ZornMatrixSU3.crossProduct, cross3,
        InfoGeometry.Canonical.ZornVectorMatrixExplicit.cross3]
  · fin_cases i <;>
      dsimp [GaugedZornDiracKahler.ZornMatrix.zornMul,
        InfoGeometry.Physics.ZornMatrixSU3.mul,
        InfoGeometry.Physics.ZornMatrixSU3.crossProduct, cross3,
        InfoGeometry.Canonical.ZornVectorMatrixExplicit.cross3]

theorem zornGaugedEquivSU3_norm (X : GaugedZornDiracKahler.ZornMatrix ℝ) :
    InfoGeometry.Physics.ZornMatrixSU3.norm (zornGaugedEquivSU3 X) =
      GaugedZornDiracKahler.ZornMatrix.norm X := by
  simp only [zornGaugedEquivSU3_apply]
  dsimp [InfoGeometry.Physics.ZornMatrixSU3.norm,
    GaugedZornDiracKahler.ZornMatrix.norm, InfoGeometry.Physics.ZornMatrixSU3.dotProduct,
    dot3, InfoGeometry.Canonical.ZornVectorMatrixExplicit.dot3]

theorem zornGaugedEquivSU3_baryonState (u v w : Vec3 ℝ) :
    zornGaugedEquivSU3 (baryonState u v w) =
      ⟨0, InfoGeometry.Physics.ZornMatrixSU3.scalarTriple u v w, 0, 0⟩ := by
  rw [baryonState_eq_scalar, zornGaugedEquivSU3_apply]
  ext
  · rfl
  · dsimp [InfoGeometry.Physics.ZornMatrixSU3.scalarTriple,
      InfoGeometry.Physics.ZornMatrixSU3.dotProduct, InfoGeometry.Physics.ZornMatrixSU3.crossProduct,
      dot3, cross3, InfoGeometry.Canonical.ZornVectorMatrixExplicit.dot3,
      InfoGeometry.Canonical.ZornVectorMatrixExplicit.cross3]
    ring
  · rfl
  · rfl

/-- `ZornMatrixSU3.gradingOperator` packaged as an `ℝ`-linear endomorphism. -/
def zornSU3GradingEnd : Module.End ℝ InfoGeometry.Physics.ZornMatrixSU3.ZornMatrix where
  toFun := InfoGeometry.Physics.ZornMatrixSU3.gradingOperator
  map_add' M N := by
    ext i
    · simp [InfoGeometry.Physics.ZornMatrixSU3.gradingOperator, InfoGeometry.Physics.ZornMatrixSU3.add]
    · simp [InfoGeometry.Physics.ZornMatrixSU3.gradingOperator, InfoGeometry.Physics.ZornMatrixSU3.add]
    · simp [InfoGeometry.Physics.ZornMatrixSU3.gradingOperator, InfoGeometry.Physics.ZornMatrixSU3.add]
    · simp [InfoGeometry.Physics.ZornMatrixSU3.gradingOperator, InfoGeometry.Physics.ZornMatrixSU3.add,
        add_comm]
  map_smul' r M := by
    ext i <;> simp [InfoGeometry.Physics.ZornMatrixSU3.gradingOperator,
      InfoGeometry.Physics.ZornMatrixSU3.smul]

theorem zornSU3GradingEnd_tripotent : zornSU3GradingEnd ^ 3 = zornSU3GradingEnd := by
  ext M
  · change (InfoGeometry.Physics.ZornMatrixSU3.gradingOperator
      (InfoGeometry.Physics.ZornMatrixSU3.gradingOperator
        (InfoGeometry.Physics.ZornMatrixSU3.gradingOperator M))).a =
      (InfoGeometry.Physics.ZornMatrixSU3.gradingOperator M).a
    rw [InfoGeometry.Physics.ZornMatrixSU3.grading_tripotent]
  · change (InfoGeometry.Physics.ZornMatrixSU3.gradingOperator
      (InfoGeometry.Physics.ZornMatrixSU3.gradingOperator
        (InfoGeometry.Physics.ZornMatrixSU3.gradingOperator M))).b =
      (InfoGeometry.Physics.ZornMatrixSU3.gradingOperator M).b
    rw [InfoGeometry.Physics.ZornMatrixSU3.grading_tripotent]
  · change (InfoGeometry.Physics.ZornMatrixSU3.gradingOperator
      (InfoGeometry.Physics.ZornMatrixSU3.gradingOperator
        (InfoGeometry.Physics.ZornMatrixSU3.gradingOperator M))).x _ =
      (InfoGeometry.Physics.ZornMatrixSU3.gradingOperator M).x _
    rw [InfoGeometry.Physics.ZornMatrixSU3.grading_tripotent]
  · change (InfoGeometry.Physics.ZornMatrixSU3.gradingOperator
      (InfoGeometry.Physics.ZornMatrixSU3.gradingOperator
        (InfoGeometry.Physics.ZornMatrixSU3.gradingOperator M))).y _ =
      (InfoGeometry.Physics.ZornMatrixSU3.gradingOperator M).y _
    rw [InfoGeometry.Physics.ZornMatrixSU3.grading_tripotent]

/-- Constructive `Z₃` parafermion `TopologicalDefectOperator` from `ZornMatrixSU3.gradingOperator`. -/
def zornSU3GradingDefectOperator :
    InfoGeometry.Physics.TopologicalDefectOperator
      (Module.End ℝ InfoGeometry.Physics.ZornMatrixSU3.ZornMatrix) where
  op := zornSU3GradingEnd
  is_parafermionic := zornSU3GradingEnd_tripotent

theorem zornSU3GradingEnd_projectors_apply (M : InfoGeometry.Physics.ZornMatrixSU3.ZornMatrix) :
    proj_up zornSU3GradingEnd M = ⟨0, 0, M.x, 0⟩ ∧
    proj_down zornSU3GradingEnd M = ⟨0, 0, 0, M.y⟩ ∧
    proj_vacancy zornSU3GradingEnd M = ⟨M.a, M.b, 0, 0⟩ := by
  have hsq : (zornSU3GradingEnd ^ 2) M = ⟨0, 0, M.x, M.y⟩ := by
    change InfoGeometry.Physics.ZornMatrixSU3.gradingOperator
      (InfoGeometry.Physics.ZornMatrixSU3.gradingOperator M) = ⟨0, 0, M.x, M.y⟩
    exact InfoGeometry.Physics.ZornMatrixSU3.grading_sq M
  have h1 : zornSU3GradingEnd M = ⟨0, 0, M.x, -M.y⟩ := rfl
  refine ⟨?_, ?_, ?_⟩
  · change (1 / 2 : ℝ) • ((zornSU3GradingEnd ^ 2) M + zornSU3GradingEnd M) = ⟨0, 0, M.x, 0⟩
    rw [hsq, h1]
    ext i <;> simp [InfoGeometry.Physics.ZornMatrixSU3.add,
      InfoGeometry.Physics.ZornMatrixSU3.smul]
    all_goals ring
  · change (1 / 2 : ℝ) • ((zornSU3GradingEnd ^ 2) M - zornSU3GradingEnd M) = ⟨0, 0, 0, M.y⟩
    rw [hsq, h1]
    ext i <;> simp [sub_eq_add_neg, InfoGeometry.Physics.ZornMatrixSU3.add,
      InfoGeometry.Physics.ZornMatrixSU3.neg, InfoGeometry.Physics.ZornMatrixSU3.smul]
    all_goals ring
  · change M - (zornSU3GradingEnd ^ 2) M = ⟨M.a, M.b, 0, 0⟩
    rw [hsq]
    ext i <;> simp [sub_eq_add_neg, InfoGeometry.Physics.ZornMatrixSU3.add,
      InfoGeometry.Physics.ZornMatrixSU3.neg]

theorem zornSU3GradingEnd_ne_zero : zornSU3GradingEnd ≠ 0 := by
  intro h
  let M : InfoGeometry.Physics.ZornMatrixSU3.ZornMatrix := ⟨0, 0, ![1, 0, 0], 0⟩
  have h0 := congrArg (fun T => (T M).x 0) h
  simp [zornSU3GradingEnd, InfoGeometry.Physics.ZornMatrixSU3.gradingOperator, M] at h0

theorem zornSU3GradingEnd_sq_ne_self : zornSU3GradingEnd ^ 2 ≠ zornSU3GradingEnd := by
  intro h
  let M : InfoGeometry.Physics.ZornMatrixSU3.ZornMatrix := ⟨0, 0, 0, ![1, 0, 0]⟩
  have hsq : (zornSU3GradingEnd ^ 2) M = ⟨0, 0, M.x, M.y⟩ := by
    change InfoGeometry.Physics.ZornMatrixSU3.gradingOperator
      (InfoGeometry.Physics.ZornMatrixSU3.gradingOperator M) = ⟨0, 0, M.x, M.y⟩
    exact InfoGeometry.Physics.ZornMatrixSU3.grading_sq M
  have h0 := congrArg (fun T => (T M).y 0) h
  have h1 : zornSU3GradingEnd M = ⟨0, 0, M.x, -M.y⟩ := rfl
  rw [hsq, h1] at h0
  simp [M] at h0
  norm_num at h0

theorem zornSU3GradingEnd_proj_up_ne_zero : proj_up zornSU3GradingEnd ≠ 0 := by
  intro h
  let M : InfoGeometry.Physics.ZornMatrixSU3.ZornMatrix := ⟨0, 0, ![1, 0, 0], 0⟩
  have h0 := congrArg (fun T => (T M).x 0) h
  rw [(zornSU3GradingEnd_projectors_apply M).1] at h0
  simp [M] at h0

theorem zornSU3GradingEnd_proj_vacancy_ne_zero : proj_vacancy zornSU3GradingEnd ≠ 0 := by
  intro h
  let M : InfoGeometry.Physics.ZornMatrixSU3.ZornMatrix := ⟨1, 0, 0, 0⟩
  have h0 := congrArg (fun T => (T M).a) h
  rw [(zornSU3GradingEnd_projectors_apply M).2.2] at h0
  simp [M] at h0

end ZornEquivalence

/-! ## Section 2: Color & Isospin Idempotent Partitions → `Z₃` Parafermions & Drazin Projector -/

section ColorParafermionDrazin

/-- The `MatStage 5` color sector tripotent `Π_quark - Π_diquark` (`3 - 3̄`). -/
def colorSectorTripotent : MatStage 5 :=
  colorQuarkTripletProj - colorDiquarkAntitripletProj

private theorem colorSectorTripotent_sq :
    colorSectorTripotent * colorSectorTripotent =
      colorQuarkTripletProj + colorDiquarkAntitripletProj := by
  rcases cl55_color_isospin_orthogonal_idempotents with
    ⟨⟨_, hQ, hD, _⟩, ⟨_, _, _, hQD, _, _⟩, _, _⟩
  have hDQ : colorDiquarkAntitripletProj * colorQuarkTripletProj = 0 := by
    have hcol := color_orthogonal_idempotent_partition
      (modeOccupied_idem 0) (modeOccupied_idem 1) (modeOccupied_idem 2)
      (modeOccupied_comm 0 1) (modeOccupied_comm 0 2) (modeOccupied_comm 1 2)
    rcases cl55_colorOccupationPolynomials_instantiation with ⟨_, _, hq, hd, _⟩
    rw [hq, hd] at hcol
    rcases hcol with ⟨_, ⟨_, _, _, _, _, _, _, h21, _, _, _, _⟩, _⟩
    exact h21
  dsimp [colorSectorTripotent]
  calc
    (colorQuarkTripletProj - colorDiquarkAntitripletProj) *
        (colorQuarkTripletProj - colorDiquarkAntitripletProj) =
      colorQuarkTripletProj * colorQuarkTripletProj -
        colorQuarkTripletProj * colorDiquarkAntitripletProj -
        colorDiquarkAntitripletProj * colorQuarkTripletProj +
        colorDiquarkAntitripletProj * colorDiquarkAntitripletProj := by noncomm_ring
    _ = colorQuarkTripletProj + colorDiquarkAntitripletProj := by
      rw [hQ, hQD, hDQ, hD]; abel

theorem colorSectorTripotent_tripotent :
    colorSectorTripotent ^ 3 = colorSectorTripotent := by
  rcases cl55_color_isospin_orthogonal_idempotents with
    ⟨⟨_, hQ, hD, _⟩, ⟨_, _, _, hQD, _, _⟩, _, _⟩
  have hDQ : colorDiquarkAntitripletProj * colorQuarkTripletProj = 0 := by
    have hcol := color_orthogonal_idempotent_partition
      (modeOccupied_idem 0) (modeOccupied_idem 1) (modeOccupied_idem 2)
      (modeOccupied_comm 0 1) (modeOccupied_comm 0 2) (modeOccupied_comm 1 2)
    rcases cl55_colorOccupationPolynomials_instantiation with ⟨_, _, hq, hd, _⟩
    rw [hq, hd] at hcol
    rcases hcol with ⟨_, ⟨_, _, _, _, _, _, _, h21, _, _, _, _⟩, _⟩
    exact h21
  calc
    colorSectorTripotent ^ 3 =
        (colorSectorTripotent * colorSectorTripotent) * colorSectorTripotent := by
      rw [pow_succ, pow_two]
    _ = (colorQuarkTripletProj + colorDiquarkAntitripletProj) *
        (colorQuarkTripletProj - colorDiquarkAntitripletProj) := by
      rw [colorSectorTripotent_sq]; rfl
    _ = colorQuarkTripletProj * colorQuarkTripletProj -
        colorQuarkTripletProj * colorDiquarkAntitripletProj +
        colorDiquarkAntitripletProj * colorQuarkTripletProj -
        colorDiquarkAntitripletProj * colorDiquarkAntitripletProj := by noncomm_ring
    _ = colorQuarkTripletProj - colorDiquarkAntitripletProj := by
      rw [hQ, hQD, hDQ, hD]; abel

/-- Constructive `TopologicalDefectOperator (MatStage 5)` for the color `3 ⊕ 3̄` sector. -/
def colorSectorDefectOperator :
    InfoGeometry.Physics.TopologicalDefectOperator (MatStage 5) where
  op := colorSectorTripotent
  is_parafermionic := colorSectorTripotent_tripotent

theorem colorSectorTripotent_projectors :
    proj_up colorSectorTripotent = colorQuarkTripletProj ∧
    proj_down colorSectorTripotent = colorDiquarkAntitripletProj ∧
    proj_vacancy colorSectorTripotent = colorBaryonSingletProj + colorVacuumSingletProj ∧
    drazin_projector colorSectorTripotent = colorQuarkTripletProj + colorDiquarkAntitripletProj := by
  have hsq : colorSectorTripotent ^ 2 = colorQuarkTripletProj + colorDiquarkAntitripletProj := by
    rw [pow_two, colorSectorTripotent_sq]
  have hsum : colorBaryonSingletProj + colorQuarkTripletProj +
      colorDiquarkAntitripletProj + colorVacuumSingletProj = 1 :=
    color_singlet_triplet_four_sector_sum.1
  refine ⟨?_, ?_, ?_, ?_⟩
  · dsimp [proj_up, InfoGeometry.Canonical.FibonacciParafermionAtoms.proj_up]
    rw [hsq]
    dsimp [colorSectorTripotent]
    rw [show (colorQuarkTripletProj + colorDiquarkAntitripletProj) +
        (colorQuarkTripletProj - colorDiquarkAntitripletProj) =
        (2 : ℝ) • colorQuarkTripletProj by rw [two_smul]; abel]
    rw [smul_smul]; norm_num
  · dsimp [proj_down, InfoGeometry.Canonical.FibonacciParafermionAtoms.proj_down]
    rw [hsq]
    dsimp [colorSectorTripotent]
    rw [show (colorQuarkTripletProj + colorDiquarkAntitripletProj) -
        (colorQuarkTripletProj - colorDiquarkAntitripletProj) =
        (2 : ℝ) • colorDiquarkAntitripletProj by rw [two_smul]; abel]
    rw [smul_smul]; norm_num
  · dsimp [proj_vacancy, InfoGeometry.Canonical.FibonacciParafermionAtoms.proj_vacancy]
    rw [hsq, ← hsum]
    abel
  · dsimp [drazin_projector, InfoGeometry.Canonical.FibonacciParafermionAtoms.drazin_projector]
    exact hsq

theorem colorSU3Casimir_eq_smul_drazin :
    colorSU3Casimir = (4 / 3 : ℝ) • drazin_projector colorSectorTripotent := by
  have hcas := (cl55_full_su3_gluon_neutrality_and_casimir 0 1 0 1 (by decide)).2.2.2.1
  rw [hcas, colorSectorTripotent_projectors.2.2.2]

theorem colorSU3Casimir_mul_proj_vacancy :
    colorSU3Casimir * proj_vacancy colorSectorTripotent = 0 := by
  rw [colorSU3Casimir_eq_smul_drazin, smul_mul_assoc,
    drazin_orthogonal_vacancy colorSectorTripotent colorSectorTripotent_tripotent, smul_zero]

theorem zornBaryon_lives_in_parafermion_vacancy (X : GaugedZornDiracKahler.ZornMatrix ℝ) :
    proj_vacancy colorSectorTripotent * zornBaryonToCl55Singlet X = zornBaryonToCl55Singlet X ∧
    colorSU3Casimir * zornBaryonToCl55Singlet X = 0 := by
  rcases cl55_color_isospin_orthogonal_idempotents with ⟨⟨_, _, _, hB⟩, _, _, _⟩
  have hVB : colorVacuumSingletProj * colorBaryonSingletProj = 0 := by
    have hcol := color_orthogonal_idempotent_partition
      (modeOccupied_idem 0) (modeOccupied_idem 1) (modeOccupied_idem 2)
      (modeOccupied_comm 0 1) (modeOccupied_comm 0 2) (modeOccupied_comm 1 2)
    rcases cl55_colorOccupationPolynomials_instantiation with ⟨hb, hv, _⟩
    rw [hb, hv] at hcol
    exact hcol.2.1.2.2.1
  have hcasB : colorSU3Casimir * colorBaryonSingletProj = 0 :=
    (cl55_full_su3_gluon_neutrality_and_casimir 0 1 0 1 (by decide)).2.2.2.2.2.2.1
  refine ⟨?_, ?_⟩
  · rw [colorSectorTripotent_projectors.2.2.1]
    dsimp [zornBaryonToCl55Singlet]
    rw [mul_smul_comm, add_mul, hB, hVB, add_zero]
  · dsimp [zornBaryonToCl55Singlet]
    rw [mul_smul_comm, hcasB, smul_zero]

theorem matStage5_ne_zero_of_trace_ne_zero {M : MatStage 5} (h : Matrix.trace M ≠ 0) :
    M ≠ 0 := by
  intro h0
  apply h
  rw [h0, Matrix.trace_zero]

theorem matStage5_diag_exists_ne_zero_of_trace_ne_zero {M : MatStage 5} (h : Matrix.trace M ≠ 0) :
    ∃ i : InfoGeometry.Clifford.TowerMatrix.Idx 5, M i i ≠ 0 := by
  by_contra hall
  push Not at hall
  apply h
  simp [Matrix.trace, hall]

theorem colorBaryonSingletProj_ne_zero : colorBaryonSingletProj ≠ 0 := by
  apply matStage5_ne_zero_of_trace_ne_zero
  rw [trace_colorFourSectors_cl55.2.2.2]
  norm_num

theorem colorSectorTripotent_ne_zero : colorSectorTripotent ≠ 0 := by
  intro h0
  have htr : Matrix.trace colorSectorTripotent = 0 := by rw [h0, Matrix.trace_zero]
  have hdiff : Matrix.trace colorSectorTripotent =
      Matrix.trace colorQuarkTripletProj - Matrix.trace colorDiquarkAntitripletProj := by
    dsimp [colorSectorTripotent]
    exact Matrix.trace_sub _ _
  rcases cl55_color_isospin_orthogonal_idempotents with ⟨⟨_, hQ, _, _⟩, _, _, _⟩
  have hDQ : colorDiquarkAntitripletProj * colorQuarkTripletProj = 0 := by
    have hcol := color_orthogonal_idempotent_partition
      (modeOccupied_idem 0) (modeOccupied_idem 1) (modeOccupied_idem 2)
      (modeOccupied_comm 0 1) (modeOccupied_comm 0 2) (modeOccupied_comm 1 2)
    rcases cl55_colorOccupationPolynomials_instantiation with ⟨_, _, hq, hd, _⟩
    rw [hq, hd] at hcol
    rcases hcol with ⟨_, ⟨_, _, _, _, _, _, _, h21, _, _, _, _⟩, _⟩
    exact h21
  have hmul : colorSectorTripotent * colorQuarkTripletProj = colorQuarkTripletProj := by
    dsimp [colorSectorTripotent]
    rw [sub_mul, hQ, hDQ, sub_zero]
  rw [h0, zero_mul] at hmul
  exact matStage5_ne_zero_of_trace_ne_zero (by rw [trace_colorFourSectors_cl55.2.1]; norm_num)
    hmul.symm

theorem colorSectorTripotent_sq_ne_self : colorSectorTripotent ^ 2 ≠ colorSectorTripotent := by
  intro h
  have hsq : colorSectorTripotent ^ 2 = colorQuarkTripletProj + colorDiquarkAntitripletProj := by
    rw [pow_two, colorSectorTripotent_sq]
  rw [hsq] at h
  have htr := congrArg Matrix.trace h
  dsimp [colorSectorTripotent] at htr
  rw [Matrix.trace_add, Matrix.trace_sub, trace_colorFourSectors_cl55.2.1,
    trace_colorFourSectors_cl55.2.2.1] at htr
  norm_num at htr

theorem colorSectorTripotent_proj_up_ne_zero : proj_up colorSectorTripotent ≠ 0 := by
  rw [colorSectorTripotent_projectors.1]
  exact matStage5_ne_zero_of_trace_ne_zero (by rw [trace_colorFourSectors_cl55.2.1]; norm_num)

theorem colorSectorTripotent_proj_vacancy_ne_zero : proj_vacancy colorSectorTripotent ≠ 0 := by
  rw [colorSectorTripotent_projectors.2.2.1]
  apply matStage5_ne_zero_of_trace_ne_zero
  rw [Matrix.trace_add, trace_colorFourSectors_cl55.2.2.2, trace_colorFourSectors_cl55.1]
  norm_num

/-! ### Generic `ColorIsospinCharge` Tripotents & `MatStage 5` / `SpinPair` Instantiations -/

/-- Generic isospin tripotent `isoPlus u v - isoMinus u v`. -/
def isospinTripotent {A : Type*} [Ring A] (u v : A) : A :=
  isoPlus u v - isoMinus u v

/-- Generic color polynomial tripotent `quark a b c - diquark a b c`. -/
def colorPolyTripotent {A : Type*} [Ring A] (a b c : A) : A :=
  quark a b c - diquark a b c

theorem charge6_eq_number_add_three_smul_isospinTripotent {A : Type*} [Ring A] (a b c u v : A) :
    charge6 a b c u v = number a b c + (3 : ℕ) • isospinTripotent u v :=
  rfl

theorem isospinTripotent_tripotent {A : Type*} [Ring A] {u v : A}
    (hu : u * u = u) (hv : v * v = v) (huv : u * v = v * u) :
    isospinTripotent u v ^ 3 = isospinTripotent u v := by
  rcases iso_orthogonal_idempotent_partition hu hv huv with
    ⟨⟨hQp, hQm, _⟩, ⟨hpm, _, hmp, _, _, _⟩, _⟩
  have hsq : isospinTripotent u v * isospinTripotent u v = isoPlus u v + isoMinus u v := by
    dsimp [isospinTripotent]
    calc
      (isoPlus u v - isoMinus u v) * (isoPlus u v - isoMinus u v) =
        isoPlus u v * isoPlus u v - isoPlus u v * isoMinus u v -
          isoMinus u v * isoPlus u v + isoMinus u v * isoMinus u v := by noncomm_ring
      _ = isoPlus u v + isoMinus u v := by rw [hQp, hpm, hmp, hQm]; abel
  calc
    isospinTripotent u v ^ 3 =
        (isospinTripotent u v * isospinTripotent u v) * isospinTripotent u v := by
      rw [pow_succ, pow_two]
    _ = (isoPlus u v + isoMinus u v) * (isoPlus u v - isoMinus u v) := by
      rw [hsq]; rfl
    _ = isoPlus u v * isoPlus u v - isoPlus u v * isoMinus u v +
        isoMinus u v * isoPlus u v - isoMinus u v * isoMinus u v := by noncomm_ring
    _ = isospinTripotent u v := by rw [hQp, hpm, hmp, hQm]; dsimp [isospinTripotent]; abel

/-- Constructive `TopologicalDefectOperator` for the generic `ColorIsospinCharge` isospin sector. -/
def isospinDefectOperator {A : Type*} [Ring A] [Algebra ℝ A] {u v : A}
    (hu : u * u = u) (hv : v * v = v) (huv : u * v = v * u) :
    InfoGeometry.Physics.TopologicalDefectOperator A where
  op := isospinTripotent u v
  is_parafermionic := isospinTripotent_tripotent hu hv huv

theorem colorPolyTripotent_tripotent {A : Type*} [Ring A] {a b c : A}
    (ha : a * a = a) (hb : b * b = b) (hc : c * c = c)
    (hab : a * b = b * a) (hac : a * c = c * a) (hbc : b * c = c * b) :
    colorPolyTripotent a b c ^ 3 = colorPolyTripotent a b c := by
  rcases color_orthogonal_idempotent_partition ha hb hc hab hac hbc with
    ⟨⟨_, hQ, hD, _⟩, ⟨_, _, _, _, hQD, _, _, hDQ, _, _, _, _⟩, _⟩
  have hsq : colorPolyTripotent a b c * colorPolyTripotent a b c = quark a b c + diquark a b c := by
    dsimp [colorPolyTripotent]
    calc
      (quark a b c - diquark a b c) * (quark a b c - diquark a b c) =
        quark a b c * quark a b c - quark a b c * diquark a b c -
          diquark a b c * quark a b c + diquark a b c * diquark a b c := by noncomm_ring
      _ = quark a b c + diquark a b c := by rw [hQ, hQD, hDQ, hD]; abel
  calc
    colorPolyTripotent a b c ^ 3 =
        (colorPolyTripotent a b c * colorPolyTripotent a b c) * colorPolyTripotent a b c := by
      rw [pow_succ, pow_two]
    _ = (quark a b c + diquark a b c) * (quark a b c - diquark a b c) := by
      rw [hsq]; rfl
    _ = quark a b c * quark a b c - quark a b c * diquark a b c +
        diquark a b c * quark a b c - diquark a b c * diquark a b c := by noncomm_ring
    _ = colorPolyTripotent a b c := by rw [hQ, hQD, hDQ, hD]; dsimp [colorPolyTripotent]; abel

/-- Constructive `TopologicalDefectOperator` for the generic `ColorIsospinCharge` color sector. -/
def colorPolyDefectOperator {A : Type*} [Ring A] [Algebra ℝ A] {a b c : A}
    (ha : a * a = a) (hb : b * b = b) (hc : c * c = c)
    (hab : a * b = b * a) (hac : a * c = c * a) (hbc : b * c = c * b) :
    InfoGeometry.Physics.TopologicalDefectOperator A where
  op := colorPolyTripotent a b c
  is_parafermionic := colorPolyTripotent_tripotent ha hb hc hab hac hbc

private theorem spNp_idem : spNp * spNp = spNp := by
  rcases cl55_two_mode_pn_spinpair_embedding (p := 3) (n := 4) (by decide) with
    ⟨⟨hEp2, hFp2, _, _⟩, ⟨hCARp, _⟩, _, _, _, _⟩
  dsimp [spNp]
  have h1 : spFp * spEp = 1 - spEp * spFp := eq_sub_of_add_eq' hCARp
  calc
    (spEp * spFp) * (spEp * spFp) = spEp * (spFp * spEp) * spFp := by noncomm_ring
    _ = spEp * (1 - spEp * spFp) * spFp := by rw [h1]
    _ = spEp * spFp - (spEp * spEp) * (spFp * spFp) := by noncomm_ring
    _ = spEp * spFp := by rw [hEp2, hFp2]; noncomm_ring

private theorem spNn_idem : spNn * spNn = spNn := by
  rcases cl55_two_mode_pn_spinpair_embedding (p := 3) (n := 4) (by decide) with
    ⟨⟨_, _, hEn2, hFn2⟩, ⟨_, hCARn⟩, _, _, _, _⟩
  dsimp [spNn]
  have h1 : spFn * spEn = 1 - spEn * spFn := eq_sub_of_add_eq' hCARn
  calc
    (spEn * spFn) * (spEn * spFn) = spEn * (spFn * spEn) * spFn := by noncomm_ring
    _ = spEn * (1 - spEn * spFn) * spFn := by rw [h1]
    _ = spEn * spFn - (spEn * spEn) * (spFn * spFn) := by noncomm_ring
    _ = spEn * spFn := by rw [hEn2, hFn2]; noncomm_ring

private theorem spNp_comm_spNn : spNp * spNn = spNn * spNp := by
  rcases cl55_two_mode_pn_spinpair_embedding (p := 3) (n := 4) (by decide) with
    ⟨_, _, ⟨hEpEn, hEpFn, hFpEn, hFpFn⟩, _, _, _⟩
  have h1 : spFp * spEn = -(spEn * spFp) := eq_neg_of_add_eq_zero_left hFpEn
  have h2 : spEp * spEn = -(spEn * spEp) := eq_neg_of_add_eq_zero_left hEpEn
  have h3 : spFp * spFn = -(spFn * spFp) := eq_neg_of_add_eq_zero_left hFpFn
  have h4 : spEp * spFn = -(spFn * spEp) := eq_neg_of_add_eq_zero_left hEpFn
  dsimp [spNp, spNn]
  calc
    (spEp * spFp) * (spEn * spFn) = spEp * (spFp * spEn) * spFn := by noncomm_ring
    _ = -((spEp * spEn) * (spFp * spFn)) := by rw [h1]; noncomm_ring
    _ = -((-(spEn * spEp)) * (-(spFn * spFp))) := by rw [h2, h3]
    _ = -(spEn * (spEp * spFn) * spFp) := by noncomm_ring
    _ = (spEn * spFn) * (spEp * spFp) := by rw [h4]; noncomm_ring

/-- `ColorIsospinCharge` instantiated on `MatStage 5` (`modeOccupied 0..4`) alongside
    `SpinPair` (`spNp, spNn`) and Wigner `SU(4)` Casimir / spin-orbit breaking. -/
theorem matStage5_and_spinPair_wigner_su4_packet (A : ℕ) (hA : 0 < A) (i j : Fin 3) :
    charge6 (modeOccupied 0) (modeOccupied 1) (modeOccupied 2) (modeOccupied 3) (modeOccupied 4) =
      sixElectricCharge ∧
    colorPolyTripotent (modeOccupied 0) (modeOccupied 1) (modeOccupied 2) = colorSectorTripotent ∧
    isospinTripotent (modeOccupied 3) (modeOccupied 4) ^ 3 =
      isospinTripotent (modeOccupied 3) (modeOccupied 4) ∧
    isospinTripotent spNp spNn ^ 3 = isospinTripotent spNp spNn ∧
    charge6 (0 : SpinPair) 0 0 spNp spNn = (3 : ℕ) • isospinTripotent spNp spNn ∧
    (InfoGeometry.Physics.NuclearSpinIsospinTensorRepresentation.su4Casimir =
        (15 / 4 : ℂ) • (1 : SpinPair) ∧ (15 / 4 : ℂ) ≠ (33 / 16 : ℂ)) ∧
    (collectiveLS A * collectiveT A j - collectiveT A j * collectiveLS A = 0 ∧
     collectiveLS A * collectiveY A i j - collectiveY A i j * collectiveLS A ≠ 0) := by
  have hinst := cl55_colorOccupationPolynomials_instantiation
  have hcol : colorPolyTripotent (modeOccupied 0) (modeOccupied 1) (modeOccupied 2) =
      colorSectorTripotent := by
    dsimp [colorPolyTripotent, colorSectorTripotent]
    rw [hinst.2.2.1, hinst.2.2.2.1]
  have hisoM := isospinTripotent_tripotent
    (modeOccupied_idem 3) (modeOccupied_idem 4) (modeOccupied_comm 3 4)
  have hisoS := isospinTripotent_tripotent spNp_idem spNn_idem spNp_comm_spNn
  have hchS : charge6 (0 : SpinPair) 0 0 spNp spNn = (3 : ℕ) • isospinTripotent spNp spNn := by
    simp [charge6, number, isospinTripotent]
  have hsu4 := wigner_su4_casimir_and_lie_closure 0 0 0 0 0 0
  have hls := collective_spin_orbit_preserves_isospin_breaks_su4 A hA i j
  exact ⟨hinst.2.2.2.2.2.2.2.2.2.2, hcol, hisoM, hisoS, hchS,
    ⟨hsu4.1, hsu4.2.1⟩, ⟨hls.1, hls.2.2⟩⟩

end ColorParafermionDrazin

/-! ## Section 3: Zorn Baryon Singlet → `ColorSpinor4 ParafermionStage4` Morphism -/

section ZornToColorSpinor4

/-- Linear morphism embedding the Zorn baryon scalar component `X.b` into the color-singlet
    fourth slot of `ColorSpinor4 ParafermionStage4` (`CuntzAlg ℂ (Fin 4)`). -/
def zornBaryonSingletToColorSpinor4 :
    GaugedZornDiracKahler.ZornMatrix ℝ →ₗ[ℝ]
      ColorSpinor4 InfoGeometry.Physics.BogoliubovSU3ParafermionProofChain.ParafermionStage4 where
  toFun X := (0, (X.b : ℂ) • bdgMajoranaPlusColorSpinor4.2)
  map_add' X Y := by
    ext
    · simp
    · change ((X.b + Y.b : ℝ) : ℂ) • bdgMajoranaPlusColorSpinor4.2 =
        (X.b : ℂ) • bdgMajoranaPlusColorSpinor4.2 +
          (Y.b : ℂ) • bdgMajoranaPlusColorSpinor4.2
      rw [Complex.ofReal_add, add_smul]
  map_smul' r X := by
    ext
    · simp
    · change ((r * X.b : ℝ) : ℂ) • bdgMajoranaPlusColorSpinor4.2 =
        r • ((X.b : ℂ) • bdgMajoranaPlusColorSpinor4.2)
      rw [Complex.ofReal_mul, mul_smul]
      rfl

theorem zornBaryonSingletToColorSpinor4_baryonState (u v w : Vec3 ℝ) :
    zornBaryonSingletToColorSpinor4 (baryonState u v w) =
      (0, ((dot3 (cross3 u v) w : ℝ) : ℂ) • bdgMajoranaPlusColorSpinor4.2) := by
  rw [baryonState_eq_scalar]
  rfl

theorem colorLieAction4_kills_zornBaryonSinglet
    (A : InfoGeometry.Physics.BogoliubovSU3ParafermionProofChain.M3C)
    (X : GaugedZornDiracKahler.ZornMatrix ℝ) :
    colorLieAction4 A (zornBaryonSingletToColorSpinor4 X) = 0 := by
  ext i <;> simp [colorLieAction4, zornBaryonSingletToColorSpinor4]

theorem frameBraid4_zornBaryonSinglet
    (F : InfoGeometry.Physics.BogoliubovWeylChemicalPotential.BogoliubovInertialFrame)
    (X : GaugedZornDiracKahler.ZornMatrix ℝ) :
    frameBraid4 F (zornBaryonSingletToColorSpinor4 X) =
      (0, (frameBraidingPhase F * (X.b : ℂ)) • bdgMajoranaPlusColorSpinor4.2) := by
  simp [frameBraid4, qBraid4, zornBaryonSingletToColorSpinor4, smul_smul]

private def cuntz4ShiftS (i : Fin 4) : Module.End ℂ (ℕ → ℂ) where
  toFun f n := if n % 4 = i.val then f (n / 4) else 0
  map_add' f g := by
    funext n
    simp only [Pi.add_apply]
    split_ifs <;> ring
  map_smul' c f := by
    funext n
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> ring

private def cuntz4ShiftT (i : Fin 4) : Module.End ℂ (ℕ → ℂ) where
  toFun f k := f (4 * k + i.val)
  map_add' f g := by funext k; rfl
  map_smul' c f := by funext k; rfl

theorem bdgMajoranaPlusColorSpinor4_singlet_ne_zero :
    bdgMajoranaPlusColorSpinor4.2 ≠ 0 := by
  have h_ortho : ∀ i j : Fin 4, cuntz4ShiftT i * cuntz4ShiftS j = if i = j then 1 else 0 := by
    intro i j
    apply LinearMap.ext
    intro f
    funext k
    change cuntz4ShiftS j f (4 * k + i.val) = (if i = j then (1 : Module.End ℂ (ℕ → ℂ)) else 0) f k
    have hmod : (4 * k + i.val) % 4 = i.val := by
      have hi : i.val < 4 := i.isLt
      omega
    have hdiv : (4 * k + i.val) / 4 = k := by
      have hi : i.val < 4 := i.isLt
      omega
    dsimp [cuntz4ShiftS]
    rw [hmod, hdiv]
    by_cases hij : i = j
    · subst hij; simp
    · have hij' : i.val ≠ j.val := fun h => hij (Fin.ext h)
      simp [hij, hij']
  have h_part : (∑ i : Fin 4, cuntz4ShiftS i * cuntz4ShiftT i) = 1 := by
    apply LinearMap.ext
    intro f
    funext n
    change ∑ i : Fin 4, cuntz4ShiftS i (cuntz4ShiftT i f) n = f n
    dsimp [cuntz4ShiftS, cuntz4ShiftT]
    let i0 : Fin 4 := ⟨n % 4, Nat.mod_lt n (by decide)⟩
    rw [Finset.sum_eq_single i0]
    · simp only [i0, ite_true]
      congr 1
      exact Nat.div_add_mod n 4
    · intro i _ hi
      have hne : n % 4 ≠ i.val := fun h => hi (Fin.ext h.symm)
      simp only [ite_eq_right_iff]
      intro h
      exact (hne h).elim
    · intro hmem
      exact (hmem (Finset.mem_univ i0)).elim
  let rep := InfoGeometry.Topology.AlgebraicCuntzQuotient.lift
    (R := ℂ) cuntz4ShiftS cuntz4ShiftT h_ortho h_part
  intro h0
  have hval : rep bdgMajoranaPlusColorSpinor4.2 = 0 := by rw [h0, map_zero]
  have hdef : bdgMajoranaPlusColorSpinor4.2 =
      InfoGeometry.Topology.AlgebraicCuntzQuotient.S (R := ℂ) (3 : Fin 4) +
        InfoGeometry.Topology.AlgebraicCuntzQuotient.T (R := ℂ) (3 : Fin 4) := rfl
  rw [hdef, map_add,
    InfoGeometry.Topology.AlgebraicCuntzQuotient.lift_S (R := ℂ) cuntz4ShiftS cuntz4ShiftT h_ortho h_part 3,
    InfoGeometry.Topology.AlgebraicCuntzQuotient.lift_T (R := ℂ) cuntz4ShiftS cuntz4ShiftT h_ortho h_part 3] at hval
  let δ0 : ℕ → ℂ := fun n => if n = 0 then 1 else 0
  have h3 := congrArg (fun T : Module.End ℂ (ℕ → ℂ) => T δ0 3) hval
  simp [cuntz4ShiftS, cuntz4ShiftT, δ0] at h3

theorem zornBaryonSingletToColorSpinor4_baryon_ne_zero :
    zornBaryonSingletToColorSpinor4 (baryonState colorE0 colorE1 colorE2) ≠ 0 := by
  intro h0
  have hb : (baryonState (colorE0 : Vec3 ℝ) colorE1 colorE2).b = 1 := by
    rw [baryonState_basis]
  have h2 := congrArg Prod.snd h0
  change (((baryonState (colorE0 : Vec3 ℝ) colorE1 colorE2).b : ℝ) : ℂ) •
      bdgMajoranaPlusColorSpinor4.2 = 0 at h2
  rw [hb] at h2
  simp only [Complex.ofReal_one, one_smul] at h2
  exact bdgMajoranaPlusColorSpinor4_singlet_ne_zero h2

theorem zorn_cl55_colorSpinor4_anyon_compatibility
    (F : InfoGeometry.Physics.BogoliubovWeylChemicalPotential.BogoliubovInertialFrame)
    (A : InfoGeometry.Physics.BogoliubovSU3ParafermionProofChain.M3C)
    (u v w : Vec3 ℝ) (t : ℂ) (k : Fin 3)
    (U : ZornOctonionAnyon.ZornCell.ColorGauge)
    (vC wC : Fin 3 → ℂ)
    (hnull : ZornOctonionAnyon.ZornCell.colorDot vC wC = 0)
    {n : ℕ} [DecidableEq (Fin n)]
    (sys : FractionalAnyonSpin.AnyonBraidSystem n) :
    colorSU3Casimir * zornBaryonToCl55Singlet (baryonState u v w) = 0 ∧
    colorLieAction4 A (zornBaryonSingletToColorSpinor4 (baryonState u v w)) = 0 ∧
    frameBraid4 F (zornBaryonSingletToColorSpinor4 (baryonState u v w)) =
      (0, (frameBraidingPhase F * ((dot3 (cross3 u v) w : ℝ) : ℂ)) • bdgMajoranaPlusColorSpinor4.2) ∧
    (∀ wOcc : InfoGeometry.Physics.FureyCharges.Occupation3,
      InfoGeometry.Physics.FureyCharges.fureyOccupationCharge wOcc = 0 ∨
      InfoGeometry.Physics.FureyCharges.fureyOccupationCharge wOcc = (1 / 3 : ℚ) ∨
      InfoGeometry.Physics.FureyCharges.fureyOccupationCharge wOcc = (2 / 3 : ℚ) ∨
      InfoGeometry.Physics.FureyCharges.fureyOccupationCharge wOcc = 1) ∧
    (InfoGeometry.Physics.SplitOctonionBraidSU3.swapRGPerm *
        InfoGeometry.Physics.SplitOctonionBraidSU3.swapGBPerm *
        InfoGeometry.Physics.SplitOctonionBraidSU3.swapRGPerm =
      InfoGeometry.Physics.SplitOctonionBraidSU3.swapGBPerm *
        InfoGeometry.Physics.SplitOctonionBraidSU3.swapRGPerm *
        InfoGeometry.Physics.SplitOctonionBraidSU3.swapGBPerm ∧
     InfoGeometry.Topology.Parafermion.sigma_1 t *
        InfoGeometry.Topology.Parafermion.sigma_2 t *
        InfoGeometry.Topology.Parafermion.sigma_1 t =
      InfoGeometry.Topology.Parafermion.sigma_2 t *
        InfoGeometry.Topology.Parafermion.sigma_1 t *
        InfoGeometry.Topology.Parafermion.sigma_2 t) ∧
    (InfoGeometry.Physics.SplitOctonionBraidSU3.zornMul
        (InfoGeometry.Physics.SplitOctonionBraidSU3.Q_k k)
        (InfoGeometry.Physics.SplitOctonionBraidSU3.Q_k k) =
      InfoGeometry.Physics.SplitOctonionBraidSU3.I_zorn) ∧
    Matrix.trace (ZornOctonionAnyon.ZornCell.colorTensorMatrix vC wC) = 0 ∧
    Matrix.trace ((U : Matrix (Fin 3) (Fin 3) ℂ) *
        ZornOctonionAnyon.ZornCell.colorTensorMatrix vC wC *
        ((U⁻¹ : ZornOctonionAnyon.ZornCell.ColorGauge) :
          Matrix (Fin 3) (Fin 3) ℂ)) =
      Matrix.trace (ZornOctonionAnyon.ZornCell.colorTensorMatrix vC wC) ∧
    sys.doubleBraidingOperator * sys.doubleBraidingOperator.conjTranspose = 1 := by
  have hB := (zornBaryon_lives_in_parafermion_vacancy (baryonState u v w)).2
  have hC := colorLieAction4_kills_zornBaryonSinglet A (baryonState u v w)
  have hF := frameBraid4_zornBaryonSinglet F (baryonState u v w)
  have hb : (baryonState u v w).b = dot3 (cross3 u v) w := by rw [baryonState_eq_scalar]
  rw [hb] at hF
  have hFurey := furey_charge_packet.2
  have hWeyl := color_weyl_and_parafermion_braid_packet t
  have hZorn := (zorn_majorana_braid_packet k).1
  have hNull := zorn_null_color_gauge_packet U vC wC hnull
  have hAnyon := (anyon_double_braid_packet sys).1
  exact ⟨hB, hC, hF, hFurey, hWeyl, hZorn, hNull.2.1, hNull.2.2, hAnyon⟩

end ZornToColorSpinor4

/-! ## Section 4: `FibonacciParafermion` → `FusionState` → `ThreeStrandState` Intertwiner & `sl₂H` Defect -/

section FibonacciThreeStrandIntertwiner

/-- `ℝ`-linear embedding of `FibonacciParafermion.RealDiracSpinor` (`Fin 2 → ℝ`) into
    `ThreeStrandJonesRecoupling.FusionState` (`Fin 2 → ℂ`). -/
def realSpinorToFusionState :
    FibonacciParafermion.RealDiracSpinor →ₗ[ℝ] FusionState where
  toFun v i := (v i : ℂ)
  map_add' v w := by funext i; simp
  map_smul' r v := by funext i; simp [Complex.real_smul]

theorem realSpinorToFusionState_intertwines_F (a b : ℝ)
    (v : FibonacciParafermion.RealDiracSpinor) :
    realSpinorToFusionState (FibonacciParafermion.F_action a b v) =
      (InfoGeometry.Canonical.FiniteFibonacciFusionMatrix.fibonacciFusionMatrix
        (a : ℂ) (b : ℂ)).mulVec (realSpinorToFusionState v) := by
  rw [← ofReal_F_matrix a b]
  funext i
  fin_cases i <;>
    simp [realSpinorToFusionState, FibonacciParafermion.F_action,
      Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- `ℂ`-linear intertwiner embedding `FusionState` (`Fin 2 → ℂ`) into the `k = 0`
    `e12`-singlet / orthogonal triplet subspace of `ThreeStrandState` (`Fin 2 → Fin 2 → Fin 2 → ℂ`). -/
def fusionStateToThreeStrand :
    FusionState →ₗ[ℂ] ThreeStrandState where
  toFun ψ i j k :=
    if k = 0 then
      if i = 0 ∧ j = 1 then ψ 0
      else if i = 1 ∧ j = 0 then -(ψ 0)
      else if i = 0 ∧ j = 0 then ψ 1
      else 0
    else 0
  map_add' ψ φ := by
    funext i j k
    fin_cases i <;> fin_cases j <;> fin_cases k <;> simp [Pi.add_apply]
    all_goals ring
  map_smul' c ψ := by
    funext i j k
    fin_cases i <;> fin_cases j <;> fin_cases k <;> simp [Pi.smul_apply, smul_eq_mul]

theorem fusionStateToThreeStrand_intertwines_e12 (ψ : FusionState) :
    e12 (fusionStateToThreeStrand ψ) = fusionStateToThreeStrand (fusionProjector12 ψ) := by
  funext i j k
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp [e12, fusionStateToThreeStrand, fusionProjector12]
  all_goals ring

theorem weylPlus_lands_in_e12_singlet (v : FibonacciParafermion.RealDiracSpinor) (q : ℂ) :
    e12 (fusionStateToThreeStrand (realSpinorToFusionState
        (FibonacciParafermion.WeylPlusProjector.mulVec v))) =
      fusionStateToThreeStrand (realSpinorToFusionState
        (FibonacciParafermion.WeylPlusProjector.mulVec v)) ∧
    braid12 q (fusionStateToThreeStrand (realSpinorToFusionState
        (FibonacciParafermion.WeylPlusProjector.mulVec v))) =
      (q - q ^ 2) • fusionStateToThreeStrand (realSpinorToFusionState
        (FibonacciParafermion.WeylPlusProjector.mulVec v)) := by
  have hproj : fusionProjector12 (realSpinorToFusionState
      (FibonacciParafermion.WeylPlusProjector.mulVec v)) =
      realSpinorToFusionState (FibonacciParafermion.WeylPlusProjector.mulVec v) := by
    funext i
    fin_cases i <;>
      simp [fusionProjector12, realSpinorToFusionState,
        FibonacciParafermion.WeylPlusProjector, dotProduct, Fin.sum_univ_two]
  have he12 : e12 (fusionStateToThreeStrand (realSpinorToFusionState
      (FibonacciParafermion.WeylPlusProjector.mulVec v))) =
      fusionStateToThreeStrand (realSpinorToFusionState
        (FibonacciParafermion.WeylPlusProjector.mulVec v)) := by
    rw [fusionStateToThreeStrand_intertwines_e12, hproj]
  exact ⟨he12, braid12_on_singlet q _ he12⟩

theorem weylMinus_lands_in_e12_kernel (v : FibonacciParafermion.RealDiracSpinor) :
    e12 (fusionStateToThreeStrand (realSpinorToFusionState
        (FibonacciParafermion.WeylMinusProjector.mulVec v))) = 0 := by
  have hproj : fusionProjector12 (realSpinorToFusionState
      (FibonacciParafermion.WeylMinusProjector.mulVec v)) = 0 := by
    funext i
    fin_cases i <;>
      simp [fusionProjector12, realSpinorToFusionState,
        FibonacciParafermion.WeylMinusProjector, dotProduct, Fin.sum_univ_two]
  rw [fusionStateToThreeStrand_intertwines_e12, hproj, map_zero]

theorem sl2H_tripotent :
    FibonacciParafermion.sl₂H ^ 3 = FibonacciParafermion.sl₂H := by
  rw [FibonacciParafermion.sl₂H_eq_majoranaZ, pow_succ, pow_two,
    FibonacciParafermion.majoranaZ_sq, one_mul]

/-- Constructive `TopologicalDefectOperator` on `Matrix (Fin 2) (Fin 2) ℝ` built from `sl₂H`. -/
def sl2HDefectOperator :
    InfoGeometry.Physics.TopologicalDefectOperator (Matrix (Fin 2) (Fin 2) ℝ) where
  op := FibonacciParafermion.sl₂H
  is_parafermionic := sl2H_tripotent

theorem sl2H_parafermion_projectors_and_triality :
    proj_up FibonacciParafermion.sl₂H = FibonacciParafermion.WeylPlusProjector ∧
    proj_down FibonacciParafermion.sl₂H = FibonacciParafermion.WeylMinusProjector ∧
    proj_vacancy FibonacciParafermion.sl₂H = 0 ∧
    drazin_projector FibonacciParafermion.sl₂H = 1 ∧
    (FibonacciFusion.phi ^ 2 = FibonacciFusion.phi + 1 ∧
     FibonacciParafermion.majoranaX * FibonacciParafermion.majoranaZ +
       FibonacciParafermion.majoranaZ * FibonacciParafermion.majoranaX = 0) := by
  have hsq : FibonacciParafermion.sl₂H ^ 2 = 1 := by
    rw [pow_two, FibonacciParafermion.sl₂H_eq_majoranaZ, FibonacciParafermion.majoranaZ_sq]
  refine ⟨?_, ?_, ?_, ?_, golden_ratio_readout_packet.1,
      celik_pauli_and_real_majorana_packets.2.2.2.2.2⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [proj_up, InfoGeometry.Canonical.FibonacciParafermionAtoms.proj_up,
        FibonacciParafermion.sl₂H, FibonacciParafermion.WeylPlusProjector, pow_two]
    all_goals norm_num
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [proj_down, InfoGeometry.Canonical.FibonacciParafermionAtoms.proj_down,
        FibonacciParafermion.sl₂H, FibonacciParafermion.WeylMinusProjector, pow_two]
    all_goals norm_num
  · dsimp [proj_vacancy, InfoGeometry.Canonical.FibonacciParafermionAtoms.proj_vacancy]
    rw [hsq, sub_self]
  · dsimp [drazin_projector, InfoGeometry.Canonical.FibonacciParafermionAtoms.drazin_projector]
    exact hsq

theorem jones_b3_and_fibonacci_sector_distinct_coexistence
    {a b : ℝ} (hb : b ^ 2 = a) (ha : a ^ 2 + a = 1) :
    (threeStrandB3Representation (PresentedGroup.of B3Gen.sig0 : B3) *
       threeStrandB3Representation (PresentedGroup.of B3Gen.sig1 : B3) *
       threeStrandB3Representation (PresentedGroup.of B3Gen.sig0 : B3) =
     threeStrandB3Representation (PresentedGroup.of B3Gen.sig1 : B3) *
       threeStrandB3Representation (PresentedGroup.of B3Gen.sig0 : B3) *
       threeStrandB3Representation (PresentedGroup.of B3Gen.sig1 : B3)) ∧
    ((standardJonesBraid12.comp standardJonesBraid12 = (-1 : ℂ) • (1 : ThreeStrandOperator)) ∧
     e12.comp (e23.comp e12) = (1 / 4 : ℂ) • e12) ∧
    (Matrix.map (InfoGeometry.Canonical.FibonacciParafermionAtoms.F_matrix a b *
        InfoGeometry.Canonical.FibonacciParafermionAtoms.F_matrix a b) Complex.ofRealHom =
      (1 : Matrix (Fin 2) (Fin 2) ℂ) ∧
     InfoGeometry.Canonical.FibonacciParafermionAtoms.IsFibonacciRelation a b) := by
  exact ⟨by simp [standardJonesBraid_units_artin],
    ⟨standardJonesBraid12_square, e12_e23_e12⟩,
    ⟨ofReal_F_matrix_sq hb ha, real_IsFibonacciRelation_of_complex_constraints hb ha⟩⟩

theorem realSpinorToFusionState_injective : Function.Injective realSpinorToFusionState := by
  intro v w h
  funext i
  exact Complex.ofReal_injective (congrFun h i)

theorem fusionStateToThreeStrand_injective : Function.Injective fusionStateToThreeStrand := by
  intro ψ φ h
  funext i
  fin_cases i
  · exact congrFun (congrFun (congrFun h 0) 1) 0
  · exact congrFun (congrFun (congrFun h 0) 0) 0

theorem sl2H_ne_zero : FibonacciParafermion.sl₂H ≠ 0 := by
  intro h
  have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 0) h
  norm_num [FibonacciParafermion.sl₂H] at h00

theorem sl2H_sq_ne_self : FibonacciParafermion.sl₂H ^ 2 ≠ FibonacciParafermion.sl₂H := by
  intro h
  have h11 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 1 1) h
  rw [pow_two, FibonacciParafermion.sl₂H_eq_majoranaZ, FibonacciParafermion.majoranaZ_sq] at h11
  norm_num [FibonacciParafermion.sl₂H, FibonacciParafermion.majoranaZ] at h11

theorem sl2H_proj_up_ne_zero : proj_up FibonacciParafermion.sl₂H ≠ 0 := by
  rw [sl2H_parafermion_projectors_and_triality.1]
  intro h
  have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 0) h
  norm_num [FibonacciParafermion.WeylPlusProjector] at h00

theorem sl2H_proj_down_ne_zero : proj_down FibonacciParafermion.sl₂H ≠ 0 := by
  rw [sl2H_parafermion_projectors_and_triality.2.1]
  intro h
  have h11 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 1 1) h
  norm_num [FibonacciParafermion.WeylMinusProjector] at h11

theorem threeStrandB3Representation_noncomm :
    (threeStrandB3Representation (PresentedGroup.of B3Gen.sig0 : B3) : ThreeStrandOperator) *
      (threeStrandB3Representation (PresentedGroup.of B3Gen.sig1 : B3) : ThreeStrandOperator) ≠
    (threeStrandB3Representation (PresentedGroup.of B3Gen.sig1 : B3) : ThreeStrandOperator) *
      (threeStrandB3Representation (PresentedGroup.of B3Gen.sig0 : B3) : ThreeStrandOperator) := by
  intro h
  let ψ : ThreeStrandState := fun i j k => if i = 0 ∧ j = 1 ∧ k = 0 then 1 else 0
  have hval := congrArg (fun T : ThreeStrandOperator => T ψ 0 0 1) h
  simp [threeStrandB3Representation_sig0, threeStrandB3Representation_sig1,
    standardJonesBraid12Unit, standardJonesBraid23Unit,
    standardJonesBraid12, standardJonesBraid23, E12, E23, e12, e23, ψ] at hval

end FibonacciThreeStrandIntertwiner

/-! ## Section 5: Explicit Non-Commutativity Witnesses (T16) -/

section NonCommutativityWitnesses

theorem majoranaX_mul_majoranaZ_ne :
    FibonacciParafermion.majoranaX * FibonacciParafermion.majoranaZ ≠
      FibonacciParafermion.majoranaZ * FibonacciParafermion.majoranaX := by
  intro h
  have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 1) h
  norm_num [FibonacciParafermion.majoranaX, FibonacciParafermion.majoranaZ,
    Matrix.mul_apply, Fin.sum_univ_two] at h01

theorem gl1_mul_gl2_ne :
    InfoGeometry.Physics.GellMannSU3.gl1 * InfoGeometry.Physics.GellMannSU3.gl2 ≠
      InfoGeometry.Physics.GellMannSU3.gl2 * InfoGeometry.Physics.GellMannSU3.gl1 := by
  intro h
  have hsub : InfoGeometry.Physics.GellMannSU3.gl1 * InfoGeometry.Physics.GellMannSU3.gl2 -
      InfoGeometry.Physics.GellMannSU3.gl2 * InfoGeometry.Physics.GellMannSU3.gl1 = 0 :=
    sub_eq_zero.mpr h
  rw [gellMann_su3_packet.1] at hsub
  have h00 := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℂ => M 0 0) hsub
  simp [InfoGeometry.Physics.GellMannSU3.gl3] at h00

theorem e12_comp_e23_ne : e12.comp e23 ≠ e23.comp e12 := by
  intro h
  let ψ : ThreeStrandState := fun i j k => if i = 0 ∧ j = 1 ∧ k = 0 then 1 else 0
  have hval := congrArg (fun T : ThreeStrandOperator => T ψ 0 0 1) h
  simp [e12, e23, ψ] at hval

theorem cl55_e0_mul_modeOccupied0_ne :
    e 0 * modeOccupied 0 ≠ modeOccupied 0 * e 0 := by
  intro h
  have hleft : e 0 * modeOccupied 0 = 0 := by
    dsimp [modeOccupied]
    rw [← mul_assoc, e_sq 0, zero_mul]
  have hcar : e (0 : Fin 5) * f 0 + f 0 * e 0 = 1 := by
    simpa using ef_car 0 0
  have hright : modeOccupied 0 * e 0 = e 0 := by
    dsimp [modeOccupied]
    have hfe : f 0 * e 0 = 1 - e 0 * f 0 := eq_sub_of_add_eq' hcar
    calc
      (e 0 * f 0) * e 0 = e 0 * (f 0 * e 0) := by noncomm_ring
      _ = e 0 * (1 - e 0 * f 0) := by rw [hfe]
      _ = e 0 - (e 0 * e 0) * f 0 := by noncomm_ring
      _ = e 0 := by rw [e_sq 0]; noncomm_ring
  rw [hleft, hright] at h
  have he0 : e (0 : Fin 5) = 0 := h.symm
  have h1 : (1 : MatStage 5) = 0 := by
    rw [he0, zero_mul, mul_zero, add_zero] at hcar
    exact hcar.symm
  exact one_ne_zero h1

theorem spinPair_spEp_mul_spNp_ne : spEp * spNp ≠ spNp * spEp := by
  intro h
  rcases cl55_two_mode_pn_spinpair_embedding (p := 3) (n := 4) (by decide) with
    ⟨⟨hEp2, _, _, _⟩, ⟨hCARp, _⟩, _, _, _, _⟩
  have hleft : spEp * spNp = 0 := by
    dsimp [spNp]
    rw [← mul_assoc, hEp2, zero_mul]
  have hright : spNp * spEp = spEp := by
    dsimp [spNp]
    have hfe : spFp * spEp = 1 - spEp * spFp := eq_sub_of_add_eq' hCARp
    calc
      (spEp * spFp) * spEp = spEp * (spFp * spEp) := by noncomm_ring
      _ = spEp * (1 - spEp * spFp) := by rw [hfe]
      _ = spEp - (spEp * spEp) * spFp := by noncomm_ring
      _ = spEp := by rw [hEp2]; noncomm_ring
  rw [hleft, hright] at h
  have hep0 : spEp = 0 := h.symm
  rw [hep0, zero_mul, mul_zero, add_zero] at hCARp
  exact one_ne_zero hCARp.symm

end NonCommutativityWitnesses

/-! ## Section 6: Seam B Unified Finite Morphism Packet (`Type*`, T17 Witnessed) -/

section SeamBMorphismPacket

/-- `Type*` compatibility packet collecting all Seam B typed morphisms and algebraic carriers
    without collapsing distinct types or using `: Prop` aggregation. -/
structure ColorParafermionMorphismPacket (n : ℕ) [DecidableEq (Fin n)] : Type _ where
  zornEquiv :
    GaugedZornDiracKahler.ZornMatrix ℝ ≃ₗ[ℝ]
      InfoGeometry.Physics.ZornMatrixSU3.ZornMatrix
  zornEquiv_mul :
    ∀ X Y : GaugedZornDiracKahler.ZornMatrix ℝ,
      zornEquiv (GaugedZornDiracKahler.ZornMatrix.zornMul X Y) =
        zornEquiv X * zornEquiv Y
  zornEquiv_baryonState :
    ∀ u v w : Vec3 ℝ,
      zornEquiv (baryonState u v w) =
        ⟨0, InfoGeometry.Physics.ZornMatrixSU3.scalarTriple u v w, 0, 0⟩
  zornToCl55Singlet : GaugedZornDiracKahler.ZornMatrix ℝ →ₗ[ℝ] MatStage 5
  zornToCl55Singlet_baryon_ne_zero :
    zornToCl55Singlet (baryonState colorE0 colorE1 colorE2) ≠ 0
  zornToCl55Singlet_casimir_zero :
    ∀ X : GaugedZornDiracKahler.ZornMatrix ℝ, colorSU3Casimir * zornToCl55Singlet X = 0
  zornToColorSpinor4 :
    GaugedZornDiracKahler.ZornMatrix ℝ →ₗ[ℝ]
      ColorSpinor4 InfoGeometry.Physics.BogoliubovSU3ParafermionProofChain.ParafermionStage4
  zornToColorSpinor4_baryon_ne_zero :
    zornToColorSpinor4 (baryonState colorE0 colorE1 colorE2) ≠ 0
  zornToColorSpinor4_singlet :
    ∀ (A : InfoGeometry.Physics.BogoliubovSU3ParafermionProofChain.M3C)
      (X : GaugedZornDiracKahler.ZornMatrix ℝ),
      colorLieAction4 A (zornToColorSpinor4 X) = 0
  realSpinorToFusion : FibonacciParafermion.RealDiracSpinor →ₗ[ℝ] FusionState
  realSpinorToFusion_injective : Function.Injective realSpinorToFusion
  realSpinorToFusion_intertwines_F :
    ∀ (a b : ℝ) (v : FibonacciParafermion.RealDiracSpinor),
      realSpinorToFusion (FibonacciParafermion.F_action a b v) =
        (InfoGeometry.Canonical.FiniteFibonacciFusionMatrix.fibonacciFusionMatrix
          (a : ℂ) (b : ℂ)).mulVec (realSpinorToFusion v)
  fusionToThreeStrand : FusionState →ₗ[ℂ] ThreeStrandState
  fusionToThreeStrand_injective : Function.Injective fusionToThreeStrand
  fusionToThreeStrand_intertwines_e12 :
    ∀ ψ : FusionState, e12 (fusionToThreeStrand ψ) = fusionToThreeStrand (fusionProjector12 ψ)
  colorDefect : InfoGeometry.Physics.TopologicalDefectOperator (MatStage 5)
  colorDefect_ne_zero : colorDefect.op ≠ 0
  colorDefect_sq_ne_op : colorDefect.op ^ 2 ≠ colorDefect.op
  colorDefect_proj_up_ne_zero :
    InfoGeometry.Categorical.Z3Parafermion.proj_up colorDefect.op ≠ 0
  colorDefect_proj_vacancy_ne_zero :
    InfoGeometry.Categorical.Z3Parafermion.proj_vacancy colorDefect.op ≠ 0
  zornGradingDefect :
    InfoGeometry.Physics.TopologicalDefectOperator
      (Module.End ℝ InfoGeometry.Physics.ZornMatrixSU3.ZornMatrix)
  zornGradingDefect_ne_zero : zornGradingDefect.op ≠ 0
  zornGradingDefect_sq_ne_op : zornGradingDefect.op ^ 2 ≠ zornGradingDefect.op
  zornGradingDefect_proj_up_ne_zero :
    InfoGeometry.Categorical.Z3Parafermion.proj_up zornGradingDefect.op ≠ 0
  zornGradingDefect_proj_vacancy_ne_zero :
    InfoGeometry.Categorical.Z3Parafermion.proj_vacancy zornGradingDefect.op ≠ 0
  sl2HDefect : InfoGeometry.Physics.TopologicalDefectOperator (Matrix (Fin 2) (Fin 2) ℝ)
  sl2HDefect_ne_zero : sl2HDefect.op ≠ 0
  sl2HDefect_sq_ne_op : sl2HDefect.op ^ 2 ≠ sl2HDefect.op
  sl2HDefect_proj_up_ne_zero :
    InfoGeometry.Categorical.Z3Parafermion.proj_up sl2HDefect.op ≠ 0
  sl2HDefect_proj_down_ne_zero :
    InfoGeometry.Categorical.Z3Parafermion.proj_down sl2HDefect.op ≠ 0
  b3Rep : B3 →* (ThreeStrandOperator)ˣ
  b3Rep_noncomm :
    (b3Rep (PresentedGroup.of B3Gen.sig0 : B3) : ThreeStrandOperator) *
      (b3Rep (PresentedGroup.of B3Gen.sig1 : B3) : ThreeStrandOperator) ≠
    (b3Rep (PresentedGroup.of B3Gen.sig1 : B3) : ThreeStrandOperator) *
      (b3Rep (PresentedGroup.of B3Gen.sig0 : B3) : ThreeStrandOperator)
  artinLift : G2SpinOperatorLift
  artinLift_exact_order12 :
    ∀ k : ℕ, 0 < k → k < 12 → (artinLift.Bs * artinLift.Bl) ^ k ≠ 1
  anyonSystem : FractionalAnyonSpin.AnyonBraidSystem n
  frame : InfoGeometry.Physics.BogoliubovWeylChemicalPotential.BogoliubovInertialFrame

private theorem end_smul_one_pow_apply (c x : ℂ) (m : ℕ) :
    ((c • (1 : Module.End ℂ ℂ)) ^ m) x = c ^ m * x := by
  induction m generalizing x with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, Module.End.mul_apply, LinearMap.smul_apply, Module.End.one_apply,
      smul_eq_mul, ih (c * x), pow_succ']
    rw [← mul_assoc, mul_comm (c ^ m) c]

/-- Constructive `G₂` spin-lift witness on `ℂ` with exact order 12:
    `Bs = exp(iπ/6) • 1`, `Bl = 1`. -/
def canonicalG2SpinOperatorLift : G2SpinOperatorLift where
  H := ℂ
  Bs := Complex.exp (Complex.I * ((Real.pi / 6 : ℝ) : ℂ)) • (1 : Module.End ℂ ℂ)
  Bl := (1 : Module.End ℂ ℂ)
  artin := by
    apply LinearMap.ext
    intro x
    simp
  coxeter_pow_six_eq_neg_one := by
    apply LinearMap.ext
    intro x
    change ((Complex.exp (Complex.I * ((Real.pi / 6 : ℝ) : ℂ)) •
        (1 : Module.End ℂ ℂ) * (1 : Module.End ℂ ℂ)) ^ 6) x = -x
    rw [mul_one, end_smul_one_pow_apply, ← Complex.exp_nat_mul]
    have harg : (6 : ℕ) * (Complex.I * ((Real.pi / 6 : ℝ) : ℂ)) = Real.pi * Complex.I := by
      push_cast
      ring
    rw [harg, Complex.exp_pi_mul_I, neg_one_mul]

theorem canonicalG2SpinOperatorLift_exact_order12 :
    ∀ k : ℕ, 0 < k → k < 12 →
      (canonicalG2SpinOperatorLift.Bs * canonicalG2SpinOperatorLift.Bl) ^ k ≠ 1 := by
  intro k hk0 hk12 h
  have h1 := congrArg (fun T : Module.End ℂ ℂ => T 1) h
  change ((Complex.exp (Complex.I * ((Real.pi / 6 : ℝ) : ℂ)) •
      (1 : Module.End ℂ ℂ) * (1 : Module.End ℂ ℂ)) ^ k) 1 = 1 at h1
  rw [mul_one, end_smul_one_pow_apply, mul_one, ← Complex.exp_nat_mul,
    Complex.exp_eq_one_iff] at h1
  rcases h1 with ⟨n, hn⟩
  have hmul0 :
      ((k : ℂ) - 12 * (n : ℂ)) * (Complex.I * ((Real.pi / 6 : ℝ) : ℂ)) = 0 := by
    calc
      ((k : ℂ) - 12 * (n : ℂ)) * (Complex.I * ((Real.pi / 6 : ℝ) : ℂ)) =
          (k : ℂ) * (Complex.I * ((Real.pi / 6 : ℝ) : ℂ)) -
            (n : ℂ) * (2 * Real.pi * Complex.I) := by
        push_cast
        ring
      _ = 0 := sub_eq_zero.mpr hn
  have hpi : Complex.I * ((Real.pi / 6 : ℝ) : ℂ) ≠ 0 := by
    apply mul_ne_zero Complex.I_ne_zero
    exact Complex.ofReal_ne_zero.mpr (by positivity)
  have hdiff : (k : ℂ) - 12 * (n : ℂ) = 0 := (mul_eq_zero.mp hmul0).resolve_right hpi
  have hk_eq : (k : ℂ) = 12 * (n : ℂ) := sub_eq_zero.mp hdiff
  have hk_re := congrArg Complex.re hk_eq
  simp only [Complex.natCast_re, Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat,
    Complex.intCast_re, Complex.intCast_im, mul_zero, sub_zero] at hk_re
  have hk_int : (k : ℤ) = 12 * n := Int.cast_injective (α := ℝ) (by simpa using hk_re)
  omega

/-- Constructive `AnyonBraidSystem 2` witness with identity unitary braiding operators. -/
def canonicalAnyonBraidSystem2 : FractionalAnyonSpin.AnyonBraidSystem 2 where
  R_ab := 1
  R_ba := 1

/-- Constructive `ℝ`-linear lift of `zornBaryonToCl55Singlet`. -/
def zornBaryonToCl55SingletLinear :
    GaugedZornDiracKahler.ZornMatrix ℝ →ₗ[ℝ] MatStage 5 where
  toFun := zornBaryonToCl55Singlet
  map_add' X Y := by
    change (X.b + Y.b) • colorBaryonSingletProj =
      X.b • colorBaryonSingletProj + Y.b • colorBaryonSingletProj
    exact add_smul X.b Y.b colorBaryonSingletProj
  map_smul' r X := by
    change (r * X.b) • colorBaryonSingletProj = r • (X.b • colorBaryonSingletProj)
    exact (smul_smul r X.b colorBaryonSingletProj).symm

/-- Constructive T17 witness for `ColorParafermionMorphismPacket 2`. -/
def canonicalColorParafermionMorphismPacket : ColorParafermionMorphismPacket 2 where
  zornEquiv := zornGaugedEquivSU3
  zornEquiv_mul := zornGaugedEquivSU3_mul
  zornEquiv_baryonState := zornGaugedEquivSU3_baryonState
  zornToCl55Singlet := zornBaryonToCl55SingletLinear
  zornToCl55Singlet_baryon_ne_zero := by
    change zornBaryonToCl55Singlet (baryonState colorE0 colorE1 colorE2) ≠ 0
    rw [(zornBaryonToCl55_bridge colorE0 colorE1 colorE2 0 0 0 0).1]
    exact colorBaryonSingletProj_ne_zero
  zornToCl55Singlet_casimir_zero X := (zornBaryon_lives_in_parafermion_vacancy X).2
  zornToColorSpinor4 := zornBaryonSingletToColorSpinor4
  zornToColorSpinor4_baryon_ne_zero := zornBaryonSingletToColorSpinor4_baryon_ne_zero
  zornToColorSpinor4_singlet A X := colorLieAction4_kills_zornBaryonSinglet A X
  realSpinorToFusion := realSpinorToFusionState
  realSpinorToFusion_injective := realSpinorToFusionState_injective
  realSpinorToFusion_intertwines_F := realSpinorToFusionState_intertwines_F
  fusionToThreeStrand := fusionStateToThreeStrand
  fusionToThreeStrand_injective := fusionStateToThreeStrand_injective
  fusionToThreeStrand_intertwines_e12 := fusionStateToThreeStrand_intertwines_e12
  colorDefect := colorSectorDefectOperator
  colorDefect_ne_zero := colorSectorTripotent_ne_zero
  colorDefect_sq_ne_op := colorSectorTripotent_sq_ne_self
  colorDefect_proj_up_ne_zero := colorSectorTripotent_proj_up_ne_zero
  colorDefect_proj_vacancy_ne_zero := colorSectorTripotent_proj_vacancy_ne_zero
  zornGradingDefect := zornSU3GradingDefectOperator
  zornGradingDefect_ne_zero := zornSU3GradingEnd_ne_zero
  zornGradingDefect_sq_ne_op := zornSU3GradingEnd_sq_ne_self
  zornGradingDefect_proj_up_ne_zero := zornSU3GradingEnd_proj_up_ne_zero
  zornGradingDefect_proj_vacancy_ne_zero := zornSU3GradingEnd_proj_vacancy_ne_zero
  sl2HDefect := sl2HDefectOperator
  sl2HDefect_ne_zero := sl2H_ne_zero
  sl2HDefect_sq_ne_op := sl2H_sq_ne_self
  sl2HDefect_proj_up_ne_zero := sl2H_proj_up_ne_zero
  sl2HDefect_proj_down_ne_zero := sl2H_proj_down_ne_zero
  b3Rep := threeStrandB3Representation
  b3Rep_noncomm := threeStrandB3Representation_noncomm
  artinLift := canonicalG2SpinOperatorLift
  artinLift_exact_order12 := canonicalG2SpinOperatorLift_exact_order12
  anyonSystem := canonicalAnyonBraidSystem2
  frame :=
    { θ := 0
      β := 1
      E := 1
      μ := 0
      Q := 1 }

/-- Standalone Seam B compatibility theorem connecting `ColorParafermionMorphismPacket` with
    `QCDTwelveFoldSchurTrialityBridge`, `NuclearExceptionalArtinGaloisBridge`,
    `QCDArchitectureSynthesis`, and `AnyonBraidSystem`. -/
theorem seamB_finite_architecture_compatibility
    {n : ℕ} [DecidableEq (Fin n)] (P : ColorParafermionMorphismPacket n)
    {A : Type*} [Ring A] (V W Binv : A)
    (a b : ℝ) (v : FibonacciParafermion.RealDiracSpinor)
    (X Y : GaugedZornDiracKahler.ZornMatrix ℝ) (u vVec w : Vec3 ℝ) (ψ : FusionState)
    (r : InfoGeometry.Algebra.Zorn.G2CyclotomicWeyl.Root) :
    (P.colorDefect.op ^ 3 = P.colorDefect.op ∧ P.colorDefect.op ≠ 0 ∧
     P.colorDefect.op ^ 2 ≠ P.colorDefect.op ∧
     proj_up P.colorDefect.op ≠ 0 ∧ proj_vacancy P.colorDefect.op ≠ 0) ∧
    (P.zornGradingDefect.op ^ 3 = P.zornGradingDefect.op ∧ P.zornGradingDefect.op ≠ 0 ∧
     P.zornGradingDefect.op ^ 2 ≠ P.zornGradingDefect.op ∧
     proj_up P.zornGradingDefect.op ≠ 0 ∧ proj_vacancy P.zornGradingDefect.op ≠ 0) ∧
    (P.sl2HDefect.op ^ 3 = P.sl2HDefect.op ∧ P.sl2HDefect.op ≠ 0 ∧
     P.sl2HDefect.op ^ 2 ≠ P.sl2HDefect.op ∧
     proj_up P.sl2HDefect.op ≠ 0 ∧ proj_down P.sl2HDefect.op ≠ 0) ∧
    (P.zornEquiv.symm (P.zornEquiv X) = X ∧
     P.zornEquiv (GaugedZornDiracKahler.ZornMatrix.zornMul X Y) = P.zornEquiv X * P.zornEquiv Y ∧
     P.zornEquiv (baryonState u vVec w) =
       ⟨0, InfoGeometry.Physics.ZornMatrixSU3.scalarTriple u vVec w, 0, 0⟩ ∧
     P.zornToCl55Singlet (baryonState colorE0 colorE1 colorE2) ≠ 0 ∧
     colorSU3Casimir * P.zornToCl55Singlet X = 0) ∧
    (P.zornToColorSpinor4 (baryonState colorE0 colorE1 colorE2) ≠ 0 ∧
     colorLieAction4 InfoGeometry.Physics.GellMannSU3.gl1 (P.zornToColorSpinor4 X) = 0) ∧
    (Function.Injective P.realSpinorToFusion ∧
     P.realSpinorToFusion (FibonacciParafermion.F_action a b v) =
       (InfoGeometry.Canonical.FiniteFibonacciFusionMatrix.fibonacciFusionMatrix
         (a : ℂ) (b : ℂ)).mulVec (P.realSpinorToFusion v) ∧
     Function.Injective P.fusionToThreeStrand ∧
     e12 (P.fusionToThreeStrand ψ) = P.fusionToThreeStrand (fusionProjector12 ψ)) ∧
    ((P.b3Rep ((PresentedGroup.of B3Gen.sig0 : B3) * (PresentedGroup.of B3Gen.sig1 : B3)) =
        P.b3Rep (PresentedGroup.of B3Gen.sig0 : B3) * P.b3Rep (PresentedGroup.of B3Gen.sig1 : B3)) ∧
     ((P.b3Rep (PresentedGroup.of B3Gen.sig0 : B3) : ThreeStrandOperator) *
        (P.b3Rep (PresentedGroup.of B3Gen.sig1 : B3) : ThreeStrandOperator) ≠
      (P.b3Rep (PresentedGroup.of B3Gen.sig1 : B3) : ThreeStrandOperator) *
        (P.b3Rep (PresentedGroup.of B3Gen.sig0 : B3) : ThreeStrandOperator))) ∧
    (InfoGeometry.Physics.NuclearOperatorSchurComplement.effectiveOperator 0 V W Binv =
        -(V * Binv * W) ∧
     (P.artinLift.Bs * P.artinLift.Bl) ^ 6 = -1 ∧
     (P.artinLift.Bs * P.artinLift.Bl) ^ 12 = 1 ∧
     (∀ k : ℕ, 0 < k → k < 12 → (P.artinLift.Bs * P.artinLift.Bl) ^ k ≠ 1) ∧
     orderOf InfoGeometry.Canonical.TwelveFoldExplicitOperators.masterTwelve = 12 ∧
     (InfoGeometry.Canonical.TrialitySpin8Permutations.trialityCycle ^ 3 =
       (1 : Equiv.Perm InfoGeometry.Canonical.TrialitySpin8Permutations.TrialitySector)) ∧
     InfoGeometry.Algebra.Zorn.G2CyclotomicWeyl.sector
         (InfoGeometry.Algebra.Zorn.G2CyclotomicSignedRootBridge.cyclotomicCoxeterPerm r) =
       InfoGeometry.Algebra.Zorn.G2CyclotomicWeyl.sector r ∧
     P.anyonSystem.doubleBraidingOperator * P.anyonSystem.doubleBraidingOperator.conjTranspose = 1 ∧
     frameBraidingPhase P.frame = InfoGeometry.Physics.BogoliubovWeylChemicalPotential.frameWeylQ P.frame) := by
  have hmon := monodromy_schur_packet V W Binv P.artinLift P.anyonSystem
  have htri := furey_triality_twelvefold_packet.2.1
  have hcyc := (g2_cyclotomic_sector_packet r).2.2
  refine ⟨⟨P.colorDefect.is_parafermionic, P.colorDefect_ne_zero, P.colorDefect_sq_ne_op,
      P.colorDefect_proj_up_ne_zero, P.colorDefect_proj_vacancy_ne_zero⟩,
    ⟨P.zornGradingDefect.is_parafermionic, P.zornGradingDefect_ne_zero, P.zornGradingDefect_sq_ne_op,
      P.zornGradingDefect_proj_up_ne_zero, P.zornGradingDefect_proj_vacancy_ne_zero⟩,
    ⟨P.sl2HDefect.is_parafermionic, P.sl2HDefect_ne_zero, P.sl2HDefect_sq_ne_op,
      P.sl2HDefect_proj_up_ne_zero, P.sl2HDefect_proj_down_ne_zero⟩,
    ⟨P.zornEquiv.symm_apply_apply X, P.zornEquiv_mul X Y, P.zornEquiv_baryonState u vVec w,
      P.zornToCl55Singlet_baryon_ne_zero, P.zornToCl55Singlet_casimir_zero X⟩,
    ⟨P.zornToColorSpinor4_baryon_ne_zero,
      P.zornToColorSpinor4_singlet InfoGeometry.Physics.GellMannSU3.gl1 X⟩,
    ⟨P.realSpinorToFusion_injective, P.realSpinorToFusion_intertwines_F a b v,
      P.fusionToThreeStrand_injective, P.fusionToThreeStrand_intertwines_e12 ψ⟩,
    ⟨map_mul P.b3Rep _ _, P.b3Rep_noncomm⟩,
    hmon.1, hmon.2.2.1, hmon.2.2.2.1, P.artinLift_exact_order12, hmon.2.2.2.2.1,
    htri, hcyc, hmon.2.2.2.2.2, frameBraidingPhase_eq_frameWeylQ P.frame⟩

end SeamBMorphismPacket

end InfoGeometry.Synthesis.QCDColorConfinementParafermionSynthesis

/-! ## Section 7: Conditional 4D Continuum QCD Confinement & Mass Gap Layer -/

namespace InfoGeometry.Synthesis.QCDColorConfinementParafermionSynthesis

open InfoGeometry.Clifford.Cl11TensorTower (MatStage)
open InfoGeometry.Canonical
open InfoGeometry.Canonical.GaugedZornDiracKahler (Vec3 dot3 cross3)
open InfoGeometry.Canonical.ZornColorConfinementBaryon
open InfoGeometry.Physics.Cl55SpinorCartanFock
open InfoGeometry.Physics.Cl55WignerSU4Embedding
open InfoGeometry.Categorical.Z3Parafermion
open InfoGeometry.Physics.ThreeStrandJonesRecoupling
open InfoGeometry.Exceptional.ArtinOperators
open InfoGeometry.Physics.B3PresentedGroup
open scoped Matrix Kronecker

/-- Hypothesis-parameterized continuum 4D QCD confinement & mass-gap carrier (`Type*`, not `Prop`).
    Separates unconditional finite Seam B algebra from nonperturbative 4D Yang–Mills dynamics. -/
structure ContinuumQCDConfinementHypothesis where
  ContinuumState : Type
  [addCommGroup : AddCommGroup ContinuumState]
  [moduleC : Module ℂ ContinuumState]
  hamiltonian : Module.End ℂ ContinuumState
  singletProjector : Module.End ℂ ContinuumState
  singletProjector_idem : singletProjector.comp singletProjector = singletProjector
  vacuum : ContinuumState
  vacuum_ne_zero : vacuum ≠ 0
  vacuum_in_singlet : singletProjector vacuum = vacuum
  hamiltonian_vacuum : hamiltonian vacuum = 0
  hamiltonian_comp_singlet : hamiltonian.comp singletProjector = 0
  non_singlet_witness : ∃ ψ : ContinuumState, ψ ≠ 0 ∧ singletProjector ψ = 0
  massGap : ℝ
  massGap_pos : 0 < massGap
  stringTension : ℝ
  stringTension_pos : 0 < stringTension
  wilsonAreaExponent : ℝ → ℝ
  area_law_bound : ∀ area : ℝ, 0 ≤ area → wilsonAreaExponent area = -(stringTension * area)
  energy : ContinuumState → ℝ
  energy_nonneg : ∀ ψ : ContinuumState, 0 ≤ energy ψ
  energy_zero_iff_hamiltonian_zero : ∀ ψ : ContinuumState, energy ψ = 0 ↔ hamiltonian ψ = 0
  non_singlet_mass_gap : ∀ ψ : ContinuumState, ψ ≠ 0 → singletProjector ψ = 0 → massGap ≤ energy ψ
  embedCl55 : MatStage 5 →ₗ[ℝ] Module.End ℂ ContinuumState
  embedCl55_one : embedCl55 1 = 1
  embedCl55_mul : ∀ A B : MatStage 5, embedCl55 (A * B) = (embedCl55 A).comp (embedCl55 B)
  embedCl55_baryon_ne_zero : embedCl55 colorBaryonSingletProj ≠ 0
  embedCl55_colored_ne_zero :
    embedCl55 (colorQuarkTripletProj + colorDiquarkAntitripletProj) ≠ 0
  embed_baryon_into_singlet :
    embedCl55 colorBaryonSingletProj = (embedCl55 colorBaryonSingletProj).comp singletProjector
  embed_baryon_range_in_singlet :
    singletProjector.comp (embedCl55 colorBaryonSingletProj) = embedCl55 colorBaryonSingletProj
  embed_colored_annihilates_singlet :
    (embedCl55 (colorQuarkTripletProj + colorDiquarkAntitripletProj)).comp singletProjector = 0
  embed_colored_range_annihilates_singlet :
    singletProjector.comp (embedCl55 (colorQuarkTripletProj + colorDiquarkAntitripletProj)) = 0

attribute [instance] ContinuumQCDConfinementHypothesis.addCommGroup
attribute [instance] ContinuumQCDConfinementHypothesis.moduleC

private def cl55BaryonDiagIdx : InfoGeometry.Clifford.TowerMatrix.Idx 5 :=
  Classical.choose
    (matStage5_diag_exists_ne_zero_of_trace_ne_zero
      (by rw [trace_colorFourSectors_cl55.2.2.2]; norm_num))

private theorem cl55BaryonDiagIdx_spec :
    colorBaryonSingletProj cl55BaryonDiagIdx cl55BaryonDiagIdx ≠ 0 :=
  Classical.choose_spec
    (matStage5_diag_exists_ne_zero_of_trace_ne_zero
      (by rw [trace_colorFourSectors_cl55.2.2.2]; norm_num))

private def cl55VacuumDiagIdx : InfoGeometry.Clifford.TowerMatrix.Idx 5 :=
  Classical.choose
    (matStage5_diag_exists_ne_zero_of_trace_ne_zero
      (by rw [trace_colorFourSectors_cl55.1]; norm_num))

private theorem cl55VacuumDiagIdx_spec :
    colorVacuumSingletProj cl55VacuumDiagIdx cl55VacuumDiagIdx ≠ 0 :=
  Classical.choose_spec
    (matStage5_diag_exists_ne_zero_of_trace_ne_zero
      (by rw [trace_colorFourSectors_cl55.1]; norm_num))

private theorem cl55_toLin_ne_zero_of_trace_ne_zero {M : MatStage 5} (h : Matrix.trace M ≠ 0) :
    (Matrix.map M Complex.ofRealHom).toLin' ≠ 0 := by
  obtain ⟨idx, hidx⟩ := matStage5_diag_exists_ne_zero_of_trace_ne_zero h
  intro h0
  have hval := congrFun
    (congrArg (fun T : Module.End ℂ (InfoGeometry.Clifford.TowerMatrix.Idx 5 → ℂ) =>
      T (Pi.single idx (1 : ℂ))) h0) idx
  simp only [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Matrix.map_apply,
    Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    ↓reduceIte, LinearMap.zero_apply, Pi.zero_apply] at hval
  exact hidx (Complex.ofReal_eq_zero.mp hval)

/-- Constructive finite-dimensional `Cl(5,5)` model witness for
    `ContinuumQCDConfinementHypothesis` on `Idx 5 → ℂ` (for Gate 2.5 / T17). -/
def cl55ModelContinuumHypothesis : ContinuumQCDConfinementHypothesis where
  ContinuumState := InfoGeometry.Clifford.TowerMatrix.Idx 5 → ℂ
  hamiltonian :=
    (1 : Module.End ℂ (InfoGeometry.Clifford.TowerMatrix.Idx 5 → ℂ)) -
      (Matrix.map colorBaryonSingletProj Complex.ofRealHom).toLin'
  singletProjector := (Matrix.map colorBaryonSingletProj Complex.ofRealHom).toLin'
  singletProjector_idem := by
    rcases cl55_color_isospin_orthogonal_idempotents with ⟨⟨_, _, _, hB⟩, _, _, _⟩
    apply LinearMap.ext
    intro v
    have hmul :
        (Matrix.map colorBaryonSingletProj Complex.ofRealHom) *
          (Matrix.map colorBaryonSingletProj Complex.ofRealHom) =
        Matrix.map colorBaryonSingletProj Complex.ofRealHom := by
      rw [← Matrix.map_mul, hB]
    change (Matrix.map colorBaryonSingletProj Complex.ofRealHom).mulVec
        ((Matrix.map colorBaryonSingletProj Complex.ofRealHom).mulVec v) =
      (Matrix.map colorBaryonSingletProj Complex.ofRealHom).mulVec v
    rw [Matrix.mulVec_mulVec, hmul]
  vacuum :=
    (Matrix.map colorBaryonSingletProj Complex.ofRealHom).toLin'
      (Pi.single cl55BaryonDiagIdx (1 : ℂ))
  vacuum_ne_zero := by
    intro h0
    have hval := congrFun h0 cl55BaryonDiagIdx
    simp only [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Matrix.map_apply,
      Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
      ↓reduceIte, Pi.zero_apply] at hval
    exact cl55BaryonDiagIdx_spec (Complex.ofReal_eq_zero.mp hval)
  vacuum_in_singlet := by
    rcases cl55_color_isospin_orthogonal_idempotents with ⟨⟨_, _, _, hB⟩, _, _, _⟩
    have hmul :
        (Matrix.map colorBaryonSingletProj Complex.ofRealHom) *
          (Matrix.map colorBaryonSingletProj Complex.ofRealHom) =
        Matrix.map colorBaryonSingletProj Complex.ofRealHom := by
      rw [← Matrix.map_mul, hB]
    change (Matrix.map colorBaryonSingletProj Complex.ofRealHom).mulVec
        ((Matrix.map colorBaryonSingletProj Complex.ofRealHom).mulVec
          (Pi.single cl55BaryonDiagIdx (1 : ℂ))) =
      (Matrix.map colorBaryonSingletProj Complex.ofRealHom).mulVec
        (Pi.single cl55BaryonDiagIdx (1 : ℂ))
    rw [Matrix.mulVec_mulVec, hmul]
  hamiltonian_vacuum := by
    rcases cl55_color_isospin_orthogonal_idempotents with ⟨⟨_, _, _, hB⟩, _, _, _⟩
    have hmul :
        (Matrix.map colorBaryonSingletProj Complex.ofRealHom) *
          (Matrix.map colorBaryonSingletProj Complex.ofRealHom) =
        Matrix.map colorBaryonSingletProj Complex.ofRealHom := by
      rw [← Matrix.map_mul, hB]
    change ((1 : Module.End ℂ (InfoGeometry.Clifford.TowerMatrix.Idx 5 → ℂ)) -
        (Matrix.map colorBaryonSingletProj Complex.ofRealHom).toLin')
        ((Matrix.map colorBaryonSingletProj Complex.ofRealHom).toLin'
          (Pi.single cl55BaryonDiagIdx (1 : ℂ))) = 0
    rw [LinearMap.sub_apply, Module.End.one_apply]
    have hidem :
        (Matrix.map colorBaryonSingletProj Complex.ofRealHom).toLin'
            ((Matrix.map colorBaryonSingletProj Complex.ofRealHom).toLin'
              (Pi.single cl55BaryonDiagIdx (1 : ℂ))) =
          (Matrix.map colorBaryonSingletProj Complex.ofRealHom).toLin'
            (Pi.single cl55BaryonDiagIdx (1 : ℂ)) := by
      change (Matrix.map colorBaryonSingletProj Complex.ofRealHom).mulVec
          ((Matrix.map colorBaryonSingletProj Complex.ofRealHom).mulVec
            (Pi.single cl55BaryonDiagIdx (1 : ℂ))) =
        (Matrix.map colorBaryonSingletProj Complex.ofRealHom).mulVec
          (Pi.single cl55BaryonDiagIdx (1 : ℂ))
      rw [Matrix.mulVec_mulVec, hmul]
    rw [hidem, sub_self]
  hamiltonian_comp_singlet := by
    rcases cl55_color_isospin_orthogonal_idempotents with ⟨⟨_, _, _, hB⟩, _, _, _⟩
    apply LinearMap.ext
    intro v
    have hmul :
        (Matrix.map colorBaryonSingletProj Complex.ofRealHom) *
          (Matrix.map colorBaryonSingletProj Complex.ofRealHom) =
        Matrix.map colorBaryonSingletProj Complex.ofRealHom := by
      rw [← Matrix.map_mul, hB]
    change ((1 : Module.End ℂ (InfoGeometry.Clifford.TowerMatrix.Idx 5 → ℂ)) -
        (Matrix.map colorBaryonSingletProj Complex.ofRealHom).toLin')
        ((Matrix.map colorBaryonSingletProj Complex.ofRealHom).toLin' v) = 0
    rw [LinearMap.sub_apply, Module.End.one_apply]
    have hidem :
        (Matrix.map colorBaryonSingletProj Complex.ofRealHom).toLin'
            ((Matrix.map colorBaryonSingletProj Complex.ofRealHom).toLin' v) =
          (Matrix.map colorBaryonSingletProj Complex.ofRealHom).toLin' v := by
      change (Matrix.map colorBaryonSingletProj Complex.ofRealHom).mulVec
          ((Matrix.map colorBaryonSingletProj Complex.ofRealHom).mulVec v) =
        (Matrix.map colorBaryonSingletProj Complex.ofRealHom).mulVec v
      rw [Matrix.mulVec_mulVec, hmul]
    rw [hidem, sub_self]
  non_singlet_witness := by
    refine ⟨(Matrix.map colorVacuumSingletProj Complex.ofRealHom).toLin'
      (Pi.single cl55VacuumDiagIdx (1 : ℂ)), ?_, ?_⟩
    · intro h0
      have hval := congrFun h0 cl55VacuumDiagIdx
      simp only [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Matrix.map_apply,
        Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
        ↓reduceIte, Pi.zero_apply] at hval
      exact cl55VacuumDiagIdx_spec (Complex.ofReal_eq_zero.mp hval)
    · have hBV : colorBaryonSingletProj * colorVacuumSingletProj = 0 := by
        have hcol := InfoGeometry.Physics.ColorIsospinCharge.color_orthogonal_idempotent_partition
          (modeOccupied_idem 0) (modeOccupied_idem 1) (modeOccupied_idem 2)
          (modeOccupied_comm 0 1) (modeOccupied_comm 0 2) (modeOccupied_comm 1 2)
        rcases cl55_colorOccupationPolynomials_instantiation with ⟨hb, hv, _⟩
        rw [hb, hv] at hcol
        rcases hcol with ⟨_, ⟨_, _, _, _, _, _, _, _, _, hBV, _, _⟩, _⟩
        exact hBV
      change (Matrix.map colorBaryonSingletProj Complex.ofRealHom).mulVec
          ((Matrix.map colorVacuumSingletProj Complex.ofRealHom).mulVec
            (Pi.single cl55VacuumDiagIdx (1 : ℂ))) = 0
      rw [Matrix.mulVec_mulVec, ← Matrix.map_mul, hBV, Matrix.map_zero, Matrix.zero_mulVec]
      exact map_zero Complex.ofRealHom
  massGap := 1
  massGap_pos := by norm_num
  stringTension := 1
  stringTension_pos := by norm_num
  wilsonAreaExponent := fun area => -area
  area_law_bound := fun area _ => by ring
  energy := fun ψ =>
    if (Matrix.map colorBaryonSingletProj Complex.ofRealHom).toLin' ψ = ψ then 0 else 1
  energy_nonneg := fun ψ => by split_ifs <;> norm_num
  energy_zero_iff_hamiltonian_zero := fun ψ => by
    change (if (Matrix.map colorBaryonSingletProj Complex.ofRealHom).toLin' ψ = ψ then (0 : ℝ) else 1) = 0 ↔
      ((1 : Module.End ℂ (InfoGeometry.Clifford.TowerMatrix.Idx 5 → ℂ)) -
        (Matrix.map colorBaryonSingletProj Complex.ofRealHom).toLin') ψ = 0
    rw [LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]
    split_ifs with h
    · constructor
      · intro _
        exact h.symm
      · intro _
        rfl
    · constructor
      · intro h0
        norm_num at h0
      · intro heq
        exact (h heq.symm).elim
  non_singlet_mass_gap := fun ψ hne hker => by
    simp only [hker, Ne.symm hne, ↓reduceIte, le_refl]
  embedCl55 :=
    { toFun := fun M => (Matrix.map M Complex.ofRealHom).toLin'
      map_add' := fun M N => by
        apply LinearMap.ext
        intro v
        simp [Matrix.map_add]
      map_smul' := fun r M => by
        apply LinearMap.ext
        intro v
        funext i
        simp [Matrix.map_smul, Complex.real_smul, Matrix.mulVec, dotProduct,
          Finset.mul_sum, mul_assoc] }
  embedCl55_one := by
    apply LinearMap.ext
    intro v
    change (Matrix.map (1 : MatStage 5) Complex.ofRealHom).mulVec v = v
    simp
  embedCl55_mul := fun A B => by
    apply LinearMap.ext
    intro v
    change (Matrix.map (A * B) Complex.ofRealHom).mulVec v =
      (Matrix.map A Complex.ofRealHom).mulVec ((Matrix.map B Complex.ofRealHom).mulVec v)
    rw [Matrix.mulVec_mulVec, ← Matrix.map_mul]
  embedCl55_baryon_ne_zero :=
    cl55_toLin_ne_zero_of_trace_ne_zero (by rw [trace_colorFourSectors_cl55.2.2.2]; norm_num)
  embedCl55_colored_ne_zero :=
    cl55_toLin_ne_zero_of_trace_ne_zero
      (by rw [Matrix.trace_add, trace_colorFourSectors_cl55.2.1,
            trace_colorFourSectors_cl55.2.2.1]; norm_num)
  embed_baryon_into_singlet := by
    rcases cl55_color_isospin_orthogonal_idempotents with ⟨⟨_, _, _, hB⟩, _, _, _⟩
    apply LinearMap.ext
    intro v
    have hmul :
        (Matrix.map colorBaryonSingletProj Complex.ofRealHom) *
          (Matrix.map colorBaryonSingletProj Complex.ofRealHom) =
        Matrix.map colorBaryonSingletProj Complex.ofRealHom := by
      rw [← Matrix.map_mul, hB]
    change (Matrix.map colorBaryonSingletProj Complex.ofRealHom).mulVec v =
      (Matrix.map colorBaryonSingletProj Complex.ofRealHom).mulVec
        ((Matrix.map colorBaryonSingletProj Complex.ofRealHom).mulVec v)
    rw [Matrix.mulVec_mulVec, hmul]
  embed_baryon_range_in_singlet := by
    rcases cl55_color_isospin_orthogonal_idempotents with ⟨⟨_, _, _, hB⟩, _, _, _⟩
    apply LinearMap.ext
    intro v
    have hmul :
        (Matrix.map colorBaryonSingletProj Complex.ofRealHom) *
          (Matrix.map colorBaryonSingletProj Complex.ofRealHom) =
        Matrix.map colorBaryonSingletProj Complex.ofRealHom := by
      rw [← Matrix.map_mul, hB]
    change (Matrix.map colorBaryonSingletProj Complex.ofRealHom).mulVec
        ((Matrix.map colorBaryonSingletProj Complex.ofRealHom).mulVec v) =
      (Matrix.map colorBaryonSingletProj Complex.ofRealHom).mulVec v
    rw [Matrix.mulVec_mulVec, hmul]
  embed_colored_annihilates_singlet := by
    have hcol := InfoGeometry.Physics.ColorIsospinCharge.color_orthogonal_idempotent_partition
      (modeOccupied_idem 0) (modeOccupied_idem 1) (modeOccupied_idem 2)
      (modeOccupied_comm 0 1) (modeOccupied_comm 0 2) (modeOccupied_comm 1 2)
    rcases cl55_colorOccupationPolynomials_instantiation with ⟨hb, _, hq, hd, _⟩
    rw [hb, hq, hd] at hcol
    rcases hcol with ⟨_, ⟨_, _, _, _, _, h13, _, _, h23, _, _, _⟩, _⟩
    have hmul : (colorQuarkTripletProj + colorDiquarkAntitripletProj) * colorBaryonSingletProj = 0 := by
      rw [add_mul, h13, h23, add_zero]
    apply LinearMap.ext
    intro v
    change (Matrix.map (colorQuarkTripletProj + colorDiquarkAntitripletProj) Complex.ofRealHom).mulVec
        ((Matrix.map colorBaryonSingletProj Complex.ofRealHom).mulVec v) = 0
    rw [Matrix.mulVec_mulVec, ← Matrix.map_mul, hmul]
    simp
  embed_colored_range_annihilates_singlet := by
    have hcol := InfoGeometry.Physics.ColorIsospinCharge.color_orthogonal_idempotent_partition
      (modeOccupied_idem 0) (modeOccupied_idem 1) (modeOccupied_idem 2)
      (modeOccupied_comm 0 1) (modeOccupied_comm 0 2) (modeOccupied_comm 1 2)
    rcases cl55_colorOccupationPolynomials_instantiation with ⟨hb, _, hq, hd, _⟩
    rw [hb, hq, hd] at hcol
    rcases hcol with ⟨_, ⟨_, _, _, _, _, _, _, _, _, _, h31, h32⟩, _⟩
    have hmul : colorBaryonSingletProj * (colorQuarkTripletProj + colorDiquarkAntitripletProj) = 0 := by
      rw [mul_add, h31, h32, add_zero]
    apply LinearMap.ext
    intro v
    change (Matrix.map colorBaryonSingletProj Complex.ofRealHom).mulVec
        ((Matrix.map (colorQuarkTripletProj + colorDiquarkAntitripletProj) Complex.ofRealHom).mulVec v) = 0
    rw [Matrix.mulVec_mulVec, ← Matrix.map_mul, hmul]
    simp

/-- Conditional dynamical bridge coupling a `ContinuumQCDConfinementHypothesis` to the
    unconditional finite Seam B algebraic structures (Zorn baryons, `Cl(5,5)` Casimir,
    `Z₃` parafermion Drazin projector, non-abelian `B₃` monodromy commuting with both
    `singletProjector` and `hamiltonian`, and exact-order-12 `G₂` spin lift). -/
structure DynamicalQCDConfinementBridge (hyp : ContinuumQCDConfinementHypothesis) where
  artinLift : G2SpinOperatorLift
  artinLift_exact_order12 :
    ∀ k : ℕ, 0 < k → k < 12 → (artinLift.Bs * artinLift.Bl) ^ k ≠ 1
  b3Rep : B3 →* (ThreeStrandOperator)ˣ
  b3Rep_noncomm :
    (b3Rep (PresentedGroup.of B3Gen.sig0 : B3) : ThreeStrandOperator) *
      (b3Rep (PresentedGroup.of B3Gen.sig1 : B3) : ThreeStrandOperator) ≠
    (b3Rep (PresentedGroup.of B3Gen.sig1 : B3) : ThreeStrandOperator) *
      (b3Rep (PresentedGroup.of B3Gen.sig0 : B3) : ThreeStrandOperator)
  monodromyAction : B3 →* (Module.End ℂ hyp.ContinuumState)ˣ
  monodromy_comm_singlet :
    ∀ g : B3,
      (monodromyAction g : Module.End ℂ hyp.ContinuumState).comp hyp.singletProjector =
        hyp.singletProjector.comp (monodromyAction g : Module.End ℂ hyp.ContinuumState)
  monodromyCommutesWithHamiltonian :
    ∀ g : B3,
      (monodromyAction g : Module.End ℂ hyp.ContinuumState).comp hyp.hamiltonian =
        hyp.hamiltonian.comp (monodromyAction g : Module.End ℂ hyp.ContinuumState)
  monodromy_noncomm :
    (monodromyAction (PresentedGroup.of B3Gen.sig0 : B3) : Module.End ℂ hyp.ContinuumState) *
      (monodromyAction (PresentedGroup.of B3Gen.sig1 : B3) : Module.End ℂ hyp.ContinuumState) ≠
    (monodromyAction (PresentedGroup.of B3Gen.sig1 : B3) : Module.End ℂ hyp.ContinuumState) *
      (monodromyAction (PresentedGroup.of B3Gen.sig0 : B3) : Module.End ℂ hyp.ContinuumState)
  monodromy_noncomm_on_non_singlet :
    ∃ ψ : hyp.ContinuumState,
      hyp.singletProjector ψ = 0 ∧
      ((monodromyAction (PresentedGroup.of B3Gen.sig0 : B3) :
          Module.End ℂ hyp.ContinuumState) *
        (monodromyAction (PresentedGroup.of B3Gen.sig1 : B3) :
          Module.End ℂ hyp.ContinuumState)) ψ ≠
      ((monodromyAction (PresentedGroup.of B3Gen.sig1 : B3) :
          Module.End ℂ hyp.ContinuumState) *
        (monodromyAction (PresentedGroup.of B3Gen.sig0 : B3) :
          Module.End ℂ hyp.ContinuumState)) ψ
  zornToContinuum :
    GaugedZornDiracKahler.ZornMatrix ℝ →ₗ[ℝ] Module.End ℂ hyp.ContinuumState
  zorn_factors_through_cl55 :
    ∀ X : GaugedZornDiracKahler.ZornMatrix ℝ,
      zornToContinuum X = hyp.embedCl55 (zornBaryonToCl55Singlet X)

private theorem modeOccupied2_eq_kron :
    modeOccupied 2 =
      (((1 : MatStage 2) ⊗ₖ
          (InfoGeometry.Clifford.Cl11TensorTower.wittCreationBase *
            InfoGeometry.Clifford.Cl11TensorTower.wittAnnihilationBase)) ⊗ₖ
        (1 : Matrix (Fin 2) (Fin 2) ℝ)) ⊗ₖ
        (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  have he2 :
      e 2 =
        ((InfoGeometry.Clifford.Cl11TensorTower.globalChirality 2 ⊗ₖ
            InfoGeometry.Clifford.Cl11TensorTower.wittCreationBase) ⊗ₖ
          (1 : Matrix (Fin 2) (Fin 2) ℝ)) ⊗ₖ
          (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
    simp [e, InfoGeometry.Canonical.Cl55WittCAR.creation,
      InfoGeometry.Clifford.Cl11TensorTower.jwCreation,
      InfoGeometry.Clifford.Cl11TensorTower.jwStringWithBase]
    rfl
  have hf2 :
      f 2 =
        ((InfoGeometry.Clifford.Cl11TensorTower.globalChirality 2 ⊗ₖ
            InfoGeometry.Clifford.Cl11TensorTower.wittAnnihilationBase) ⊗ₖ
          (1 : Matrix (Fin 2) (Fin 2) ℝ)) ⊗ₖ
          (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
    simp [f, InfoGeometry.Canonical.Cl55WittCAR.annihilation,
      InfoGeometry.Clifford.Cl11TensorTower.jwAnnihilation,
      InfoGeometry.Clifford.Cl11TensorTower.jwStringWithBase]
    rfl
  dsimp [modeOccupied]
  rw [he2, hf2]
  change
    ((((InfoGeometry.Clifford.Cl11TensorTower.globalChirality 2 ⊗ₖ
          InfoGeometry.Clifford.Cl11TensorTower.wittCreationBase) ⊗ₖ
        (1 : Matrix (Fin 2) (Fin 2) ℝ)) ⊗ₖ
        (1 : Matrix (Fin 2) (Fin 2) ℝ)) *
      (((InfoGeometry.Clifford.Cl11TensorTower.globalChirality 2 ⊗ₖ
          InfoGeometry.Clifford.Cl11TensorTower.wittAnnihilationBase) ⊗ₖ
        (1 : Matrix (Fin 2) (Fin 2) ℝ)) ⊗ₖ
        (1 : Matrix (Fin 2) (Fin 2) ℝ))) = _
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
  rw [InfoGeometry.Clifford.JordanWignerCAR.globalChirality_sq 2, mul_one]

private theorem modeOccupied2_eq_zero_of_left
    {x y : InfoGeometry.Clifford.TowerMatrix.Idx 5} (hx : x.1.1.2 = 1) :
    modeOccupied 2 x y = 0 := by
  rw [modeOccupied2_eq_kron]
  have hbase : ∀ b : Fin 2,
      (InfoGeometry.Clifford.Cl11TensorTower.wittCreationBase *
        InfoGeometry.Clifford.Cl11TensorTower.wittAnnihilationBase) 1 b = 0 := by
    intro b
    fin_cases b <;>
      norm_num [InfoGeometry.Clifford.Cl11TensorTower.wittCreationBase,
        InfoGeometry.Clifford.Cl11TensorTower.wittAnnihilationBase,
        Matrix.mul_apply, Fin.sum_univ_two]
  change
    (1 : MatStage 2) x.1.1.1 y.1.1.1 *
      ((InfoGeometry.Clifford.Cl11TensorTower.wittCreationBase *
        InfoGeometry.Clifford.Cl11TensorTower.wittAnnihilationBase) x.1.1.2 y.1.1.2) *
      (1 : Matrix (Fin 2) (Fin 2) ℝ) x.1.2 y.1.2 *
      (1 : Matrix (Fin 2) (Fin 2) ℝ) x.2 y.2 = 0
  rw [hx, hbase y.1.1.2]
  ring

private theorem modeOccupied2_eq_zero_of_right
    {x y : InfoGeometry.Clifford.TowerMatrix.Idx 5} (hy : y.1.1.2 = 1) :
    modeOccupied 2 x y = 0 := by
  rw [modeOccupied2_eq_kron]
  have hbase : ∀ a : Fin 2,
      (InfoGeometry.Clifford.Cl11TensorTower.wittCreationBase *
        InfoGeometry.Clifford.Cl11TensorTower.wittAnnihilationBase) a 1 = 0 := by
    intro a
    fin_cases a <;>
      norm_num [InfoGeometry.Clifford.Cl11TensorTower.wittCreationBase,
        InfoGeometry.Clifford.Cl11TensorTower.wittAnnihilationBase,
        Matrix.mul_apply, Fin.sum_univ_two]
  change
    (1 : MatStage 2) x.1.1.1 y.1.1.1 *
      ((InfoGeometry.Clifford.Cl11TensorTower.wittCreationBase *
        InfoGeometry.Clifford.Cl11TensorTower.wittAnnihilationBase) x.1.1.2 y.1.1.2) *
      (1 : Matrix (Fin 2) (Fin 2) ℝ) x.1.2 y.1.2 *
      (1 : Matrix (Fin 2) (Fin 2) ℝ) x.2 y.2 = 0
  rw [hy, hbase x.1.1.2]
  ring

private theorem colorBaryonSingletProj_eq_zero_of_left
    {x y : InfoGeometry.Clifford.TowerMatrix.Idx 5} (hx : x.1.1.2 = 1) :
    colorBaryonSingletProj x y = 0 := by
  have hreorder : colorBaryonSingletProj = modeOccupied 2 * (modeOccupied 0 * modeOccupied 1) := by
    dsimp [colorBaryonSingletProj]
    calc
      modeOccupied 0 * modeOccupied 1 * modeOccupied 2 =
          modeOccupied 0 * (modeOccupied 1 * modeOccupied 2) := by rw [mul_assoc]
      _ = modeOccupied 0 * (modeOccupied 2 * modeOccupied 1) := by rw [modeOccupied_comm 1 2]
      _ = (modeOccupied 0 * modeOccupied 2) * modeOccupied 1 := by rw [← mul_assoc]
      _ = (modeOccupied 2 * modeOccupied 0) * modeOccupied 1 := by rw [modeOccupied_comm 0 2]
      _ = modeOccupied 2 * (modeOccupied 0 * modeOccupied 1) := by rw [mul_assoc]
  rw [hreorder, Matrix.mul_apply]
  exact Finset.sum_eq_zero fun z _ => by rw [modeOccupied2_eq_zero_of_left hx, zero_mul]

private theorem colorBaryonSingletProj_eq_zero_of_right
    {x y : InfoGeometry.Clifford.TowerMatrix.Idx 5} (hy : y.1.1.2 = 1) :
    colorBaryonSingletProj x y = 0 := by
  change (modeOccupied 0 * modeOccupied 1 * modeOccupied 2) x y = 0
  rw [Matrix.mul_apply]
  exact Finset.sum_eq_zero fun z _ => by rw [modeOccupied2_eq_zero_of_right hy, mul_zero]

private def threeStrandToCl55 :
    ThreeStrandState →ₗ[ℂ] (InfoGeometry.Clifford.TowerMatrix.Idx 5 → ℂ) where
  toFun ψ idx :=
    if idx.1.1.1.2 = 0 ∧ idx.1.1.2 = 1 then ψ idx.1.1.1.1.2 idx.1.2 idx.2 else 0
  map_add' ψ φ := by
    funext idx
    simp only [Pi.add_apply]
    split_ifs <;> simp
  map_smul' c ψ := by
    funext idx
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> simp

private def idx0Zero : InfoGeometry.Clifford.TowerMatrix.Idx 0 := (0 : Fin 1)

private def embedIdx5 (i j k : Fin 2) : InfoGeometry.Clifford.TowerMatrix.Idx 5 :=
  (((((idx0Zero, i), (0 : Fin 2)), (1 : Fin 2)), j), k)

private theorem embedIdx5_mode2 (i j k : Fin 2) :
    (embedIdx5 i j k).1.1.2 = 1 := rfl

private def cl55ToThreeStrand :
    (InfoGeometry.Clifford.TowerMatrix.Idx 5 → ℂ) →ₗ[ℂ] ThreeStrandState where
  toFun v i j k := v (embedIdx5 i j k)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem cl55ToThreeStrand_comp_threeStrandToCl55 :
    cl55ToThreeStrand.comp threeStrandToCl55 = (1 : ThreeStrandOperator) := by
  apply LinearMap.ext
  intro ψ
  funext i j k
  simp [cl55ToThreeStrand, threeStrandToCl55, embedIdx5]

private def cl55SingletProjEnd : Module.End ℂ (InfoGeometry.Clifford.TowerMatrix.Idx 5 → ℂ) :=
  (Matrix.map colorBaryonSingletProj Complex.ofRealHom).toLin'

private theorem singletProjector_comp_threeStrandToCl55 :
    cl55SingletProjEnd.comp threeStrandToCl55 = 0 := by
  apply LinearMap.ext
  intro ψ
  funext x
  change (Matrix.map colorBaryonSingletProj Complex.ofRealHom).mulVec (threeStrandToCl55 ψ) x = 0
  dsimp [Matrix.mulVec, dotProduct]
  refine Finset.sum_eq_zero fun y _ => ?_
  dsimp [threeStrandToCl55]
  split_ifs with h
  · rw [colorBaryonSingletProj_eq_zero_of_right h.2, Complex.ofReal_zero, zero_mul]
  · rw [mul_zero]

private theorem cl55ToThreeStrand_comp_singletProjector :
    cl55ToThreeStrand.comp cl55SingletProjEnd = 0 := by
  apply LinearMap.ext
  intro v
  funext i j k
  change (Matrix.map colorBaryonSingletProj Complex.ofRealHom).mulVec v (embedIdx5 i j k) = 0
  dsimp [Matrix.mulVec, dotProduct]
  refine Finset.sum_eq_zero fun y _ => ?_
  change (colorBaryonSingletProj (embedIdx5 i j k) y : ℂ) * v y = 0
  rw [colorBaryonSingletProj_eq_zero_of_left (embedIdx5_mode2 i j k),
    Complex.ofReal_zero, zero_mul]

private def liftThreeStrandOp (U : ThreeStrandOperator) :
    Module.End ℂ (InfoGeometry.Clifford.TowerMatrix.Idx 5 → ℂ) :=
  1 + threeStrandToCl55.comp ((U - 1).comp cl55ToThreeStrand)

private theorem liftThreeStrandOp_one : liftThreeStrandOp 1 = 1 := by
  simp [liftThreeStrandOp]

private theorem liftThreeStrandOp_mul (U V : ThreeStrandOperator) :
    liftThreeStrandOp (U * V) = liftThreeStrandOp U * liftThreeStrandOp V := by
  dsimp [liftThreeStrandOp]
  change 1 + threeStrandToCl55.comp (((U.comp V) - 1).comp cl55ToThreeStrand) =
    (1 + threeStrandToCl55.comp ((U - 1).comp cl55ToThreeStrand)).comp
      (1 + threeStrandToCl55.comp ((V - 1).comp cl55ToThreeStrand))
  apply LinearMap.ext
  intro v
  have hret : ∀ φ : ThreeStrandState, cl55ToThreeStrand (threeStrandToCl55 φ) = φ := by
    intro φ
    exact congrFun (congrArg DFunLike.coe cl55ToThreeStrand_comp_threeStrandToCl55) φ
  simp only [LinearMap.add_apply, Module.End.one_apply, LinearMap.comp_apply,
    LinearMap.sub_apply, map_add, map_sub, hret]
  abel

private theorem liftThreeStrandOp_comm_singlet (U : ThreeStrandOperator) :
    (liftThreeStrandOp U).comp cl55SingletProjEnd =
      cl55SingletProjEnd.comp (liftThreeStrandOp U) := by
  have hL :
      (liftThreeStrandOp U).comp cl55SingletProjEnd = cl55SingletProjEnd := by
    apply LinearMap.ext
    intro v
    have h0 : cl55ToThreeStrand (cl55SingletProjEnd v) = 0 :=
      congrFun (congrArg DFunLike.coe cl55ToThreeStrand_comp_singletProjector) v
    rw [LinearMap.comp_apply, liftThreeStrandOp, LinearMap.add_apply, Module.End.one_apply,
      LinearMap.comp_apply, LinearMap.comp_apply, h0, map_zero, map_zero, add_zero]
  have hR :
      cl55SingletProjEnd.comp (liftThreeStrandOp U) = cl55SingletProjEnd := by
    apply LinearMap.ext
    intro v
    have h0 : cl55SingletProjEnd (threeStrandToCl55 ((U - 1) (cl55ToThreeStrand v))) = 0 :=
      congrFun (congrArg DFunLike.coe singletProjector_comp_threeStrandToCl55) _
    rw [LinearMap.comp_apply, liftThreeStrandOp, LinearMap.add_apply, Module.End.one_apply,
      LinearMap.comp_apply, LinearMap.comp_apply, map_add, h0, add_zero]
  rw [hL, hR]

private def liftThreeStrandUnitHom :
    (ThreeStrandOperator)ˣ →*
      (Module.End ℂ (InfoGeometry.Clifford.TowerMatrix.Idx 5 → ℂ))ˣ where
  toFun u :=
    { val := liftThreeStrandOp u.val
      inv := liftThreeStrandOp u.inv
      val_inv := by rw [← liftThreeStrandOp_mul, u.val_inv, liftThreeStrandOp_one]
      inv_val := by rw [← liftThreeStrandOp_mul, u.inv_val, liftThreeStrandOp_one] }
  map_one' := by
    apply Units.ext
    exact liftThreeStrandOp_one
  map_mul' u v := by
    apply Units.ext
    exact liftThreeStrandOp_mul u.val v.val

/-- Constructive T17 witness for `DynamicalQCDConfinementBridge cl55ModelContinuumHypothesis`
    with non-abelian lifted `B₃` monodromy commuting with both `singletProjector` and `hamiltonian`. -/
def cl55ModelDynamicalBridge :
    DynamicalQCDConfinementBridge cl55ModelContinuumHypothesis where
  artinLift := canonicalG2SpinOperatorLift
  artinLift_exact_order12 := canonicalG2SpinOperatorLift_exact_order12
  b3Rep := threeStrandB3Representation
  b3Rep_noncomm := threeStrandB3Representation_noncomm
  monodromyAction := liftThreeStrandUnitHom.comp threeStrandB3Representation
  monodromy_comm_singlet g := liftThreeStrandOp_comm_singlet _
  monodromyCommutesWithHamiltonian g := by
    have hsing := liftThreeStrandOp_comm_singlet
      (threeStrandB3Representation g : ThreeStrandOperator)
    change (liftThreeStrandOp (threeStrandB3Representation g : ThreeStrandOperator)).comp
        ((1 : Module.End ℂ (InfoGeometry.Clifford.TowerMatrix.Idx 5 → ℂ)) - cl55SingletProjEnd) =
      ((1 : Module.End ℂ (InfoGeometry.Clifford.TowerMatrix.Idx 5 → ℂ)) - cl55SingletProjEnd).comp
        (liftThreeStrandOp (threeStrandB3Representation g : ThreeStrandOperator))
    apply LinearMap.ext
    intro v
    have hsing_v := congrArg
      (fun T : Module.End ℂ (InfoGeometry.Clifford.TowerMatrix.Idx 5 → ℂ) => T v) hsing
    change
      (liftThreeStrandOp (threeStrandB3Representation g : ThreeStrandOperator))
          (v - cl55SingletProjEnd v) =
        (liftThreeStrandOp (threeStrandB3Representation g : ThreeStrandOperator)) v -
          cl55SingletProjEnd
            ((liftThreeStrandOp (threeStrandB3Representation g : ThreeStrandOperator)) v)
    rw [map_sub]
    change
      (liftThreeStrandOp (threeStrandB3Representation g : ThreeStrandOperator)) v -
          ((liftThreeStrandOp (threeStrandB3Representation g : ThreeStrandOperator)).comp
            cl55SingletProjEnd) v =
        (liftThreeStrandOp (threeStrandB3Representation g : ThreeStrandOperator)) v -
          (cl55SingletProjEnd.comp
            (liftThreeStrandOp (threeStrandB3Representation g : ThreeStrandOperator))) v
    rw [hsing_v]
  monodromy_noncomm := by
    intro h
    have hsub :
        (threeStrandB3Representation (PresentedGroup.of B3Gen.sig0 : B3) : ThreeStrandOperator) *
          (threeStrandB3Representation (PresentedGroup.of B3Gen.sig1 : B3) : ThreeStrandOperator) =
        (threeStrandB3Representation (PresentedGroup.of B3Gen.sig1 : B3) : ThreeStrandOperator) *
          (threeStrandB3Representation (PresentedGroup.of B3Gen.sig0 : B3) : ThreeStrandOperator) := by
      apply LinearMap.ext
      intro ψ
      have hψ := congrArg
        (fun T : Module.End ℂ (InfoGeometry.Clifford.TowerMatrix.Idx 5 → ℂ) =>
          cl55ToThreeStrand (T (threeStrandToCl55 ψ))) h
      have hret : ∀ φ : ThreeStrandState, cl55ToThreeStrand (threeStrandToCl55 φ) = φ := by
        intro φ
        exact congrFun (congrArg DFunLike.coe cl55ToThreeStrand_comp_threeStrandToCl55) φ
      have hlift : ∀ (U : ThreeStrandOperator) (φ : ThreeStrandState),
          liftThreeStrandOp U (threeStrandToCl55 φ) = threeStrandToCl55 (U φ) := by
        intro U φ
        simp [liftThreeStrandOp, hret]
      change
        cl55ToThreeStrand
            (liftThreeStrandOp
                (threeStrandB3Representation (PresentedGroup.of B3Gen.sig0 : B3) : ThreeStrandOperator)
              (liftThreeStrandOp
                  (threeStrandB3Representation (PresentedGroup.of B3Gen.sig1 : B3) : ThreeStrandOperator)
                (threeStrandToCl55 ψ))) =
          cl55ToThreeStrand
            (liftThreeStrandOp
                (threeStrandB3Representation (PresentedGroup.of B3Gen.sig1 : B3) : ThreeStrandOperator)
              (liftThreeStrandOp
                  (threeStrandB3Representation (PresentedGroup.of B3Gen.sig0 : B3) : ThreeStrandOperator)
                (threeStrandToCl55 ψ))) at hψ
      rw [hlift, hlift, hlift, hlift, hret, hret] at hψ
      exact hψ
    exact threeStrandB3Representation_noncomm hsub
  monodromy_noncomm_on_non_singlet := by
    let ψ₀ : ThreeStrandState := fun i j k => if i = 0 ∧ j = 1 ∧ k = 0 then 1 else 0
    refine ⟨threeStrandToCl55 ψ₀, ?_, ?_⟩
    · exact congrFun (congrArg DFunLike.coe singletProjector_comp_threeStrandToCl55) ψ₀
    · intro h
      have hret : ∀ φ : ThreeStrandState, cl55ToThreeStrand (threeStrandToCl55 φ) = φ := by
        intro φ
        exact congrFun (congrArg DFunLike.coe cl55ToThreeStrand_comp_threeStrandToCl55) φ
      have hlift : ∀ (U : ThreeStrandOperator) (φ : ThreeStrandState),
          liftThreeStrandOp U (threeStrandToCl55 φ) = threeStrandToCl55 (U φ) := by
        intro U φ
        simp [liftThreeStrandOp, hret]
      have hval := congrArg (fun v => cl55ToThreeStrand v 0 0 1) h
      change
        cl55ToThreeStrand
            (liftThreeStrandOp
                (threeStrandB3Representation (PresentedGroup.of B3Gen.sig0 : B3) : ThreeStrandOperator)
              (liftThreeStrandOp
                  (threeStrandB3Representation (PresentedGroup.of B3Gen.sig1 : B3) : ThreeStrandOperator)
                (threeStrandToCl55 ψ₀))) 0 0 1 =
          cl55ToThreeStrand
            (liftThreeStrandOp
                (threeStrandB3Representation (PresentedGroup.of B3Gen.sig1 : B3) : ThreeStrandOperator)
              (liftThreeStrandOp
                  (threeStrandB3Representation (PresentedGroup.of B3Gen.sig0 : B3) : ThreeStrandOperator)
                (threeStrandToCl55 ψ₀))) 0 0 1 at hval
      rw [hlift, hlift, hlift, hlift, hret, hret] at hval
      simp [threeStrandB3Representation_sig0, threeStrandB3Representation_sig1,
        standardJonesBraid12Unit, standardJonesBraid23Unit,
        standardJonesBraid12, standardJonesBraid23, E12, E23, e12, e23, ψ₀] at hval
  zornToContinuum := cl55ModelContinuumHypothesis.embedCl55.comp zornBaryonToCl55SingletLinear
  zorn_factors_through_cl55 X := rfl

theorem dynamical_zorn_baryon_lands_in_continuum_singlet
    {hyp : ContinuumQCDConfinementHypothesis}
    (bridge : DynamicalQCDConfinementBridge hyp)
    (u v w : Vec3 ℝ) :
    bridge.zornToContinuum (baryonState u v w) =
      (dot3 (cross3 u v) w) • hyp.embedCl55 colorBaryonSingletProj ∧
    (bridge.zornToContinuum (baryonState u v w)).comp hyp.singletProjector =
      bridge.zornToContinuum (baryonState u v w) ∧
    hyp.singletProjector.comp (bridge.zornToContinuum (baryonState u v w)) =
      bridge.zornToContinuum (baryonState u v w) ∧
    hyp.hamiltonian.comp (bridge.zornToContinuum (baryonState u v w)) = 0 ∧
    (∀ ψ : hyp.ContinuumState,
      hyp.energy (bridge.zornToContinuum (baryonState u v w) ψ) = 0) ∧
    bridge.zornToContinuum (baryonState colorE0 colorE1 colorE2) ≠ 0 := by
  have hfac : bridge.zornToContinuum (baryonState u v w) =
      (dot3 (cross3 u v) w) • hyp.embedCl55 colorBaryonSingletProj := by
    rw [bridge.zorn_factors_through_cl55, (zornBaryonToCl55_bridge u v w 0 0 0 0).2.1,
      LinearMap.map_smul]
  have hright :
      (bridge.zornToContinuum (baryonState u v w)).comp hyp.singletProjector =
        bridge.zornToContinuum (baryonState u v w) := by
    rw [hfac, LinearMap.smul_comp, ← hyp.embed_baryon_into_singlet]
  have hleft :
      hyp.singletProjector.comp (bridge.zornToContinuum (baryonState u v w)) =
        bridge.zornToContinuum (baryonState u v w) := by
    rw [hfac]
    apply LinearMap.ext
    intro ψ
    change hyp.singletProjector
        ((dot3 (cross3 u v) w) • hyp.embedCl55 colorBaryonSingletProj ψ) =
      (dot3 (cross3 u v) w) • hyp.embedCl55 colorBaryonSingletProj ψ
    have hsmul : ∀ (r : ℝ) (x : hyp.ContinuumState),
        hyp.singletProjector (r • x) = r • hyp.singletProjector x := by
      intro r x
      change hyp.singletProjector (((r : ℝ) : ℂ) • x) = ((r : ℝ) : ℂ) • hyp.singletProjector x
      exact hyp.singletProjector.map_smul ((r : ℝ) : ℂ) x
    rw [hsmul]
    have hrange := congrArg
      (fun T : Module.End ℂ hyp.ContinuumState => T ψ) hyp.embed_baryon_range_in_singlet
    change hyp.singletProjector (hyp.embedCl55 colorBaryonSingletProj ψ) =
      hyp.embedCl55 colorBaryonSingletProj ψ at hrange
    rw [hrange]
  have hham : hyp.hamiltonian.comp (bridge.zornToContinuum (baryonState u v w)) = 0 := by
    calc
      hyp.hamiltonian.comp (bridge.zornToContinuum (baryonState u v w)) =
          hyp.hamiltonian.comp
            (hyp.singletProjector.comp (bridge.zornToContinuum (baryonState u v w))) := by
        rw [hleft]
      _ = (hyp.hamiltonian.comp hyp.singletProjector).comp
            (bridge.zornToContinuum (baryonState u v w)) := by
        rw [LinearMap.comp_assoc]
      _ = 0 := by rw [hyp.hamiltonian_comp_singlet, LinearMap.zero_comp]
  have henergy :
      ∀ ψ : hyp.ContinuumState,
        hyp.energy (bridge.zornToContinuum (baryonState u v w) ψ) = 0 := by
    intro ψ
    rw [hyp.energy_zero_iff_hamiltonian_zero]
    exact congrArg (fun T : Module.End ℂ hyp.ContinuumState => T ψ) hham
  have hne : bridge.zornToContinuum (baryonState colorE0 colorE1 colorE2) ≠ 0 := by
    rw [bridge.zorn_factors_through_cl55, (zornBaryonToCl55_bridge colorE0 colorE1 colorE2 0 0 0 0).1]
    exact hyp.embedCl55_baryon_ne_zero
  exact ⟨hfac, hright, hleft, hham, henergy, hne⟩

theorem dynamical_casimir_and_drazin_annihilate_continuum_singlet
    (hyp : ContinuumQCDConfinementHypothesis) :
    (hyp.embedCl55 colorSU3Casimir).comp hyp.singletProjector = 0 ∧
    (hyp.embedCl55 (drazin_projector colorSectorTripotent)).comp hyp.singletProjector = 0 ∧
    hyp.singletProjector.comp (hyp.embedCl55 colorSU3Casimir) = 0 ∧
    hyp.singletProjector.comp (hyp.embedCl55 (drazin_projector colorSectorTripotent)) = 0 ∧
    hyp.embedCl55 (drazin_projector colorSectorTripotent) ≠ 0 := by
  have hdraz : (hyp.embedCl55 (drazin_projector colorSectorTripotent)).comp hyp.singletProjector = 0 := by
    rw [colorSectorTripotent_projectors.2.2.2]
    exact hyp.embed_colored_annihilates_singlet
  have hdrazR : hyp.singletProjector.comp (hyp.embedCl55 (drazin_projector colorSectorTripotent)) = 0 := by
    rw [colorSectorTripotent_projectors.2.2.2]
    exact hyp.embed_colored_range_annihilates_singlet
  have hcas : (hyp.embedCl55 colorSU3Casimir).comp hyp.singletProjector = 0 := by
    rw [colorSU3Casimir_eq_smul_drazin, LinearMap.map_smul, LinearMap.smul_comp, hdraz, smul_zero]
  have hcasR : hyp.singletProjector.comp (hyp.embedCl55 colorSU3Casimir) = 0 := by
    rw [colorSU3Casimir_eq_smul_drazin, LinearMap.map_smul]
    apply LinearMap.ext
    intro ψ
    change hyp.singletProjector
        ((4 / 3 : ℝ) • hyp.embedCl55 (drazin_projector colorSectorTripotent) ψ) = 0
    have hsmul : ∀ (r : ℝ) (x : hyp.ContinuumState),
        hyp.singletProjector (r • x) = r • hyp.singletProjector x := by
      intro r x
      change hyp.singletProjector (((r : ℝ) : ℂ) • x) = ((r : ℝ) : ℂ) • hyp.singletProjector x
      exact hyp.singletProjector.map_smul ((r : ℝ) : ℂ) x
    rw [hsmul]
    have h0 := congrArg (fun T : Module.End ℂ hyp.ContinuumState => T ψ) hdrazR
    change hyp.singletProjector (hyp.embedCl55 (drazin_projector colorSectorTripotent) ψ) = 0 at h0
    rw [h0, smul_zero]
  have hne : hyp.embedCl55 (drazin_projector colorSectorTripotent) ≠ 0 := by
    rw [colorSectorTripotent_projectors.2.2.2]
    exact hyp.embedCl55_colored_ne_zero
  exact ⟨hcas, hdraz, hcasR, hdrazR, hne⟩

theorem dynamical_monodromy_preserves_non_singlet_mass_gap
    {hyp : ContinuumQCDConfinementHypothesis}
    (bridge : DynamicalQCDConfinementBridge hyp)
    (g : B3) (ψ : hyp.ContinuumState)
    (hne : ψ ≠ 0) (hker : hyp.singletProjector ψ = 0) :
    hyp.massGap ≤ hyp.energy ((bridge.monodromyAction g : Module.End ℂ hyp.ContinuumState) ψ) ∧
    hyp.hamiltonian ((bridge.monodromyAction g : Module.End ℂ hyp.ContinuumState) ψ) ≠ 0 ∧
    (bridge.artinLift.Bs * bridge.artinLift.Bl) ^ 12 = 1 ∧
    (∀ k : ℕ, 0 < k → k < 12 → (bridge.artinLift.Bs * bridge.artinLift.Bl) ^ k ≠ 1) := by
  have hg_ne : (bridge.monodromyAction g : Module.End ℂ hyp.ContinuumState) ψ ≠ 0 := by
    intro h0
    let gInv : Module.End ℂ hyp.ContinuumState :=
      ((bridge.monodromyAction g)⁻¹ : (Module.End ℂ hyp.ContinuumState)ˣ)
    have hinv : gInv ((bridge.monodromyAction g : Module.End ℂ hyp.ContinuumState) ψ) = 0 := by
      rw [h0, map_zero]
    have hcomp :
        (gInv.comp (bridge.monodromyAction g : Module.End ℂ hyp.ContinuumState)) ψ =
          (1 : Module.End ℂ hyp.ContinuumState) ψ := by
      have hu : ((bridge.monodromyAction g)⁻¹ * bridge.monodromyAction g :
          (Module.End ℂ hyp.ContinuumState)ˣ) = 1 := inv_mul_cancel _
      exact congrArg
        (fun u : (Module.End ℂ hyp.ContinuumState)ˣ => (u : Module.End ℂ hyp.ContinuumState) ψ) hu
    change gInv ((bridge.monodromyAction g : Module.End ℂ hyp.ContinuumState) ψ) = ψ at hcomp
    rw [hinv] at hcomp
    exact hne hcomp.symm
  have hg_ker :
      hyp.singletProjector ((bridge.monodromyAction g : Module.End ℂ hyp.ContinuumState) ψ) = 0 := by
    have hc := congrArg (fun T : Module.End ℂ hyp.ContinuumState => T ψ) (bridge.monodromy_comm_singlet g)
    change (bridge.monodromyAction g : Module.End ℂ hyp.ContinuumState) (hyp.singletProjector ψ) =
      hyp.singletProjector ((bridge.monodromyAction g : Module.End ℂ hyp.ContinuumState) ψ) at hc
    rw [← hc, hker, map_zero]
  have hgap := hyp.non_singlet_mass_gap _ hg_ne hg_ker
  have hham : hyp.hamiltonian ((bridge.monodromyAction g : Module.End ℂ hyp.ContinuumState) ψ) ≠ 0 := by
    intro h0
    have he0 : hyp.energy ((bridge.monodromyAction g : Module.End ℂ hyp.ContinuumState) ψ) = 0 :=
      (hyp.energy_zero_iff_hamiltonian_zero _).mpr h0
    have hlt : (0 : ℝ) < 0 := lt_of_lt_of_le hyp.massGap_pos (he0 ▸ hgap)
    exact lt_irrefl (0 : ℝ) hlt
  exact ⟨hgap, hham, bridge.artinLift.spin_coxeter_pow_twelve, bridge.artinLift_exact_order12⟩

theorem dynamical_wilson_area_law_strictly_decaying
    (hyp : ContinuumQCDConfinementHypothesis) {area : ℝ} (harea : 0 < area) :
    hyp.wilsonAreaExponent area < 0 := by
  rw [hyp.area_law_bound area (le_of_lt harea)]
  exact neg_lt_zero.mpr (mul_pos hyp.stringTension_pos harea)

end InfoGeometry.Synthesis.QCDColorConfinementParafermionSynthesis

end noncomputable section
