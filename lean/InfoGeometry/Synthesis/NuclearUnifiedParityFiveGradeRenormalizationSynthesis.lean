/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Tactic
import InfoGeometry.Synthesis.NuclearFiveGradeSuperGrassmannianIntertwiner
import InfoGeometry.Synthesis.QCDColorConfinementParafermionSynthesis
import InfoGeometry.Synthesis.HelicityNuclearKProjectionSynthesis
import InfoGeometry.Synthesis.FeshbachRPASchurRenormalizationFlow
import InfoGeometry.OperatorAlgebra.PeirceSpine.NuclearThoulessDensity
import InfoGeometry.Physics.NuclearKohnShamPeirceBridge
import InfoGeometry.Physics.NuclearInternalExternalParityFactorization
import InfoGeometry.Physics.NuclearChiralMengBridge
import InfoGeometry.Physics.MengChPSelectionRules
import InfoGeometry.Physics.QCDChiralStructuralBridge
import InfoGeometry.Physics.NuclearWignerSupermultipletSymmetry
import InfoGeometry.Physics.NuclearKleinParameterBundle
import InfoGeometry.Physics.NuclearKleinSpectralDescentBridge
import InfoGeometry.Physics.NuclearCartanProjectorParityBridge
import InfoGeometry.Physics.NuclearWignerDensityProjectorBridge
import InfoGeometry.Physics.NuclearCl55CartanParityDictionary
import InfoGeometry.Physics.NuclearFiveGradeParity

/-!
# Unified Synthesis: Nuclear Parity, Five-Graded Intertwiners, QCD Parafermions, and Renormalization

Top-level Milestone M5 synthesis module soldering:
1. **Seam A** (`NuclearFiveGradeSuperGrassmannianIntertwiner`): concrete two-mode CAR–BdG–Soloviev
   5-grading ↔ Super-Grassmannian `(2|1)` OSp / `(2|3)` `Z2Z2ColorGrade` / Günaydin–Gürsey
   intertwiner and `32×32` `MatStage 5` Soloviev no-go boundary.
2. **Seam B** (`QCDColorConfinementParafermionSynthesis`): Zorn baryon / `Cl(5,5)` color singlet /
   Wigner `SU(4)` / `charge6` morphisms ↔ Temperley–Lieb `B3`, Fibonacci parafermions,
   `op^3 = op` defects, and Artin 12-fold monodromy, with explicit conditional 4D confinement
   hypotheses.
3. **Seam C** (`HelicityNuclearKProjectionSynthesis`): massless `U(1)` little-group helicity,
   massive Pauli–Lubanski / `OperatorZornSpinCasimirLift`, and `SDiff` helicity ↔ nuclear
   `RotationalBandhead`, `NuclearTaxonomyPacket`, `KParitySector`, and GDR multipoles.
4. **Seam D** (`FeshbachRPASchurRenormalizationFlow`): dual `NuclearPhononRPAAlgebra`
   reconciliation, discrete Feshbach/Schur/Krein elimination, and `kreinHyperbolicFlow`
   invariance of noncommutative `[a, b]` RPA defects ↔ Iwasawa scale conjugation and
   dilaton–Andreev RG flow, with explicit conditional continuum RG and spectral-gap hypotheses.
5. **Unified Substrate & R2/R3 Integration**:
   - Peirce/Krein Thouless and Kohn–Sham four-sector particle-hole / Gamow–Teller substrate
     (`NuclearThoulessDensity`, `NuclearKohnShamPeirceBridge`),
   - Uncollapsed four-way `FourParityCarrier` (`piOp`, `fermionOp`, `wmOp`, `mengParityOp`),
     triaxial ChP selection rules (`NuclearChiralMengBridge`, `MengChPSelectionRules`),
     structural `ℤ₂` chiral bridge (`QCDChiralStructuralBridge`), and Klein spectral descent
     (`NuclearKleinParameterBundle`, `NuclearKleinSpectralDescentBridge`),
   - Wigner `SU(4)` supermultiplet (`NuclearWignerSupermultipletSymmetry`, namespace
     `InfoGeometry.Physics.NuclearWignerSupermultiplet`),
   - R3 clean complementary owners (`NuclearCartanProjectorParityBridge`,
     `NuclearWignerDensityProjectorBridge`, `NuclearCl55CartanParityDictionary`,
     `NuclearFiveGradeParity`), grounded in Lean owner source while noting Auto-Ontology `:3001`
     index lag on recent `FourParity` declarations and live Alexandria `:8538` retrieval.
-/

set_option autoImplicit false

noncomputable section

namespace InfoGeometry.Synthesis.NuclearUnifiedParityFiveGradeRenormalizationSynthesis

open InfoGeometry.Synthesis.NuclearFiveGradeSuperGrassmannianIntertwiner
open InfoGeometry.Synthesis.QCDColorConfinementParafermionSynthesis
open InfoGeometry.Synthesis.HelicityNuclearKProjectionSynthesis
open InfoGeometry.Synthesis.FeshbachRPASchurRenormalizationFlow
open InfoGeometry.OperatorAlgebra.PeirceSpine
open InfoGeometry.Physics.NuclearInternalExternalParityFactorization
open InfoGeometry.Physics.NuclearChiralMengBridge
open InfoGeometry.Physics.NuclearWignerSupermultiplet
open scoped ScopedOpZornModule

/-! ## 1. Closed Non-Commutativity Witnesses (T16) -/

/-- Closed non-commutativity witness on `Matrix (Fin 2) (Fin 2) ℝ`. -/
theorem block2_real_noncomm_witness :
    ∃ A B : Matrix (Fin 2) (Fin 2) ℝ, A * B ≠ B * A := by
  refine ⟨rpaWitnessA, rpaWitnessB, ?_⟩
  intro h
  have h01 := congrFun (congrFun h 0) 1
  simp [rpaWitnessA, rpaWitnessB, InfoGeometry.Physics.NuclearOperatorSuperSoloviev.blockHamiltonian,
    Matrix.mul_apply, Fin.sum_univ_two] at h01
  norm_num at h01

/-- Closed non-commutativity witness on `Matrix (Fin 4) (Fin 4) ℝ`. -/
theorem m4r_noncomm_witness :
    ∃ A B : Matrix (Fin 4) (Fin 4) ℝ, A * B ≠ B * A := by
  refine ⟨InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.pairCreation,
    InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.pairAnnihilation, ?_⟩
  intro h
  have h33 := congrFun (congrFun h 3) 3
  norm_num [InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.pairCreation,
    InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.pairAnnihilation,
    InfoGeometry.Canonical.SplitCliffordTwoModeCAR.a1,
    InfoGeometry.Canonical.SplitCliffordTwoModeCAR.a2,
    InfoGeometry.Canonical.SplitCliffordTwoModeCAR.a1Dag,
    InfoGeometry.Canonical.SplitCliffordTwoModeCAR.a2Dag,
    Matrix.mul_apply, Fin.sum_univ_four] at h33

/-- Closed non-commutativity witness on `Matrix (Fin 2) (Fin 2) ℂ` via isospin ladder `T₃, T₊`. -/
theorem m2c_isospin_noncomm_witness :
    isospin3 * isospinPlus ≠ isospinPlus * isospin3 := by
  intro heq
  have hcomm := isospin_comm_3_plus
  rw [heq, sub_self] at hcomm
  have h01 := congrFun (congrFun hcomm.symm 0) 1
  simp [isospinPlus, pauli1, pauli2] at h01

/-- Closed non-commutativity witness on `Module.End ℂ FourParityCarrier`. -/
theorem fourParityCarrier_k0_wm_noncomm_witness :
    k0Op * wmOp ≠ wmOp * k0Op := by
  intro heq
  exact four_parity_separation_and_compatibility.2.2.1.1 heq

/-- Closed non-commutativity witness on `Module.End ℂ ChiralParitySpace`. -/
theorem chiralParitySpace_chiture_e2_noncomm_witness :
    triaxialChitureOp * triaxialMultipoleOp .electricTwo ≠
      triaxialMultipoleOp .electricTwo * triaxialChitureOp := by
  intro heq
  exact triaxialChitureOp_e2_noncomm heq

/-! ## 2. Unified Unconditional `Type*` Synthesis Packet & T17 Witness -/

private theorem involution_mul_involutionProjector_comm
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (A B : Module.End ℂ V) (hAB : A * B = B * A) (b : Bool) :
    A * involutionProjector (K := ℂ) B b = involutionProjector (K := ℂ) B b * A := by
  unfold involutionProjector
  rw [mul_smul_comm, smul_mul_assoc, mul_add, add_mul, mul_one, one_mul,
    mul_smul_comm, smul_mul_assoc, hAB]

private theorem fourParityProjector_eig_all (b : Fin 4 → Bool) :
    piOp * fourParityProjector b = (if b 0 then (1 : ℂ) else -1) • fourParityProjector b ∧
    fermionOp * fourParityProjector b = (if b 1 then (1 : ℂ) else -1) • fourParityProjector b ∧
    wmOp * fourParityProjector b = (if b 2 then (1 : ℂ) else -1) • fourParityProjector b ∧
    mengParityOp * fourParityProjector b =
      (if b 3 then (1 : ℂ) else -1) • fourParityProjector b := by
  have hfp := four_parity_separation_and_compatibility
  have hpi := hfp.1.1
  have hfe := hfp.1.2.1
  have hwm := hfp.1.2.2.1
  have hme := hfp.1.2.2.2.2.2.1
  have c12 := hfp.2.1.1
  have c13 := hfp.2.1.2.1
  have c14 := hfp.2.1.2.2.1
  have c23 := hfp.2.1.2.2.2.1
  have c24 := hfp.2.1.2.2.2.2.1
  have c34 := hfp.2.1.2.2.2.2.2.1
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold fourParityProjector
    rw [← mul_assoc, ← mul_assoc, ← mul_assoc, mul_involutionProjector (K := ℂ) piOp hpi (b 0),
      smul_mul_assoc, smul_mul_assoc, smul_mul_assoc]
  · unfold fourParityProjector
    rw [← mul_assoc, ← mul_assoc, ← mul_assoc,
      involution_mul_involutionProjector_comm fermionOp piOp c12.symm (b 0),
      mul_assoc (involutionProjector (K := ℂ) piOp (b 0)),
      mul_involutionProjector (K := ℂ) fermionOp hfe (b 1),
      mul_smul_comm, smul_mul_assoc, smul_mul_assoc]
  · unfold fourParityProjector
    rw [← mul_assoc, ← mul_assoc, ← mul_assoc,
      involution_mul_involutionProjector_comm wmOp piOp c13.symm (b 0),
      mul_assoc (involutionProjector (K := ℂ) piOp (b 0)),
      involution_mul_involutionProjector_comm wmOp fermionOp c23.symm (b 1),
      ← mul_assoc (involutionProjector (K := ℂ) piOp (b 0)),
      mul_assoc (involutionProjector (K := ℂ) piOp (b 0) * involutionProjector (K := ℂ) fermionOp (b 1)),
      mul_involutionProjector (K := ℂ) wmOp hwm (b 2),
      mul_smul_comm, smul_mul_assoc]
  · unfold fourParityProjector
    rw [← mul_assoc, ← mul_assoc, ← mul_assoc,
      involution_mul_involutionProjector_comm mengParityOp piOp c14.symm (b 0),
      mul_assoc (involutionProjector (K := ℂ) piOp (b 0)),
      involution_mul_involutionProjector_comm mengParityOp fermionOp c24.symm (b 1),
      ← mul_assoc (involutionProjector (K := ℂ) piOp (b 0)),
      mul_assoc (involutionProjector (K := ℂ) piOp (b 0) * involutionProjector (K := ℂ) fermionOp (b 1)),
      involution_mul_involutionProjector_comm mengParityOp wmOp c34.symm (b 2),
      ← mul_assoc (involutionProjector (K := ℂ) piOp (b 0) * involutionProjector (K := ℂ) fermionOp (b 1)),
      mul_assoc (involutionProjector (K := ℂ) piOp (b 0) * involutionProjector (K := ℂ) fermionOp (b 1) *
        involutionProjector (K := ℂ) wmOp (b 2)),
      mul_involutionProjector (K := ℂ) mengParityOp hme (b 3),
      mul_smul_comm]

private theorem gamowTellerPlus_sq_zero (i : Fin 3) :
    gamowTellerPlus i * gamowTellerPlus i = 0 := by
  unfold gamowTellerPlus wignerY
  change (InfoGeometry.Physics.NuclearSpinIsospinTensorRepresentation.su4GamowTellerGen
      InfoGeometry.Physics.NuclearSpinIsospinTensorRepresentation.pauliTripleM2C i 0 +
      Complex.I • InfoGeometry.Physics.NuclearSpinIsospinTensorRepresentation.su4GamowTellerGen
        InfoGeometry.Physics.NuclearSpinIsospinTensorRepresentation.pauliTripleM2C i 1) *
    (InfoGeometry.Physics.NuclearSpinIsospinTensorRepresentation.su4GamowTellerGen
      InfoGeometry.Physics.NuclearSpinIsospinTensorRepresentation.pauliTripleM2C i 0 +
      Complex.I • InfoGeometry.Physics.NuclearSpinIsospinTensorRepresentation.su4GamowTellerGen
        InfoGeometry.Physics.NuclearSpinIsospinTensorRepresentation.pauliTripleM2C i 1) = 0
  have hsq0 := InfoGeometry.Physics.NuclearSpinIsospinTensorRepresentation.su4GamowTellerGen_sq
    InfoGeometry.Physics.NuclearSpinIsospinTensorRepresentation.pauliTripleM2C i 0
  have hsq1 := InfoGeometry.Physics.NuclearSpinIsospinTensorRepresentation.su4GamowTellerGen_sq
    InfoGeometry.Physics.NuclearSpinIsospinTensorRepresentation.pauliTripleM2C i 1
  have hanti :
      InfoGeometry.Physics.NuclearSpinIsospinTensorRepresentation.su4GamowTellerGen
          InfoGeometry.Physics.NuclearSpinIsospinTensorRepresentation.pauliTripleM2C i 0 *
        InfoGeometry.Physics.NuclearSpinIsospinTensorRepresentation.su4GamowTellerGen
          InfoGeometry.Physics.NuclearSpinIsospinTensorRepresentation.pauliTripleM2C i 1 +
      InfoGeometry.Physics.NuclearSpinIsospinTensorRepresentation.su4GamowTellerGen
          InfoGeometry.Physics.NuclearSpinIsospinTensorRepresentation.pauliTripleM2C i 1 *
        InfoGeometry.Physics.NuclearSpinIsospinTensorRepresentation.su4GamowTellerGen
          InfoGeometry.Physics.NuclearSpinIsospinTensorRepresentation.pauliTripleM2C i 0 = 0 := by
    unfold InfoGeometry.Physics.NuclearSpinIsospinTensorRepresentation.su4GamowTellerGen
    rw [smul_mul_smul, smul_mul_smul, ← smul_add,
      Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul,
      InfoGeometry.Physics.NuclearSpinIsospinTensorRepresentation.pauliTripleM2C.gen_sq i,
      ← TensorProduct.tmul_add,
      InfoGeometry.Physics.NuclearSpinIsospinTensorRepresentation.pauliTripleM2C.gen_anticomm
        0 1 (by decide),
      TensorProduct.tmul_zero, smul_zero]
  rw [add_mul, mul_add, mul_add, smul_mul_assoc, mul_smul_comm, smul_mul_smul,
    Complex.I_mul_I, hsq0, hsq1, neg_one_smul]
  have hre :
      ((1 / 4 : ℂ) • (1 : _root_.ChiralTensorRecoupling.SpinPair) +
        Complex.I • (InfoGeometry.Physics.NuclearSpinIsospinTensorRepresentation.su4GamowTellerGen
          InfoGeometry.Physics.NuclearSpinIsospinTensorRepresentation.pauliTripleM2C i 0 *
          InfoGeometry.Physics.NuclearSpinIsospinTensorRepresentation.su4GamowTellerGen
            InfoGeometry.Physics.NuclearSpinIsospinTensorRepresentation.pauliTripleM2C i 1)) +
      (Complex.I • (InfoGeometry.Physics.NuclearSpinIsospinTensorRepresentation.su4GamowTellerGen
          InfoGeometry.Physics.NuclearSpinIsospinTensorRepresentation.pauliTripleM2C i 1 *
          InfoGeometry.Physics.NuclearSpinIsospinTensorRepresentation.su4GamowTellerGen
            InfoGeometry.Physics.NuclearSpinIsospinTensorRepresentation.pauliTripleM2C i 0) +
        -((1 / 4 : ℂ) • (1 : _root_.ChiralTensorRecoupling.SpinPair))) =
      Complex.I • (InfoGeometry.Physics.NuclearSpinIsospinTensorRepresentation.su4GamowTellerGen
          InfoGeometry.Physics.NuclearSpinIsospinTensorRepresentation.pauliTripleM2C i 0 *
          InfoGeometry.Physics.NuclearSpinIsospinTensorRepresentation.su4GamowTellerGen
            InfoGeometry.Physics.NuclearSpinIsospinTensorRepresentation.pauliTripleM2C i 1 +
        InfoGeometry.Physics.NuclearSpinIsospinTensorRepresentation.su4GamowTellerGen
          InfoGeometry.Physics.NuclearSpinIsospinTensorRepresentation.pauliTripleM2C i 1 *
          InfoGeometry.Physics.NuclearSpinIsospinTensorRepresentation.su4GamowTellerGen
            InfoGeometry.Physics.NuclearSpinIsospinTensorRepresentation.pauliTripleM2C i 0) := by
    rw [smul_add]; abel
  rw [hre, hanti, smul_zero]

/-- Unconditional `Type*` synthesis packet bundling finite algebraic data from Seams A–D,
the uncollapsed `FourParityCarrier` projector family (idempotent, orthogonal, and eigen-linked to
`piOp`, `fermionOp`, `wmOp`, `mengParityOp`), triaxial ChP involutions, Wigner `SU(4)`
supermultiplet generators (`gamowTellerRaise` nilpotent with `+1` isospin weight), and discrete
RPA defect data with explicit non-collapse and non-degeneracy constraints across every seam. -/
structure UnifiedParityFiveGradeSynthesisPacket : Type _ where
  seamA : NuclearFiveGradeSuperGrassmannianIntertwinerData
  seamA_carToComplexOp_nonzero :
    seamA.carToComplexOp InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.gradingOperator ≠ 0
  seamA_carToFreudenthal_nonzero : seamA.carToFreudenthal gradingCartanSub ≠ 0
  seamA_freudenthalToM4R_left_inv :
    seamA.freudenthalToM4R (seamA.carToFreudenthal gradingCartanSub) = gradingCartanSub.1
  seamA_cuntzToM3_nonzero :
    seamA.cuntzToM3 InfoGeometry.Algebra.CuntzMatrixUnitFiveGradingBridge.gradingOpSub ≠ 0
  seamA_carToGunaydin_nonzero : seamA.carToGunaydinGursey gradingCartanSub ≠ 0
  seamA_carToOpZorn_nonzero : seamA.carToOpZorn gradingCartanSub ≠ 0
  seamA_carToOpZorn_pairCreation_ne_zero :
    seamA.carToOpZorn
      ⟨InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.pairCreation,
        InfoGeometry.Physics.NuclearFiveGradeGeneratorRepresentation.representM4R_mem_carLieSubalgebra .pairCreation⟩ ≠ 0
  seamA_carToGunaydin_pairCreation_ne_zero :
    seamA.carToGunaydinGursey
      ⟨InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.pairCreation,
        InfoGeometry.Physics.NuclearFiveGradeGeneratorRepresentation.representM4R_mem_carLieSubalgebra .pairCreation⟩ ≠ 0
  seamA_carToOpZorn_grade2 :
    InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.opEulerFiveGrading
      (seamA.carToOpZorn
        ⟨InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.pairCreation,
          InfoGeometry.Physics.NuclearFiveGradeGeneratorRepresentation.representM4R_mem_carLieSubalgebra .pairCreation⟩) =
      (2 : ℝ) • seamA.carToOpZorn
        ⟨InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.pairCreation,
          InfoGeometry.Physics.NuclearFiveGradeGeneratorRepresentation.representM4R_mem_carLieSubalgebra .pairCreation⟩
  seamB : ColorParafermionMorphismPacket 2
  seamC : HelicityToNuclearKPacket
  seamD_flow : ℝ → ℝ → InfoGeometry.Physics.NuclearOperatorSuperSoloviev.Block2 ℝ
  seamD_renorm :
    InfoGeometry.Integration.IwasawaTimeRenormalization.RenormalizationData
      InfoGeometry.Algebra.IwasawaRealKAN.Mat2
  seamD_flow_unitary : ∀ lam τ : ℝ,
    seamD_flow lam τ * seamD_flow lam (-τ) = 1 ∧
      seamD_flow lam (-τ) * seamD_flow lam τ = 1 ∧
      seamD_flow lam τ *
          (InfoGeometry.Physics.NuclearInternalExternalParityFactorization.externalFockParity :
            InfoGeometry.Physics.NuclearOperatorSuperSoloviev.Block2 ℝ) *
          seamD_flow lam τ =
        InfoGeometry.Physics.NuclearInternalExternalParityFactorization.externalFockParity
  seamD_flow_hadamard : ∀ lam τ : ℝ,
    InfoGeometry.Physics.NuclearOperatorSuperSoloviev.blockHamiltonian (1 : ℝ) (-1) 1 1 *
        seamD_flow lam τ *
        InfoGeometry.Physics.NuclearOperatorSuperSoloviev.blockHamiltonian (1 : ℝ) (-1) 1 1 =
      (2 : ℝ) • InfoGeometry.Algebra.IwasawaRealKAN.aDiag (lam * τ)
  seamD_renorm_noncomm :
    (seamD_renorm.scale : InfoGeometry.Algebra.IwasawaRealKAN.Mat2) * seamD_renorm.unipotent ≠
        seamD_renorm.unipotent * seamD_renorm.scale ∧
      InfoGeometry.Integration.IwasawaTimeRenormalization.normalizedStep seamD_renorm ≠
        seamD_renorm.unipotent
  rpaA : InfoGeometry.Physics.NuclearOperatorSuperSoloviev.Block2 ℝ
  rpaB : InfoGeometry.Physics.NuclearOperatorSuperSoloviev.Block2 ℝ
  rpaDefect_noncomm : rpaA * rpaB ≠ rpaB * rpaA
  chpAlgebra : ChPInvolutions (Module.End ℂ ChiralParitySpace)
  chpAlgebra_noncollapse :
    chpAlgebra.chirality ≠ chpAlgebra.parity ∧
      chpAlgebra.chirality ≠ 1 ∧ chpAlgebra.parity ≠ 1
  fourParityProj : (Fin 4 → Bool) → Module.End ℂ FourParityCarrier
  fourParityProj_ne_zero : ∀ b : Fin 4 → Bool, fourParityProj b ≠ 0
  fourParityProj_idem : ∀ b : Fin 4 → Bool, fourParityProj b * fourParityProj b = fourParityProj b
  fourParityProj_orth :
    ∀ b₁ b₂ : Fin 4 → Bool, b₁ ≠ b₂ → fourParityProj b₁ * fourParityProj b₂ = 0
  fourParityProj_eig : ∀ b : Fin 4 → Bool,
    piOp * fourParityProj b = (if b 0 then (1 : ℂ) else -1) • fourParityProj b ∧
    fermionOp * fourParityProj b = (if b 1 then (1 : ℂ) else -1) • fourParityProj b ∧
    wmOp * fourParityProj b = (if b 2 then (1 : ℂ) else -1) • fourParityProj b ∧
    mengParityOp * fourParityProj b = (if b 3 then (1 : ℂ) else -1) • fourParityProj b
  fourParityProj_sum : (∑ b : Fin 4 → Bool, fourParityProj b) = 1
  wignerCasimir : _root_.ChiralTensorRecoupling.SpinPair
  wignerCasimir_eq :
    wignerCasimir = (15 / 4 : ℂ) • (1 : _root_.ChiralTensorRecoupling.SpinPair)
  wignerCasimir_ne_zero : wignerCasimir ≠ 0
  gamowTellerRaise : _root_.ChiralTensorRecoupling.SpinPair
  gamowTellerRaise_ne_zero : gamowTellerRaise ≠ 0
  gamowTellerRaise_sq : gamowTellerRaise * gamowTellerRaise = 0
  gamowTellerRaise_isospin_weight :
    InfoGeometry.Physics.NuclearSpinIsospinTensorRepresentation.pairBracket
        (wignerT 2) gamowTellerRaise =
      gamowTellerRaise

/-- Zero-hypothesis constructive finite-model inhabitant (`T17`) for
`UnifiedParityFiveGradeSynthesisPacket`. -/
def canonicalUnifiedParityFiveGradeSynthesisPacket :
    UnifiedParityFiveGradeSynthesisPacket where
  seamA := canonicalNuclearFiveGradeSuperGrassmannianIntertwiner
  seamA_carToComplexOp_nonzero := by
    intro h0
    have hgr0 : InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.gradingOperator = 0 := by
      apply InfoGeometry.Physics.NuclearFiveGradeGeneratorRepresentation.m4rToOp_injective
      change canonicalNuclearFiveGradeSuperGrassmannianIntertwiner.carToComplexOp
          InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.gradingOperator =
        InfoGeometry.Physics.NuclearFiveGradeGeneratorRepresentation.m4rToOp 0
      rw [h0, map_zero]
    exact InfoGeometry.Physics.NuclearFiveGradeSameCarrierClosure.pair_rpa_square_defect_is_grade_zero_cartan.2 hgr0
  seamA_carToFreudenthal_nonzero := by
    intro h0
    have hinv := Phi_comp_carToFiveGraded gradingCartanSub
    change InfoGeometry.Nuclear.FiveGraded.Phi
        (canonicalNuclearFiveGradeSuperGrassmannianIntertwiner.carToFreudenthal gradingCartanSub) =
      gradingCartanSub.1 at hinv
    rw [h0, map_zero] at hinv
    exact InfoGeometry.Physics.NuclearFiveGradeSameCarrierClosure.pair_rpa_square_defect_is_grade_zero_cartan.2
      hinv.symm
  seamA_freudenthalToM4R_left_inv := Phi_comp_carToFiveGraded gradingCartanSub
  seamA_cuntzToM3_nonzero := by
    intro h0
    change cuntzMatUnitToM3 InfoGeometry.Algebra.CuntzMatrixUnitFiveGradingBridge.gradingOpSub = 0 at h0
    rw [cuntzMatUnitToM3_gradingOp] at h0
    have h00 := congrFun (congrFun h0 0) 0
    norm_num [InfoGeometry.SuperGrassmannian.SuperconformalOSpJordanPair.H_gen,
      InfoGeometry.SuperGrassmannian.SuperconformalOSpJordanPair.E] at h00
  seamA_carToGunaydin_nonzero := by
    intro h0
    have h1 := congrFun (congrArg (fun x => x.1) h0) 0
    dsimp [canonicalNuclearFiveGradeSuperGrassmannianIntertwiner, car5ToGunaydinGursey,
      gradingCartanSub] at h1
    simp [InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.gradingOperator_eq_diagonal] at h1
  seamA_carToOpZorn_nonzero := by
    intro h0
    have ha := congrArg (fun x :
        InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.OpZornMatrix ℝ => x.a) h0
    dsimp [canonicalNuclearFiveGradeSuperGrassmannianIntertwiner, car5ToOpZornEuler,
      gradingCartanSub] at ha
    simp [InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.gradingOperator_eq_diagonal] at ha
  seamA_carToOpZorn_pairCreation_ne_zero := by
    intro h0
    change car5ToOpZornEuler
        ⟨InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.pairCreation,
          InfoGeometry.Physics.NuclearFiveGradeGeneratorRepresentation.representM4R_mem_carLieSubalgebra .pairCreation⟩ =
      0 at h0
    have hgen := (car5ToOpZornEuler_generators_and_kkt gradingCartanSub).2.2.2.2.2.2.2.1
    rw [hgen] at h0
    have hw := congrArg
      (fun x : InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.OpZornMatrix ℝ => x.w.x) h0
    norm_num [InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.opGradePlus2] at hw
  seamA_carToGunaydin_pairCreation_ne_zero := by
    intro h0
    change car5ToGunaydinGursey
        ⟨InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.pairCreation,
          InfoGeometry.Physics.NuclearFiveGradeGeneratorRepresentation.representM4R_mem_carLieSubalgebra .pairCreation⟩ =
      0 at h0
    rw [← car5ToGunaydinGursey_eq_opZornEquiv,
      (car5ToOpZornEuler_generators_and_kkt gradingCartanSub).2.2.2.2.2.2.2.1] at h0
    have hw := congrFun (congrArg (fun x => x.2.2) h0) 0
    norm_num [InfoGeometry.Synthesis.SuperGrassmannianFiveGradedColorSupersymmetrySynthesis.opZornGunaydinGurseyEquiv,
      InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.opGradePlus2,
      InfoGeometry.Synthesis.SuperGrassmannianFiveGradedColorSupersymmetrySynthesis.opVec3Fin3Equiv] at hw
  seamA_carToOpZorn_grade2 :=
    car5ToOpZornEuler_preserves_grade
      InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.pairCreation_grade
  seamB := canonicalColorParafermionMorphismPacket
  seamC := defaultHelicityToNuclearKPacket
  seamD_flow := kreinHyperbolicFlow
  seamD_renorm := noncommKanRenormalizationData 1 1
  seamD_flow_unitary := kreinHyperbolicFlow_krein_unitary
  seamD_flow_hadamard := hadamard_kreinHyperbolicFlow_eq_two_aDiag
  seamD_renorm_noncomm := noncommKanRenormalizationData_noncomm_of_ne_zero one_ne_zero one_ne_zero
  rpaA := rpaWitnessA
  rpaB := rpaWitnessB
  rpaDefect_noncomm := block2_real_noncomm_and_rpa_defect_witness.1
  chpAlgebra := triaxialChPInvolutions
  chpAlgebra_noncollapse := by
    refine ⟨?_, ?_, ?_⟩
    · intro h
      have hv := LinearMap.congr_fun h (Pi.single (0, 0) (1 : ℂ))
      have h10 := congrFun hv (1, 0)
      change triaxialChitureOp (Pi.single (0, 0) (1 : ℂ)) (1, 0) =
        triaxialParityOp (Pi.single (0, 0) (1 : ℂ)) (1, 0) at h10
      simp [triaxialChitureOp_apply, triaxialParityOp_apply] at h10
    · intro h
      have hv := LinearMap.congr_fun h (Pi.single (0, 0) (1 : ℂ))
      have h10 := congrFun hv (1, 0)
      change triaxialChitureOp (Pi.single (0, 0) (1 : ℂ)) (1, 0) =
        (Pi.single (0, 0) (1 : ℂ) : ChiralParitySpace) (1, 0) at h10
      simp [triaxialChitureOp_apply] at h10
    · intro h
      have hv := LinearMap.congr_fun h (Pi.single (0, 1) (1 : ℂ))
      have h01 := congrFun hv (0, 1)
      change triaxialParityOp (Pi.single (0, 1) (1 : ℂ)) (0, 1) =
        (Pi.single (0, 1) (1 : ℂ) : ChiralParitySpace) (0, 1) at h01
      simp [triaxialParityOp_apply] at h01
      norm_num at h01
  fourParityProj := fourParityProjector
  fourParityProj_ne_zero := fourParityProjector_ne_zero
  fourParityProj_idem := fourParityProjector_idem
  fourParityProj_orth := fourParityProjector_mul_ne
  fourParityProj_eig := fourParityProjector_eig_all
  fourParityProj_sum := fourParityProjector_sum_eq_one
  wignerCasimir := wignerSU4Casimir
  wignerCasimir_eq := wigner_su4_casimir
  wignerCasimir_ne_zero := by
    intro h0
    have htr := congrArg InfoGeometry.Physics.NuclearSpinIsospinTensorRepresentation.pairTrace h0
    rw [wigner_su4_casimir, map_smul, map_zero, smul_eq_mul] at htr
    change (15 / 4 : ℂ) * InfoGeometry.Physics.NuclearSpinIsospinTensorRepresentation.pairTrace
        ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₜ[ℂ] (1 : Matrix (Fin 2) (Fin 2) ℂ)) = 0 at htr
    rw [InfoGeometry.Physics.NuclearSpinIsospinTensorRepresentation.pairTrace_tmul] at htr
    norm_num [Matrix.trace] at htr
  gamowTellerRaise := gamowTellerPlus 0
  gamowTellerRaise_ne_zero := by
    intro h0
    have hbr := congrArg (fun x : _root_.ChiralTensorRecoupling.SpinPair =>
      InfoGeometry.Physics.NuclearSpinIsospinTensorRepresentation.pairBracket x (wignerY 0 1)) h0
    have hL : InfoGeometry.Physics.NuclearSpinIsospinTensorRepresentation.pairBracket
        (gamowTellerPlus 0) (wignerY 0 1) =
        Complex.I • wignerT 2 := by
      unfold gamowTellerPlus
      have h01 : InfoGeometry.Physics.NuclearSpinIsospinTensorRepresentation.pairBracket
          (wignerY 0 0) (wignerY 0 1) = Complex.I • wignerT 2 := by
        change InfoGeometry.Physics.NuclearSpinIsospinTensorRepresentation.tensorBracket
            (InfoGeometry.Physics.NuclearSpinIsospinTensorRepresentation.su4GamowTellerGen
              InfoGeometry.Physics.NuclearSpinIsospinTensorRepresentation.pauliTripleM2C 0 0)
            (InfoGeometry.Physics.NuclearSpinIsospinTensorRepresentation.su4GamowTellerGen
              InfoGeometry.Physics.NuclearSpinIsospinTensorRepresentation.pauliTripleM2C 0 1) =
          InfoGeometry.Physics.NuclearSpinIsospinTensorRepresentation.pauliTripleM2C.iUnit •
            InfoGeometry.Physics.NuclearSpinIsospinTensorRepresentation.su4IsospinGen
              InfoGeometry.Physics.NuclearSpinIsospinTensorRepresentation.pauliTripleM2C 2
        exact gamowTeller_obstruction_generates_isospin
          InfoGeometry.Physics.NuclearSpinIsospinTensorRepresentation.pauliTripleM2C 0
      simp only [InfoGeometry.Physics.NuclearSpinIsospinTensorRepresentation.pairBracket,
        InfoGeometry.Physics.NuclearSpinIsospinTensorRepresentation.tensorBracket] at h01 ⊢
      rw [add_mul, mul_add, smul_mul_assoc, mul_smul_comm]
      have hre : (wignerY 0 0 * wignerY 0 1 + Complex.I • (wignerY 0 1 * wignerY 0 1)) -
          (wignerY 0 1 * wignerY 0 0 + Complex.I • (wignerY 0 1 * wignerY 0 1)) =
          wignerY 0 0 * wignerY 0 1 - wignerY 0 1 * wignerY 0 0 := by abel
      rw [hre, h01]
    have hzero : Complex.I • wignerT 2 = 0 := by
      rw [← hL, hbr]
      simp [InfoGeometry.Physics.NuclearSpinIsospinTensorRepresentation.pairBracket,
        InfoGeometry.Physics.NuclearSpinIsospinTensorRepresentation.tensorBracket]
    have htr := congrArg (fun x =>
      InfoGeometry.Physics.NuclearSpinIsospinTensorRepresentation.pairTrace (wignerT 2 * x)) hzero
    rw [mul_zero, map_zero, mul_smul_comm, map_smul, smul_eq_mul] at htr
    have hsq : InfoGeometry.Physics.NuclearSpinIsospinTensorRepresentation.pairTrace
        (wignerT 2 * wignerT 2) = (1 / 4 : ℂ) := by
      unfold wignerT InfoGeometry.Physics.NuclearSpinIsospinTensorRepresentation.isospinGenVec
      rw [InfoGeometry.Physics.NuclearSpinIsospinTensorRepresentation.su4IsospinGen_sq,
        Algebra.TensorProduct.one_def, map_smul,
        InfoGeometry.Physics.NuclearSpinIsospinTensorRepresentation.pairTrace_tmul]
      simp [Matrix.trace]
      norm_num
    rw [hsq] at htr
    exact Complex.I_ne_zero ((mul_eq_zero.mp htr).resolve_right (by norm_num))
  gamowTellerRaise_sq := gamowTellerPlus_sq_zero 0
  gamowTellerRaise_isospin_weight := isospin3_comm_gamowTellerPlus 0

/-! ## 3. Peirce/Krein Thouless, Kohn–Sham Four-Sector, and Wigner SU(4) Soldering -/

/-- Unconditional synthesis of the Peirce/Krein Thouless particle-hole algebra
(`NuclearThoulessDensity`), Kohn–Sham four-sector proton/neutron particle/hole & Gamow–Teller
operator resolution (`NuclearKohnShamPeirceBridge`), Wigner `SU(4)` supermultiplet algebra
(`NuclearWignerSupermultipletSymmetry`), rank-one density projector intertwining
(`NuclearWignerDensityProjectorBridge`), and Cartan `±2` alignment
(`NuclearCartanProjectorParityBridge`). -/
theorem unconditional_peirce_thouless_kohn_sham_wigner_synthesis
    {B : Type*} [Ring B] {P Pocc Pp Pn A C W M : B}
    (hP : P * P = P) (hOcc : Pocc * Pocc = Pocc)
    (hpp : Pp * Pp = Pp) (hnn : Pn * Pn = Pn)
    (hpn : Pp * Pn = 0) (hnp : Pn * Pp = 0)
    (hppOcc : Pp * Pocc = Pocc * Pp) (hnnOcc : Pn * Pocc = Pocc * Pn)
    {K Alg : Type*} [Field K] [CharZero K] [Ring Alg] [Algebra K Alg]
    (pt : InfoGeometry.Physics.NuclearSpinIsospinTensorRepresentation.PauliTriple K Alg)
    (i : Fin 3) (j : Fin 3) (a15 : Fin 15) :
    (thoulessIdempotent P A C * thoulessIdempotent P A C = thoulessIdempotent P A C ∧
      evenGrade P (thoulessIdempotent P A C) = thoulessOccupation P A C ∧
      comm (ksbGenerator P A C) (ksbStationaryDensity P A C) = 0 ∧
      comm (InfoGeometry.OperatorAlgebra.PeirceSpine.isospinCharge Pp Pn)
        (isospinRaise Pp Pn W) = (2 : ℤ) • isospinRaise Pp Pn W ∧
      comm (InfoGeometry.OperatorAlgebra.PeirceSpine.isospinCharge Pp Pn)
        (isospinLower Pp Pn M) = -((2 : ℤ) • isospinLower Pp Pn M)) ∧
    (InfoGeometry.Physics.NuclearKohnShamPeirceBridge.thoulessDensity P A C *
        InfoGeometry.Physics.NuclearKohnShamPeirceBridge.thoulessDensity P A C =
        InfoGeometry.Physics.NuclearKohnShamPeirceBridge.thoulessDensity P A C ∧
      comm (InfoGeometry.Physics.NuclearKohnShamPeirceBridge.bogoliubovOperator P A C)
        (InfoGeometry.Physics.NuclearKohnShamPeirceBridge.selfConsistentDensity P A C) = 0 ∧
      InfoGeometry.Physics.NuclearKohnShamPeirceBridge.gamowTeller Pocc Pp Pn W *
        InfoGeometry.Physics.NuclearKohnShamPeirceBridge.gamowTeller Pocc Pp Pn W = 0 ∧
      comm Pocc (InfoGeometry.Physics.NuclearKohnShamPeirceBridge.gamowTeller Pocc Pp Pn W) =
        -InfoGeometry.Physics.NuclearKohnShamPeirceBridge.gamowTeller Pocc Pp Pn W) ∧
    (wignerSU4Casimir = (15 / 4 : ℂ) • (1 : _root_.ChiralTensorRecoupling.SpinPair) ∧
      InfoGeometry.Physics.NuclearSpinIsospinTensorRepresentation.tensorBracket
        (InfoGeometry.Physics.NuclearSpinIsospinTensorRepresentation.su4GamowTellerGen pt i 0)
        (InfoGeometry.Physics.NuclearSpinIsospinTensorRepresentation.su4GamowTellerGen pt i 1) =
        pt.iUnit • InfoGeometry.Physics.NuclearSpinIsospinTensorRepresentation.su4IsospinGen pt 2 ∧
      InfoGeometry.Physics.NuclearSpinIsospinTensorRepresentation.tensorBracket
        (InfoGeometry.Physics.NuclearSpinIsospinTensorRepresentation.su4GamowTellerGen pt 0 j)
        (InfoGeometry.Physics.NuclearSpinIsospinTensorRepresentation.su4GamowTellerGen pt 1 j) =
        pt.iUnit • InfoGeometry.Physics.NuclearSpinIsospinTensorRepresentation.su4SpinGen pt 2 ∧
      InfoGeometry.Physics.NuclearSpinIsospinTensorRepresentation.pairBracket
        (wignerT 2) (gamowTellerPlus i) = gamowTellerPlus i ∧
      InfoGeometry.Physics.NuclearSpinIsospinTensorRepresentation.twoNucleonSU4CasimirOf pt *
        InfoGeometry.Physics.NuclearSpinIsospinTensorRepresentation.wignerPairing6AOf pt =
        (5 : K) • InfoGeometry.Physics.NuclearSpinIsospinTensorRepresentation.wignerPairing6AOf pt ∧
      InfoGeometry.Physics.NuclearSpinIsospinTensorRepresentation.twoNucleonSU4CasimirOf pt *
        InfoGeometry.Physics.NuclearSpinIsospinTensorRepresentation.wignerPairing10SOf pt =
        (9 : K) • InfoGeometry.Physics.NuclearSpinIsospinTensorRepresentation.wignerPairing10SOf pt ∧
      InfoGeometry.Physics.NuclearSpinIsospinTensorRepresentation.twoNucleonSU4Casimir *
        InfoGeometry.Physics.NuclearSpinIsospinTensorRepresentation.wignerPairing6A =
        (5 : ℂ) • InfoGeometry.Physics.NuclearSpinIsospinTensorRepresentation.wignerPairing6A ∧
      InfoGeometry.Physics.NuclearSpinIsospinTensorRepresentation.totalTwoNucleonGen a15 *
        InfoGeometry.Physics.NuclearSpinIsospinTensorRepresentation.wignerPairing6A =
        InfoGeometry.Physics.NuclearSpinIsospinTensorRepresentation.wignerPairing6A *
          InfoGeometry.Physics.NuclearSpinIsospinTensorRepresentation.totalTwoNucleonGen a15) ∧
    (InfoGeometry.Physics.HestenesSpinDensityXpQuantization.densityMatrix isospinPlus =
        InfoGeometry.Physics.NuclearCartanProjectorParityBridge.isospinPositiveProjector ∧
      InfoGeometry.Physics.HestenesSpinDensityXpQuantization.rightDensityMatrix isospinPlus =
        InfoGeometry.Physics.NuclearCartanProjectorParityBridge.isospinNegativeProjector ∧
      InfoGeometry.Physics.NuclearCartanProjectorParityBridge.isospinPositiveProjector *
        InfoGeometry.Physics.NuclearCartanProjectorParityBridge.isospinNegativeProjector = 0 ∧
      isospin3 * isospinPlus - isospinPlus * isospin3 = isospinPlus) := by
  have hks := InfoGeometry.Physics.NuclearKohnShamPeirceBridge.stageDF43_operator_synthesis
    hP hOcc hpp hnn hpn hnp hppOcc hnnOcc (A := A) (C := C) (W := W) (M := M)
  have hwp := general_wigner_pairing_splitting pt
  have hw6 := wignerPairing6A_casimir_and_invariance a15
  have hdens := InfoGeometry.Physics.NuclearWignerDensityProjectorBridge.wigner_density_projector_packet
  refine ⟨⟨thoulessIdempotent_idempotent hP A C, evenGrade_thoulessIdempotent hP A C,
      ksbGenerator_comm_stationaryDensity hP A C,
      isospinCharge_comm_raise hpp hnn hnp,
      isospinCharge_comm_lower hpp hnn hpn⟩,
    ⟨hks.1, hks.2.2.2.2.1, hks.2.2.2.2.2.2.2.2.2.1, hks.2.2.2.2.2.2.2.2.2.2.2⟩,
    ⟨wigner_su4_casimir,
      gamowTeller_obstruction_generates_isospin pt i,
      gamowTeller_obstruction_generates_spin pt j,
      isospin3_comm_gamowTellerPlus i,
      hwp.1, hwp.2, hw6.1, hw6.2⟩,
    ⟨hdens.1, hdens.2.1, hdens.2.2.2.1, isospin_comm_3_plus⟩⟩

/-! ## 4. Uncollapsed Four-Way Parities, Chiral Meng, Klein Descent & Structural QCD ℤ₂ -/

/-- Unconditional R2 boundary theorem keeping all four commuting `FourParityCarrier` involutions
(`piOp`, `fermionOp`, `wmOp`, `mengParityOp`) strictly uncollapsed and pairwise distinct, linking
`HelicityToNuclearKPacket.toTaxonomyPacket.fourParityProj` (Seam C), `triaxialChPInvolutions` &
`MengChPSelectionRules.Multipole` (`E2`/`M1`/`E3`), `NuclearFiveGradeParity`,
`QCDChiralStructuralBridge`, `NuclearCl55CartanParityDictionary`, and
`NuclearKleinSpectralDescentBridge`. -/
theorem uncollapsed_four_parity_chp_klein_qcd_synthesis
    {ι : Type*} [DecidableEq ι]
    {A : Type*} [Ring A] [Algebra ℝ A]
    (car : InfoGeometry.Physics.NuclearQuasiparticleCAR.QuasiparticleCAR ι A) (i : ι)
    (a5 : Fin 5)
    (P : InfoGeometry.Physics.NuclearOperatorSuperSoloviev.InternalParity A) (E0 E1 V W : A)
    (hE0 : P.IsEven E0) (hE1 : P.IsEven E1) (hV : P.IsOdd V) (hW : P.IsOdd W)
    {n : ℕ} (K : Matrix (Fin n) (Fin n) ℝ)
    {T : A} (hT : T * T * T = T)
    (H5 : InfoGeometry.Physics.NuclearSuperSolovievPeirceBridge.PeirceCompatibleBlock T)
    (Hklein : InfoGeometry.Physics.NuclearKleinParameterBundle.KleinEquivariantHamiltonian P)
    (Rklein : InfoGeometry.Physics.NuclearOperatorSchurComplement.ResolventData A)
    (cell : InfoGeometry.Physics.NuclearKleinParameterBundle.ParameterCell)
    (pkt : HelicityToNuclearKPacket) (m : InfoGeometry.Physics.MengChPSelectionRules.Multipole) :
    (piOp * piOp = 1 ∧ fermionOp * fermionOp = 1 ∧ wmOp * wmOp = 1 ∧
      mengParityOp * mengParityOp = 1 ∧ chitureOp * chitureOp = 1 ∧ chiplexOp * chiplexOp = 1 ∧
      piOp * fermionOp = fermionOp * piOp ∧ piOp * wmOp = wmOp * piOp ∧
      piOp * mengParityOp = mengParityOp * piOp ∧ fermionOp * wmOp = wmOp * fermionOp ∧
      fermionOp * mengParityOp = mengParityOp * fermionOp ∧
      wmOp * mengParityOp = mengParityOp * wmOp ∧
      k0Op * wmOp ≠ wmOp * k0Op ∧
      piOp ≠ fermionOp ∧ piOp ≠ wmOp ∧ piOp ≠ mengParityOp ∧
      fermionOp ≠ wmOp ∧ fermionOp ≠ mengParityOp ∧ wmOp ≠ mengParityOp ∧
      (∀ b : Fin 4 → Bool, fourParityProjector b ≠ 0)) ∧
    (piOp * pkt.toTaxonomyPacket.fourParityProj =
        (pkt.toTaxonomyPacket.spatialParitySign : ℂ) • pkt.toTaxonomyPacket.fourParityProj ∧
      fermionOp * pkt.toTaxonomyPacket.fourParityProj =
        (pkt.toTaxonomyPacket.base.quasiparticleParity : ℂ) • pkt.toTaxonomyPacket.fourParityProj ∧
      wmOp * pkt.toTaxonomyPacket.fourParityProj =
        (pkt.toTaxonomyPacket.wmSector.sign : ℂ) • pkt.toTaxonomyPacket.fourParityProj ∧
      mengParityOp * pkt.toTaxonomyPacket.fourParityProj =
        (pkt.toTaxonomyPacket.chitureSector.sign : ℂ) • pkt.toTaxonomyPacket.fourParityProj ∧
      pkt.toTaxonomyPacket.fourParityProj ≠ 0) ∧
    (triaxialChPInvolutions.chiplex * triaxialChPInvolutions.chiplex = 1 ∧
      triaxialChitureOp = chpChitureOp ∧
      triaxialIntrinsicParityOp = chpIntrinsicParityOp ∧
      chiralBandBra 1 1 (triaxialMultipoleOp m (chiralBandKet 0 0)) = 0 ∧
      chiralBandBra 1 0 (triaxialMultipoleOp .electricTwo (chiralBandKet 0 0)) ≠ 0) ∧
    (internalParity P *
        InfoGeometry.Physics.NuclearOperatorSuperSoloviev.blockHamiltonian E0 E1 V W *
        internalParity P =
        InfoGeometry.Physics.NuclearOperatorSuperSoloviev.reflectOffDiagonal E0 E1 V W ∧
      InfoGeometry.MassSpectrometry.gradingMatrix n *
        InfoGeometry.MassSpectrometry.doubledOperator K *
        InfoGeometry.MassSpectrometry.gradingMatrix n =
        -InfoGeometry.MassSpectrometry.doubledOperator K ∧
      InfoGeometry.Physics.NuclearOperatorSuperSoloviev.totalParity
        (InfoGeometry.Physics.NuclearFiveGradeParity.zeroModeInternalParity T H5.tripotent) *
        H5.toHamiltonian *
        InfoGeometry.Physics.NuclearOperatorSuperSoloviev.totalParity
          (InfoGeometry.Physics.NuclearFiveGradeParity.zeroModeInternalParity T H5.tripotent) =
        H5.toHamiltonian ∧
      InfoGeometry.Physics.NuclearOperatorSuperSoloviev.totalParity
          (InfoGeometry.Physics.NuclearFiveGradeParity.zeroModeInternalParity T hT) *
        InfoGeometry.Physics.NuclearOperatorSuperSoloviev.blockHamiltonian
          (InfoGeometry.Physics.Algebra.fiveGradeProjector T .zero E0)
          (InfoGeometry.Physics.Algebra.fiveGradeProjector T .zero E1)
          (InfoGeometry.Physics.Algebra.fiveGradeProjector T .posOne V)
          (InfoGeometry.Physics.Algebra.fiveGradeProjector T .negOne W) *
        InfoGeometry.Physics.NuclearOperatorSuperSoloviev.totalParity
          (InfoGeometry.Physics.NuclearFiveGradeParity.zeroModeInternalParity T hT) =
        InfoGeometry.Physics.NuclearOperatorSuperSoloviev.blockHamiltonian
          (InfoGeometry.Physics.Algebra.fiveGradeProjector T .zero E0)
          (InfoGeometry.Physics.Algebra.fiveGradeProjector T .zero E1)
          (InfoGeometry.Physics.Algebra.fiveGradeProjector T .posOne V)
          (InfoGeometry.Physics.Algebra.fiveGradeProjector T .negOne W) ∧
      (InfoGeometry.Physics.NuclearFiveGradeParity.zeroModeInternalParity T hT).gamma *
        (InfoGeometry.Physics.NuclearFiveGradeParity.zeroModeInternalParity T hT).gamma = 1 ∧
      InfoGeometry.Physics.NuclearQuasiparticleCAR.QuasiparticleCAR.fermionParity car i *
        InfoGeometry.Physics.NuclearQuasiparticleCAR.QuasiparticleCAR.fermionParity car i = 1 ∧
      InfoGeometry.Physics.Cl55SpinorCartanFock.gammaChiral *
        InfoGeometry.Physics.Cl55SpinorCartanFock.gammaChiral = 1 ∧
      InfoGeometry.Canonical.Cl55WittLieRouting.bracket
          (InfoGeometry.Physics.NuclearCl55CartanParityDictionary.normalizedCl55Cartan a5)
          (InfoGeometry.Physics.Cl55SpinorCartanFock.e a5) =
        (2 : ℝ) • InfoGeometry.Physics.Cl55SpinorCartanFock.e a5) ∧
    ((({} : InfoGeometry.Physics.NuclearKleinSpectralDescentBridge.CommonKleinObservables
          Hklein Rklein).nuclearEffective
        (InfoGeometry.Canonical.D6HexTiledKleinBottleQuotient.quotientMap cell) =
        Hklein.effectiveAt Rklein cell) ∧
      Hklein.effectiveAt Rklein (InfoGeometry.Canonical.D6HexTiledKleinBottleQuotient.glide cell) =
        Hklein.effectiveAt Rklein cell ∧
      InfoGeometry.Canonical.D6KleinDiracBands.quotientBandGap
        (InfoGeometry.Canonical.D6HexTiledKleinBottleQuotient.quotientMap cell) =
        InfoGeometry.Canonical.D6KleinDiracBands.bandGap cell) := by
  have hfp := four_parity_separation_and_compatibility
  have htax := InfoGeometry.Physics.NuclearQuantumNumberPacket.NuclearTaxonomyPacket.isospin_and_fourParity_compatibility
    pkt.toTaxonomyPacket
  have hchp := triaxial_opposite_chiplex_allowed_nonzero
  have hqcd := InfoGeometry.Physics.QCDChiralStructuralBridge.nuclear_massspec_chiral_packet
    P E0 E1 V W hE0 hE1 hV hW K
  have h5p := InfoGeometry.Physics.NuclearFiveGradeParity.PeirceCompatibleBlock.totalParity_invariant H5
  have h5proj := InfoGeometry.Physics.NuclearFiveGradeParity.totalParity_invariant_projected_block
    hT E0 E1 V W
  have hcl := InfoGeometry.Physics.NuclearCl55CartanParityDictionary.nuclear_cl55_parity_shape_packet car i
  have hcl_cart := InfoGeometry.Physics.NuclearCl55CartanParityDictionary.normalizedCl55Cartan_creation a5
  have hkl := InfoGeometry.Physics.NuclearKleinSpectralDescentBridge.common_klein_quotient_packet
    Hklein Rklein cell
  refine ⟨⟨hfp.1.1, hfp.1.2.1, hfp.1.2.2.1, hfp.1.2.2.2.2.2.1, hfp.1.2.2.2.2.1, hfp.1.2.2.2.2.2.2,
      hfp.2.1.1, hfp.2.1.2.1, hfp.2.1.2.2.1, hfp.2.1.2.2.2.1, hfp.2.1.2.2.2.2.1, hfp.2.1.2.2.2.2.2.1,
      hfp.2.2.1.1, hfp.2.2.1.2.1, hfp.2.2.1.2.2.1, hfp.2.2.1.2.2.2.1,
      hfp.2.2.1.2.2.2.2.2.2.1, hfp.2.2.1.2.2.2.2.2.2.2.1,
      hfp.2.2.1.2.2.2.2.2.2.2.2.2.2.1, hfp.2.2.2⟩,
    ⟨htax.2.1.1, htax.2.1.2.1, htax.2.1.2.2.1, htax.2.1.2.2.2, htax.2.2.1.2⟩,
    ⟨triaxialChPInvolutions.chiplex_sq, triaxialChitureOp_eq_chpChitureOp,
      triaxialIntrinsicParityOp_eq_chpIntrinsicParityOp, triaxial_same_chiplex_vanishes m, hchp.1⟩,
    ⟨hqcd.1, hqcd.2, h5p, h5proj,
      (InfoGeometry.Physics.NuclearFiveGradeParity.zeroModeInternalParity T hT).gamma_sq,
      hcl.1, hcl.2, hcl_cart⟩,
    ⟨hkl.1, hkl.2.1, hkl.2.2.1⟩⟩

/-! ## 5. Unconditional Noncommutative RPA Defect & Finite Seams A–D Soldering -/

/-- Unconditional finite-algebraic synthesis across Seams A–D:
- **Seam A**: `car5ToOpZornEuler` grade preservation, `seamA_rpa_commutator_defect_preserved`,
  and `seamA_soloviev_matStage5_nogo`.
- **Seam B**: `seamB_finite_architecture_compatibility` on `ColorParafermionMorphismPacket n`.
- **Seam C**: `unsigned_bandhead_vs_signed_KParitySector_separation`.
- **Seam D**: `dual_phonon_rpa_reconciliation`, `feshbach_schur_kernel_eigen_bridge`,
  `three_config_krein_and_callan_harvey_bridge`, `nested_krein_feshbach_bogoliubov_rg_bridge`,
  `kreinHyperbolicFlow_preserves_car_grade_zero_defect`, `noncommKanRenormalizationData_normalizedStep`,
  and `iwasawa_commutation_vs_rpa_defect_separation`. -/
theorem unified_rpa_defect_and_finite_seam_synthesis
    {k : ℤ} {Xcar : InfoGeometry.Physics.NuclearFiveGradeGeneratorRepresentation.carLieSubalgebra}
    (hX : InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.HasGrade k Xcar.1)
    {ιq ιph A : Type*} [DecidableEq ιq] [DecidableEq ιph] [Ring A] [Algebra ℝ A]
    {grade : ℤ → Submodule ℝ A}
    {M : InfoGeometry.Physics.NuclearGradedBathCommutant.ThermalQuasiparticleModel grade}
    {sys : InfoGeometry.Physics.NuclearPhononRPA.CoupledQuasiparticlePhononSystem ιq ιph A}
    (Eqp ω V : ℂ) (α β lam τ ξ : ℝ)
    {n : ℕ} [DecidableEq (Fin n)] (P : ColorParafermionMorphismPacket n)
    {R : Type*} [Ring R] (Vop Wop Binv : R)
    (aF bF : ℝ) (vF : _root_.FibonacciParafermion.RealDiracSpinor)
    (Xz Yz : InfoGeometry.Canonical.GaugedZornDiracKahler.ZornMatrix ℝ)
    (u vVec w : InfoGeometry.Canonical.GaugedZornDiracKahler.Vec3 ℝ)
    (ψ : InfoGeometry.Physics.ThreeStrandJonesRecoupling.FusionState)
    (r : InfoGeometry.Algebra.Zorn.G2CyclotomicWeyl.Root)
    (a b : A) (hab : a * b ≠ b * a)
    {Riw : Type*} [Ring Riw]
    (Ops : InfoGeometry.Integration.IwasawaTimeRenormalization.RenormalizationData Riw)
    (hIwasawa : (Ops.scale : Riw) * Ops.unipotent = Ops.unipotent * (Ops.scale : Riw))
    {Vkr : Type*} [NormedAddCommGroup Vkr] [InnerProductSpace ℝ Vkr] [CompleteSpace Vkr]
    [InfoGeometry.Krein.KreinSpace Vkr]
    (Pkr Hkr Kres : Vkr →L[ℝ] Vkr) (hPkr : Pkr * Pkr = Pkr) (hPHkr : Pkr * Hkr = Hkr * Pkr)
    (hQRkr : (1 - Pkr) * Kres = Kres)
    (R2 : InfoGeometry.Nuclear.NuclearPhononRPAAlgebra.QuasibosonRPADatum)
    {nR : ℕ} (hnR : 0 < nR)
    (Rn : InfoGeometry.Nuclear.NuclearPhononRPAAlgebra.QuasibosonRPADatumN ℝ nR)
    {Kf Vf : Type*} [Field Kf] [AddCommGroup Vf] [Module Kf Vf]
    (Pf Hf Rf : Module.End Kf Vf) (Ef : Kf)
    (hPf : Pf * Pf = Pf) (hQRf : (1 - Pf) * Rf = Rf) (hRQf : Rf * (1 - Pf) = Rf)
    (hDRf : InfoGeometry.Physics.NuclearFeshbachReduction.denominator Pf Hf Ef * Rf = 1 - Pf)
    (hRDf : Rf * InfoGeometry.Physics.NuclearFeshbachReduction.denominator Pf Hf Ef = 1 - Pf)
    (vf : Vf) (hvf : Pf vf = vf) (ψf : Vf) (hψf : Hf ψf = Ef • ψf)
    (Af Bf Cf Kresf : Vf →ₗ[Kf] Vf)
    (a3 c3 g3 E3 ell3 : ℝ) (hE3 : E3 ≠ c3) (h_ell3 : 0 < ell3)
    (x3 : InfoGeometry.Physics.NuclearThreeConfigurationKreinReduction.DoubledModelSpace)
    {H_space : Type*} [NormedAddCommGroup H_space] [InnerProductSpace ℝ H_space]
    (CH : InfoGeometry.Physics.DilatonWeylAnomalyInflow.CallanHarveyInflow H_space)
    (A_ch : H_space →ₗ[ℝ] H_space)
    (h_adj_ch : InfoGeometry.Physics.LorentzBoostKreinConfinement.IsKreinSelfAdjoint CH.K A_ch)
    (v_ch : H_space) (lam1 lam2 : ℝ) (h_diff : lam1 ≠ lam2)
    (h_e1 : A_ch v_ch = lam1 • v_ch) (h_e2 : CH.K.J (A_ch v_ch) = lam2 • CH.K.J v_ch)
    {E_bog : Type} [NormedAddCommGroup E_bog] [InnerProductSpace ℝ E_bog] [CompleteSpace E_bog]
    (B_bog : InfoGeometry.Canonical.BogoliubovRGFlowBridge.Bridge E_bog)
    (hEq_bog : B_bog.metriplecticFlow.IsDissipativeEquilibrium)
    (P₀_bog P₁_bog R₁_bog R₀₁_bog :
      InfoGeometry.Krein.DoubledSpace E_bog →L[ℝ] InfoGeometry.Krein.DoubledSpace E_bog)
    (E0_bog : ℝ) (hP0_bog : P₀_bog * P₀_bog = P₀_bog) (hP1_bog : P₁_bog * P₁_bog = P₁_bog)
    (hP0_sa : InfoGeometry.Krein.KreinSpace.kreinAdjoint P₀_bog = P₀_bog)
    (hP1_sa : InfoGeometry.Krein.KreinSpace.kreinAdjoint P₁_bog = P₁_bog)
    (hK_sa : InfoGeometry.Krein.KreinSpace.kreinAdjoint B_bog.reduction.Kambient = B_bog.reduction.Kambient)
    (h_nest : P₀_bog * P₁_bog = P₀_bog)
    (hSub : P₁_bog * B_bog.reduction.Preg = P₁_bog)
    (hSubR : B_bog.reduction.Preg * P₁_bog = P₁_bog)
    (hQR1 : (1 - P₁_bog) * R₁_bog = R₁_bog)
    (hDR1 : InfoGeometry.Physics.NuclearRealKreinFeshbach.denominator P₁_bog B_bog.reduction.Kambient E0_bog *
      R₁_bog = 1 - P₁_bog)
    (hSR01 : InfoGeometry.Physics.NuclearRealKreinFeshbach.intermediateShell P₀_bog P₁_bog * R₀₁_bog = R₀₁_bog)
    (hDR01 : InfoGeometry.Physics.NuclearRealKreinFeshbach.intermediateDenominator P₀_bog P₁_bog
      (InfoGeometry.Physics.NuclearRealKreinFeshbach.effectiveHamiltonian P₁_bog B_bog.reduction.Kambient R₁_bog)
      E0_bog * R₀₁_bog = InfoGeometry.Physics.NuclearRealKreinFeshbach.intermediateShell P₀_bog P₁_bog)
    {ξ_bog Δ_bog : ℝ} (hgap_bog : 0 < InfoGeometry.Physics.NuclearBdGTwoLevelExact.bdgEnergy ξ_bog Δ_bog) :
    (InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.opEulerFiveGrading
        (car5ToOpZornEuler Xcar) = (k : ℝ) • car5ToOpZornEuler Xcar ∧
      IsEmpty
        (InfoGeometry.Physics.NuclearSolovievFiveGradedCommutantBridge.SolovievFiveGradedRealization
          grade M sys) ∧
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
      (α * β) • InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.gradingOperator =
        (InfoGeometry.Physics.NuclearOperatorSuperSoloviev.blockHamiltonian
          (α • InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.pairCreation)
          (-(α • InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.pairCreation))
          (β • InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.pairAnnihilation)
          (-(β • InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.pairAnnihilation)) *
        InfoGeometry.Physics.NuclearOperatorSuperSoloviev.blockHamiltonian
          (α • InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.pairCreation)
          (-(α • InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.pairCreation))
          (β • InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.pairAnnihilation)
          (-(β • InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.pairAnnihilation))) 0 1) ∧
    (P.colorDefect.op ^ 3 = P.colorDefect.op ∧
      P.zornEquiv (InfoGeometry.Canonical.GaugedZornDiracKahler.ZornMatrix.zornMul Xz Yz) =
        P.zornEquiv Xz * P.zornEquiv Yz ∧
      P.zornToCl55Singlet (InfoGeometry.Canonical.ZornColorConfinementBaryon.baryonState
        InfoGeometry.Canonical.ZornColorConfinementBaryon.colorE0
        InfoGeometry.Canonical.ZornColorConfinementBaryon.colorE1
        InfoGeometry.Canonical.ZornColorConfinementBaryon.colorE2) ≠ 0 ∧
      InfoGeometry.Physics.Cl55WignerSU4Embedding.colorSU3Casimir * P.zornToCl55Singlet Xz = 0 ∧
      (P.artinLift.Bs * P.artinLift.Bl) ^ 12 = 1 ∧
      (∀ k12 : ℕ, 0 < k12 → k12 < 12 → (P.artinLift.Bs * P.artinLift.Bl) ^ k12 ≠ 1)) ∧
    ((MasslessHelicityBranch.plusOne.toBandhead.twoK =
        MasslessHelicityBranch.minusOne.toBandhead.twoK) ∧
      (MasslessHelicityBranch.plusOne.toKParitySector.twoK ≠
        MasslessHelicityBranch.minusOne.toKParitySector.twoK) ∧
      ((⟨1, InfoGeometry.Physics.NuclearSymmetrySectors.SpatialParity.positive⟩ :
          InfoGeometry.Physics.NuclearSpinIsospinTensorRepresentation.KParitySector) ≠
        ⟨1, InfoGeometry.Physics.NuclearSymmetrySectors.SpatialParity.negative⟩)) ∧
    ((let aM : InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.M4R :=
          InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.pairCreation
      let bM : InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.M4R :=
          InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.pairAnnihilation
      let cM : InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.M4R :=
          algebraMap ℝ InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.M4R (Real.cosh (lam * τ))
      let sM : InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.M4R :=
          algebraMap ℝ InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.M4R (Real.sinh (lam * τ))
      let aM' := (cM * cM + sM * sM) * aM - (2 : ℕ) • (cM * sM * bM)
      let bM' := (cM * cM + sM * sM) * bM - (2 : ℕ) • (cM * sM * aM)
      aM' * bM' - bM' * aM' =
        InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.gradingOperator ∧ bM' ≠ 0) ∧
      (InfoGeometry.Physics.NuclearOperatorSuperSoloviev.blockHamiltonian (1 : ℝ) (-1) 1 1 *
          kreinHyperbolicFlow lam τ *
          InfoGeometry.Physics.NuclearOperatorSuperSoloviev.blockHamiltonian (1 : ℝ) (-1) 1 1 =
        (2 : ℝ) • InfoGeometry.Algebra.IwasawaRealKAN.aDiag (lam * τ)) ∧
      (InfoGeometry.Integration.IwasawaTimeRenormalization.normalizedStep
          (noncommKanRenormalizationData lam ξ) =
        InfoGeometry.Algebra.IwasawaRealKAN.nShear (Real.exp (2 * lam) * ξ)) ∧
      (InfoGeometry.Integration.IwasawaTimeRenormalization.normalizedStep Ops = Ops.unipotent ∧
        InfoGeometry.Canonical.BogoliubovRGFlowBridge.schurCorrection Pkr Hkr Kres = 0 ∧
        (InfoGeometry.Physics.NuclearOperatorSuperSoloviev.blockHamiltonian a (-a) b (-b) *
          InfoGeometry.Physics.NuclearOperatorSuperSoloviev.blockHamiltonian a (-a) b (-b)) 0 1 ≠ 0) ∧
      (R2.defect ≠ 0 ∧ Rn.defect ≠ 0 ∧
        IsEmpty (InfoGeometry.Physics.NuclearPhononRPA.PhononRPA (Fin 2)
          (Matrix (Fin nR) (Fin nR) ℝ)) ∧
        (¬ ∃ Q Qdag : Matrix (Fin nR) (Fin nR) ℝ,
          InfoGeometry.Nuclear.NuclearPhononRPAAlgebra.commutatorN Q Qdag = 1)) ∧
      ((Hf (InfoGeometry.Physics.NuclearFeshbachReduction.waveOperator Pf Hf Rf vf) =
          Ef • InfoGeometry.Physics.NuclearFeshbachReduction.waveOperator Pf Hf Rf vf ↔
          InfoGeometry.Physics.NuclearFeshbachReduction.effectiveHamiltonian Pf Hf Rf vf = Ef • vf) ∧
        InfoGeometry.Physics.NuclearFeshbachReduction.waveOperator Pf Hf Rf (Pf ψf) = ψf ∧
        Af - Bf.comp (Kresf.comp Cf) =
          InfoGeometry.Physics.NuclearOperatorSchurComplement.effectiveOperator Af Bf Cf Kresf) ∧
      (InfoGeometry.Krein.KreinSpace.IsKreinSelfAdjoint
          (InfoGeometry.Physics.NuclearRealKreinFeshbach.effectiveHamiltonian
            InfoGeometry.Physics.NuclearThreeConfigurationDual.doubledProjection
            (InfoGeometry.Physics.NuclearThreeConfigurationDual.doubledHamiltonian a3 c3 g3)
            (InfoGeometry.Physics.NuclearThreeConfigurationKreinReduction.doubledResolvent c3 E3)) ∧
        (InfoGeometry.Physics.NuclearThreeConfigurationDual.doubledHamiltonian a3 c3 g3
            (InfoGeometry.Physics.NuclearThreeConfigurationKreinReduction.doubledGraphMap c3 g3 E3 x3) =
            E3 • InfoGeometry.Physics.NuclearThreeConfigurationKreinReduction.doubledGraphMap c3 g3 E3 x3 ↔
          InfoGeometry.Physics.NuclearThreeConfigurationKreinReduction.doubledReducedHamiltonian a3 c3 g3 E3 x3 =
            E3 • x3) ∧
        CH.bulkInflowCurrent = CH.seamAnomalyCurrent ∧
        InfoGeometry.Physics.DilatonWeylAnomalyInflow.seamNoetherCharge CH v_ch = 0 ∧
        0 < InfoGeometry.Physics.DilatonWeylAnomalyInflow.selbergHyperbolicWeight ell3) ∧
      (B_bog.metriplecticFlow.totalFlow =
          InfoGeometry.Canonical.BogoliubovOptimalTransport.canonicalBogoliubovFlow B_bog.reduction B_bog.time ∧
        (let K_01 := InfoGeometry.Physics.NuclearRealKreinFeshbach.effectiveHamiltonian P₀_bog
            (InfoGeometry.Physics.NuclearRealKreinFeshbach.effectiveHamiltonian P₁_bog
              B_bog.reduction.Kambient R₁_bog) R₀₁_bog;
          InfoGeometry.Physics.NuclearRealKreinFeshbach.effectiveHamiltonian P₀_bog B_bog.reduction.Kambient
              (InfoGeometry.Physics.NuclearRealKreinFeshbach.nestedResolvent
                B_bog.reduction.Kambient R₁_bog R₀₁_bog) = K_01 ∧
            InfoGeometry.Krein.KreinSpace.IsKreinSelfAdjoint K_01 ∧
            InfoGeometry.Canonical.BogoliubovOptimalTransport.IsOptimalBogoliubovFlow B_bog.reduction
              (fun t => NormedSpace.exp (t • K_01))) ∧
        (-InfoGeometry.Physics.NuclearBdGTwoLevelExact.bdgBlock ξ_bog Δ_bog) *
            InfoGeometry.Canonical.BogoliubovRGFlowBridge.bdgExplicitResolvent ξ_bog Δ_bog 0 = 1)) := by
  have hA_nogo := seamA_soloviev_matStage5_nogo (grade := grade) (M := M) (sys := sys) Eqp ω V
  have hA_rpa := seamA_rpa_commutator_defect_preserved α β
  have hB := seamB_finite_architecture_compatibility P Vop Wop Binv aF bF vF Xz Yz u vVec w ψ r
  have hC := unsigned_bandhead_vs_signed_KParitySector_separation
  have hD_car := kreinHyperbolicFlow_preserves_car_grade_zero_defect lam τ
  have hD_sep := iwasawa_commutation_vs_rpa_defect_separation Ops hIwasawa Pkr Hkr Kres hPkr hPHkr hQRkr a b hab lam τ
  have hD_dual := dual_phonon_rpa_reconciliation R2 hnR Rn
  have hD_fesh := feshbach_schur_kernel_eigen_bridge Pf Hf Rf Ef hPf hQRf hRQf hDRf hRDf vf hvf ψf hψf Af Bf Cf Kresf
  have hD_3cfg := three_config_krein_and_callan_harvey_bridge a3 c3 g3 E3 ell3 hE3 h_ell3 x3 CH A_ch h_adj_ch v_ch lam1 lam2 h_diff h_e1 h_e2
  have hD_nest := nested_krein_feshbach_bogoliubov_rg_bridge B_bog hEq_bog P₀_bog P₁_bog R₁_bog R₀₁_bog E0_bog hP0_bog hP1_bog hP0_sa hP1_sa hK_sa h_nest hSub hSubR hQR1 hDR1 hSR01 hDR01 hgap_bog
  refine ⟨⟨car5ToOpZornEuler_preserves_grade hX, hA_nogo.1, hA_rpa.1, hA_rpa.2.2.1.symm⟩,
    ⟨hB.1.1, hB.2.2.2.1.2.1, hB.2.2.2.1.2.2.2.1, hB.2.2.2.1.2.2.2.2,
      hB.2.2.2.2.2.2.2.2.2.1, hB.2.2.2.2.2.2.2.2.2.2.1⟩,
    ⟨hC.1, hC.2.1, hC.2.2.2.2⟩,
    ⟨⟨hD_car.1, hD_car.2.2⟩,
      hadamard_kreinHyperbolicFlow_eq_two_aDiag lam τ,
      noncommKanRenormalizationData_normalizedStep lam ξ,
      ⟨hD_sep.1, hD_sep.2.1.1, hD_sep.2.2.1⟩,
      ⟨hD_dual.2.1, hD_dual.2.2.2.1, hD_dual.2.2.2.2.1, hD_dual.2.2.1⟩,
      hD_fesh,
      ⟨hD_3cfg.2.1, hD_3cfg.2.2.1, hD_3cfg.2.2.2.1, hD_3cfg.2.2.2.2.1, hD_3cfg.2.2.2.2.2⟩,
      ⟨hD_nest.1,
        ⟨hD_nest.2.1.1, hD_nest.2.1.2.2.1, hD_nest.2.1.2.2.2.2.2.2.1⟩,
        hD_nest.2.2.1⟩⟩⟩

/-- Universally quantified synthesis theorem exercising every field of any
`UnifiedParityFiveGradeSynthesisPacket` across Seams A–D, the idempotent/orthogonal/eigen-linked
`fourParityProj` family, all 6 derived pairwise `FourParityCarrier` inequalities, ChP
non-collapse, and nilpotent/weight-raised Wigner `SU(4)` Gamow–Teller data. -/
theorem unified_synthesis_packet_universal_laws
    (P : UnifiedParityFiveGradeSynthesisPacket) (lam τ : ℝ) (b : Fin 4 → Bool) :
    (P.seamA.carToComplexOp InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.gradingOperator ≠ 0 ∧
      P.seamA.carToFreudenthal gradingCartanSub ≠ 0 ∧
      P.seamA.freudenthalToM4R (P.seamA.carToFreudenthal gradingCartanSub) = gradingCartanSub.1 ∧
      P.seamA.cuntzToM3 InfoGeometry.Algebra.CuntzMatrixUnitFiveGradingBridge.gradingOpSub ≠ 0 ∧
      P.seamA.carToGunaydinGursey gradingCartanSub ≠ 0 ∧
      P.seamA.carToOpZorn gradingCartanSub ≠ 0 ∧
      P.seamA.carToOpZorn
        ⟨InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.pairCreation,
          InfoGeometry.Physics.NuclearFiveGradeGeneratorRepresentation.representM4R_mem_carLieSubalgebra .pairCreation⟩ ≠ 0 ∧
      P.seamA.carToGunaydinGursey
        ⟨InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.pairCreation,
          InfoGeometry.Physics.NuclearFiveGradeGeneratorRepresentation.representM4R_mem_carLieSubalgebra .pairCreation⟩ ≠ 0 ∧
      InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.opEulerFiveGrading
        (P.seamA.carToOpZorn
          ⟨InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.pairCreation,
            InfoGeometry.Physics.NuclearFiveGradeGeneratorRepresentation.representM4R_mem_carLieSubalgebra .pairCreation⟩) =
        (2 : ℝ) • P.seamA.carToOpZorn
          ⟨InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.pairCreation,
            InfoGeometry.Physics.NuclearFiveGradeGeneratorRepresentation.representM4R_mem_carLieSubalgebra .pairCreation⟩) ∧
    ((P.seamB.artinLift.Bs * P.seamB.artinLift.Bl) ^ 12 = 1 ∧
      P.seamC.bandhead.twoK = P.seamC.sdiffQuantized.twoK ∧
      P.seamC.toTaxonomyPacket.fourParityProj ≠ 0 ∧
      piOp * P.seamC.toTaxonomyPacket.fourParityProj =
        (P.seamC.toTaxonomyPacket.spatialParitySign : ℂ) •
          P.seamC.toTaxonomyPacket.fourParityProj) ∧
    (P.seamD_flow lam τ * P.seamD_flow lam (-τ) = 1 ∧
      InfoGeometry.Physics.NuclearOperatorSuperSoloviev.blockHamiltonian (1 : ℝ) (-1) 1 1 *
          P.seamD_flow lam τ *
          InfoGeometry.Physics.NuclearOperatorSuperSoloviev.blockHamiltonian (1 : ℝ) (-1) 1 1 =
        (2 : ℝ) • InfoGeometry.Algebra.IwasawaRealKAN.aDiag (lam * τ) ∧
      (P.seamD_renorm.scale : InfoGeometry.Algebra.IwasawaRealKAN.Mat2) * P.seamD_renorm.unipotent ≠
        P.seamD_renorm.unipotent * P.seamD_renorm.scale ∧
      InfoGeometry.Integration.IwasawaTimeRenormalization.normalizedStep P.seamD_renorm ≠
        P.seamD_renorm.unipotent ∧
      (let aM : InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.M4R :=
          InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.pairCreation
       let bM : InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.M4R :=
          InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.pairAnnihilation
       let cM : InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.M4R :=
          algebraMap ℝ InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.M4R (Real.cosh (lam * τ))
       let sM : InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.M4R :=
          algebraMap ℝ InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.M4R (Real.sinh (lam * τ))
       let aM' := (cM * cM + sM * sM) * aM - (2 : ℕ) • (cM * sM * bM)
       let bM' := (cM * cM + sM * sM) * bM - (2 : ℕ) • (cM * sM * aM)
       aM' * bM' - bM' * aM' =
         InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.gradingOperator ∧ bM' ≠ 0)) ∧
    (P.rpaA * P.rpaB ≠ P.rpaB * P.rpaA ∧
      P.chpAlgebra.chiplex * P.chpAlgebra.chiplex = 1 ∧
      P.chpAlgebra.chirality ≠ P.chpAlgebra.parity ∧
      P.chpAlgebra.chirality ≠ 1 ∧
      P.chpAlgebra.parity ≠ 1) ∧
    (P.fourParityProj b ≠ 0 ∧
      P.fourParityProj b * P.fourParityProj b = P.fourParityProj b ∧
      (∀ b' : Fin 4 → Bool, b ≠ b' → P.fourParityProj b * P.fourParityProj b' = 0) ∧
      (piOp * P.fourParityProj b = (if b 0 then (1 : ℂ) else -1) • P.fourParityProj b ∧
        fermionOp * P.fourParityProj b = (if b 1 then (1 : ℂ) else -1) • P.fourParityProj b ∧
        wmOp * P.fourParityProj b = (if b 2 then (1 : ℂ) else -1) • P.fourParityProj b ∧
        mengParityOp * P.fourParityProj b = (if b 3 then (1 : ℂ) else -1) • P.fourParityProj b) ∧
      (∑ b' : Fin 4 → Bool, P.fourParityProj b') = 1 ∧
      piOp ≠ fermionOp ∧ piOp ≠ wmOp ∧ piOp ≠ mengParityOp ∧
      fermionOp ≠ wmOp ∧ fermionOp ≠ mengParityOp ∧ wmOp ≠ mengParityOp) ∧
    (P.wignerCasimir = (15 / 4 : ℂ) • (1 : _root_.ChiralTensorRecoupling.SpinPair) ∧
      P.wignerCasimir ≠ 0 ∧
      P.gamowTellerRaise ≠ 0 ∧
      P.gamowTellerRaise * P.gamowTellerRaise = 0 ∧
      InfoGeometry.Physics.NuclearSpinIsospinTensorRepresentation.pairBracket
          (wignerT 2) P.gamowTellerRaise =
        P.gamowTellerRaise) := by
  have hC_tax :=
    InfoGeometry.Physics.NuclearQuantumNumberPacket.NuclearTaxonomyPacket.isospin_and_fourParity_compatibility
      P.seamC.toTaxonomyPacket
  have hflow := P.seamD_flow_unitary lam τ
  have hhad := P.seamD_flow_hadamard lam τ
  have hrpa := kreinHyperbolicFlow_preserves_car_grade_zero_defect lam τ
  have hneg_ne : ∀ b₀ : Fin 4 → Bool,
      (-1 : ℂ) • P.fourParityProj b₀ ≠ P.fourParityProj b₀ := by
    intro b₀ heq
    apply P.fourParityProj_ne_zero b₀
    have h2 : (2 : ℂ) • P.fourParityProj b₀ = 0 := by
      rw [two_smul]
      calc P.fourParityProj b₀ + P.fourParityProj b₀
          = (-1 : ℂ) • P.fourParityProj b₀ + P.fourParityProj b₀ := by rw [heq]
        _ = ((-1 : ℂ) + 1) • P.fourParityProj b₀ := by rw [add_smul, one_smul]
        _ = 0 := by norm_num
    have hs := congrArg (fun x => (1 / 2 : ℂ) • x) h2
    rw [smul_smul, show (1 / 2 : ℂ) * 2 = 1 by norm_num, one_smul, smul_zero] at hs
    exact hs
  have hpi_ne_ferm : piOp ≠ fermionOp := by
    intro h
    have he := P.fourParityProj_eig ![true, false, true, true]
    have hv := congrArg (fun op => op * P.fourParityProj ![true, false, true, true]) h
    rw [he.1, he.2.1] at hv
    simp at hv
    exact hneg_ne ![true, false, true, true] hv.symm
  have hpi_ne_wm : piOp ≠ wmOp := by
    intro h
    have he := P.fourParityProj_eig ![true, true, false, true]
    have hv := congrArg (fun op => op * P.fourParityProj ![true, true, false, true]) h
    rw [he.1, he.2.2.1] at hv
    simp at hv
    exact hneg_ne ![true, true, false, true] hv.symm
  have hpi_ne_meng : piOp ≠ mengParityOp := by
    intro h
    have he := P.fourParityProj_eig ![true, true, true, false]
    have hv := congrArg (fun op => op * P.fourParityProj ![true, true, true, false]) h
    rw [he.1, he.2.2.2] at hv
    simp at hv
    exact hneg_ne ![true, true, true, false] hv.symm
  have hferm_ne_wm : fermionOp ≠ wmOp := by
    intro h
    have he := P.fourParityProj_eig ![true, true, false, true]
    have hv := congrArg (fun op => op * P.fourParityProj ![true, true, false, true]) h
    rw [he.2.1, he.2.2.1] at hv
    simp at hv
    exact hneg_ne ![true, true, false, true] hv.symm
  have hferm_ne_meng : fermionOp ≠ mengParityOp := by
    intro h
    have he := P.fourParityProj_eig ![true, true, true, false]
    have hv := congrArg (fun op => op * P.fourParityProj ![true, true, true, false]) h
    rw [he.2.1, he.2.2.2] at hv
    simp at hv
    exact hneg_ne ![true, true, true, false] hv.symm
  have hwm_ne_meng : wmOp ≠ mengParityOp := by
    intro h
    have he := P.fourParityProj_eig ![true, true, true, false]
    have hv := congrArg (fun op => op * P.fourParityProj ![true, true, true, false]) h
    rw [he.2.2.1, he.2.2.2] at hv
    simp at hv
    exact hneg_ne ![true, true, true, false] hv.symm
  refine ⟨⟨P.seamA_carToComplexOp_nonzero, P.seamA_carToFreudenthal_nonzero,
      P.seamA_freudenthalToM4R_left_inv, P.seamA_cuntzToM3_nonzero,
      P.seamA_carToGunaydin_nonzero, P.seamA_carToOpZorn_nonzero,
      P.seamA_carToOpZorn_pairCreation_ne_zero, P.seamA_carToGunaydin_pairCreation_ne_zero,
      P.seamA_carToOpZorn_grade2⟩,
    ⟨P.seamB.artinLift.spin_coxeter_pow_twelve,
      P.seamC.bandhead_twoK_eq, hC_tax.2.2.1.2, hC_tax.2.1.1⟩,
    ⟨hflow.1, hhad, P.seamD_renorm_noncomm.1, P.seamD_renorm_noncomm.2, ⟨hrpa.1, hrpa.2.2⟩⟩,
    ⟨P.rpaDefect_noncomm, P.chpAlgebra.chiplex_sq,
      P.chpAlgebra_noncollapse.1, P.chpAlgebra_noncollapse.2.1, P.chpAlgebra_noncollapse.2.2⟩,
    ⟨P.fourParityProj_ne_zero b, P.fourParityProj_idem b, fun b' hne => P.fourParityProj_orth b b' hne,
      P.fourParityProj_eig b, P.fourParityProj_sum,
      hpi_ne_ferm, hpi_ne_wm, hpi_ne_meng, hferm_ne_wm, hferm_ne_meng, hwm_ne_meng⟩,
    ⟨P.wignerCasimir_eq, P.wignerCasimir_ne_zero, P.gamowTellerRaise_ne_zero,
      P.gamowTellerRaise_sq, P.gamowTellerRaise_isospin_weight⟩⟩

/-- Non-vacuous unconditional canonical witness theorem instantiating
`unified_synthesis_packet_universal_laws` on `canonicalUnifiedParityFiveGradeSynthesisPacket`
with explicit Seam C (`twoK = 1`), Seam D (`aDiag`), idempotent/nilpotent readouts, and
`[k0Op, wmOp] ≠ 0`. -/
theorem canonical_unified_synthesis_packet_witness (lam τ : ℝ) (b : Fin 4 → Bool) :
    let P := canonicalUnifiedParityFiveGradeSynthesisPacket
    P.rpaA * P.rpaB ≠ P.rpaB * P.rpaA ∧
      piOp ≠ fermionOp ∧ piOp ≠ wmOp ∧ piOp ≠ mengParityOp ∧
      fermionOp ≠ wmOp ∧ fermionOp ≠ mengParityOp ∧ wmOp ≠ mengParityOp ∧
      k0Op * wmOp ≠ wmOp * k0Op ∧
      P.fourParityProj b ≠ 0 ∧
      P.fourParityProj b * P.fourParityProj b = P.fourParityProj b ∧
      P.chpAlgebra.chiplex * P.chpAlgebra.chiplex = 1 ∧
      P.chpAlgebra.chirality ≠ P.chpAlgebra.parity ∧
      P.wignerCasimir = (15 / 4 : ℂ) • (1 : _root_.ChiralTensorRecoupling.SpinPair) ∧
      P.gamowTellerRaise ≠ 0 ∧
      P.gamowTellerRaise * P.gamowTellerRaise = 0 ∧
      InfoGeometry.Physics.NuclearSpinIsospinTensorRepresentation.pairBracket
          (wignerT 2) P.gamowTellerRaise =
        P.gamowTellerRaise ∧
      (P.seamB.artinLift.Bs * P.seamB.artinLift.Bl) ^ 12 = 1 ∧
      P.seamC.toSignedKParitySector.twoK = 1 ∧
      InfoGeometry.Physics.NuclearOperatorSuperSoloviev.blockHamiltonian (1 : ℝ) (-1) 1 1 *
          P.seamD_flow lam τ *
          InfoGeometry.Physics.NuclearOperatorSuperSoloviev.blockHamiltonian (1 : ℝ) (-1) 1 1 =
        (2 : ℝ) • InfoGeometry.Algebra.IwasawaRealKAN.aDiag (lam * τ) := by
  intro P
  have huniv := unified_synthesis_packet_universal_laws P lam τ b
  have hk0 := fourParityCarrier_k0_wm_noncomm_witness
  refine ⟨huniv.2.2.2.1.1,
    huniv.2.2.2.2.1.2.2.2.2.2.1, huniv.2.2.2.2.1.2.2.2.2.2.2.1,
    huniv.2.2.2.2.1.2.2.2.2.2.2.2.1, huniv.2.2.2.2.1.2.2.2.2.2.2.2.2.1,
    huniv.2.2.2.2.1.2.2.2.2.2.2.2.2.2.1, huniv.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2,
    hk0,
    huniv.2.2.2.2.1.1,
    huniv.2.2.2.2.1.2.1,
    huniv.2.2.2.1.2.1,
    huniv.2.2.2.1.2.2.1,
    huniv.2.2.2.2.2.1,
    huniv.2.2.2.2.2.2.2.1,
    huniv.2.2.2.2.2.2.2.2.1,
    huniv.2.2.2.2.2.2.2.2.2,
    huniv.2.1.1,
    rfl,
    huniv.2.2.1.2.1⟩

/-! ## 6. Explicit Conditional Continuum Extension Bundle (R2 Separation) -/

/-- Orthogonal projection `(x, y) ↦ (x, 0)` on `DoubledSpace ℝ` used in the nontrivial
canonical spectral-gap termination witness. -/
private def doubledProjPlus :
    InfoGeometry.Krein.DoubledSpace ℝ →L[ℝ] InfoGeometry.Krein.DoubledSpace ℝ :=
  LinearMap.mkContinuous
    { toFun := fun u => WithLp.toLp 2 ((WithLp.ofLp u).1, (0 : ℝ))
      map_add' := fun u v => by
        rcases u with ⟨x1, y1⟩
        rcases v with ⟨x2, y2⟩
        apply (WithLp.ofLp_injective (p := (2 : ENNReal)))
        ext <;> simp
      map_smul' := fun r u => by
        rcases u with ⟨x, y⟩
        apply (WithLp.ofLp_injective (p := (2 : ENNReal)))
        ext <;> simp }
    1
    (fun u => by
      rcases u with ⟨x, y⟩
      change ‖WithLp.toLp 2 (x, (0 : ℝ))‖ ≤ 1 * ‖WithLp.toLp 2 (x, y)‖
      rw [one_mul]
      have hsq : ‖WithLp.toLp 2 (x, (0 : ℝ))‖ ^ 2 ≤ ‖WithLp.toLp 2 (x, y)‖ ^ 2 := by
        rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq,
          WithLp.prod_inner_apply, WithLp.prod_inner_apply]
        simp only [real_inner_self_eq_norm_sq, norm_zero, ne_eq, OfNat.ofNat_ne_zero,
          not_false_eq_true, zero_pow, add_zero]
        exact le_add_of_nonneg_right (sq_nonneg ‖y‖)
      nlinarith [norm_nonneg (WithLp.toLp 2 (x, (0 : ℝ))),
        norm_nonneg (WithLp.toLp 2 (x, y))])

/-- Off-diagonal Krein-self-adjoint coupling `(x, y) ↦ (y, -x)` on `DoubledSpace ℝ`
(with `J(x, y) = (x, -y)`), failing to commute with `doubledProjPlus` and generating a
nontrivial Schur complement correction `effectiveHamiltonian P₀ H R = -P₀ ≠ P₀ * H * P₀`. -/
private def doubledKreinCouplingOp :
    InfoGeometry.Krein.DoubledSpace ℝ →L[ℝ] InfoGeometry.Krein.DoubledSpace ℝ :=
  LinearMap.mkContinuous
    { toFun := fun u => WithLp.toLp 2 ((WithLp.ofLp u).2, -(WithLp.ofLp u).1)
      map_add' := fun u v => by
        rcases u with ⟨x1, y1⟩
        rcases v with ⟨x2, y2⟩
        apply (WithLp.ofLp_injective (p := (2 : ENNReal)))
        ext <;> simp [add_comm]
      map_smul' := fun r u => by
        rcases u with ⟨x, y⟩
        apply (WithLp.ofLp_injective (p := (2 : ENNReal)))
        ext <;> simp }
    1
    (fun u => by
      rcases u with ⟨x, y⟩
      change ‖WithLp.toLp 2 (y, -x)‖ ≤ 1 * ‖WithLp.toLp 2 (x, y)‖
      rw [one_mul]
      have hsq : ‖WithLp.toLp 2 (y, -x)‖ ^ 2 ≤ ‖WithLp.toLp 2 (x, y)‖ ^ 2 := by
        rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq,
          WithLp.prod_inner_apply, WithLp.prod_inner_apply]
        simp only [real_inner_self_eq_norm_sq, norm_neg]
        linarith
      nlinarith [norm_nonneg (WithLp.toLp 2 (y, -x)),
        norm_nonneg (WithLp.toLp 2 (x, y))])

/-- Nontrivial constructive inhabitant (`T17`) for `SpectralGapTerminationHypothesis` on
`DoubledSpace ℝ` with Krein-self-adjoint idempotent `P₀ ≠ 0, P₀ ≠ 1`, Krein-self-adjoint
non-commuting off-diagonal coupling `H`, positive coupling bound `ε = 1 > 0`, and nonzero
resolvent `R = 1 - P₀ ≠ 0`. -/
def canonicalNontrivialKreinGapData :
    SpectralGapTerminationHypothesis (InfoGeometry.Krein.DoubledSpace ℝ) where
  P₀ := doubledProjPlus
  H := doubledKreinCouplingOp
  R := 1 - doubledProjPlus
  g := 1
  ε := 1
  δ := 1
  hg := by norm_num
  hδ := by norm_num
  hR := by
    rw [inv_one]
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun u => ?_)
    rcases u with ⟨x, y⟩
    rw [one_mul]
    have hact : (1 - doubledProjPlus) (WithLp.toLp 2 (x, y)) = WithLp.toLp 2 ((0 : ℝ), y) := by
      apply (WithLp.ofLp_injective (p := (2 : ENNReal)))
      ext <;> simp [doubledProjPlus]
    rw [hact]
    have hsq : ‖WithLp.toLp 2 ((0 : ℝ), y)‖ ^ 2 ≤ ‖WithLp.toLp 2 (x, y)‖ ^ 2 := by
      rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq,
        WithLp.prod_inner_apply, WithLp.prod_inner_apply]
      simp only [real_inner_self_eq_norm_sq, norm_zero, ne_eq, OfNat.ofNat_ne_zero,
        not_false_eq_true, zero_pow, zero_add]
      exact le_add_of_nonneg_left (sq_nonneg ‖x‖)
    nlinarith [norm_nonneg (WithLp.toLp 2 ((0 : ℝ), y)),
      norm_nonneg (WithLp.toLp 2 (x, y))]
  h1 := by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun u => ?_)
    rcases u with ⟨x, y⟩
    rw [one_mul]
    have hact : (doubledProjPlus * doubledKreinCouplingOp * (1 - doubledProjPlus))
        (WithLp.toLp 2 (x, y)) = WithLp.toLp 2 (y, (0 : ℝ)) := by
      apply (WithLp.ofLp_injective (p := (2 : ENNReal)))
      ext <;> simp [doubledProjPlus, doubledKreinCouplingOp]
    rw [hact]
    have hsq : ‖WithLp.toLp 2 (y, (0 : ℝ))‖ ^ 2 ≤ ‖WithLp.toLp 2 (x, y)‖ ^ 2 := by
      rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq,
        WithLp.prod_inner_apply, WithLp.prod_inner_apply]
      simp only [real_inner_self_eq_norm_sq, norm_zero, ne_eq, OfNat.ofNat_ne_zero,
        not_false_eq_true, zero_pow, add_zero]
      rw [add_comm]
      exact le_add_of_nonneg_right (sq_nonneg ‖x‖)
    nlinarith [norm_nonneg (WithLp.toLp 2 (y, (0 : ℝ))),
      norm_nonneg (WithLp.toLp 2 (x, y))]
  h2 := by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun u => ?_)
    rcases u with ⟨x, y⟩
    rw [one_mul]
    have hact : ((1 - doubledProjPlus) * doubledKreinCouplingOp * doubledProjPlus)
        (WithLp.toLp 2 (x, y)) = WithLp.toLp 2 ((0 : ℝ), -x) := by
      apply (WithLp.ofLp_injective (p := (2 : ENNReal)))
      ext <;> simp [doubledProjPlus, doubledKreinCouplingOp]
    rw [hact]
    have hsq : ‖WithLp.toLp 2 ((0 : ℝ), -x)‖ ^ 2 ≤ ‖WithLp.toLp 2 (x, y)‖ ^ 2 := by
      rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq,
        WithLp.prod_inner_apply, WithLp.prod_inner_apply]
      simp only [real_inner_self_eq_norm_sq, norm_zero, ne_eq, OfNat.ofNat_ne_zero,
        not_false_eq_true, zero_pow, zero_add, norm_neg]
      rw [add_comm]
      exact le_add_of_nonneg_left (sq_nonneg ‖y‖)
    nlinarith [norm_nonneg (WithLp.toLp 2 ((0 : ℝ), -x)),
      norm_nonneg (WithLp.toLp 2 (x, y))]
  hQR := by
    ext u
    · simp [doubledProjPlus]
    · simp [doubledProjPlus]
  hRQ := by
    ext u
    · simp [doubledProjPlus]
    · simp [doubledProjPlus]
  hgap_threshold := by norm_num

/-- Explicit hypothesis-parameterized `Type 1` bundle packaging continuum / nonperturbative
physical extensions across Seams B, C, and D with explicit non-degeneracy and Krein
self-adjointness constraints:
- Seam B: `ContinuumQCDConfinementHypothesis` and `DynamicalQCDConfinementBridge` (4D confinement & mass gap),
- Seam C: `QuantizedSDiffHelicityHypothesis` with `0 < sdiffQuantized.twoK`,
- Seam D: `ContinuumRGFlowHypothesis` (`lam ≠ 0`, `x0 ≠ 0`) and `SpectralGapTerminationHypothesis`
  (`P₀ * P₀ = P₀`, `P₀ ≠ 0`, `P₀ ≠ 1`, `IsKreinSelfAdjoint P₀`, `IsKreinSelfAdjoint H`, `0 < ε`,
  `R ≠ 0`, `P₀ * H ≠ H * P₀`, exact Schur resolvent identity at `spectral_E`, and nonzero Schur
  correction `effectiveHamiltonian P₀ H R ≠ P₀ * H * P₀`).

Separated from all unconditional algebraic theorems above per R2. -/
structure UnifiedContinuumExtensionHypothesis : Type 1 where
  qcdConfinement : ContinuumQCDConfinementHypothesis
  qcdBridge : DynamicalQCDConfinementBridge qcdConfinement
  sdiffQuantized : QuantizedSDiffHelicityHypothesis
  sdiff_twoK_pos : 0 < sdiffQuantized.twoK
  continuumRG : ContinuumRGFlowHypothesis
  rg_lam_ne_zero : continuumRG.lam ≠ 0
  rg_x0_ne_zero : continuumRG.x0 ≠ 0
  SpectralV : Type
  instNormed : NormedAddCommGroup SpectralV
  instInner : InnerProductSpace ℝ SpectralV
  instComplete : CompleteSpace SpectralV
  instKrein : InfoGeometry.Krein.KreinSpace SpectralV
  spectralGap :
    @SpectralGapTerminationHypothesis SpectralV instNormed instInner instComplete instKrein
  spectral_P0_idem : spectralGap.P₀ * spectralGap.P₀ = spectralGap.P₀
  spectral_P0_ne_zero : spectralGap.P₀ ≠ 0
  spectral_P0_ne_one : spectralGap.P₀ ≠ 1
  spectral_P0_krein_sa : InfoGeometry.Krein.KreinSpace.IsKreinSelfAdjoint spectralGap.P₀
  spectral_H_krein_sa : InfoGeometry.Krein.KreinSpace.IsKreinSelfAdjoint spectralGap.H
  spectral_eps_pos : 0 < spectralGap.ε
  spectral_R_ne_zero : spectralGap.R ≠ 0
  spectral_noncomm : spectralGap.P₀ * spectralGap.H ≠ spectralGap.H * spectralGap.P₀
  spectral_E : ℝ
  spectral_resolvent_right :
    InfoGeometry.Physics.NuclearRealKreinFeshbach.denominator
        spectralGap.P₀ spectralGap.H spectral_E * spectralGap.R =
      1 - spectralGap.P₀
  spectral_schur_ne_zero :
    InfoGeometry.Physics.NuclearRealKreinFeshbach.effectiveHamiltonian
        spectralGap.P₀ spectralGap.H spectralGap.R ≠
      spectralGap.P₀ * spectralGap.H * spectralGap.P₀

attribute [instance] UnifiedContinuumExtensionHypothesis.instNormed
attribute [instance] UnifiedContinuumExtensionHypothesis.instInner
attribute [instance] UnifiedContinuumExtensionHypothesis.instComplete
attribute [instance] UnifiedContinuumExtensionHypothesis.instKrein

private theorem doubledProjPlus_krein_sa :
    InfoGeometry.Krein.KreinSpace.IsKreinSelfAdjoint doubledProjPlus := by
  rw [InfoGeometry.Krein.KreinSpace.isKreinSelfAdjoint_iff]
  intro u v
  rw [InfoGeometry.Krein.krein_inner_prod_l2, InfoGeometry.Krein.krein_inner_prod_l2]
  simp [doubledProjPlus]

private theorem doubledKreinCouplingOp_krein_sa :
    InfoGeometry.Krein.KreinSpace.IsKreinSelfAdjoint doubledKreinCouplingOp := by
  rw [InfoGeometry.Krein.KreinSpace.isKreinSelfAdjoint_iff]
  intro u v
  rw [InfoGeometry.Krein.krein_inner_prod_l2, InfoGeometry.Krein.krein_inner_prod_l2]
  simp [doubledKreinCouplingOp]
  ring

/-- Zero-hypothesis constructive finite-model witness (`T17`) for
`UnifiedContinuumExtensionHypothesis`. -/
def canonicalUnifiedContinuumExtensionHypothesis : UnifiedContinuumExtensionHypothesis where
  qcdConfinement := cl55ModelContinuumHypothesis
  qcdBridge := cl55ModelDynamicalBridge
  sdiffQuantized := defaultQuantizedSDiffHelicityHypothesis
  sdiff_twoK_pos := by decide
  continuumRG := canonicalContinuumRGFlowHypothesis
  rg_lam_ne_zero := by
    dsimp [canonicalContinuumRGFlowHypothesis]
    norm_num
  rg_x0_ne_zero := by
    dsimp [canonicalContinuumRGFlowHypothesis]
    norm_num
  SpectralV := InfoGeometry.Krein.DoubledSpace ℝ
  instNormed := inferInstance
  instInner := inferInstance
  instComplete := inferInstance
  instKrein := inferInstance
  spectralGap := canonicalNontrivialKreinGapData
  spectral_P0_idem := by
    dsimp [canonicalNontrivialKreinGapData]
    ext u
    · simp [doubledProjPlus]
    · simp [doubledProjPlus]
  spectral_P0_ne_zero := by
    intro h0
    have hv := congrArg (fun T : InfoGeometry.Krein.DoubledSpace ℝ →L[ℝ]
        InfoGeometry.Krein.DoubledSpace ℝ => (WithLp.ofLp (T (WithLp.toLp 2 (1, 0)))).1) h0
    dsimp [canonicalNontrivialKreinGapData] at hv
    simp [doubledProjPlus] at hv
  spectral_P0_ne_one := by
    intro h1
    have hv := congrArg (fun T : InfoGeometry.Krein.DoubledSpace ℝ →L[ℝ]
        InfoGeometry.Krein.DoubledSpace ℝ => (WithLp.ofLp (T (WithLp.toLp 2 (0, 1)))).2) h1
    dsimp [canonicalNontrivialKreinGapData] at hv
    simp [doubledProjPlus] at hv
  spectral_P0_krein_sa := doubledProjPlus_krein_sa
  spectral_H_krein_sa := doubledKreinCouplingOp_krein_sa
  spectral_eps_pos := by
    dsimp [canonicalNontrivialKreinGapData]
    norm_num
  spectral_R_ne_zero := by
    intro h0
    have hv := congrArg (fun T : InfoGeometry.Krein.DoubledSpace ℝ →L[ℝ]
        InfoGeometry.Krein.DoubledSpace ℝ => (WithLp.ofLp (T (WithLp.toLp 2 (0, 1)))).2) h0
    dsimp [canonicalNontrivialKreinGapData] at hv
    simp [doubledProjPlus] at hv
  spectral_noncomm := by
    intro hcomm
    have hv := congrArg (fun T : InfoGeometry.Krein.DoubledSpace ℝ →L[ℝ]
        InfoGeometry.Krein.DoubledSpace ℝ => (WithLp.ofLp (T (WithLp.toLp 2 (1, 0)))).2) hcomm
    dsimp [canonicalNontrivialKreinGapData] at hv
    simp [doubledProjPlus, doubledKreinCouplingOp] at hv
  spectral_E := 1
  spectral_resolvent_right := by
    dsimp [canonicalNontrivialKreinGapData]
    ext u
    · simp [InfoGeometry.Physics.NuclearRealKreinFeshbach.denominator,
        doubledProjPlus, doubledKreinCouplingOp]
    · simp [InfoGeometry.Physics.NuclearRealKreinFeshbach.denominator,
        doubledProjPlus, doubledKreinCouplingOp]
  spectral_schur_ne_zero := by
    intro heq
    have hv := congrArg (fun T : InfoGeometry.Krein.DoubledSpace ℝ →L[ℝ]
        InfoGeometry.Krein.DoubledSpace ℝ => (WithLp.ofLp (T (WithLp.toLp 2 (1, 0)))).1) heq
    dsimp [canonicalNontrivialKreinGapData] at hv
    simp [InfoGeometry.Physics.NuclearRealKreinFeshbach.effectiveHamiltonian,
      doubledProjPlus, doubledKreinCouplingOp] at hv

/-- Conditional continuum synthesis theorem deriving Seam B dynamical baryon confinement,
Casimir/Drazin annihilation, monodromy mass-gap preservation, Wilson area-law decay,
Seam C nonzero quantized `SDiff` coadjoint helicity invariance, and Seam D nontrivial
continuum/discrete RG derivatives + Krein-self-adjoint non-degenerate Schur spectral-gap bound
from `UnifiedContinuumExtensionHypothesis`. -/
theorem unified_conditional_continuum_extension_theorem
    (U : UnifiedContinuumExtensionHypothesis)
    (u v w : InfoGeometry.Canonical.GaugedZornDiracKahler.Vec3 ℝ)
    (g : InfoGeometry.Physics.B3PresentedGroup.B3)
    (ψ : U.qcdConfinement.ContinuumState) (hne : ψ ≠ 0)
    (hker : U.qcdConfinement.singletProjector ψ = 0)
    (area : ℝ) (harea : 0 < area)
    (R : InfoGeometry.Physics.SDiffCoadjoint.LocalSDiffIsometry)
    (h_smul : ∀ (c : ℝ) (v3 : _root_.ChiralVector3), R.toFun (c • v3) = c • R.toFun v3)
    (lambda_param : ℝ) (u3 omega3 : _root_.ChiralVector3) :
    (U.qcdBridge.zornToContinuum (InfoGeometry.Canonical.ZornColorConfinementBaryon.baryonState u v w) =
        (InfoGeometry.Canonical.GaugedZornDiracKahler.dot3
          (InfoGeometry.Canonical.GaugedZornDiracKahler.cross3 u v) w) •
          U.qcdConfinement.embedCl55 InfoGeometry.Physics.Cl55SpinorCartanFock.colorBaryonSingletProj ∧
      (U.qcdConfinement.embedCl55 InfoGeometry.Physics.Cl55WignerSU4Embedding.colorSU3Casimir).comp
        U.qcdConfinement.singletProjector = 0 ∧
      U.qcdConfinement.massGap ≤
        U.qcdConfinement.energy ((U.qcdBridge.monodromyAction g : Module.End ℂ U.qcdConfinement.ContinuumState) ψ) ∧
      U.qcdConfinement.wilsonAreaExponent area < 0) ∧
    (InfoGeometry.Physics.SDiffCoadjoint.totalHelicity
        (InfoGeometry.Physics.SDiffCoadjoint.coadjointFlow R U.sdiffQuantized.state) =
      InfoGeometry.Physics.SDiffCoadjoint.totalHelicity U.sdiffQuantized.state ∧
      sdiffHelicitySignParity
        (InfoGeometry.Physics.SDiffCoadjoint.coadjointFlow R U.sdiffQuantized.state) =
      sdiffHelicitySignParity U.sdiffQuantized.state ∧
      0 < U.sdiffQuantized.twoK ∧
      0 < |InfoGeometry.Physics.SDiffCoadjoint.totalHelicity U.sdiffQuantized.state|) ∧
    (HasDerivAt U.continuumRG.flow (U.continuumRG.lam * U.continuumRG.x0) 0 ∧
      (∀ n : ℕ,
        HasDerivAt U.continuumRG.flow (U.continuumRG.lam * U.continuumRG.discreteStep n)
          ((n : ℝ) * U.continuumRG.dt) ∧
        U.continuumRG.discreteStep n = U.continuumRG.flow ((n : ℝ) * U.continuumRG.dt)) ∧
      U.continuumRG.lam ≠ 0 ∧
      U.continuumRG.x0 ≠ 0 ∧
      0 < U.continuumRG.dt ∧
      ‖InfoGeometry.Physics.NuclearRealKreinFeshbach.effectiveHamiltonian
          U.spectralGap.P₀ U.spectralGap.H U.spectralGap.R -
        U.spectralGap.P₀ * U.spectralGap.H * U.spectralGap.P₀‖ ≤ U.spectralGap.δ ∧
      U.spectralGap.P₀ * U.spectralGap.P₀ = U.spectralGap.P₀ ∧
      U.spectralGap.P₀ ≠ 0 ∧
      U.spectralGap.P₀ ≠ 1 ∧
      InfoGeometry.Krein.KreinSpace.IsKreinSelfAdjoint U.spectralGap.P₀ ∧
      InfoGeometry.Krein.KreinSpace.IsKreinSelfAdjoint U.spectralGap.H ∧
      0 < U.spectralGap.ε ∧
      U.spectralGap.R ≠ 0 ∧
      U.spectralGap.P₀ * U.spectralGap.H ≠ U.spectralGap.H * U.spectralGap.P₀ ∧
      InfoGeometry.Physics.NuclearRealKreinFeshbach.denominator
          U.spectralGap.P₀ U.spectralGap.H U.spectral_E * U.spectralGap.R =
        1 - U.spectralGap.P₀ ∧
      InfoGeometry.Physics.NuclearRealKreinFeshbach.effectiveHamiltonian
          U.spectralGap.P₀ U.spectralGap.H U.spectralGap.R ≠
        U.spectralGap.P₀ * U.spectralGap.H * U.spectralGap.P₀ ∧
      U.spectralGap.P₀ * U.spectralGap.H * (1 - U.spectralGap.P₀) ≠ 0 ∧
      InfoGeometry.Krein.KreinSpace.IsKreinSelfAdjoint
        (InfoGeometry.Physics.NuclearRealKreinFeshbach.effectiveHamiltonian
          U.spectralGap.P₀ U.spectralGap.H U.spectralGap.R)) := by
  have hB_bar := dynamical_zorn_baryon_lands_in_continuum_singlet U.qcdBridge u v w
  have hB_cas := dynamical_casimir_and_drazin_annihilate_continuum_singlet U.qcdConfinement
  have hB_gap := dynamical_monodromy_preserves_non_singlet_mass_gap U.qcdBridge g ψ hne hker
  have hB_wil := dynamical_wilson_area_law_strictly_decaying U.qcdConfinement harea
  have hC := sdiff_helicity_coadjoint_and_sign_parity_invariant
    R U.sdiffQuantized.state h_smul lambda_param u3 omega3 U.sdiffQuantized
  have hC_pos : 0 < |InfoGeometry.Physics.SDiffCoadjoint.totalHelicity U.sdiffQuantized.state| := by
    rw [U.sdiffQuantized.quantization_law]
    exact mul_pos U.sdiffQuantized.helicityScale_pos (Nat.cast_pos.mpr U.sdiff_twoK_pos)
  have hD_rg := continuum_rg_flow_zero_deriv U.continuumRG
  have hD_step : ∀ n : ℕ,
      HasDerivAt U.continuumRG.flow (U.continuumRG.lam * U.continuumRG.discreteStep n)
        ((n : ℝ) * U.continuumRG.dt) ∧
      U.continuumRG.discreteStep n = U.continuumRG.flow ((n : ℝ) * U.continuumRG.dt) :=
    fun n => ⟨continuum_rg_flow_discrete_step_deriv U.continuumRG n, U.continuumRG.discreteStep_samples n⟩
  have hD_gap := spectral_gap_termination_schur_bound U.spectralGap
  have hD_offdiag_ne :
      U.spectralGap.P₀ * U.spectralGap.H * (1 - U.spectralGap.P₀) ≠ 0 := by
    intro h0
    apply U.spectral_schur_ne_zero
    unfold InfoGeometry.Physics.NuclearRealKreinFeshbach.effectiveHamiltonian
    have hterm :
        U.spectralGap.P₀ * U.spectralGap.H * U.spectralGap.R * U.spectralGap.H *
          U.spectralGap.P₀ = 0 := by
      rw [← U.spectralGap.hQR]
      have hre :
          U.spectralGap.P₀ * U.spectralGap.H * ((1 - U.spectralGap.P₀) * U.spectralGap.R) *
            U.spectralGap.H * U.spectralGap.P₀ =
          (U.spectralGap.P₀ * U.spectralGap.H * (1 - U.spectralGap.P₀)) *
            (U.spectralGap.R * U.spectralGap.H * U.spectralGap.P₀) := by
        noncomm_ring
      rw [hre, h0, zero_mul]
    rw [hterm, add_zero]
  have hD_eff_sa :=
    InfoGeometry.Physics.NuclearRealKreinFeshbach.effectiveHamiltonian_kreinSelfAdjoint
      U.spectralGap.P₀ U.spectralGap.H U.spectralGap.R U.spectral_E
      U.spectral_P0_krein_sa U.spectral_H_krein_sa U.spectralGap.hQR U.spectral_resolvent_right
  exact ⟨⟨hB_bar.1, hB_cas.1, hB_gap.1, hB_wil⟩,
    ⟨hC.2.2.2.1.1, hC.2.1, U.sdiff_twoK_pos, hC_pos⟩,
    ⟨hD_rg, hD_step, U.rg_lam_ne_zero, U.rg_x0_ne_zero, U.continuumRG.dt_pos, hD_gap,
      U.spectral_P0_idem, U.spectral_P0_ne_zero, U.spectral_P0_ne_one,
      U.spectral_P0_krein_sa, U.spectral_H_krein_sa,
      U.spectral_eps_pos, U.spectral_R_ne_zero, U.spectral_noncomm, U.spectral_resolvent_right,
      U.spectral_schur_ne_zero, hD_offdiag_ne, hD_eff_sa⟩⟩

end InfoGeometry.Synthesis.NuclearUnifiedParityFiveGradeRenormalizationSynthesis

end
