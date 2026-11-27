/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Tactic
import InfoGeometry.Nuclear.NuclearPhononRPAAlgebra
import InfoGeometry.Physics.NuclearPhononRPAAlgebra
import InfoGeometry.Physics.NuclearRPAQuantumNumberSeparation
import InfoGeometry.Physics.NuclearFeshbachReduction
import InfoGeometry.Physics.NuclearOperatorSchurComplement
import InfoGeometry.Physics.NuclearEffectiveMultipole
import InfoGeometry.Physics.NuclearThreeConfigurationKreinReduction
import InfoGeometry.Physics.NuclearRealKreinFeshbach
import InfoGeometry.Physics.OperatorRPABlock
import InfoGeometry.Physics.OperatorRPABlockZornKreinFlow
import InfoGeometry.Physics.NuclearFiveGradeSameCarrierClosure
import InfoGeometry.Integration.IwasawaTimeRenormalization
import InfoGeometry.OptimalTransport.DilatonAndreevRenormalization
import InfoGeometry.Canonical.BogoliubovRGFlowBridge
import InfoGeometry.Physics.DilatonWeylAnomalyInflowBridge
import InfoGeometry.Volume.IwasawaScaleParityBridge
import InfoGeometry.Algebra.IwasawaRealKAN

/-!
# Seam D: Discrete Feshbach/Schur Elimination & Krein RPA Flow to Renormalization Flow

This synthesis module reconciles and bridges the discrete Feshbach/Schur/Krein elimination
architecture, dual nuclear phonon RPA algebras, and `Block2` hyperbolic Krein-Bogoliubov flow
with Iwasawa scale conjugation, dilaton-Andreev exponential renormalization, Callan-Harvey
anomaly inflow, and Bogoliubov RG decimation.

## Main Components
1. **Non-Commutativity Witnesses & Dual `NuclearPhononRPAAlgebra` Reconciliation**:
   Explicit `Block2 ℝ` non-commutativity witnesses (`T16`), connecting finite-matrix CCR
   obstructions in `InfoGeometry.Nuclear.NuclearPhononRPAAlgebra` with the infinite Fock
   realization `fockPhononRPA` (`B ≠ 0`), static single-pair CAR obstructions, and CAR-RPA
   quantum-number separation in `InfoGeometry.Physics.NuclearPhononRPA` and
   `InfoGeometry.Physics.NuclearRPAQuantumNumberSeparation`.
2. **Lifting `IwasawaTimeRenormalization.RenormalizationData` & Commutation Boundaries**:
   Embeds `RenormalizationData` into `Block2`, exhibits an explicit non-commuting
   `RenormalizationData IwasawaRealKAN.Mat2` witness (`aDiag lam` + `nShear ξ`), and
   contrasts `[scale, unipotent] = 0` and `[P, H] = 0` against preserved `[a, b] ≠ 0`.
3. **Hyperbolic Krein-Bogoliubov Flow ↔ Dilaton-Andreev RG & Hadamard Intertwining**:
   Proves exact Hadamard intertwining
   `blockHamiltonian 1 (-1) 1 1 * kreinHyperbolicFlow lam τ * blockHamiltonian 1 (-1) 1 1 = (2 : ℝ) • aDiag (lam * τ)`,
   linking `OperatorRPABlockZornKreinFlow.kreinBogoliubovU` directly to
   `DilatonAndreevRenormalization`, `DilatonWeylAnomalyInflow`, and `IwasawaScaleParityBridge`,
   while proving `[a, b]` RPA curvature defect invariance (`R2`) over any `[Ring A] [Algebra ℝ A]`
   and instantiating on `M4R` via `NuclearFiveGradeSameCarrierClosure`.
4. **Discrete Feshbach/Schur/Krein Reduction ↔ `BogoliubovRGFlowBridge`**:
   Bridges `NuclearFeshbachReduction`, `NuclearOperatorSchurComplement`,
   `NuclearEffectiveMultipole`, `NuclearThreeConfigurationKreinReduction`, and
   `NuclearRealKreinFeshbach` with `BogoliubovRGFlowBridge.SchurRGDecimation`.
5. **Conditional Continuum RG & Spectral-Gap Termination (`Type*` + `T17` Witnesses)**:
   Models continuum multi-scale RG limits and spectral-gap termination via explicit
   hypothesis-parameterized `Type*` structures (`ContinuumRGFlowHypothesis`,
   `SpectralGapTerminationHypothesis`) with zero-argument constructive witnesses.
-/

set_option autoImplicit false

namespace InfoGeometry.Synthesis.FeshbachRPASchurRenormalizationFlow

noncomputable section

open InfoGeometry.Physics.NuclearOperatorSuperSoloviev (Block2 blockHamiltonian)
open InfoGeometry.Physics.NuclearInternalExternalParityFactorization (externalFockParity)

private abbrev M4R := InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.M4R

/-! ## 1. Non-Commutativity Witnesses & Dual `NuclearPhononRPAAlgebra` Reconciliation -/

section DualPhononRPAReconciliation

/-- Concrete `Block2 ℝ` (`Matrix (Fin 2) (Fin 2) ℝ`) non-commutativity witness (`T16`). -/
def rpaWitnessA : Block2 ℝ := blockHamiltonian (1 : ℝ) (-1) 0 0

/-- Concrete off-diagonal `Block2 ℝ` matrix failing to commute with `rpaWitnessA`. -/
def rpaWitnessB : Block2 ℝ := blockHamiltonian (0 : ℝ) 0 1 0

/-- Explicit closed `Block2 ℝ` non-commutativity witness and resulting nonzero RPA square defect. -/
theorem block2_real_noncomm_and_rpa_defect_witness :
    rpaWitnessA * rpaWitnessB ≠ rpaWitnessB * rpaWitnessA ∧
      (blockHamiltonian rpaWitnessA (-rpaWitnessA) rpaWitnessB (-rpaWitnessB) *
        blockHamiltonian rpaWitnessA (-rpaWitnessA) rpaWitnessB (-rpaWitnessB)) 0 1 ≠ 0 := by
  have hnc : rpaWitnessA * rpaWitnessB ≠ rpaWitnessB * rpaWitnessA := by
    intro h
    have h01 := congrFun (congrFun h 0) 1
    simp [rpaWitnessA, rpaWitnessB, blockHamiltonian, Matrix.mul_apply, Fin.sum_univ_two] at h01
    norm_num at h01
  exact ⟨hnc,
    InfoGeometry.Physics.OperatorRPABlock.rpa_square_offDiagonal_ne_zero_of_not_commute
      rpaWitnessA rpaWitnessB hnc⟩

/-- General `Block2 ℝ` existential non-commutativity witness (`T16`). -/
theorem block2_real_exists_noncomm :
    ∃ A B : Block2 ℝ, A * B ≠ B * A :=
  ⟨rpaWitnessA, rpaWitnessB, block2_real_noncomm_and_rpa_defect_witness.1⟩

/-- Reconciles the finite-matrix CCR impossibility in `InfoGeometry.Nuclear.NuclearPhononRPAAlgebra`
with the infinite Fock realization `fockPhononRPA` (`B ≠ 0`) and static single-pair CAR
obstruction (`B = 0`) in `InfoGeometry.Physics.NuclearPhononRPA`, together with the
`Block2` Thouless zero-mode bridge. -/
theorem dual_phonon_rpa_reconciliation
    (R2 : InfoGeometry.Nuclear.NuclearPhononRPAAlgebra.QuasibosonRPADatum)
    {n : ℕ} (hn : 0 < n)
    (Rn : InfoGeometry.Nuclear.NuclearPhononRPAAlgebra.QuasibosonRPADatumN ℝ n) :
    (¬ ∃ Q Qdag : InfoGeometry.Nuclear.NuclearPhononRPAAlgebra.Mat2,
        InfoGeometry.Nuclear.NuclearPhononRPAAlgebra.commutator Q Qdag = 1) ∧
      R2.defect ≠ 0 ∧
      (¬ ∃ Q Qdag : Matrix (Fin n) (Fin n) ℝ,
        InfoGeometry.Nuclear.NuclearPhononRPAAlgebra.commutatorN Q Qdag = 1) ∧
      Rn.defect ≠ 0 ∧
      IsEmpty (InfoGeometry.Physics.NuclearPhononRPA.PhononRPA (Fin 2)
        (Matrix (Fin n) (Fin n) ℝ)) ∧
      ((!![(0 : ℝ), (-1 : ℝ); (-1 : ℝ), (0 : ℝ)] : Matrix (Fin 2) (Fin 2) ℝ) ≠ 0 ∧
        InfoGeometry.Physics.NuclearPhononRPA.comm
          (InfoGeometry.Physics.NuclearPhononRPA.fockPhononRPA.Qdag 0 *
              InfoGeometry.Physics.NuclearPhononRPA.fockPhononRPA.Q 0 +
            InfoGeometry.Physics.NuclearPhononRPA.fockPhononRPA.Qdag 1 *
              InfoGeometry.Physics.NuclearPhononRPA.fockPhononRPA.Q 1 +
            (InfoGeometry.Physics.NuclearPhononRPA.fockPhononRPA.Qdag 0 *
                InfoGeometry.Physics.NuclearPhononRPA.fockPhononRPA.Qdag 1 +
              InfoGeometry.Physics.NuclearPhononRPA.fockPhononRPA.Q 0 *
                InfoGeometry.Physics.NuclearPhononRPA.fockPhononRPA.Q 1))
          (InfoGeometry.Physics.NuclearPhononRPA.fockPhononRPA.rpaMode Finset.univ
            (![1, 0] : Fin 2 → ℝ) (![0, 1] : Fin 2 → ℝ)) = 0) := by
  refine ⟨InfoGeometry.Nuclear.NuclearPhononRPAAlgebra.no_exact_boson_ccr_2x2,
    R2.defect_ne_zero,
    InfoGeometry.Nuclear.NuclearPhononRPAAlgebra.no_exact_boson_ccr_fin n hn,
    InfoGeometry.Nuclear.NuclearPhononRPAAlgebra.QuasibosonRPADatumN.defect_ne_zero hn Rn,
    InfoGeometry.Physics.NuclearPhononRPA.no_finite_matrix_phononRPA n hn,
    ?_⟩
  have htw := InfoGeometry.Physics.NuclearPhononRPA.phononRPA_thouless_witness_B_nonzero
  exact ⟨htw.1, htw.2.2.1⟩

/-- CAR-RPA quantum-number separation, static single-pair `B0 = 0` obstruction, QBA zero-defect
embedding, and `Block2` Thouless zero-mode realization. -/
theorem car_rpa_separation_and_block_thouless_bridge
    {ι_qp ι_ph : Type*} [DecidableEq ι_qp] [DecidableEq ι_ph]
    {A : Type*} [Ring A] [Algebra ℝ A]
    (sys : InfoGeometry.Physics.NuclearPhononRPA.CoupledQuasiparticlePhononSystem ι_qp ι_ph A)
    (i : ι_qp) (j : ι_ph)
    {V : Type*} [AddCommGroup V] [Module ℝ V] [Module A V] [IsScalarTower ℝ A V]
    (v : V) (hv : v ≠ 0)
    (hvac : ∀ p, sys.car.a p • v = 0)
    {a b : ι_qp} (hab : a ≠ b) (H : A) (A0 B0 : ℝ)
    (h_eom : InfoGeometry.Physics.NuclearPhononRPA.comm H (sys.car.pairCreation a b) =
      A0 • sys.car.pairCreation a b - B0 • sys.car.pairAnnihilation a b)
    (pairs : Finset (ι_qp × ι_qp))
    (h_no_swap : ∀ p ∈ pairs, (p.2, p.1) ∉ pairs)
    (ψ : ι_ph → ι_qp → ι_qp → ℝ)
    (h_ortho : ∀ μ μ', ∑ p ∈ pairs, ψ μ p.1 p.2 * ψ μ' p.1 p.2 = if μ = μ' then (1 : ℝ) else 0)
    (h_defect : ∀ μ μ', sys.car.tdaPairPauliDefect pairs pairs (ψ μ) (ψ μ') = 0) :
    (InfoGeometry.Physics.NuclearPhononRPA.comm (sys.car.numberOp i) (sys.rpa.numberOp j) = 0 ∧
      InfoGeometry.Physics.NuclearPhononRPA.comm
        (sys.car.centeredOccupationCartan i) (sys.rpa.numberOp j) = 0 ∧
      InfoGeometry.Physics.NuclearPhononRPA.comm
        (sys.car.vacancyProjector i) (sys.rpa.numberOp j) = 0 ∧
      InfoGeometry.Physics.NuclearPhononRPA.comm
        (sys.car.fermionParity i) (sys.rpa.numberOp j) = 0) ∧
      B0 = 0 ∧
      Nonempty (InfoGeometry.Physics.NuclearPhononRPA.PhononRPA ι_ph A) := by
  refine ⟨InfoGeometry.Physics.NuclearRPAQuantumNumberSeparation.car_rpa_quantum_number_separation_packet
      sys i j,
    InfoGeometry.Physics.NuclearPhononRPA.car_operator_eom_single_pair_forces_B_zero
      sys.car v hv hvac a b hab H A0 B0 h_eom,
    ⟨InfoGeometry.Physics.NuclearPhononRPA.tdaPhononRPA_of_zero_pauliDefect
      sys.car pairs h_no_swap ψ h_ortho h_defect⟩⟩

/-- Translates a `PhononRPA` Thouless/Goldstone zero mode directly to a zero eigenvector of
`blockHamiltonian A_mat (-A_mat) B_mat (-B_mat)` via `OperatorRPABlock`. -/
theorem phonon_rpa_thouless_to_block_zero_mode
    {ι F Alg : Type*} [Fintype ι] [DecidableEq ι] [Field F] [Ring Alg] [Algebra F Alg]
    [Nontrivial Alg]
    (rpa : InfoGeometry.Physics.NuclearPhononRPA.PhononRPA ι Alg)
    (H P_rest : Alg) (A_mat B_mat : Matrix ι ι F) (x y : ι → F)
    (h_eom_Qdag : ∀ i : ι, InfoGeometry.Physics.NuclearPhononRPA.comm H (rpa.Qdag i) =
      ∑ j : ι, (A_mat j i • rpa.Qdag j - B_mat j i • rpa.Q j))
    (h_eom_Q : ∀ i : ι, InfoGeometry.Physics.NuclearPhononRPA.comm H (rpa.Q i) =
      ∑ j : ι, (B_mat j i • rpa.Qdag j - A_mat j i • rpa.Q j))
    (h_rest : ∀ k : ι,
      InfoGeometry.Physics.NuclearPhononRPA.comm (rpa.Q k)
        (InfoGeometry.Physics.NuclearPhononRPA.comm H P_rest) = 0 ∧
      InfoGeometry.Physics.NuclearPhononRPA.comm (rpa.Qdag k)
        (InfoGeometry.Physics.NuclearPhononRPA.comm H P_rest) = 0)
    (h_comm : InfoGeometry.Physics.NuclearPhononRPA.comm H
      (P_rest + rpa.rpaMode Finset.univ x y) = 0) :
    InfoGeometry.Physics.OperatorRPABlock.blockAction
      (blockHamiltonian A_mat (-A_mat) B_mat (-B_mat)) ![x, y] = 0 :=
  InfoGeometry.Physics.OperatorRPABlock.phononRPA_thouless_zero_mode_to_blockHamiltonian
    rpa H P_rest A_mat B_mat x y h_eom_Qdag h_eom_Q h_rest h_comm

end DualPhononRPAReconciliation

/-! ## 2. Lifting `RenormalizationData` to `Block2` & `IwasawaRealKAN` Non-Commutation -/

section RenormalizationBlockLift

variable {R : Type*} [Ring R]

/-- Diagonal `Block2 R` lift of the invertible Iwasawa scale unit. -/
def liftRenormalizationScale
    (Ops : InfoGeometry.Integration.IwasawaTimeRenormalization.RenormalizationData R) :
    Block2 R :=
  blockHamiltonian (Ops.scale : R) (Ops.scale : R) 0 0

/-- Diagonal `Block2 R` lift of the inverse Iwasawa scale unit. -/
def liftRenormalizationScaleInv
    (Ops : InfoGeometry.Integration.IwasawaTimeRenormalization.RenormalizationData R) :
    Block2 R :=
  blockHamiltonian (↑Ops.scale⁻¹ : R) (↑Ops.scale⁻¹ : R) 0 0

/-- Diagonal `Block2 R` lift of the unipotent renormalization step. -/
def liftRenormalizationUnipotent
    (Ops : InfoGeometry.Integration.IwasawaTimeRenormalization.RenormalizationData R) :
    Block2 R :=
  blockHamiltonian Ops.unipotent Ops.unipotent 0 0

/-- `Block2 R` lift of `IwasawaTimeRenormalization.normalizedStep`. -/
def liftNormalizedStep
    (Ops : InfoGeometry.Integration.IwasawaTimeRenormalization.RenormalizationData R) :
    Block2 R :=
  liftRenormalizationScale Ops * liftRenormalizationUnipotent Ops * liftRenormalizationScaleInv Ops

/-- The `Block2 R` lift of `normalizedStep` equals the diagonal block of `normalizedStep Ops`. -/
theorem liftNormalizedStep_eq_blockHamiltonian
    (Ops : InfoGeometry.Integration.IwasawaTimeRenormalization.RenormalizationData R) :
    liftNormalizedStep Ops =
      blockHamiltonian
        (InfoGeometry.Integration.IwasawaTimeRenormalization.normalizedStep Ops)
        (InfoGeometry.Integration.IwasawaTimeRenormalization.normalizedStep Ops) 0 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [liftNormalizedStep, liftRenormalizationScale, liftRenormalizationUnipotent,
      liftRenormalizationScaleInv,
      InfoGeometry.Integration.IwasawaTimeRenormalization.normalizedStep,
      blockHamiltonian, Matrix.mul_apply, Fin.sum_univ_two]

/-- When `[scale, unipotent] = 0`, the lifted normalized step collapses to the unipotent block. -/
theorem liftNormalizedStep_eq_unipotent_of_commute
    (Ops : InfoGeometry.Integration.IwasawaTimeRenormalization.RenormalizationData R)
    (hcomm : (Ops.scale : R) * Ops.unipotent = Ops.unipotent * (Ops.scale : R)) :
    liftNormalizedStep Ops = liftRenormalizationUnipotent Ops := by
  rw [liftNormalizedStep_eq_blockHamiltonian,
    InfoGeometry.Integration.IwasawaTimeRenormalization.normalizedStep_eq_unipotent Ops hcomm]
  rfl

/-- Lifts quadratic ghost accumulation `(1 + ghost)^2 = 1 + 2 * ghost` into `Block2 R`. -/
theorem liftRenormalizationGhost_accumulation
    (Ops : InfoGeometry.Integration.IwasawaTimeRenormalization.RenormalizationData R)
    (hN : InfoGeometry.Integration.IwasawaTimeRenormalization.ghost Ops *
      InfoGeometry.Integration.IwasawaTimeRenormalization.ghost Ops = 0) :
    liftRenormalizationUnipotent Ops * liftRenormalizationUnipotent Ops =
      1 + (2 : ℕ) • blockHamiltonian
        (InfoGeometry.Integration.IwasawaTimeRenormalization.ghost Ops)
        (InfoGeometry.Integration.IwasawaTimeRenormalization.ghost Ops) 0 0 := by
  have hacc :=
    InfoGeometry.Integration.IwasawaTimeRenormalization.unipotent_time_accumulation Ops hN
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [liftRenormalizationUnipotent, blockHamiltonian, Matrix.mul_apply, Fin.sum_univ_two, hacc]

end RenormalizationBlockLift

section NoncommKANRenormalizationWitness

private theorem aDiag_mul_neg (lam : ℝ) :
    InfoGeometry.Algebra.IwasawaRealKAN.aDiag lam *
      InfoGeometry.Algebra.IwasawaRealKAN.aDiag (-lam) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [InfoGeometry.Algebra.IwasawaRealKAN.aDiag, Matrix.mul_apply, Fin.sum_univ_two,
      ← Real.exp_add]

private theorem aDiag_neg_mul (lam : ℝ) :
    InfoGeometry.Algebra.IwasawaRealKAN.aDiag (-lam) *
      InfoGeometry.Algebra.IwasawaRealKAN.aDiag lam = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [InfoGeometry.Algebra.IwasawaRealKAN.aDiag, Matrix.mul_apply, Fin.sum_univ_two,
      ← Real.exp_add]

/-- Concrete non-commuting `RenormalizationData IwasawaRealKAN.Mat2` built from `aDiag lam`
and the unipotent shear `nShear ξ`. -/
def noncommKanRenormalizationData (lam ξ : ℝ) :
    InfoGeometry.Integration.IwasawaTimeRenormalization.RenormalizationData
      InfoGeometry.Algebra.IwasawaRealKAN.Mat2 where
  prefactor := 1
  scale := ⟨InfoGeometry.Algebra.IwasawaRealKAN.aDiag lam,
    InfoGeometry.Algebra.IwasawaRealKAN.aDiag (-lam),
    aDiag_mul_neg lam, aDiag_neg_mul lam⟩
  unipotent := InfoGeometry.Algebra.IwasawaRealKAN.nShear ξ

/-- The ghost of `noncommKanRenormalizationData lam ξ` is the nilpotent shear `ξ • sPlus`. -/
theorem noncommKanRenormalizationData_ghost (lam ξ : ℝ) :
    InfoGeometry.Integration.IwasawaTimeRenormalization.ghost
        (noncommKanRenormalizationData lam ξ) =
      ξ • InfoGeometry.Algebra.IwasawaRealKAN.sPlus := by
  dsimp [InfoGeometry.Integration.IwasawaTimeRenormalization.ghost, noncommKanRenormalizationData]
  rw [InfoGeometry.Algebra.IwasawaRealKAN.nShear_eq_one_add_smul]
  abel

/-- The ghost of `noncommKanRenormalizationData lam ξ` squares to zero, giving exact
unipotent quadratic accumulation. -/
theorem noncommKanRenormalizationData_accumulation (lam ξ : ℝ) :
    InfoGeometry.Integration.IwasawaTimeRenormalization.ghost
        (noncommKanRenormalizationData lam ξ) *
      InfoGeometry.Integration.IwasawaTimeRenormalization.ghost
        (noncommKanRenormalizationData lam ξ) = 0 ∧
      (noncommKanRenormalizationData lam ξ).unipotent *
        (noncommKanRenormalizationData lam ξ).unipotent =
      1 + 2 * InfoGeometry.Integration.IwasawaTimeRenormalization.ghost
        (noncommKanRenormalizationData lam ξ) := by
  have hsq :
      InfoGeometry.Integration.IwasawaTimeRenormalization.ghost
          (noncommKanRenormalizationData lam ξ) *
        InfoGeometry.Integration.IwasawaTimeRenormalization.ghost
          (noncommKanRenormalizationData lam ξ) = 0 := by
    rw [noncommKanRenormalizationData_ghost]
    have hs : InfoGeometry.Algebra.IwasawaRealKAN.sPlus *
        InfoGeometry.Algebra.IwasawaRealKAN.sPlus = 0 := by
      simpa [pow_two] using InfoGeometry.Algebra.IwasawaRealKAN.sPlus_sq
    rw [smul_mul_assoc, mul_smul_comm, hs, smul_zero, smul_zero]
  exact ⟨hsq, InfoGeometry.Integration.IwasawaTimeRenormalization.unipotent_time_accumulation
    (noncommKanRenormalizationData lam ξ) hsq⟩

/-- Non-commuting conjugation `aDiag lam * nShear ξ * aDiag (-lam)` rescales the shear parameter
by `Real.exp (2 * lam)` (`normalizedStep` is genuinely non-trivial when `lam ≠ 0` and `ξ ≠ 0`). -/
theorem noncommKanRenormalizationData_normalizedStep (lam ξ : ℝ) :
    InfoGeometry.Integration.IwasawaTimeRenormalization.normalizedStep
        (noncommKanRenormalizationData lam ξ) =
      InfoGeometry.Algebra.IwasawaRealKAN.nShear (Real.exp (2 * lam) * ξ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [InfoGeometry.Integration.IwasawaTimeRenormalization.normalizedStep,
      noncommKanRenormalizationData, InfoGeometry.Algebra.IwasawaRealKAN.aDiag,
      InfoGeometry.Algebra.IwasawaRealKAN.nShear, Matrix.mul_apply, Fin.sum_univ_two]
  · rw [← Real.exp_add]; simp
  · rw [mul_right_comm, ← Real.exp_add, two_mul]
  · rw [← Real.exp_add]; simp

/-- When `lam ≠ 0` and `ξ ≠ 0`, `aDiag lam` and `nShear ξ` genuinely do not commute, so
`normalizedStep` differs from `unipotent`. -/
theorem noncommKanRenormalizationData_noncomm_of_ne_zero {lam ξ : ℝ}
    (hlam : lam ≠ 0) (hξ : ξ ≠ 0) :
    ((noncommKanRenormalizationData lam ξ).scale : InfoGeometry.Algebra.IwasawaRealKAN.Mat2) *
        (noncommKanRenormalizationData lam ξ).unipotent ≠
      (noncommKanRenormalizationData lam ξ).unipotent *
        (noncommKanRenormalizationData lam ξ).scale ∧
      InfoGeometry.Integration.IwasawaTimeRenormalization.normalizedStep
        (noncommKanRenormalizationData lam ξ) ≠
      (noncommKanRenormalizationData lam ξ).unipotent := by
  have hdiff : Real.exp (2 * lam) * ξ ≠ ξ := by
    intro heq
    have h1 : Real.exp (2 * lam) = 1 := by
      have hsub : (Real.exp (2 * lam) - 1) * ξ = 0 := by linarith
      rcases mul_eq_zero.mp hsub with h0 | hξ0
      · linarith
      · exact (hξ hξ0).elim
    have h2 : 2 * lam = 0 := Real.exp_injective (by simpa using h1)
    exact hlam (by linarith)
  have hstep :
      InfoGeometry.Integration.IwasawaTimeRenormalization.normalizedStep
          (noncommKanRenormalizationData lam ξ) ≠
        (noncommKanRenormalizationData lam ξ).unipotent := by
    intro h
    have h01 := congrFun (congrFun h 0) 1
    rw [noncommKanRenormalizationData_normalizedStep] at h01
    simp [noncommKanRenormalizationData, InfoGeometry.Algebra.IwasawaRealKAN.nShear] at h01
    exact hdiff h01
  have hnc :
      ((noncommKanRenormalizationData lam ξ).scale : InfoGeometry.Algebra.IwasawaRealKAN.Mat2) *
          (noncommKanRenormalizationData lam ξ).unipotent ≠
        (noncommKanRenormalizationData lam ξ).unipotent *
          (noncommKanRenormalizationData lam ξ).scale := by
    intro hcomm
    exact hstep
      (InfoGeometry.Integration.IwasawaTimeRenormalization.normalizedStep_eq_unipotent
        (noncommKanRenormalizationData lam ξ) hcomm)
  exact ⟨hnc, hstep⟩

end NoncommKANRenormalizationWitness

/-! ## 3. Hyperbolic Krein Flow ↔ Dilaton-Andreev RG & R2 `[a, b]` Defect Preservation -/

section KreinHyperbolicDilatonAndRPA

/-- Hyperbolic Krein-Bogoliubov flow `U_K(cosh (lam * τ), sinh (lam * τ))` on `Block2 ℝ`. -/
def kreinHyperbolicFlow (lam τ : ℝ) : Block2 ℝ :=
  InfoGeometry.Physics.OperatorRPABlockZornKreinFlow.kreinBogoliubovU
    (Real.cosh (lam * τ)) (Real.sinh (lam * τ))

/-- `kreinHyperbolicFlow lam τ` is Krein-unitary with inverse at `-τ` and preserves
`externalFockParity`. -/
theorem kreinHyperbolicFlow_krein_unitary (lam τ : ℝ) :
    kreinHyperbolicFlow lam τ * kreinHyperbolicFlow lam (-τ) = 1 ∧
      kreinHyperbolicFlow lam (-τ) * kreinHyperbolicFlow lam τ = 1 ∧
      kreinHyperbolicFlow lam τ * (externalFockParity : Block2 ℝ) * kreinHyperbolicFlow lam τ =
        (externalFockParity : Block2 ℝ) := by
  have hcs : Real.cosh (lam * τ) * Real.sinh (lam * τ) =
      Real.sinh (lam * τ) * Real.cosh (lam * τ) := mul_comm _ _
  have hhyp : Real.cosh (lam * τ) * Real.cosh (lam * τ) -
      Real.sinh (lam * τ) * Real.sinh (lam * τ) = 1 := by
    simpa [pow_two] using Real.cosh_sq_sub_sinh_sq (lam * τ)
  have hneg : kreinHyperbolicFlow lam (-τ) =
      InfoGeometry.Physics.OperatorRPABlockZornKreinFlow.kreinBogoliubovU
        (Real.cosh (lam * τ)) (-Real.sinh (lam * τ)) := by
    simp [kreinHyperbolicFlow, mul_neg, Real.cosh_neg, Real.sinh_neg]
  rw [hneg]
  exact InfoGeometry.Physics.OperatorRPABlockZornKreinFlow.kreinBogoliubovU_krein_unitary
    (Real.cosh (lam * τ)) (Real.sinh (lam * τ)) hcs hhyp

/-- Exact Hadamard intertwining between `kreinHyperbolicFlow lam τ` and the Iwasawa split-torus
matrix `IwasawaRealKAN.aDiag (lam * τ)`. -/
theorem hadamard_kreinHyperbolicFlow_eq_two_aDiag (lam τ : ℝ) :
    blockHamiltonian (1 : ℝ) (-1) 1 1 * kreinHyperbolicFlow lam τ *
        blockHamiltonian (1 : ℝ) (-1) 1 1 =
      (2 : ℝ) • InfoGeometry.Algebra.IwasawaRealKAN.aDiag (lam * τ) := by
  have hplus : Real.cosh (lam * τ) + Real.sinh (lam * τ) = Real.exp (lam * τ) :=
    Real.cosh_add_sinh (lam * τ)
  have hminus : Real.cosh (lam * τ) - Real.sinh (lam * τ) = Real.exp (-(lam * τ)) :=
    Real.cosh_sub_sinh (lam * τ)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [kreinHyperbolicFlow,
      InfoGeometry.Physics.OperatorRPABlockZornKreinFlow.kreinBogoliubovU,
      blockHamiltonian, InfoGeometry.Algebra.IwasawaRealKAN.aDiag,
      Matrix.mul_apply, Fin.sum_univ_two]
  · linarith [hplus]
  · linarith [hminus]

/-- Connects the Hadamard-intertwined `aDiag (lam * τ)` diagonal readout directly to
`DilatonAndreevRenormalization`, `DilatonWeylAnomalyInflow`, and `IwasawaScaleParityBridge`. -/
theorem kreinHyperbolicFlow_dilaton_andreev_anomaly_bridge
    (x lam τ θ ξ phi t : ℝ) (hx : 0 < x) :
    (InfoGeometry.Algebra.IwasawaRealKAN.aDiag (lam * τ) 0 0 * x =
        InfoGeometry.OptimalTransport.DilatonAndreevRenormalization.hyperbolic_expansion x lam τ ∧
      InfoGeometry.Algebra.IwasawaRealKAN.aDiag (lam * τ) 0 0 * x =
        InfoGeometry.Physics.DilatonWeylAnomalyInflow.dilationFlow (lam * τ) x) ∧
      InfoGeometry.Algebra.IwasawaRealKAN.aDiag (lam * τ) 1 1 * x =
        InfoGeometry.OptimalTransport.DilatonAndreevRenormalization.andreev_contraction x lam τ ∧
      InfoGeometry.OptimalTransport.DilatonAndreevRenormalization.andreev_contraction
        (InfoGeometry.OptimalTransport.DilatonAndreevRenormalization.hyperbolic_expansion x lam τ)
        lam τ = x ∧
      HasDerivAt
        (fun s => InfoGeometry.OptimalTransport.DilatonAndreevRenormalization.hyperbolic_expansion
          x lam s)
        (InfoGeometry.OptimalTransport.DilatonAndreevRenormalization.dilaton_generator lam
          (InfoGeometry.OptimalTransport.DilatonAndreevRenormalization.hyperbolic_expansion
            x lam τ))
        τ ∧
      InfoGeometry.Physics.DilatonWeylAnomalyInflow.dilatonField
        (InfoGeometry.Physics.DilatonWeylAnomalyInflow.dilationFlow (lam * τ) x) =
        InfoGeometry.Physics.DilatonWeylAnomalyInflow.dilatonField x + lam * τ ∧
      InfoGeometry.Physics.DilatonWeylAnomalyInflow.weylDilatonMetric (phi + t) x x =
        Real.exp (2 * t) * InfoGeometry.Physics.DilatonWeylAnomalyInflow.weylDilatonMetric phi x x ∧
      InfoGeometry.Volume.RealUnitScaleParity.realUnitScaleParityEquiv
        (InfoGeometry.Volume.IwasawaScaleParityBridge.kanDetUnit θ (lam * τ) ξ) = 1 := by
  refine ⟨⟨?_, ?_⟩, ?_,
    InfoGeometry.OptimalTransport.DilatonAndreevRenormalization.unitarity_enforced_each_tick x lam τ,
    InfoGeometry.OptimalTransport.DilatonAndreevRenormalization.time_derivative_eats_dilaton x lam τ,
    InfoGeometry.Physics.DilatonWeylAnomalyInflow.dilaton_flow_additive (lam * τ) x hx,
    InfoGeometry.Physics.DilatonWeylAnomalyInflow.weylDilatonMetric_shift phi t x x,
    InfoGeometry.Volume.IwasawaScaleParityBridge.kan_scaleParity_trivial θ (lam * τ) ξ⟩
  · simp [InfoGeometry.Algebra.IwasawaRealKAN.aDiag,
      InfoGeometry.OptimalTransport.DilatonAndreevRenormalization.hyperbolic_expansion, mul_comm]
  · simp [InfoGeometry.Algebra.IwasawaRealKAN.aDiag,
      InfoGeometry.Physics.DilatonWeylAnomalyInflow.dilationFlow]
  · simp [InfoGeometry.Algebra.IwasawaRealKAN.aDiag,
      InfoGeometry.OptimalTransport.DilatonAndreevRenormalization.andreev_contraction, mul_comm]

/-- **R2 `[a, b]` Curvature Preservation Over Any Real Algebra**:
Conjugation of a signed RPA block `blockHamiltonian a (-a) b (-b)` by the hyperbolic
Krein-Bogoliubov flow `kreinBogoliubovU (algebraMap ℝ A (cosh (lam * τ))) (algebraMap ℝ A (sinh (lam * τ)))`
leaves `M_RPA^2`, the commutator defect `a * b - b * a`, and the chiral sheet curvature
`(a - b) * (a + b) - (a + b) * (a - b) = (2 : ℝ) • (a * b - b * a)` strictly invariant,
and forbids TDA decoupling `b' = 0` whenever `a * b ≠ b * a`. -/
theorem kreinHyperbolicFlow_preserves_rpa_curvature
    {A : Type*} [Ring A] [Algebra ℝ A] (a b : A) (lam τ : ℝ) :
    let c : A := algebraMap ℝ A (Real.cosh (lam * τ))
    let s : A := algebraMap ℝ A (Real.sinh (lam * τ))
    let a' := (c * c + s * s) * a - (2 : ℕ) • (c * s * b)
    let b' := (c * c + s * s) * b - (2 : ℕ) • (c * s * a)
    (InfoGeometry.Physics.OperatorRPABlockZornKreinFlow.kreinBogoliubovU c s *
        blockHamiltonian a (-a) b (-b) *
        InfoGeometry.Physics.OperatorRPABlockZornKreinFlow.kreinBogoliubovU c (-s)) =
      blockHamiltonian a' (-a') b' (-b') ∧
      (InfoGeometry.Physics.OperatorRPABlockZornKreinFlow.kreinBogoliubovU c s *
        blockHamiltonian a (-a) b (-b) *
        InfoGeometry.Physics.OperatorRPABlockZornKreinFlow.kreinBogoliubovU c (-s)) *
      (InfoGeometry.Physics.OperatorRPABlockZornKreinFlow.kreinBogoliubovU c s *
        blockHamiltonian a (-a) b (-b) *
        InfoGeometry.Physics.OperatorRPABlockZornKreinFlow.kreinBogoliubovU c (-s)) =
        blockHamiltonian a (-a) b (-b) * blockHamiltonian a (-a) b (-b) ∧
      a' * b' - b' * a' = a * b - b * a ∧
      (a' - b') * (a' + b') - (a' + b') * (a' - b') = (2 : ℝ) • (a * b - b * a) ∧
      (a * b ≠ b * a → b' ≠ 0) := by
  intro c s a' b'
  have hcs : c * s = s * c := Algebra.commutes _ _
  have hca : c * a = a * c := Algebra.commutes _ _
  have hcb : c * b = b * c := Algebra.commutes _ _
  have hsa : s * a = a * s := Algebra.commutes _ _
  have hsb : s * b = b * s := Algebra.commutes _ _
  have hhypR : Real.cosh (lam * τ) * Real.cosh (lam * τ) -
      Real.sinh (lam * τ) * Real.sinh (lam * τ) = 1 := by
    simpa [pow_two] using Real.cosh_sq_sub_sinh_sq (lam * τ)
  have hhyp : c * c - s * s = 1 := by
    dsimp [c, s]
    rw [← map_mul, ← map_mul, ← map_sub, hhypR, map_one]
  have hinv :=
    InfoGeometry.Physics.OperatorRPABlockZornKreinFlow.kreinBogoliubovU_rpa_flow_and_curvature_invariance
      a b c s hcs hca hcb hsa hsb
  have h2 := hinv.2.2 hhyp
  refine ⟨hinv.1, h2.1, h2.2.1, ?_, ?_⟩
  · rw [InfoGeometry.Physics.OperatorRPABlock.chiral_rpa_sheet_curvature_eq_two_comm, h2.2.1]
  · intro hne hb0
    exact hne (h2.2.2 hb0)

/-- Instantiates `kreinHyperbolicFlow_preserves_rpa_curvature` on the concrete 4×4 CAR carrier `M4R`
via `NuclearFiveGradeSameCarrierClosure.pair_rpa_square_defect_is_grade_zero_cartan`: the
flowed commutator `a' * b' - b' * a'` remains equal to the nonzero grade-zero Cartan
`gradingOperator`, and `b' ≠ 0` for every `(lam, τ)`. -/
theorem kreinHyperbolicFlow_preserves_car_grade_zero_defect (lam τ : ℝ) :
    let a : M4R := InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.pairCreation
    let b : M4R := InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.pairAnnihilation
    let c : M4R := algebraMap ℝ M4R (Real.cosh (lam * τ))
    let s : M4R := algebraMap ℝ M4R (Real.sinh (lam * τ))
    let a' := (c * c + s * s) * a - (2 : ℕ) • (c * s * b)
    let b' := (c * c + s * s) * b - (2 : ℕ) • (c * s * a)
    a' * b' - b' * a' =
        InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.gradingOperator ∧
      InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.gradingOperator ≠ 0 ∧
      b' ≠ 0 := by
  intro a b c s a' b'
  have hpair :=
    InfoGeometry.Physics.NuclearFiveGradeSameCarrierClosure.pair_rpa_square_defect_is_grade_zero_cartan
  have hcomm : a * b - b * a =
      InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.gradingOperator := by
    have h01 := hpair.1
    rw [InfoGeometry.Physics.OperatorRPABlock.rpa_square] at h01
    exact h01
  have hne : a * b ≠ b * a := by
    intro heq
    apply hpair.2
    rw [← hcomm, heq, sub_self]
  have hflow := kreinHyperbolicFlow_preserves_rpa_curvature a b lam τ
  refine ⟨?_, hpair.2, hflow.2.2.2.2 hne⟩
  rw [hflow.2.2.1, hcomm]

/-- Explicit R2 boundary theorem contrasting commutation-induced cancellation in Iwasawa RG
(`[scale, unipotent] = 0`) and Krein-Feshbach fixed points (`[P, H] = 0`) against preserved
noncommutative RPA curvature defects (`[a, b] ≠ 0`). -/
theorem iwasawa_commutation_vs_rpa_defect_separation
    {R : Type*} [Ring R]
    (Ops : InfoGeometry.Integration.IwasawaTimeRenormalization.RenormalizationData R)
    (hIwasawa : (Ops.scale : R) * Ops.unipotent = Ops.unipotent * (Ops.scale : R))
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [InfoGeometry.Krein.KreinSpace V]
    (P H Kres : V →L[ℝ] V) (hP : P * P = P) (hPH : P * H = H * P)
    (hQR : (1 - P) * Kres = Kres)
    {A : Type*} [Ring A] [Algebra ℝ A] (a b : A) (hab : a * b ≠ b * a) (lam τ : ℝ) :
    InfoGeometry.Integration.IwasawaTimeRenormalization.normalizedStep Ops = Ops.unipotent ∧
      (InfoGeometry.Canonical.BogoliubovRGFlowBridge.schurCorrection P H Kres = 0 ∧
        InfoGeometry.Physics.NuclearRealKreinFeshbach.effectiveHamiltonian P H Kres = P * H * P) ∧
      ((blockHamiltonian a (-a) b (-b) * blockHamiltonian a (-a) b (-b)) 0 1 ≠ 0 ∧
        (let c : A := algebraMap ℝ A (Real.cosh (lam * τ));
         let s : A := algebraMap ℝ A (Real.sinh (lam * τ));
         let a' := (c * c + s * s) * a - (2 : ℕ) • (c * s * b);
         let b' := (c * c + s * s) * b - (2 : ℕ) • (c * s * a);
         a' * b' - b' * a' ≠ 0 ∧
           (a' - b') * (a' + b') - (a' + b') * (a' - b') ≠ 0 ∧
           b' ≠ 0)) := by
  have hflow := kreinHyperbolicFlow_preserves_rpa_curvature a b lam τ
  have hsub : a * b - b * a ≠ 0 := sub_ne_zero.mpr hab
  refine ⟨InfoGeometry.Integration.IwasawaTimeRenormalization.normalizedStep_eq_unipotent
      Ops hIwasawa,
    InfoGeometry.Canonical.BogoliubovRGFlowBridge.schurCorrection_zero_of_commute
      P H Kres hP hPH hQR,
    InfoGeometry.Physics.OperatorRPABlock.rpa_square_offDiagonal_ne_zero_of_not_commute a b hab,
    ?_⟩
  intro c s a' b'
  refine ⟨?_, ?_, hflow.2.2.2.2 hab⟩
  · rw [hflow.2.2.1]
    exact hsub
  · rw [hflow.2.2.2.1]
    intro hzero
    exact hab ((InfoGeometry.Physics.OperatorRPABlock.chiral_rpa_sheet_difference_eq_zero_iff a b).mp
      (sub_eq_zero.mp (by
        rw [InfoGeometry.Physics.OperatorRPABlock.chiral_rpa_sheet_curvature_eq_two_comm]
        exact hzero))).eq

end KreinHyperbolicDilatonAndRPA

/-! ## 4. Discrete Feshbach / Schur / Krein Reduction ↔ Bogoliubov RG & Callan-Harvey Inflow -/

section FeshbachSchurBogoliubovRG

open scoped ComplexOrder

/-- Linear Feshbach reduction (`NuclearFeshbachReduction`) coincides definitionally with
`NuclearOperatorSchurComplement.effectiveOperator` and governs exact eigenvalue equivalence
and eigenvector reconstruction. -/
theorem feshbach_schur_kernel_eigen_bridge
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (P H R : Module.End K V) (E : K)
    (hP : P * P = P)
    (hQR : (1 - P) * R = R) (hRQ : R * (1 - P) = R)
    (hDR : InfoGeometry.Physics.NuclearFeshbachReduction.denominator P H E * R = 1 - P)
    (hRD : R * InfoGeometry.Physics.NuclearFeshbachReduction.denominator P H E = 1 - P)
    (v : V) (hv : P v = v) (ψ : V) (hψ : H ψ = E • ψ)
    (A B C Kres : V →ₗ[K] V) :
    (H (InfoGeometry.Physics.NuclearFeshbachReduction.waveOperator P H R v) =
        E • InfoGeometry.Physics.NuclearFeshbachReduction.waveOperator P H R v ↔
        InfoGeometry.Physics.NuclearFeshbachReduction.effectiveHamiltonian P H R v = E • v) ∧
      InfoGeometry.Physics.NuclearFeshbachReduction.waveOperator P H R (P ψ) = ψ ∧
      A - B.comp (Kres.comp C) =
        InfoGeometry.Physics.NuclearOperatorSchurComplement.effectiveOperator A B C Kres :=
  ⟨InfoGeometry.Physics.NuclearFeshbachReduction.eigen_equation_iff P H R E hQR hDR v hv,
    InfoGeometry.Physics.NuclearFeshbachReduction.reconstruct_eigenvector P H R E hP hRQ hRD ψ hψ,
    InfoGeometry.Physics.NuclearFeshbachReduction.effective_eq_existing A B C Kres⟩

/-- Connects Schur reflection symmetry, finite nilpotent soul resolvents, positive-definite
Feshbach dressing metrics, and parity intertwining for effective multipole transitions. -/
theorem schur_multipole_dressing_bridge
    {Alg : Type*} [Ring Alg] [StarRing Alg]
    (S : InfoGeometry.Physics.NuclearFiniteNilpotentSoul.FiniteSoul Alg) (E0 V W : Alg)
    {i f a b q : Type*} [Fintype i] [Fintype f] [Fintype a] [Fintype b] [Fintype q]
    [DecidableEq i]
    (C : Matrix q i ℂ) (K : Matrix q q ℂ)
    (Ωi : Matrix a i ℂ) (Ωf : Matrix b f ℂ) (O : Matrix b a ℂ)
    (parityInitial : Matrix a a ℂ) (parityFinal : Matrix b b ℂ)
    (reducedParityInitial : Matrix i i ℂ) (reducedParityFinal : Matrix f f ℂ)
    (hf : parityFinal.IsHermitian) (hfr : reducedParityFinal.IsHermitian)
    (hiΩ : parityInitial * Ωi = Ωi * reducedParityInitial)
    (hfΩ : parityFinal * Ωf = Ωf * reducedParityFinal)
    (hO : parityFinal * O = O * parityInitial) :
    InfoGeometry.Physics.NuclearOperatorSchurComplement.effectiveOperator E0 (-V) (-W)
        (InfoGeometry.Physics.NuclearOperatorSchurComplement.soulResolvent S).inv =
        InfoGeometry.Physics.NuclearOperatorSchurComplement.effectiveOperator E0 V W
          (InfoGeometry.Physics.NuclearOperatorSchurComplement.soulResolvent S).inv ∧
      ((InfoGeometry.Physics.NuclearOperatorSchurComplement.soulResolvent S).inv *
          (InfoGeometry.Physics.NuclearOperatorSchurComplement.soulResolvent S).denom = 1 ∧
        (InfoGeometry.Physics.NuclearOperatorSchurComplement.soulResolvent S).denom *
          (InfoGeometry.Physics.NuclearOperatorSchurComplement.soulResolvent S).inv = 1 ∧
        InfoGeometry.Physics.NuclearOperatorSchurComplement.soulEffectiveOperator S E0 (-V) (-W) =
          InfoGeometry.Physics.NuclearOperatorSchurComplement.soulEffectiveOperator S E0 V W) ∧
      (InfoGeometry.Physics.NuclearEffectiveMultipole.normMetric
        (InfoGeometry.Physics.NuclearEffectiveMultipole.feshbachDressing C K)).PosDef ∧
      reducedParityFinal *
          InfoGeometry.Physics.NuclearEffectiveMultipole.effectiveTransition Ωi Ωf O =
        InfoGeometry.Physics.NuclearEffectiveMultipole.effectiveTransition Ωi Ωf O *
          reducedParityInitial :=
  ⟨InfoGeometry.Physics.NuclearOperatorSchurComplement.effectiveOperator_reflection_resolvent
      (InfoGeometry.Physics.NuclearOperatorSchurComplement.soulResolvent S) E0 V W,
    InfoGeometry.Physics.NuclearOperatorSchurComplement.soul_schur_packet S E0 V W,
    InfoGeometry.Physics.NuclearEffectiveMultipole.feshbach_normMetric_posDef C K,
    InfoGeometry.Physics.NuclearEffectiveMultipole.effective_parity_intertwining
      Ωi Ωf O parityInitial parityFinal reducedParityInitial reducedParityFinal
      hf hfr hiΩ hfΩ hO⟩

/-- Connects doubled three-configuration Krein reduction (`NuclearThreeConfigurationKreinReduction`)
and Callan-Harvey anomaly inflow (`DilatonWeylAnomalyInflow`). -/
theorem three_config_krein_and_callan_harvey_bridge
    (a c g E ell : ℝ) (hE : E ≠ c) (h_ell : 0 < ell)
    (x : InfoGeometry.Physics.NuclearThreeConfigurationKreinReduction.DoubledModelSpace)
    {H_space : Type*} [NormedAddCommGroup H_space] [InnerProductSpace ℝ H_space]
    (CH : InfoGeometry.Physics.DilatonWeylAnomalyInflow.CallanHarveyInflow H_space)
    (A : H_space →ₗ[ℝ] H_space)
    (h_adjoint : InfoGeometry.Physics.LorentzBoostKreinConfinement.IsKreinSelfAdjoint CH.K A)
    (v : H_space) (lam1 lam2 : ℝ) (h_diff : lam1 ≠ lam2)
    (h_eigen1 : A v = lam1 • v) (h_eigen2 : CH.K.J (A v) = lam2 • CH.K.J v) :
    (InfoGeometry.Physics.NuclearRealKreinFeshbach.denominator
        InfoGeometry.Physics.NuclearThreeConfigurationDual.doubledProjection
        (InfoGeometry.Physics.NuclearThreeConfigurationDual.doubledHamiltonian a c g) E *
        InfoGeometry.Physics.NuclearThreeConfigurationKreinReduction.doubledResolvent c E =
          1 - InfoGeometry.Physics.NuclearThreeConfigurationDual.doubledProjection ∧
        InfoGeometry.Physics.NuclearThreeConfigurationKreinReduction.doubledResolvent c E *
        InfoGeometry.Physics.NuclearRealKreinFeshbach.denominator
        InfoGeometry.Physics.NuclearThreeConfigurationDual.doubledProjection
        (InfoGeometry.Physics.NuclearThreeConfigurationDual.doubledHamiltonian a c g) E =
          1 - InfoGeometry.Physics.NuclearThreeConfigurationDual.doubledProjection) ∧
      InfoGeometry.Krein.KreinSpace.IsKreinSelfAdjoint
        (InfoGeometry.Physics.NuclearRealKreinFeshbach.effectiveHamiltonian
          InfoGeometry.Physics.NuclearThreeConfigurationDual.doubledProjection
          (InfoGeometry.Physics.NuclearThreeConfigurationDual.doubledHamiltonian a c g)
          (InfoGeometry.Physics.NuclearThreeConfigurationKreinReduction.doubledResolvent c E)) ∧
      (InfoGeometry.Physics.NuclearThreeConfigurationDual.doubledHamiltonian a c g
          (InfoGeometry.Physics.NuclearThreeConfigurationKreinReduction.doubledGraphMap c g E x) =
          E • InfoGeometry.Physics.NuclearThreeConfigurationKreinReduction.doubledGraphMap c g E x ↔
        InfoGeometry.Physics.NuclearThreeConfigurationKreinReduction.doubledReducedHamiltonian a c g E x =
          E • x) ∧
      CH.bulkInflowCurrent = CH.seamAnomalyCurrent ∧
      InfoGeometry.Physics.DilatonWeylAnomalyInflow.seamNoetherCharge CH v = 0 ∧
      0 < InfoGeometry.Physics.DilatonWeylAnomalyInflow.selbergHyperbolicWeight ell :=
  ⟨InfoGeometry.Physics.NuclearThreeConfigurationKreinReduction.doubled_corner_inverse a c g E hE,
    InfoGeometry.Physics.NuclearThreeConfigurationKreinReduction.doubled_effectiveHamiltonian_kreinSelfAdjoint
      a c g E hE,
    InfoGeometry.Physics.NuclearThreeConfigurationKreinReduction.doubledGraphMap_eigen_equation_iff
      a c g E hE x,
    InfoGeometry.Physics.DilatonWeylAnomalyInflow.anomaly_inflow_conservation CH,
    InfoGeometry.Physics.DilatonWeylAnomalyInflow.broken_pt_charge_collapse
      CH A h_adjoint v lam1 lam2 h_diff h_eigen1 h_eigen2,
    InfoGeometry.Physics.DilatonWeylAnomalyInflow.selberg_hyperbolic_weight_pos ell h_ell⟩

/-- Connects nested Krein-Feshbach Schur transitivity (`NuclearRealKreinFeshbach`) and the
concrete indefinite `(2, 1)` Pontryagin-Krein witness with `BogoliubovRGFlowBridge` decimation
and explicit two-level BdG resolvents. -/
theorem nested_krein_feshbach_bogoliubov_rg_bridge
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (B : InfoGeometry.Canonical.BogoliubovRGFlowBridge.Bridge E)
    (hEq : B.metriplecticFlow.IsDissipativeEquilibrium)
    (P₀ P₁ R₁ R₀₁ :
      InfoGeometry.Krein.DoubledSpace E →L[ℝ] InfoGeometry.Krein.DoubledSpace E)
    (E0 : ℝ)
    (hP0 : P₀ * P₀ = P₀) (hP1 : P₁ * P₁ = P₁)
    (hP0_sa : InfoGeometry.Krein.KreinSpace.kreinAdjoint P₀ = P₀)
    (hP1_sa : InfoGeometry.Krein.KreinSpace.kreinAdjoint P₁ = P₁)
    (hK_sa : InfoGeometry.Krein.KreinSpace.kreinAdjoint B.reduction.Kambient = B.reduction.Kambient)
    (h_nest : P₀ * P₁ = P₀)
    (hSub : P₁ * B.reduction.Preg = P₁) (hSubR : B.reduction.Preg * P₁ = P₁)
    (hQR1 : (1 - P₁) * R₁ = R₁)
    (hDR1 : InfoGeometry.Physics.NuclearRealKreinFeshbach.denominator P₁ B.reduction.Kambient E0 *
      R₁ = 1 - P₁)
    (hSR01 : InfoGeometry.Physics.NuclearRealKreinFeshbach.intermediateShell P₀ P₁ * R₀₁ = R₀₁)
    (hDR01 : InfoGeometry.Physics.NuclearRealKreinFeshbach.intermediateDenominator P₀ P₁
      (InfoGeometry.Physics.NuclearRealKreinFeshbach.effectiveHamiltonian P₁ B.reduction.Kambient R₁)
      E0 * R₀₁ = InfoGeometry.Physics.NuclearRealKreinFeshbach.intermediateShell P₀ P₁)
    {ξ Δ : ℝ} (hgap : 0 < InfoGeometry.Physics.NuclearBdGTwoLevelExact.bdgEnergy ξ Δ) :
    B.metriplecticFlow.totalFlow =
        InfoGeometry.Canonical.BogoliubovOptimalTransport.canonicalBogoliubovFlow B.reduction B.time ∧
      (let K_01 := InfoGeometry.Physics.NuclearRealKreinFeshbach.effectiveHamiltonian P₀
          (InfoGeometry.Physics.NuclearRealKreinFeshbach.effectiveHamiltonian P₁
            B.reduction.Kambient R₁) R₀₁;
        InfoGeometry.Physics.NuclearRealKreinFeshbach.effectiveHamiltonian P₀ B.reduction.Kambient
            (InfoGeometry.Physics.NuclearRealKreinFeshbach.nestedResolvent
              B.reduction.Kambient R₁ R₀₁) = K_01 ∧
          InfoGeometry.Physics.NuclearRealKreinFeshbach.waveOperator P₁ B.reduction.Kambient R₁ *
            InfoGeometry.Physics.NuclearRealKreinFeshbach.waveOperator P₀
              (InfoGeometry.Physics.NuclearRealKreinFeshbach.effectiveHamiltonian P₁
                B.reduction.Kambient R₁) R₀₁ =
            InfoGeometry.Physics.NuclearRealKreinFeshbach.waveOperator P₀ B.reduction.Kambient
              (InfoGeometry.Physics.NuclearRealKreinFeshbach.nestedResolvent
                B.reduction.Kambient R₁ R₀₁) ∧
          InfoGeometry.Krein.KreinSpace.IsKreinSelfAdjoint K_01 ∧
          (P₀ * K_01 = K_01 ∧ K_01 * P₀ = K_01) ∧
          (B.reduction.Preg * K_01 = K_01 ∧ K_01 * B.reduction.Preg = K_01) ∧
          (B.reduction.Pzero * K_01 = 0 ∧ K_01 * B.reduction.Pzero = 0) ∧
          InfoGeometry.Canonical.BogoliubovOptimalTransport.IsOptimalBogoliubovFlow B.reduction
            (fun t => NormedSpace.exp (t • K_01)) ∧
          ∀ t : ℝ, (1 - P₀) * NormedSpace.exp (t • K_01) = 1 - P₀) ∧
      ((-InfoGeometry.Physics.NuclearBdGTwoLevelExact.bdgBlock ξ Δ) *
          InfoGeometry.Canonical.BogoliubovRGFlowBridge.bdgExplicitResolvent ξ Δ 0 = 1 ∧
        InfoGeometry.Canonical.BogoliubovRGFlowBridge.bdgExplicitResolvent ξ Δ 0 =
          -((ξ ^ 2 + Δ ^ 2)⁻¹ • InfoGeometry.Physics.NuclearBdGTwoLevelExact.bdgBlock ξ Δ)) := by
  have hnested :=
    InfoGeometry.Canonical.BogoliubovRGFlowBridge.nested_decimated_Kambient_transitive
      B P₀ P₁ R₁ R₀₁ E0 hP0 hP1 hP0_sa hP1_sa hK_sa h_nest hSub hSubR hQR1 hDR1 hSR01 hDR01
  have h_nestR := InfoGeometry.Physics.NuclearRealKreinFeshbach.nested_mul_right
    P₀ P₁ hP0_sa hP1_sa h_nest
  have hR01S := InfoGeometry.Physics.NuclearRealKreinFeshbach.intermediateResolvent_mul_shell
    P₀ P₁ B.reduction.Kambient R₁ R₀₁ E0 hP0_sa hP1_sa hK_sa hQR1 hDR1 hSR01 hDR01
  have hwave :=
    InfoGeometry.Physics.NuclearRealKreinFeshbach.waveOperator_schur_comp
      P₀ P₁ B.reduction.Kambient R₁ R₀₁ hP1 h_nest h_nestR hSR01 hR01S
  refine ⟨B.rg_fixed_point_is_pure_bogoliubov_flow hEq,
    ?_,
    InfoGeometry.Canonical.BogoliubovRGFlowBridge.bdg_zero_energy_resolvent hgap⟩
  intro K_01
  exact ⟨hnested.1, hwave, hnested.2.1, hnested.2.2.1, hnested.2.2.2.1,
    hnested.2.2.2.2.1, hnested.2.2.2.2.2.1, hnested.2.2.2.2.2.2⟩

/-- Re-exports the non-vacuous indefinite `(2, 1)` Pontryagin-Krein nested Schur witness from
`NuclearRealKreinFeshbach`. -/
theorem indefinite_krein21_nested_decimation_witness
    (a b c v g₁ g₂ E : ℝ) (hE1 : E ≠ b) (hE01 : E ≠ c - g₂ ^ 2 / (E - b)) :
    ∃ P₀ P₁ H R₁ R₀₁ :
      InfoGeometry.Physics.NuclearRealKreinFeshbach.E21 →L[ℝ]
        InfoGeometry.Physics.NuclearRealKreinFeshbach.E21,
      let H₁ := InfoGeometry.Physics.NuclearRealKreinFeshbach.effectiveHamiltonian P₁ H R₁
      InfoGeometry.Physics.NuclearRealKreinFeshbach.effectiveHamiltonian P₀ H
          (InfoGeometry.Physics.NuclearRealKreinFeshbach.nestedResolvent H R₁ R₀₁) =
        InfoGeometry.Physics.NuclearRealKreinFeshbach.effectiveHamiltonian P₀ H₁ R₀₁ ∧
      InfoGeometry.Krein.KreinSpace.IsKreinSelfAdjoint H₁ ∧
      InfoGeometry.Krein.KreinSpace.IsKreinSelfAdjoint
        (InfoGeometry.Physics.NuclearRealKreinFeshbach.effectiveHamiltonian P₀ H₁ R₀₁) := by
  have hw :=
    InfoGeometry.Physics.NuclearRealKreinFeshbach.indefinite_krein21_nested_witness
      a b c v g₁ g₂ E hE1 hE01
  exact ⟨_, _, _, _, _, hw.2.2.2.2.1.1, hw.2.2.2.2.1.2.1, hw.2.2.2.2.1.2.2.2⟩

end FeshbachSchurBogoliubovRG

/-! ## 5. Conditional Continuum RG & Spectral-Gap Termination (`Type*` + `T17` Witnesses) -/

section ConditionalContinuumHypotheses

/-- Hypothesis-parameterized `Type` bundle modeling a continuum renormalization flow
compatible with discrete RG sampling `discreteStep n = flow (n * dt)` and the dilaton
generator differential equation `d/dτ flow(τ) = lam * flow(τ)`. -/
structure ContinuumRGFlowHypothesis : Type where
  lam : ℝ
  x0 : ℝ
  flow : ℝ → ℝ
  discreteStep : ℕ → ℝ
  dt : ℝ
  dt_pos : 0 < dt
  flow_zero : flow 0 = x0
  flow_hasDerivAt : ∀ τ : ℝ,
    HasDerivAt flow
      (InfoGeometry.OptimalTransport.DilatonAndreevRenormalization.dilaton_generator lam (flow τ))
      τ
  discreteStep_samples : ∀ n : ℕ, discreteStep n = flow ((n : ℝ) * dt)

/-- Hypothesis-parameterized `Type*` bundle modeling spectral-gap termination for Krein-Feshbach
RG elimination: the complementary resolvent satisfies `‖R‖ ≤ g⁻¹` (`0 < g`), the off-diagonal
shell couplings satisfy `≤ ε`, and the gap suppression ratio `ε^2 / g` is bounded by `δ`. -/
structure SpectralGapTerminationHypothesis
    (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [InfoGeometry.Krein.KreinSpace V] : Type _ where
  P₀ : V →L[ℝ] V
  H : V →L[ℝ] V
  R : V →L[ℝ] V
  g : ℝ
  ε : ℝ
  δ : ℝ
  hg : 0 < g
  hδ : 0 < δ
  hR : ‖R‖ ≤ g⁻¹
  h1 : ‖P₀ * H * (1 - P₀)‖ ≤ ε
  h2 : ‖(1 - P₀) * H * P₀‖ ≤ ε
  hQR : (1 - P₀) * R = R
  hRQ : R * (1 - P₀) = R
  hgap_threshold : ε ^ 2 / g ≤ δ

/-- Zero-argument constructive witness (`T17`) for `ContinuumRGFlowHypothesis` using the
exact dilaton-Andreev hyperbolic expansion flow. -/
def canonicalContinuumRGFlowHypothesis : ContinuumRGFlowHypothesis where
  lam := 1
  x0 := 1
  flow := fun τ =>
    InfoGeometry.OptimalTransport.DilatonAndreevRenormalization.hyperbolic_expansion 1 1 τ
  discreteStep := fun n =>
    InfoGeometry.OptimalTransport.DilatonAndreevRenormalization.hyperbolic_expansion 1 1 (n : ℝ)
  dt := 1
  dt_pos := by norm_num
  flow_zero := by
    simp [InfoGeometry.OptimalTransport.DilatonAndreevRenormalization.hyperbolic_expansion]
  flow_hasDerivAt := fun τ =>
    InfoGeometry.OptimalTransport.DilatonAndreevRenormalization.time_derivative_eats_dilaton 1 1 τ
  discreteStep_samples := fun n => by
    simp

/-- Zero-argument constructive witness (`T17`) for `SpectralGapTerminationHypothesis` on the
native Krein doubled space `InfoGeometry.Krein.DoubledSpace ℝ`. -/
def canonicalSpectralGapTerminationHypothesis :
    SpectralGapTerminationHypothesis (InfoGeometry.Krein.DoubledSpace ℝ) where
  P₀ := 1
  H := 1
  R := 0
  g := 1
  ε := 0
  δ := 1
  hg := by norm_num
  hδ := by norm_num
  hR := by norm_num
  h1 := by simp
  h2 := by simp
  hQR := by simp
  hRQ := by simp
  hgap_threshold := by norm_num

/-- At `τ = 0`, any `ContinuumRGFlowHypothesis` has derivative `lam * x0`. -/
theorem continuum_rg_flow_zero_deriv (C : ContinuumRGFlowHypothesis) :
    HasDerivAt C.flow (C.lam * C.x0) 0 := by
  have hd := C.flow_hasDerivAt 0
  simpa [InfoGeometry.OptimalTransport.DilatonAndreevRenormalization.dilaton_generator,
    C.flow_zero] using hd

/-- At every discrete RG step `n * dt`, the continuum derivative equals `lam * discreteStep n`. -/
theorem continuum_rg_flow_discrete_step_deriv (C : ContinuumRGFlowHypothesis) (n : ℕ) :
    HasDerivAt C.flow (C.lam * C.discreteStep n) ((n : ℝ) * C.dt) := by
  have hd := C.flow_hasDerivAt ((n : ℝ) * C.dt)
  simpa [InfoGeometry.OptimalTransport.DilatonAndreevRenormalization.dilaton_generator,
    C.discreteStep_samples n] using hd

/-- Exponential realization of `ContinuumRGFlowHypothesis` via `DilatonAndreevRenormalization`
matching the Hadamard-intertwined `kreinHyperbolicFlow` diagonal `(0, 0)` sector. -/
theorem continuum_rg_flow_exponential_realization (x0 lam dt : ℝ) (hdt : 0 < dt) :
    let C : ContinuumRGFlowHypothesis := {
      lam := lam
      x0 := x0
      flow := fun τ =>
        InfoGeometry.OptimalTransport.DilatonAndreevRenormalization.hyperbolic_expansion x0 lam τ
      discreteStep := fun n =>
        InfoGeometry.OptimalTransport.DilatonAndreevRenormalization.hyperbolic_expansion
          x0 lam ((n : ℝ) * dt)
      dt := dt
      dt_pos := hdt
      flow_zero := by
        simp [InfoGeometry.OptimalTransport.DilatonAndreevRenormalization.hyperbolic_expansion]
      flow_hasDerivAt := fun τ =>
        InfoGeometry.OptimalTransport.DilatonAndreevRenormalization.time_derivative_eats_dilaton
          x0 lam τ
      discreteStep_samples := fun _ => rfl }
    ∀ τ : ℝ,
      C.flow τ = InfoGeometry.Algebra.IwasawaRealKAN.aDiag (lam * τ) 0 0 * x0 ∧
        InfoGeometry.OptimalTransport.DilatonAndreevRenormalization.andreev_contraction
          (C.flow τ) lam τ = x0 ∧
        HasDerivAt C.flow (C.lam * C.x0) 0 := by
  intro C τ
  refine ⟨?_,
    InfoGeometry.OptimalTransport.DilatonAndreevRenormalization.unitarity_enforced_each_tick
      x0 lam τ,
    continuum_rg_flow_zero_deriv C⟩
  simp [C, InfoGeometry.Algebra.IwasawaRealKAN.aDiag,
    InfoGeometry.OptimalTransport.DilatonAndreevRenormalization.hyperbolic_expansion, mul_comm]

/-- Conditional spectral-gap termination bound: under `SpectralGapTerminationHypothesis`,
the Schur correction is bounded by `S.δ`. -/
theorem spectral_gap_termination_schur_bound
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [InfoGeometry.Krein.KreinSpace V]
    (S : SpectralGapTerminationHypothesis V) :
    ‖InfoGeometry.Physics.NuclearRealKreinFeshbach.effectiveHamiltonian S.P₀ S.H S.R -
        S.P₀ * S.H * S.P₀‖ ≤ S.δ :=
  le_trans
    (InfoGeometry.Canonical.BogoliubovRGFlowBridge.schur_gap_suppression_bound
      S.P₀ S.H S.R S.hg S.hR S.h1 S.h2 S.hQR S.hRQ)
    S.hgap_threshold

/-- Conditional exact RG fixed-point collapse under `SpectralGapTerminationHypothesis` when
`P₀` is an idempotent commuting with `H`. -/
theorem spectral_gap_termination_commuting_exact
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [InfoGeometry.Krein.KreinSpace V]
    (S : SpectralGapTerminationHypothesis V)
    (hP : S.P₀ * S.P₀ = S.P₀) (hComm : S.P₀ * S.H = S.H * S.P₀) :
    InfoGeometry.Canonical.BogoliubovRGFlowBridge.schurCorrection S.P₀ S.H S.R = 0 ∧
      InfoGeometry.Physics.NuclearRealKreinFeshbach.effectiveHamiltonian S.P₀ S.H S.R =
        S.P₀ * S.H * S.P₀ :=
  InfoGeometry.Canonical.BogoliubovRGFlowBridge.schurCorrection_zero_of_commute
    S.P₀ S.H S.R hP hComm S.hQR

/-- Top-level Seam D synthesis theorem uniting:
1. Finite-matrix RPA obstruction vs infinite Fock RPA witness,
2. Lifted `RenormalizationData` & non-commuting `IwasawaRealKAN` witness (`normalizedStep`),
3. Hadamard intertwining of `kreinHyperbolicFlow` with `IwasawaRealKAN.aDiag` and
   `DilatonAndreevRenormalization`,
4. Preservation of noncommutative `[a, b]` RPA defects under `kreinHyperbolicFlow`,
5. Conditional `ContinuumRGFlowHypothesis` and `SpectralGapTerminationHypothesis` consequences. -/
theorem feshbach_rpa_schur_renormalization_flow_synthesis
    (R2 : InfoGeometry.Nuclear.NuclearPhononRPAAlgebra.QuasibosonRPADatum)
    {n : ℕ} (hn : 0 < n)
    (Rn : InfoGeometry.Nuclear.NuclearPhononRPAAlgebra.QuasibosonRPADatumN ℝ n)
    (lam τ ξ : ℝ)
    {A : Type*} [Ring A] [Algebra ℝ A] (a b : A) (hab : a * b ≠ b * a)
    (C : ContinuumRGFlowHypothesis)
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [InfoGeometry.Krein.KreinSpace V]
    (S : SpectralGapTerminationHypothesis V) :
    (R2.defect ≠ 0 ∧ Rn.defect ≠ 0 ∧
      IsEmpty (InfoGeometry.Physics.NuclearPhononRPA.PhononRPA (Fin 2)
        (Matrix (Fin n) (Fin n) ℝ))) ∧
      (InfoGeometry.Integration.IwasawaTimeRenormalization.normalizedStep
          (noncommKanRenormalizationData lam ξ) =
        InfoGeometry.Algebra.IwasawaRealKAN.nShear (Real.exp (2 * lam) * ξ)) ∧
      (blockHamiltonian (1 : ℝ) (-1) 1 1 * kreinHyperbolicFlow lam τ *
          blockHamiltonian (1 : ℝ) (-1) 1 1 =
        (2 : ℝ) • InfoGeometry.Algebra.IwasawaRealKAN.aDiag (lam * τ)) ∧
      (let c : A := algebraMap ℝ A (Real.cosh (lam * τ));
       let s : A := algebraMap ℝ A (Real.sinh (lam * τ));
       let a' := (c * c + s * s) * a - (2 : ℕ) • (c * s * b);
       let b' := (c * c + s * s) * b - (2 : ℕ) • (c * s * a);
       a' * b' - b' * a' = a * b - b * a ∧ b' ≠ 0) ∧
      HasDerivAt C.flow (C.lam * C.x0) 0 ∧
      ‖InfoGeometry.Physics.NuclearRealKreinFeshbach.effectiveHamiltonian S.P₀ S.H S.R -
        S.P₀ * S.H * S.P₀‖ ≤ S.δ := by
  have hflow := kreinHyperbolicFlow_preserves_rpa_curvature a b lam τ
  refine ⟨⟨R2.defect_ne_zero,
      InfoGeometry.Nuclear.NuclearPhononRPAAlgebra.QuasibosonRPADatumN.defect_ne_zero hn Rn,
      InfoGeometry.Physics.NuclearPhononRPA.no_finite_matrix_phononRPA n hn⟩,
    noncommKanRenormalizationData_normalizedStep lam ξ,
    hadamard_kreinHyperbolicFlow_eq_two_aDiag lam τ,
    ⟨hflow.2.2.1, hflow.2.2.2.2 hab⟩,
    continuum_rg_flow_zero_deriv C,
    spectral_gap_termination_schur_bound S⟩

end ConditionalContinuumHypotheses

end

end InfoGeometry.Synthesis.FeshbachRPASchurRenormalizationFlow
