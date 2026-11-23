/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.LeibnizDerivationFrechetOnsagerCapstone
import InfoGeometry.Algebra.MatrixNoncommutativity
import InfoGeometry.OperatorAlgebra.FiniteMatrixNoncommutativeWitness
import InfoGeometry.Canonical.ModularSuperchargeClosure
import InfoGeometry.Modular.Noncommutative
import InfoGeometry.Algebra.ZornMatrix
import Mathlib.Algebra.Polynomial.Derivative

/-!
# End-to-End Verification Suite: Unified Leibniz–Derivation–Fréchet–Onsager Framework

Implements independent, opaque-box, noncommutative concrete witness and boundary checks
across Tiers 1–4 (`TEST_INFRA.md` checks `T1-F1-01..T1-F8-05`, `T2-F1-01..T2-F8-05`,
`T3-AB-01..T3-AC-02`, and `T4-SC-01..T4-SC-05`), paired with
`LeibnizDerivationFrechetOnsagerE2ETestsAudit.lean` (`#print axioms`).

## Hygiene
- Starts at byte 0 with the exact 5-line Apache 2.0 copyright header.
- Zero `sorry`, `admit`, custom axioms, `native_decide`, `unsafe`, or `partial`.
- Zero global `instance` declarations and zero global `open scoped` overrides
  (`Matrix.Norms.L2Operator` and `LieRing.ofAssociativeRing` /
  `LieAlgebra.ofAssociativeAlgebra` are strictly section-local).
- Uses the global `NormedAlgebra.restrictScalars ℝ ℂ (FiniteOperatorAlgebra 2)` instance
  without adding any competing `Algebra.ofModule` instance.
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 300000
set_option maxHeartbeats 1200000

noncomputable section

namespace InfoGeometry.Canonical.LeibnizDerivationFrechetOnsagerE2ETests

open InfoGeometry.Core
open InfoGeometry.Algebra
open InfoGeometry.Algebra.MatrixNoncommutativity
open InfoGeometry.Algebra.NonAssocDerivation
open InfoGeometry.OperatorAlgebra
open InfoGeometry.OperatorAlgebra.FiniteMatrixNoncommutativeWitness
open InfoGeometry.OperatorAlgebra.DerivationDifferentialForms
open InfoGeometry.OperatorAlgebra.ComplexBoundedOperators
open InfoGeometry.OperatorAlgebra.ComplexBoundedOperators.CblinfunMatrix
open InfoGeometry.OperatorAlgebra.PeirceSpine
open InfoGeometry.OperatorAlgebra.PeirceSpine.ArchetypeCausalSynthesis
open InfoGeometry.Optics.OperatorDerivationForms
open InfoGeometry.Thermo
open InfoGeometry.Thermo.OnsagerClosure
open InfoGeometry.Thermo.OnsagerClosure.OnsagerCasimirSystem
open InfoGeometry.Thermo.OnsagerFormsBridge
open InfoGeometry.SuperMetriplectic
open InfoGeometry.SuperMetriplectic.CartanBridge
open InfoGeometry.SuperMetriplectic.CartanOnsagerParityBridge
open InfoGeometry.SuperMetriplectic.PeirceCutCartanDerivationBridge
open InfoGeometry.Krein (DoubledSpace)
open InfoGeometry.Canonical
open InfoGeometry.Canonical.OperatorFrechetForms
open InfoGeometry.Canonical.OperatorFrechetDerivationJet
open InfoGeometry.Canonical.PeirceFrechetOperatorArchetypes
open InfoGeometry.Canonical.CEOneFormNOperatorBridge
open InfoGeometry.Canonical.CEBKMOnsagerSystem
open InfoGeometry.Canonical.CEBKMOnsagerGibbsIntegration
open InfoGeometry.Canonical.CEBKMOnsagerGibbsNOperatorFamily
open InfoGeometry.Canonical.CEBKMParityUnificationBridge
open InfoGeometry.Canonical.BKMMetriplecticTrajectorySecondLaw
open InfoGeometry.Canonical.BKMScalarGaugeQuotient
open InfoGeometry.Canonical.ModularDerivationLaneBridge
open InfoGeometry.Canonical.ExceptionalZornSuperBraidedDerivationBridge
open InfoGeometry.Canonical.NoncommutativeGibbsExpectationBridge
open InfoGeometry.Canonical.NoncommutativeGibbsFaithfulNormalizationBridge
open InfoGeometry.Canonical.FiniteSelfAdjointGibbsStateBridge
open InfoGeometry.Canonical.NoncommutativeGibbsCenteredBKMCovariance
open InfoGeometry.Canonical.NoncommutativeGibbsBKMHessianBridge
open InfoGeometry.Canonical.BKMOnsagerMobilityBridge
open InfoGeometry.Canonical.LeibnizDerivationFrechetOnsagerCapstone
open InfoGeometry.Canonical.ErlangenOperator2 (ErlangenOperatorDatum HasJReciprocity)
open SouriauOnsagerBKM

/-! ## Section 0: Shared Concrete Noncommutative Witness Kit -/

section SharedWitnessKit

def A_swap : FiniteOperatorAlgebra 2 :=
  matrixOp (swapMatrix : Matrix (Fin 2) (Fin 2) ℂ)

def B_tilt : FiniteOperatorAlgebra 2 :=
  matrixOp (tiltedMatrix : Matrix (Fin 2) (Fin 2) ℂ)

def P_d63 : PeirceCut 2 := d63FrechetOperatorCut

def P_diag_mat : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, 0]

def P_diag : PeirceCut 2 :=
  ⟨matrixOp P_diag_mat, by
    apply matrixOfOp_injective
    change matrixOfOp ((matrixOp P_diag_mat).comp (matrixOp P_diag_mat)) = matrixOfOp (matrixOp P_diag_mat)
    rw [matrixOfOp_comp, matrixOfOp_matrixOp]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [P_diag_mat, Matrix.mul_apply, Fin.sum_univ_two]⟩

def H_d63 : FiniteOperatorAlgebra 2 := matrixOp d63TiltedAmplitude

def Q_odd : FiniteOperatorAlgebra 2 := Complex.I • A_swap

def K1_real : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; -1, 0]
def K2_real : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, -1]

theorem hK12_real_noncomm : K1_real * K2_real ≠ K2_real * K1_real := by
  intro h
  have hm := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 1) h
  norm_num [K1_real, K2_real, Matrix.mul_apply, Fin.sum_univ_two] at hm

private lemma matrixOfOp_sub_eq {n : ℕ} (S T : FiniteOperatorAlgebra n) :
    matrixOfOp (S - T) = matrixOfOp S - matrixOfOp T := by
  unfold matrixOfOp
  exact (LinearMap.toMatrix (ketBasis (Fin n)) (ketBasis (Fin n))).map_sub
    S.toLinearMap T.toLinearMap

private lemma matrixOfOp_neg_eq {n : ℕ} (T : FiniteOperatorAlgebra n) :
    matrixOfOp (-T) = -matrixOfOp T := by
  unfold matrixOfOp
  exact (LinearMap.toMatrix (ketBasis (Fin n)) (ketBasis (Fin n))).map_neg T.toLinearMap

private lemma matrixOfOp_mul_eq {n : ℕ} (S T : FiniteOperatorAlgebra n) :
    matrixOfOp (S * T) = matrixOfOp S * matrixOfOp T :=
  matrixOfOp_comp S T

private lemma matrixOfOp_one_eq {n : ℕ} :
    matrixOfOp (1 : FiniteOperatorAlgebra n) = 1 :=
  matrixOfOp_id

theorem hA_swap_sa : IsSelfAdjoint A_swap := by
  rw [isSelfAdjoint_iff]
  apply matrixOfOp_injective
  change matrixOfOp (ContinuousLinearMap.adjoint (matrixOp (swapMatrix : Matrix (Fin 2) (Fin 2) ℂ))) = _
  rw [matrixOfOp_adjoint, matrixOfOp_matrixOp]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [A_swap, swapMatrix]

theorem hB_tilt_sa : IsSelfAdjoint B_tilt := by
  rw [isSelfAdjoint_iff]
  apply matrixOfOp_injective
  change matrixOfOp (ContinuousLinearMap.adjoint (matrixOp (tiltedMatrix : Matrix (Fin 2) (Fin 2) ℂ))) = _
  rw [matrixOfOp_adjoint, matrixOfOp_matrixOp]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [B_tilt, tiltedMatrix]

theorem hH_d63_sa : IsSelfAdjoint H_d63 := by
  rw [isSelfAdjoint_iff]
  apply matrixOfOp_injective
  change matrixOfOp (ContinuousLinearMap.adjoint (matrixOp d63TiltedAmplitude)) = _
  rw [matrixOfOp_adjoint, matrixOfOp_matrixOp]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [H_d63, d63TiltedAmplitude]

theorem hZ_d63_pos : 0 < gibbsPartitionReal H_d63 :=
  tracedExponential_re_pos_of_isSelfAdjoint H_d63 hH_d63_sa

theorem hQ_odd_anti : star Q_odd = -Q_odd := by
  rw [Q_odd, star_smul, Complex.star_def, Complex.conj_I, hA_swap_sa.star_eq]
  exact neg_smul Complex.I A_swap

theorem hMat2C_noncomm_witness :
    ∃ M1 M2 : Matrix (Fin 2) (Fin 2) ℂ, M1 * M2 ≠ M2 * M1 :=
  ⟨swapMatrix, tiltedMatrix, swapMatrix_mul_tiltedMatrix_ne (A := ℂ)⟩

theorem hMat2Ext_noncomm_witness :
    ∃ M1 M2 : Matrix (Fin 2) (Fin 2) (ExteriorAlgebra ℝ (Fin 3 → ℝ)), M1 * M2 ≠ M2 * M1 := by
  refine ⟨!![0, 1; 0, 0], !![0, 0; 1, 0], ?_⟩
  intro h
  have hm := congrArg (fun M : Matrix (Fin 2) (Fin 2) (ExteriorAlgebra ℝ (Fin 3 → ℝ)) => M 0 0) h
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, mul_zero, add_zero, zero_add, one_mul] at hm
  exact one_ne_zero hm

theorem hMat3C_noncomm_witness :
    ∃ M1 M2 : Matrix (Fin 3) (Fin 3) ℂ, M1 * M2 ≠ M2 * M1 := by
  refine ⟨!![0, 0, 1; 0, 0, 0; 0, 0, 0], !![0, 0, 0; 0, 0, 0; 1, 0, 0], ?_⟩
  intro h
  have hm := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℂ => M 0 0) h
  norm_num [Matrix.mul_apply, Fin.sum_univ_three] at hm

theorem hAB_noncomm : A_swap * B_tilt ≠ B_tilt * A_swap := by
  intro h
  have hm := congrArg matrixOfOp h
  rw [matrixOfOp_mul_eq, matrixOfOp_mul_eq, A_swap, B_tilt, matrixOfOp_matrixOp,
    matrixOfOp_matrixOp] at hm
  exact (swapMatrix_mul_tiltedMatrix_ne (A := ℂ)) hm

theorem hHA_noncomm : H_d63 * A_swap ≠ A_swap * H_d63 := by
  intro h
  have hm := congrArg (fun T => matrixOfOp T 0 1) h
  rw [matrixOfOp_mul_eq, matrixOfOp_mul_eq, H_d63, A_swap, matrixOfOp_matrixOp,
    matrixOfOp_matrixOp] at hm
  norm_num [d63TiltedAmplitude, swapMatrix, Matrix.mul_apply, Fin.sum_univ_two] at hm

theorem hP_diag_P_d63_noncomm : P_diag.1 * P_d63.1 ≠ P_d63.1 * P_diag.1 := by
  intro h
  have hm := congrArg (fun T => matrixOfOp T 0 1) h
  change (matrixOfOp (P_diag.1.comp P_d63.1)) 0 1 =
    (matrixOfOp (P_d63.1.comp P_diag.1)) 0 1 at hm
  rw [matrixOfOp_comp, matrixOfOp_comp] at hm
  have hP1 : matrixOfOp P_diag.1 = P_diag_mat := matrixOfOp_matrixOp _
  have hP2 : matrixOfOp P_d63.1 = d63TiltedProjection := matrixOfOp_matrixOp _
  rw [hP1, hP2] at hm
  norm_num [P_diag_mat, d63TiltedProjection, Matrix.mul_apply, Fin.sum_univ_two] at hm

/-- Non-diagonal real rank-1 projection `!![1/2, 1/2; 1/2, 1/2]` on `EuclideanSpace ℝ (Fin 2)`. -/
def P_real2_mat : Matrix (Fin 2) (Fin 2) ℝ := !![1 / 2, 1 / 2; 1 / 2, 1 / 2]

def P_real2 : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2) :=
  P_real2_mat.toEuclideanLin.toContinuousLinearMap

theorem P_real2_apply (x : EuclideanSpace ℝ (Fin 2)) :
    P_real2 x = WithLp.toLp 2 ![((1 / 2 : ℝ) * (x 0 + x 1)), ((1 / 2 : ℝ) * (x 0 + x 1))] := by
  ext i
  fin_cases i <;>
    simp [P_real2, P_real2_mat, Matrix.toEuclideanLin, Matrix.mulVec, dotProduct,
      Fin.sum_univ_two] <;> ring

theorem P_real2_idem : P_real2 * P_real2 = P_real2 := by
  ext x i
  change P_real2 (P_real2 x) i = P_real2 x i
  rw [P_real2_apply, P_real2_apply]
  fin_cases i <;> simp <;> ring

theorem P_real2_selfAdjoint : star P_real2 = P_real2 := by
  apply ContinuousLinearMap.coe_injective
  change P_real2.adjoint.toLinearMap = P_real2.toLinearMap
  have hconj : P_real2_mat.conjTranspose = P_real2_mat := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [P_real2_mat]
  have hadj := P_real2_mat.toEuclideanLin_conjTranspose_eq_adjoint
  rw [hconj] at hadj
  exact hadj.symm

def CIK_real2 : InfoGeometry.Canonical.CertifiedInverseKernel (EuclideanSpace ℝ (Fin 2)) where
  A := P_real2
  A_D := P_real2
  A_MP := P_real2
  drazinIndex := 1
  hDrazin := InfoGeometry.Canonical.Drazin.IsDrazinInverse.of_idempotent P_real2_idem
  hMoorePenrose := InfoGeometry.Canonical.MoorePenrose.IsMoorePenroseInverse.mk
    (by rw [P_real2_idem, P_real2_idem])
    (by rw [P_real2_idem, P_real2_idem])
    (by rw [P_real2_idem]; exact P_real2_selfAdjoint)
    (by rw [P_real2_idem]; exact P_real2_selfAdjoint)

def B_real2 : DrazinCartanOnsagerBridge (E := EuclideanSpace ℝ (Fin 2)) := ⟨CIK_real2⟩

def tilt_real2 : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2) :=
  (!![1, 0; 0, -1] : Matrix (Fin 2) (Fin 2) ℝ).toEuclideanLin.toContinuousLinearMap

/-- Non-singular `ScalarSchurDrazinBlock` (`effectiveEvenOnsager = 3`, `drazinDefectProjector = 0`). -/
def B_ns : ScalarSchurDrazinBlock where
  LPP := 5
  LPΘ := 2
  LΘP := 2
  LΘΘ := 2
  penrose := ⟨2, 1 / 2, by norm_num, by norm_num⟩
  drazin := ⟨2, 1 / 2, 0, by norm_num, by norm_num, by norm_num⟩
  penrose_matches_hidden := rfl
  drazin_matches_hidden := rfl

/-- Singular hidden-block `ScalarSchurDrazinBlock` (`LΘΘ = 0`, `index = 1`, `drazinDefectProjector = 1`). -/
def B_sing : ScalarSchurDrazinBlock where
  LPP := 4
  LPΘ := 3
  LΘP := 3
  LΘΘ := 0
  penrose := ⟨0, 0, by norm_num, by norm_num⟩
  drazin := ⟨0, 0, 1, by norm_num, by norm_num, by norm_num⟩
  penrose_matches_hidden := rfl
  drazin_matches_hidden := rfl

/-- Saturated Schur-complement `ScalarSchurDrazinBlock` (`effectiveEvenOnsager = 0`). -/
def B_sat : ScalarSchurDrazinBlock where
  LPP := 2
  LPΘ := 2
  LΘP := 2
  LΘΘ := 2
  penrose := ⟨2, 1 / 2, by norm_num, by norm_num⟩
  drazin := ⟨2, 1 / 2, 0, by norm_num, by norm_num, by norm_num⟩
  penrose_matches_hidden := rfl
  drazin_matches_hidden := rfl

def triad_pos : DrazinPenroseSchurTriad where
  block := B_ns
  entropy := ⟨2, 3, 12, by norm_num [B_ns, ScalarSchurDrazinBlock.effectiveEvenOnsager], by norm_num⟩
  entropy_uses_effective_block := by norm_num [B_ns, ScalarSchurDrazinBlock.effectiveEvenOnsager]

def triad_sat : DrazinPenroseSchurTriad where
  block := B_sat
  entropy := ⟨5, 0, 0, by norm_num, by norm_num⟩
  entropy_uses_effective_block := by norm_num [B_sat, ScalarSchurDrazinBlock.effectiveEvenOnsager]

def triad_zero : DrazinPenroseSchurTriad where
  block := B_ns
  entropy := ⟨0, 3, 0, by norm_num, by norm_num⟩
  entropy_uses_effective_block := by norm_num [B_ns, ScalarSchurDrazinBlock.effectiveEvenOnsager]

def M_tkk : TKKOnsagerMatrix where
  entry i j := match i, j with
    | .minus, .minus => 2
    | .zero, .zero => 3
    | .plus, .plus => 2
    | .minus, .plus => 1
    | .plus, .minus => 1
    | _, _ => 0
  reciprocal i j := by cases i <;> cases j <;> rfl

theorem M_tkk_psd (v : InfoGeometry.SuperMetriplectic.TKKGrade → ℝ) :
    0 ≤ tkkSum (fun i => tkkSum (fun j => v i * M_tkk.entry i j * v j)) := by
  simp only [tkkSum, M_tkk]
  nlinarith [sq_nonneg (v .minus + v .plus), sq_nonneg (v .minus),
    sq_nonneg (v .plus), sq_nonneg (v .zero)]

theorem M_tkk_dual (i j : InfoGeometry.SuperMetriplectic.TKKGrade) :
    M_tkk.entry i.dual j.dual = M_tkk.entry i j := by
  cases i <;> cases j <;> rfl

def conformalBlock_nc : ConformalOnsagerBlock (FiniteOperatorAlgebra 2) where
  Pmu := matrixOp !![0, 1; 0, 0]
  Kmu := matrixOp !![0, 0; 1, 0]
  D := (1 / 2 : ℝ) • matrixOp !![1, 0; 0, -1]
  Mmunu := 0
  covariancePK := 2
  souriauCocyclePK := 1
  reversiblePK := 3
  totalPK := 6
  dilationMoment := 3 / 2
  lorentzMoment := 0
  eta := 1
  weylWeightP := 0
  weylWeightK := 0
  bracket_P_K_eq := by
    apply matrixOfOp_injective
    dsimp [AssociativeSuperBracket.commutator, AssociativeSuperBracket.superBracket,
      SuperAnomaly.paritySign]
    rw [matrixOfOp_sub_eq, one_smul, matrixOfOp_mul_eq, matrixOfOp_mul_eq, sub_zero,
      one_smul, two_smul, matrixOfOp_add, matrixOfOp_real_smul,
      matrixOfOp_matrixOp, matrixOfOp_matrixOp, matrixOfOp_matrixOp]
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.mul_apply, Fin.sum_univ_two]
  reversiblePK_eq_dilation_lorentz_moment := by norm_num
  totalPK_eq_reversible_plus_covariance_plus_cocycle := by norm_num

end SharedWitnessKit

/-! ## Section 1: Tier 1 & Tier 2 — Gap A (`F1`, `F2`, `F3`) -/

section GapA_Tests

attribute [local instance 100] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

private theorem invS_P_d63_eq_A_swap :
    invS (P_d63 : FiniteOperatorAlgebra 2) = A_swap := by
  apply matrixOfOp_injective
  rw [invS_eq_two_smul_sub_one, matrixOfOp_sub_eq, matrixOfOp_real_smul, matrixOfOp_one_eq,
    show matrixOfOp P_d63.1 = d63TiltedProjection from matrixOfOp_matrixOp _,
    A_swap, matrixOfOp_matrixOp]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [d63TiltedProjection, swapMatrix]

private theorem matrixOfOp_d63_P_minus_B_tilt :
    matrixOfOp ((peirceSymmetricLieAlgebra P_d63).P_minus B_tilt) = !![1 / 2, 0; 0, -1 / 2] := by
  change matrixOfOp (((2 : ℝ)⁻¹) • (B_tilt - invS P_d63.1 * B_tilt * invS P_d63.1)) = _
  rw [invS_P_d63_eq_A_swap, matrixOfOp_real_smul, matrixOfOp_sub_eq,
    matrixOfOp_mul_eq, matrixOfOp_mul_eq, A_swap, B_tilt, matrixOfOp_matrixOp,
    matrixOfOp_matrixOp]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [tiltedMatrix, swapMatrix, Matrix.mul_apply, Fin.sum_univ_two]

private theorem matrixOfOp_d63_P_plus_B_tilt :
    matrixOfOp ((peirceSymmetricLieAlgebra P_d63).P_plus B_tilt) = !![1 / 2, 1; 1, 1 / 2] := by
  change matrixOfOp (((2 : ℝ)⁻¹) • (B_tilt + invS P_d63.1 * B_tilt * invS P_d63.1)) = _
  rw [invS_P_d63_eq_A_swap, matrixOfOp_real_smul, matrixOfOp_add,
    matrixOfOp_mul_eq, matrixOfOp_mul_eq, A_swap, B_tilt, matrixOfOp_matrixOp,
    matrixOfOp_matrixOp]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [tiltedMatrix, swapMatrix, Matrix.mul_apply, Fin.sum_univ_two]

private theorem peirce_d63_P_minus_B_tilt_ne :
    (peirceSymmetricLieAlgebra P_d63).P_minus B_tilt ≠ 0 := by
  intro h0
  have hm := congrArg (fun Z : FiniteOperatorAlgebra 2 => matrixOfOp Z 0 0) h0
  rw [matrixOfOp_d63_P_minus_B_tilt, matrixOfOp_zero, Matrix.zero_apply] at hm
  norm_num at hm

private theorem peirce_d63_P_plus_B_tilt_ne :
    (peirceSymmetricLieAlgebra P_d63).P_plus B_tilt ≠ 0 := by
  intro h0
  have hm := congrArg (fun Z : FiniteOperatorAlgebra 2 => matrixOfOp Z 0 1) h0
  rw [matrixOfOp_d63_P_plus_B_tilt, matrixOfOp_zero, Matrix.zero_apply] at hm
  norm_num at hm

/-- `T1-F1-01`: `cartanTimeReversal` realizes `TimeReversal` with `𝔭` `+1` and `𝔨` `-1` on nonzero witnesses. -/
theorem t1_f1_01_cartanTimeReversal :
    let C := peirceCartanOnsagerSplit P_d63
    let T := cartanTimeReversal C
    let x_p := C.S.P_minus B_tilt
    let x_k := C.S.P_plus B_tilt
    T.op (T.op B_tilt) = B_tilt ∧
      T.op x_p = x_p ∧ T.op x_k = -x_k ∧
      x_p ≠ 0 ∧ x_k ≠ 0 := by
  intro C T x_p x_k
  have hp_mem : x_p ∈ C.dissipativeRange := by
    rw [C.dissipativeRange_eq_p]
    exact C.S.minusPart_mem_odd B_tilt
  have hk_mem : x_k ∈ C.drazinCore := by
    rw [C.drazinCore_eq_k]
    exact C.S.plusPart_mem_even B_tilt
  exact ⟨T.involutive B_tilt,
    cartanTimeReversal_eq_self_of_mem_dissipativeRange C hp_mem,
    cartanTimeReversal_eq_neg_of_mem_drazinCore C hk_mem,
    peirce_d63_P_minus_B_tilt_ne, peirce_d63_P_plus_B_tilt_ne⟩

/-- `T1-F1-02`: `cartanInvolutionTimeReversal` realizes `TimeReversal` with `𝔨` `+1` and `𝔭` `-1`. -/
theorem t1_f1_02_cartanInvolutionTimeReversal :
    let C := peirceCartanOnsagerSplit P_d63
    let T' := cartanInvolutionTimeReversal C
    let x_k := C.S.P_plus B_tilt
    let x_p := C.S.P_minus B_tilt
    T'.op (T'.op B_tilt) = B_tilt ∧
      T'.op x_k = x_k ∧ T'.op x_p = -x_p := by
  intro C T' x_k x_p
  have hk_mem : x_k ∈ C.drazinCore := by
    rw [C.drazinCore_eq_k]
    exact C.S.plusPart_mem_even B_tilt
  have hp_mem : x_p ∈ C.dissipativeRange := by
    rw [C.dissipativeRange_eq_p]
    exact C.S.minusPart_mem_odd B_tilt
  exact ⟨T'.involutive B_tilt,
    cartanInvolutionTimeReversal_eq_self_of_mem_drazinCore C hk_mem,
    cartanInvolutionTimeReversal_eq_neg_of_mem_dissipativeRange C hp_mem⟩

/-- `T1-F1-03`: `CartanOnsagerSplit` constructs `ParityOnsagerSystem` with non-zero dissipation and skew coupling. -/
theorem t1_f1_03_cartanParityOnsagerSystem :
    let C := peirceCartanOnsagerSplit P_d63
    let P_sys := cartanParityOnsagerSystemOfForms C (hsRealBilinForm 2)
      (hsRealBilinForm_symm 2) (hsRealBilinForm_nonneg 2) (hsProbeBilinForm 2 tiltOp2)
    let x_p := C.S.P_minus B_tilt
    let x_k := C.S.P_plus B_tilt
    P_sys.T = cartanTimeReversal C ∧
      0 < P_sys.dissipative x_p x_p ∧
      P_sys.reversible x_k x_p ≠ 0 ∧
      P_sys.dissipative (P_sys.T.op x_k) (P_sys.T.op x_p) = P_sys.dissipative x_k x_p ∧
      P_sys.reversible (P_sys.T.op x_k) (P_sys.T.op x_p) = -P_sys.reversible x_k x_p := by
  intro C P_sys x_p x_k
  have hxp_mem : x_p ∈ C.S.𝔭 := C.S.minusPart_mem_odd B_tilt
  have hxk_mem : x_k ∈ C.S.𝔨 := C.S.plusPart_mem_even B_tilt
  have hxp_idem : C.S.P_minus x_p = x_p := by
    have h := (C.S.mem_oddSubmodule_iff).mp hxp_mem
    change ((2 : ℝ)⁻¹) • (x_p - C.S.θ x_p) = x_p
    rw [h, sub_neg_eq_add, ← two_smul ℝ x_p, smul_smul]
    norm_num
  have hdiss_pos : 0 < P_sys.dissipative x_p x_p := by
    change 0 < hsRealBilinForm 2 (C.S.P_minus x_p) (C.S.P_minus x_p)
    rw [hxp_idem, hsRealBilinForm_apply]
    exact lt_of_le_of_ne (finiteOperatorTrace_star_mul_self_re_nonneg x_p) (Ne.symm (by
      intro h0
      exact peirce_d63_P_minus_B_tilt_ne
        ((finiteOperatorTrace_star_mul_self_re_eq_zero_iff x_p).mp h0)))
  have hxk_plus : C.S.P_plus x_k = x_k := by
    have h := (C.S.mem_evenSubmodule_iff).mp hxk_mem
    change ((2 : ℝ)⁻¹) • (x_k + C.S.θ x_k) = x_k
    rw [h, ← two_smul ℝ x_k, smul_smul]
    norm_num
  have hxk_minus : C.S.P_minus x_k = 0 := by
    have h := (C.S.mem_evenSubmodule_iff).mp hxk_mem
    change ((2 : ℝ)⁻¹) • (x_k - C.S.θ x_k) = 0
    rw [h, sub_self, smul_zero]
  have hxp_plus : C.S.P_plus x_p = 0 := by
    have h := (C.S.mem_oddSubmodule_iff).mp hxp_mem
    change ((2 : ℝ)⁻¹) • (x_p + C.S.θ x_p) = 0
    rw [h, add_neg_cancel, smul_zero]
  have hrev_ne : P_sys.reversible x_k x_p ≠ 0 := by
    change hsProbeBilinForm 2 tiltOp2 (C.S.P_plus x_k) (C.S.P_minus x_p) -
        hsProbeBilinForm 2 tiltOp2 (C.S.P_plus x_p) (C.S.P_minus x_k) ≠ 0
    rw [hxk_plus, hxp_idem, hxp_plus, hxk_minus, map_zero]
    change hsProbeBilinForm 2 tiltOp2 x_k x_p - (0 : FiniteOperatorAlgebra 2 →ₗ[ℝ] ℝ) x_k ≠ 0
    rw [LinearMap.zero_apply, sub_zero, hsProbeBilinForm_apply]
    have hval : (finiteOperatorTrace (star (tiltOp2 * x_k) * x_p)).re = (1 / 2 : ℝ) := by
      dsimp only [x_k, x_p, C, peirceCartanOnsagerSplit]
      change (Matrix.trace (matrixOfOp (star (tiltOp2 * (peirceSymmetricLieAlgebra P_d63).P_plus B_tilt) *
        (peirceSymmetricLieAlgebra P_d63).P_minus B_tilt))).re = 1 / 2
      have hmat : matrixOfOp (star (tiltOp2 * (peirceSymmetricLieAlgebra P_d63).P_plus B_tilt) *
          (peirceSymmetricLieAlgebra P_d63).P_minus B_tilt) =
          Matrix.conjTranspose (matrixOfOp tiltOp2 *
            matrixOfOp ((peirceSymmetricLieAlgebra P_d63).P_plus B_tilt)) *
            matrixOfOp ((peirceSymmetricLieAlgebra P_d63).P_minus B_tilt) := by
        rw [matrixOfOp_mul_eq]
        change matrixOfOp (ContinuousLinearMap.adjoint
          (tiltOp2 * (peirceSymmetricLieAlgebra P_d63).P_plus B_tilt)) * _ = _
        rw [matrixOfOp_adjoint, matrixOfOp_mul_eq]
      rw [hmat, matrixOfOp_d63_P_plus_B_tilt, matrixOfOp_d63_P_minus_B_tilt,
        tiltOp2, matrixOfOp_matrixOp]
      simp only [Matrix.trace, Matrix.diag, Fin.sum_univ_two, Matrix.mul_apply,
        Matrix.conjTranspose_apply, InfoGeometry.Physics.KleinBottleSewingExact.tilt2]
      norm_num
    intro h0
    linarith
  exact ⟨rfl, hdiss_pos, hrev_ne, P_sys.dissipative_T_even x_k x_p,
    P_sys.reversible_T_odd x_k x_p⟩

private theorem tilt_real2_apply (x : EuclideanSpace ℝ (Fin 2)) :
    tilt_real2 x = WithLp.toLp 2 ![x 0, -x 1] := by
  ext i
  fin_cases i <;>
    simp [tilt_real2, Matrix.toEuclideanLin, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

private theorem B_real2_GammaS_apply (x : EuclideanSpace ℝ (Fin 2)) :
    B_real2.CIK.GammaS x = WithLp.toLp 2 ![x 1, x 0] := by
  have hG : B_real2.CIK.GammaS = 2 * P_real2 - 1 := by
    rw [InfoGeometry.Canonical.CertifiedInverseKernel.GammaS_eq_two_mul_spectralProjector_sub_one]
    change 2 * (P_real2 * P_real2) - 1 = 2 * P_real2 - 1
    rw [P_real2_idem]
  rw [hG]
  have h2 : (2 * P_real2 - 1) x = (2 : ℝ) • P_real2 x - x := by
    rw [two_mul]
    ext j
    rw [two_smul]
    rfl
  rw [h2]
  ext i
  change (2 : ℝ) * P_real2 x i - x i = (WithLp.toLp 2 ![x 1, x 0]) i
  rw [P_real2_apply]
  fin_cases i <;> (simp; try ring)

private theorem tilt_real2_isSpectralNonCompact :
    B_real2.CIK.IsSpectralNonCompact tilt_real2 := by
  rw [InfoGeometry.Canonical.CertifiedInverseKernel.isSpectralNonCompact_iff_anticommute_GammaS]
  ext x i
  change tilt_real2 (B_real2.CIK.GammaS x) i = -(B_real2.CIK.GammaS (tilt_real2 x)) i
  rw [B_real2_GammaS_apply, tilt_real2_apply, tilt_real2_apply, B_real2_GammaS_apply]
  fin_cases i <;> simp

private def P_doubled_proj : DoubledSpace ℝ →L[ℝ] DoubledSpace ℝ :=
  (1 / 2 : ℝ) • (1 + InfoGeometry.Krein.modular_j (E := ℝ))

private theorem P_doubled_proj_idem : P_doubled_proj * P_doubled_proj = P_doubled_proj := by
  apply ContinuousLinearMap.ext
  intro v
  change P_doubled_proj (P_doubled_proj v) = P_doubled_proj v
  dsimp [P_doubled_proj]
  apply InfoGeometry.Krein.DoubledSpace.ext <;>
    simp [InfoGeometry.Krein.modular_j] <;> ring

private theorem P_doubled_proj_selfAdjoint : star P_doubled_proj = P_doubled_proj := by
  apply ContinuousLinearMap.coe_injective
  change (ContinuousLinearMap.adjoint P_doubled_proj).toLinearMap = P_doubled_proj.toLinearMap
  have hadj : ContinuousLinearMap.adjoint P_doubled_proj = P_doubled_proj := by
    symm
    refine (ContinuousLinearMap.eq_adjoint_iff (A := P_doubled_proj) (B := P_doubled_proj)).2 ?_
    intro u v
    simp [P_doubled_proj, InfoGeometry.Krein.modular_j_apply, WithLp.prod_inner_apply]
    ring
  rw [hadj]

private def CIK_doubled : InfoGeometry.Canonical.CertifiedInverseKernel (DoubledSpace ℝ) where
  A := P_doubled_proj
  A_D := P_doubled_proj
  A_MP := P_doubled_proj
  drazinIndex := 1
  hDrazin := InfoGeometry.Canonical.Drazin.IsDrazinInverse.of_idempotent P_doubled_proj_idem
  hMoorePenrose := InfoGeometry.Canonical.MoorePenrose.IsMoorePenroseInverse.mk
    (by rw [P_doubled_proj_idem, P_doubled_proj_idem])
    (by rw [P_doubled_proj_idem, P_doubled_proj_idem])
    (by rw [P_doubled_proj_idem]; exact P_doubled_proj_selfAdjoint)
    (by rw [P_doubled_proj_idem]; exact P_doubled_proj_selfAdjoint)

private def B_doubled : DrazinCartanOnsagerBridge (E := DoubledSpace ℝ) := ⟨CIK_doubled⟩

/-- `T1-F1-04`: `DrazinCartanOnsagerBridge` (`idCertifiedInverseKernel`, non-trivial `B_doubled`, and non-diagonal `B_real2`) bridges to `ParityOnsagerSystem` with non-zero dissipation, reversible coupling, and reciprocity. -/
theorem t1_f1_04_drazinCartanParityOnsagerSystem :
    let B_id : DrazinCartanOnsagerBridge (E := DoubledSpace ℝ) :=
      ⟨InfoGeometry.Canonical.ModularSuperchargeClosure.idCertifiedInverseKernel (E := ℝ)⟩
    let S_id := B_id.toCartanOnsagerSplit
    let S_2 := B_real2.toCartanOnsagerSplit
    let S_doubled := B_doubled.toCartanOnsagerSplit
    let v_id : DoubledSpace ℝ := InfoGeometry.Krein.to_doubled (1 : ℝ) 0
    let w_id : DoubledSpace ℝ := InfoGeometry.Krein.to_doubled (0 : ℝ) 1
    let η_doubled : LinearMap.BilinForm ℝ (DoubledSpace ℝ →L[ℝ] DoubledSpace ℝ) :=
      LinearMap.mk₂ ℝ
        (fun X Y : DoubledSpace ℝ →L[ℝ] DoubledSpace ℝ =>
          @inner ℝ (DoubledSpace ℝ) _ (X w_id) (Y v_id))
        (fun X₁ X₂ Y => by simp [inner_add_left])
        (fun r X Y => by simp [inner_smul_left])
        (fun X Y₁ Y₂ => by simp [inner_add_right])
        (fun r X Y => by simp [inner_smul_right])
    let P_doubled := drazinCartanParityOnsagerSystemOfProbe B_doubled v_id η_doubled
    let P_2 := drazinCartanParityOnsagerSystemOfProbe B_real2
      (EuclideanSpace.basisFun (Fin 2) ℝ 0)
      (operatorProbeBilin (EuclideanSpace.basisFun (Fin 2) ℝ 0))
    let J_op : DoubledSpace ℝ →L[ℝ] DoubledSpace ℝ := InfoGeometry.Krein.modular_j (E := ℝ)
    let ε_op : DoubledSpace ℝ →L[ℝ] DoubledSpace ℝ := InfoGeometry.Krein.spectral_epsilon (E := ℝ)
    S_id.drazinCore = S_id.S.𝔨 ∧ S_id.dissipativeRange = S_id.S.𝔭 ∧
      S_2.drazinCore = S_2.S.𝔨 ∧ S_2.dissipativeRange = S_2.S.𝔭 ∧
      (drazinCartanTimeReversal B_real2).op tilt_real2 = tilt_real2 ∧
      0 < P_2.dissipative tilt_real2 tilt_real2 ∧
      S_doubled.drazinCore = S_doubled.S.𝔨 ∧ S_doubled.dissipativeRange = S_doubled.S.𝔭 ∧
      0 < P_doubled.dissipative ε_op ε_op ∧
      P_doubled.reversible J_op ε_op ≠ 0 ∧
      P_doubled.totalGenerator (P_doubled.T.op J_op) (P_doubled.T.op ε_op) =
        P_doubled.totalGenerator ε_op J_op ∧
      P_doubled.totalGenerator ε_op J_op ≠ 0 ∧
      P_2.reversible P_real2 tilt_real2 ≠ 0 ∧
      P_2.totalGenerator (P_2.T.op tilt_real2) (P_2.T.op P_real2) =
        P_2.totalGenerator P_real2 tilt_real2 ∧
      P_2.totalGenerator P_real2 tilt_real2 ≠ 0 ∧
      P_2.totalGenerator (P_2.T.op tilt_real2) (P_2.T.op (tilt_real2 + P_real2)) =
        P_2.totalGenerator (tilt_real2 + P_real2) tilt_real2 ∧
      P_2.totalGenerator (tilt_real2 + P_real2) tilt_real2 ≠ 0 := by
  intro B_id S_id S_2 S_doubled v_id w_id η_doubled P_doubled P_2 J_op ε_op
  have hrev_self : (drazinCartanTimeReversal B_real2).op tilt_real2 = tilt_real2 :=
    drazinCartanTimeReversal_eq_self_of_isSpectralNonCompact B_real2 tilt_real2_isSpectralNonCompact
  have hmem_p : tilt_real2 ∈ S_2.S.𝔭 := by
    change tilt_real2 ∈ S_2.S.oddSubmodule
    rw [S_2.S.mem_oddSubmodule_iff]
    change B_real2.CIK.thetaS tilt_real2 = -tilt_real2
    have hneg := congrArg Neg.neg hrev_self
    change -(-(B_real2.CIK.thetaS tilt_real2)) = -tilt_real2 at hneg
    rwa [neg_neg] at hneg
  have hP_minus_tilt : S_2.S.P_minus tilt_real2 = tilt_real2 := by
    have h := (S_2.S.mem_oddSubmodule_iff).mp hmem_p
    change ((2 : ℝ)⁻¹) • (tilt_real2 - S_2.S.θ tilt_real2) = tilt_real2
    rw [h, sub_neg_eq_add, ← two_smul ℝ tilt_real2, smul_smul]
    norm_num
  have hP_plus_tilt : S_2.S.P_plus tilt_real2 = 0 := by
    have h := (S_2.S.mem_oddSubmodule_iff).mp hmem_p
    change ((2 : ℝ)⁻¹) • (tilt_real2 + S_2.S.θ tilt_real2) = 0
    rw [h, add_neg_cancel, smul_zero]
  have hP_real2_comm : P_real2 * B_real2.CIK.GammaS = B_real2.CIK.GammaS * P_real2 := by
    rw [InfoGeometry.Canonical.CertifiedInverseKernel.GammaS_eq_two_mul_spectralProjector_sub_one]
    change P_real2 * (2 * (P_real2 * P_real2) - 1) = (2 * (P_real2 * P_real2) - 1) * P_real2
    rw [P_real2_idem, mul_sub, sub_mul, mul_one, one_mul, two_mul, mul_add, add_mul, P_real2_idem]
  have hmem_k2 : P_real2 ∈ S_2.S.𝔨 := by
    change P_real2 ∈ S_2.S.evenSubmodule
    rw [S_2.S.mem_evenSubmodule_iff]
    change B_real2.CIK.GammaS * P_real2 * B_real2.CIK.GammaS = P_real2
    rw [← hP_real2_comm, mul_assoc, B_real2.CIK.GammaS_sq_eq_one, mul_one]
  have hP_plus_P_real2 : S_2.S.P_plus P_real2 = P_real2 := by
    have h := (S_2.S.mem_evenSubmodule_iff).mp hmem_k2
    change ((2 : ℝ)⁻¹) • (P_real2 + S_2.S.θ P_real2) = P_real2
    rw [h, ← two_smul ℝ P_real2, smul_smul]
    norm_num
  have hP_minus_P_real2 : S_2.S.P_minus P_real2 = 0 := by
    have h := (S_2.S.mem_evenSubmodule_iff).mp hmem_k2
    change ((2 : ℝ)⁻¹) • (P_real2 - S_2.S.θ P_real2) = 0
    rw [h, sub_self, smul_zero]
  have hdiss_pos : 0 < P_2.dissipative tilt_real2 tilt_real2 := by
    change 0 < operatorProbeBilin (EuclideanSpace.basisFun (Fin 2) ℝ 0)
      (S_2.S.P_minus tilt_real2) (S_2.S.P_minus tilt_real2)
    rw [hP_minus_tilt, operatorProbeBilin_apply]
    have he0 : tilt_real2 (EuclideanSpace.basisFun (Fin 2) ℝ 0) =
        EuclideanSpace.basisFun (Fin 2) ℝ 0 := by
      ext i
      rw [tilt_real2_apply]
      fin_cases i <;> simp
    rw [he0, real_inner_self_eq_norm_sq, norm_eq_sqrt_real_inner]
    simp only [OrthonormalBasis.inner_eq_ite, ↓reduceIte]
    norm_num
  have hdiss_val : P_2.dissipative tilt_real2 tilt_real2 = 1 := by
    change operatorProbeBilin (EuclideanSpace.basisFun (Fin 2) ℝ 0)
      (S_2.S.P_minus tilt_real2) (S_2.S.P_minus tilt_real2) = 1
    rw [hP_minus_tilt, operatorProbeBilin_apply]
    have he0 : tilt_real2 (EuclideanSpace.basisFun (Fin 2) ℝ 0) =
        EuclideanSpace.basisFun (Fin 2) ℝ 0 := by
      ext i
      rw [tilt_real2_apply]
      fin_cases i <;> simp
    rw [he0, real_inner_self_eq_norm_sq, norm_eq_sqrt_real_inner]
    simp only [OrthonormalBasis.inner_eq_ite, ↓reduceIte]
    norm_num
  have hrev2_val : P_2.reversible P_real2 tilt_real2 = 1 / 2 := by
    change operatorProbeBilin (EuclideanSpace.basisFun (Fin 2) ℝ 0)
        (S_2.S.P_plus P_real2) (S_2.S.P_minus tilt_real2) -
      operatorProbeBilin (EuclideanSpace.basisFun (Fin 2) ℝ 0)
        (S_2.S.P_plus tilt_real2) (S_2.S.P_minus P_real2) = 1 / 2
    simp only [hP_plus_P_real2, hP_minus_tilt, hP_plus_tilt, hP_minus_P_real2,
      _root_.map_zero, sub_zero, operatorProbeBilin_apply]
    have h0 : P_real2 (EuclideanSpace.basisFun (Fin 2) ℝ 0) =
        WithLp.toLp 2 ![1 / 2, 1 / 2] := by
      rw [P_real2_apply]
      ext i; fin_cases i <;> simp
    have h1 : tilt_real2 (EuclideanSpace.basisFun (Fin 2) ℝ 0) =
        WithLp.toLp 2 ![1, 0] := by
      rw [tilt_real2_apply]
      ext i; fin_cases i <;> simp
    rw [h0, h1, EuclideanSpace.inner_eq_star_dotProduct]
    norm_num [dotProduct, Fin.sum_univ_two]
  have hrev2_ne : P_2.reversible P_real2 tilt_real2 ≠ 0 := by
    rw [hrev2_val]; norm_num
  have htot2_ne : P_2.totalGenerator P_real2 tilt_real2 ≠ 0 := by
    have hd0 : P_2.dissipative P_real2 tilt_real2 = 0 := by
      change operatorProbeBilin (EuclideanSpace.basisFun (Fin 2) ℝ 0)
        (S_2.S.P_minus P_real2) (S_2.S.P_minus tilt_real2) = 0
      rw [hP_minus_P_real2, _root_.map_zero, LinearMap.zero_apply]
    change P_2.dissipative P_real2 tilt_real2 + P_2.reversible P_real2 tilt_real2 ≠ 0
    rw [hd0, zero_add]
    exact hrev2_ne
  have htot2_mix_ne : P_2.totalGenerator (tilt_real2 + P_real2) tilt_real2 ≠ 0 := by
    change P_2.dissipative (tilt_real2 + P_real2) tilt_real2 +
      P_2.reversible (tilt_real2 + P_real2) tilt_real2 ≠ 0
    rw [_root_.map_add, LinearMap.add_apply, _root_.map_add, LinearMap.add_apply]
    have hd0 : P_2.dissipative P_real2 tilt_real2 = 0 := by
      change operatorProbeBilin (EuclideanSpace.basisFun (Fin 2) ℝ 0)
        (S_2.S.P_minus P_real2) (S_2.S.P_minus tilt_real2) = 0
      rw [hP_minus_P_real2, _root_.map_zero, LinearMap.zero_apply]
    have hr0 : P_2.reversible tilt_real2 tilt_real2 = 0 :=
      self_eq_neg.mp (P_2.reversible_skew tilt_real2 tilt_real2)
    rw [hd0, hdiss_val, hr0, hrev2_val]
    norm_num
  have hGamma_doubled : B_doubled.CIK.GammaS = J_op := by
    rw [InfoGeometry.Canonical.CertifiedInverseKernel.GammaS_eq_two_mul_spectralProjector_sub_one]
    change 2 * (P_doubled_proj * P_doubled_proj) - 1 = J_op
    rw [P_doubled_proj_idem]
    dsimp [P_doubled_proj, J_op]
    apply ContinuousLinearMap.ext
    intro v
    apply InfoGeometry.Krein.DoubledSpace.ext <;>
      simp [InfoGeometry.Krein.modular_j]
  have htheta_eps : S_doubled.S.θ ε_op = -ε_op := by
    change B_doubled.CIK.GammaS * ε_op * B_doubled.CIK.GammaS = -ε_op
    rw [hGamma_doubled]
    have hanti : J_op * ε_op = -(ε_op * J_op) :=
      InfoGeometry.Krein.modular_j_spectral_epsilon_anticommute ℝ
    have hj2 : J_op * J_op = 1 := InfoGeometry.Krein.modular_j_involution ℝ
    calc J_op * ε_op * J_op = (-(ε_op * J_op)) * J_op := by rw [hanti]
      _ = -((ε_op * J_op) * J_op) := neg_mul (ε_op * J_op) J_op
      _ = -(ε_op * (J_op * J_op)) := by rw [mul_assoc]
      _ = -(ε_op * 1) := by rw [hj2]
      _ = -ε_op := by rw [mul_one]
  have htheta_J : S_doubled.S.θ J_op = J_op := by
    change B_doubled.CIK.GammaS * J_op * B_doubled.CIK.GammaS = J_op
    rw [hGamma_doubled]
    have hj2 : J_op * J_op = 1 := InfoGeometry.Krein.modular_j_involution ℝ
    rw [hj2, one_mul]
  have hPm_eps : S_doubled.S.P_minus ε_op = ε_op := by
    change ((2 : ℝ)⁻¹) • (ε_op - S_doubled.S.θ ε_op) = ε_op
    rw [htheta_eps, sub_neg_eq_add, ← two_smul ℝ ε_op, smul_smul]; norm_num
  have hPp_eps : S_doubled.S.P_plus ε_op = 0 := by
    change ((2 : ℝ)⁻¹) • (ε_op + S_doubled.S.θ ε_op) = 0
    rw [htheta_eps, add_neg_cancel, smul_zero]
  have hPp_J : S_doubled.S.P_plus J_op = J_op := by
    change ((2 : ℝ)⁻¹) • (J_op + S_doubled.S.θ J_op) = J_op
    rw [htheta_J, ← two_smul ℝ J_op, smul_smul]; norm_num
  have hPm_J : S_doubled.S.P_minus J_op = 0 := by
    change ((2 : ℝ)⁻¹) • (J_op - S_doubled.S.θ J_op) = 0
    rw [htheta_J, sub_self, smul_zero]
  have hdiss_doubled_pos : 0 < P_doubled.dissipative ε_op ε_op := by
    change 0 < operatorProbeBilin v_id (S_doubled.S.P_minus ε_op) (S_doubled.S.P_minus ε_op)
    rw [hPm_eps, operatorProbeBilin_apply]
    have hev : ε_op v_id = v_id := by
      apply InfoGeometry.Krein.DoubledSpace.ext <;> simp [ε_op, v_id]
    rw [hev, WithLp.prod_inner_apply]
    simp [v_id]
  have hrev_doubled_val : P_doubled.reversible J_op ε_op = 1 := by
    change η_doubled (S_doubled.S.P_plus J_op) (S_doubled.S.P_minus ε_op) -
      η_doubled (S_doubled.S.P_plus ε_op) (S_doubled.S.P_minus J_op) = 1
    simp only [hPp_J, hPm_eps, hPp_eps, hPm_J, _root_.map_zero, sub_zero]
    change @inner ℝ (DoubledSpace ℝ) _ (J_op w_id) (ε_op v_id) = 1
    have hjw : J_op w_id = v_id := by
      apply InfoGeometry.Krein.DoubledSpace.ext <;> simp [J_op, w_id, v_id]
    have hev : ε_op v_id = v_id := by
      apply InfoGeometry.Krein.DoubledSpace.ext <;> simp [ε_op, v_id]
    rw [hjw, hev, WithLp.prod_inner_apply]
    simp [v_id]
  have hrev_doubled_ne : P_doubled.reversible J_op ε_op ≠ 0 := by
    rw [hrev_doubled_val]; norm_num
  have htot_doubled_ne : P_doubled.totalGenerator ε_op J_op ≠ 0 := by
    have hd0 : P_doubled.dissipative ε_op J_op = 0 := by
      change operatorProbeBilin v_id (S_doubled.S.P_minus ε_op) (S_doubled.S.P_minus J_op) = 0
      rw [hPm_eps, hPm_J, map_zero]
    have hrev_skew : P_doubled.reversible ε_op J_op = -1 := by
      rw [P_doubled.reversible_skew, hrev_doubled_val]
    change P_doubled.dissipative ε_op J_op + P_doubled.reversible ε_op J_op ≠ 0
    rw [hd0, hrev_skew]
    norm_num
  exact ⟨S_id.drazinCore_eq_k, S_id.dissipativeRange_eq_p,
    S_2.drazinCore_eq_k, S_2.dissipativeRange_eq_p,
    hrev_self, hdiss_pos,
    S_doubled.drazinCore_eq_k, S_doubled.dissipativeRange_eq_p,
    hdiss_doubled_pos, hrev_doubled_ne,
    P_doubled.onsager_casimir_master_reciprocity J_op ε_op, htot_doubled_ne,
    hrev2_ne, P_2.onsager_casimir_master_reciprocity tilt_real2 P_real2, htot2_ne,
    P_2.onsager_casimir_master_reciprocity tilt_real2 (tilt_real2 + P_real2), htot2_mix_ne⟩

/-- `T1-F1-05`: `onsager_casimir_master_reciprocity` and `entropy_production_T_invariant` on Cartan `ParityOnsagerSystem` with strictly non-zero reciprocity and entropy production. -/
theorem t1_f1_05_cartanMasterReciprocityAndEntropy :
    let C := peirceCartanOnsagerSplit P_d63
    let P_sys := cartanParityOnsagerSystemOfForms C (hsRealBilinForm 2)
      (hsRealBilinForm_symm 2) (hsRealBilinForm_nonneg 2) (hsProbeBilinForm 2 tiltOp2)
    let x_k := C.S.P_plus B_tilt
    let x_p := C.S.P_minus B_tilt
    P_sys.totalGenerator (P_sys.T.op x_k) (P_sys.T.op x_p) =
        P_sys.totalGenerator x_p x_k ∧
      P_sys.totalGenerator x_p x_k ≠ 0 ∧
      P_sys.reversible x_k x_p ≠ 0 ∧
      P_sys.totalGenerator B_tilt B_tilt = P_sys.dissipative B_tilt B_tilt ∧
      0 < P_sys.totalGenerator B_tilt B_tilt ∧
      P_sys.totalGenerator (P_sys.T.op B_tilt) (P_sys.T.op B_tilt) =
        P_sys.totalGenerator B_tilt B_tilt := by
  intro C P_sys x_k x_p
  have hf3 := t1_f1_03_cartanParityOnsagerSystem
  have hrev_ne : P_sys.reversible x_k x_p ≠ 0 := hf3.2.2.1
  have hxk_minus : C.S.P_minus x_k = 0 := by
    have hθ : C.S.θ x_k = x_k := (C.S.mem_evenSubmodule_iff).mp (by
      dsimp only [x_k]
      rw [C.S.P_plus_eq_plusPart]
      exact C.S.plusPart_mem_even B_tilt)
    change ((2 : ℝ)⁻¹) • (x_k - C.S.θ x_k) = 0
    rw [hθ, sub_self, smul_zero]
  have htot_ne : P_sys.totalGenerator x_p x_k ≠ 0 := by
    have hd0 : P_sys.dissipative x_p x_k = 0 := by
      change hsRealBilinForm 2 (C.S.P_minus x_p) (C.S.P_minus x_k) = 0
      rw [hxk_minus, _root_.map_zero]
    change P_sys.dissipative x_p x_k + P_sys.reversible x_p x_k ≠ 0
    rw [hd0, zero_add, P_sys.reversible_skew]
    exact neg_ne_zero.mpr hrev_ne
  have hxp_idem : C.S.P_minus x_p = x_p := by
    have hθ : C.S.θ x_p = -x_p := (C.S.mem_oddSubmodule_iff).mp (by
      dsimp only [x_p]
      rw [C.S.P_minus_eq_minusPart]
      exact C.S.minusPart_mem_odd B_tilt)
    change ((2 : ℝ)⁻¹) • (x_p - C.S.θ x_p) = x_p
    rw [hθ, sub_neg_eq_add, ← two_smul ℝ x_p, smul_smul]; norm_num
  have hBt_pos : 0 < P_sys.totalGenerator B_tilt B_tilt := by
    rw [P_sys.entropy_production_eq B_tilt]
    change 0 < hsRealBilinForm 2 x_p x_p
    rw [← hxp_idem]
    exact hf3.2.1
  exact ⟨P_sys.onsager_casimir_master_reciprocity x_k x_p,
    htot_ne, hrev_ne,
    P_sys.entropy_production_eq B_tilt,
    hBt_pos,
    P_sys.entropy_production_T_invariant B_tilt⟩

/-- `T1-F2-01`: `ScalarSchurDrazinBlock` bridges via `effectiveEvenOnsager` to `ParityOnsagerSystem ℝ`. -/
theorem t1_f2_01_scalarSchurEffective :
    let hEff : 0 ≤ B_ns.effectiveEvenOnsager := by
      norm_num [B_ns, ScalarSchurDrazinBlock.effectiveEvenOnsager]
    let P_ns := scalarEffectiveParityOnsagerSystem B_ns hEff
    B_ns.effectiveEvenOnsager = 3 ∧
      P_ns.dissipative 2 2 = 12 ∧
      0 ≤ P_ns.dissipative 2 2 ∧
      P_ns.totalGenerator (P_ns.T.op 2) (P_ns.T.op 3) = P_ns.totalGenerator 3 2 := by
  intro hEff P_ns
  have heff : B_ns.effectiveEvenOnsager = 3 := by
    norm_num [B_ns, ScalarSchurDrazinBlock.effectiveEvenOnsager]
  have hdiss : P_ns.dissipative 2 2 = 12 := by
    change B_ns.effectiveEvenOnsager * 2 * 2 = 12
    rw [heff]; norm_num
  exact ⟨heff, hdiss, P_ns.dissipative_nonneg 2, P_ns.onsager_casimir_master_reciprocity 2 3⟩

/-- `T1-F2-02`: `DrazinPenroseSchurTriad` with `bodyForce ≠ 0` preserves `production = bodyForce * effectiveEvenOnsager * bodyForce`. -/
theorem t1_f2_02_drazinPenroseTriad :
    let hForce : triad_pos.entropy.bodyForce ≠ 0 := by norm_num [triad_pos]
    let P_tr := triadEffectiveParityOnsagerSystem triad_pos hForce
    P_tr.dissipative triad_pos.entropy.bodyForce triad_pos.entropy.bodyForce =
        triad_pos.entropy.production ∧
      triad_pos.entropy.production = 12 ∧
      0 ≤ triad_pos.entropy.production := by
  intro hForce P_tr
  have h1 : P_tr.dissipative triad_pos.entropy.bodyForce triad_pos.entropy.bodyForce =
      triad_pos.entropy.production := by
    change triad_pos.block.effectiveEvenOnsager * triad_pos.entropy.bodyForce *
        triad_pos.entropy.bodyForce = triad_pos.entropy.production
    rw [triad_pos.entropy.production_eq, triad_pos.entropy_uses_effective_block]
    ring
  exact ⟨h1, rfl, triad_pos.entropy.production_nonneg⟩

/-- `T1-F2-03`: `TKKOnsagerMatrix` bridges to `ParityOnsagerSystem (TKKGrade → ℝ)` under `TKKGrade.dual`. -/
theorem t1_f2_03_tkkParityOnsagerSystem :
    let P_tkk := tkkParityOnsagerSystem M_tkk M_tkk_psd M_tkk_dual
    let x : InfoGeometry.SuperMetriplectic.TKKGrade → ℝ :=
      fun g => match g with | .minus => 1 | .zero => 2 | .plus => -1
    let y : InfoGeometry.SuperMetriplectic.TKKGrade → ℝ :=
      fun g => match g with | .minus => 0 | .zero => 1 | .plus => 3
    P_tkk.dissipative x y =
        tkkSum (fun i => tkkSum (fun j => x i * M_tkk.entry i j * y j)) ∧
      P_tkk.dissipative (P_tkk.T.op x) (P_tkk.T.op y) = P_tkk.dissipative x y ∧
      0 < P_tkk.dissipative x x ∧
      P_tkk.totalGenerator (P_tkk.T.op x) (P_tkk.T.op y) = P_tkk.totalGenerator y x := by
  intro P_tkk x y
  have hpos : 0 < P_tkk.dissipative x x := by
    change 0 < tkkSum (fun i => tkkSum (fun j => x i * M_tkk.entry i j * x j))
    norm_num [tkkSum, M_tkk, x]
  exact ⟨rfl, P_tkk.dissipative_T_even x y, hpos, P_tkk.onsager_casimir_master_reciprocity x y⟩

/-- `T1-F2-04`: Noncommutative `ConformalOnsagerBlock (FiniteOperatorAlgebra 2)` using global `NormedAlgebra.restrictScalars` bridges to `ParityOnsagerSystem` with strictly positive dissipation and non-zero reciprocity. -/
theorem t1_f2_04_conformalOnsagerBlock :
    let P_conf := conformalBlockCanonicalParityOnsagerSystem conformalBlock_nc
    conformalBlock_nc.Pmu * conformalBlock_nc.Kmu ≠
        conformalBlock_nc.Kmu * conformalBlock_nc.Pmu ∧
      conformalBlock_nc.reversiblePK = 3 ∧
      conformalBlock_nc.totalPK = 6 ∧
      0 < P_conf.dissipative ![1, 0] ![1, 0] ∧
      P_conf.totalGenerator (P_conf.T.op ![0, 1]) (P_conf.T.op ![1, 0]) =
        P_conf.totalGenerator ![1, 0] ![0, 1] ∧
      P_conf.totalGenerator ![1, 0] ![0, 1] ≠ 0 ∧
      P_conf.reversible ![1, 0] ![0, 1] ≠ 0 := by
  intro P_conf
  have hnc : conformalBlock_nc.Pmu * conformalBlock_nc.Kmu ≠
      conformalBlock_nc.Kmu * conformalBlock_nc.Pmu := by
    intro heq
    have hm := congrArg (fun Z : FiniteOperatorAlgebra 2 => matrixOfOp Z 0 0) heq
    rw [matrixOfOp_mul_eq, matrixOfOp_mul_eq, conformalBlock_nc, matrixOfOp_matrixOp,
      matrixOfOp_matrixOp] at hm
    norm_num [Matrix.mul_apply, Fin.sum_univ_two] at hm
  have hd_pos : 0 < P_conf.dissipative ![1, 0] ![1, 0] := by
    change 0 < |conformalBlock_nc.covariancePK + conformalBlock_nc.souriauCocyclePK| * 1 * 1 +
      (conformalBlock_nc.covariancePK + conformalBlock_nc.souriauCocyclePK) * (1 * 0 + 0 * 1) +
      |conformalBlock_nc.covariancePK + conformalBlock_nc.souriauCocyclePK| * 0 * 0
    norm_num [conformalBlock_nc]
  have htot_ne : P_conf.totalGenerator ![1, 0] ![0, 1] ≠ 0 := by
    rw [conformalBlockCanonicalParityOnsagerSystem_totalGenerator_basis conformalBlock_nc]
    norm_num [conformalBlock_nc]
  have hrev_ne : P_conf.reversible ![1, 0] ![0, 1] ≠ 0 := by
    change conformalBlock_nc.reversiblePK * ((1 : ℝ) * 1 - 0 * 0) ≠ 0
    norm_num [conformalBlock_nc]
  exact ⟨hnc, rfl, rfl, hd_pos,
    P_conf.onsager_casimir_master_reciprocity ![0, 1] ![1, 0],
    htot_ne, hrev_ne⟩

/-- `T1-F2-05`: `ConformalPKMetriplecticSplit` bridges to `ParityOnsagerSystem` evaluated on `![1, 0]` and `![0, 1]` with strictly positive dissipation and non-zero reciprocity. -/
theorem t1_f2_05_conformalPKMetriplecticSplit :
    let split_pk : ConformalPKMetriplecticSplit :=
      { reversiblePK := 3
        covariancePK := 2
        souriauCocyclePK := 1
        dissipativePK := 3
        totalPK := 6
        dissipativePK_eq_covariance_plus_cocycle := by norm_num
        totalPK_eq_reversible_plus_dissipative := by norm_num }
    let P_pk := conformalPKSplitCanonicalParityOnsagerSystem split_pk
    P_pk.dissipative ![1, 0] ![1, 0] = split_pk.dissipativePK ∧
      P_pk.totalGenerator ![1, 0] ![0, 1] = split_pk.totalPK ∧
      0 < P_pk.dissipative ![1, 0] ![1, 0] ∧
      P_pk.totalGenerator (P_pk.T.op ![0, 1]) (P_pk.T.op ![1, 0]) =
        P_pk.totalGenerator ![1, 0] ![0, 1] ∧
      P_pk.totalGenerator ![1, 0] ![0, 1] ≠ 0 := by
  intro split_pk P_pk
  have hd : P_pk.dissipative ![1, 0] ![1, 0] = split_pk.dissipativePK := by
    change |split_pk.dissipativePK| * 1 * 1 + split_pk.dissipativePK * (1 * 0 + 0 * 1) +
      |split_pk.dissipativePK| * 0 * 0 = split_pk.dissipativePK
    norm_num [split_pk]
  have hd_pos : 0 < P_pk.dissipative ![1, 0] ![1, 0] := by
    rw [hd]; norm_num [split_pk]
  have htot := conformalPKSplitCanonicalParityOnsagerSystem_totalGenerator_basis split_pk
  have htot_ne : P_pk.totalGenerator ![1, 0] ![0, 1] ≠ 0 := by
    rw [htot]; norm_num [split_pk]
  exact ⟨hd, htot, hd_pos,
    P_pk.onsager_casimir_master_reciprocity ![0, 1] ![1, 0], htot_ne⟩

/-- `T1-F3-01`: `peirceSymmetricLieAlgebra P_d63` preserves Lie brackets and is involutive. -/
theorem t1_f3_01_peirceSymmetricLieAlgebra :
    let S := peirceSymmetricLieAlgebra P_d63
    S.θ (S.θ A_swap) = A_swap ∧
      S.θ ⁅A_swap, B_tilt⁆ = ⁅S.θ A_swap, S.θ B_tilt⁆ := by
  intro S
  exact ⟨S.involutive A_swap, S.θ.map_lie A_swap B_tilt⟩

/-- `T1-F3-02`: Exact Cartan subspace equality `ker(ad_P^2) = S.𝔨` and `range ad_P = S.𝔭` on `P_d63` and `P_diag`. -/
theorem t1_f3_02_peirceAdKerRange :
    (LinearMap.ker (peirceAdMap P_d63 ∘ₗ peirceAdMap P_d63) = (peirceSymmetricLieAlgebra P_d63).𝔨 ∧
      LinearMap.range (peirceAdMap P_d63) = (peirceSymmetricLieAlgebra P_d63).𝔭) ∧
    (LinearMap.ker (peirceAdMap P_diag ∘ₗ peirceAdMap P_diag) = (peirceSymmetricLieAlgebra P_diag).𝔨 ∧
      LinearMap.range (peirceAdMap P_diag) = (peirceSymmetricLieAlgebra P_diag).𝔭) :=
  ⟨⟨peirceAdSq_ker_eq_k P_d63, peirceAd_range_eq_p P_d63⟩,
    ⟨peirceAdSq_ker_eq_k P_diag, peirceAd_range_eq_p P_diag⟩⟩

/-- `T1-F3-03`: `peirceCartanOnsagerSplit` and `peirceCartanLinearEquiv` decompose `B_tilt` into `𝔨 ⊕ 𝔭`. -/
theorem t1_f3_03_peirceCartanSplitAndEquiv :
    let C := peirceCartanOnsagerSplit P_d63
    let splitB := peirceCartanLinearEquiv P_d63 B_tilt
    C.drazinCore = C.S.𝔨 ∧
      C.dissipativeRange = C.S.𝔭 ∧
      (splitB.1 : FiniteOperatorAlgebra 2) ∈ C.S.𝔨 ∧
      (splitB.2 : FiniteOperatorAlgebra 2) ∈ C.S.𝔭 ∧
      (splitB.1 : FiniteOperatorAlgebra 2) + (splitB.2 : FiniteOperatorAlgebra 2) = B_tilt := by
  intro C splitB
  have hmem1 : (splitB.1 : FiniteOperatorAlgebra 2) ∈ C.S.𝔨 := by
    change (splitB.1 : FiniteOperatorAlgebra 2) ∈ (peirceSymmetricLieAlgebra P_d63).𝔨
    rw [← peirceAdSq_ker_eq_k P_d63]
    exact splitB.1.property
  have hmem2 : (splitB.2 : FiniteOperatorAlgebra 2) ∈ C.S.𝔭 := by
    change (splitB.2 : FiniteOperatorAlgebra 2) ∈ (peirceSymmetricLieAlgebra P_d63).𝔭
    rw [← peirceAd_range_eq_p P_d63]
    exact splitB.2.property
  have hsum : (splitB.1 : FiniteOperatorAlgebra 2) + (splitB.2 : FiniteOperatorAlgebra 2) = B_tilt := by
    have h := peirceCartanLinearEquiv_apply P_d63 B_tilt
    rw [h.1, h.2]
    change evenGrade P_d63.1 B_tilt + oddGrade P_d63.1 B_tilt = B_tilt
    have hp1 := symmetricLieAlgebraOfIdempotent_P_plus P_d63.1 P_d63.property B_tilt
    have hp2 := symmetricLieAlgebraOfIdempotent_P_minus P_d63.1 P_d63.property B_tilt
    rw [← hp1, ← hp2]
    exact ((peirceSymmetricLieAlgebra P_d63).cartan_decomposition B_tilt).symm
  exact ⟨C.drazinCore_eq_k, C.dissipativeRange_eq_p, hmem1, hmem2, hsum⟩

/-- `T1-F3-04`: `cutDerivation P_d63` embeds faithfully into `peirceCutDerivationLieLane 2`. -/
theorem t1_f3_04_peirceCutDerivationLieLane :
    let K := peirceCutDerivationLieLane 2
    let d := peirceCutGenerator P_d63
    K.operatorAction d B_tilt = P_d63.1 * B_tilt - B_tilt * P_d63.1 ∧
      K.operatorAction d B_tilt ≠ 0 ∧
      K.operatorAction d (A_swap * B_tilt) =
        K.operatorAction d A_swap * B_tilt + A_swap * K.operatorAction d B_tilt ∧
      Function.Injective K.act := by
  intro K d
  have hne : K.operatorAction d B_tilt ≠ 0 := by
    intro h0
    have hact : K.operatorAction d B_tilt = cutDerivation P_d63 B_tilt :=
      peirceCutGenerator_operatorAction P_d63 B_tilt
    rw [hact, cutDerivation_apply] at h0
    have hm := congrArg (fun Z : FiniteOperatorAlgebra 2 => matrixOfOp Z 0 1) h0
    change matrixOfOp (P_d63.1 * B_tilt - B_tilt * P_d63.1) 0 1 = 0 at hm
    rw [matrixOfOp_sub_eq, matrixOfOp_mul_eq, matrixOfOp_mul_eq,
      show matrixOfOp P_d63.1 = d63TiltedProjection from matrixOfOp_matrixOp _,
      B_tilt, matrixOfOp_matrixOp] at hm
    norm_num [d63TiltedProjection, tiltedMatrix, Matrix.mul_apply, Fin.sum_univ_two] at hm
  exact ⟨by rw [peirceCutGenerator_operatorAction, cutDerivation_apply]; rfl,
    hne, K.operatorAction_leibniz d A_swap B_tilt, K.faithful⟩

/-- `T1-F3-05`: `cutDerivation` grading powers align with `S.P_plus` and `S.P_minus`. -/
theorem t1_f3_05_cutDerivationPowersAlign :
    let S := peirceSymmetricLieAlgebra P_d63
    cutDerivation P_d63 (cutDerivation P_d63 B_tilt) = S.P_minus B_tilt ∧
      cutDerivation P_d63 (S.P_plus B_tilt) = 0 ∧
      cutDerivation P_d63 (cutDerivation P_d63 (cutDerivation P_d63 B_tilt)) =
        cutDerivation P_d63 B_tilt := by
  intro S
  have hPplus : S.P_plus B_tilt = evenGrade P_d63.1 B_tilt :=
    symmetricLieAlgebraOfIdempotent_P_plus P_d63.1 P_d63.property B_tilt
  have hPminus : S.P_minus B_tilt = oddGrade P_d63.1 B_tilt :=
    symmetricLieAlgebraOfIdempotent_P_minus P_d63.1 P_d63.property B_tilt
  exact ⟨(cutDerivation_square_eq_oddGrade P_d63 B_tilt).trans hPminus.symm,
    by rw [hPplus]; exact cutDerivation_evenGrade_zero P_d63 B_tilt,
    cutDerivation_cube_eq_self P_d63 B_tilt⟩

/-- `T2-F1-01`: Sign-flip boundary (`-S.θ` vs `S.θ`) on nonzero `x_p ∈ S.𝔭`. -/
theorem t2_f1_01_signFlipParity :
    let C := peirceCartanOnsagerSplit P_d63
    let x_p := C.S.P_minus B_tilt
    (cartanTimeReversal C).op x_p = x_p ∧
      (cartanInvolutionTimeReversal C).op x_p = -x_p ∧
      x_p ≠ -x_p := by
  intro C x_p
  have hp_mem : x_p ∈ C.dissipativeRange := by
    rw [C.dissipativeRange_eq_p]
    exact C.S.minusPart_mem_odd B_tilt
  refine ⟨cartanTimeReversal_eq_self_of_mem_dissipativeRange C hp_mem,
    cartanInvolutionTimeReversal_eq_neg_of_mem_dissipativeRange C hp_mem, ?_⟩
  intro heq
  have hm := congrArg (fun Z : FiniteOperatorAlgebra 2 => matrixOfOp Z 0 0) heq
  rw [matrixOfOp_neg_eq] at hm
  change matrixOfOp ((peirceSymmetricLieAlgebra P_d63).P_minus B_tilt) 0 0 =
    -matrixOfOp ((peirceSymmetricLieAlgebra P_d63).P_minus B_tilt) 0 0 at hm
  rw [matrixOfOp_d63_P_minus_B_tilt] at hm
  norm_num at hm

/-- `T2-F1-02`: Degenerate identity involution (`θ = id`) collapses `S.𝔭 = ⊥`. -/
theorem t2_f1_02_degenerateIdInvolution :
    let idLie : LieEquiv ℝ (FiniteOperatorAlgebra 2) (FiniteOperatorAlgebra 2) :=
      { toFun := id, invFun := id, left_inv := fun _ => rfl, right_inv := fun _ => rfl,
        map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl, map_lie' := rfl }
    let θ_id : InvolutiveLieAut (FiniteOperatorAlgebra 2) := ⟨idLie, fun _ => rfl⟩
    let S_id := SymmetricLieAlgebra.ofInvolutiveLieAut θ_id
    let C_id : CartanOnsagerSplit (FiniteOperatorAlgebra 2) :=
      { S := S_id
        onsager := S_id.P_minus
        drazinCore := S_id.𝔨
        dissipativeRange := S_id.𝔭
        drazinCore_eq_k := rfl
        dissipativeRange_eq_p := rfl }
    S_id.oddSubmodule = ⊥ ∧
      (∀ X : FiniteOperatorAlgebra 2, X ∈ S_id.𝔨) ∧
      (∀ X Y : FiniteOperatorAlgebra 2, cartanProjectedDissipative C_id (hsRealBilinForm 2) X Y = 0) := by
  intro idLie θ_id S_id C_id
  have hk : ∀ X : FiniteOperatorAlgebra 2, X ∈ S_id.𝔨 := fun X => by
    change X ∈ S_id.evenSubmodule
    rw [S_id.mem_evenSubmodule_iff]
    rfl
  have hp : S_id.oddSubmodule = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro X hX
    rw [S_id.mem_oddSubmodule_iff] at hX
    change X = -X at hX
    have h2 : (2 : ℝ) • X = 0 := by
      rw [two_smul ℝ X]
      nth_rw 2 [hX]
      exact add_neg_cancel X
    have hhalf := congrArg (fun Z : FiniteOperatorAlgebra 2 => ((2 : ℝ)⁻¹) • Z) h2
    have h0 : ((2 : ℝ)⁻¹) • (0 : FiniteOperatorAlgebra 2) = 0 :=
      ContinuousLinearMap.ext fun _ => by simp
    rw [h0, smul_smul] at hhalf
    norm_num at hhalf
    exact hhalf
  have hPminus0 : ∀ X : FiniteOperatorAlgebra 2, S_id.P_minus X = 0 := fun X => by
    change ((2 : ℝ)⁻¹) • (X - X) = 0
    simp
  refine ⟨hp, hk, fun X Y => ?_⟩
  change hsRealBilinForm 2 (S_id.P_minus X) (S_id.P_minus Y) = 0
  rw [hPminus0 X, map_zero, LinearMap.zero_apply]

/-- `T2-F1-03`: Reversible-only limit (`dissipative = 0`, `reversible ≠ 0`). -/
theorem t2_f1_03_reversibleOnlyZeroOnsager :
    let C := peirceCartanOnsagerSplit P_d63
    let P_rev := cartanParityOnsagerSystemOfForms C 0 (fun _ _ => rfl) (fun _ => le_rfl)
      (hsProbeBilinForm 2 tiltOp2)
    let x_k := C.S.P_plus B_tilt
    let x_p := C.S.P_minus B_tilt
    (∀ X, P_rev.totalGenerator X X = 0) ∧
      P_rev.reversible x_k x_p ≠ 0 ∧
      P_rev.totalGenerator (P_rev.T.op x_k) (P_rev.T.op x_p) = P_rev.totalGenerator x_p x_k := by
  intro C P_rev x_k x_p
  refine ⟨fun X => ?_, ?_, P_rev.onsager_casimir_master_reciprocity x_k x_p⟩
  · rw [P_rev.entropy_production_eq]
    rfl
  · let P_sys := cartanParityOnsagerSystemOfForms C (hsRealBilinForm 2)
      (hsRealBilinForm_symm 2) (hsRealBilinForm_nonneg 2) (hsProbeBilinForm 2 tiltOp2)
    change P_sys.reversible x_k x_p ≠ 0
    exact t1_f1_03_cartanParityOnsagerSystem.2.2.1

/-- `T2-F1-04`: Non-abelian Cartan Lie bracket `⁅x_k, x_p⁆ ≠ 0` and `⁅x_k, x_p⁆ ∈ S.𝔭`. -/
theorem t2_f1_04_nonabelianCartanBrackets :
    let S := peirceSymmetricLieAlgebra P_d63
    let x_k := S.P_plus B_tilt
    let x_p := S.P_minus B_tilt
    ⁅x_k, x_p⁆ ≠ 0 ∧ ⁅x_k, x_p⁆ ∈ S.𝔭 := by
  intro S x_k x_p
  have hmem : ⁅x_k, x_p⁆ ∈ S.𝔭 :=
    S.bracket_k_p (S.plusPart_mem_even B_tilt) (S.minusPart_mem_odd B_tilt)
  have hne : ⁅x_k, x_p⁆ ≠ 0 := by
    intro h0
    have hm := congrArg (fun Z : FiniteOperatorAlgebra 2 => matrixOfOp Z 0 1) h0
    change matrixOfOp (x_k * x_p - x_p * x_k) 0 1 = 0 at hm
    rw [matrixOfOp_sub_eq, matrixOfOp_mul_eq, matrixOfOp_mul_eq,
      matrixOfOp_d63_P_plus_B_tilt, matrixOfOp_d63_P_minus_B_tilt] at hm
    norm_num [Matrix.mul_apply, Fin.sum_univ_two] at hm
  exact ⟨hne, hmem⟩

/-- `T2-F1-05`: Negative dissipative bilinear counterexample fails `0 ≤ D_neg x x`. -/
theorem t2_f1_05_negativeDissipativeCounterexample :
    let D_neg : LinearMap.BilinForm ℝ (FiniteOperatorAlgebra 2) := -(hsRealBilinForm 2)
    D_neg A_swap A_swap = -2 ∧ ¬ (0 ≤ D_neg A_swap A_swap) := by
  intro D_neg
  have hval : D_neg A_swap A_swap = -2 := by
    change -(Matrix.trace (matrixOfOp (star A_swap * A_swap))).re = -2
    rw [hA_swap_sa.star_eq, matrixOfOp_mul_eq, A_swap, matrixOfOp_matrixOp]
    norm_num [Matrix.trace, Matrix.diag, Matrix.mul_apply, swapMatrix, Fin.sum_univ_two]
  exact ⟨hval, by rw [hval]; norm_num⟩

/-- `T2-F2-01`: Singular hidden block (`LΘΘ = 0`, `index = 1`) has `drazinDefectProjector = 1` and `dissipative 2 2 = 16 > 0`. -/
theorem t2_f2_01_singularHiddenBlock :
    let hEff : 0 ≤ B_sing.effectiveEvenOnsager := by
      norm_num [B_sing, ScalarSchurDrazinBlock.effectiveEvenOnsager]
    let P_sing := scalarEffectiveParityOnsagerSystem B_sing hEff
    B_sing.drazinDefectProjector = 1 ∧
      B_sing.effectiveEvenOnsager = 4 ∧
      P_sing.dissipative 2 2 = 16 ∧
      0 < P_sing.dissipative 2 2 := by
  intro hEff P_sing
  have hd : B_sing.drazinDefectProjector = 1 := by
    norm_num [B_sing, ScalarSchurDrazinBlock.drazinDefectProjector]
  have he : B_sing.effectiveEvenOnsager = 4 := by
    norm_num [B_sing, ScalarSchurDrazinBlock.effectiveEvenOnsager]
  have hp : P_sing.dissipative 2 2 = 16 := by
    change B_sing.effectiveEvenOnsager * 2 * 2 = 16
    rw [he]; norm_num
  exact ⟨hd, he, hp, by linarith⟩

/-- `T2-F2-02`: Schur complement saturation (`effectiveEvenOnsager = 0` despite `LPP > 0`). -/
theorem t2_f2_02_schurComplementSaturation :
    B_sat.drazinDefectProjector = 0 ∧
      B_sat.effectiveEvenOnsager = 0 ∧
      triad_sat.entropy.bodyForce = 5 ∧
      triad_sat.entropy.production = 0 :=
  ⟨by norm_num [B_sat, ScalarSchurDrazinBlock.drazinDefectProjector],
   by norm_num [B_sat, ScalarSchurDrazinBlock.effectiveEvenOnsager],
   rfl, rfl⟩

/-- `T2-F2-03`: Strict positivity `production > 0` at `bodyForce = 2` vs `0` at `bodyForce = 0`. -/
theorem t2_f2_03_bodyForcePositivityVsZero :
    0 < triad_pos.entropy.production ∧ triad_zero.entropy.production = 0 :=
  ⟨by norm_num [triad_pos], rfl⟩

/-- `T2-F2-04`: `TKKGrade.dual_dual` involution and degenerate zero `TKKOnsagerMatrix`. -/
theorem t2_f2_04_tkkDualDualAndZeroMatrix
    (g : InfoGeometry.SuperMetriplectic.TKKGrade)
    (x : InfoGeometry.SuperMetriplectic.TKKGrade → ℝ) :
    let M_zero : TKKOnsagerMatrix := ⟨fun _ _ => 0, fun _ _ => rfl⟩
    let P_zero := tkkOnsagerSystem M_zero (fun v => by simp [tkkSum, M_zero])
    g.dual.dual = g ∧ P_zero.dissipative x x = 0 := by
  intro M_zero P_zero
  exact ⟨InfoGeometry.SuperMetriplectic.TKKGrade.dual_dual g,
    by simp [P_zero, tkkOnsagerSystem, tkkSum, M_zero]⟩

/-- `T2-F2-05`: Conformal commutator boundary (`[Pmu, Kmu] ≠ 0` vs commuting scalar limit). -/
theorem t2_f2_05_conformalCommutatorVsCommutingLimit :
    let B_comm : ConformalOnsagerBlock (FiniteOperatorAlgebra 2) :=
      { Pmu := 0, Kmu := 0, D := 1, Mmunu := 1
        covariancePK := 0, souriauCocyclePK := 0, reversiblePK := 0, totalPK := 0
        dilationMoment := 1, lorentzMoment := 1, eta := 1, weylWeightP := 0, weylWeightK := 0
        bracket_P_K_eq := by simp
        reversiblePK_eq_dilation_lorentz_moment := by norm_num
        totalPK_eq_reversible_plus_covariance_plus_cocycle := by norm_num }
    (conformalBlock_nc.Pmu * conformalBlock_nc.Kmu ≠
        conformalBlock_nc.Kmu * conformalBlock_nc.Pmu) ∧
      (conformalBlockToPKSplit B_comm).dissipativePK = 0 ∧
      B_comm.totalPK = B_comm.reversiblePK := by
  intro B_comm
  exact ⟨t1_f2_04_conformalOnsagerBlock.1, by norm_num [conformalBlockToPKSplit, B_comm], rfl⟩

/-- `T2-F3-01`: Degenerate zero projector `P = 0` collapses `cutDerivation 0 = 0`, `S.𝔭 = ⊥`, `S.𝔨 = ⊤`. -/
theorem t2_f3_01_zeroProjector :
    let P_0 : PeirceCut 2 := ⟨0, by simp⟩
    let S := peirceSymmetricLieAlgebra P_0
    (∀ X, cutDerivation P_0 X = 0) ∧ S.𝔭 = ⊥ ∧ S.𝔨 = ⊤ := by
  intro P_0 S
  have hcut : ∀ X, cutDerivation P_0 X = 0 := fun X => by
    rw [cutDerivation_apply]
    change (0 : FiniteOperatorAlgebra 2) * X - X * 0 = 0
    simp
  have hp : S.𝔭 = ⊥ := by
    rw [← peirceAd_range_eq_p P_0, LinearMap.range_eq_bot]
    apply LinearMap.ext
    intro X
    rw [peirceAdMap_eq_adMap]
    exact hcut X
  have hk : S.𝔨 = ⊤ := by
    rw [← peirceAd_ker_eq_k P_0, LinearMap.ker_eq_top]
    apply LinearMap.ext
    intro X
    rw [peirceAdMap_eq_adMap]
    exact hcut X
  exact ⟨hcut, hp, hk⟩

/-- `T2-F3-02`: Degenerate identity projector `P = 1` collapses `cutDerivation 1 = 0`, `S.𝔭 = ⊥`, `S.𝔨 = ⊤`. -/
theorem t2_f3_02_identityProjector :
    let P_1 : PeirceCut 2 := ⟨1, by simp⟩
    let S := peirceSymmetricLieAlgebra P_1
    (∀ X, cutDerivation P_1 X = 0) ∧ S.𝔭 = ⊥ ∧ S.𝔨 = ⊤ := by
  intro P_1 S
  have hcut : ∀ X, cutDerivation P_1 X = 0 := fun X => by
    rw [cutDerivation_apply]
    change (1 : FiniteOperatorAlgebra 2) * X - X * 1 = 0
    simp
  have hp : S.𝔭 = ⊥ := by
    rw [← peirceAd_range_eq_p P_1, LinearMap.range_eq_bot]
    apply LinearMap.ext
    intro X
    rw [peirceAdMap_eq_adMap]
    exact hcut X
  have hk : S.𝔨 = ⊤ := by
    rw [← peirceAd_ker_eq_k P_1, LinearMap.ker_eq_top]
    apply LinearMap.ext
    intro X
    rw [peirceAdMap_eq_adMap]
    exact hcut X
  exact ⟨hcut, hp, hk⟩

/-- `T2-F3-03`: Noncommuting Peirce cuts `[cutDerivation P_diag, cutDerivation P_d63] A_swap ≠ 0`. -/
theorem t2_f3_03_noncommutingPeirceCuts :
    let K := peirceCutDerivationLieLane 2
    let d1 := peirceCutGenerator P_diag
    let d2 := peirceCutGenerator P_d63
    K.operatorAction ⁅d1, d2⁆ A_swap ≠ 0 := by
  intro K d1 d2 h0
  have hbr : K.operatorAction ⁅d1, d2⁆ A_swap =
      cutDerivation P_diag (cutDerivation P_d63 A_swap) -
        cutDerivation P_d63 (cutDerivation P_diag A_swap) := rfl
  rw [hbr] at h0
  have hP1A : cutDerivation P_d63 A_swap = 0 := by
    rw [cutDerivation_apply]
    change P_d63.1 * A_swap - A_swap * P_d63.1 = 0
    apply matrixOfOp_injective
    rw [matrixOfOp_sub_eq, matrixOfOp_mul_eq, matrixOfOp_mul_eq, matrixOfOp_zero,
      show matrixOfOp P_d63.1 = d63TiltedProjection from matrixOfOp_matrixOp _,
      A_swap, matrixOfOp_matrixOp]
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [d63TiltedProjection, swapMatrix, Matrix.mul_apply, Fin.sum_univ_two]
  rw [hP1A, map_zero, zero_sub, neg_eq_zero, cutDerivation_apply, cutDerivation_apply] at h0
  have hm := congrArg (fun Z : FiniteOperatorAlgebra 2 => matrixOfOp Z 0 0) h0
  change matrixOfOp (P_d63.1 * (P_diag.1 * A_swap - A_swap * P_diag.1) -
    (P_diag.1 * A_swap - A_swap * P_diag.1) * P_d63.1) 0 0 = 0 at hm
  rw [matrixOfOp_sub_eq, matrixOfOp_mul_eq, matrixOfOp_mul_eq, matrixOfOp_sub_eq,
    matrixOfOp_mul_eq, matrixOfOp_mul_eq,
    show matrixOfOp P_d63.1 = d63TiltedProjection from matrixOfOp_matrixOp _,
    show matrixOfOp P_diag.1 = P_diag_mat from matrixOfOp_matrixOp _,
    A_swap, matrixOfOp_matrixOp] at hm
  norm_num [d63TiltedProjection, P_diag_mat, swapMatrix, Matrix.mul_apply, Fin.sum_univ_two] at hm

/-- `T2-F3-04`: Non-idempotent operator `B_tilt * B_tilt ≠ B_tilt` cannot form a `PeirceCut 2`. -/
theorem t2_f3_04_nonIdempotentBoundary : B_tilt * B_tilt ≠ B_tilt := by
  intro h
  have hm := congrArg (fun Z : FiniteOperatorAlgebra 2 => matrixOfOp Z 0 0) h
  rw [matrixOfOp_mul_eq, B_tilt, matrixOfOp_matrixOp] at hm
  norm_num [tiltedMatrix, Matrix.mul_apply, Fin.sum_univ_two] at hm

/-- `T2-F3-05`: Dimension `n = 0` forces `FiniteOperatorAlgebra 0` trivial while `n = 2` has `S.𝔭 ≠ ⊥`. -/
theorem t2_f3_05_dim0VsDim2Boundary (X : FiniteOperatorAlgebra 0) :
    X = 0 ∧ (peirceSymmetricLieAlgebra P_d63).P_minus B_tilt ≠ 0 := by
  refine ⟨ContinuousLinearMap.ext fun v => ?_, peirce_d63_P_minus_B_tilt_ne⟩
  ext i
  exact Fin.elim0 i

end GapA_Tests

/-! ## Section 2: Tier 1 & Tier 2 — Gap B (`F4`, `F5`) & Gap C (`F6`) -/

section GapB_Tests

attribute [local instance 100] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

private lemma isSelfAdjoint_I_smul_comm {n : ℕ} (X Y : GibbsOperator n)
    (hX : IsSelfAdjoint X) (hY : IsSelfAdjoint Y) :
    IsSelfAdjoint ((Complex.I • X) * Y - Y * (Complex.I • X)) := by
  rw [isSelfAdjoint_iff]
  have hsub : star ((Complex.I • X) * Y - Y * (Complex.I • X)) =
      star ((Complex.I • X) * Y) - star (Y * (Complex.I • X)) :=
    (finiteOperatorStarRealCLM n).map_sub _ _
  rw [hsub, StarMul.star_mul, StarMul.star_mul, star_smul, Complex.star_def, Complex.conj_I,
    hX.star_eq, hY.star_eq, smul_mul_assoc, mul_smul_comm, mul_smul_comm, smul_mul_assoc]
  have h1 : (-Complex.I) • (Y * X) = -(Complex.I • (Y * X)) := neg_smul Complex.I (Y * X)
  have h2 : (-Complex.I) • (X * Y) = -(Complex.I • (X * Y)) := neg_smul Complex.I (X * Y)
  rw [h1, h2]
  abel

private lemma isSelfAdjoint_real_smul {n : ℕ} (r : ℝ) (X : GibbsOperator n)
    (hX : IsSelfAdjoint X) : IsSelfAdjoint (r • X) := by
  rw [isSelfAdjoint_iff, real_smul_eq_complex_smul, star_smul, Complex.star_def,
    Complex.conj_ofReal, hX.star_eq]

private lemma isSelfAdjoint_add_op {n : ℕ} {X Y : GibbsOperator n}
    (hX : IsSelfAdjoint X) (hY : IsSelfAdjoint Y) : IsSelfAdjoint (X + Y) := by
  rw [isSelfAdjoint_iff]
  have hadd := (finiteOperatorStarRealCLM n).map_add X Y
  change star (X + Y) = X + Y
  rw [show star (X + Y) = star X + star Y from hadd, hX.star_eq, hY.star_eq]

private lemma switchOp2_eq_A_swap : switchOp2 = A_swap := by
  apply matrixOfOp_injective
  rw [switchOp2, A_swap, matrixOfOp_matrixOp, matrixOfOp_matrixOp]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [InfoGeometry.Physics.KleinBottleSewingExact.switch2, swapMatrix]

/-- `T1-F4-01`: `bkmRealBilinForm_star` and `centeredBKMRealCovariance_star` on non-maximally-mixed `H_d63`. -/
theorem t1_f4_01_bkmStarInvariance :
    let D := faithfulGibbsDensity H_d63 hH_d63_sa hZ_d63_pos
    let hpow := continuous_faithfulGibbsDensity_rpow H_d63 hH_d63_sa hZ_d63_pos
    let E01 : GibbsOperator 2 := matrixOp !![0, 1; 0, 0]
    D.bkmRealBilinForm hpow (star A_swap) (star B_tilt) = D.bkmRealBilinForm hpow A_swap B_tilt ∧
      D.bkmRealBilinForm hpow (star E01) (star B_tilt) = D.bkmRealBilinForm hpow E01 B_tilt ∧
      centeredBKMRealCovariance D hpow (star E01) (star B_tilt) =
        centeredBKMRealCovariance D hpow E01 B_tilt := by
  intro D hpow E01
  exact ⟨bkmRealBilinForm_star D hpow A_swap B_tilt,
    bkmRealBilinForm_star D hpow E01 B_tilt,
    centeredBKMRealCovariance_star D hpow E01 B_tilt⟩

private lemma matrixOp_ne_scalarGauge {n : ℕ} [Nonempty (Fin n)] (X : GibbsOperator n)
    (i j : Fin n) (hij : i ≠ j) (h0 : matrixOfOp X i j ≠ 0) :
    X ∉ scalarGauge n := by
  intro hmem
  obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp hmem
  have hm := congrArg (fun Z : GibbsOperator n => matrixOfOp Z i j) hr
  rw [matrixOfOp_real_smul, matrixOfOp_one_eq] at hm
  simp only [Matrix.smul_apply, Matrix.one_apply, hij, ↓reduceIte, smul_zero] at hm
  exact h0 hm.symm

private lemma matrixOfOp_tiltOp2 :
    matrixOfOp tiltOp2 = InfoGeometry.Physics.KleinBottleSewingExact.tilt2 :=
  matrixOfOp_matrixOp _

private lemma matrixOfOp_A_swap :
    matrixOfOp A_swap = swapMatrix :=
  matrixOfOp_matrixOp _

private lemma matrixOfOp_B_tilt :
    matrixOfOp B_tilt = tiltedMatrix :=
  matrixOfOp_matrixOp _

private lemma matrixOfOp_H_d63 :
    matrixOfOp H_d63 = d63TiltedAmplitude :=
  matrixOfOp_matrixOp _

private lemma centeredBKMRealCovariance_self_pos_of_not_scalarGauge
    {n : ℕ} [NeZero n] [Nonempty (Fin n)]
    {H : GibbsOperator n} (hH : IsSelfAdjoint H) (hZ : 0 < gibbsPartitionReal H)
    (X : GibbsOperator n) (hX : X ∉ scalarGauge n) :
    0 < centeredBKMRealCovariance (faithfulGibbsDensity H hH hZ)
      (continuous_faithfulGibbsDensity_rpow H hH hZ) X X := by
  let D := faithfulGibbsDensity H hH hZ
  let hpow := continuous_faithfulGibbsDensity_rpow H hH hZ
  rw [centeredBKMRealCovariance_self, D.bkmRealBilinForm_apply]
  exact D.kuboMoriPairing_self_re_pos (centeredStatistic D X) hpow
    fun h0 => hX ((centeredStatistic_eq_zero_iff D hpow X).mp h0)

private lemma exp_real_smul_of_sq_one
    (J : FiniteOperatorAlgebra 2) (hJ : J * J = 1) (x : ℝ) :
    NormedSpace.exp (x • J) =
      Real.cosh x • (1 : FiniteOperatorAlgebra 2) + Real.sinh x • J := by
  let f : ℝ → FiniteOperatorAlgebra 2 := fun s =>
    (Real.cosh s • (1 : FiniteOperatorAlgebra 2) + Real.sinh s • J) *
      NormedSpace.exp ((-s) • J)
  have hf_deriv : ∀ s : ℝ, HasDerivAt f 0 s := fun s => by
    have h1 : HasDerivAt (fun u : ℝ => NormedSpace.exp ((-u) • J))
        (-(J * NormedSpace.exp ((-s) • J))) s := by
      have hexp := (hasStrictDerivAt_exp_smul_const' (-J) s).hasDerivAt
      have hfun : (fun u : ℝ => NormedSpace.exp (u • (-J))) =
          (fun u : ℝ => NormedSpace.exp ((-u) • J)) := by
        funext u; rw [smul_neg, ← neg_smul]
      rw [hfun] at hexp
      exact hexp.congr_deriv (ContinuousLinearMap.ext fun v => by simp [smul_neg, ← neg_smul])
    have h2 : HasDerivAt
        (fun u : ℝ => Real.cosh u • (1 : FiniteOperatorAlgebra 2) + Real.sinh u • J)
        (Real.sinh s • (1 : FiniteOperatorAlgebra 2) + Real.cosh s • J) s :=
      ((Real.hasDerivAt_cosh s).smul_const (1 : FiniteOperatorAlgebra 2)).add
        ((Real.hasDerivAt_sinh s).smul_const J)
    refine (h2.mul h1).congr_deriv ?_
    have hmul_J : (Real.cosh s • (1 : FiniteOperatorAlgebra 2) + Real.sinh s • J) * J =
        Real.cosh s • J + Real.sinh s • (1 : FiniteOperatorAlgebra 2) := by
      simp only [add_mul, real_smul_eq_complex_smul, smul_mul_assoc, one_mul, hJ]
    have hneg_mul : (Real.cosh s • (1 : FiniteOperatorAlgebra 2) + Real.sinh s • J) *
        (-(J * NormedSpace.exp ((-s) • J))) =
        -((Real.cosh s • (1 : FiniteOperatorAlgebra 2) + Real.sinh s • J) * J *
          NormedSpace.exp ((-s) • J)) :=
      ContinuousLinearMap.ext fun v => by simp [add_comm]
    rw [hneg_mul, hmul_J, add_mul, add_mul]
    abel
  have hf_const : f x = f 0 :=
    is_const_of_deriv_eq_zero (fun s => (hf_deriv s).differentiableAt)
      (fun s => (hf_deriv s).deriv) x 0
  have hf0 : f 0 = 1 := by
    dsimp [f]
    have hz : (0 : ℝ) • J = 0 := zero_smul ℝ J
    rw [Real.cosh_zero, Real.sinh_zero, neg_zero, one_smul, hz, add_zero, NormedSpace.exp_zero,
      mul_one]
  calc NormedSpace.exp (x • J)
      = 1 * NormedSpace.exp (x • J) := (one_mul _).symm
    _ = f x * NormedSpace.exp (x • J) := by rw [hf_const, hf0]
    _ = (Real.cosh x • (1 : FiniteOperatorAlgebra 2) + Real.sinh x • J) *
          (NormedSpace.exp ((-x) • J) * NormedSpace.exp (x • J)) := by
        dsimp [f]; rw [mul_assoc]
    _ = Real.cosh x • (1 : FiniteOperatorAlgebra 2) + Real.sinh x • J := by
        simp only [real_smul_eq_complex_smul, Complex.ofReal_neg]
        have hc : Commute ((-↑x : ℂ) • J) ((↑x : ℂ) • J) :=
          (Commute.refl J).smul_left (-↑x : ℂ) |>.smul_right (↑x : ℂ)
        have hzero : (-↑x : ℂ) • J + (↑x : ℂ) • J = 0 :=
          ContinuousLinearMap.ext fun v => by simp
        rw [← NormedSpace.exp_add_of_commute hc, hzero, NormedSpace.exp_zero, mul_one]

private lemma exp_real_smul_tiltOp2 (x : ℝ) :
    NormedSpace.exp (x • tiltOp2) =
      Real.cosh x • (1 : FiniteOperatorAlgebra 2) + Real.sinh x • tiltOp2 :=
  exp_real_smul_of_sq_one tiltOp2 tiltOp2_sq x

private lemma exp_real_smul_one (x : ℝ) :
    NormedSpace.exp (x • (1 : FiniteOperatorAlgebra 2)) =
      Real.exp x • (1 : FiniteOperatorAlgebra 2) := by
  let g : ℝ → FiniteOperatorAlgebra 2 := fun s =>
    (Real.exp s • (1 : FiniteOperatorAlgebra 2)) *
      NormedSpace.exp ((-s) • (1 : FiniteOperatorAlgebra 2))
  have hg_deriv : ∀ s : ℝ, HasDerivAt g 0 s := fun s => by
    have h1 : HasDerivAt (fun u : ℝ => NormedSpace.exp ((-u) • (1 : FiniteOperatorAlgebra 2)))
        (-((1 : FiniteOperatorAlgebra 2) *
          NormedSpace.exp ((-s) • (1 : FiniteOperatorAlgebra 2)))) s := by
      have hexp := (hasStrictDerivAt_exp_smul_const' (-(1 : FiniteOperatorAlgebra 2)) s).hasDerivAt
      have hfun : (fun u : ℝ => NormedSpace.exp (u • -(1 : FiniteOperatorAlgebra 2))) =
          (fun u : ℝ => NormedSpace.exp ((-u) • (1 : FiniteOperatorAlgebra 2))) := by
        funext u; rw [smul_neg, ← neg_smul]
      rw [hfun] at hexp
      exact hexp.congr_deriv (ContinuousLinearMap.ext fun v => by simp [smul_neg, ← neg_smul])
    have h2 : HasDerivAt (fun u : ℝ => Real.exp u • (1 : FiniteOperatorAlgebra 2))
        (Real.exp s • (1 : FiniteOperatorAlgebra 2)) s :=
      (Real.hasDerivAt_exp s).smul_const (1 : FiniteOperatorAlgebra 2)
    refine (h2.mul h1).congr_deriv ?_
    have hneg_mul : (Real.exp s • (1 : FiniteOperatorAlgebra 2)) *
        (-((1 : FiniteOperatorAlgebra 2) * NormedSpace.exp ((-s) • (1 : FiniteOperatorAlgebra 2)))) =
        -(Real.exp s • (1 : FiniteOperatorAlgebra 2) *
          NormedSpace.exp ((-s) • (1 : FiniteOperatorAlgebra 2))) :=
      ContinuousLinearMap.ext fun v => by simp
    rw [hneg_mul, add_neg_cancel]
  have hg_const : g x = g 0 :=
    is_const_of_deriv_eq_zero (fun s => (hg_deriv s).differentiableAt)
      (fun s => (hg_deriv s).deriv) x 0
  have hg0 : g 0 = 1 := by
    dsimp [g]
    have hz : (0 : ℝ) • (1 : FiniteOperatorAlgebra 2) = 0 :=
      zero_smul ℝ (1 : FiniteOperatorAlgebra 2)
    rw [Real.exp_zero, neg_zero, one_smul, hz, NormedSpace.exp_zero, mul_one]
  calc NormedSpace.exp (x • (1 : FiniteOperatorAlgebra 2))
      = 1 * NormedSpace.exp (x • (1 : FiniteOperatorAlgebra 2)) := (one_mul _).symm
    _ = g x * NormedSpace.exp (x • (1 : FiniteOperatorAlgebra 2)) := by rw [hg_const, hg0]
    _ = (Real.exp x • (1 : FiniteOperatorAlgebra 2)) *
          (NormedSpace.exp ((-x) • (1 : FiniteOperatorAlgebra 2)) *
            NormedSpace.exp (x • (1 : FiniteOperatorAlgebra 2))) := by
        dsimp [g]; rw [mul_assoc]
    _ = Real.exp x • (1 : FiniteOperatorAlgebra 2) := by
        simp only [real_smul_eq_complex_smul, Complex.ofReal_neg]
        have hc : Commute ((-↑x : ℂ) • (1 : FiniteOperatorAlgebra 2))
            ((↑x : ℂ) • (1 : FiniteOperatorAlgebra 2)) :=
          (Commute.refl (1 : FiniteOperatorAlgebra 2)).smul_left (-↑x : ℂ) |>.smul_right (↑x : ℂ)
        have hzero : (-↑x : ℂ) • (1 : FiniteOperatorAlgebra 2) +
            (↑x : ℂ) • (1 : FiniteOperatorAlgebra 2) = 0 :=
          ContinuousLinearMap.ext fun v => by simp
        rw [← NormedSpace.exp_add_of_commute hc, hzero, NormedSpace.exp_zero, mul_one]

private lemma tanh_pos_of_pos {x : ℝ} (hx : 0 < x) : 0 < Real.tanh x := by
  rw [Real.tanh_eq_sinh_div_cosh]
  exact div_pos (Real.sinh_pos_iff.mpr hx) (Real.cosh_pos x)

private lemma A_swap_sq : A_swap * A_swap = 1 := by
  rw [← switchOp2_eq_A_swap]
  exact switchOp2_sq

private lemma exp_real_smul_A_swap (x : ℝ) :
    NormedSpace.exp (x • A_swap) =
      Real.cosh x • (1 : FiniteOperatorAlgebra 2) + Real.sinh x • A_swap :=
  exp_real_smul_of_sq_one A_swap A_swap_sq x

private lemma H_d63_rho_eq :
    (faithfulGibbsDensity H_d63 hH_d63_sa hZ_d63_pos).rho =
      (1 / 2 : ℝ) • (1 : FiniteOperatorAlgebra 2) +
        (Real.tanh (Real.sqrt 2) / (2 * Real.sqrt 2)) • H_d63 := by
  let r : ℝ := Real.sqrt 2
  have hr_pos : 0 < r := Real.sqrt_pos.mpr (by norm_num)
  have hr_ne : r ≠ 0 := ne_of_gt hr_pos
  have hr_sq : r * r = 2 := Real.mul_self_sqrt (by norm_num)
  let J : FiniteOperatorAlgebra 2 := r⁻¹ • H_d63
  have hJ_sq : J * J = 1 := by
    apply matrixOfOp_injective
    dsimp only [J]
    rw [matrixOfOp_mul_eq, matrixOfOp_real_smul, matrixOfOp_H_d63, matrixOfOp_one_eq]
    ext i j; fin_cases i <;> fin_cases j <;>
      · simp only [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul, d63TiltedAmplitude,
          Matrix.one_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val_zero,
          Matrix.cons_val_one, Fin.isValue]
        norm_num
        try (apply Complex.ext <;> (simp; try (field_simp [hr_ne]; linarith [hr_sq])))
  have hH_eq : H_d63 = r • J := by
    dsimp only [J]
    rw [smul_smul, mul_inv_cancel₀ hr_ne, one_smul]
  have hexp : NormedSpace.exp H_d63 =
      Real.cosh r • (1 : FiniteOperatorAlgebra 2) + Real.sinh r • J := by
    conv_lhs => rw [hH_eq]
    exact exp_real_smul_of_sq_one J hJ_sq r
  have htr1 : finiteOperatorTrace (1 : FiniteOperatorAlgebra 2) = 2 := by
    change Matrix.trace (matrixOfOp (1 : FiniteOperatorAlgebra 2)) = 2
    rw [matrixOfOp_one_eq]
    norm_num [Matrix.trace, Matrix.diag, Fin.sum_univ_two]
  have htr_H : finiteOperatorTrace H_d63 = 0 := by
    change Matrix.trace (matrixOfOp H_d63) = 0
    rw [matrixOfOp_H_d63]
    norm_num [d63TiltedAmplitude, Matrix.trace, Matrix.diag, Fin.sum_univ_two]
  have htr_J : finiteOperatorTrace J = 0 := by
    change finiteOperatorTrace (r⁻¹ • H_d63) = 0
    rw [real_smul_eq_complex_smul, ← finiteOperatorTraceLinear_apply, _root_.map_smul,
      finiteOperatorTraceLinear_apply, htr_H, smul_zero]
  have hZ_eq : gibbsPartitionReal H_d63 = 2 * Real.cosh r := by
    have htr : tracedExponential H_d63 = ((2 * Real.cosh r : ℝ) : ℂ) := by
      unfold tracedExponential
      rw [hexp, real_smul_eq_complex_smul, real_smul_eq_complex_smul,
        (finiteOperatorTraceCLM 2).map_add, (finiteOperatorTraceCLM 2).map_smul,
        (finiteOperatorTraceCLM 2).map_smul]
      change (Real.cosh r : ℂ) • finiteOperatorTrace 1 + (Real.sinh r : ℂ) • finiteOperatorTrace J = _
      rw [htr1, htr_J, smul_eq_mul, smul_eq_mul, mul_zero, add_zero]
      push_cast; ring
    exact congrArg Complex.re htr
  erw [faithfulGibbsDensity_rho_eq_normalizedExponential]
  unfold normalizedExponential
  rw [tracedExponential_eq_gibbsPartitionReal H_d63 hH_d63_sa, hZ_eq, hexp]
  have hcosh_ne : Real.cosh r ≠ 0 := ne_of_gt (Real.cosh_pos r)
  have hinv_smul : ∀ (c : ℝ) (X : GibbsOperator 2), ((c : ℂ)⁻¹) • X = (c⁻¹ : ℝ) • X := by
    intro c X
    rw [← Complex.ofReal_inv, ← real_smul_eq_complex_smul]
  rw [hinv_smul (2 * Real.cosh r), smul_add, smul_smul, smul_smul]
  dsimp only [J]
  rw [smul_smul]
  congr 1
  · congr 1
    field_simp [hcosh_ne]
  · congr 1
    rw [show (Real.sqrt 2 : ℝ) = r from rfl, Real.tanh_eq_sinh_div_cosh]
    field_simp [hcosh_ne, hr_ne]

private lemma bkm_H_d63_A_swap_B_tilt_pos :
    let D := faithfulGibbsDensity H_d63 hH_d63_sa hZ_d63_pos
    let hpow := continuous_faithfulGibbsDensity_rpow H_d63 hH_d63_sa hZ_d63_pos
    0 < D.bkmRealBilinForm hpow A_swap B_tilt := by
  intro D hpow
  have hB_decomp : B_tilt =
      (1 / 2 : ℝ) • (1 : GibbsOperator 2) + (1 / 2 : ℝ) • H_d63 + (1 / 2 : ℝ) • A_swap := by
    apply matrixOfOp_injective
    rw [matrixOfOp_add, matrixOfOp_add, matrixOfOp_real_smul, matrixOfOp_real_smul,
      matrixOfOp_real_smul, matrixOfOp_one_eq, matrixOfOp_B_tilt, matrixOfOp_H_d63,
      matrixOfOp_A_swap]
    ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [tiltedMatrix, d63TiltedAmplitude, swapMatrix]
  have hterm1 : D.bkmRealBilinForm hpow A_swap 1 =
      Real.tanh (Real.sqrt 2) / Real.sqrt 2 := by
    rw [bkmRealBilinForm_one_right D hpow A_swap]
    unfold expectationReal
    rw [H_d63_rho_eq, add_mul, real_smul_eq_complex_smul, real_smul_eq_complex_smul,
      smul_mul_assoc, smul_mul_assoc, one_mul, ← finiteOperatorTraceLinear_apply,
      _root_.map_add, _root_.map_smul, _root_.map_smul, finiteOperatorTraceLinear_apply,
      finiteOperatorTraceLinear_apply]
    have htrA : finiteOperatorTrace A_swap = 0 := by
      change Matrix.trace (matrixOfOp A_swap) = 0
      rw [matrixOfOp_A_swap]
      norm_num [swapMatrix, Matrix.trace, Matrix.diag, Fin.sum_univ_two]
    have htrHA : finiteOperatorTrace (H_d63 * A_swap) = 2 := by
      change Matrix.trace (matrixOfOp (H_d63 * A_swap)) = 2
      rw [matrixOfOp_mul_eq, matrixOfOp_H_d63, matrixOfOp_A_swap]
      norm_num [d63TiltedAmplitude, swapMatrix, Matrix.trace, Matrix.diag,
        Matrix.mul_apply, Fin.sum_univ_two]
    rw [htrA, htrHA, smul_zero, zero_add, smul_eq_mul, mul_comm, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im]
    have hr_ne : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
    simp only [Complex.re_ofNat, Complex.im_ofNat, mul_zero, sub_zero]
    field_simp [hr_ne]
  have hterm1_pos : 0 < D.bkmRealBilinForm hpow A_swap 1 := by
    rw [hterm1]
    exact div_pos (tanh_pos_of_pos (Real.sqrt_pos.mpr (by norm_num)))
      (Real.sqrt_pos.mpr (by norm_num))
  have hcomm_H_rho : Commute H_d63 D.rho := by
    change Commute H_d63 (faithfulGibbsDensity H_d63 hH_d63_sa hZ_d63_pos).rho
    rw [H_d63_rho_eq, real_smul_eq_complex_smul, real_smul_eq_complex_smul]
    exact (Commute.one_right H_d63).smul_right _ |>.add_right ((Commute.refl H_d63).smul_right _)
  have hcomm_H_rpow : ∀ t : ℝ, Commute H_d63 (D.rpow t) := fun t => by
    unfold FaithfulDensityOperator.rpow
    change Commute H_d63 (D.rho ^ t)
    rw [CFC.rpow_eq_cfc_real D.strictlyPositive.nonneg]
    exact (hcomm_H_rho.symm.cfc_real (fun x : ℝ => x ^ t)).symm
  have hterm2 : D.bkmRealBilinForm hpow A_swap H_d63 = 1 := by
    rw [D.bkmRealBilinForm_apply]
    unfold FaithfulDensityOperator.kuboMoriPairing
    have hInt : IntervalIntegrable (D.kuboMoriIntegrand A_swap H_d63) MeasureTheory.volume 0 1 :=
      (D.continuous_kuboMoriIntegrand_of_continuous_rpow A_swap H_d63 hpow).intervalIntegrable 0 1
    have hre : (∫ s in (0 : ℝ)..1, D.kuboMoriIntegrand A_swap H_d63 s).re =
        ∫ s in (0 : ℝ)..1, (D.kuboMoriIntegrand A_swap H_d63 s).re :=
      (ContinuousLinearMap.intervalIntegral_comp_comm (RCLike.reCLM : ℂ →L[ℝ] ℝ) hInt).symm
    rw [hre]
    have hintegrand : ∀ s : ℝ,
        (D.kuboMoriIntegrand A_swap H_d63 s).re = 1 := fun s => by
      unfold FaithfulDensityOperator.kuboMoriIntegrand
      rw [hA_swap_sa.star_eq]
      have h1 : D.rpow s * A_swap * D.rpow (1 - s) * H_d63 =
          (D.rpow s * A_swap) * (H_d63 * D.rpow (1 - s)) := by
        rw [mul_assoc (D.rpow s * A_swap), (hcomm_H_rpow (1 - s)).eq]
      have h2 : finiteOperatorTrace ((D.rpow s * A_swap) * (H_d63 * D.rpow (1 - s))) =
          finiteOperatorTrace (D.rho * (A_swap * H_d63)) := by
        rw [finiteOperatorTrace_mul_comm (D.rpow s * A_swap) (H_d63 * D.rpow (1 - s))]
        calc finiteOperatorTrace ((H_d63 * D.rpow (1 - s)) * (D.rpow s * A_swap))
            = finiteOperatorTrace (H_d63 * ((D.rpow (1 - s) * D.rpow s) * A_swap)) := by
              simp only [mul_assoc]
          _ = finiteOperatorTrace (H_d63 * (D.rho * A_swap)) := by
              rw [← D.rpow_add (1 - s) s, sub_add_cancel, D.rpow_one]
          _ = finiteOperatorTrace ((D.rho * A_swap) * H_d63) := finiteOperatorTrace_mul_comm _ _
          _ = finiteOperatorTrace (D.rho * (A_swap * H_d63)) := by rw [mul_assoc]
      rw [h1, h2, H_d63_rho_eq, add_mul, real_smul_eq_complex_smul, real_smul_eq_complex_smul,
        smul_mul_assoc, smul_mul_assoc, one_mul, ← finiteOperatorTraceLinear_apply,
        _root_.map_add, _root_.map_smul, _root_.map_smul, finiteOperatorTraceLinear_apply,
        finiteOperatorTraceLinear_apply]
      have htrAH : finiteOperatorTrace (A_swap * H_d63) = 2 := by
        change Matrix.trace (matrixOfOp (A_swap * H_d63)) = 2
        rw [matrixOfOp_mul_eq, matrixOfOp_A_swap, matrixOfOp_H_d63]
        norm_num [d63TiltedAmplitude, swapMatrix, Matrix.trace, Matrix.diag,
          Matrix.mul_apply, Fin.sum_univ_two]
      have htrHAH : finiteOperatorTrace (H_d63 * (A_swap * H_d63)) = 0 := by
        change Matrix.trace (matrixOfOp (H_d63 * (A_swap * H_d63))) = 0
        rw [matrixOfOp_mul_eq, matrixOfOp_mul_eq, matrixOfOp_H_d63, matrixOfOp_A_swap]
        norm_num [d63TiltedAmplitude, swapMatrix, Matrix.trace, Matrix.diag,
          Matrix.mul_apply, Fin.sum_univ_two]
      rw [htrAH, htrHAH, smul_zero, add_zero]
      simp
    simp_rw [hintegrand]
    simp
  have hA_ne : A_swap ≠ 0 := by rw [← switchOp2_eq_A_swap]; exact switchOp2_ne_zero
  have hterm3_pos : 0 < D.bkmRealBilinForm hpow A_swap A_swap :=
    (D.bkmRealBilinForm_self_pos_iff hpow A_swap).mpr hA_ne
  rw [hB_decomp, (D.bkmRealBilinForm hpow A_swap).map_add,
    (D.bkmRealBilinForm hpow A_swap).map_add,
    (D.bkmRealBilinForm hpow A_swap).map_smul,
    (D.bkmRealBilinForm hpow A_swap).map_smul,
    (D.bkmRealBilinForm hpow A_swap).map_smul,
    smul_eq_mul, smul_eq_mul, smul_eq_mul, hterm2]
  linarith

private lemma cbkm_H_d63_A_swap_B_tilt_pos :
    let D := faithfulGibbsDensity H_d63 hH_d63_sa hZ_d63_pos
    let hpow := continuous_faithfulGibbsDensity_rpow H_d63 hH_d63_sa hZ_d63_pos
    0 < centeredBKMRealCovariance D hpow A_swap B_tilt := by
  intro D hpow
  have hB_decomp : B_tilt =
      (1 / 2 : ℝ) • (1 : GibbsOperator 2) + (1 / 2 : ℝ) • H_d63 + (1 / 2 : ℝ) • A_swap := by
    apply matrixOfOp_injective
    rw [matrixOfOp_add, matrixOfOp_add, matrixOfOp_real_smul, matrixOfOp_real_smul,
      matrixOfOp_real_smul, matrixOfOp_one_eq, matrixOfOp_B_tilt, matrixOfOp_H_d63,
      matrixOfOp_A_swap]
    ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [tiltedMatrix, d63TiltedAmplitude, swapMatrix]
  have h1_zero : centeredBKMRealCovariance D hpow A_swap 1 = 0 := by
    unfold centeredBKMRealCovariance
    have hc1 : centeredStatistic D (1 : GibbsOperator 2) = 0 :=
      (centeredStatistic_eq_zero_iff D hpow 1).mpr
        (Submodule.mem_span_singleton.mpr ⟨1, one_smul ℝ 1⟩)
    rw [hc1, _root_.map_zero]
  have hcomm_H_rho : Commute H_d63 D.rho := by
    change Commute H_d63 (faithfulGibbsDensity H_d63 hH_d63_sa hZ_d63_pos).rho
    rw [H_d63_rho_eq, real_smul_eq_complex_smul, real_smul_eq_complex_smul]
    exact (Commute.one_right H_d63).smul_right _ |>.add_right ((Commute.refl H_d63).smul_right _)
  have hcomm_H_rpow : ∀ t : ℝ, Commute H_d63 (D.rpow t) := fun t => by
    unfold FaithfulDensityOperator.rpow
    change Commute H_d63 (D.rho ^ t)
    rw [CFC.rpow_eq_cfc_real D.strictlyPositive.nonneg]
    exact (hcomm_H_rho.symm.cfc_real (fun x : ℝ => x ^ t)).symm
  have hcomm_cH_rpow : ∀ t : ℝ, Commute (centeredStatistic D H_d63) (D.rpow t) := fun t => by
    unfold centeredStatistic
    rw [real_smul_eq_complex_smul]
    exact (hcomm_H_rpow t).sub_left ((Commute.one_left _).smul_left _)
  have hexpA : expectationReal D A_swap = Real.tanh (Real.sqrt 2) / Real.sqrt 2 := by
    rw [← bkmRealBilinForm_one_right D hpow A_swap, bkmRealBilinForm_one_right]
    unfold expectationReal
    rw [H_d63_rho_eq, add_mul, real_smul_eq_complex_smul, real_smul_eq_complex_smul,
      smul_mul_assoc, smul_mul_assoc, one_mul, ← finiteOperatorTraceLinear_apply,
      _root_.map_add, _root_.map_smul, _root_.map_smul, finiteOperatorTraceLinear_apply,
      finiteOperatorTraceLinear_apply]
    have htrA : finiteOperatorTrace A_swap = 0 := by
      change Matrix.trace (matrixOfOp A_swap) = 0
      rw [matrixOfOp_A_swap]
      norm_num [swapMatrix, Matrix.trace, Matrix.diag, Fin.sum_univ_two]
    have htrHA : finiteOperatorTrace (H_d63 * A_swap) = 2 := by
      change Matrix.trace (matrixOfOp (H_d63 * A_swap)) = 2
      rw [matrixOfOp_mul_eq, matrixOfOp_H_d63, matrixOfOp_A_swap]
      norm_num [d63TiltedAmplitude, swapMatrix, Matrix.trace, Matrix.diag,
        Matrix.mul_apply, Fin.sum_univ_two]
    rw [htrA, htrHA, smul_zero, zero_add, smul_eq_mul, mul_comm, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im]
    have hr_ne : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
    simp only [Complex.re_ofNat, Complex.im_ofNat, mul_zero, sub_zero]
    field_simp [hr_ne]
  have hexpH : expectationReal D H_d63 = Real.sqrt 2 * Real.tanh (Real.sqrt 2) := by
    unfold expectationReal
    rw [H_d63_rho_eq, add_mul, real_smul_eq_complex_smul, real_smul_eq_complex_smul,
      smul_mul_assoc, smul_mul_assoc, one_mul, ← finiteOperatorTraceLinear_apply,
      _root_.map_add, _root_.map_smul, _root_.map_smul, finiteOperatorTraceLinear_apply,
      finiteOperatorTraceLinear_apply]
    have htrH : finiteOperatorTrace H_d63 = 0 := by
      change Matrix.trace (matrixOfOp H_d63) = 0
      rw [matrixOfOp_H_d63]
      norm_num [d63TiltedAmplitude, Matrix.trace, Matrix.diag, Fin.sum_univ_two]
    have htrHH : finiteOperatorTrace (H_d63 * H_d63) = 4 := by
      change Matrix.trace (matrixOfOp (H_d63 * H_d63)) = 4
      rw [matrixOfOp_mul_eq, matrixOfOp_H_d63]
      norm_num [d63TiltedAmplitude, Matrix.trace, Matrix.diag,
        Matrix.mul_apply, Fin.sum_univ_two]
    rw [htrH, htrHH, smul_zero, zero_add, smul_eq_mul, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im]
    have hr_ne : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
    simp only [Complex.re_ofNat, Complex.im_ofNat, mul_zero, sub_zero]
    field_simp [hr_ne]
    rw [Real.sq_sqrt (by norm_num)]
    ring
  have hstar_cA : star (centeredStatistic D A_swap) = centeredStatistic D A_swap := by
    rw [← centeredStatistic_star D A_swap, hA_swap_sa.star_eq]
  have h2_val : centeredBKMRealCovariance D hpow A_swap H_d63 =
      1 - (Real.tanh (Real.sqrt 2)) ^ 2 := by
    unfold centeredBKMRealCovariance
    rw [D.bkmRealBilinForm_apply]
    unfold FaithfulDensityOperator.kuboMoriPairing
    have hInt : IntervalIntegrable
        (D.kuboMoriIntegrand (centeredStatistic D A_swap) (centeredStatistic D H_d63))
        MeasureTheory.volume 0 1 :=
      (D.continuous_kuboMoriIntegrand_of_continuous_rpow _ _ hpow).intervalIntegrable 0 1
    have hre : (∫ s in (0 : ℝ)..1,
          D.kuboMoriIntegrand (centeredStatistic D A_swap) (centeredStatistic D H_d63) s).re =
        ∫ s in (0 : ℝ)..1,
          (D.kuboMoriIntegrand (centeredStatistic D A_swap) (centeredStatistic D H_d63) s).re :=
      (ContinuousLinearMap.intervalIntegral_comp_comm (RCLike.reCLM : ℂ →L[ℝ] ℝ) hInt).symm
    rw [hre]
    have hconst : ∀ s : ℝ,
        (D.kuboMoriIntegrand (centeredStatistic D A_swap) (centeredStatistic D H_d63) s).re =
          1 - (Real.tanh (Real.sqrt 2)) ^ 2 := fun s => by
      unfold FaithfulDensityOperator.kuboMoriIntegrand
      rw [hstar_cA]
      have h1 : D.rpow s * centeredStatistic D A_swap * D.rpow (1 - s) * centeredStatistic D H_d63 =
          (D.rpow s * centeredStatistic D A_swap) * (centeredStatistic D H_d63 * D.rpow (1 - s)) := by
        rw [mul_assoc (D.rpow s * centeredStatistic D A_swap), (hcomm_cH_rpow (1 - s)).eq]
      have h2 : finiteOperatorTrace
            ((D.rpow s * centeredStatistic D A_swap) * (centeredStatistic D H_d63 * D.rpow (1 - s))) =
          finiteOperatorTrace (D.rho * (centeredStatistic D A_swap * centeredStatistic D H_d63)) := by
        rw [finiteOperatorTrace_mul_comm (D.rpow s * centeredStatistic D A_swap)
          (centeredStatistic D H_d63 * D.rpow (1 - s))]
        calc finiteOperatorTrace
              ((centeredStatistic D H_d63 * D.rpow (1 - s)) * (D.rpow s * centeredStatistic D A_swap))
            = finiteOperatorTrace
                (centeredStatistic D H_d63 * ((D.rpow (1 - s) * D.rpow s) * centeredStatistic D A_swap)) := by
              simp only [mul_assoc]
          _ = finiteOperatorTrace
                (centeredStatistic D H_d63 * (D.rho * centeredStatistic D A_swap)) := by
              rw [← D.rpow_add (1 - s) s, sub_add_cancel, D.rpow_one]
          _ = finiteOperatorTrace
                ((D.rho * centeredStatistic D A_swap) * centeredStatistic D H_d63) :=
              finiteOperatorTrace_mul_comm _ _
          _ = finiteOperatorTrace
                (D.rho * (centeredStatistic D A_swap * centeredStatistic D H_d63)) := by
              rw [mul_assoc]
      have hexpand : centeredStatistic D A_swap * centeredStatistic D H_d63 =
          A_swap * H_d63 - (expectationReal D H_d63 : ℂ) • A_swap -
            (expectationReal D A_swap : ℂ) • H_d63 +
            (expectationReal D A_swap * expectationReal D H_d63 : ℂ) • 1 := by
        simp only [centeredStatistic, real_smul_eq_complex_smul, sub_mul, mul_sub, smul_sub,
          smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
        rw [smul_smul, mul_comm (expectationReal D H_d63 : ℂ) (expectationReal D A_swap : ℂ)]
        abel
      rw [h1, h2, hexpand, mul_add, mul_sub, mul_sub, mul_smul_comm, mul_smul_comm,
        mul_smul_comm, mul_one, ← finiteOperatorTraceLinear_apply,
        _root_.map_add, _root_.map_sub, _root_.map_sub, _root_.map_smul, _root_.map_smul,
        _root_.map_smul, finiteOperatorTraceLinear_apply, finiteOperatorTraceLinear_apply,
        finiteOperatorTraceLinear_apply, finiteOperatorTraceLinear_apply]
      have htr1 : finiteOperatorTrace D.rho = 1 := D.trace_one
      have htrDA : finiteOperatorTrace (D.rho * A_swap) = (expectationReal D A_swap : ℂ) := by
        rw [hexpA, H_d63_rho_eq, add_mul, real_smul_eq_complex_smul, real_smul_eq_complex_smul,
          smul_mul_assoc, smul_mul_assoc, one_mul, ← finiteOperatorTraceLinear_apply,
          _root_.map_add, _root_.map_smul, _root_.map_smul, finiteOperatorTraceLinear_apply,
          finiteOperatorTraceLinear_apply]
        have htrA0 : finiteOperatorTrace A_swap = 0 := by
          change Matrix.trace (matrixOfOp A_swap) = 0
          rw [matrixOfOp_A_swap]; norm_num [swapMatrix, Matrix.trace, Matrix.diag, Fin.sum_univ_two]
        have htrHA2 : finiteOperatorTrace (H_d63 * A_swap) = 2 := by
          change Matrix.trace (matrixOfOp (H_d63 * A_swap)) = 2
          rw [matrixOfOp_mul_eq, matrixOfOp_H_d63, matrixOfOp_A_swap]
          norm_num [d63TiltedAmplitude, swapMatrix, Matrix.trace, Matrix.diag,
            Matrix.mul_apply, Fin.sum_univ_two]
        rw [htrA0, htrHA2, smul_zero, zero_add, smul_eq_mul]
        have hr_ne : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
        push_cast; field_simp [hr_ne]
      have htrDH : finiteOperatorTrace (D.rho * H_d63) = (expectationReal D H_d63 : ℂ) := by
        rw [hexpH, H_d63_rho_eq, add_mul, real_smul_eq_complex_smul, real_smul_eq_complex_smul,
          smul_mul_assoc, smul_mul_assoc, one_mul, ← finiteOperatorTraceLinear_apply,
          _root_.map_add, _root_.map_smul, _root_.map_smul, finiteOperatorTraceLinear_apply,
          finiteOperatorTraceLinear_apply]
        have htrH0 : finiteOperatorTrace H_d63 = 0 := by
          change Matrix.trace (matrixOfOp H_d63) = 0
          rw [matrixOfOp_H_d63]; norm_num [d63TiltedAmplitude, Matrix.trace, Matrix.diag, Fin.sum_univ_two]
        have htrHH4 : finiteOperatorTrace (H_d63 * H_d63) = 4 := by
          change Matrix.trace (matrixOfOp (H_d63 * H_d63)) = 4
          rw [matrixOfOp_mul_eq, matrixOfOp_H_d63]
          norm_num [d63TiltedAmplitude, Matrix.trace, Matrix.diag, Matrix.mul_apply, Fin.sum_univ_two]
        rw [htrH0, htrHH4, smul_zero, zero_add, smul_eq_mul]
        have hr_ne : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
        have hr_sq : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
        push_cast; field_simp [hr_ne]; ring_nf; rw [show (Real.sqrt 2 : ℂ) ^ 2 = 2 from by
          rw [sq, ← Complex.ofReal_mul, hr_sq]; norm_num]; ring
      have htrDAH : finiteOperatorTrace (D.rho * (A_swap * H_d63)) = 1 := by
        rw [H_d63_rho_eq, add_mul, real_smul_eq_complex_smul, real_smul_eq_complex_smul,
          smul_mul_assoc, smul_mul_assoc, one_mul, ← finiteOperatorTraceLinear_apply,
          _root_.map_add, _root_.map_smul, _root_.map_smul, finiteOperatorTraceLinear_apply,
          finiteOperatorTraceLinear_apply]
        have htrAH : finiteOperatorTrace (A_swap * H_d63) = 2 := by
          change Matrix.trace (matrixOfOp (A_swap * H_d63)) = 2
          rw [matrixOfOp_mul_eq, matrixOfOp_A_swap, matrixOfOp_H_d63]
          norm_num [d63TiltedAmplitude, swapMatrix, Matrix.trace, Matrix.diag,
            Matrix.mul_apply, Fin.sum_univ_two]
        have htrHAH : finiteOperatorTrace (H_d63 * (A_swap * H_d63)) = 0 := by
          change Matrix.trace (matrixOfOp (H_d63 * (A_swap * H_d63))) = 0
          rw [matrixOfOp_mul_eq, matrixOfOp_mul_eq, matrixOfOp_H_d63, matrixOfOp_A_swap]
          norm_num [d63TiltedAmplitude, swapMatrix, Matrix.trace, Matrix.diag,
            Matrix.mul_apply, Fin.sum_univ_two]
        rw [htrAH, htrHAH, smul_zero, add_zero]; simp
      rw [htrDAH, htrDA, htrDH, htr1]
      simp only [smul_eq_mul, mul_one, Complex.add_re, Complex.sub_re, Complex.one_re,
        Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
      rw [hexpA, hexpH]
      have hr_ne : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
      field_simp [hr_ne]
      ring
    simp_rw [hconst]
    simp
  have h2_pos : 0 < centeredBKMRealCovariance D hpow A_swap H_d63 := by
    rw [h2_val]
    have ht1 : Real.tanh (Real.sqrt 2) < 1 := Real.tanh_lt_one (Real.sqrt 2)
    have ht0 : 0 < Real.tanh (Real.sqrt 2) := tanh_pos_of_pos (Real.sqrt_pos.mpr (by norm_num))
    nlinarith
  have hA_not_gauge : A_swap ∉ scalarGauge 2 := by
    apply matrixOp_ne_scalarGauge A_swap 0 1 (by decide)
    rw [matrixOfOp_A_swap]; norm_num [swapMatrix]
  have h3_pos : 0 < centeredBKMRealCovariance D hpow A_swap A_swap :=
    centeredBKMRealCovariance_self_pos_of_not_scalarGauge hH_d63_sa hZ_d63_pos A_swap hA_not_gauge
  rw [hB_decomp, ← centeredBKMRealCovarianceBilin_apply,
    (centeredBKMRealCovarianceBilin D hpow A_swap).map_add,
    (centeredBKMRealCovarianceBilin D hpow A_swap).map_add,
    (centeredBKMRealCovarianceBilin D hpow A_swap).map_smul,
    (centeredBKMRealCovarianceBilin D hpow A_swap).map_smul,
    (centeredBKMRealCovarianceBilin D hpow A_swap).map_smul,
    centeredBKMRealCovarianceBilin_apply, centeredBKMRealCovarianceBilin_apply,
    centeredBKMRealCovarianceBilin_apply, smul_eq_mul, smul_eq_mul, smul_eq_mul, h1_zero]
  linarith

/-- `T1-F4-02`: `starDerivationTimeReversal` equips `finiteCEOnsagerSystem` with `ParityOnsagerSystem` (nonzero dissipation & reversibility). -/
theorem t1_f4_02_starDerivationParitySystem :
    let D := faithfulGibbsDensity H_d63 hH_d63_sa hZ_d63_pos
    let hpow := continuous_faithfulGibbsDensity_rpow H_d63 hH_d63_sa hZ_d63_pos
    let PS := finiteCEParityOnsagerSystem D hpow A_swap A_swap hA_swap_sa hA_swap_sa
    let d1 := innerDerivation tiltOp2
    let d2 := innerDerivation (tiltOp2 + tiltOp2 * switchOp2)
    PS.T = starDerivationTimeReversal 2 ∧
      PS.T.op (PS.T.op d1) = d1 ∧
      PS.dissipative (PS.T.op d1) (PS.T.op d2) = PS.dissipative d1 d2 ∧
      PS.reversible (PS.T.op d1) (PS.T.op d2) = -PS.reversible d1 d2 ∧
      PS.totalGenerator (PS.T.op d1) (PS.T.op d2) = PS.totalGenerator d2 d1 ∧
      PS.dissipative d1 d1 ≠ 0 ∧
      PS.dissipative d1 d2 ≠ 0 ∧
      PS.reversible d1 d2 ≠ 0 := by
  intro D hpow PS d1 d2
  have hd1A : d1.1 A_swap = (2 : ℝ) • (tiltOp2 * A_swap) := by
    apply matrixOfOp_injective
    change matrixOfOp (tiltOp2 * A_swap - A_swap * tiltOp2) =
      matrixOfOp ((2 : ℝ) • (tiltOp2 * A_swap))
    rw [matrixOfOp_sub_eq, matrixOfOp_mul_eq, matrixOfOp_mul_eq, matrixOfOp_real_smul,
      matrixOfOp_mul_eq, matrixOfOp_tiltOp2, matrixOfOp_A_swap]
    ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [InfoGeometry.Physics.KleinBottleSewingExact.tilt2, swapMatrix,
        Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct]
  have hd2A : d2.1 A_swap = (2 : ℝ) • (tiltOp2 * A_swap) + (2 : ℝ) • tiltOp2 := by
    apply matrixOfOp_injective
    change matrixOfOp ((tiltOp2 + tiltOp2 * switchOp2) * A_swap -
        A_swap * (tiltOp2 + tiltOp2 * switchOp2)) =
      matrixOfOp ((2 : ℝ) • (tiltOp2 * A_swap) + (2 : ℝ) • tiltOp2)
    rw [matrixOfOp_sub_eq, matrixOfOp_mul_eq, matrixOfOp_mul_eq,
      matrixOfOp_add, matrixOfOp_add, matrixOfOp_real_smul, matrixOfOp_real_smul,
      matrixOfOp_mul_eq, matrixOfOp_mul_eq, switchOp2_eq_A_swap,
      matrixOfOp_tiltOp2, matrixOfOp_A_swap]
    ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [InfoGeometry.Physics.KleinBottleSewingExact.tilt2, swapMatrix,
        Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct]
  have h1_not_gauge : d1.1 A_swap ∉ scalarGauge 2 := by
    apply matrixOp_ne_scalarGauge _ 0 1 (by decide)
    rw [hd1A, matrixOfOp_real_smul, matrixOfOp_mul_eq, matrixOfOp_tiltOp2, matrixOfOp_A_swap]
    norm_num [InfoGeometry.Physics.KleinBottleSewingExact.tilt2, swapMatrix,
      Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct]
  have hd11_pos : 0 < PS.dissipative d1 d1 := by
    change 0 < centeredCEBKMForm D hpow A_swap d1 d1
    rw [centeredCEBKMForm_apply]
    exact centeredBKMRealCovariance_self_pos_of_not_scalarGauge hH_d63_sa hZ_d63_pos _ h1_not_gauge
  have h1_star : star ((2 : ℝ) • (tiltOp2 * A_swap)) = -((2 : ℝ) • (tiltOp2 * A_swap)) := by
    apply matrixOfOp_injective
    change matrixOfOp (ContinuousLinearMap.adjoint ((2 : ℝ) • (tiltOp2 * A_swap))) =
      matrixOfOp (-((2 : ℝ) • (tiltOp2 * A_swap)))
    rw [matrixOfOp_adjoint, matrixOfOp_neg_eq, matrixOfOp_real_smul,
      matrixOfOp_mul_eq, matrixOfOp_tiltOp2, matrixOfOp_A_swap]
    ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [Complex.ext_iff, InfoGeometry.Physics.KleinBottleSewingExact.tilt2, swapMatrix,
        Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct]
  have h2_star : star ((2 : ℝ) • tiltOp2) = (2 : ℝ) • tiltOp2 :=
    (isSelfAdjoint_real_smul 2 tiltOp2 tiltOp2_isSelfAdjoint).star_eq
  have hcross_zero : centeredBKMRealCovariance D hpow
      ((2 : ℝ) • (tiltOp2 * A_swap)) ((2 : ℝ) • tiltOp2) = 0 := by
    have hst := centeredBKMRealCovariance_star D hpow
      ((2 : ℝ) • (tiltOp2 * A_swap)) ((2 : ℝ) • tiltOp2)
    rw [h1_star, h2_star, ← centeredBKMRealCovarianceBilin_apply, _root_.map_neg,
      LinearMap.neg_apply, centeredBKMRealCovarianceBilin_apply] at hst
    linarith
  have hd12_pos : 0 < PS.dissipative d1 d2 := by
    change 0 < centeredCEBKMForm D hpow A_swap d1 d2
    rw [centeredCEBKMForm_apply]
    change 0 < centeredBKMRealCovariance D hpow (d1.1 A_swap) (d2.1 A_swap)
    rw [hd2A, ← centeredBKMRealCovarianceBilin_apply, (centeredBKMRealCovarianceBilin D hpow (d1.1 A_swap)).map_add,
      centeredBKMRealCovarianceBilin_apply, centeredBKMRealCovarianceBilin_apply,
      hd1A, hcross_zero, add_zero, ← hd1A]
    exact centeredBKMRealCovariance_self_pos_of_not_scalarGauge hH_d63_sa hZ_d63_pos _ h1_not_gauge
  have hcomm_eq : d1.1 A_swap * d2.1 A_swap - d2.1 A_swap * d1.1 A_swap = (-8 : ℝ) • A_swap := by
    rw [hd1A, hd2A]
    apply matrixOfOp_injective
    rw [matrixOfOp_sub_eq, matrixOfOp_mul_eq, matrixOfOp_mul_eq, matrixOfOp_add,
      matrixOfOp_real_smul, matrixOfOp_real_smul, matrixOfOp_mul_eq,
      matrixOfOp_real_smul, matrixOfOp_tiltOp2, matrixOfOp_A_swap]
    ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [InfoGeometry.Physics.KleinBottleSewingExact.tilt2, swapMatrix,
        Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct]
  have hA_ne : A_swap ≠ 0 := by
    rw [← switchOp2_eq_A_swap]
    exact switchOp2_ne_zero
  have hrev_ne : PS.reversible d1 d2 ≠ 0 := by
    change ceCurvatureBKMProbeForm D hpow A_swap A_swap d1 d2 ≠ 0
    rw [ceCurvatureBKMProbeForm_apply]
    have hcurv : connectionCurvature (realDerivationsLane (GibbsOperator 2))
        (exteriorDerivativeZero (realDerivationsLane (GibbsOperator 2)) A_swap) d1 d2 =
        (-8 : ℝ) • A_swap := by
      rw [connectionCurvature, exteriorDerivativeOne_exteriorDerivativeZero, zero_add]
      exact hcomm_eq
    rw [hcurv, (D.bkmRealBilinForm hpow).map_smul (-8 : ℝ) A_swap,
      LinearMap.smul_apply, smul_eq_mul]
    have hpos : 0 < D.bkmRealBilinForm hpow A_swap A_swap :=
      (D.bkmRealBilinForm_self_pos_iff hpow A_swap).mpr hA_ne
    linarith
  exact ⟨rfl, PS.T.involutive d1, PS.dissipative_T_even d1 d2, PS.reversible_T_odd d1 d2,
    PS.onsager_casimir_master_reciprocity d1 d2, ne_of_gt hd11_pos, ne_of_gt hd12_pos, hrev_ne⟩

/-- `T1-F4-03`: `D.rho`-preserving `*`-automorphism `τ` (`conjStarAlgEquiv 2`) with `τ Q = -Q` yields `ParityOnsagerSystem` with nonzero dissipation and nonzero reversibility. -/
theorem t1_f4_03_autDerivationParitySystem :
    let τ := conjStarAlgEquiv 2
    let H := H_d63
    let a := B_tilt
    let Q := Complex.I • ((2 : ℝ) • switchOp2 + tiltOp2)
    have hτ_H : τ H = H := by
      rw [conjStarAlgEquiv_apply, conjOpFun, show H = H_d63 from rfl, matrixOfOp_H_d63]
      apply matrixOfOp_injective
      rw [matrixOfOp_matrixOp, matrixOfOp_H_d63]
      ext i j; fin_cases i <;> fin_cases j <;> simp [d63TiltedAmplitude]
    have ha : τ a = a := by
      rw [conjStarAlgEquiv_apply, conjOpFun, show a = B_tilt from rfl, matrixOfOp_B_tilt]
      apply matrixOfOp_injective
      rw [matrixOfOp_matrixOp, matrixOfOp_B_tilt]
      ext i j; fin_cases i <;> fin_cases j <;> simp [tiltedMatrix]
    have hQ : τ Q = -Q := by
      apply conjStarAlgEquiv_purelyImaginary_odd ((2 : ℝ) • switchOp2 + tiltOp2)
      rw [_root_.map_add, _root_.map_smul, conj_switchOp2, conj_tiltOp2]
    let D := faithfulGibbsDensity H hH_d63_sa hZ_d63_pos
    let hpow := continuous_faithfulGibbsDensity_rpow H hH_d63_sa hZ_d63_pos
    let hτ_rho := conjStarAlgEquiv_gibbs_fixed H hH_d63_sa hZ_d63_pos hτ_H
    let PS := finiteCEParityOnsagerSystemOfAut τ (conjStarAlgEquiv_involutive (n := 2))
      D hpow hτ_rho (conjStarAlgEquiv_trace_re (n := 2)) a Q ha hQ
    let d1 := innerDerivation tiltOp2
    let d2 := innerDerivation (tiltOp2 + Complex.I • (tiltOp2 * switchOp2))
    τ H = H ∧ τ a = a ∧ τ Q = -Q ∧
      PS.dissipative (PS.T.op d1) (PS.T.op d2) = PS.dissipative d1 d2 ∧
      PS.reversible (PS.T.op d1) (PS.T.op d2) = -PS.reversible d1 d2 ∧
      PS.totalGenerator (PS.T.op d1) (PS.T.op d2) = PS.totalGenerator d2 d1 ∧
      d1.1 a ≠ 0 ∧
      d2.1 a ≠ 0 ∧
      PS.dissipative d1 d2 ≠ 0 ∧
      PS.reversible d1 d2 ≠ 0 := by
  intro τ H a Q hτ_H ha hQ D hpow hτ_rho PS d1 d2
  let X_re : GibbsOperator 2 := (2 : ℝ) • (tiltOp2 * switchOp2)
  let Y_im : GibbsOperator 2 := Complex.I • ((2 : ℝ) • tiltOp2 - switchOp2)
  have hd1_eq : d1.1 a = X_re := by
    apply matrixOfOp_injective
    change matrixOfOp (tiltOp2 * B_tilt - B_tilt * tiltOp2) = matrixOfOp ((2 : ℝ) • (tiltOp2 * switchOp2))
    rw [matrixOfOp_sub_eq, matrixOfOp_mul_eq, matrixOfOp_mul_eq, matrixOfOp_real_smul,
      matrixOfOp_mul_eq, matrixOfOp_tiltOp2, matrixOfOp_B_tilt, switchOp2_eq_A_swap,
      matrixOfOp_A_swap]
    ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [InfoGeometry.Physics.KleinBottleSewingExact.tilt2, tiltedMatrix, swapMatrix,
        Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct]
  have hd2_eq : d2.1 a = X_re + Y_im := by
    apply matrixOfOp_injective
    change matrixOfOp ((tiltOp2 + Complex.I • (tiltOp2 * switchOp2)) * B_tilt -
        B_tilt * (tiltOp2 + Complex.I • (tiltOp2 * switchOp2))) =
      matrixOfOp ((2 : ℝ) • (tiltOp2 * switchOp2) + Complex.I • ((2 : ℝ) • tiltOp2 - switchOp2))
    simp only [matrixOfOp_sub_eq, matrixOfOp_mul_eq, matrixOfOp_add, matrixOfOp_real_smul,
      matrixOfOp_complex_smul, matrixOfOp_tiltOp2, matrixOfOp_B_tilt, switchOp2_eq_A_swap,
      matrixOfOp_A_swap]
    ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [Complex.ext_iff, InfoGeometry.Physics.KleinBottleSewingExact.tilt2,
        tiltedMatrix, swapMatrix, Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct]
  have hd1_ne : d1.1 a ≠ 0 := by
    intro h0
    have hm := congrArg (fun M : GibbsOperator 2 => matrixOfOp M 0 1) h0
    rw [hd1_eq, matrixOfOp_real_smul, matrixOfOp_mul_eq, matrixOfOp_tiltOp2, switchOp2_eq_A_swap,
      matrixOfOp_A_swap, matrixOfOp_zero] at hm
    norm_num [InfoGeometry.Physics.KleinBottleSewingExact.tilt2, swapMatrix,
      Matrix.mul_apply, Fin.sum_univ_two] at hm
  have hd2_ne : d2.1 a ≠ 0 := by
    intro h0
    have hm := congrArg (fun M : GibbsOperator 2 => matrixOfOp M 0 1) h0
    rw [hd2_eq, matrixOfOp_add, matrixOfOp_real_smul, matrixOfOp_complex_smul, matrixOfOp_sub_eq,
      matrixOfOp_real_smul, matrixOfOp_mul_eq, matrixOfOp_tiltOp2, switchOp2_eq_A_swap,
      matrixOfOp_A_swap, matrixOfOp_zero] at hm
    norm_num [Complex.ext_iff, InfoGeometry.Physics.KleinBottleSewingExact.tilt2, swapMatrix,
      Matrix.mul_apply, Fin.sum_univ_two] at hm
  have hX_not_gauge : X_re ∉ scalarGauge 2 := by
    apply matrixOp_ne_scalarGauge X_re 0 1 (by decide)
    rw [matrixOfOp_real_smul, matrixOfOp_mul_eq, matrixOfOp_tiltOp2, switchOp2_eq_A_swap,
      matrixOfOp_A_swap]
    norm_num [InfoGeometry.Physics.KleinBottleSewingExact.tilt2, swapMatrix,
      Matrix.mul_apply, Fin.sum_univ_two]
  have hτ_X : τ X_re = X_re := by
    dsimp only [X_re]
    rw [_root_.map_smul, _root_.map_mul, conj_tiltOp2, conj_switchOp2]
  have hτ_Y : τ Y_im = -Y_im :=
    conjStarAlgEquiv_purelyImaginary_odd ((2 : ℝ) • tiltOp2 - switchOp2)
      (by rw [_root_.map_sub, _root_.map_smul, conj_tiltOp2, conj_switchOp2])
  have hcross_zero : centeredBKMRealCovariance D hpow X_re Y_im = 0 := by
    have hinv := centeredBKMRealCovariance_aut τ D hpow hτ_rho
      (conjStarAlgEquiv_trace_re (n := 2)) X_re Y_im
    rw [hτ_X, hτ_Y, ← centeredBKMRealCovarianceBilin_apply, _root_.map_neg,
      centeredBKMRealCovarianceBilin_apply] at hinv
    linarith
  have hdiss_pos : 0 < PS.dissipative d1 d2 := by
    change 0 < centeredCEBKMForm D hpow a d1 d2
    rw [centeredCEBKMForm_apply]
    change 0 < centeredBKMRealCovariance D hpow (d1.1 a) (d2.1 a)
    rw [hd1_eq, hd2_eq, ← centeredBKMRealCovarianceBilin_apply,
      (centeredBKMRealCovarianceBilin D hpow X_re).map_add X_re Y_im,
      centeredBKMRealCovarianceBilin_apply, centeredBKMRealCovarianceBilin_apply,
      hcross_zero, add_zero]
    exact centeredBKMRealCovariance_self_pos_of_not_scalarGauge hH_d63_sa hZ_d63_pos X_re hX_not_gauge
  have hcomm_eq : d1.1 a * d2.1 a - d2.1 a * d1.1 a = (-4 : ℝ) • Q := by
    rw [hd1_eq, hd2_eq]
    apply matrixOfOp_injective
    dsimp only [X_re, Y_im, Q]
    rw [matrixOfOp_sub_eq, matrixOfOp_mul_eq, matrixOfOp_mul_eq, matrixOfOp_add,
      matrixOfOp_real_smul, matrixOfOp_real_smul, matrixOfOp_complex_smul,
      matrixOfOp_complex_smul, matrixOfOp_sub_eq, matrixOfOp_add,
      matrixOfOp_real_smul, matrixOfOp_real_smul, matrixOfOp_mul_eq,
      matrixOfOp_tiltOp2, switchOp2_eq_A_swap, matrixOfOp_A_swap]
    ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [Complex.ext_iff, InfoGeometry.Physics.KleinBottleSewingExact.tilt2, swapMatrix,
        Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct]
  have hQ_ne : Q ≠ 0 := by
    intro h0
    have hm := congrArg (fun M : GibbsOperator 2 => matrixOfOp M 0 1) h0
    dsimp only [Q] at hm
    rw [matrixOfOp_complex_smul, matrixOfOp_add, matrixOfOp_real_smul, switchOp2_eq_A_swap,
      matrixOfOp_A_swap, matrixOfOp_tiltOp2, matrixOfOp_zero] at hm
    norm_num [Complex.ext_iff, swapMatrix, InfoGeometry.Physics.KleinBottleSewingExact.tilt2] at hm
  have hrev_neg : PS.reversible d1 d2 < 0 := by
    change ceCurvatureBKMProbeForm D hpow a Q d1 d2 < 0
    rw [ceCurvatureBKMProbeForm_apply]
    have hcurv : connectionCurvature (realDerivationsLane (GibbsOperator 2))
        (exteriorDerivativeZero (realDerivationsLane (GibbsOperator 2)) a) d1 d2 =
        (-4 : ℝ) • Q := by
      rw [connectionCurvature, exteriorDerivativeOne_exteriorDerivativeZero, zero_add]
      exact hcomm_eq
    rw [hcurv, (D.bkmRealBilinForm hpow).map_smul (-4 : ℝ) Q,
      LinearMap.smul_apply, smul_eq_mul]
    have hpos : 0 < D.bkmRealBilinForm hpow Q Q :=
      (D.bkmRealBilinForm_self_pos_iff hpow Q).mpr hQ_ne
    linarith
  exact ⟨hτ_H, ha, hQ, PS.dissipative_T_even d1 d2, PS.reversible_T_odd d1 d2,
    PS.onsager_casimir_master_reciprocity d1 d2, hd1_ne, hd2_ne, ne_of_gt hdiss_pos,
    ne_of_lt hrev_neg⟩

/-- `T1-F4-04`: `finiteGibbsCEParityOnsagerSystem` preserves Hessian equality, master reciprocity, nonzero dissipation, and nonzero reversibility. -/
theorem t1_f4_04_finiteGibbsCEParitySystem :
    let P_gibbs := finiteGibbsCEParityOnsagerSystem H_d63 hH_d63_sa hZ_d63_pos A_swap B_tilt
      hA_swap_sa hB_tilt_sa
    let D1 := innerFrechetComplexDeriv (Complex.I • H_d63)
    let D2 := innerFrechetComplexDeriv (Complex.I • tiltOp2 + Complex.I • (tiltOp2 * switchOp2))
    let x1 := finiteCEFrechetDirection D1
    let x2 := finiteCEFrechetDirection D2
    P_gibbs.toOnsagerCasimirSystem =
        finiteGibbsCEOnsagerSystem H_d63 hH_d63_sa hZ_d63_pos A_swap B_tilt ∧
      (secondFDerivLogPartitionReadout H_d63
          (finiteCEOperatorForm 2 A_swap x1) (finiteCEOperatorForm 2 A_swap x2)).re =
        P_gibbs.dissipative x1 x2 ∧
      P_gibbs.totalGenerator (P_gibbs.T.op x1) (P_gibbs.T.op x2) =
        P_gibbs.totalGenerator x2 x1 ∧
      finiteCEOperatorForm 2 A_swap x1 ≠ 0 ∧
      P_gibbs.dissipative x1 x2 ≠ 0 ∧
      P_gibbs.reversible x1 x2 ≠ 0 := by
  intro P_gibbs D1 D2 x1 x2
  have hA1 : IsSelfAdjoint (finiteCEOperatorForm 2 A_swap x1) :=
    isSelfAdjoint_I_smul_comm H_d63 A_swap hH_d63_sa hA_swap_sa
  let X_anti : GibbsOperator 2 := (2 * Complex.I) • tiltOp2
  have hA2_eq : finiteCEOperatorForm 2 A_swap x2 = finiteCEOperatorForm 2 A_swap x1 + X_anti := by
    apply matrixOfOp_injective
    change matrixOfOp ((Complex.I • tiltOp2 + Complex.I • (tiltOp2 * switchOp2)) * A_swap -
        A_swap * (Complex.I • tiltOp2 + Complex.I • (tiltOp2 * switchOp2))) =
      matrixOfOp (((Complex.I • H_d63) * A_swap - A_swap * (Complex.I • H_d63)) +
        (2 * Complex.I) • tiltOp2)
    rw [matrixOfOp_add, matrixOfOp_sub_eq, matrixOfOp_sub_eq,
      matrixOfOp_mul_eq, matrixOfOp_mul_eq, matrixOfOp_mul_eq, matrixOfOp_mul_eq,
      matrixOfOp_add, matrixOfOp_complex_smul, matrixOfOp_complex_smul, matrixOfOp_complex_smul,
      matrixOfOp_complex_smul, matrixOfOp_mul_eq, switchOp2_eq_A_swap,
      matrixOfOp_H_d63, matrixOfOp_A_swap, matrixOfOp_tiltOp2]
    ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [Complex.ext_iff, d63TiltedAmplitude, swapMatrix,
        InfoGeometry.Physics.KleinBottleSewingExact.tilt2, Matrix.mul_apply,
        Fin.sum_univ_two, Matrix.vecMul, dotProduct]
  have hA1_not_gauge : finiteCEOperatorForm 2 A_swap x1 ∉ scalarGauge 2 := by
    apply matrixOp_ne_scalarGauge _ 0 1 (by decide)
    change matrixOfOp ((Complex.I • H_d63) * A_swap - A_swap * (Complex.I • H_d63)) 0 1 ≠ 0
    rw [matrixOfOp_sub_eq, matrixOfOp_mul_eq, matrixOfOp_mul_eq, matrixOfOp_complex_smul,
      matrixOfOp_H_d63, matrixOfOp_A_swap]
    simp [d63TiltedAmplitude, swapMatrix]
  have hA1_ne : finiteCEOperatorForm 2 A_swap x1 ≠ 0 := by
    intro h0
    exact hA1_not_gauge (h0 ▸ Submodule.zero_mem _)
  have hX_anti_star : star X_anti = -X_anti := by
    dsimp only [X_anti]
    rw [star_smul, Complex.star_def, map_mul, Complex.conj_ofNat, Complex.conj_I,
      tiltOp2_isSelfAdjoint.star_eq, mul_neg]
    module
  have hdiss_pos : 0 < P_gibbs.dissipative x1 x2 := by
    let D := faithfulGibbsDensity H_d63 hH_d63_sa hZ_d63_pos
    let hpow := continuous_faithfulGibbsDensity_rpow H_d63 hH_d63_sa hZ_d63_pos
    have hcross : centeredBKMRealCovariance D hpow (finiteCEOperatorForm 2 A_swap x1) X_anti = 0 := by
      have hst := centeredBKMRealCovariance_star D hpow (finiteCEOperatorForm 2 A_swap x1) X_anti
      rw [hA1.star_eq, hX_anti_star, ← centeredBKMRealCovarianceBilin_apply, _root_.map_neg,
        centeredBKMRealCovarianceBilin_apply] at hst
      linarith
    change 0 < centeredCEBKMForm D hpow A_swap x1 x2
    rw [centeredCEBKMForm_apply, hA2_eq, ← centeredBKMRealCovarianceBilin_apply,
      (centeredBKMRealCovarianceBilin D hpow (finiteCEOperatorForm 2 A_swap x1)).map_add
        (finiteCEOperatorForm 2 A_swap x1) X_anti,
      centeredBKMRealCovarianceBilin_apply, centeredBKMRealCovarianceBilin_apply,
      hcross, add_zero]
    exact centeredBKMRealCovariance_self_pos_of_not_scalarGauge hH_d63_sa hZ_d63_pos _ hA1_not_gauge
  have hcomm_eq : x1.1 A_swap * x2.1 A_swap - x2.1 A_swap * x1.1 A_swap = (8 : ℝ) • A_swap := by
    change finiteCEOperatorForm 2 A_swap x1 * finiteCEOperatorForm 2 A_swap x2 -
      finiteCEOperatorForm 2 A_swap x2 * finiteCEOperatorForm 2 A_swap x1 = (8 : ℝ) • A_swap
    rw [hA2_eq]
    apply matrixOfOp_injective
    change matrixOfOp (((Complex.I • H_d63) * A_swap - A_swap * (Complex.I • H_d63)) *
        (((Complex.I • H_d63) * A_swap - A_swap * (Complex.I • H_d63)) + (2 * Complex.I) • tiltOp2) -
      (((Complex.I • H_d63) * A_swap - A_swap * (Complex.I • H_d63)) + (2 * Complex.I) • tiltOp2) *
        ((Complex.I • H_d63) * A_swap - A_swap * (Complex.I • H_d63))) =
      matrixOfOp ((8 : ℝ) • A_swap)
    rw [matrixOfOp_sub_eq, matrixOfOp_mul_eq, matrixOfOp_mul_eq, matrixOfOp_add,
      matrixOfOp_sub_eq, matrixOfOp_mul_eq, matrixOfOp_mul_eq,
      matrixOfOp_complex_smul, matrixOfOp_complex_smul, matrixOfOp_real_smul,
      matrixOfOp_H_d63, matrixOfOp_A_swap, matrixOfOp_tiltOp2]
    ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [Complex.ext_iff, d63TiltedAmplitude, swapMatrix,
        InfoGeometry.Physics.KleinBottleSewingExact.tilt2, Matrix.mul_apply,
        Fin.sum_univ_two, Matrix.vecMul, dotProduct]
  have hrev_pos : 0 < P_gibbs.reversible x1 x2 := by
    let D := faithfulGibbsDensity H_d63 hH_d63_sa hZ_d63_pos
    let hpow := continuous_faithfulGibbsDensity_rpow H_d63 hH_d63_sa hZ_d63_pos
    change ceCurvatureBKMProbeForm D hpow A_swap B_tilt x1 x2 > 0
    rw [ceCurvatureBKMProbeForm_apply]
    have hcurv : connectionCurvature (realDerivationsLane (GibbsOperator 2))
        (exteriorDerivativeZero (realDerivationsLane (GibbsOperator 2)) A_swap) x1 x2 =
        (8 : ℝ) • A_swap := by
      rw [connectionCurvature, exteriorDerivativeOne_exteriorDerivativeZero, zero_add]
      exact hcomm_eq
    rw [hcurv, (D.bkmRealBilinForm hpow).map_smul (8 : ℝ) A_swap,
      LinearMap.smul_apply, smul_eq_mul]
    exact mul_pos (by norm_num) bkm_H_d63_A_swap_B_tilt_pos
  exact ⟨rfl,
    finiteGibbsCEOnsagerSystem_dissipative_eq_logPartitionHessian H_d63 A_swap B_tilt
      hH_d63_sa hZ_d63_pos D1 D2 hA1,
    P_gibbs.onsager_casimir_master_reciprocity x1 x2,
    hA1_ne,
    ne_of_gt hdiss_pos,
    ne_of_gt hrev_pos⟩

/-- `T1-F4-05`: `finiteGibbsCEFamilyNOperatorParitySystem` preserves N-operator Hessian dissipation identity, nonzero dissipation, and nonzero reversibility. -/
theorem t1_f4_05_finiteGibbsFamilyNOperatorParity :
    let a : Fin 2 → GibbsOperator 2 := ![A_swap, B_tilt]
    let ha : ∀ i, IsSelfAdjoint (a i) := fun i => by
      fin_cases i
      · exact hA_swap_sa
      · exact hB_tilt_sa
    let c : Fin 2 → ℝ := ![1, 2]
    let P_fam := finiteGibbsCEFamilyNOperatorParitySystem H_d63 hH_d63_sa hZ_d63_pos a ha c
      B_tilt hB_tilt_sa
    let D1 : Fin 2 → FrechetOperatorDerivation ℂ (GibbsOperator 2) :=
      ![innerFrechetComplexDeriv (Complex.I • tiltOp2),
        innerFrechetComplexDeriv (Complex.I • tiltOp2)]
    let D2 : Fin 2 → FrechetOperatorDerivation ℂ (GibbsOperator 2) :=
      ![innerFrechetComplexDeriv (Complex.I • tiltOp2 + Complex.I • (tiltOp2 * switchOp2)),
        innerFrechetComplexDeriv (Complex.I • tiltOp2)]
    let x1 := finiteCEFrechetFamilyDirection D1
    let x2 := finiteCEFrechetFamilyDirection D2
    (secondFDerivLogPartitionReadout H_d63
        (finiteGibbsCEFamilyNOperatorReadoutLinear a c x1)
        (finiteGibbsCEFamilyNOperatorReadoutLinear a c x2)).re =
      P_fam.dissipative x1 x2 ∧
      P_fam.totalGenerator (P_fam.T.op x1) (P_fam.T.op x2) = P_fam.totalGenerator x2 x1 ∧
      P_fam.dissipative x1 x2 ≠ 0 ∧
      P_fam.reversible x1 x2 ≠ 0 := by
  intro a ha c P_fam D1 D2 x1 x2
  have hD1 : IsSelfAdjoint (finiteGibbsCEFamilyNOperatorReadoutLinear a c x1) := by
    have h0 := isSelfAdjoint_I_smul_comm tiltOp2 A_swap tiltOp2_isSelfAdjoint hA_swap_sa
    have h1 := isSelfAdjoint_I_smul_comm tiltOp2 B_tilt tiltOp2_isSelfAdjoint hB_tilt_sa
    change IsSelfAdjoint
      (∑ i : Fin 2, c i • finiteCEOperatorForm 2 (a i)
        (finiteCEFrechetDirection (D1 i)))
    rw [Fin.sum_univ_two]
    exact isSelfAdjoint_add_op (isSelfAdjoint_real_smul _ _ h0) (isSelfAdjoint_real_smul _ _ h1)
  have hdiss :
      (finiteGibbsCEFamilyNOperatorSystem H_d63 hH_d63_sa hZ_d63_pos a c B_tilt).dissipative
          (finiteCEFrechetFamilyDirection D1) (finiteCEFrechetFamilyDirection D2) =
        P_fam.dissipative x1 x2 := by
    dsimp only [P_fam, finiteGibbsCEFamilyNOperatorParitySystem, x1, x2]
  have hpair := finiteGibbsCEFamilyNOperatorSystem_pairwise_eq_dissipation_hessian
    H_d63 hH_d63_sa hZ_d63_pos a c B_tilt D1 D2 hD1
  let X_anti : GibbsOperator 2 := (2 * Complex.I) • tiltOp2
  have hR2_eq : finiteGibbsCEFamilyNOperatorReadoutLinear a c x2 =
      finiteGibbsCEFamilyNOperatorReadoutLinear a c x1 + X_anti := by
    apply matrixOfOp_injective
    change matrixOfOp (∑ i : Fin 2, c i • finiteCEOperatorForm 2 (a i)
        (finiteCEFrechetDirection (D2 i))) =
      matrixOfOp ((∑ i : Fin 2, c i • finiteCEOperatorForm 2 (a i)
        (finiteCEFrechetDirection (D1 i))) + (2 * Complex.I) • tiltOp2)
    rw [Fin.sum_univ_two, Fin.sum_univ_two, matrixOfOp_add, matrixOfOp_add, matrixOfOp_add,
      matrixOfOp_real_smul, matrixOfOp_real_smul, matrixOfOp_real_smul, matrixOfOp_real_smul]
    change (1 : ℝ) • matrixOfOp ((Complex.I • tiltOp2 + Complex.I • (tiltOp2 * switchOp2)) * A_swap -
          A_swap * (Complex.I • tiltOp2 + Complex.I • (tiltOp2 * switchOp2))) +
        (2 : ℝ) • matrixOfOp ((Complex.I • tiltOp2) * B_tilt - B_tilt * (Complex.I • tiltOp2)) =
      ((1 : ℝ) • matrixOfOp ((Complex.I • tiltOp2) * A_swap - A_swap * (Complex.I • tiltOp2)) +
        (2 : ℝ) • matrixOfOp ((Complex.I • tiltOp2) * B_tilt - B_tilt * (Complex.I • tiltOp2))) +
        matrixOfOp ((2 * Complex.I) • tiltOp2)
    simp only [matrixOfOp_sub_eq, matrixOfOp_mul_eq, matrixOfOp_add, matrixOfOp_complex_smul,
      switchOp2_eq_A_swap, matrixOfOp_A_swap, matrixOfOp_B_tilt, matrixOfOp_tiltOp2]
    ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [Complex.ext_iff, swapMatrix, tiltedMatrix,
        InfoGeometry.Physics.KleinBottleSewingExact.tilt2, Matrix.mul_apply,
        Fin.sum_univ_two, Matrix.vecMul, dotProduct]
  have hR1_not_gauge : finiteGibbsCEFamilyNOperatorReadoutLinear a c x1 ∉ scalarGauge 2 := by
    apply matrixOp_ne_scalarGauge _ 0 1 (by decide)
    change matrixOfOp (∑ i : Fin 2, c i • finiteCEOperatorForm 2 (a i)
      (finiteCEFrechetDirection (D1 i))) 0 1 ≠ 0
    rw [Fin.sum_univ_two, matrixOfOp_add, matrixOfOp_real_smul, matrixOfOp_real_smul]
    change ((1 : ℝ) • matrixOfOp ((Complex.I • tiltOp2) * A_swap - A_swap * (Complex.I • tiltOp2)) +
      (2 : ℝ) • matrixOfOp ((Complex.I • tiltOp2) * B_tilt - B_tilt * (Complex.I • tiltOp2))) 0 1 ≠ 0
    rw [matrixOfOp_sub_eq, matrixOfOp_sub_eq, matrixOfOp_mul_eq, matrixOfOp_mul_eq,
      matrixOfOp_mul_eq, matrixOfOp_mul_eq, matrixOfOp_complex_smul,
      matrixOfOp_A_swap, matrixOfOp_B_tilt, matrixOfOp_tiltOp2]
    norm_num [Complex.ext_iff, swapMatrix, tiltedMatrix,
      InfoGeometry.Physics.KleinBottleSewingExact.tilt2, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.vecMul, dotProduct]
  have hX_anti_star : star X_anti = -X_anti := by
    dsimp only [X_anti]
    rw [star_smul, Complex.star_def, map_mul, Complex.conj_ofNat, Complex.conj_I,
      tiltOp2_isSelfAdjoint.star_eq, mul_neg]
    module
  have hdiss_pos : 0 < P_fam.dissipative x1 x2 := by
    let D := faithfulGibbsDensity H_d63 hH_d63_sa hZ_d63_pos
    let hpow := continuous_faithfulGibbsDensity_rpow H_d63 hH_d63_sa hZ_d63_pos
    have hcross : centeredBKMRealCovariance D hpow
        (finiteGibbsCEFamilyNOperatorReadoutLinear a c x1) X_anti = 0 := by
      have hst := centeredBKMRealCovariance_star D hpow
        (finiteGibbsCEFamilyNOperatorReadoutLinear a c x1) X_anti
      rw [hD1.star_eq, hX_anti_star, ← centeredBKMRealCovarianceBilin_apply, _root_.map_neg,
        centeredBKMRealCovarianceBilin_apply] at hst
      linarith
    rw [← hdiss]
    dsimp only [finiteGibbsCEFamilyNOperatorSystem]
    rw [finiteCEFamilyNOperatorDissipativeForm_apply]
    have hx1 : finiteCEFrechetFamilyDirection D1 = x1 := rfl
    have hx2 : finiteCEFrechetFamilyDirection D2 = x2 := rfl
    rw [hx1, hx2, hR2_eq, ← centeredBKMRealCovarianceBilin_apply,
      (centeredBKMRealCovarianceBilin _ _ _).map_add
        (finiteGibbsCEFamilyNOperatorReadoutLinear a c x1) X_anti,
      centeredBKMRealCovarianceBilin_apply, centeredBKMRealCovarianceBilin_apply,
      hcross, add_zero]
    exact centeredBKMRealCovariance_self_pos_of_not_scalarGauge hH_d63_sa hZ_d63_pos _ hR1_not_gauge
  have hrev_pos : 0 < P_fam.reversible x1 x2 := by
    let D := faithfulGibbsDensity H_d63 hH_d63_sa hZ_d63_pos
    let hpow := continuous_faithfulGibbsDensity_rpow H_d63 hH_d63_sa hZ_d63_pos
    change finiteCEFamilyNOperatorCurvatureProbeForm D hpow a c B_tilt x1 x2 > 0
    rw [finiteCEFamilyNOperatorCurvatureProbeForm_apply, Fin.sum_univ_two]
    have h1_zero : ceCurvatureBKMProbeForm D hpow (a 1) B_tilt (x1 1) (x2 1) = 0 := by
      rw [ceCurvatureBKMProbeForm_apply]
      have hx_eq : x1 1 = x2 1 := rfl
      have hcurv : connectionCurvature (realDerivationsLane (GibbsOperator 2))
          (exteriorDerivativeZero (realDerivationsLane (GibbsOperator 2)) (a 1)) (x1 1) (x2 1) = 0 := by
        rw [hx_eq, connectionCurvature, exteriorDerivativeOne_exteriorDerivativeZero, zero_add]
        exact sub_self _
      rw [hcurv, _root_.map_zero, LinearMap.zero_apply]
    have hcomm0 : (x1 0).1 (a 0) * (x2 0).1 (a 0) - (x2 0).1 (a 0) * (x1 0).1 (a 0) =
        (8 : ℝ) • A_swap := by
      apply matrixOfOp_injective
      change matrixOfOp (((Complex.I • tiltOp2) * A_swap - A_swap * (Complex.I • tiltOp2)) *
          ((Complex.I • tiltOp2 + Complex.I • (tiltOp2 * switchOp2)) * A_swap -
            A_swap * (Complex.I • tiltOp2 + Complex.I • (tiltOp2 * switchOp2))) -
        ((Complex.I • tiltOp2 + Complex.I • (tiltOp2 * switchOp2)) * A_swap -
            A_swap * (Complex.I • tiltOp2 + Complex.I • (tiltOp2 * switchOp2))) *
          ((Complex.I • tiltOp2) * A_swap - A_swap * (Complex.I • tiltOp2))) =
        matrixOfOp ((8 : ℝ) • A_swap)
      rw [matrixOfOp_sub_eq, matrixOfOp_mul_eq, matrixOfOp_mul_eq,
        matrixOfOp_sub_eq, matrixOfOp_mul_eq, matrixOfOp_mul_eq,
        matrixOfOp_sub_eq, matrixOfOp_mul_eq, matrixOfOp_mul_eq,
        matrixOfOp_add, matrixOfOp_complex_smul, matrixOfOp_complex_smul, matrixOfOp_real_smul,
        matrixOfOp_mul_eq, switchOp2_eq_A_swap, matrixOfOp_tiltOp2, matrixOfOp_A_swap]
      ext i j; fin_cases i <;> fin_cases j <;>
        norm_num [Complex.ext_iff, swapMatrix, InfoGeometry.Physics.KleinBottleSewingExact.tilt2,
          Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct]
    have h0_val : ceCurvatureBKMProbeForm D hpow (a 0) B_tilt (x1 0) (x2 0) =
        8 * D.bkmRealBilinForm hpow A_swap B_tilt := by
      rw [ceCurvatureBKMProbeForm_apply]
      have hcurv : connectionCurvature (realDerivationsLane (GibbsOperator 2))
          (exteriorDerivativeZero (realDerivationsLane (GibbsOperator 2)) (a 0)) (x1 0) (x2 0) =
          (8 : ℝ) • A_swap := by
        rw [connectionCurvature, exteriorDerivativeOne_exteriorDerivativeZero, zero_add]
        exact hcomm0
      rw [hcurv, (D.bkmRealBilinForm hpow).map_smul (8 : ℝ) A_swap,
        LinearMap.smul_apply, smul_eq_mul]
    rw [h1_zero, smul_zero, add_zero, h0_val]
    change 0 < (1 : ℝ) * (8 * D.bkmRealBilinForm hpow A_swap B_tilt)
    rw [one_mul]
    exact mul_pos (by norm_num) bkm_H_d63_A_swap_B_tilt_pos
  exact ⟨(hpair.2.symm.trans hpair.1).trans hdiss,
    P_fam.onsager_casimir_master_reciprocity x1 x2,
    ne_of_gt hdiss_pos,
    ne_of_gt hrev_pos⟩

/-- `T1-F4-06`: `gibbsNOperatorFamilyStarErlangenDatum` specializes cleanly to `H_d63` and `a = ![A_swap, B_tilt]` with nonzero response and nonzero skew Onsager pairing. -/
theorem t1_f4_06_erlangenDatumSpecialization :
    let a : Fin 2 → GibbsOperator 2 := ![A_swap, B_tilt]
    let ha : ∀ i, IsSelfAdjoint (a i) := fun i => by
      fin_cases i
      · exact hA_swap_sa
      · exact hB_tilt_sa
    let c : Fin 2 → ℝ := ![1, 2]
    let datum := gibbsNOperatorFamilyStarErlangenDatum (G := Unit)
      H_d63 hH_d63_sa hZ_d63_pos a ha c B_tilt hB_tilt_sa
    let D1 : Fin 2 → FrechetOperatorDerivation ℂ (GibbsOperator 2) :=
      ![innerFrechetComplexDeriv (Complex.I • tiltOp2),
        innerFrechetComplexDeriv (Complex.I • tiltOp2)]
    let D2 : Fin 2 → FrechetOperatorDerivation ℂ (GibbsOperator 2) :=
      ![innerFrechetComplexDeriv (Complex.I • tiltOp2 + Complex.I • (tiltOp2 * switchOp2)),
        innerFrechetComplexDeriv (Complex.I • tiltOp2)]
    let x1 := finiteCEFrechetFamilyDirection D1
    let x2 := finiteCEFrechetFamilyDirection D2
    HasJReciprocity datum.onsagerPairing
        (familyTimeReversal 2 (starDerivationTimeReversal 2)).op ∧
      datum.responseMetric () x1 x2 =
        (secondFDerivLogPartitionReadout H_d63
          (finiteGibbsCEFamilyNOperatorReadoutLinear a c x1)
          (finiteGibbsCEFamilyNOperatorReadoutLinear a c x2)).re ∧
      datum.responseMetric () x1 x2 ≠ 0 ∧
      datum.onsagerPairing () x1 x2 ≠ datum.onsagerPairing () x2 x1 := by
  intro a ha c datum D1 D2 x1 x2
  have hD1 : IsSelfAdjoint (finiteGibbsCEFamilyNOperatorReadoutLinear a c
      (finiteCEFrechetFamilyDirection D1)) := by
    have h0 := isSelfAdjoint_I_smul_comm tiltOp2 A_swap tiltOp2_isSelfAdjoint hA_swap_sa
    have h1 := isSelfAdjoint_I_smul_comm tiltOp2 B_tilt tiltOp2_isSelfAdjoint hB_tilt_sa
    change IsSelfAdjoint (∑ i : Fin 2, c i • finiteCEOperatorForm 2 (a i)
      (finiteCEFrechetDirection (D1 i)))
    rw [Fin.sum_univ_two]
    exact isSelfAdjoint_add_op (isSelfAdjoint_real_smul _ _ h0) (isSelfAdjoint_real_smul _ _ h1)
  have hrec := gibbsNOperatorFamilyStarErlangenDatum_reciprocity_and_hessian (G := Unit)
    H_d63 hH_d63_sa hZ_d63_pos a ha c B_tilt hB_tilt_sa D1 D2 hD1
  have hf5 := t1_f4_05_finiteGibbsFamilyNOperatorParity
  have hresp_ne : datum.responseMetric () x1 x2 ≠ 0 := by
    rw [hrec.2]
    change (secondFDerivLogPartitionReadout H_d63
      (finiteGibbsCEFamilyNOperatorReadoutLinear a c x1)
      (finiteGibbsCEFamilyNOperatorReadoutLinear a c x2)).re ≠ 0
    rw [hf5.1]
    exact hf5.2.2.1
  have hpair_ne : datum.onsagerPairing () x1 x2 ≠ datum.onsagerPairing () x2 x1 := by
    dsimp only [datum]
    rw [gibbsNOperatorFamilyStarErlangenDatum_onsagerPairing,
      gibbsNOperatorFamilyStarErlangenDatum_onsagerPairing]
    intro heq
    let P_fam := finiteGibbsCEFamilyNOperatorParitySystem H_d63 hH_d63_sa hZ_d63_pos a ha c
      B_tilt hB_tilt_sa
    have htot1 : (finiteGibbsCEFamilyNOperatorSystem H_d63 hH_d63_sa hZ_d63_pos a c B_tilt).totalGenerator x1 x2 =
        P_fam.dissipative x1 x2 + P_fam.reversible x1 x2 := rfl
    have htot2 : (finiteGibbsCEFamilyNOperatorSystem H_d63 hH_d63_sa hZ_d63_pos a c B_tilt).totalGenerator x2 x1 =
        P_fam.dissipative x2 x1 + P_fam.reversible x2 x1 := rfl
    rw [htot1, htot2, P_fam.dissipative_symm x2 x1, P_fam.reversible_skew x2 x1] at heq
    have hrev0 : P_fam.reversible x1 x2 = 0 := by linarith
    exact hf5.2.2.2 hrev0
  exact ⟨fun A B s => hrec.1 A B s, hrec.2, hresp_ne, hpair_ne⟩

private def traceMulAlt2CLM :
    GibbsOperator 2 →L[ℝ] (GibbsOperator 2 [⋀^(Fin 2)]→L[ℝ] GibbsOperator 2) :=
  (Complex.reCLM.comp ((finiteOperatorTraceRealCLM 2).comp (leftMulRealCLM tiltOp2))).smulRight
    (frechetExtDerivReal (smoothLeftMulOneForm 2) H_d63)

private def omega0Smooth :
    RealOperatorFrechetForm (GibbsOperator 2) (GibbsOperator 2) (GibbsOperator 2) 0 :=
  fun H => ContinuousAlternatingMap.constOfIsEmpty ℝ (GibbsOperator 2) (Fin 0) H

private def omega3Const :
    RealOperatorFrechetForm (GibbsOperator 2) (GibbsOperator 2) (GibbsOperator 2) 3 :=
  fun _ => ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ (GibbsOperator 2) (GibbsOperator 2)
    traceMulAlt2CLM

/-- `T1-F5-01`: `frechetFormToCEForm` transports smooth `RealOperatorFrechetForm` at degrees `n = 0, 1, 2, 3` (all nonzero). -/
theorem t1_f5_01_frechetFormToCEFormDegrees0123 :
    let h0 : ContDiff ℝ (⊤ : WithTop ℕ∞) omega0Smooth :=
      contDiff_realLinearMap_gibbsOperator omega0Smooth
        (fun H1 H2 => by apply ContinuousAlternatingMap.ext; intro _; simp [omega0Smooth])
        (fun r H => by
          apply ContinuousAlternatingMap.ext; intro _
          change ContinuousAlternatingMap.constOfIsEmpty ℝ (GibbsOperator 2) (Fin 0) (r • H) Fin.elim0 =
            (r • ContinuousAlternatingMap.constOfIsEmpty ℝ (GibbsOperator 2) (Fin 0) H) Fin.elim0
          simp [real_smul_eq_complex_smul])
    let h1 : ContDiff ℝ (⊤ : WithTop ℕ∞) (smoothLeftMulOneForm 2) := contDiff_smoothLeftMulOneForm 2
    let h2 : ContDiff ℝ (⊤ : WithTop ℕ∞) (frechetExtDerivReal (smoothLeftMulOneForm 2)) :=
      contDiff_frechetExtDerivK h1
    let h3 : ContDiff ℝ (⊤ : WithTop ℕ∞) omega3Const := contDiff_const
    let vfA : (frechetVectorFieldDerivationLane ℝ (GibbsOperator 2)).L :=
      frechetVectorFieldFromComplex (innerFrechetComplexDeriv A_swap)
    let vfB : (frechetVectorFieldDerivationLane ℝ (GibbsOperator 2)).L :=
      frechetVectorFieldFromComplex (innerFrechetComplexDeriv (matrixOp !![0, 1; 0, 0]))
    let vf1 : (frechetVectorFieldDerivationLane ℝ (GibbsOperator 2)).L :=
      frechetVectorFieldFromComplex (innerFrechetComplexDeriv (matrixOp !![0, Complex.I; 0, 0]))
    (frechetFormToCEForm 0 omega0Smooth h0 Fin.elim0).toFun H_d63 = H_d63 ∧
      (frechetFormToCEForm 1 (smoothLeftMulOneForm 2) h1 ![vfA]).toFun H_d63 =
        H_d63 * (A_swap * H_d63 - H_d63 * A_swap) ∧
      (frechetFormToCEForm 2 (frechetExtDerivReal (smoothLeftMulOneForm 2)) h2 ![vfA, vfB]).toFun H_d63 ≠ 0 ∧
      (frechetFormToCEForm 3 omega3Const h3 ![vf1, vfA, vfB]).toFun H_d63 =
        omega3Const H_d63 (fun i => (![vf1, vfA, vfB] i).toDerivation H_d63) ∧
      (frechetFormToCEForm 3 omega3Const h3 ![vf1, vfA, vfB]).toFun H_d63 ≠ 0 := by
  intro h0 h1 h2 h3 vfA vfB vf1
  refine ⟨rfl, rfl, ?_, rfl, ?_⟩
  · have hv : (fun i => (![vfA, vfB] i).toDerivation H_d63) =
        ![A_swap * H_d63 - H_d63 * A_swap,
          (matrixOp !![0, 1; 0, 0] : GibbsOperator 2) * H_d63 -
            H_d63 * (matrixOp !![0, 1; 0, 0] : GibbsOperator 2)] := by
      ext i; fin_cases i <;> rfl
    change frechetExtDerivReal (smoothLeftMulOneForm 2) H_d63
      (fun i => (![vfA, vfB] i).toDerivation H_d63) ≠ 0
    rw [hv, frechetExtDerivReal_smoothLeftMulOneForm]
    intro hzero
    have hm := congrArg (fun Z : GibbsOperator 2 => matrixOfOp Z 0 0) hzero
    rw [matrixOfOp_sub_eq, matrixOfOp_mul_eq, matrixOfOp_mul_eq,
      matrixOfOp_sub_eq, matrixOfOp_mul_eq, matrixOfOp_mul_eq,
      matrixOfOp_sub_eq, matrixOfOp_mul_eq, matrixOfOp_mul_eq,
      A_swap, H_d63, matrixOfOp_matrixOp, matrixOfOp_matrixOp, matrixOfOp_matrixOp,
      matrixOfOp_zero] at hm
    norm_num [swapMatrix, d63TiltedAmplitude, Matrix.mul_apply, Fin.sum_univ_two] at hm
  · change omega3Const H_d63 (fun i => (![vf1, vfA, vfB] i).toDerivation H_d63) ≠ 0
    dsimp only [omega3Const]
    rw [ContinuousAlternatingMap.alternatizeUncurryFinCLM_apply,
      ContinuousAlternatingMap.alternatizeUncurryFin_apply]
    rw [Fin.sum_univ_three]
    have hcoeff0 : (Complex.reCLM.comp ((finiteOperatorTraceRealCLM 2).comp (leftMulRealCLM tiltOp2)))
        ((![vf1, vfA, vfB] 0).toDerivation H_d63) = 0 := by
      change (finiteOperatorTrace (tiltOp2 * ((matrixOp !![0, Complex.I; 0, 0] : GibbsOperator 2) * H_d63 -
        H_d63 * (matrixOp !![0, Complex.I; 0, 0] : GibbsOperator 2)))).re = 0
      change (Matrix.trace (matrixOfOp (tiltOp2 * ((matrixOp !![0, Complex.I; 0, 0] : GibbsOperator 2) * H_d63 -
        H_d63 * (matrixOp !![0, Complex.I; 0, 0] : GibbsOperator 2))))).re = 0
      rw [matrixOfOp_mul_eq, matrixOfOp_sub_eq, matrixOfOp_mul_eq, matrixOfOp_mul_eq,
        matrixOfOp_tiltOp2, matrixOfOp_H_d63, matrixOfOp_matrixOp]
      norm_num [InfoGeometry.Physics.KleinBottleSewingExact.tilt2, d63TiltedAmplitude,
        Matrix.trace, Matrix.diag, Matrix.mul_apply, Fin.sum_univ_two]
    have hcoeff1 : (Complex.reCLM.comp ((finiteOperatorTraceRealCLM 2).comp (leftMulRealCLM tiltOp2)))
        ((![vf1, vfA, vfB] 1).toDerivation H_d63) = 0 := by
      change (finiteOperatorTrace (tiltOp2 * (A_swap * H_d63 - H_d63 * A_swap))).re = 0
      change (Matrix.trace (matrixOfOp (tiltOp2 * (A_swap * H_d63 - H_d63 * A_swap)))).re = 0
      rw [matrixOfOp_mul_eq, matrixOfOp_sub_eq, matrixOfOp_mul_eq, matrixOfOp_mul_eq,
        matrixOfOp_tiltOp2, matrixOfOp_A_swap, matrixOfOp_H_d63]
      norm_num [InfoGeometry.Physics.KleinBottleSewingExact.tilt2, swapMatrix, d63TiltedAmplitude,
        Matrix.trace, Matrix.diag, Matrix.mul_apply, Fin.sum_univ_two]
    have hcoeff2 : (Complex.reCLM.comp ((finiteOperatorTraceRealCLM 2).comp (leftMulRealCLM tiltOp2)))
        ((![vf1, vfA, vfB] 2).toDerivation H_d63) = 2 := by
      change (finiteOperatorTrace (tiltOp2 * ((matrixOp !![0, 1; 0, 0] : GibbsOperator 2) * H_d63 -
        H_d63 * (matrixOp !![0, 1; 0, 0] : GibbsOperator 2)))).re = 2
      change (Matrix.trace (matrixOfOp (tiltOp2 * ((matrixOp !![0, 1; 0, 0] : GibbsOperator 2) * H_d63 -
        H_d63 * (matrixOp !![0, 1; 0, 0] : GibbsOperator 2))))).re = 2
      rw [matrixOfOp_mul_eq, matrixOfOp_sub_eq, matrixOfOp_mul_eq, matrixOfOp_mul_eq,
        matrixOfOp_tiltOp2, matrixOfOp_H_d63, matrixOfOp_matrixOp]
      norm_num [InfoGeometry.Physics.KleinBottleSewingExact.tilt2, d63TiltedAmplitude,
        Matrix.trace, Matrix.diag, Matrix.mul_apply, Fin.sum_univ_two]
    have ht1 : traceMulAlt2CLM ((![vf1, vfA, vfB] 1).toDerivation H_d63)
        ((fun i => (![vf1, vfA, vfB] i).toDerivation H_d63) ∘ Fin.succAbove 1) = 0 := by
      dsimp only [traceMulAlt2CLM]
      rw [ContinuousLinearMap.smulRight_apply, hcoeff1, ContinuousAlternatingMap.smul_apply,
        zero_smul]
    have ht2 : traceMulAlt2CLM ((![vf1, vfA, vfB] 2).toDerivation H_d63)
        ((fun i => (![vf1, vfA, vfB] i).toDerivation H_d63) ∘ Fin.succAbove 2) =
        (2 : ℝ) • ((![vf1, vfA, vfB] 0).toDerivation H_d63 * (![vf1, vfA, vfB] 1).toDerivation H_d63 -
          (![vf1, vfA, vfB] 1).toDerivation H_d63 * (![vf1, vfA, vfB] 0).toDerivation H_d63) := by
      dsimp only [traceMulAlt2CLM]
      rw [ContinuousLinearMap.smulRight_apply, hcoeff2]
      have hf : ((fun i => (![vf1, vfA, vfB] i).toDerivation H_d63) ∘ Fin.succAbove 2) =
          ![(![vf1, vfA, vfB] 0).toDerivation H_d63, (![vf1, vfA, vfB] 1).toDerivation H_d63] := by
        ext i; fin_cases i <;> rfl
      rw [ContinuousAlternatingMap.smul_apply, hf, frechetExtDerivReal_smoothLeftMulOneForm]
    change ((-1 : ℤ) ^ (0 : ℕ) •
        traceMulAlt2CLM ((![vf1, vfA, vfB] 0).toDerivation H_d63)
          ((fun i => (![vf1, vfA, vfB] i).toDerivation H_d63) ∘ Fin.succAbove 0) +
      (-1 : ℤ) ^ (1 : ℕ) •
        traceMulAlt2CLM ((![vf1, vfA, vfB] 1).toDerivation H_d63)
          ((fun i => (![vf1, vfA, vfB] i).toDerivation H_d63) ∘ Fin.succAbove 1) +
      (-1 : ℤ) ^ (2 : ℕ) •
        traceMulAlt2CLM ((![vf1, vfA, vfB] 2).toDerivation H_d63)
          ((fun i => (![vf1, vfA, vfB] i).toDerivation H_d63) ∘ Fin.succAbove 2)) ≠ 0
    have ht0' : traceMulAlt2CLM ((![vf1, vfA, vfB] 0).toDerivation H_d63)
        ((fun i => (![vf1, vfA, vfB] i).toDerivation H_d63) ∘ Fin.succAbove 0) = 0 := by
      dsimp only [traceMulAlt2CLM]
      rw [ContinuousLinearMap.smulRight_apply, hcoeff0, ContinuousAlternatingMap.smul_apply,
        zero_smul]
    rw [ht0', ht1, ht2, zsmul_zero, zsmul_zero, zero_add, zero_add]
    norm_num
    intro h0
    have hm := congrArg (fun Z : GibbsOperator 2 => matrixOfOp Z 0 0) h0
    change matrixOfOp ((2 : ℝ) • (((matrixOp !![0, Complex.I; 0, 0] : GibbsOperator 2) * H_d63 -
        H_d63 * (matrixOp !![0, Complex.I; 0, 0] : GibbsOperator 2)) * (A_swap * H_d63 - H_d63 * A_swap) -
      (A_swap * H_d63 - H_d63 * A_swap) * ((matrixOp !![0, Complex.I; 0, 0] : GibbsOperator 2) * H_d63 -
        H_d63 * (matrixOp !![0, Complex.I; 0, 0] : GibbsOperator 2)))) 0 0 = 0 at hm
    rw [matrixOfOp_real_smul, matrixOfOp_sub_eq, matrixOfOp_mul_eq, matrixOfOp_mul_eq,
      matrixOfOp_sub_eq, matrixOfOp_mul_eq, matrixOfOp_mul_eq,
      matrixOfOp_sub_eq, matrixOfOp_mul_eq, matrixOfOp_mul_eq,
      matrixOfOp_A_swap, matrixOfOp_H_d63, matrixOfOp_matrixOp] at hm
    norm_num [Complex.ext_iff, swapMatrix, d63TiltedAmplitude, Matrix.mul_apply,
      Fin.sum_univ_two, Matrix.vecMul, dotProduct] at hm

/-- `T1-F5-02`: `frechetExtDerivK_linear_eq_ceExteriorDerivative` at degrees `n = 1` and `n = 2` on non-closed forms (both nonzero). -/
theorem t1_f5_02_frechetExtDerivEqCeExterior :
    let h1 := contDiff_smoothLeftMulOneForm 2
    let ω2_nc : RealOperatorFrechetForm (GibbsOperator 2) (GibbsOperator 2) (GibbsOperator 2) 2 :=
      traceMulAlt2CLM
    let h2 : ContDiff ℝ (⊤ : WithTop ℕ∞) ω2_nc :=
      contDiff_realLinearMap_gibbsOperator ω2_nc
        (fun H1 H2 => traceMulAlt2CLM.map_add H1 H2)
        (fun r H => traceMulAlt2CLM.map_smul r H)
    let vfA : (frechetVectorFieldDerivationLane ℝ (GibbsOperator 2)).L :=
      frechetVectorFieldFromComplex (innerFrechetComplexDeriv A_swap)
    let vfB : (frechetVectorFieldDerivationLane ℝ (GibbsOperator 2)).L :=
      frechetVectorFieldFromComplex (innerFrechetComplexDeriv (matrixOp !![0, 1; 0, 0]))
    let vf1 : (frechetVectorFieldDerivationLane ℝ (GibbsOperator 2)).L :=
      frechetVectorFieldFromComplex (innerFrechetComplexDeriv (matrixOp !![0, Complex.I; 0, 0]))
    frechetFormToCEForm 2 (frechetExtDerivReal (smoothLeftMulOneForm 2))
        (contDiff_frechetExtDerivK h1) =
      ceExteriorDerivative (frechetVectorFieldDerivationLane ℝ (GibbsOperator 2)) 1
        (frechetFormToCEForm 1 (smoothLeftMulOneForm 2) h1) ∧
      (ceExteriorDerivative (frechetVectorFieldDerivationLane ℝ (GibbsOperator 2)) 1
        (frechetFormToCEForm 1 (smoothLeftMulOneForm 2) h1) ![vfA, vfB]).toFun H_d63 ≠ 0 ∧
      frechetFormToCEForm 3 (frechetExtDerivReal ω2_nc) (contDiff_frechetExtDerivK h2) =
        ceExteriorDerivative (frechetVectorFieldDerivationLane ℝ (GibbsOperator 2)) 2
          (frechetFormToCEForm 2 ω2_nc h2) ∧
      (ceExteriorDerivative (frechetVectorFieldDerivationLane ℝ (GibbsOperator 2)) 2
        (frechetFormToCEForm 2 ω2_nc h2) ![vf1, vfA, vfB]).toFun H_d63 ≠ 0 := by
  intro h1 ω2_nc h2 vfA vfB vf1
  have eq1 := frechetExtDerivK_linear_eq_ceExteriorDerivative 1 (smoothLeftMulOneForm 2) h1
  have eq2 := frechetExtDerivK_linear_eq_ceExteriorDerivative 2 ω2_nc h2
  have hf1 := t1_f5_01_frechetFormToCEFormDegrees0123
  have hne1 : (ceExteriorDerivative (frechetVectorFieldDerivationLane ℝ (GibbsOperator 2)) 1
      (frechetFormToCEForm 1 (smoothLeftMulOneForm 2) h1) ![vfA, vfB]).toFun H_d63 ≠ 0 := by
    rw [← eq1]
    exact hf1.2.2.1
  have hω3_eq : frechetExtDerivReal ω2_nc = omega3Const := by
    funext H
    apply ContinuousAlternatingMap.ext
    intro v
    rw [frechetExtDerivReal, frechetExtDerivK_apply (h2.differentiable (by simp) H)]
    dsimp only [omega3Const]
    rw [ContinuousAlternatingMap.alternatizeUncurryFinCLM_apply,
      ContinuousAlternatingMap.alternatizeUncurryFin_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    let L0 : GibbsOperator 2 →ₗ[ℝ] GibbsOperator 2 :=
      { toFun := fun y => traceMulAlt2CLM y (i.removeNth v)
        map_add' := fun y₁ y₂ => by
          change (traceMulAlt2CLM (y₁ + y₂)) (i.removeNth v) =
            (traceMulAlt2CLM y₁) (i.removeNth v) + (traceMulAlt2CLM y₂) (i.removeNth v)
          rw [traceMulAlt2CLM.map_add, ContinuousAlternatingMap.add_apply]
        map_smul' := fun r y => by
          simp only [RingHom.id_apply]
          change (traceMulAlt2CLM (r • y)) (i.removeNth v) =
            r • (traceMulAlt2CLM y) (i.removeNth v)
          rw [traceMulAlt2CLM.map_smul, ContinuousAlternatingMap.smul_apply] }
    let Rw : GibbsOperator 2 →L[ℝ] GibbsOperator 2 :=
      { toLinearMap := L0
        cont := LinearMap.continuous_of_finiteDimensional L0 }
    have hf : fderiv ℝ (fun y : GibbsOperator 2 => ω2_nc y (i.removeNth v)) H = Rw := by
      have hfun : (fun y : GibbsOperator 2 => ω2_nc y (i.removeNth v)) = Rw := rfl
      rw [hfun]
      exact Rw.fderiv
    rw [hf]
    rfl
  have hne2 : (ceExteriorDerivative (frechetVectorFieldDerivationLane ℝ (GibbsOperator 2)) 2
      (frechetFormToCEForm 2 ω2_nc h2) ![vf1, vfA, vfB]).toFun H_d63 ≠ 0 := by
    rw [← eq2]
    change (frechetExtDerivReal ω2_nc H_d63) (fun i => (![vf1, vfA, vfB] i).toDerivation H_d63) ≠ 0
    rw [hω3_eq]
    exact hf1.2.2.2.2
  exact ⟨eq1, hne1, eq2, hne2⟩

/-- `T1-F5-03`: `ceCurvature` satisfies `ceCurvature_eq` and links to `ceCurvatureBKMProbeForm` (both nonzero). -/
theorem t1_f5_03_ceCurvatureEqAndBkmProbe :
    let K := realDerivationsLane (GibbsOperator 2)
    let Γ := exteriorDerivativeZero K A_swap
    let D := faithfulGibbsDensity H_d63 hH_d63_sa hZ_d63_pos
    let hpow := continuous_faithfulGibbsDensity_rpow H_d63 hH_d63_sa hZ_d63_pos
    let d1 := innerDerivation tiltOp2
    let d2 := innerDerivation (tiltOp2 * switchOp2)
    ceCurvature K (oneFormAlternatingLinearEquiv K Γ) =
        twoCochainEquivDerivationOperatorForm K (connectionCurvature K Γ) ∧
      D.bkmRealBilinForm hpow (ceCurvature K (oneFormAlternatingLinearEquiv K Γ) ![d1, d2]) B_tilt =
        ceCurvatureBKMProbeForm D hpow A_swap B_tilt d1 d2 ∧
      ceCurvature K (oneFormAlternatingLinearEquiv K Γ) ![d1, d2] ≠ 0 ∧
      ceCurvatureBKMProbeForm D hpow A_swap B_tilt d1 d2 ≠ 0 := by
  intro K Γ D hpow d1 d2
  have hcurv_eq : ceCurvature K (oneFormAlternatingLinearEquiv K Γ) ![d1, d2] =
      (-8 : ℝ) • A_swap := by
    rw [ceCurvature_eq, twoCochainEquivDerivationOperatorForm_apply,
      connectionCurvature, exteriorDerivativeOne_exteriorDerivativeZero, zero_add]
    change (tiltOp2 * A_swap - A_swap * tiltOp2) *
          ((tiltOp2 * switchOp2) * A_swap - A_swap * (tiltOp2 * switchOp2)) -
        ((tiltOp2 * switchOp2) * A_swap - A_swap * (tiltOp2 * switchOp2)) *
          (tiltOp2 * A_swap - A_swap * tiltOp2) =
      (-8 : ℝ) • A_swap
    apply matrixOfOp_injective
    rw [matrixOfOp_sub_eq, matrixOfOp_mul_eq, matrixOfOp_mul_eq,
      matrixOfOp_sub_eq, matrixOfOp_mul_eq, matrixOfOp_mul_eq,
      matrixOfOp_sub_eq, matrixOfOp_mul_eq, matrixOfOp_mul_eq,
      matrixOfOp_mul_eq, matrixOfOp_mul_eq, matrixOfOp_real_smul,
      switchOp2_eq_A_swap, matrixOfOp_tiltOp2, matrixOfOp_A_swap]
    ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [InfoGeometry.Physics.KleinBottleSewingExact.tilt2, swapMatrix,
        Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct]
  have hcurv_ne : ceCurvature K (oneFormAlternatingLinearEquiv K Γ) ![d1, d2] ≠ 0 := by
    rw [hcurv_eq]
    intro h0
    have hm := congrArg (fun M : GibbsOperator 2 => matrixOfOp M 0 1) h0
    rw [matrixOfOp_real_smul, matrixOfOp_A_swap, matrixOfOp_zero] at hm
    norm_num [swapMatrix] at hm
  have hprobe_ne : ceCurvatureBKMProbeForm D hpow A_swap B_tilt d1 d2 ≠ 0 := by
    rw [← ceCurvature_exteriorDerivativeZero_bkmProbe_eq D hpow A_swap B_tilt d1 d2,
      hcurv_eq, (D.bkmRealBilinForm hpow).map_smul (-8 : ℝ) A_swap,
      LinearMap.smul_apply, smul_eq_mul]
    have hpos : 0 < D.bkmRealBilinForm hpow A_swap B_tilt := bkm_H_d63_A_swap_B_tilt_pos
    linarith
  exact ⟨ceCurvature_eq _ _,
    ceCurvature_exteriorDerivativeZero_bkmProbe_eq D hpow A_swap B_tilt d1 d2,
    hcurv_ne,
    hprobe_ne⟩

/-- `T1-F5-04`: `frechetExtDeriv_logPartition_bkmHessian_alignment` aligns with `ParityOnsagerFormPairing` (nonzero Hessian, dissipative, and reversible pairings). -/
theorem t1_f5_04_logPartitionHessianAlignment :
    let τ := conjStarAlgEquiv 2
    let Q := Complex.I • switchOp2
    let D1 := innerFrechetComplexDeriv (Complex.I • B_tilt)
    let x1 := finiteCEFrechetDirection D1
    let D_t := faithfulGibbsDensity tiltOp2 tiltOp2_isSelfAdjoint
      (tracedExponential_re_pos_of_isSelfAdjoint tiltOp2 tiltOp2_isSelfAdjoint)
    let hpow_t := continuous_faithfulGibbsDensity_rpow tiltOp2 tiltOp2_isSelfAdjoint
      (tracedExponential_re_pos_of_isSelfAdjoint tiltOp2 tiltOp2_isSelfAdjoint)
    let PP := centeredBKMOnsagerFormPairingOfAut_ofValueParity τ
      (conjStarAlgEquiv_involutive (n := 2)) D_t hpow_t
      (aut_faithfulGibbsDensity_rho τ tiltOp2 tiltOp2_isSelfAdjoint
        (tracedExponential_re_pos_of_isSelfAdjoint tiltOp2 tiltOp2_isSelfAdjoint) conj_tiltOp2)
      (conjStarAlgEquiv_trace_re (n := 2)) Q
      (conjStarAlgEquiv_purelyImaginary_odd switchOp2 conj_switchOp2) ![x1]
    let K := realDerivationsLane (GibbsOperator 2)
    let ωA := oneFormAlternatingLinearEquiv K (exteriorDerivativeZero K switchOp2)
    let ωB := oneFormAlternatingLinearEquiv K
      (exteriorDerivativeZero K (switchOp2 + matrixOp !![0, Complex.I; 0, 0]))
    frechetExtDeriv (logPartitionOneForm 2) H_d63 ![A_swap, B_tilt] = 0 ∧
      (secondFDerivLogPartitionReadout H_d63 A_swap B_tilt).re =
        centeredBKMRealCovariance
          (faithfulGibbsDensity H_d63 hH_d63_sa hZ_d63_pos)
          (continuous_faithfulGibbsDensity_rpow H_d63 hH_d63_sa hZ_d63_pos) A_swap B_tilt ∧
      (secondFDerivLogPartitionReadout H_d63 A_swap B_tilt).re ≠ 0 ∧
      PP.totalGenerator (PP.T.op ωA) (PP.T.op ωB) = PP.totalGenerator ωB ωA ∧
      x1.1 switchOp2 * x1.1 (switchOp2 + matrixOp !![0, Complex.I; 0, 0]) ≠
        x1.1 (switchOp2 + matrixOp !![0, Complex.I; 0, 0]) * x1.1 switchOp2 ∧
      PP.dissipative ωA ωB ≠ 0 ∧
      PP.reversible ωA ωB ≠ 0 := by
  intro τ Q D1 x1 D_t hpow_t PP K ωA ωB
  have halign := frechetExtDeriv_logPartition_bkmHessian_alignment
    H_d63 hH_d63_sa hZ_d63_pos A_swap B_tilt hA_swap_sa hB_tilt_sa
  have hhess_ne : (secondFDerivLogPartitionReadout H_d63 A_swap B_tilt).re ≠ 0 := by
    rw [halign.2.1]
    exact ne_of_gt cbkm_H_d63_A_swap_B_tilt_pos
  let E01_i : GibbsOperator 2 := matrixOp !![0, Complex.I; 0, 0]
  have hx1_add : x1.1 (switchOp2 + E01_i) = x1.1 switchOp2 + x1.1 E01_i :=
    x1.1.map_add switchOp2 E01_i
  have hcomm_eq : x1.1 switchOp2 * x1.1 (switchOp2 + E01_i) -
      x1.1 (switchOp2 + E01_i) * x1.1 switchOp2 = (-2 : ℝ) • Q - Complex.I • tiltOp2 := by
    rw [hx1_add, mul_add, add_mul]
    have hsub : x1.1 switchOp2 * x1.1 switchOp2 + x1.1 switchOp2 * x1.1 E01_i -
        (x1.1 switchOp2 * x1.1 switchOp2 + x1.1 E01_i * x1.1 switchOp2) =
        x1.1 switchOp2 * x1.1 E01_i - x1.1 E01_i * x1.1 switchOp2 := by abel
    rw [hsub]
    apply matrixOfOp_injective
    change matrixOfOp (((Complex.I • B_tilt) * switchOp2 - switchOp2 * (Complex.I • B_tilt)) *
        ((Complex.I • B_tilt) * E01_i - E01_i * (Complex.I • B_tilt)) -
      ((Complex.I • B_tilt) * E01_i - E01_i * (Complex.I • B_tilt)) *
        ((Complex.I • B_tilt) * switchOp2 - switchOp2 * (Complex.I • B_tilt))) =
      matrixOfOp ((-2 : ℝ) • Q - Complex.I • tiltOp2)
    dsimp only [Q, E01_i]
    rw [matrixOfOp_sub_eq, matrixOfOp_mul_eq, matrixOfOp_mul_eq,
      matrixOfOp_sub_eq, matrixOfOp_mul_eq, matrixOfOp_mul_eq,
      matrixOfOp_sub_eq, matrixOfOp_mul_eq, matrixOfOp_mul_eq,
      matrixOfOp_sub_eq, matrixOfOp_real_smul, matrixOfOp_complex_smul,
      matrixOfOp_complex_smul, matrixOfOp_complex_smul,
      switchOp2_eq_A_swap, matrixOfOp_B_tilt, matrixOfOp_A_swap, matrixOfOp_tiltOp2,
      matrixOfOp_matrixOp]
    ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [Complex.ext_iff, tiltedMatrix, swapMatrix,
        InfoGeometry.Physics.KleinBottleSewingExact.tilt2, Matrix.mul_apply,
        Fin.sum_univ_two, Matrix.vecMul, dotProduct]
  have hnoncomm : x1.1 switchOp2 * x1.1 (switchOp2 + E01_i) ≠
      x1.1 (switchOp2 + E01_i) * x1.1 switchOp2 := by
    intro heq
    have hm := congrArg (fun M : GibbsOperator 2 => matrixOfOp M 0 0) (sub_eq_zero.mpr heq)
    rw [hcomm_eq, matrixOfOp_sub_eq, matrixOfOp_real_smul, matrixOfOp_complex_smul,
      matrixOfOp_complex_smul, switchOp2_eq_A_swap, matrixOfOp_A_swap, matrixOfOp_tiltOp2,
      matrixOfOp_zero] at hm
    simp [swapMatrix, InfoGeometry.Physics.KleinBottleSewingExact.tilt2] at hm
  have hτ_x1_sw : τ (x1.1 switchOp2) = -(x1.1 switchOp2) := by
    have hval : x1.1 switchOp2 = Complex.I • (B_tilt * switchOp2 - switchOp2 * B_tilt) := by
      change (Complex.I • B_tilt) * switchOp2 - switchOp2 * (Complex.I • B_tilt) = _
      rw [smul_mul_assoc, mul_smul_comm, smul_sub]
    rw [hval]
    apply conjStarAlgEquiv_purelyImaginary_odd
    rw [conjStarAlgEquiv_apply, conjOpFun]
    apply matrixOfOp_injective
    rw [matrixOfOp_matrixOp, matrixOfOp_sub_eq, matrixOfOp_mul_eq, matrixOfOp_mul_eq,
      switchOp2_eq_A_swap, matrixOfOp_B_tilt, matrixOfOp_A_swap]
    ext i j; fin_cases i <;> fin_cases j <;> simp [tiltedMatrix, swapMatrix]
  have hτ_x1_E01 : τ (x1.1 E01_i) = x1.1 E01_i := by
    rw [conjStarAlgEquiv_apply, conjOpFun]
    apply matrixOfOp_injective
    change matrixOfOp (matrixOp ((matrixOfOp ((Complex.I • B_tilt) * E01_i -
        E01_i * (Complex.I • B_tilt))).map (starRingEnd ℂ))) =
      matrixOfOp ((Complex.I • B_tilt) * E01_i - E01_i * (Complex.I • B_tilt))
    dsimp only [E01_i]
    rw [matrixOfOp_matrixOp, matrixOfOp_sub_eq, matrixOfOp_mul_eq, matrixOfOp_mul_eq,
      matrixOfOp_complex_smul, matrixOfOp_B_tilt, matrixOfOp_matrixOp]
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [tiltedMatrix]
  have hortho_diss : centeredBKMRealCovariance D_t hpow_t (x1.1 switchOp2) (x1.1 E01_i) = 0 := by
    have hinv := centeredBKMRealCovariance_aut τ D_t hpow_t
      (aut_faithfulGibbsDensity_rho τ tiltOp2 tiltOp2_isSelfAdjoint
        (tracedExponential_re_pos_of_isSelfAdjoint tiltOp2 tiltOp2_isSelfAdjoint) conj_tiltOp2)
      (conjStarAlgEquiv_trace_re (n := 2)) (x1.1 switchOp2) (x1.1 E01_i)
    rw [hτ_x1_sw, hτ_x1_E01, ← centeredBKMRealCovarianceBilin_apply, _root_.map_neg,
      LinearMap.neg_apply, centeredBKMRealCovarianceBilin_apply] at hinv
    linarith
  have hx1_sw_not_gauge : x1.1 switchOp2 ∉ scalarGauge 2 := by
    apply matrixOp_ne_scalarGauge _ 0 1 (by decide)
    change matrixOfOp ((Complex.I • B_tilt) * switchOp2 - switchOp2 * (Complex.I • B_tilt)) 0 1 ≠ 0
    rw [matrixOfOp_sub_eq, matrixOfOp_mul_eq, matrixOfOp_mul_eq, matrixOfOp_complex_smul,
      switchOp2_eq_A_swap, matrixOfOp_B_tilt, matrixOfOp_A_swap]
    norm_num [Complex.ext_iff, tiltedMatrix, swapMatrix, Matrix.mul_apply, Fin.sum_univ_two]
  have hdiss_ne : PP.dissipative ωA ωB ≠ 0 := by
    rw [centeredBKMOnsagerFormPairingOfAut_ofValueParity_dissipative]
    change centeredBKMRealCovariance D_t hpow_t (x1.1 switchOp2) (x1.1 (switchOp2 + E01_i)) ≠ 0
    rw [hx1_add, ← centeredBKMRealCovarianceBilin_apply,
      (centeredBKMRealCovarianceBilin D_t hpow_t (x1.1 switchOp2)).map_add
        (x1.1 switchOp2) (x1.1 E01_i),
      centeredBKMRealCovarianceBilin_apply, centeredBKMRealCovarianceBilin_apply,
      hortho_diss, add_zero]
    exact ne_of_gt (centeredBKMRealCovariance_self_pos_of_not_scalarGauge
      tiltOp2_isSelfAdjoint (tracedExponential_re_pos_of_isSelfAdjoint tiltOp2 tiltOp2_isSelfAdjoint)
      _ hx1_sw_not_gauge)
  let τU := adGammaStarAlgEquiv tiltOp2 tiltOp2_isSelfAdjoint tiltOp2_sq
  have hτU_rho : τU D_t.rho = D_t.rho :=
    adGammaStarAlgEquiv_gibbs_fixed tiltOp2 tiltOp2 tiltOp2_isSelfAdjoint
      (tracedExponential_re_pos_of_isSelfAdjoint tiltOp2 tiltOp2_isSelfAdjoint)
      tiltOp2_isSelfAdjoint tiltOp2_sq (Commute.refl tiltOp2)
  have hτU_tr := adGammaStarAlgEquiv_trace_re tiltOp2 tiltOp2_isSelfAdjoint tiltOp2_sq
  have hτU_Itilt : τU (Complex.I • tiltOp2) = Complex.I • tiltOp2 := by
    apply matrixOfOp_injective
    change matrixOfOp (tiltOp2 * (Complex.I • tiltOp2) * tiltOp2) = matrixOfOp (Complex.I • tiltOp2)
    rw [mul_smul_comm, smul_mul_assoc, tiltOp2_sq, one_mul]
  have hτU_Q : τU Q = -Q := by
    apply adGammaStarAlgEquiv_odd_of_anticomm tiltOp2 Q tiltOp2_isSelfAdjoint tiltOp2_sq
    dsimp only [Q]
    rw [mul_smul_comm, smul_mul_assoc, tiltOp2_switchOp2_anticomm, smul_neg, neg_neg]
  have hortho : D_t.bkmRealBilinForm hpow_t (Complex.I • tiltOp2) Q = 0 := by
    have hinv := bkmRealBilinForm_aut τU D_t hpow_t hτU_rho hτU_tr (Complex.I • tiltOp2) Q
    rw [hτU_Itilt, hτU_Q, _root_.map_neg] at hinv
    linarith
  have hQ_ne : Q ≠ 0 := by
    intro h0
    have hm := congrArg (fun M : GibbsOperator 2 => matrixOfOp M 0 1) h0
    dsimp only [Q] at hm
    rw [switchOp2_eq_A_swap, matrixOfOp_complex_smul, matrixOfOp_A_swap, matrixOfOp_zero] at hm
    simp [swapMatrix] at hm
  have hrev_ne : PP.reversible ωA ωB ≠ 0 := by
    rw [centeredBKMOnsagerFormPairingOfAut_ofValueParity_reversible, commutatorBKMProbeForm_apply]
    change D_t.bkmRealBilinForm hpow_t (x1.1 switchOp2 * x1.1 (switchOp2 + E01_i) -
      x1.1 (switchOp2 + E01_i) * x1.1 switchOp2) Q ≠ 0
    rw [hcomm_eq, (D_t.bkmRealBilinForm hpow_t).map_sub ((-2 : ℝ) • Q) (Complex.I • tiltOp2),
      LinearMap.sub_apply, hortho, sub_zero,
      (D_t.bkmRealBilinForm hpow_t).map_smul (-2 : ℝ) Q,
      LinearMap.smul_apply, smul_eq_mul]
    have hpos : 0 < D_t.bkmRealBilinForm hpow_t Q Q :=
      (D_t.bkmRealBilinForm_self_pos_iff hpow_t Q).mpr hQ_ne
    linarith
  exact ⟨halign.1, halign.2.1, hhess_ne, onsager_pairing_derivationForm_reciprocity _ PP _ _,
    hnoncomm, hdiss_ne, hrev_ne⟩

/-- `T1-F5-05`: `ParityOnsagerFormPairing` at degrees `n = 1` and `n = 2` satisfies parity, reciprocity, and nonzero diagonal/off-diagonal pairings. -/
theorem t1_f5_05_parityOnsagerFormPairingDegrees12 :
    let D := faithfulGibbsDensity H_d63 hH_d63_sa hZ_d63_pos
    let hpow := continuous_faithfulGibbsDensity_rpow H_d63 hH_d63_sa hZ_d63_pos
    let K := realDerivationsLane (GibbsOperator 2)
    let d1 := innerDerivation tiltOp2
    let d2 := innerDerivation (tiltOp2 * switchOp2)
    let P1 := centeredBKMOnsagerFormPairing_ofValueParity D hpow tiltOp2 tiltOp2_isSelfAdjoint ![d1]
    let P2 := centeredBKMOnsagerFormPairing_ofValueParity D hpow tiltOp2 tiltOp2_isSelfAdjoint ![d1, d2]
    let ω1 : DerivationOperatorForm K 1 :=
      oneFormAlternatingLinearEquiv K (exteriorDerivativeZero K A_swap)
    let η1 : DerivationOperatorForm K 1 :=
      oneFormAlternatingLinearEquiv K (exteriorDerivativeZero K (matrixOp !![0, 1; 0, 0]))
    let ω2 : DerivationOperatorForm K 2 :=
      ceCurvature K (oneFormAlternatingLinearEquiv K (exteriorDerivativeZero K A_swap))
    let η2 : DerivationOperatorForm K 2 :=
      ceCurvature K (oneFormAlternatingLinearEquiv K (exteriorDerivativeZero K (matrixOp !![0, 1; 0, 0])))
    P1.dissipative (P1.T.op ω1) (P1.T.op ω1) = P1.dissipative ω1 ω1 ∧
      P1.reversible (P1.T.op ω1) (P1.T.op η1) = -P1.reversible ω1 η1 ∧
      P1.toParityOnsagerSystem.totalGenerator (P1.toParityOnsagerSystem.T.op ω1)
        (P1.toParityOnsagerSystem.T.op η1) = P1.toParityOnsagerSystem.totalGenerator η1 ω1 ∧
      P1.dissipative ω1 ω1 ≠ 0 ∧
      P1.reversible ω1 η1 ≠ 0 ∧
      P2.dissipative (P2.T.op ω2) (P2.T.op ω2) = P2.dissipative ω2 ω2 ∧
      P2.reversible (P2.T.op ω2) (P2.T.op η2) = -P2.reversible ω2 η2 ∧
      P2.toParityOnsagerSystem.totalGenerator (P2.toParityOnsagerSystem.T.op ω2)
        (P2.toParityOnsagerSystem.T.op η2) = P2.toParityOnsagerSystem.totalGenerator η2 ω2 ∧
      P2.dissipative ω2 ω2 ≠ 0 ∧
      P2.reversible ω2 η2 ≠ 0 := by
  intro D hpow K d1 d2 P1 P2 ω1 η1 ω2 η2
  have htilt_ne : tiltOp2 ≠ 0 := by
    intro h0
    have hm := congrArg (fun M : GibbsOperator 2 => matrixOfOp M 0 0) h0
    rw [tiltOp2, matrixOfOp_matrixOp, matrixOfOp_zero] at hm
    norm_num [InfoGeometry.Physics.KleinBottleSewingExact.tilt2] at hm
  have hQ_pos : 0 < D.bkmRealBilinForm hpow tiltOp2 tiltOp2 :=
    (D.bkmRealBilinForm_self_pos_iff hpow tiltOp2).mpr htilt_ne
  have hω1_not_gauge : ω1 ![d1] ∉ scalarGauge 2 := by
    apply matrixOp_ne_scalarGauge _ 0 1 (by decide)
    change matrixOfOp (tiltOp2 * A_swap - A_swap * tiltOp2) 0 1 ≠ 0
    rw [matrixOfOp_sub_eq, matrixOfOp_mul_eq, matrixOfOp_mul_eq, matrixOfOp_tiltOp2, matrixOfOp_A_swap]
    norm_num [InfoGeometry.Physics.KleinBottleSewingExact.tilt2, swapMatrix,
      Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct]
  have hP1_diss : P1.dissipative ω1 ω1 ≠ 0 := by
    rw [centeredBKMOnsagerFormPairing_ofValueParity_dissipative]
    exact ne_of_gt (centeredBKMRealCovariance_self_pos_of_not_scalarGauge hH_d63_sa hZ_d63_pos _ hω1_not_gauge)
  have hcomm1 : ω1 ![d1] * η1 ![d1] - η1 ![d1] * ω1 ![d1] = (4 : ℝ) • tiltOp2 := by
    apply matrixOfOp_injective
    change matrixOfOp ((tiltOp2 * A_swap - A_swap * tiltOp2) *
        (tiltOp2 * matrixOp !![0, 1; 0, 0] - matrixOp !![0, 1; 0, 0] * tiltOp2) -
      (tiltOp2 * matrixOp !![0, 1; 0, 0] - matrixOp !![0, 1; 0, 0] * tiltOp2) *
        (tiltOp2 * A_swap - A_swap * tiltOp2)) =
      matrixOfOp ((4 : ℝ) • tiltOp2)
    rw [matrixOfOp_sub_eq, matrixOfOp_mul_eq, matrixOfOp_mul_eq,
      matrixOfOp_sub_eq, matrixOfOp_mul_eq, matrixOfOp_mul_eq,
      matrixOfOp_sub_eq, matrixOfOp_mul_eq, matrixOfOp_mul_eq,
      matrixOfOp_real_smul, matrixOfOp_tiltOp2, matrixOfOp_A_swap, matrixOfOp_matrixOp]
    ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [InfoGeometry.Physics.KleinBottleSewingExact.tilt2, swapMatrix,
        Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct]
  have hP1_rev : P1.reversible ω1 η1 ≠ 0 := by
    rw [centeredBKMOnsagerFormPairing_ofValueParity_reversible, commutatorBKMProbeForm_apply,
      hcomm1, _root_.map_smul, LinearMap.smul_apply, smul_eq_mul]
    linarith
  have hω2_val : ω2 ![d1, d2] = (-8 : ℝ) • A_swap := by
    dsimp only [ω2]
    rw [ceCurvature_eq]
    change connectionCurvature K (exteriorDerivativeZero K A_swap) d1 d2 = (-8 : ℝ) • A_swap
    rw [connectionCurvature, exteriorDerivativeOne_exteriorDerivativeZero, zero_add]
    apply matrixOfOp_injective
    change matrixOfOp ((tiltOp2 * A_swap - A_swap * tiltOp2) *
        ((tiltOp2 * switchOp2) * A_swap - A_swap * (tiltOp2 * switchOp2)) -
      ((tiltOp2 * switchOp2) * A_swap - A_swap * (tiltOp2 * switchOp2)) *
        (tiltOp2 * A_swap - A_swap * tiltOp2)) =
      matrixOfOp ((-8 : ℝ) • A_swap)
    simp only [matrixOfOp_sub_eq, matrixOfOp_mul_eq, matrixOfOp_real_smul, switchOp2_eq_A_swap,
      matrixOfOp_tiltOp2, matrixOfOp_A_swap]
    ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [InfoGeometry.Physics.KleinBottleSewingExact.tilt2, swapMatrix,
        Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct]
  have hω2_not_gauge : ω2 ![d1, d2] ∉ scalarGauge 2 := by
    apply matrixOp_ne_scalarGauge _ 0 1 (by decide)
    rw [hω2_val, matrixOfOp_real_smul, matrixOfOp_A_swap]
    norm_num [swapMatrix]
  have hP2_diss : P2.dissipative ω2 ω2 ≠ 0 := by
    rw [centeredBKMOnsagerFormPairing_ofValueParity_dissipative]
    exact ne_of_gt (centeredBKMRealCovariance_self_pos_of_not_scalarGauge hH_d63_sa hZ_d63_pos _ hω2_not_gauge)
  have hη2_val : η2 ![d1, d2] = (-4 : ℝ) • matrixOp !![0, 1; 0, 0] := by
    dsimp only [η2]
    rw [ceCurvature_eq]
    change connectionCurvature K (exteriorDerivativeZero K (matrixOp !![0, 1; 0, 0])) d1 d2 = _
    rw [connectionCurvature, exteriorDerivativeOne_exteriorDerivativeZero, zero_add]
    apply matrixOfOp_injective
    change matrixOfOp ((tiltOp2 * matrixOp !![0, 1; 0, 0] - matrixOp !![0, 1; 0, 0] * tiltOp2) *
        ((tiltOp2 * switchOp2) * matrixOp !![0, 1; 0, 0] -
          matrixOp !![0, 1; 0, 0] * (tiltOp2 * switchOp2)) -
      ((tiltOp2 * switchOp2) * matrixOp !![0, 1; 0, 0] -
          matrixOp !![0, 1; 0, 0] * (tiltOp2 * switchOp2)) *
        (tiltOp2 * matrixOp !![0, 1; 0, 0] - matrixOp !![0, 1; 0, 0] * tiltOp2)) =
      matrixOfOp ((-4 : ℝ) • (matrixOp !![0, 1; 0, 0] : GibbsOperator 2))
    simp only [matrixOfOp_sub_eq, matrixOfOp_mul_eq, matrixOfOp_real_smul, switchOp2_eq_A_swap,
      matrixOfOp_tiltOp2, matrixOfOp_A_swap, matrixOfOp_matrixOp]
    ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [InfoGeometry.Physics.KleinBottleSewingExact.tilt2, swapMatrix,
        Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct]
  have hcomm2 : ω2 ![d1, d2] * η2 ![d1, d2] - η2 ![d1, d2] * ω2 ![d1, d2] = (-32 : ℝ) • tiltOp2 := by
    rw [hω2_val, hη2_val]
    apply matrixOfOp_injective
    rw [matrixOfOp_sub_eq, matrixOfOp_mul_eq, matrixOfOp_mul_eq,
      matrixOfOp_real_smul, matrixOfOp_real_smul, matrixOfOp_real_smul,
      matrixOfOp_A_swap, matrixOfOp_tiltOp2, matrixOfOp_matrixOp]
    ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [swapMatrix, InfoGeometry.Physics.KleinBottleSewingExact.tilt2,
        Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct]
  have hP2_rev : P2.reversible ω2 η2 ≠ 0 := by
    rw [centeredBKMOnsagerFormPairing_ofValueParity_reversible, commutatorBKMProbeForm_apply,
      hcomm2, _root_.map_smul, LinearMap.smul_apply, smul_eq_mul]
    linarith
  exact ⟨P1.dissipative_T_even ω1 ω1, P1.reversible_T_odd ω1 η1,
    P1.toParityOnsagerSystem.onsager_casimir_master_reciprocity ω1 η1,
    hP1_diss, hP1_rev,
    P2.dissipative_T_even ω2 ω2, P2.reversible_T_odd ω2 η2,
    P2.toParityOnsagerSystem.onsager_casimir_master_reciprocity ω2 η2,
    hP2_diss, hP2_rev⟩

/-- `T2-F4-01`: Zero probe `Q = 0` annihilates reversible part while keeping positive dissipation. -/
theorem t2_f4_01_zeroProbeSystem :
    let sys := finiteGibbsCEOnsagerSystem H_d63 hH_d63_sa hZ_d63_pos A_swap 0
    let d := innerDerivation H_d63
    (∀ d1 d2, sys.reversible d1 d2 = 0) ∧ 0 < sys.dissipative d d := by
  intro sys d
  refine ⟨fun d1 d2 => ?_, ?_⟩
  · change ceCurvatureBKMProbeForm _ _ A_swap 0 d1 d2 = 0
    rw [ceCurvatureBKMProbeForm_apply, map_zero]
  · let D := faithfulGibbsDensity H_d63 hH_d63_sa hZ_d63_pos
    let hpow := continuous_faithfulGibbsDensity_rpow H_d63 hH_d63_sa hZ_d63_pos
    change 0 < centeredCEBKMForm D hpow A_swap d d
    rw [centeredCEBKMForm_apply, centeredBKMRealCovariance_self, D.bkmRealBilinForm_apply]
    apply D.kuboMoriPairing_self_re_pos _ hpow
    intro hzero
    have hmem := (centeredStatistic_eq_zero_iff D hpow _).mp hzero
    obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp hmem
    have hm := congrArg (fun Z : GibbsOperator 2 => matrixOfOp Z 0 1) hr
    change matrixOfOp (r • (1 : GibbsOperator 2)) 0 1 =
      matrixOfOp (H_d63 * A_swap - A_swap * H_d63) 0 1 at hm
    rw [matrixOfOp_sub_eq, matrixOfOp_mul_eq, matrixOfOp_mul_eq,
      matrixOfOp_real_smul, matrixOfOp_one_eq, H_d63, A_swap, matrixOfOp_matrixOp,
      matrixOfOp_matrixOp] at hm
    norm_num [d63TiltedAmplitude, swapMatrix, Matrix.mul_apply, Fin.sum_univ_two] at hm

/-- `T2-F4-02`: Self-adjoint curvature pair `(d1_sa, d2_sa)` witnesses non-zero `T`-odd sign flip with `B_tilt`, while anti-self-adjoint probe `Q_odd` flips `ceCurvatureBKMProbeForm` to `T`-even (`≠ 0`). -/
theorem t2_f4_02_starSignFlipProbe :
    let D := faithfulGibbsDensity H_d63 hH_d63_sa hZ_d63_pos
    let hpow := continuous_faithfulGibbsDensity_rpow H_d63 hH_d63_sa hZ_d63_pos
    let T := starDerivationTimeReversal 2
    let d1_sa := innerDerivation tiltOp2
    let d2_sa := innerDerivation (tiltOp2 * switchOp2)
    let d1 := innerDerivation tiltOp2
    let d2 := innerDerivation (Complex.I • (tiltOp2 * switchOp2))
    ceCurvatureBKMProbeForm D hpow A_swap B_tilt (T.op d1_sa) (T.op d2_sa) =
        -ceCurvatureBKMProbeForm D hpow A_swap B_tilt d1_sa d2_sa ∧
      ceCurvatureBKMProbeForm D hpow A_swap B_tilt d1_sa d2_sa ≠ 0 ∧
      ceCurvatureBKMProbeForm D hpow A_swap Q_odd (T.op d1) (T.op d2) =
        ceCurvatureBKMProbeForm D hpow A_swap Q_odd d1 d2 ∧
      ceCurvatureBKMProbeForm D hpow A_swap Q_odd d1 d2 ≠ 0 := by
  intro D hpow T d1_sa d2_sa d1 d2
  have heven := ceCurvatureBKMProbeForm_starDerivation_eq D hpow A_swap Q_odd
    (Or.inl rfl) (by rw [hA_swap_sa.star_eq, one_smul]) d1 d2
  rw [hQ_odd_anti] at heven
  have hneg : ceCurvatureBKMProbeForm D hpow A_swap (-Q_odd) d1 d2 =
      -ceCurvatureBKMProbeForm D hpow A_swap Q_odd d1 d2 := by
    rw [ceCurvatureBKMProbeForm_apply, ceCurvatureBKMProbeForm_apply, map_neg]
  rw [hneg, neg_neg] at heven
  have hcurv :
      connectionCurvature (realDerivationsLane (GibbsOperator 2))
          (exteriorDerivativeZero (realDerivationsLane (GibbsOperator 2)) A_swap) d1 d2 =
        (-8 : ℝ) • Q_odd := by
    rw [connectionCurvature, exteriorDerivativeOne_exteriorDerivativeZero, zero_add]
    change (tiltOp2 * A_swap - A_swap * tiltOp2) *
          ((Complex.I • (tiltOp2 * switchOp2)) * A_swap -
            A_swap * (Complex.I • (tiltOp2 * switchOp2))) -
        ((Complex.I • (tiltOp2 * switchOp2)) * A_swap -
            A_swap * (Complex.I • (tiltOp2 * switchOp2))) *
          (tiltOp2 * A_swap - A_swap * tiltOp2) =
      (-8 : ℝ) • Q_odd
    apply matrixOfOp_injective
    rw [Q_odd, matrixOfOp_sub_eq, matrixOfOp_mul_eq, matrixOfOp_mul_eq,
      matrixOfOp_sub_eq, matrixOfOp_mul_eq, matrixOfOp_mul_eq,
      matrixOfOp_sub_eq, matrixOfOp_mul_eq, matrixOfOp_mul_eq,
      matrixOfOp_real_smul, matrixOfOp_complex_smul, matrixOfOp_complex_smul,
      switchOp2_eq_A_swap, tiltOp2, A_swap, matrixOfOp_mul_eq, matrixOfOp_matrixOp]
    ext i j
    fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
      simp [InfoGeometry.Physics.KleinBottleSewingExact.tilt2, swapMatrix,
        Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct] <;> norm_num
  have hQne : Q_odd ≠ 0 := by
    intro h0
    have hm := congrArg (fun Z : GibbsOperator 2 => matrixOfOp Z 0 1) h0
    rw [Q_odd, matrixOfOp_complex_smul, A_swap, matrixOfOp_matrixOp, matrixOfOp_zero] at hm
    simp [swapMatrix] at hm
  have hne : ceCurvatureBKMProbeForm D hpow A_swap Q_odd d1 d2 ≠ 0 := by
    rw [ceCurvatureBKMProbeForm_apply, hcurv, _root_.map_smul, LinearMap.smul_apply, smul_eq_mul]
    have hpos : 0 < D.bkmRealBilinForm hpow Q_odd Q_odd :=
      (D.bkmRealBilinForm_self_pos_iff hpow Q_odd).mpr hQne
    linarith
  have hBt_ne : ceCurvatureBKMProbeForm D hpow A_swap B_tilt d1_sa d2_sa ≠ 0 :=
    t1_f5_03_ceCurvatureEqAndBkmProbe.2.2.2
  exact ⟨ceCurvatureBKMProbeForm_starDerivation_odd D hpow A_swap B_tilt hA_swap_sa hB_tilt_sa d1_sa d2_sa,
    hBt_ne, heven, hne⟩

/-- `T2-F4-03`: `*`-automorphism `τ` sign-flip (`Q_odd` vs `Q_even`), `Q_even` `reversible_T_even` nonzero parity, and `τ H_bad ≠ H_bad` / `τ D_bad.rho ≠ D_bad.rho` obstruction. -/
theorem t2_f4_03_autSignFlipAndBadHamiltonian :
    let U := tiltOp2
    let τ := adGammaStarAlgEquiv U tiltOp2_isSelfAdjoint tiltOp2_sq
    let H_good : GibbsOperator 2 := matrixOp !![2, 0; 0, 1]
    let Q_even := H_good
    let H_bad := A_swap
    let D_bad := faithfulGibbsDensity H_bad hA_swap_sa
      (tracedExponential_re_pos_of_isSelfAdjoint H_bad hA_swap_sa)
    have hH_good : IsSelfAdjoint H_good := by
      rw [isSelfAdjoint_iff]
      apply matrixOfOp_injective
      change matrixOfOp (ContinuousLinearMap.adjoint H_good) = matrixOfOp H_good
      dsimp only [H_good]
      rw [matrixOfOp_adjoint, matrixOfOp_matrixOp]
      ext i j; fin_cases i <;> fin_cases j <;> simp
    let hZ_good := tracedExponential_re_pos_of_isSelfAdjoint H_good hH_good
    let D_good := faithfulGibbsDensity H_good hH_good hZ_good
    let hpow_good := continuous_faithfulGibbsDensity_rpow H_good hH_good hZ_good
    let T := autDerivationTimeReversal τ
      (adGammaStarAlgEquiv_involutive U tiltOp2_isSelfAdjoint tiltOp2_sq)
    let d1 := innerDerivation switchOp2
    let d2 := innerDerivation (tiltOp2 * switchOp2)
    τ A_swap = -A_swap ∧
      τ Q_even = Q_even ∧
      τ H_bad = -H_bad ∧
      τ H_bad ≠ H_bad ∧
      τ D_bad.rho ≠ D_bad.rho ∧
      ceCurvatureBKMProbeForm D_good hpow_good tiltOp2 Q_even (T.op d1) (T.op d2) =
        ceCurvatureBKMProbeForm D_good hpow_good tiltOp2 Q_even d1 d2 ∧
      ceCurvatureBKMProbeForm D_good hpow_good tiltOp2 Q_even d1 d2 ≠ 0 := by
  intro U τ H_good Q_even H_bad D_bad hH_good hZ_good D_good hpow_good T d1 d2
  have hQodd : τ A_swap = -A_swap := by
    apply adGammaStarAlgEquiv_odd_of_anticomm U A_swap tiltOp2_isSelfAdjoint tiltOp2_sq
    dsimp only [U]
    rw [← switchOp2_eq_A_swap, tiltOp2_switchOp2_anticomm, neg_neg]
  have hQeven : τ Q_even = Q_even := by
    change U * H_good * U = H_good
    apply matrixOfOp_injective
    dsimp only [U, H_good]
    rw [matrixOfOp_mul_eq, matrixOfOp_mul_eq, tiltOp2, matrixOfOp_matrixOp,
      matrixOfOp_matrixOp]
    ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [InfoGeometry.Physics.KleinBottleSewingExact.tilt2, Matrix.mul_apply,
        Fin.sum_univ_two]
  have hne : τ H_bad ≠ H_bad := by
    dsimp only [H_bad]
    rw [hQodd]
    intro heq
    have hm := congrArg (fun Z : GibbsOperator 2 => matrixOfOp Z 0 1) heq
    rw [matrixOfOp_neg_eq, A_swap, matrixOfOp_matrixOp] at hm
    norm_num [swapMatrix] at hm
  have hD_bad_rho : D_bad.rho =
      (1 / 2 : ℝ) • (1 : GibbsOperator 2) + (Real.tanh 1 / 2) • A_swap := by
    have hexp : NormedSpace.exp A_swap =
        Real.cosh 1 • (1 : GibbsOperator 2) + Real.sinh 1 • A_swap := by
      simpa using exp_real_smul_A_swap 1
    have htr1 : finiteOperatorTrace (1 : GibbsOperator 2) = 2 := by
      change Matrix.trace (matrixOfOp (1 : GibbsOperator 2)) = 2
      rw [matrixOfOp_one_eq]; norm_num [Matrix.trace, Matrix.diag, Fin.sum_univ_two]
    have htrA : finiteOperatorTrace A_swap = 0 := by
      change Matrix.trace (matrixOfOp A_swap) = 0
      rw [matrixOfOp_A_swap]; norm_num [swapMatrix, Matrix.trace, Matrix.diag, Fin.sum_univ_two]
    have hZ_bad : gibbsPartitionReal A_swap = 2 * Real.cosh 1 := by
      have htr : tracedExponential A_swap = ((2 * Real.cosh 1 : ℝ) : ℂ) := by
        unfold tracedExponential
        rw [hexp, real_smul_eq_complex_smul, real_smul_eq_complex_smul,
          (finiteOperatorTraceCLM 2).map_add, (finiteOperatorTraceCLM 2).map_smul,
          (finiteOperatorTraceCLM 2).map_smul]
        change (Real.cosh 1 : ℂ) • finiteOperatorTrace 1 +
            (Real.sinh 1 : ℂ) • finiteOperatorTrace A_swap = _
        rw [htr1, htrA, smul_eq_mul, smul_eq_mul, mul_zero, add_zero]
        push_cast; ring
      have hre := congrArg Complex.re htr
      exact hre
    dsimp only [D_bad, H_bad]
    erw [faithfulGibbsDensity_rho_eq_normalizedExponential]
    unfold normalizedExponential
    rw [tracedExponential_eq_gibbsPartitionReal A_swap hA_swap_sa, hZ_bad, hexp]
    have hcosh_ne : Real.cosh 1 ≠ 0 := ne_of_gt (Real.cosh_pos 1)
    have hinv_smul : ∀ (c : ℝ) (X : GibbsOperator 2), ((c : ℂ)⁻¹) • X = (c⁻¹ : ℝ) • X := by
      intro c X; rw [← Complex.ofReal_inv, ← real_smul_eq_complex_smul]
    rw [hinv_smul (2 * Real.cosh 1), smul_add, smul_smul, smul_smul]
    congr 1
    · congr 1; field_simp [hcosh_ne]
    · congr 1; rw [Real.tanh_eq_sinh_div_cosh]; field_simp [hcosh_ne]
  have hrho_ne : τ D_bad.rho ≠ D_bad.rho := by
    intro heq
    rw [hD_bad_rho, _root_.map_add, _root_.map_smul, _root_.map_smul, _root_.map_one, hQodd,
      smul_neg, ← neg_smul] at heq
    have hm := congrArg (fun Z : GibbsOperator 2 => (matrixOfOp Z 0 1).re) heq
    simp only [matrixOfOp_add, matrixOfOp_real_smul, matrixOfOp_one_eq, matrixOfOp_A_swap,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply, swapMatrix,
      Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Fin.isValue,
      Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.one_re, Complex.one_im, mul_zero, sub_zero, zero_mul] at hm
    have ht : 0 < Real.tanh 1 := tanh_pos_of_pos one_pos
    linarith
  have hτ_tilt : τ tiltOp2 = tiltOp2 := by
    change U * tiltOp2 * U = tiltOp2
    dsimp only [U]
    rw [tiltOp2_sq, one_mul]
  have hτ_rho_good : τ D_good.rho = D_good.rho :=
    adGammaStarAlgEquiv_gibbs_fixed H_good U hH_good hZ_good tiltOp2_isSelfAdjoint tiltOp2_sq
      (by rw [Commute, SemiconjBy]; apply matrixOfOp_injective
          dsimp only [H_good, U]
          rw [matrixOfOp_mul_eq, matrixOfOp_mul_eq, matrixOfOp_tiltOp2, matrixOfOp_matrixOp]
          ext i j; fin_cases i <;> fin_cases j <;>
            norm_num [InfoGeometry.Physics.KleinBottleSewingExact.tilt2, Matrix.mul_apply,
              Fin.sum_univ_two])
  have hrev_even :
      ceCurvatureBKMProbeForm D_good hpow_good tiltOp2 Q_even (T.op d1) (T.op d2) =
        ceCurvatureBKMProbeForm D_good hpow_good tiltOp2 Q_even d1 d2 := by
    change ceCurvatureBKMProbeForm D_good hpow_good tiltOp2 Q_even
        ((autDerivationTimeReversal τ (adGammaStarAlgEquiv_involutive U tiltOp2_isSelfAdjoint tiltOp2_sq)).op d1)
        ((autDerivationTimeReversal τ (adGammaStarAlgEquiv_involutive U tiltOp2_isSelfAdjoint tiltOp2_sq)).op d2) = _
    rw [ceCurvatureBKMProbeForm_autDerivation_eq τ
      (adGammaStarAlgEquiv_involutive U tiltOp2_isSelfAdjoint tiltOp2_sq)
      D_good hpow_good hτ_rho_good
      (adGammaStarAlgEquiv_trace_re U tiltOp2_isSelfAdjoint tiltOp2_sq)
      tiltOp2 Q_even (Or.inl rfl) (by simpa using hτ_tilt) d1 d2, hQeven]
  have hH_good_decomp : H_good =
      (3 / 2 : ℝ) • (1 : GibbsOperator 2) + (1 / 2 : ℝ) • tiltOp2 := by
    apply matrixOfOp_injective
    dsimp only [H_good]
    rw [matrixOfOp_add, matrixOfOp_real_smul, matrixOfOp_real_smul, matrixOfOp_one_eq,
      matrixOfOp_tiltOp2, matrixOfOp_matrixOp]
    ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [InfoGeometry.Physics.KleinBottleSewingExact.tilt2]
  have hD_good_rho : D_good.rho =
      (1 / 2 : ℝ) • (1 : GibbsOperator 2) + (Real.tanh (1 / 2) / 2) • tiltOp2 := by
    have hcomm : Commute ((3 / 2 : ℝ) • (1 : GibbsOperator 2)) ((1 / 2 : ℝ) • tiltOp2) := by
      simp only [real_smul_eq_complex_smul]
      exact (Commute.one_left _).smul_left _ |>.smul_right _
    have hexp : NormedSpace.exp H_good =
        Real.exp (3 / 2) •
          (Real.cosh (1 / 2) • (1 : GibbsOperator 2) + Real.sinh (1 / 2) • tiltOp2) := by
      rw [hH_good_decomp, NormedSpace.exp_add_of_commute hcomm, exp_real_smul_one,
        exp_real_smul_tiltOp2]
      simp only [real_smul_eq_complex_smul, smul_mul_assoc, one_mul, smul_add, smul_smul]
    have htr1 : finiteOperatorTrace (1 : GibbsOperator 2) = 2 := by
      change Matrix.trace (matrixOfOp (1 : GibbsOperator 2)) = 2
      rw [matrixOfOp_one_eq]; norm_num [Matrix.trace, Matrix.diag, Fin.sum_univ_two]
    have htr_tilt : finiteOperatorTrace tiltOp2 = 0 := by
      change Matrix.trace (matrixOfOp tiltOp2) = 0
      rw [matrixOfOp_tiltOp2]
      norm_num [InfoGeometry.Physics.KleinBottleSewingExact.tilt2, Matrix.trace, Matrix.diag,
        Fin.sum_univ_two]
    have hZ_good_eq : gibbsPartitionReal H_good = 2 * Real.exp (3 / 2) * Real.cosh (1 / 2) := by
      have htr : tracedExponential H_good =
          ((2 * Real.exp (3 / 2) * Real.cosh (1 / 2) : ℝ) : ℂ) := by
        unfold tracedExponential
        rw [hexp, real_smul_eq_complex_smul, (finiteOperatorTraceCLM 2).map_smul,
          (finiteOperatorTraceCLM 2).map_add, real_smul_eq_complex_smul,
          real_smul_eq_complex_smul, (finiteOperatorTraceCLM 2).map_smul,
          (finiteOperatorTraceCLM 2).map_smul]
        change (Real.exp (3 / 2) : ℂ) •
            ((Real.cosh (1 / 2) : ℂ) • finiteOperatorTrace 1 +
              (Real.sinh (1 / 2) : ℂ) • finiteOperatorTrace tiltOp2) = _
        rw [htr1, htr_tilt, smul_eq_mul, smul_eq_mul, smul_eq_mul]
        push_cast; ring
      exact congrArg Complex.re htr
    dsimp only [D_good]
    erw [faithfulGibbsDensity_rho_eq_normalizedExponential]
    unfold normalizedExponential
    rw [tracedExponential_eq_gibbsPartitionReal H_good hH_good, hZ_good_eq, hexp]
    have hcosh_ne : Real.cosh (1 / 2) ≠ 0 := ne_of_gt (Real.cosh_pos _)
    have hexp_ne : Real.exp (3 / 2) ≠ 0 := ne_of_gt (Real.exp_pos _)
    have hinv_smul : ∀ (c : ℝ) (X : GibbsOperator 2), ((c : ℂ)⁻¹) • X = (c⁻¹ : ℝ) • X := by
      intro c X; rw [← Complex.ofReal_inv, ← real_smul_eq_complex_smul]
    rw [hinv_smul (2 * Real.exp (3 / 2) * Real.cosh (1 / 2)), smul_smul, smul_add,
      smul_smul, smul_smul]
    congr 1
    · congr 1; field_simp [hcosh_ne, hexp_ne]
    · congr 1; rw [Real.tanh_eq_sinh_div_cosh]; field_simp [hcosh_ne, hexp_ne]
  have hcurv_even :
      connectionCurvature (realDerivationsLane (GibbsOperator 2))
          (exteriorDerivativeZero (realDerivationsLane (GibbsOperator 2)) tiltOp2) d1 d2 =
        (8 : ℝ) • tiltOp2 := by
    rw [connectionCurvature, exteriorDerivativeOne_exteriorDerivativeZero, zero_add]
    change (switchOp2 * tiltOp2 - tiltOp2 * switchOp2) *
          ((tiltOp2 * switchOp2) * tiltOp2 - tiltOp2 * (tiltOp2 * switchOp2)) -
        ((tiltOp2 * switchOp2) * tiltOp2 - tiltOp2 * (tiltOp2 * switchOp2)) *
          (switchOp2 * tiltOp2 - tiltOp2 * switchOp2) =
      (8 : ℝ) • tiltOp2
    apply matrixOfOp_injective
    rw [matrixOfOp_sub_eq, matrixOfOp_mul_eq, matrixOfOp_mul_eq,
      matrixOfOp_sub_eq, matrixOfOp_mul_eq, matrixOfOp_mul_eq,
      matrixOfOp_sub_eq, matrixOfOp_mul_eq, matrixOfOp_mul_eq,
      matrixOfOp_mul_eq, matrixOfOp_mul_eq, matrixOfOp_real_smul,
      switchOp2_eq_A_swap, matrixOfOp_tiltOp2, matrixOfOp_A_swap]
    ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [InfoGeometry.Physics.KleinBottleSewingExact.tilt2, swapMatrix,
        Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct]
  have hrev_ne : ceCurvatureBKMProbeForm D_good hpow_good tiltOp2 Q_even d1 d2 ≠ 0 := by
    rw [ceCurvatureBKMProbeForm_apply, hcurv_even, (D_good.bkmRealBilinForm hpow_good).map_smul,
      LinearMap.smul_apply, smul_eq_mul]
    have hQ_decomp : Q_even = (3 / 2 : ℝ) • (1 : GibbsOperator 2) + (1 / 2 : ℝ) • tiltOp2 :=
      hH_good_decomp
    rw [hQ_decomp, (D_good.bkmRealBilinForm hpow_good tiltOp2).map_add,
      (D_good.bkmRealBilinForm hpow_good tiltOp2).map_smul,
      (D_good.bkmRealBilinForm hpow_good tiltOp2).map_smul,
      smul_eq_mul, smul_eq_mul, bkmRealBilinForm_one_right D_good hpow_good tiltOp2]
    have hexp_tilt : expectationReal D_good tiltOp2 = Real.tanh (1 / 2) := by
      unfold expectationReal
      rw [hD_good_rho, add_mul, real_smul_eq_complex_smul, real_smul_eq_complex_smul,
        smul_mul_assoc, smul_mul_assoc, one_mul, ← finiteOperatorTraceLinear_apply,
        _root_.map_add, _root_.map_smul, _root_.map_smul, finiteOperatorTraceLinear_apply,
        finiteOperatorTraceLinear_apply]
      have htr_tilt : finiteOperatorTrace tiltOp2 = 0 := by
        change Matrix.trace (matrixOfOp tiltOp2) = 0
        rw [matrixOfOp_tiltOp2]
        norm_num [InfoGeometry.Physics.KleinBottleSewingExact.tilt2, Matrix.trace, Matrix.diag,
          Fin.sum_univ_two]
      have htr_tt : finiteOperatorTrace (tiltOp2 * tiltOp2) = 2 := by
        rw [tiltOp2_sq]
        change Matrix.trace (matrixOfOp (1 : GibbsOperator 2)) = 2
        rw [matrixOfOp_one_eq]; norm_num [Matrix.trace, Matrix.diag, Fin.sum_univ_two]
      rw [htr_tilt, htr_tt, smul_zero, zero_add]
      rw [smul_eq_mul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
      norm_num
    have htilt_ne : tiltOp2 ≠ 0 := by
      intro h0
      have hm := congrArg (fun M : GibbsOperator 2 => matrixOfOp M 0 0) h0
      rw [matrixOfOp_tiltOp2, matrixOfOp_zero] at hm
      norm_num [InfoGeometry.Physics.KleinBottleSewingExact.tilt2] at hm
    have hpos_tt : 0 < D_good.bkmRealBilinForm hpow_good tiltOp2 tiltOp2 :=
      (D_good.bkmRealBilinForm_self_pos_iff hpow_good tiltOp2).mpr htilt_ne
    have hpos_tanh : 0 < Real.tanh (1 / 2 : ℝ) := tanh_pos_of_pos (by norm_num)
    rw [hexp_tilt]
    linarith
  exact ⟨hQodd, hQeven, hQodd, hne, hrho_ne, hrev_even, hrev_ne⟩

/-- `T2-F4-04`: Empty family `m = 0` and zero weights `c = ![0, 0]` vanish identically. -/
theorem t2_f4_04_emptyFamilyAndZeroWeights :
    let P0 := finiteGibbsCEFamilyNOperatorParitySystem (m := 0) H_d63 hH_d63_sa hZ_d63_pos
      Fin.elim0 (fun i => Fin.elim0 i) Fin.elim0 B_tilt hB_tilt_sa
    let a : Fin 2 → GibbsOperator 2 := ![A_swap, B_tilt]
    let ha : ∀ i, IsSelfAdjoint (a i) := fun i => by fin_cases i <;> [exact hA_swap_sa; exact hB_tilt_sa]
    let Pz := finiteGibbsCEFamilyNOperatorParitySystem (m := 2) H_d63 hH_d63_sa hZ_d63_pos
      a ha ![0, 0] B_tilt hB_tilt_sa
    (∀ x y : FamilyCarrier 0 2, P0.dissipative x y = 0 ∧ P0.reversible x y = 0) ∧
      (∀ x y : FamilyCarrier 2 2, Pz.dissipative x y = 0 ∧ Pz.reversible x y = 0) := by
  intro P0 a ha Pz
  constructor
  · intro x y
    have hx : finiteGibbsCEFamilyNOperatorReadoutLinear Fin.elim0 Fin.elim0 x = 0 := by
      simp [finiteGibbsCEFamilyNOperatorReadoutLinear]
    constructor
    · dsimp only [P0, finiteGibbsCEFamilyNOperatorParitySystem, finiteGibbsCEFamilyNOperatorSystem]
      rw [finiteCEFamilyNOperatorDissipativeForm_apply, hx,
        ← centeredBKMRealCovarianceBilin_apply, _root_.map_zero, LinearMap.zero_apply]
    · dsimp only [P0, finiteGibbsCEFamilyNOperatorParitySystem, finiteGibbsCEFamilyNOperatorSystem]
      rw [finiteCEFamilyNOperatorCurvatureProbeForm_apply]
      exact Finset.sum_empty
  · intro x y
    have hx : finiteGibbsCEFamilyNOperatorReadoutLinear a ![0, 0] x = 0 := by
      simp [finiteGibbsCEFamilyNOperatorReadoutLinear, Fin.sum_univ_two]
    constructor
    · dsimp only [Pz, finiteGibbsCEFamilyNOperatorParitySystem, finiteGibbsCEFamilyNOperatorSystem]
      rw [finiteCEFamilyNOperatorDissipativeForm_apply, hx,
        ← centeredBKMRealCovarianceBilin_apply, _root_.map_zero, LinearMap.zero_apply]
    · dsimp only [Pz, finiteGibbsCEFamilyNOperatorParitySystem, finiteGibbsCEFamilyNOperatorSystem]
      rw [finiteCEFamilyNOperatorCurvatureProbeForm_apply, Fin.sum_univ_two]
      simp

/-- `T2-F4-05`: Identity observable `1` cancels in centered BKM variance & CE exterior derivative while `[A_swap, B_tilt] ≠ 0`. -/
theorem t2_f4_05_identityVsNoncommFamily :
    let D := faithfulGibbsDensity H_d63 hH_d63_sa hZ_d63_pos
    let hpow := continuous_faithfulGibbsDensity_rpow H_d63 hH_d63_sa hZ_d63_pos
    let K := realDerivationsLane (GibbsOperator 2)
    centeredBKMRealCovariance D hpow 1 1 = 0 ∧
      exteriorDerivativeZero K (1 : GibbsOperator 2) = 0 ∧
      A_swap * B_tilt ≠ B_tilt * A_swap ∧
      0 < centeredBKMRealCovariance D hpow A_swap A_swap := by
  intro D hpow K
  have h1_cov : centeredBKMRealCovariance D hpow 1 1 = 0 := by
    rw [centeredBKMRealCovariance_self]
    have hc : centeredStatistic D (1 : GibbsOperator 2) = 0 :=
      (centeredStatistic_eq_zero_iff D hpow 1).mpr
        (Submodule.mem_span_singleton.mpr ⟨1, one_smul ℝ 1⟩)
    rw [hc, _root_.map_zero]
  have h1_ext : exteriorDerivativeZero K (1 : GibbsOperator 2) = 0 := by
    apply LinearMap.ext
    intro d
    change d.1 (1 : GibbsOperator 2) = 0
    have hmul := d.property (1 : GibbsOperator 2) 1
    simp only [mul_one, one_mul] at hmul
    exact add_left_cancel (by simpa only [add_zero] using hmul.symm)
  have hpos : 0 < centeredBKMRealCovariance D hpow A_swap A_swap := by
    rw [centeredBKMRealCovariance_self, D.bkmRealBilinForm_apply]
    apply D.kuboMoriPairing_self_re_pos _ hpow
    intro h0
    have hmem := (centeredStatistic_eq_zero_iff D hpow A_swap).mp h0
    obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp hmem
    have hm := congrArg (fun Z : GibbsOperator 2 => matrixOfOp Z 0 1) hr
    rw [matrixOfOp_real_smul, matrixOfOp_one_eq, A_swap, matrixOfOp_matrixOp] at hm
    norm_num [swapMatrix] at hm
  exact ⟨h1_cov, h1_ext, hAB_noncomm, hpos⟩

/-- `T2-F5-01`: Exterior derivative nilpotency `d² = 0` on `logPartitionOneForm`, `ceExteriorDerivative`, and `frechetExtDerivK`. -/
theorem t2_f5_01_exteriorDerivNilpotency :
    let K := realDerivationsLane (GibbsOperator 2)
    let ω0 : DerivationOperatorForm K 0 := zeroFormAlternatingEquiv K A_swap
    frechetExtDeriv (logPartitionOneForm 2) H_d63 ![A_swap, B_tilt] = 0 ∧
      ceExteriorDerivative K 1 (ceExteriorDerivative K 0 ω0) = 0 ∧
      frechetExtDerivReal (frechetExtDerivReal (smoothLeftMulOneForm 2)) H_d63 = 0 := by
  intro K ω0
  have h1 := contDiff_smoothLeftMulOneForm 2
  have hSlit := tracedExponential_mem_slitPlane_of_isSelfAdjoint H_d63 hH_d63_sa
  have hlog : frechetExtDeriv (logPartitionOneForm 2) H_d63 ![A_swap, B_tilt] = 0 := by
    rw [frechetExtDeriv_logPartitionOneForm_eq_zero H_d63 hSlit]
    rfl
  have hce : ceExteriorDerivative K 1 (ceExteriorDerivative K 0 ω0) = 0 :=
    ceExteriorDerivative_succ_comp K 0 ω0
  have hfr : frechetExtDerivReal (frechetExtDerivReal (smoothLeftMulOneForm 2)) H_d63 = 0 := by
    have hspec : frechetExtDerivReal (frechetExtDerivReal (smoothLeftMulOneForm 2)) = 0 :=
      frechetExtDerivK_frechetExtDeriv h1 (by simp)
    rw [hspec]
    rfl
  exact ⟨hlog, hce, hfr⟩

/-- `T2-F5-02`: Scalar field boundary (`𝕜 = ℂ` vs `𝕜 = ℝ`) and `(secondFDerivLogPartitionReadout H_d63 A_swap B_tilt).im = 0`. -/
theorem t2_f5_02_complexVsRealScalarAndZeroIm :
    let ω_re : RealOperatorFrechetForm (GibbsOperator 2) (GibbsOperator 2) ℝ 1 :=
      complexFrechetFormRe (logPartitionOneForm 2)
    ω_re H_d63 ![A_swap] = (logPartitionOneForm 2 H_d63 ![A_swap]).re ∧
      (secondFDerivLogPartitionReadout H_d63 A_swap B_tilt).im = 0 := by
  intro ω_re
  refine ⟨rfl, ?_⟩
  have hZc : tracedExponential H_d63 ≠ 0 :=
    Complex.slitPlane_ne_zero (tracedExponential_mem_slitPlane_of_isSelfAdjoint H_d63 hH_d63_sa)
  rw [secondFDerivLogPartitionReadout_eq_complexResponse H_d63 A_swap B_tilt hZc]
  unfold complexGibbsHessianResponse
  rw [tracedExponential_eq_gibbsPartitionReal H_d63 hH_d63_sa]
  have hAim := operatorExpectation_im_eq_zero_of_isSelfAdjoint H_d63 hH_d63_sa hZ_d63_pos
    A_swap hA_swap_sa
  have hBim := operatorExpectation_im_eq_zero_of_isSelfAdjoint H_d63 hH_d63_sa hZ_d63_pos
    B_tilt hB_tilt_sa
  have hstar_duhamel :
      star (duhamelDerivative H_d63 A_swap) = duhamelDerivative H_d63 A_swap := by
    rw [duhamelDerivative_apply_integral H_d63 A_swap, star_intervalIntegral]
    · have hfn : (fun s : ℝ => star (NormedSpace.exp ((1 - s) • H_d63) * A_swap *
          NormedSpace.exp (s • H_d63))) =
          fun s : ℝ => NormedSpace.exp ((1 - (1 - s)) • H_d63) * A_swap *
            NormedSpace.exp ((1 - s) • H_d63) := by
        funext s
        rw [StarMul.star_mul, StarMul.star_mul, hA_swap_sa.star_eq]
        have hexp1 : star (NormedSpace.exp (s • H_d63)) = NormedSpace.exp (s • H_d63) :=
          (isSelfAdjoint_real_smul s H_d63 hH_d63_sa).exp.star_eq
        have hexp2 : star (NormedSpace.exp ((1 - s) • H_d63)) =
            NormedSpace.exp ((1 - s) • H_d63) :=
          (isSelfAdjoint_real_smul (1 - s) H_d63 hH_d63_sa).exp.star_eq
        rw [hexp1, hexp2, sub_sub_cancel, mul_assoc]
      rw [hfn, intervalIntegral.integral_comp_sub_left
        (fun u : ℝ => NormedSpace.exp ((1 - u) • H_d63) * A_swap * NormedSpace.exp (u • H_d63)) 1]
      simp
    · exact Continuous.intervalIntegrable (by
        simp_rw [real_smul_eq_complex_smul]
        exact ((NormedSpace.exp_continuous.comp
          ((Complex.continuous_ofReal.comp (continuous_const.sub continuous_id)).smul
            continuous_const)).mul continuous_const).mul
          (NormedSpace.exp_continuous.comp
            ((Complex.continuous_ofReal.comp continuous_id).smul continuous_const))) 0 1
  have htr_im : (finiteOperatorTrace (exponentialDerivative (𝕜 := ℂ) H_d63 A_swap * B_tilt)).im = 0 := by
    rw [InfoGeometry.Canonical.NoncommutativeGibbsSecondDerivativeCenteredBridge.exponentialDerivative_complex_apply_eq_real H_d63 A_swap,
      InfoGeometry.Canonical.NoncommutativeGibbsSecondDerivativeCenteredBridge.gibbs_exponentialDerivative_eq_duhamelDerivative H_d63]
    have hstar :
        star (finiteOperatorTrace (duhamelDerivative H_d63 A_swap * B_tilt)) =
          finiteOperatorTrace (duhamelDerivative H_d63 A_swap * B_tilt) := by
      calc
        star (finiteOperatorTrace (duhamelDerivative H_d63 A_swap * B_tilt)) =
            finiteOperatorTrace (star (duhamelDerivative H_d63 A_swap * B_tilt)) :=
          (finiteOperatorTrace_star _).symm
        _ = finiteOperatorTrace (star B_tilt * star (duhamelDerivative H_d63 A_swap)) := by
          rw [star_mul]
        _ = finiteOperatorTrace (B_tilt * duhamelDerivative H_d63 A_swap) := by
          rw [hB_tilt_sa.star_eq, hstar_duhamel]
        _ = finiteOperatorTrace (duhamelDerivative H_d63 A_swap * B_tilt) :=
          finiteOperatorTrace_mul_comm _ _
    have him := congrArg Complex.im hstar
    simp only [Complex.star_def, Complex.conj_im] at him
    linarith
  simp [Complex.sub_im, Complex.mul_im, Complex.inv_im, hAim, hBim, htr_im]

/-- `T2-F5-03`: `ceCurvature` vanishes on repeated tangent `![d1, d1]` and is nonzero on noncommuting `![d1, d2]`. -/
theorem t2_f5_03_ceCurvatureAlternatingVsNoncomm :
    let K := realDerivationsLane (GibbsOperator 2)
    let Γ := exteriorDerivativeZero K A_swap
    let Γ_alt := oneFormAlternatingLinearEquiv K Γ
    let d1 := innerDerivation tiltOp2
    let d2 := innerDerivation (Complex.I • (tiltOp2 * switchOp2))
    ceCurvature K Γ_alt ![d1, d1] = 0 ∧
      ceCurvature K Γ_alt ![d1, d2] ≠ 0 := by
  intro K Γ Γ_alt d1 d2
  refine ⟨(ceCurvature K Γ_alt).map_eq_zero_of_eq ![d1, d1] (i := 0) (j := 1)
    rfl (by decide), ?_⟩
  rw [ceCurvature_eq, twoCochainEquivDerivationOperatorForm_apply,
    connectionCurvature, exteriorDerivativeOne_exteriorDerivativeZero, zero_add]
  intro h0
  have hm := congrArg (fun Z : GibbsOperator 2 => matrixOfOp Z 0 1) h0
  change matrixOfOp ((tiltOp2 * A_swap - A_swap * tiltOp2) *
      ((Complex.I • (tiltOp2 * switchOp2)) * A_swap -
        A_swap * (Complex.I • (tiltOp2 * switchOp2))) -
    ((Complex.I • (tiltOp2 * switchOp2)) * A_swap -
        A_swap * (Complex.I • (tiltOp2 * switchOp2))) *
      (tiltOp2 * A_swap - A_swap * tiltOp2)) 0 1 = 0 at hm
  rw [matrixOfOp_sub_eq, matrixOfOp_mul_eq, matrixOfOp_mul_eq,
    matrixOfOp_sub_eq, matrixOfOp_mul_eq, matrixOfOp_mul_eq,
    matrixOfOp_sub_eq, matrixOfOp_mul_eq, matrixOfOp_mul_eq,
    matrixOfOp_complex_smul, matrixOfOp_mul_eq, tiltOp2, A_swap, switchOp2,
    matrixOfOp_matrixOp, matrixOfOp_matrixOp] at hm
  simp only [InfoGeometry.Physics.KleinBottleSewingExact.tilt2, swapMatrix,
    Matrix.sub_apply, Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_two] at hm
  have him := congrArg Complex.im hm
  norm_num [InfoGeometry.Physics.KleinBottleSewingExact.switch2] at him

/-- `T2-F5-04`: Closed `1`-form `exteriorDerivativeZero K A_swap` has `ceCurvature = ceWedge`, and constant `RealOperatorFrechetForm` has `frechetExtDerivReal = 0`. -/
theorem t2_f5_04_closedAndConstantForms :
    let K := realDerivationsLane (GibbsOperator 2)
    let Γ_exact := exteriorDerivativeZero K A_swap
    let Γ_alt := oneFormAlternatingLinearEquiv K Γ_exact
    let ω_const : RealOperatorFrechetForm (GibbsOperator 2) (GibbsOperator 2) (GibbsOperator 2) 1 :=
      fun _ => ContinuousAlternatingMap.ofSubsingleton ℝ (GibbsOperator 2) (GibbsOperator 2)
        (0 : Fin 1) (leftMulRealCLM A_swap)
    exteriorDerivativeOne K Γ_exact = 0 ∧
      ceCurvature K Γ_alt = ceWedge K Γ_alt Γ_alt ∧
      frechetExtDerivReal ω_const H_d63 = 0 := by
  intro K Γ_exact Γ_alt ω_const
  have h1 : exteriorDerivativeOne K Γ_exact = 0 :=
    exteriorDerivativeOne_exteriorDerivativeZero K A_swap
  have h2 : ceCurvature K Γ_alt = ceWedge K Γ_alt Γ_alt := by
    rw [ceCurvature_eq, connectionCurvature, h1, zero_add,
      ceWedge_one_one_eq_connectionWedgeSquare]
  have h3 : frechetExtDerivReal ω_const H_d63 = 0 := by
    unfold frechetExtDerivReal
    ext v
    rw [frechetExtDerivK_apply (differentiable_const _ H_d63)]
    simp_rw [fderiv_const_apply]
    simp
  exact ⟨h1, h2, h3⟩

/-- `T2-F5-05`: Degree `0` pairing reduction and dimension `0` form collapse. -/
theorem t2_f5_05_degree0AndDim0Boundary
    (ω0 η0 : DerivationOperatorForm (realDerivationsLane (GibbsOperator 2)) 0)
    (ω_dim0 : DerivationOperatorForm (realDerivationsLane (GibbsOperator 0)) 2) :
    let D := faithfulGibbsDensity H_d63 hH_d63_sa hZ_d63_pos
    let hpow := continuous_faithfulGibbsDensity_rpow H_d63 hH_d63_sa hZ_d63_pos
    let P0 := centeredBKMOnsagerFormPairing_ofValueParity D hpow B_tilt hB_tilt_sa Fin.elim0
    P0.dissipative ω0 η0 = (centeredBKMOnsagerSystem D hpow B_tilt).dissipative
        (ω0 Fin.elim0) (η0 Fin.elim0) ∧
      ω_dim0 = 0 := by
  intro D hpow P0
  refine ⟨?_, ?_⟩
  · dsimp only [P0]
    unfold centeredBKMOnsagerFormPairing_ofValueParity centeredBKMParityOnsagerSystem
    dsimp only [ParityOnsagerFormPairing.ofValueParity, OnsagerFormPairing.ofFrame]
    rw [LinearMap.compl₁₂_apply, evalAlternatingForm_apply, evalAlternatingForm_apply]
  · ext v x i
    exact Fin.elim0 i

end GapB_Tests

section GapC_Tests

/-- `T1-F6-01`: Layer 1 Banach & GENERIC metriplectic trajectory decay on `ℝ × ℝ` and `ℝ × ℝ × ℝ`. -/
theorem t1_f6_01_banachMetriplecticFlow :
    let Φ : ℝ × ℝ → ℝ := fun p => p.2 ^ 2
    let dΦ : ℝ × ℝ → (ℝ × ℝ →L[ℝ] ℝ) := fun p => (2 * p.2) • ContinuousLinearMap.snd ℝ ℝ ℝ
    let x : ℝ → ℝ × ℝ := fun t => (t, Real.exp (-2 * t))
    let v_rev : ℝ → ℝ × ℝ := fun _ => (1, 0)
    let v_diss : ℝ → ℝ × ℝ := fun t => (0, -2 * Real.exp (-2 * t))
    let sys_gen : GenericMetriplecticFlow.System (ℝ × ℝ × ℝ) :=
      { dH := ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)
        dS := -(ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))
        L := { toFun := fun _ => (0, 0, 0)
               map_add' := fun _ _ => by simp [Prod.mk_add_mk]
               map_smul' := fun _ _ => by simp }
        M := { toFun := fun α => (0, 0, α (0, 0, 1))
               map_add' := fun _ _ => by simp [Prod.mk_add_mk]
               map_smul' := fun _ _ => by simp [Prod.smul_mk] }
        L_skew := fun α β => by
          have h0 : ((0 : ℝ), (0 : ℝ), (0 : ℝ)) = 0 := rfl
          change α (0, 0, 0) = -β (0, 0, 0)
          rw [h0, map_zero, map_zero, neg_zero]
        L_entropy_casimir := rfl
        M_symmetric := fun α β => by
          have hmk : ∀ (γ : GenericMetriplecticFlow.Covector (ℝ × ℝ × ℝ)) (r : ℝ),
              γ (0, 0, r) = r * γ (0, 0, 1) := fun γ r => by
            simpa [smul_eq_mul, Prod.smul_mk] using γ.map_smul r (0, 0, (1 : ℝ))
          change α (0, 0, β (0, 0, 1)) = β (0, 0, α (0, 0, 1))
          rw [hmk α (β (0, 0, 1)), hmk β (α (0, 0, 1)), mul_comm]
        M_hamiltonian_casimir := rfl
        M_nonneg := fun α => by
          have hmk : ∀ (γ : GenericMetriplecticFlow.Covector (ℝ × ℝ × ℝ)) (r : ℝ),
              γ (0, 0, r) = r * γ (0, 0, 1) := fun γ r => by
            simpa [smul_eq_mul, Prod.smul_mk] using γ.map_smul r (0, 0, (1 : ℝ))
          change 0 ≤ α (0, 0, α (0, 0, 1))
          rw [hmk α]
          exact mul_self_nonneg _ }
    (HasDerivAt (fun s => Φ (x s)) (dΦ (x 0) (v_diss 0)) 0 ∧
        dΦ (x 0) (v_rev 0) = 0 ∧ dΦ (x 0) (v_diss 0) < 0) ∧
      AntitoneOn (fun s => Φ (x s)) (Set.Icc 0 1) ∧
      0 ≤ sys_gen.dS sys_gen.flow := by
  intro Φ dΦ x v_rev v_diss sys_gen
  have hΦ : ∀ t, HasFDerivAt Φ (dΦ (x t)) (x t) := fun t => by
    have hsnd : HasFDerivAt (fun p : ℝ × ℝ => p.2) (ContinuousLinearMap.snd ℝ ℝ ℝ) (x t) :=
      ContinuousLinearMap.hasFDerivAt (ContinuousLinearMap.snd ℝ ℝ ℝ)
    simpa [Φ, dΦ, pow_two, mul_assoc] using hsnd.pow 2
  have hx : ∀ t, HasDerivAt x (v_rev t + v_diss t) t := fun t => by
    have h1 : HasDerivAt (fun s : ℝ => s) 1 t := hasDerivAt_id t
    have h2 : HasDerivAt (fun s : ℝ => Real.exp (-2 * s)) (-2 * Real.exp (-2 * t)) t := by
      have hm : HasDerivAt (fun s : ℝ => -2 * s) (-2) t := by
        simpa using ((hasDerivAt_id t).const_mul (-2 : ℝ))
      simpa [mul_comm] using hm.exp
    simpa [x, v_rev, v_diss] using h1.prodMk h2
  have hrev : ∀ t, dΦ (x t) (v_rev t) = 0 := fun t => by simp [dΦ, v_rev]
  have hdiss : ∀ t, dΦ (x t) (v_diss t) ≤ 0 := fun t => by
    change (2 * (x t).2) * (0, -2 * Real.exp (-2 * t)).2 ≤ 0
    dsimp only [x]
    nlinarith [Real.exp_pos (-2 * t)]
  have hdiss0_strict : dΦ (x 0) (v_diss 0) < 0 := by
    change (2 * (x 0).2) * (0, -2 * Real.exp (-2 * 0)).2 < 0
    norm_num [x]
  have hcont : ContinuousOn (fun s => Φ (x s)) (Set.Icc 0 1) :=
    (fun t _ => (hΦ t).continuousAt.comp (hx t).continuousAt |>.continuousWithinAt)
  exact ⟨⟨(banach_metriplectic_hasDerivAt_nonpos (hΦ 0) (hx 0) (hrev 0) (hdiss 0)).1,
      hrev 0, hdiss0_strict⟩,
    banach_metriplectic_antitoneOn (convex_Icc 0 1) hcont (fun t _ => hΦ t) (fun t _ => hx t)
      (fun t _ => hrev t) (fun t _ => hdiss t),
    sys_gen.entropy_rate_nonneg⟩

private def H_sol_c (t : ℝ) : ℝ := Real.arsinh (Real.exp (-t / 4))
private def H_sol_d (t : ℝ) : ℝ := (1 / 2 : ℝ) * Real.log (1 + Real.exp (-t / 2))

private def H_sol_curve (t : ℝ) : FiniteOperatorAlgebra 2 :=
  H_sol_c t • tiltOp2 + H_sol_d t • (1 : FiniteOperatorAlgebra 2)

private lemma H_sol_curve_isSelfAdjoint (t : ℝ) : IsSelfAdjoint (H_sol_curve t) :=
  isSelfAdjoint_add_op
    (isSelfAdjoint_real_smul (H_sol_c t) tiltOp2 tiltOp2_isSelfAdjoint)
    (isSelfAdjoint_real_smul (H_sol_d t) 1 (by rw [isSelfAdjoint_iff, star_one]))

private lemma H_sol_curve_rho (t : ℝ) :
    (faithfulGibbsDensity (H_sol_curve t) (H_sol_curve_isSelfAdjoint t)
      (tracedExponential_re_pos_of_isSelfAdjoint (H_sol_curve t) (H_sol_curve_isSelfAdjoint t))).rho =
      (1 / 2 : ℝ) • (1 : FiniteOperatorAlgebra 2) + (Real.tanh (H_sol_c t) / 2) • tiltOp2 := by
  erw [faithfulGibbsDensity_rho_eq_normalizedExponential]
  have hcomm : Commute (H_sol_c t • tiltOp2) (H_sol_d t • (1 : FiniteOperatorAlgebra 2)) := by
    simp only [real_smul_eq_complex_smul]
    exact (Commute.one_right _).smul_left _ |>.smul_right _
  have hexp : NormedSpace.exp (H_sol_curve t) =
      Real.exp (H_sol_d t) •
        (Real.cosh (H_sol_c t) • (1 : FiniteOperatorAlgebra 2) + Real.sinh (H_sol_c t) • tiltOp2) := by
    dsimp [H_sol_curve]
    rw [NormedSpace.exp_add_of_commute hcomm, exp_real_smul_tiltOp2, exp_real_smul_one]
    simp only [real_smul_eq_complex_smul, mul_smul_comm, mul_one, smul_add, smul_smul]
  have htr1 : finiteOperatorTrace (1 : FiniteOperatorAlgebra 2) = 2 := by
    change Matrix.trace (matrixOfOp (1 : FiniteOperatorAlgebra 2)) = 2
    rw [matrixOfOp_one_eq]
    norm_num [Matrix.trace, Matrix.diag, Fin.sum_univ_two]
  have htr_tilt : finiteOperatorTrace tiltOp2 = 0 := by
    change Matrix.trace (matrixOfOp tiltOp2) = 0
    rw [matrixOfOp_tiltOp2]
    norm_num [InfoGeometry.Physics.KleinBottleSewingExact.tilt2, Matrix.trace, Matrix.diag,
      Fin.sum_univ_two]
  have htr : tracedExponential (H_sol_curve t) =
      ((2 * Real.exp (H_sol_d t) * Real.cosh (H_sol_c t) : ℝ) : ℂ) := by
    unfold tracedExponential
    rw [hexp, real_smul_eq_complex_smul, (finiteOperatorTraceCLM 2).map_smul,
      (finiteOperatorTraceCLM 2).map_add, real_smul_eq_complex_smul,
      real_smul_eq_complex_smul, (finiteOperatorTraceCLM 2).map_smul,
      (finiteOperatorTraceCLM 2).map_smul]
    change (Real.exp (H_sol_d t) : ℂ) • ((Real.cosh (H_sol_c t) : ℂ) • finiteOperatorTrace 1 +
      (Real.sinh (H_sol_c t) : ℂ) • finiteOperatorTrace tiltOp2) = _
    rw [htr1, htr_tilt, smul_eq_mul, smul_eq_mul, smul_eq_mul]
    push_cast
    ring
  have hcosh_ne : Real.cosh (H_sol_c t) ≠ 0 := ne_of_gt (Real.cosh_pos _)
  have hexp_ne : Real.exp (H_sol_d t) ≠ 0 := Real.exp_ne_zero _
  unfold normalizedExponential
  rw [htr, hexp, real_smul_eq_complex_smul, real_smul_eq_complex_smul,
    real_smul_eq_complex_smul, real_smul_eq_complex_smul, real_smul_eq_complex_smul,
    smul_add, smul_smul, smul_smul, smul_add, smul_smul, smul_smul]
  congr 1
  · congr 1
    exact_mod_cast (by field_simp [hcosh_ne, hexp_ne] :
      (2 * Real.exp (H_sol_d t) * Real.cosh (H_sol_c t))⁻¹ *
        (Real.exp (H_sol_d t) * Real.cosh (H_sol_c t)) = 1 / 2)
  · congr 1
    rw [Real.tanh_eq_sinh_div_cosh]
    exact_mod_cast (by field_simp [hcosh_ne, hexp_ne] :
      (2 * Real.exp (H_sol_d t) * Real.cosh (H_sol_c t))⁻¹ *
        (Real.exp (H_sol_d t) * Real.sinh (H_sol_c t)) =
        Real.sinh (H_sol_c t) / Real.cosh (H_sol_c t) / 2)

private lemma H_sol_curve_flow (t : ℝ) :
    HasDerivAt H_sol_curve
      (gibbsMetriplecticFlow 0 ((1 / 2 : ℝ) • (1 : FiniteOperatorAlgebra 2))
        (H_sol_curve t) (H_sol_curve_isSelfAdjoint t)) t := by
  let D := faithfulGibbsDensity (H_sol_curve t) (H_sol_curve_isSelfAdjoint t)
    (tracedExponential_re_pos_of_isSelfAdjoint (H_sol_curve t) (H_sol_curve_isSelfAdjoint t))
  let hpow := continuous_faithfulGibbsDensity_rpow (H_sol_curve t) (H_sol_curve_isSelfAdjoint t)
    (tracedExponential_re_pos_of_isSelfAdjoint (H_sol_curve t) (H_sol_curve_isSelfAdjoint t))
  let τ := adGammaStarAlgEquiv tiltOp2 tiltOp2_isSelfAdjoint tiltOp2_sq
  have hτ_rho : τ D.rho = D.rho := by
    rw [show D.rho = (1 / 2 : ℝ) • (1 : FiniteOperatorAlgebra 2) +
        (Real.tanh (H_sol_c t) / 2) • tiltOp2 from H_sol_curve_rho t]
    rw [_root_.map_add, _root_.map_smul, _root_.map_smul, _root_.map_one]
    have hτ_tilt : τ tiltOp2 = tiltOp2 := by
      apply matrixOfOp_injective
      change matrixOfOp (tiltOp2 * tiltOp2 * tiltOp2) = matrixOfOp tiltOp2
      rw [tiltOp2_sq, one_mul]
    rw [hτ_tilt]
  have hcomm_rpow : ∀ s : ℝ, D.rpow s * tiltOp2 = tiltOp2 * D.rpow s := fun s => by
    have hfix := aut_rpow τ D hτ_rho s
    change tiltOp2 * D.rpow s * tiltOp2 = D.rpow s at hfix
    calc D.rpow s * tiltOp2 = (tiltOp2 * D.rpow s * tiltOp2) * tiltOp2 := by rw [hfix]
      _ = tiltOp2 * D.rpow s * (tiltOp2 * tiltOp2) := by rw [mul_assoc, mul_assoc]
      _ = tiltOp2 * D.rpow s := by rw [tiltOp2_sq, mul_one]
  have hkm_tilt : D.kuboMoriTransform tiltOp2 = D.rho * tiltOp2 := by
    unfold FaithfulDensityOperator.kuboMoriTransform
    have heq : (fun s : ℝ => D.modularInterpolation s tiltOp2) = fun _ => D.rho * tiltOp2 := by
      funext s
      unfold FaithfulDensityOperator.modularInterpolation
      rw [hcomm_rpow s, mul_assoc, ← D.rpow_add, add_sub_cancel, ← hcomm_rpow 1,
        D.rpow_one]
    rw [heq, intervalIntegral.integral_const, sub_zero, one_smul]
  have hflow_eq : gibbsMetriplecticFlow 0 ((1 / 2 : ℝ) • (1 : FiniteOperatorAlgebra 2))
      (H_sol_curve t) (H_sol_curve_isSelfAdjoint t) =
      (-(Real.tanh (H_sol_c t) / 4)) • tiltOp2 +
        (-(Real.tanh (H_sol_c t) ^ 2 / 4)) • (1 : FiniteOperatorAlgebra 2) := by
    dsimp only [gibbsMetriplecticFlow, gibbsUnitaryVectorField, gibbsBKMDissipativeField]
    rw [zero_mul, mul_zero, sub_self, smul_zero, zero_add]
    have hdiff : D.rho - (1 / 2 : ℝ) • (1 : FiniteOperatorAlgebra 2) =
        (Real.tanh (H_sol_c t) / 2) • tiltOp2 := by
      rw [H_sol_curve_rho t]
      abel
    change -(D.kuboMoriTransform (D.rho - (1 / 2 : ℝ) • (1 : FiniteOperatorAlgebra 2))) = _
    rw [hdiff, ← D.kuboMoriTransformCLM_apply hpow, real_smul_eq_complex_smul,
      (D.kuboMoriTransformCLM hpow).map_smul, ← real_smul_eq_complex_smul,
      D.kuboMoriTransformCLM_apply hpow, hkm_tilt, H_sol_curve_rho t, add_mul]
    simp only [real_smul_eq_complex_smul, smul_mul_assoc, one_mul, tiltOp2_sq, smul_add, neg_add,
      smul_smul]
    congr 1
    · apply ContinuousLinearMap.ext; intro v; simp; ring
    · apply ContinuousLinearMap.ext; intro v; simp; ring
  have hc_deriv : HasDerivAt H_sol_c (-(Real.tanh (H_sol_c t) / 4)) t := by
    have hexp_d : HasDerivAt (fun s : ℝ => Real.exp (-s / 4))
        (-(1 / 4 : ℝ) * Real.exp (-t / 4)) t := by
      have hl : HasDerivAt (fun s : ℝ => -s / 4) (-(1 / 4 : ℝ)) t := by
        simpa [neg_div, one_div] using ((hasDerivAt_id t).neg.div_const (4 : ℝ))
      simpa [mul_comm] using hl.exp
    have hcomp := (Real.hasDerivAt_arsinh (Real.exp (-t / 4))).comp t hexp_d
    refine hcomp.congr_deriv ?_
    have hsinh : Real.sinh (H_sol_c t) = Real.exp (-t / 4) := Real.sinh_arsinh _
    have hcosh : Real.cosh (H_sol_c t) = √(1 + Real.exp (-t / 4) ^ 2) := Real.cosh_arsinh _
    rw [Real.tanh_eq_sinh_div_cosh, hsinh, hcosh]
    ring
  have hd_deriv : HasDerivAt H_sol_d (-(Real.tanh (H_sol_c t) ^ 2 / 4)) t := by
    have hpos : 1 + Real.exp (-t / 2) ≠ 0 := ne_of_gt (by linarith [Real.exp_pos (-t / 2)])
    have hexp_d : HasDerivAt (fun s : ℝ => 1 + Real.exp (-s / 2))
        (-(1 / 2 : ℝ) * Real.exp (-t / 2)) t := by
      have hl : HasDerivAt (fun s : ℝ => -s / 2) (-(1 / 2 : ℝ)) t := by
        simpa [neg_div, one_div] using ((hasDerivAt_id t).neg.div_const (2 : ℝ))
      simpa [mul_comm] using (hl.exp).const_add 1
    have hlog := ((Real.hasDerivAt_log hpos).comp t hexp_d).const_mul (1 / 2 : ℝ)
    refine hlog.congr_deriv ?_
    have hsinh : Real.sinh (H_sol_c t) = Real.exp (-t / 4) := Real.sinh_arsinh _
    have hcosh : Real.cosh (H_sol_c t) = √(1 + Real.exp (-t / 4) ^ 2) := Real.cosh_arsinh _
    have hsq_pos : 0 ≤ 1 + Real.exp (-t / 4) ^ 2 := by positivity
    have hexp_sq : Real.exp (-t / 4) ^ 2 = Real.exp (-t / 2) := by
      rw [← Real.exp_nat_mul]
      congr 1; ring
    rw [Real.tanh_eq_sinh_div_cosh, div_pow, hsinh, hcosh, Real.sq_sqrt hsq_pos, hexp_sq]
    ring
  rw [hflow_eq]
  exact (hc_deriv.smul_const tiltOp2).add (hd_deriv.smul_const (1 : FiniteOperatorAlgebra 2))

/-- `T1-F6-02`: Layer 2 `gibbsRelativePotential` `HasDerivAt`, strict negativity (`< 0`), and `AntitoneOn` on a strictly decreasing non-constant trajectory. -/
theorem t1_f6_02_gibbsRelativePotentialMetriplectic :
    let σ_mix : FiniteOperatorAlgebra 2 := (1 / 2 : ℝ) • (1 : FiniteOperatorAlgebra 2)
    let v0 := gibbsMetriplecticFlow tiltOp2 σ_mix tiltOp2 tiltOp2_isSelfAdjoint
    let H_curve : ℝ → FiniteOperatorAlgebra 2 := fun s => tiltOp2 + s • v0
    deriv (fun s => gibbsRelativePotential σ_mix (H_curve s)) 0 < 0 ∧
      AntitoneOn (fun s => gibbsRelativePotential σ_mix (H_sol_curve s)) (Set.Icc 0 1) ∧
      gibbsRelativePotential σ_mix (H_sol_curve 1) < gibbsRelativePotential σ_mix (H_sol_curve 0) := by
  intro σ_mix v0 H_curve
  have hneg := capstone_qubit_nondegenerate_witness.2.2.2.2.2.2
  have hσ_sa : IsSelfAdjoint σ_mix :=
    isSelfAdjoint_real_smul (1 / 2 : ℝ) 1 (by rw [isSelfAdjoint_iff, star_one])
  have hcomm : Commute σ_mix (0 : FiniteOperatorAlgebra 2) := Commute.zero_right _
  have hanti : AntitoneOn (fun s => gibbsRelativePotential σ_mix (H_sol_curve s)) (Set.Icc 0 1) :=
    antitoneOn_gibbsRelativePotential_metriplectic 0 σ_mix hσ_sa hcomm H_sol_curve
      (convex_Icc 0 1) (fun t _ => H_sol_curve_isSelfAdjoint t) (fun t _ => H_sol_curve_flow t)
  have hstrict_anti : StrictAntiOn (fun s => gibbsRelativePotential σ_mix (H_sol_curve s)) (Set.Icc 0 1) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc 0 1)
    · intro t _
      exact (hasDerivAt_gibbsRelativePotential_metriplectic 0 σ_mix hσ_sa hcomm H_sol_curve
        (H_sol_curve_isSelfAdjoint t) (H_sol_curve_flow t)).continuousAt.continuousWithinAt
    · intro t _
      apply deriv_gibbsRelativePotential_metriplectic_neg_of_ne 0 σ_mix hσ_sa hcomm
        H_sol_curve (H_sol_curve_isSelfAdjoint t) (H_sol_curve_flow t)
      rw [H_sol_curve_rho t]
      intro h0
      have hm := congrArg (fun M : FiniteOperatorAlgebra 2 => matrixOfOp M 0 0) h0
      rw [matrixOfOp_add, matrixOfOp_real_smul, matrixOfOp_real_smul, matrixOfOp_one_eq,
        matrixOfOp_tiltOp2] at hm
      simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, ↓reduceIte,
        smul_eq_mul, mul_one, InfoGeometry.Physics.KleinBottleSewingExact.tilt2] at hm
      have hre := congrArg Complex.re hm
      simp only [Complex.add_re, Complex.ofReal_re] at hre
      have htanh_pos : 0 < Real.tanh (H_sol_c t) := by
        rw [Real.tanh_eq_sinh_div_cosh]
        dsimp only [H_sol_c]
        rw [Real.sinh_arsinh]
        exact div_pos (Real.exp_pos _) (Real.cosh_pos _)
      linarith
  exact ⟨hneg, hanti, hstrict_anti (by norm_num) (by norm_num) (by norm_num)⟩

/-- `T1-F6-03`: `kuboMoriTransform_commutator_eq_commutator_rho` on noncommuting `H_d63, A_swap`. -/
theorem t1_f6_03_kuboMoriTransformCommutator :
    let D := faithfulGibbsDensity H_d63 hH_d63_sa hZ_d63_pos
    D.kuboMoriTransform (H_d63 * A_swap - A_swap * H_d63) = D.rho * A_swap - A_swap * D.rho ∧
      D.rho * A_swap ≠ A_swap * D.rho := by
  intro D
  have heq := kuboMoriTransform_commutator_eq_commutator_rho H_d63 A_swap hH_d63_sa hZ_d63_pos
  have hne : D.rho * A_swap ≠ A_swap * D.rho := by
    intro hcomm
    have h0 : D.kuboMoriTransform (H_d63 * A_swap - A_swap * H_d63) = 0 := by
      rw [heq, hcomm, sub_self]
    have hpow := continuous_faithfulGibbsDensity_rpow H_d63 hH_d63_sa hZ_d63_pos
    have hinj := D.kuboMoriTransformCLM_injective hpow
    have hc0 : H_d63 * A_swap - A_swap * H_d63 = 0 := by
      apply hinj
      simpa [FaithfulDensityOperator.kuboMoriTransformCLM_apply] using
        h0.trans (D.kuboMoriTransformCLM hpow).map_zero.symm
    exact hHA_noncomm (sub_eq_zero.mp hc0)
  exact ⟨heq, hne⟩

private lemma hasDerivAt_add_real_smul (B V : FiniteOperatorAlgebra 2) (t : ℝ) :
    HasDerivAt (fun s : ℝ => B + s • V) V t := by
  rw [hasDerivAt_iff_tendsto_slope_zero]
  have h : (fun s : ℝ => s⁻¹ • ((B + (t + s) • V) - (B + t • V))) =ᶠ[nhdsWithin 0 {0}ᶜ]
      fun _ => V := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hs0 : s ≠ 0 := hs
    rw [real_smul_eq_complex_smul, add_sub_add_left_eq_sub, real_smul_eq_complex_smul,
      real_smul_eq_complex_smul, Complex.ofReal_inv]
    have hsub : ((t + s : ℝ) : ℂ) • V - (t : ℂ) • V = (s : ℂ) • V := by
      rw [Complex.ofReal_add, add_smul (t : ℂ) (s : ℂ) V, add_sub_cancel_left]
    rw [hsub, smul_smul, inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr hs0), one_smul]
  exact tendsto_const_nhds.congr' h.symm

/-- `T1-F6-04`: `hasDerivAt_normalizedExponential` along `H(t) := B_tilt + t • A_swap` (`[H(t), H'(t)] ≠ 0`). -/
theorem t1_f6_04_hasDerivAtNormalizedExponential :
    let H : ℝ → FiniteOperatorAlgebra 2 := fun t => B_tilt + t • A_swap
    ∀ t : ℝ,
      tracedExponential (H t) ∈ Complex.slitPlane ∧
      HasDerivAt (fun s => normalizedExponential (H s))
        ((faithfulGibbsDensity (H t) (isSelfAdjoint_add_op hB_tilt_sa (isSelfAdjoint_real_smul t A_swap hA_swap_sa))
            (tracedExponential_re_pos_of_isSelfAdjoint (H t)
              (isSelfAdjoint_add_op hB_tilt_sa (isSelfAdjoint_real_smul t A_swap hA_swap_sa)))).kuboMoriTransform
          (A_swap - finiteOperatorTrace
            ((faithfulGibbsDensity (H t) (isSelfAdjoint_add_op hB_tilt_sa (isSelfAdjoint_real_smul t A_swap hA_swap_sa))
              (tracedExponential_re_pos_of_isSelfAdjoint (H t)
                (isSelfAdjoint_add_op hB_tilt_sa (isSelfAdjoint_real_smul t A_swap hA_swap_sa)))).rho * A_swap) •
              (1 : FiniteOperatorAlgebra 2))) t := by
  intro H t
  have hHt : IsSelfAdjoint (H t) := isSelfAdjoint_add_op hB_tilt_sa (isSelfAdjoint_real_smul t A_swap hA_swap_sa)
  have hderiv : HasDerivAt H A_swap t := hasDerivAt_add_real_smul B_tilt A_swap t
  exact ⟨tracedExponential_mem_slitPlane_of_isSelfAdjoint (H t) hHt,
    hasDerivAt_normalizedExponential H hHt hderiv⟩

section GapC_Layer3

open scoped Matrix.Norms.L2Operator

private def Φ_norm_swap (M : Matrix (Fin 2) (Fin 2) ℂ) : ℝ :=
  -(Matrix.trace (swapMatrix * M) / Matrix.trace M).re

private def matrix_trace_clm :
    Matrix (Fin 2) (Fin 2) ℂ →L[ℂ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := Matrix.trace
      map_add' := Matrix.trace_add
      map_smul' := fun c M => by simp }

private def trace_swap_mul_clm :
    Matrix (Fin 2) (Fin 2) ℂ →L[ℂ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M => Matrix.trace (swapMatrix * M)
      map_add' := fun M N => by rw [Matrix.mul_add, Matrix.trace_add]
      map_smul' := fun c M => by simp }

private lemma Φ_norm_swap_continuousOn_of_ne
    (rho : ℝ → Matrix (Fin 2) (Fin 2) ℂ) (I : Set ℝ)
    (hcont_rho : ContinuousOn rho I)
    (htr_ne : ∀ t ∈ I, Matrix.trace (rho t) ≠ 0) :
    ContinuousOn (fun t => Φ_norm_swap (rho t)) I := by
  intro t ht
  have h1 : ContinuousWithinAt (fun s => Matrix.trace (swapMatrix * rho s)) I t := by
    change ContinuousWithinAt (⇑trace_swap_mul_clm ∘ rho) I t
    exact trace_swap_mul_clm.continuous.continuousAt.comp_continuousWithinAt (hcont_rho t ht)
  have h2 : ContinuousWithinAt (fun s => Matrix.trace (rho s)) I t := by
    change ContinuousWithinAt (⇑matrix_trace_clm ∘ rho) I t
    exact matrix_trace_clm.continuous.continuousAt.comp_continuousWithinAt (hcont_rho t ht)
  exact (Complex.continuous_re.continuousAt.comp_continuousWithinAt
    (h1.div h2 (htr_ne t ht))).neg

private lemma Φ_norm_swap_hasFDerivAt
    (H0 : FiniteOperatorAlgebra 2) (hH0 : IsSelfAdjoint H0)
    (hZ0 : 0 < gibbsPartitionReal H0) :
    let D0 := faithfulGibbsDensity H0 hH0 hZ0
    let rho0 := matrixOfOp D0.rho
    let gradF : Matrix (Fin 2) (Fin 2) ℂ := -matrixOfOp (centeredStatistic D0 A_swap)
    let L_dΦ0 : Matrix (Fin 2) (Fin 2) ℂ →ₗ[ℝ] ℝ :=
      { toFun := fun V => (Matrix.trace (star gradF * V)).re
        map_add' := fun V W => by
          rw [Matrix.mul_add, Matrix.trace_add, Complex.add_re]
        map_smul' := fun r V => by
          simp only [RingHom.id_apply]
          rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, Complex.real_smul, Complex.mul_re,
            Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] }
    let dΦ0 : Matrix (Fin 2) (Fin 2) ℂ →L[ℝ] ℝ :=
      { toLinearMap := L_dΦ0
        cont := LinearMap.continuous_of_finiteDimensional L_dΦ0 }
    HasFDerivAt Φ_norm_swap dΦ0 rho0 := by
  intro D0 rho0 gradF L_dΦ0 dΦ0
  have htr1 : Matrix.trace rho0 = 1 := by
    change finiteOperatorTrace D0.rho = 1
    exact D0.trace_one
  have htr_ne : Matrix.trace rho0 ≠ 0 := by rw [htr1]; exact one_ne_zero
  have hf : HasFDerivAt (fun M => Matrix.trace (swapMatrix * M)) trace_swap_mul_clm rho0 :=
    trace_swap_mul_clm.hasFDerivAt
  have hg : HasFDerivAt Matrix.trace matrix_trace_clm rho0 :=
    matrix_trace_clm.hasFDerivAt
  have hdiv := HasFDerivAt.congr_of_eventuallyEq
    (f := fun M => Matrix.trace (swapMatrix * M) / Matrix.trace M)
    (hf.mul ((hasFDerivAt_inv htr_ne).comp rho0 hg))
    (Filter.Eventually.of_forall fun M => (div_eq_mul_inv _ _).symm)
  have hre := (Complex.reCLM.hasFDerivAt.comp rho0 (hdiv.restrictScalars ℝ)).neg
  have hexp_im : (Matrix.trace (swapMatrix * rho0)).im = 0 := by
    have hmul : Matrix.trace (swapMatrix * rho0) = finiteOperatorTrace (D0.rho * A_swap) := by
      have hA : (swapMatrix : Matrix (Fin 2) (Fin 2) ℂ) = matrixOfOp A_swap :=
        (matrixOfOp_matrixOp _).symm
      change Matrix.trace (swapMatrix * matrixOfOp D0.rho) =
        Matrix.trace (matrixOfOp (D0.rho * A_swap))
      rw [hA, matrixOfOp_mul_eq, Matrix.trace_mul_comm]
    rw [hmul, ← operatorExpectation_eq_faithfulGibbsDensity_expectation H0 hH0 hZ0 A_swap]
    exact operatorExpectation_im_eq_zero_of_isSelfAdjoint H0 hH0 hZ0 A_swap hA_swap_sa
  have hexp_re : (Matrix.trace (swapMatrix * rho0)).re =
      (finiteOperatorTrace (D0.rho * A_swap)).re := by
    have hmul : Matrix.trace (swapMatrix * rho0) = finiteOperatorTrace (D0.rho * A_swap) := by
      have hA : (swapMatrix : Matrix (Fin 2) (Fin 2) ℂ) = matrixOfOp A_swap :=
        (matrixOfOp_matrixOp _).symm
      change Matrix.trace (swapMatrix * matrixOfOp D0.rho) =
        Matrix.trace (matrixOfOp (D0.rho * A_swap))
      rw [hA, matrixOfOp_mul_eq, Matrix.trace_mul_comm]
    rw [hmul]
  have hstar_grad : star gradF = -(swapMatrix - (finiteOperatorTrace (D0.rho * A_swap)).re • (1 : Matrix (Fin 2) (Fin 2) ℂ)) := by
    have hcsa : IsSelfAdjoint (centeredStatistic D0 A_swap) := by
      rw [isSelfAdjoint_iff]
      dsimp only [centeredStatistic]
      change (A_swap - expectationReal D0 A_swap • (1 : FiniteOperatorAlgebra 2))† =
        A_swap - expectationReal D0 A_swap • (1 : FiniteOperatorAlgebra 2)
      rw [← finiteOperatorStarRealCLM_apply, (finiteOperatorStarRealCLM 2).map_sub,
        finiteOperatorStarRealCLM_apply, finiteOperatorStarRealCLM_apply, hA_swap_sa.star_eq,
        (isSelfAdjoint_real_smul (expectationReal D0 A_swap) 1
          (by rw [isSelfAdjoint_iff, star_one])).star_eq]
    have hgs : IsSelfAdjoint gradF := by
      change IsSelfAdjoint (-matrixOfOp (centeredStatistic D0 A_swap))
      rw [isSelfAdjoint_iff, star_neg]
      congr 1
      change (matrixOfOp (centeredStatistic D0 A_swap)).conjTranspose = matrixOfOp (centeredStatistic D0 A_swap)
      rw [← matrixOfOp_adjoint, hcsa.adjoint_eq]
    rw [hgs.star_eq]
    change -matrixOfOp (A_swap - (finiteOperatorTrace (D0.rho * A_swap)).re •
      (1 : FiniteOperatorAlgebra 2)) = _
    rw [matrixOfOp_sub_eq, matrixOfOp_real_smul, matrixOfOp_one_eq, A_swap, matrixOfOp_matrixOp]
    rfl
  refine hre.congr_fderiv (ContinuousLinearMap.ext fun V => ?_)
  symm
  change (Matrix.trace (star gradF * V)).re =
    (-Complex.reCLM ∘SL ContinuousLinearMap.restrictScalars ℝ
      ((Matrix.trace (swapMatrix * rho0)) •
        ((ContinuousLinearMap.toSpanSingleton ℂ (-(Matrix.trace rho0 ^ 2)⁻¹)).comp
          matrix_trace_clm) +
      ((fun x : ℂ => x⁻¹) ∘ Matrix.trace) rho0 • trace_swap_mul_clm)) V
  rw [htr1]
  simp only [ContinuousLinearMap.coe_comp, ContinuousLinearMap.coe_restrictScalars',
    Function.comp_apply, neg_apply, add_apply, smul_apply,
    ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul, Complex.reCLM_apply,
    one_pow, inv_one, neg_mul, mul_neg, mul_one, one_mul,
    hstar_grad, Matrix.trace_neg, Complex.neg_re,
    Matrix.sub_mul, Matrix.trace_sub, Matrix.smul_mul,
    Matrix.trace_smul, Complex.sub_re]
  rw [add_comm, ← sub_eq_add_neg, Complex.sub_re]
  congr 1
  congr 1
  · simp [htr1, trace_swap_mul_clm]
  · rw [Complex.mul_re, hexp_im, zero_mul, sub_zero, hexp_re]
    simp [matrix_trace_clm]

/-- `T1-F6-05`: Layer 3 `hasDerivAt_freeEnergy_of_matrixKuboMoriMobility` & `antitoneOn_freeEnergy_of_matrixKuboMoriMobility` along `H(t) := B_tilt + t • A_swap`. -/
theorem t1_f6_05_freeEnergyMatrixKuboMoriMobility :
    let H : ℝ → FiniteOperatorAlgebra 2 := fun t => B_tilt + t • A_swap
    let hH : ∀ t : ℝ, IsSelfAdjoint (H t) := fun t =>
      isSelfAdjoint_add_op hB_tilt_sa (isSelfAdjoint_real_smul t A_swap hA_swap_sa)
    let hZ : ∀ t : ℝ, 0 < gibbsPartitionReal (H t) := fun t =>
      tracedExponential_re_pos_of_isSelfAdjoint (H t) (hH t)
    let D : ℝ → FaithfulDensityOperator 2 := fun t => faithfulGibbsDensity (H t) (hH t) (hZ t)
    let rho : ℝ → Matrix (Fin 2) (Fin 2) ℂ := fun t => matrixOfOp (normalizedExponential (H t))
    let sys : ℝ → MetriplecticDissipation.MetriplecticDissipativeSystem (Fin 2) := fun t =>
      { rho := rho t
        H := 0
        grad_F := -matrixOfOp (centeredStatistic (D t) A_swap)
        Onsager := matrixKuboMoriMobility (D t) (continuous_faithfulGibbsDensity_rpow (H t) (hH t) (hZ t)) }
    (∀ t : ℝ, HasDerivAt (fun s => Φ_norm_swap (rho s)) (MetriplecticDissipation.freeEnergyRate (sys t)) t) ∧
      deriv (fun s => Φ_norm_swap (rho s)) 0 < 0 ∧
      AntitoneOn (fun s => Φ_norm_swap (rho s)) (Set.Icc 0 1) := by
  intro H hH hZ D rho sys
  have hpow : ∀ t : ℝ, Continuous (D t).rpow := fun t =>
    continuous_faithfulGibbsDensity_rpow (H t) (hH t) (hZ t)
  have hrho_eq : ∀ t : ℝ, rho t = matrixOfOp (D t).rho := fun t => by
    change matrixOfOp (normalizedExponential (H t)) = matrixOfOp (D t).rho
    rw [faithfulGibbsDensity_rho_eq_normalizedExponential (H t) (hH t) (hZ t)]
  have hrho_deriv : ∀ t : ℝ, HasDerivAt rho (MetriplecticDissipation.stateEvolution (sys t)) t := by
    intro t
    have hH_deriv : HasDerivAt H A_swap t := hasDerivAt_add_real_smul B_tilt A_swap t
    have hnorm := hasDerivAt_normalizedExponential_centered H (hH t) hA_swap_sa hH_deriv
    have hmat := ((matrixOfOpCLMℝ 2).hasFDerivAt.comp_hasDerivAt t hnorm)
    have hevol : matrixOfOp ((D t).kuboMoriTransform (centeredStatistic (D t) A_swap)) =
        MetriplecticDissipation.stateEvolution (sys t) := by
      simp only [MetriplecticDissipation.stateEvolution, MetriplecticDissipation.unitaryFlow,
        MetriplecticDissipation.commutator, sys, zero_mul, mul_zero, sub_zero, smul_zero, zero_sub]
      change matrixOfOp ((D t).kuboMoriTransform (centeredStatistic (D t) A_swap)) =
        -(matrixKuboMoriMobility (D t) (hpow t) (-matrixOfOp (centeredStatistic (D t) A_swap)))
      rw [LinearMap.map_neg, neg_neg]
      dsimp only [matrixKuboMoriMobility]
      change matrixOfOp ((D t).kuboMoriTransform (centeredStatistic (D t) A_swap)) =
        matrixOfOp ((D t).kuboMoriTransform (matrixOp (matrixOfOp (centeredStatistic (D t) A_swap))))
      rw [matrixOp_matrixOfOp]
    change HasDerivAt rho (matrixOfOp ((D t).kuboMoriTransform (centeredStatistic (D t) A_swap))) t
      at hmat
    rwa [hevol] at hmat
  let L_dΦ : ℝ → (Matrix (Fin 2) (Fin 2) ℂ →ₗ[ℝ] ℝ) := fun t =>
    { toFun := fun V => (Matrix.trace (star (sys t).grad_F * V)).re
      map_add' := fun V W => by rw [Matrix.mul_add, Matrix.trace_add, Complex.add_re]
      map_smul' := fun r V => by
        simp only [RingHom.id_apply]
        rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, Complex.real_smul,
          Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] }
  let dΦ : ℝ → (Matrix (Fin 2) (Fin 2) ℂ →L[ℝ] ℝ) := fun t =>
    { toLinearMap := L_dΦ t
      cont := LinearMap.continuous_of_finiteDimensional (L_dΦ t) }
  have hΦ : ∀ t : ℝ, HasFDerivAt Φ_norm_swap (dΦ t) (rho t) := fun t => by
    rw [hrho_eq t]
    exact Φ_norm_swap_hasFDerivAt (H t) (hH t) (hZ t)
  have hderiv_all : ∀ t : ℝ,
      HasDerivAt (fun s => Φ_norm_swap (rho s)) (MetriplecticDissipation.freeEnergyRate (sys t)) t :=
    fun t => hasDerivAt_freeEnergy_of_matrixKuboMoriMobility Φ_norm_swap dΦ rho sys
      (hrho_deriv t) (hΦ t) (fun _ => rfl)
  have hneg0 : deriv (fun s => Φ_norm_swap (rho s)) 0 < 0 := by
    rw [(hderiv_all 0).deriv]
    change (Matrix.trace (star (sys 0).grad_F *
      MetriplecticDissipation.stateEvolution (sys 0))).re < 0
    have hevol0 : MetriplecticDissipation.stateEvolution (sys 0) =
        -(matrixKuboMoriMobility (D 0) (hpow 0) (-matrixOfOp (centeredStatistic (D 0) A_swap))) := by
      simp [MetriplecticDissipation.stateEvolution, MetriplecticDissipation.unitaryFlow,
        MetriplecticDissipation.commutator, sys]
    rw [hevol0]
    change (Matrix.trace (star (-matrixOfOp (centeredStatistic (D 0) A_swap)) *
      (-(matrixKuboMoriMobility (D 0) (hpow 0) (-matrixOfOp (centeredStatistic (D 0) A_swap)))))).re < 0
    rw [LinearMap.map_neg, neg_neg, star_neg, Matrix.neg_mul, Matrix.trace_neg,
      Complex.neg_re]
    have htr_pos := matrixKuboMoriMobility_trace_eq_bkm (D 0) (hpow 0)
      (matrixOfOp (centeredStatistic (D 0) A_swap))
    rw [show matrixOp (matrixOfOp (centeredStatistic (D 0) A_swap)) = centeredStatistic (D 0) A_swap from
      matrixOp_matrixOfOp _] at htr_pos
    rw [htr_pos]
    apply neg_lt_zero.mpr
    apply (D 0).kuboMoriPairing_self_re_pos _ (hpow 0)
    intro hstar0
    have h0 : centeredStatistic (D 0) A_swap = 0 := by
      have hst := congrArg star hstar0
      rw [star_star, ← finiteOperatorStarRealCLM_apply,
        (finiteOperatorStarRealCLM 2).map_zero] at hst
      exact hst
    have hmem := (centeredStatistic_eq_zero_iff (D 0) (hpow 0) A_swap).mp h0
    obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp hmem
    have hm := congrArg (fun Z : GibbsOperator 2 => matrixOfOp Z 0 1) hr
    rw [matrixOfOp_real_smul, matrixOfOp_one_eq, A_swap, matrixOfOp_matrixOp] at hm
    norm_num [swapMatrix] at hm
  have hcont : ContinuousOn (fun s => Φ_norm_swap (rho s)) (Set.Icc 0 1) :=
    fun t _ => (hderiv_all t).continuousAt.continuousWithinAt
  have hanti : AntitoneOn (fun s => Φ_norm_swap (rho s)) (Set.Icc 0 1) :=
    antitoneOn_freeEnergy_of_matrixKuboMoriMobility Φ_norm_swap dΦ rho sys D hpow
      (convex_Icc 0 1) hcont
      (fun t _ => by
        change star (-matrixOfOp (centeredStatistic (D t) A_swap)) =
          -matrixOfOp (centeredStatistic (D t) A_swap)
        rw [star_neg]
        congr 1
        have hcsa : IsSelfAdjoint (centeredStatistic (D t) A_swap) := by
          rw [isSelfAdjoint_iff]
          change (A_swap - expectationReal (D t) A_swap • (1 : FiniteOperatorAlgebra 2))† =
            A_swap - expectationReal (D t) A_swap • (1 : FiniteOperatorAlgebra 2)
          rw [← finiteOperatorStarRealCLM_apply, (finiteOperatorStarRealCLM 2).map_sub,
            finiteOperatorStarRealCLM_apply, finiteOperatorStarRealCLM_apply, hA_swap_sa.star_eq,
            (isSelfAdjoint_real_smul _ 1 (by rw [isSelfAdjoint_iff, star_one])).star_eq]
        change (matrixOfOp (centeredStatistic (D t) A_swap)).conjTranspose = _
        rw [← matrixOfOp_adjoint, hcsa.adjoint_eq])
      (fun _ _ _ => rfl)
      (fun t _ => by simp [sys])
      (fun t _ => hrho_deriv t)
      (fun t _ => hΦ t)
      (fun _ _ _ => rfl)
  exact ⟨hderiv_all, hneg0, hanti⟩

/-- `T2-F6-01`: Strict `< 0` dissipation off equilibrium (`ρ ≠ σ`) vs `= 0` at equilibrium (`ρ = σ`) or `Onsager = 0`. -/
theorem t2_f6_01_strictNegVsEquilibriumZero :
    let σ_mix : FiniteOperatorAlgebra 2 := (1 / 2 : ℝ) • (1 : FiniteOperatorAlgebra 2)
    let v0 := gibbsMetriplecticFlow tiltOp2 σ_mix tiltOp2 tiltOp2_isSelfAdjoint
    let H_curve : ℝ → FiniteOperatorAlgebra 2 := fun s => tiltOp2 + s • v0
    let D_d63 := faithfulGibbsDensity H_d63 hH_d63_sa hZ_d63_pos
    let H_eq : ℝ → FiniteOperatorAlgebra 2 := fun _ => H_d63
    let sys_zero : MetriplecticDissipation.MetriplecticDissipativeSystem (Fin 2) :=
      { rho := matrixOfOp D_d63.rho, H := 0, grad_F := swapMatrix, Onsager := 0 }
    deriv (fun s => gibbsRelativePotential σ_mix (H_curve s)) 0 < 0 ∧
      deriv (fun s => gibbsRelativePotential D_d63.rho (H_eq s)) 0 = 0 ∧
      MetriplecticDissipation.freeEnergyRate sys_zero = 0 := by
  intro σ_mix v0 H_curve D_d63 H_eq sys_zero
  have hneg := capstone_qubit_nondegenerate_witness.2.2.2.2.2.2
  have hconst : (fun s => gibbsRelativePotential D_d63.rho (H_eq s)) =
      fun _ => gibbsRelativePotential D_d63.rho H_d63 := rfl
  have hsys0 : MetriplecticDissipation.freeEnergyRate sys_zero = 0 := by
    simp [MetriplecticDissipation.freeEnergyRate, MetriplecticDissipation.stateEvolution,
      MetriplecticDissipation.unitaryFlow, MetriplecticDissipation.commutator, sys_zero]
  refine ⟨hneg, by simp [hconst], hsys0⟩

/-- `T2-F6-02`: `Complex.slitPlane` boundary: `(I * π) • 1 ∉ slitPlane` vs `H_d63 ∈ slitPlane`. -/
theorem t2_f6_02_slitPlaneBoundary :
    let H_bad : FiniteOperatorAlgebra 2 := (Complex.I * Real.pi) • (1 : FiniteOperatorAlgebra 2)
    tracedExponential H_bad = -2 ∧
      tracedExponential H_bad ∉ Complex.slitPlane ∧
      tracedExponential H_d63 ∈ Complex.slitPlane := by
  intro H_bad
  have hexp : NormedSpace.exp H_bad = (-1 : ℂ) • (1 : FiniteOperatorAlgebra 2) := by
    let φ : ℂ →L[ℂ] FiniteOperatorAlgebra 2 :=
      (ContinuousLinearMap.id ℂ ℂ).smulRight (1 : FiniteOperatorAlgebra 2)
    have hsum : Summable (fun n : ℕ => (n.factorial : ℂ)⁻¹ • (Complex.I * Real.pi) ^ n) :=
      NormedSpace.expSeries_summable' (𝕂 := ℂ) (Complex.I * Real.pi)
    have hmap : φ (∑' n : ℕ, (n.factorial : ℂ)⁻¹ • (Complex.I * Real.pi) ^ n) =
        ∑' n : ℕ, φ ((n.factorial : ℂ)⁻¹ • (Complex.I * Real.pi) ^ n) :=
      φ.map_tsum hsum
    have hpow : ∀ n : ℕ, ((n.factorial : ℂ)⁻¹ • H_bad ^ n) =
        φ ((n.factorial : ℂ)⁻¹ • (Complex.I * Real.pi) ^ n) := fun n => by
      dsimp only [φ, H_bad]
      rw [smul_pow, one_pow, ContinuousLinearMap.smulRight_apply,
        ContinuousLinearMap.id_apply, smul_eq_mul, smul_smul]
    have hexp_c : (∑' n : ℕ, (n.factorial : ℂ)⁻¹ • (Complex.I * Real.pi) ^ n) =
        NormedSpace.exp (Complex.I * Real.pi) :=
      (congrFun (NormedSpace.exp_eq_tsum ℂ) _).symm
    rw [NormedSpace.exp_eq_tsum ℂ]
    simp_rw [hpow]
    rw [← hmap, hexp_c, ← Complex.exp_eq_exp_ℂ,
      mul_comm Complex.I (Real.pi : ℂ), Complex.exp_pi_mul_I]
    rfl
  have htr : tracedExponential H_bad = -2 := by
    change finiteOperatorTrace (NormedSpace.exp H_bad) = -2
    rw [hexp, ← finiteOperatorTraceLinear_apply, _root_.map_smul, finiteOperatorTraceLinear_apply]
    change (-1 : ℂ) * Matrix.trace (matrixOfOp (1 : FiniteOperatorAlgebra 2)) = -2
    rw [matrixOfOp_one_eq, Matrix.trace_one, Fintype.card_fin]
    norm_num
  have hnot : tracedExponential H_bad ∉ Complex.slitPlane := by
    rw [htr, Complex.mem_slitPlane_iff]
    norm_num
  exact ⟨htr, hnot, tracedExponential_mem_slitPlane_of_isSelfAdjoint H_d63 hH_d63_sa⟩

/-- `T2-F6-03`: Noncommuting trajectory `[H(t), H'(t)] ≠ 0` alongside `hasDerivAt_normalizedExponential`. -/
theorem t2_f6_03_noncommutingTrajectory (t : ℝ) :
    let H : ℝ → FiniteOperatorAlgebra 2 := fun s => B_tilt + s • A_swap
    H t * A_swap ≠ A_swap * H t ∧
      HasDerivAt (fun s => normalizedExponential (H s))
        ((faithfulGibbsDensity (H t) (isSelfAdjoint_add_op hB_tilt_sa (isSelfAdjoint_real_smul t A_swap hA_swap_sa))
            (tracedExponential_re_pos_of_isSelfAdjoint (H t)
              (isSelfAdjoint_add_op hB_tilt_sa (isSelfAdjoint_real_smul t A_swap hA_swap_sa)))).kuboMoriTransform
          (A_swap - finiteOperatorTrace
            ((faithfulGibbsDensity (H t) (isSelfAdjoint_add_op hB_tilt_sa (isSelfAdjoint_real_smul t A_swap hA_swap_sa))
              (tracedExponential_re_pos_of_isSelfAdjoint (H t)
                (isSelfAdjoint_add_op hB_tilt_sa (isSelfAdjoint_real_smul t A_swap hA_swap_sa)))).rho * A_swap) •
              (1 : FiniteOperatorAlgebra 2))) t := by
  intro H
  have hnc : H t * A_swap ≠ A_swap * H t := by
    change (B_tilt + t • A_swap) * A_swap ≠ A_swap * (B_tilt + t • A_swap)
    rw [add_mul, mul_add, real_smul_eq_complex_smul, smul_mul_assoc, mul_smul_comm]
    intro heq
    have hc : B_tilt * A_swap = A_swap * B_tilt := add_right_cancel heq
    exact hAB_noncomm hc.symm
  exact ⟨hnc, (t1_f6_04_hasDerivAtNormalizedExponential t).2⟩

/-- `T2-F6-04`: Noncommuting `H, grad_F` reversible-cancellation failure on complex Hermitian `Y_mat` (`σ_y`) Gibbs state. -/
theorem t2_f6_04_noncommutingReversibleCancellationFailure :
    let Y_mat : Matrix (Fin 2) (Fin 2) ℂ := !![0, -Complex.I; Complex.I, 0]
    let Y_op : FiniteOperatorAlgebra 2 := matrixOp Y_mat
    let rho : Matrix (Fin 2) (Fin 2) ℂ := matrixOfOp (normalizedExponential Y_op)
    let H := InfoGeometry.Physics.KleinBottleSewingExact.tilt2
    let gradF := (swapMatrix : Matrix (Fin 2) (Fin 2) ℂ)
    (Matrix.trace (star gradF * (-Complex.I • (H * rho - rho * H)))).re ≠ 0 := by
  intro Y_mat Y_op rho H gradF
  have hY_sa : IsSelfAdjoint Y_op := by
    rw [isSelfAdjoint_iff]
    apply matrixOfOp_injective
    change matrixOfOp (ContinuousLinearMap.adjoint Y_op) = matrixOfOp Y_op
    dsimp only [Y_op]
    rw [matrixOfOp_adjoint, matrixOfOp_matrixOp]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Y_mat]
  have hZ : 0 < gibbsPartitionReal Y_op := tracedExponential_re_pos_of_isSelfAdjoint Y_op hY_sa
  let Z := gibbsPartitionReal Y_op
  let D := faithfulGibbsDensity Y_op hY_sa hZ
  have hY_sq : Y_op * Y_op = 1 := by
    apply matrixOfOp_injective
    dsimp only [Y_op]
    rw [matrixOfOp_mul_eq, matrixOfOp_one_eq, matrixOfOp_matrixOp]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Y_mat, Matrix.mul_apply, Fin.sum_univ_two]
  have hspec : ∀ x ∈ spectrum ℝ Y_op, x = 1 ∨ x = -1 := by
    intro x hx
    have hpoly : (x ^ 2 - 1 : ℝ) ∈ spectrum ℝ (Y_op * Y_op - (1 : FiniteOperatorAlgebra 2)) := by
      have hcont : ContinuousOn (fun y : ℝ => y ^ 2 - 1) (spectrum ℝ Y_op) :=
        ((continuous_pow 2).sub continuous_const).continuousOn
      have hcfc : cfc (fun y : ℝ => y ^ 2 - 1) Y_op = Y_op * Y_op - 1 := by
        let f : ℝ → ℝ := fun y => y ^ 2
        let g : ℝ → ℝ := fun _ => 1
        have hf : ContinuousOn f (spectrum ℝ Y_op) := (continuous_pow 2).continuousOn
        have hg : ContinuousOn g (spectrum ℝ Y_op) := continuousOn_const
        rw [cfc_sub f g Y_op hf hg]
        change cfc (fun y : ℝ => id y ^ 2) Y_op - cfc g Y_op = Y_op * Y_op - 1
        rw [cfc_pow (id : ℝ → ℝ) 2 Y_op continuousOn_id,
          cfc_id ℝ Y_op, cfc_const (1 : ℝ) Y_op hY_sa, pow_two, _root_.map_one]
      rw [← hcfc, cfc_map_spectrum (ha := hY_sa) (hf := hcont)]
      exact ⟨x, hx, rfl⟩
    rw [hY_sq, sub_self, spectrum.zero_eq] at hpoly
    have h0 : x ^ 2 - 1 = 0 := hpoly
    have hmul : (x - 1) * (x + 1) = 0 := by linarith
    rcases mul_eq_zero.mp hmul with h1 | h2
    · left; linarith
    · right; linarith
  let a : ℝ := (Real.exp 1 - Real.exp (-1)) / (2 * Z)
  let b : ℝ := (Real.exp 1 + Real.exp (-1)) / (2 * Z)
  have hcfc : D.rho = cfc (NoncommutativeGibbsRpowNormalizationBridge.normalizedScalarGibbsWeight Z) Y_op :=
    faithfulGibbsDensity_rho_eq_normalizedGibbsCFC Y_op hY_sa hZ
  have hcongr : cfc (NoncommutativeGibbsRpowNormalizationBridge.normalizedScalarGibbsWeight Z) Y_op =
      cfc (fun x : ℝ => a * x + b) Y_op := by
    apply cfc_congr
    intro x hx
    rcases hspec x hx with rfl | rfl
    · simp only [NoncommutativeGibbsRpowNormalizationBridge.normalizedScalarGibbsWeight, a, b]
      field_simp [hZ.ne']
      ring
    · simp only [NoncommutativeGibbsRpowNormalizationBridge.normalizedScalarGibbsWeight, a, b]
      field_simp [hZ.ne']
      ring
  have hlin : cfc (fun x : ℝ => a * x + b) Y_op = a • Y_op + b • (1 : FiniteOperatorAlgebra 2) := by
    have hf : ContinuousOn (fun x : ℝ => a * x) (spectrum ℝ Y_op) :=
      (continuous_const.mul continuous_id).continuousOn
    have hg : ContinuousOn (fun _ : ℝ => b) (spectrum ℝ Y_op) := continuousOn_const
    rw [cfc_add Y_op (fun x => a * x) (fun _ => b) hf hg]
    change cfc (fun x => a * id x) Y_op + cfc (fun _ => b) Y_op = a • Y_op + b • 1
    rw [cfc_const_mul a (id : ℝ → ℝ) Y_op continuousOn_id,
      cfc_id ℝ Y_op, cfc_const b Y_op hY_sa, Algebra.algebraMap_eq_smul_one]
  have hrho_eq : rho = (a : ℂ) • Y_mat + (b : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    have hnorm : normalizedExponential Y_op = D.rho :=
      (faithfulGibbsDensity_rho_eq_normalizedExponential Y_op hY_sa hZ).symm
    change matrixOfOp (normalizedExponential Y_op) = _
    dsimp only [Y_op] at hnorm hcfc hcongr hlin ⊢
    rw [hnorm, hcfc, hcongr, hlin, matrixOfOp_add, matrixOfOp_real_smul, matrixOfOp_real_smul,
      matrixOfOp_one_eq, matrixOfOp_matrixOp]
  rw [hrho_eq]
  have hcalc : (Matrix.trace (star gradF * (-Complex.I • (H * ((a : ℂ) • Y_mat +
      (b : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) -
      ((a : ℂ) • Y_mat + (b : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) * H)))).re = -4 * a := by
    have hs : star gradF = (swapMatrix : Matrix (Fin 2) (Fin 2) ℂ) := by
      ext i j; fin_cases i <;> fin_cases j <;> simp [gradF, swapMatrix]
    rw [hs]
    simp only [H, InfoGeometry.Physics.KleinBottleSewingExact.tilt2, swapMatrix, Y_mat,
      Matrix.trace, Matrix.diag, Fin.sum_univ_two, Matrix.mul_apply, Matrix.sub_apply,
      Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul,
      Fin.isValue, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one]
    simp
    ring
  rw [hcalc]
  have ha_pos : 0 < a := by
    apply div_pos
    · linarith [Real.exp_lt_exp.mpr (by norm_num : (-1 : ℝ) < 1)]
    · linarith
  linarith

/-- `T2-F6-05`: Empty dimension `n = 0` gives `tracedExponential 0 = 0 ∉ Complex.slitPlane`. -/
theorem t2_f6_05_dim0SlitPlaneBoundary :
    tracedExponential (0 : FiniteOperatorAlgebra 0) = 0 ∧
      tracedExponential (0 : FiniteOperatorAlgebra 0) ∉ Complex.slitPlane := by
  have h0 : tracedExponential (0 : FiniteOperatorAlgebra 0) = 0 := by
    change finiteOperatorTrace (NormedSpace.exp (0 : FiniteOperatorAlgebra 0)) = 0
    change Matrix.trace (matrixOfOp (NormedSpace.exp (0 : FiniteOperatorAlgebra 0))) = 0
    simp
  exact ⟨h0, by rw [h0]; exact Complex.zero_notMem_slitPlane⟩

/-- `T2-F6-06`: Degenerate `grad_F ∈ ker` boundary (`grad_F = 0` gives `freeEnergyRate = 0`; `1 ∈ ker(centeredStatistic)` while `matrixKuboMoriMobility D 1 ≠ 0`). -/
theorem t2_f6_06_degenerateKernelBoundary :
    let D := faithfulGibbsDensity H_d63 hH_d63_sa hZ_d63_pos
    let hpow := continuous_faithfulGibbsDensity_rpow H_d63 hH_d63_sa hZ_d63_pos
    let sys0 : MetriplecticDissipation.MetriplecticDissipativeSystem (Fin 2) :=
      { rho := matrixOfOp D.rho
        H := 0
        grad_F := 0
        Onsager := matrixKuboMoriMobility D hpow }
    MetriplecticDissipation.freeEnergyRate sys0 = 0 ∧
      centeredStatistic D (1 : FiniteOperatorAlgebra 2) = 0 ∧
      matrixKuboMoriMobility D hpow 1 ≠ 0 := by
  intro D hpow sys0
  have hrate : MetriplecticDissipation.freeEnergyRate sys0 = 0 := by
    simp [MetriplecticDissipation.freeEnergyRate, sys0]
  have hcent : centeredStatistic D (1 : FiniteOperatorAlgebra 2) = 0 :=
    (centeredStatistic_eq_zero_iff D hpow 1).mpr
      (Submodule.mem_span_singleton.mpr ⟨1, one_smul ℝ 1⟩)
  have hmob_ne : matrixKuboMoriMobility D hpow 1 ≠ 0 := by
    intro h0
    have htr := matrixKuboMoriMobility_trace_eq_bkm D hpow 1
    rw [h0, Matrix.mul_zero, Matrix.trace_zero] at htr
    rw [show matrixOp 1 = (1 : FiniteOperatorAlgebra 2) from by
      apply matrixOfOp_injective; rw [matrixOfOp_matrixOp, matrixOfOp_one_eq],
      star_one] at htr
    have hre := congrArg Complex.re htr
    rw [Complex.zero_re] at hre
    have hpos := D.kuboMoriPairing_self_re_pos 1 hpow one_ne_zero
    linarith
  exact ⟨hrate, hcent, hmob_ne⟩

end GapC_Layer3

end GapC_Tests

/-! ## Section 3: Tier 1 & Tier 2 — Gap D (`F7`, `F8`) -/

section GapD_Tests

attribute [local instance 100] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

private abbrev Mat2R := Matrix (Fin 2) (Fin 2) ℝ
private abbrev Mat2C := Matrix (Fin 2) (Fin 2) ℂ

private def innerMat2RDeriv (K : Mat2R) : NonAssocDerivation.derivations ℝ Mat2R :=
  ⟨{ toFun := fun X => K * X - X * K
     map_add' := fun X Y => by noncomm_ring
     map_smul' := fun r X => by
       change K * (r • X) - (r • X) * K = r • (K * X - X * K)
       rw [mul_smul_comm, smul_mul_assoc, smul_sub] },
   fun X Y => by
     change K * (X * Y) - (X * Y) * K = (K * X - X * K) * Y + X * (K * Y - Y * K)
     noncomm_ring⟩

private def innerMat2CDeriv (K : Mat2C) : NonAssocDerivation.derivations ℂ Mat2C :=
  ⟨{ toFun := fun X => K * X - X * K
     map_add' := fun X Y => by noncomm_ring
     map_smul' := fun c X => by
       change K * (c • X) - (c • X) * K = c • (K * X - X * K)
       rw [mul_smul_comm, smul_mul_assoc, smul_sub] },
   fun X Y => by
     change K * (X * Y) - (X * Y) * K = (K * X - X * K) * Y + X * (K * Y - Y * K)
     noncomm_ring⟩

private theorem mat2R_comm_01_10_ne_zero :
    matrixUnit01 * matrixUnit10 - matrixUnit10 * matrixUnit01 ≠ (0 : Mat2R) := by
  intro h0
  have hm := congrArg (fun M : Mat2R => M 0 0) h0
  norm_num [matrixUnit01, matrixUnit10, Matrix.mul_apply, Fin.sum_univ_two] at hm

private theorem mat2R_K1_K2_comm_ne_zero :
    (K1_real * K2_real - K2_real * K1_real) * matrixUnit01 -
      matrixUnit01 * (K1_real * K2_real - K2_real * K1_real) ≠ 0 := by
  intro h0
  have hm := congrArg (fun M : Mat2R => M 0 0) h0
  norm_num [K1_real, K2_real, matrixUnit01, Matrix.mul_apply, Fin.sum_univ_two] at hm

/-- `T1-F7-01`: All `10` `ℤ`-linear `Modular.*` derivation/predicate types bridge into `derivations ℤ Mat2R`. -/
theorem t1_f7_01_modularZDerivationsRoundTrip :
    let dK : NonAssocDerivation.derivations ℤ Mat2R := innerIntDerivation matrixUnit01
    let d_lieIdeal := lieIdealRingDerivationEquivDerivations.symm dK
    let d_dualExp := dualExponentialRingDerivationEquivDerivations.symm dK
    let d_lieAlg := lieAlgebraRingDerivationEquivDerivations.symm dK
    let d_synth := synthesisRingDerivationEquivDerivations.symm dK
    let d_nc := noncommutativeDerivationEquivDerivations.symm dK
    let d_comm := commutantDerivationEquivDerivations.symm dK
    let d_idealDer := lieIdealDerivationAddEquivDerivations.symm dK
    let d_ts := timeSemigroupDerivationEquivDerivations.symm dK
    let d_exact := InfoGeometry.Modular.ExactSequence.modularDerivation matrixUnit01
    lieIdealRingDerivationEquivDerivations d_lieIdeal = dK ∧
      dualExponentialRingDerivationEquivDerivations d_dualExp = dK ∧
      lieAlgebraRingDerivationEquivDerivations d_lieAlg = dK ∧
      synthesisRingDerivationEquivDerivations d_synth = dK ∧
      noncommutativeDerivationEquivDerivations d_nc = dK ∧
      commutantDerivationEquivDerivations d_comm = dK ∧
      lieIdealDerivationAddEquivDerivations d_idealDer = dK ∧
      timeSemigroupDerivationEquivDerivations d_ts = dK ∧
      modularDerivationToDerivations d_exact = dK ∧
      InfoGeometry.Modular.Noncommutative.IsNCDerivation (dK : Module.End ℤ Mat2R) ∧
      (dK : Module.End ℤ Mat2R) matrixUnit10 ≠ 0 := by
  intro dK d_lieIdeal d_dualExp d_lieAlg d_synth d_nc d_comm d_idealDer d_ts d_exact
  have hexact : modularDerivationToDerivations d_exact = dK := by
    apply Subtype.ext; ext X; rfl
  refine ⟨lieIdealRingDerivationEquivDerivations.apply_symm_apply dK,
    dualExponentialRingDerivationEquivDerivations.apply_symm_apply dK,
    lieAlgebraRingDerivationEquivDerivations.apply_symm_apply dK,
    synthesisRingDerivationEquivDerivations.apply_symm_apply dK,
    noncommutativeDerivationEquivDerivations.apply_symm_apply dK,
    commutantDerivationEquivDerivations.apply_symm_apply dK,
    lieIdealDerivationAddEquivDerivations.apply_symm_apply dK,
    timeSemigroupDerivationEquivDerivations.apply_symm_apply dK,
    hexact, dK.property, mat2R_comm_01_10_ne_zero⟩

/-- `T1-F7-02`: `R`-linear `Modular.*` and `IsLinearDerivation` types bridge into `derivations R A`. -/
theorem t1_f7_02_modularRLinearDerivations :
    let dC : NonAssocDerivation.derivations ℂ Mat2C :=
      innerMat2CDeriv (swapMatrix : Mat2C)
    let d_skms := superKMSLinearDerivationEquivDerivations.symm dC
    let d_kms := kmsStateLinearDerivationEquivDerivations.symm dC
    let d_semi := semidirectDerivationEquivDerivations.symm dC
    let dR0 : ℝ →ₗ[ℝ] ℝ := 0
    let hTri : InfoGeometry.Modular.IsLinearDerivation dR0 := fun _ _ => by dsimp [dR0]; simp
    let hModS : InfoGeometry.Modular.ModularSurprisalDerivationBridge.IsLinearDerivation dR0 :=
      fun _ _ => by dsimp [dR0]; simp
    let hInfoS : InfoGeometry.Information.ModularSurprisalDerivationBridge.IsLinearDerivation dR0 :=
      fun _ _ => by dsimp [dR0]; simp
    let d_tri := trifoldIsLinearDerivationEquivDerivations (R := ℝ) ⟨dR0, hTri⟩
    let d_modS := modularSurprisalIsLinearDerivationEquivDerivations (R := ℝ) ⟨dR0, hModS⟩
    let d_infoS := infoModularSurprisalIsLinearDerivationEquivDerivations (R := ℝ) ⟨dR0, hInfoS⟩
    superKMSLinearDerivationEquivDerivations d_skms = dC ∧
      kmsStateLinearDerivationEquivDerivations d_kms = dC ∧
      semidirectDerivationEquivDerivations d_semi = dC ∧
      (dC : Module.End ℂ Mat2C) (!![1, 0; 0, -1] : Mat2C) ≠ 0 ∧
      d_tri = (0 : NonAssocDerivation.derivations ℝ ℝ) ∧
      d_modS = (0 : NonAssocDerivation.derivations ℝ ℝ) ∧
      d_infoS = (0 : NonAssocDerivation.derivations ℝ ℝ) ∧
      Function.Injective (trifoldIsLinearDerivationEquivDerivations (R := ℝ)) ∧
      Function.Injective (modularSurprisalIsLinearDerivationEquivDerivations (R := ℝ)) ∧
      Function.Injective (infoModularSurprisalIsLinearDerivationEquivDerivations (R := ℝ)) := by
  intro dC d_skms d_kms d_semi dR0 hTri hModS hInfoS d_tri d_modS d_infoS
  have hne : (dC : Module.End ℂ Mat2C) (!![1, 0; 0, -1] : Mat2C) ≠ 0 := by
    intro h0
    have hm := congrArg (fun M : Mat2C => M 0 1) h0
    change ((swapMatrix : Mat2C) * (!![1, 0; 0, -1] : Mat2C) -
      (!![1, 0; 0, -1] : Mat2C) * (swapMatrix : Mat2C)) 0 1 = 0 at hm
    norm_num [swapMatrix, Matrix.mul_apply, Fin.sum_univ_two] at hm
  exact ⟨superKMSLinearDerivationEquivDerivations.apply_symm_apply dC,
    kmsStateLinearDerivationEquivDerivations.apply_symm_apply dC,
    semidirectDerivationEquivDerivations.apply_symm_apply dC,
    hne,
    rfl,
    rfl,
    rfl,
    (trifoldIsLinearDerivationEquivDerivations (R := ℝ)).injective,
    (modularSurprisalIsLinearDerivationEquivDerivations (R := ℝ)).injective,
    (infoModularSurprisalIsLinearDerivationEquivDerivations (R := ℝ)).injective⟩

/-- `T1-F7-03`: `ColimitFlowDerivation`, `ColimitKMSInfinitesimal`, and `LocalDerivationSystem` tower bridges. -/
theorem t1_f7_03_colimitTowerAndLocalSystem :
    let A : ℕ → Type := fun _ => Mat2C
    let iota : ∀ n, A n →⋆ₐ[ℂ] A (n + 1) := fun _ => StarAlgHom.id ℂ Mat2C
    let dC : NonAssocDerivation.derivations ℂ Mat2C := innerMat2CDeriv (swapMatrix : Mat2C)
    let tFlow : InfoGeometry.Modular.ColimitFlowDerivation.TowerDerivation A iota :=
      { deriv := fun _ => (dC : Module.End ℂ Mat2C)
        leibniz := fun _ => dC.property
        deriv_comm := fun _ => rfl }
    let tKMS := colimitFlowTowerEquivKMSTower A iota tFlow
    let psi : ∀ n, A n →⋆ₐ[ℂ] Mat2C := fun _ => StarAlgHom.id ℂ Mat2C
    let d_colim := colimitFlowTowerToColimitDerivation A iota Mat2C psi (fun _ => rfl)
      (fun x => ⟨0, x, rfl⟩) (fun _ _ h => ⟨0, h⟩) tFlow
    let d_kms_colim := colimitKMSInfinitesimalToColimitDerivation A iota Mat2C psi (fun _ => rfl)
      (fun x => ⟨0, x, rfl⟩) (fun _ _ h => ⟨0, h⟩) tKMS
    let sys : InfoGeometry.Modular.ColimitDerivation.DirectedAlgSystem (R := ℂ) ℕ A :=
      { map := fun _ => AlgHom.id ℂ Mat2C
        map_self := fun _ _ => rfl
        map_trans := fun _ _ _ => rfl }
    let colim : InfoGeometry.Modular.ColimitDerivation.AlgColimitCocone (R := ℂ) ℕ A sys Mat2C :=
      { inr := fun _ => AlgHom.id ℂ Mat2C
        inr_comm := fun _ _ => rfl
        surj_dense := fun x => ⟨0, x, rfl⟩
        inr_inj := fun {i} _ _ h => ⟨i, le_refl i, h⟩ }
    let dsys : InfoGeometry.Modular.ColimitDerivation.LocalDerivationSystem (R := ℂ) ℕ A sys :=
      { deriv := fun _ => (dC : Module.End ℂ Mat2C)
        deriv_leibniz := fun _ => dC.property
        intertwine := fun _ _ => rfl }
    colimitFlowStageDerivation A iota tFlow 0 = dC ∧
      colimitKMSStageDerivation A iota tKMS 0 = dC ∧
      (d_colim : Module.End ℂ Mat2C) (!![1, 0; 0, -1] : Mat2C) =
        (dC : Module.End ℂ Mat2C) (!![1, 0; 0, -1] : Mat2C) ∧
      (d_kms_colim : Module.End ℂ Mat2C) (!![1, 0; 0, -1] : Mat2C) =
        (dC : Module.End ℂ Mat2C) (!![1, 0; 0, -1] : Mat2C) ∧
      localDerivationStage sys dsys 0 = dC ∧
      colimitDerivationToDerivations sys colim dsys = dC := by
  intro A iota dC tFlow tKMS psi d_colim d_kms_colim sys colim dsys
  have h1 : (d_colim : Module.End ℂ Mat2C) (!![1, 0; 0, -1] : Mat2C) =
      (dC : Module.End ℂ Mat2C) (!![1, 0; 0, -1] : Mat2C) := by
    dsimp only [d_colim]
    have heq := colimitFlowTowerToColimitDerivation_apply_psi A iota Mat2C psi
      (fun _ => rfl) (fun x => ⟨0, x, rfl⟩) (fun _ _ h => ⟨0, h⟩) tFlow 0 !![1, 0; 0, -1]
    dsimp only [psi, InfoGeometry.Modular.ColimitFlowDerivation.liftedDeriv, tFlow] at heq
    exact heq
  have h2 : (d_kms_colim : Module.End ℂ Mat2C) (!![1, 0; 0, -1] : Mat2C) =
      (dC : Module.End ℂ Mat2C) (!![1, 0; 0, -1] : Mat2C) := by
    dsimp only [d_kms_colim, colimitKMSInfinitesimalToColimitDerivation]
    have heq := colimitFlowTowerToColimitDerivation_apply_psi A iota Mat2C psi
      (fun _ => rfl) (fun x => ⟨0, x, rfl⟩) (fun _ _ h => ⟨0, h⟩)
      ((colimitFlowTowerEquivKMSTower A iota).symm tKMS) 0 !![1, 0; 0, -1]
    dsimp only [psi, InfoGeometry.Modular.ColimitFlowDerivation.liftedDeriv, tKMS, tFlow] at heq
    exact heq
  have h3 : colimitDerivationToDerivations sys colim dsys = dC := by
    apply Subtype.ext; apply LinearMap.ext; intro x
    change InfoGeometry.Modular.ColimitDerivation.colimitDerivVal sys dsys colim (colim.inr 0 x) = _
    rw [InfoGeometry.Modular.ColimitDerivation.colimitDerivVal_inr]
    rfl
  exact ⟨rfl, rfl, h1, h2, rfl, h3⟩

/-- `T1-F7-04`: `OuterDerivation` and all standalone associative `*Derivation` wrappers embed cleanly. -/
theorem t1_f7_04_outerAndStandaloneWrappers :
    let K_diag : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℝ :=
      Matrix.fromBlocks matrixUnit01 0 0 matrixUnit01
    let D_outer : InfoGeometry.Modular.TrifoldSurprisalIntertwiningBridge.OuterDerivation (Fin 2) ℝ :=
      { toLinearMap :=
          { toFun := fun X => K_diag * X - X * K_diag
            map_add' := fun _ _ => by noncomm_ring
            map_smul' := fun r X => by
              change K_diag * (r • X) - (r • X) * K_diag = r • (K_diag * X - X * K_diag)
              rw [mul_smul_comm, smul_mul_assoc, smul_sub] }
        leibniz' := fun X Y => by
          change K_diag * (X * Y) - (X * Y) * K_diag =
            (K_diag * X - X * K_diag) * Y + X * (K_diag * Y - Y * K_diag)
          noncomm_ring
        map_one' := by simp
        map_gamma' := by
          change K_diag * InfoGeometry.Modular.TrifoldSurprisalIntertwiningBridge.GammaGrading -
            InfoGeometry.Modular.TrifoldSurprisalIntertwiningBridge.GammaGrading * K_diag = 0
          dsimp [K_diag, InfoGeometry.Modular.TrifoldSurprisalIntertwiningBridge.GammaGrading]
          rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
          simp }
    let dR : NonAssocDerivation.derivations ℝ Mat2R := innerMat2RDeriv matrixUnit01
    let dZ : NonAssocDerivation.derivations ℤ Mat2R := innerIntDerivation matrixUnit01
    let dC : NonAssocDerivation.derivations ℂ Mat2C := innerMat2CDeriv (swapMatrix : Mat2C)
    let polyDer : _root_.Derivation ℝ (Polynomial ℝ) (Polynomial ℝ) :=
      { toLinearMap := Polynomial.derivative
        map_one_eq_zero' := Polynomial.derivative_one
        leibniz' := fun p q => by
          change Polynomial.derivative (p * q) =
            p • Polynomial.derivative q + q • Polynomial.derivative p
          simp only [Polynomial.derivative_mul, smul_eq_mul]
          ring }
    let d_frame : InfoGeometry.Thermo.BipolarObservableMetriplecticAlgebra.DerivationFrame (Polynomial ℝ) :=
      ⟨polyDer, polyDer, polyDer, fun _ => rfl⟩
    let d_poset := posetOpDerivationEquivDerivations.symm dZ
    let d_commR := commRingDerivationEquivDerivations.symm (innerIntDerivation (0 : Polynomial ℝ))
    let d_gen := genericDerivationEquivDerivations.symm dZ
    let d_dlog := densityDLogDerivationEquivDerivations.symm dZ
    let d_syn := synthesisDerivationEquivDerivations.symm dZ
    let d_cert := dualExpCertDerivationEquivDerivations.symm dZ
    let d_phase := phaseSpaceDerivationEquivDerivations.symm dZ
    let d_gauge := gaugeDerivationEquivDerivations.symm dZ
    let d_alg := algDerivationEquivDerivations.symm dR
    let d_op := operatorDerivationEquivDerivations.symm dR
    let d_e2e := endToEndDerivationEquivDerivations.symm dC
    let d_kmsM := kmsModularDerivationEquivDerivations.symm dC
    let d_cpx := complexDerivationEquivDerivations.symm dC
    (outerDerivationToDerivations D_outer : Module.End ℝ (Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℝ))
        (Matrix.fromBlocks matrixUnit10 (0 : Mat2R) 0 0) ≠ 0 ∧
      Function.Injective (outerDerivationToDerivations (ι := Fin 2) (R := ℝ)) ∧
      posetOpDerivationEquivDerivations d_poset = dZ ∧
      commRingDerivationEquivDerivations d_commR = innerIntDerivation (0 : Polynomial ℝ) ∧
      genericDerivationEquivDerivations d_gen = dZ ∧
      densityDLogDerivationEquivDerivations d_dlog = dZ ∧
      synthesisDerivationEquivDerivations d_syn = dZ ∧
      dualExpCertDerivationEquivDerivations d_cert = dZ ∧
      phaseSpaceDerivationEquivDerivations d_phase = dZ ∧
      gaugeDerivationEquivDerivations d_gauge = dZ ∧
      algDerivationEquivDerivations d_alg = dR ∧
      operatorDerivationEquivDerivations d_op = dR ∧
      endToEndDerivationEquivDerivations d_e2e = dC ∧
      kmsModularDerivationEquivDerivations d_kmsM = dC ∧
      complexDerivationEquivDerivations d_cpx = dC ∧
      (mathlibDerivationLieEquivDerivations polyDer : Module.End ℝ (Polynomial ℝ)) Polynomial.X = 1 ∧
      (derivationFrameToDerivationsTriple d_frame).1 = mathlibDerivationLinearEquivDerivations polyDer := by
  intro K_diag D_outer dR dZ dC polyDer d_frame d_poset d_commR d_gen d_dlog d_syn
    d_cert d_phase d_gauge d_alg d_op d_e2e d_kmsM d_cpx
  have houter_ne :
      (outerDerivationToDerivations D_outer : Module.End ℝ (Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℝ))
        (Matrix.fromBlocks matrixUnit10 (0 : Mat2R) 0 0) ≠ 0 := by
    intro h0
    have hm := congrArg (fun M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℝ => M (Sum.inl 0) (Sum.inl 0)) h0
    change (K_diag * Matrix.fromBlocks matrixUnit10 (0 : Mat2R) (0 : Mat2R) (0 : Mat2R) -
      Matrix.fromBlocks matrixUnit10 (0 : Mat2R) (0 : Mat2R) (0 : Mat2R) * K_diag)
        (Sum.inl 0) (Sum.inl 0) = 0 at hm
    dsimp [K_diag] at hm
    rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply] at hm
    simp only [Matrix.mul_zero, zero_mul, add_zero,
      Matrix.fromBlocks_apply₁₁] at hm
    have h00 : (matrixUnit01 * matrixUnit10 - matrixUnit10 * matrixUnit01 : Mat2R) 0 0 = 0 := hm
    norm_num [matrixUnit01, matrixUnit10, Matrix.mul_apply, Fin.sum_univ_two] at h00
  exact ⟨houter_ne,
    outerDerivationToDerivations_injective,
    posetOpDerivationEquivDerivations.apply_symm_apply dZ,
    commRingDerivationEquivDerivations.apply_symm_apply _,
    genericDerivationEquivDerivations.apply_symm_apply dZ,
    densityDLogDerivationEquivDerivations.apply_symm_apply dZ,
    synthesisDerivationEquivDerivations.apply_symm_apply dZ,
    dualExpCertDerivationEquivDerivations.apply_symm_apply dZ,
    phaseSpaceDerivationEquivDerivations.apply_symm_apply dZ,
    gaugeDerivationEquivDerivations.apply_symm_apply dZ,
    algDerivationEquivDerivations.apply_symm_apply dR,
    operatorDerivationEquivDerivations.apply_symm_apply dR,
    endToEndDerivationEquivDerivations.apply_symm_apply dC,
    kmsModularDerivationEquivDerivations.apply_symm_apply dC,
    complexDerivationEquivDerivations.apply_symm_apply dC,
    by dsimp [mathlibDerivationLieEquivDerivations, mathlibDerivationLinearEquivDerivations, polyDer]; exact Polynomial.derivative_X,
    rfl⟩

/-- `T1-F7-05`: `StarDerivation`, `InvolutiveDerivation`, and `KreinStarDerivation` inject, lift to `DerivationLieLane`, and evaluate in `OnsagerFormPairing`. -/
theorem t1_f7_05_properSubtypesAndOnsagerFormPairing :
    let hK_skew : star K1_real = -K1_real := by
      ext i j; fin_cases i <;> fin_cases j <;> simp [K1_real, Matrix.star_apply]
    let d_star := InfoGeometry.Algebra.Cuntz.innerStarDerivation K1_real hK_skew
    let d_inv : InfoGeometry.Algebra.Cuntz.InvolutiveDerivation (A := Mat2R) star :=
      ⟨d_star.toAddHom, d_star.leibniz', d_star.star'⟩
    let K_krein : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2) :=
      K1_real.toEuclideanLin.toContinuousLinearMap
    let hK_krein : InfoGeometry.Krein.KreinSpace.IsKreinSkewAdjoint K_krein := by
      change ContinuousLinearMap.adjoint K_krein = -K_krein
      apply ContinuousLinearMap.coe_injective
      have hconj : K1_real.conjTranspose = -K1_real := by
        ext i j; fin_cases i <;> fin_cases j <;> simp [K1_real, Matrix.conjTranspose_apply]
      have hnegLin : Matrix.toEuclideanLin (-K1_real) = -K1_real.toEuclideanLin := by
        apply LinearMap.ext; intro v; ext i
        simp [Matrix.toEuclideanLin, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      have hadj := K1_real.toEuclideanLin_conjTranspose_eq_adjoint
      rw [hconj, hnegLin] at hadj
      exact hadj.symm
    let d_krein := InfoGeometry.OperatorAlgebra.kreinCommutatorDerivation K_krein hK_krein
    let dR := innerMat2RDeriv K1_real
    let K_lane := realDerivationLieLane Mat2R
    let S_mat : OnsagerCasimirSystem Mat2R :=
      { dissipative :=
          { toFun := fun X =>
              { toFun := fun Y => Matrix.trace (star X * Y)
                map_add' := fun Y Z => by rw [Matrix.mul_add, Matrix.trace_add]
                map_smul' := fun r Y => by simp }
            map_add' := fun X Y => by
              ext Z; simp [Matrix.add_mul, Matrix.trace_add]
            map_smul' := fun r X => by
              ext Z; simp }
        reversible := 0
        dissipative_symm := fun X Y => by
          change Matrix.trace (star X * Y) = Matrix.trace (star Y * X)
          simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.star_apply,
            star_trivial, Fin.sum_univ_two]
          ring
        reversible_skew := fun _ _ => by simp
        dissipative_nonneg := fun X => by
          change 0 ≤ Matrix.trace (star X * X)
          simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.star_apply,
            star_trivial, Fin.sum_univ_two]
          nlinarith [sq_nonneg (X 0 0), sq_nonneg (X 1 0), sq_nonneg (X 0 1), sq_nonneg (X 1 1)] }
    let P_mat : ParityOnsagerSystem Mat2R :=
      { toOnsagerCasimirSystem := S_mat
        T := ⟨LinearMap.id, fun _ => rfl⟩
        dissipative_T_even := fun _ _ => rfl
        reversible_T_odd := fun X Y => by simp [S_mat] }
    let PP := ParityOnsagerFormPairing.ofValueParity P_mat ![dR]
    let ω : DerivationOperatorForm K_lane 1 :=
      oneFormAlternatingLinearEquiv K_lane (exteriorDerivativeZero K_lane K2_real)
    Function.Injective (starDerivationToDerivations (A := Mat2R)) ∧
      Function.Injective (involutiveDerivationToDerivations (A := Mat2R) star) ∧
      Function.Injective (kreinStarDerivationToDerivations (H := EuclideanSpace ℝ (Fin 2))) ∧
      starDerivationToDerivations d_star ∈ starPreservingDerivations Mat2R ∧
      involutiveDerivationToDerivations star d_inv = starDerivationToDerivations d_star ∧
      (kreinStarDerivationToDerivations d_krein : Module.End ℤ _) P_real2 ≠ 0 ∧
      0 < PP.dissipative ω ω ∧
      PP.totalGenerator (PP.T.op ω) (PP.T.op ω) = PP.totalGenerator ω ω := by
  intro hK_skew d_star d_inv K_krein hK_krein d_krein dR K_lane S_mat P_mat PP ω
  have hkrein_ne : (kreinStarDerivationToDerivations d_krein : Module.End ℤ _) P_real2 ≠ 0 := by
    intro h0
    have hval := congrArg (fun f : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2) =>
      f (EuclideanSpace.basisFun (Fin 2) ℝ 0) 0) h0
    have hK_apply : ∀ v : EuclideanSpace ℝ (Fin 2),
        K_krein v = WithLp.toLp 2 ![v 1, -v 0] := fun v => by
      ext i; fin_cases i <;>
        simp [K_krein, K1_real, Matrix.toEuclideanLin, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    change K_krein (P_real2 (EuclideanSpace.basisFun (Fin 2) ℝ 0)) 0 -
      P_real2 (K_krein (EuclideanSpace.basisFun (Fin 2) ℝ 0)) 0 = 0 at hval
    rw [P_real2_apply, hK_apply, hK_apply, P_real2_apply] at hval
    simp only [EuclideanSpace.basisFun_apply] at hval
    norm_num at hval
  have hdiss_pos : 0 < PP.dissipative ω ω := by
    change 0 < Matrix.trace (star (K1_real * K2_real - K2_real * K1_real) *
      (K1_real * K2_real - K2_real * K1_real))
    norm_num [K1_real, K2_real, Matrix.trace, Matrix.diag, Matrix.mul_apply,
      Matrix.star_apply, Fin.sum_univ_two]
  exact ⟨starDerivationToDerivations_injective,
    involutiveDerivationToDerivations_injective star,
    kreinStarDerivationToDerivations_injective,
    d_star.star',
    rfl,
    hkrein_ne,
    hdiss_pos,
    onsager_pairing_derivationForm_reciprocity K_lane PP ω ω⟩

/-- `T2-F7-01`: `ScalarDerivation` fails on noncommutative `Mat2R` and succeeds on commutative `Polynomial ℝ`. -/
theorem t2_f7_01_scalarDerivationNoncommBoundary :
    let D : Mat2R → Mat2R := fun X => matrixUnit01 * X - X * matrixUnit01
    let a : Mat2R := matrixUnit10
    let b : Mat2R := matrixUnit01
    let d_poly : InfoGeometry.Canonical.CoordinateFreeSouriau.ScalarDerivation (Polynomial ℝ) :=
      { toFun := Polynomial.derivative
        map_add' := fun _ _ => Polynomial.derivative_add
        map_mul' := fun p q => by simp only [Polynomial.derivative_mul]; ring }
    D (a * b) ≠ a * D b + b * D a ∧
      (scalarDerivationEquivDerivations d_poly : Module.End ℤ (Polynomial ℝ)) Polynomial.X = 1 := by
  intro D a b d_poly
  refine ⟨?_, by dsimp [scalarDerivationEquivDerivations, d_poly]; exact Polynomial.derivative_X⟩
  intro heq
  have hm := congrArg (fun M : Mat2R => M 0 1) heq
  norm_num [D, a, b, matrixUnit01, matrixUnit10, Matrix.mul_apply, Fin.sum_univ_two] at hm

/-- `T2-F7-02`: Non-block-diagonal `K'` fails `[K', GammaGrading] = 0`, establishing `OuterDerivation` is a proper subset. -/
theorem t2_f7_02_outerDerivationProperSubtypeBoundary :
    let K' : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℝ := Matrix.fromBlocks 0 1 0 0
    let Γ := (InfoGeometry.Modular.TrifoldSurprisalIntertwiningBridge.GammaGrading :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℝ)
    K' * Γ ≠ Γ * K' := by
  intro K' Γ heq
  have hm := congrArg (fun M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℝ => M (Sum.inl 0) (Sum.inr 0)) heq
  dsimp [K', Γ, InfoGeometry.Modular.TrifoldSurprisalIntertwiningBridge.GammaGrading] at hm
  rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply] at hm
  simp only [Matrix.mul_zero, zero_mul, one_mul,
    zero_add, add_zero, Matrix.fromBlocks_apply₁₂, Matrix.neg_apply, Matrix.one_apply_eq] at hm
  norm_num at hm

/-- `T2-F7-03`: Self-adjoint `H := swapMatrix` fails `StarDerivation.star'` on `matrixUnit01`. -/
theorem t2_f7_03_starDerivationProperSubtypeBoundary :
    let H : Mat2R := swapMatrix
    let X : Mat2R := matrixUnit01
    star (H * X - X * H) ≠ H * star X - star X * H := by
  intro H X heq
  have hm := congrArg (fun M : Mat2R => M 0 0) heq
  norm_num [H, X, swapMatrix, matrixUnit01, Matrix.mul_apply,
    Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply,
    Matrix.vecMul, dotProduct, Fin.sum_univ_two] at hm

/-- `T2-F7-04`: Non-abelian Lie bracket `⁅D₁, D₂⁆ ≠ 0` preserved across `Modular.*` bridges. -/
theorem t2_f7_04_modularNonAbelianBracket :
    let d1 : NonAssocDerivation.derivations ℤ Mat2R := innerIntDerivation K1_real
    let d2 : NonAssocDerivation.derivations ℤ Mat2R := innerIntDerivation K2_real
    let m1 := lieIdealRingDerivationEquivDerivations.symm d1
    let m2 := lieIdealRingDerivationEquivDerivations.symm d2
    ⁅lieIdealRingDerivationEquivDerivations m1,
      lieIdealRingDerivationEquivDerivations m2⁆ ≠ 0 ∧
      (⁅lieIdealRingDerivationEquivDerivations m1,
        lieIdealRingDerivationEquivDerivations m2⁆ : Module.End ℤ Mat2R) matrixUnit01 ≠ 0 := by
  intro d1 d2 m1 m2
  dsimp only [m1, m2]
  rw [Equiv.apply_symm_apply lieIdealRingDerivationEquivDerivations d1,
    Equiv.apply_symm_apply lieIdealRingDerivationEquivDerivations d2]
  have hact : (⁅d1, d2⁆ : Module.End ℤ Mat2R) matrixUnit01 ≠ 0 := by
    change (K1_real * (K2_real * matrixUnit01 - matrixUnit01 * K2_real) -
        (K2_real * matrixUnit01 - matrixUnit01 * K2_real) * K1_real) -
      (K2_real * (K1_real * matrixUnit01 - matrixUnit01 * K1_real) -
        (K1_real * matrixUnit01 - matrixUnit01 * K1_real) * K2_real) ≠ 0
    have hrew : (K1_real * (K2_real * matrixUnit01 - matrixUnit01 * K2_real) -
        (K2_real * matrixUnit01 - matrixUnit01 * K2_real) * K1_real) -
      (K2_real * (K1_real * matrixUnit01 - matrixUnit01 * K1_real) -
        (K1_real * matrixUnit01 - matrixUnit01 * K1_real) * K2_real) =
      (K1_real * K2_real - K2_real * K1_real) * matrixUnit01 -
        matrixUnit01 * (K1_real * K2_real - K2_real * K1_real) := by noncomm_ring
    rw [hrew]
    exact mat2R_K1_K2_comm_ne_zero
  exact ⟨fun h0 => hact (congrArg (fun D : NonAssocDerivation.derivations ℤ Mat2R =>
    (D : Module.End ℤ Mat2R) matrixUnit01) h0), hact⟩

/-- `T2-F7-05`: Scalar/carrier boundary: `ℤ`-linear vs `ℝ`-linear lifting and `ZornMatrix ℝ` scalar tower guard. -/
theorem t2_f7_05_scalarCarrierHypothesisBoundary :
    let d1 : NonAssocDerivation.derivations ℤ Mat2R := innerIntDerivation K1_real
    let hsmul : ∀ (c : ℝ) (X : Mat2R),
        (d1 : Module.End ℤ Mat2R) (c • X) = c • (d1 : Module.End ℤ Mat2R) X := fun c X => by
      change K1_real * (c • X) - (c • X) * K1_real = c • (K1_real * X - X * K1_real)
      rw [mul_smul_comm, smul_mul_assoc, smul_sub]
    (modularLinearLiftToReal d1 hsmul : Module.End ℝ Mat2R) matrixUnit01 =
      (d1 : Module.End ℤ Mat2R) matrixUnit01 ∧
      Function.Injective canonicalZornDerivationsToIntDerivations :=
  ⟨rfl, canonicalZornDerivationsToIntDerivations_injective⟩

/-- `T1-F8-01`: All `3` `G2Derivation` definitions bridge into `derivations` / `LieActionLane` cleanly. -/
theorem t1_f8_01_threeG2Derivations :
    let f_lift_arg : (Fin 3 → ℝ) →ₗ[ℝ] Matrix (Fin 2) (Fin 2) (ExteriorAlgebra ℝ (Fin 3 → ℝ)) :=
      { toFun := fun v => !![ExteriorAlgebra.ι ℝ v, ExteriorAlgebra.ι ℝ v; 0, ExteriorAlgebra.ι ℝ v]
        map_add' := fun u v => by
          ext i j; fin_cases i <;> fin_cases j <;>
            simp [Matrix.add_apply, _root_.map_add]
        map_smul' := fun r v => by
          ext i j; fin_cases i <;> fin_cases j <;>
            simp [Matrix.smul_apply, _root_.map_smul] }
    let algMap : ExteriorAlgebra ℝ (Fin 3 → ℝ) →ₐ[ℝ] Matrix (Fin 2) (Fin 2) (ExteriorAlgebra ℝ (Fin 3 → ℝ)) :=
      ExteriorAlgebra.lift ℝ ⟨f_lift_arg, fun v => by
        ext i j; fin_cases i <;> fin_cases j <;>
          simp [f_lift_arg, Matrix.mul_apply, Fin.sum_univ_two]⟩
    let d_ext_lin : ExteriorAlgebra ℝ (Fin 3 → ℝ) →ₗ[ℝ] ExteriorAlgebra ℝ (Fin 3 → ℝ) :=
      { toFun := fun x => algMap x 0 1
        map_add' := fun x y => by simp [_root_.map_add]
        map_smul' := fun r x => by simp }
    have hdiag : ∀ z : ExteriorAlgebra ℝ (Fin 3 → ℝ),
        algMap z 0 0 = z ∧ algMap z 1 0 = 0 ∧ algMap z 1 1 = z := by
      intro z
      refine ExteriorAlgebra.induction (C := fun w =>
        algMap w 0 0 = w ∧ algMap w 1 0 = 0 ∧ algMap w 1 1 = w) ?_ ?_ ?_ ?_ z
      · intro r
        simp [Algebra.algebraMap_eq_smul_one]
      · intro v
        simp [algMap, f_lift_arg]
      · intro x y hx hy
        rw [map_mul]
        simp only [Matrix.mul_apply, Fin.sum_univ_two, hx.1, hx.2.1, hx.2.2,
          hy.1, hy.2.1, hy.2.2, mul_zero, zero_mul, add_zero, zero_add, and_self]
      · intro x y hx hy
        rw [_root_.map_add]
        simp only [Matrix.add_apply, hx.1, hx.2.1, hx.2.2, hy.1, hy.2.1, hy.2.2,
          add_zero, and_self]
    let d_g2_1 : InfoGeometry.Canonical.G2Derivation ℝ (Fin 3 → ℝ) :=
      { d := d_ext_lin
        map_add' := d_ext_lin.map_add
        map_smul' := d_ext_lin.map_smul
        map_mul' := fun x y => by
          change algMap (x * y) 0 1 = algMap x 0 1 * y + x * algMap y 0 1
          rw [map_mul]
          simp only [Matrix.mul_apply, Fin.sum_univ_two]
          rw [(hdiag x).1, (hdiag y).2.2, add_comm] }
    let d_g2_2 : InfoGeometry.Algebra.Zorn.G2DerivationLieAlgebra.G2Derivation ℝ :=
      { toFun := fun u => ![0, u 3, 0, -u 1, -u 5, u 4, 0]
        map_add := fun u v => by
          ext i; fin_cases i <;> simp <;> ring
        map_sub := fun u v => by
          ext i; fin_cases i <;> simp <;> ring
        leibniz := fun u v => by
          funext i
          fin_cases i <;>
            · dsimp [InfoGeometry.Algebra.Zorn.G2DerivationLieAlgebra.crossProd]
              ring }
    let d_g2_3 : InfoGeometry.Canonical.G2ToBraidChain.G2Derivation :=
      ⟨InfoGeometry.Lie.BaezG2SplitOctonion.rot01G2Derivation.1,
        InfoGeometry.Lie.BaezG2SplitOctonion.rot01G2Derivation.2⟩
    (albertG2DerivationEquivDerivations d_g2_1 :
        Module.End ℝ (ExteriorAlgebra ℝ (Fin 3 → ℝ))) (ExteriorAlgebra.ι ℝ (Pi.single 0 1)) ≠ 0 ∧
      (g2DerivationEquivIntDerivations ℝ d_g2_2 :
        Module.End ℤ (CrossProdCarrier ℝ)) ⟨Pi.single 3 1⟩ ≠ 0 ∧
      (g2ToBraidDerivationEquivVectorDerivations d_g2_3 :
        Module.End ℝ (InfoGeometry.Algebra.ZornVectorMatrix ℝ))
        (InfoGeometry.Algebra.ZornVectorMatrix.U 0) ≠ 0 := by
  intro f_lift_arg algMap d_ext_lin hdiag d_g2_1 d_g2_2 d_g2_3
  have h1 : (albertG2DerivationEquivDerivations d_g2_1 :
      Module.End ℝ (ExteriorAlgebra ℝ (Fin 3 → ℝ))) (ExteriorAlgebra.ι ℝ (Pi.single 0 1)) ≠ 0 := by
    change algMap (ExteriorAlgebra.ι ℝ (Pi.single 0 1)) 0 1 ≠ 0
    have hval : algMap (ExteriorAlgebra.ι ℝ (Pi.single 0 1)) 0 1 =
        ExteriorAlgebra.ι ℝ (Pi.single 0 1) := by
      simp [algMap, f_lift_arg]
    rw [hval]
    let f_dual : (Fin 3 → ℝ) →ₗ[ℝ] DualNumber ℝ :=
      { toFun := fun v => (v 0) • DualNumber.eps
        map_add' := fun u v => by simp [add_smul]
        map_smul' := fun r v => by simp [smul_smul] }
    let ev_dual : ExteriorAlgebra ℝ (Fin 3 → ℝ) →ₐ[ℝ] DualNumber ℝ :=
      ExteriorAlgebra.lift ℝ ⟨f_dual, fun v => by
        dsimp [f_dual]
        exact TrivSqZeroExt.ext (by simp) (by simp)⟩
    intro h0
    have hev := congrArg ev_dual h0
    rw [map_zero] at hev
    dsimp [ev_dual] at hev
    rw [ExteriorAlgebra.lift_ι_apply] at hev
    have hinl : (f_dual (Pi.single 0 1)).snd = (0 : DualNumber ℝ).snd :=
      congrArg TrivSqZeroExt.snd hev
    simp [f_dual] at hinl
  have h2 : (g2DerivationEquivIntDerivations ℝ d_g2_2 :
      Module.End ℤ (CrossProdCarrier ℝ)) ⟨Pi.single 3 1⟩ ≠ 0 := by
    intro h0
    have hc := congrArg (fun x : CrossProdCarrier ℝ => x.val 1) h0
    simp [g2DerivationEquivIntDerivations, g2DerivationToIntDerivations, d_g2_2] at hc
  have h3 : (g2ToBraidDerivationEquivVectorDerivations d_g2_3 :
      Module.End ℝ (InfoGeometry.Algebra.ZornVectorMatrix ℝ))
      (InfoGeometry.Algebra.ZornVectorMatrix.U 0) ≠ 0 := by
    intro h0
    have ha := congrArg (fun Z : InfoGeometry.Algebra.ZornVectorMatrix ℝ => Z.v 1) h0
    change ((InfoGeometry.Lie.CanonicalZornDerivation.vectorCanonicalLinearEquiv.symm
      (g2ToBraidDerivationEquivCanonicalZorn d_g2_3))
      (InfoGeometry.Algebra.ZornVectorMatrix.U 0)).v 1 = 0 at ha
    dsimp [InfoGeometry.Lie.CanonicalZornDerivation.vectorCanonicalLinearEquiv,
      InfoGeometry.Lie.CanonicalZornDerivation.canonicalToVectorDerivation,
      InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.canonicalVectorEquiv,
      g2ToBraidDerivationEquivCanonicalZorn, d_g2_3] at ha
    simp [InfoGeometry.Lie.BaezG2SplitOctonion.rot01G2Derivation,
      InfoGeometry.Lie.RealSplitOctonionDerivation.rot01Linear,
      InfoGeometry.Lie.RealSplitOctonionDerivationWitness.rot01Real,
      InfoGeometry.Algebra.ZornVectorMatrix.U,
      InfoGeometry.Algebra.ZornVec3.basis] at ha
  exact ⟨h1, h2, h3⟩

/-- `T1-F8-02`: `SplitCayleyG2Derivation`, `SplitCayleyDerivation`, `SplitCayleyLinearDerivation`, and `SplitOctonionDerivation`. -/
theorem t1_f8_02_splitCayleyAndSplitOctonionDerivations :
    let d_sc_g2 := InfoGeometry.Lie.BaezG2SplitOctonion.rot01G2Derivation
    let d_sc_lin := InfoGeometry.Lie.RealSplitOctonionDerivation.rot01LinearDerivation
    let d_sc_add := InfoGeometry.Lie.RealSplitOctonionDerivation.rot01Derivation
    let d_oct : InfoGeometry.Algebra.SplitOctonionDerivationAutomorphism.SplitOctonionDerivation :=
      { toLinearMap :=
          { toFun := fun X =>
              ⟨0, ⟨-X.u.y, X.u.x, 0⟩, ⟨-X.v.y, X.v.x, 0⟩, 0⟩
            map_add' := fun X Y => by
              cases X with | mk Xa Xu Xv Xd =>
              cases Y with | mk Ya Yu Yv Yd =>
              cases Xu; cases Xv; cases Yu; cases Yv
              have hadd : ∀ A B : InfoGeometry.Algebra.SplitOctonionZorn.SplitOctonion,
                  A + B = InfoGeometry.Algebra.SplitOctonionZorn.SplitOctonion.add A B := fun _ _ => rfl
              simp only [hadd]
              apply InfoGeometry.Algebra.SplitOctonionZorn.SplitOctonion.ext
              · dsimp [InfoGeometry.Algebra.SplitOctonionZorn.SplitOctonion.add]; ring
              · apply InfoGeometry.Algebra.SplitOctonionZorn.Vector3.ext <;>
                  (dsimp [InfoGeometry.Algebra.SplitOctonionZorn.SplitOctonion.add,
                      InfoGeometry.Algebra.SplitOctonionZorn.Vector3.add]; try ring)
              · apply InfoGeometry.Algebra.SplitOctonionZorn.Vector3.ext <;>
                  (dsimp [InfoGeometry.Algebra.SplitOctonionZorn.SplitOctonion.add,
                      InfoGeometry.Algebra.SplitOctonionZorn.Vector3.add]; try ring)
              · dsimp [InfoGeometry.Algebra.SplitOctonionZorn.SplitOctonion.add]; ring
            map_smul' := fun r X => by
              cases X with | mk Xa Xu Xv Xd =>
              cases Xu; cases Xv
              have hsmul : ∀ (c : ℝ) (A : InfoGeometry.Algebra.SplitOctonionZorn.SplitOctonion),
                  c • A = InfoGeometry.Algebra.SplitOctonionZorn.SplitOctonion.smul c A := fun _ _ => rfl
              have hvsmul : ∀ (c : ℝ) (u : InfoGeometry.Algebra.SplitOctonionZorn.Vector3),
                  c • u = InfoGeometry.Algebra.SplitOctonionZorn.Vector3.smul c u := fun _ _ => rfl
              simp only [hsmul]
              dsimp [InfoGeometry.Algebra.SplitOctonionZorn.SplitOctonion.smul]
              simp only [hvsmul]
              apply InfoGeometry.Algebra.SplitOctonionZorn.SplitOctonion.ext
              · ring
              · apply InfoGeometry.Algebra.SplitOctonionZorn.Vector3.ext <;>
                  (dsimp [InfoGeometry.Algebra.SplitOctonionZorn.Vector3.smul]; try ring)
              · apply InfoGeometry.Algebra.SplitOctonionZorn.Vector3.ext <;>
                  (dsimp [InfoGeometry.Algebra.SplitOctonionZorn.Vector3.smul]; try ring)
              · ring }
        leibniz := fun X Y => by
          cases X with | mk Xa Xu Xv Xd =>
          cases Y with | mk Ya Yu Yv Yd =>
          cases Xu; cases Xv; cases Yu; cases Yv
          have hadd : ∀ A B : InfoGeometry.Algebra.SplitOctonionZorn.SplitOctonion,
              A + B = InfoGeometry.Algebra.SplitOctonionZorn.SplitOctonion.add A B := fun _ _ => rfl
          have hmul : ∀ A B : InfoGeometry.Algebra.SplitOctonionZorn.SplitOctonion,
              A * B = InfoGeometry.Algebra.SplitOctonionZorn.SplitOctonion.mul A B := fun _ _ => rfl
          simp only [hmul, hadd]
          apply InfoGeometry.Algebra.SplitOctonionZorn.SplitOctonion.ext
          · dsimp [InfoGeometry.Algebra.SplitOctonionZorn.SplitOctonion.mul,
              InfoGeometry.Algebra.SplitOctonionZorn.SplitOctonion.add,
              InfoGeometry.Algebra.SplitOctonionZorn.Vector3.dot]; ring
          · apply InfoGeometry.Algebra.SplitOctonionZorn.Vector3.ext <;>
              (dsimp [InfoGeometry.Algebra.SplitOctonionZorn.SplitOctonion.mul,
                  InfoGeometry.Algebra.SplitOctonionZorn.SplitOctonion.add,
                  InfoGeometry.Algebra.SplitOctonionZorn.Vector3.sub,
                  InfoGeometry.Algebra.SplitOctonionZorn.Vector3.add,
                  InfoGeometry.Algebra.SplitOctonionZorn.Vector3.smul,
                  InfoGeometry.Algebra.SplitOctonionZorn.Vector3.cross]; try ring)
          · apply InfoGeometry.Algebra.SplitOctonionZorn.Vector3.ext <;>
              (dsimp [InfoGeometry.Algebra.SplitOctonionZorn.SplitOctonion.mul,
                  InfoGeometry.Algebra.SplitOctonionZorn.SplitOctonion.add,
                  InfoGeometry.Algebra.SplitOctonionZorn.Vector3.sub,
                  InfoGeometry.Algebra.SplitOctonionZorn.Vector3.add,
                  InfoGeometry.Algebra.SplitOctonionZorn.Vector3.smul,
                  InfoGeometry.Algebra.SplitOctonionZorn.Vector3.cross]; try ring)
          · dsimp [InfoGeometry.Algebra.SplitOctonionZorn.SplitOctonion.mul,
              InfoGeometry.Algebra.SplitOctonionZorn.SplitOctonion.add,
              InfoGeometry.Algebra.SplitOctonionZorn.Vector3.dot]; ring }
    let x_oct : SplitOctonionZornCarrier := ⟨⟨0, ⟨1, 0, 0⟩, ⟨0, 0, 0⟩, 0⟩⟩
    splitCayleyG2DerivationEquivCanonicalZorn.symm (splitCayleyG2DerivationEquivCanonicalZorn d_sc_g2) = d_sc_g2 ∧
      splitCayleyLinearDerivationEquivCanonicalZorn.symm
        (splitCayleyLinearDerivationEquivCanonicalZorn d_sc_lin) = d_sc_lin ∧
      (∃ X, (splitCayleyDerivationEquivIntDerivations d_sc_add :
        Module.End ℤ (InfoGeometry.Canonical.ZornMatrix ℝ)) X ≠ 0) ∧
      (splitOctonionDerivationEquivDerivations d_oct :
        Module.End ℝ SplitOctonionZornCarrier) x_oct ≠ 0 := by
  intro d_sc_g2 d_sc_lin d_sc_add d_oct x_oct
  obtain ⟨X_nz, hX_nz⟩ := InfoGeometry.Lie.RealSplitOctonionDerivation.rot01Derivation_nonzero
  have hoct_ne : (splitOctonionDerivationEquivDerivations d_oct :
      Module.End ℝ SplitOctonionZornCarrier) x_oct ≠ 0 := by
    intro h0
    have hy := congrArg (fun Z : SplitOctonionZornCarrier => Z.val.u.y) h0
    change (1 : ℝ) = 0 at hy
    norm_num at hy
  exact ⟨splitCayleyG2DerivationEquivCanonicalZorn.symm_apply_apply d_sc_g2,
    splitCayleyLinearDerivationEquivCanonicalZorn.symm_apply_apply d_sc_lin,
    ⟨X_nz, hX_nz⟩,
    hoct_ne⟩

private def ncZornRot01Fun
    (X : InfoGeometry.Physics.NoncommutativeZornBdGDerivations.NCZorn ℝ) :
    InfoGeometry.Physics.NoncommutativeZornBdGDerivations.NCZorn ℝ :=
  ⟨0, ![-(X.u 1), X.u 0, 0], ![-(X.v 1), X.v 0, 0], 0⟩

/-- `T1-F8-03`: `ZornVectorMatrix.Derivation`, `ZornDerivation` (`NCZorn`), `JordanDerivation`, and `H3ZornF4Derivations`. -/
theorem t1_f8_03_zornJordanAndH3ZornDerivations :
    let d_zvm : InfoGeometry.Algebra.ZornVectorMatrix.Derivation (R := ℝ) :=
      { toFun := fun X =>
          ⟨0, ![-(X.v 1), X.v 0, 0], ![-(X.w 1), X.w 0, 0], 0⟩
        map_add' := fun X Y => by
          ext i <;> simp [InfoGeometry.Algebra.ZornVectorMatrix.add]
          · (fin_cases i <;> simp); ring
          · (fin_cases i <;> simp); ring
        map_smul' := fun r X => by
          ext i <;> simp [InfoGeometry.Algebra.ZornVectorMatrix.smul]
          · fin_cases i <;> simp
          · fin_cases i <;> simp
        map_mul' := fun X Y => by
          ext i
          · simp [InfoGeometry.Algebra.ZornVectorMatrix.mul,
              InfoGeometry.Algebra.ZornVectorMatrix.add,
              InfoGeometry.Algebra.ZornVec3.dot, Fin.sum_univ_three]
          · fin_cases i <;>
              (simp [InfoGeometry.Algebra.ZornVectorMatrix.mul,
                InfoGeometry.Algebra.ZornVectorMatrix.add,
                InfoGeometry.Algebra.ZornVec3.cross]; try ring)
          · fin_cases i <;>
              (simp [InfoGeometry.Algebra.ZornVectorMatrix.mul,
                InfoGeometry.Algebra.ZornVectorMatrix.add,
                InfoGeometry.Algebra.ZornVec3.cross]; try ring)
          · simp [InfoGeometry.Algebra.ZornVectorMatrix.mul,
              InfoGeometry.Algebra.ZornVectorMatrix.add,
              InfoGeometry.Algebra.ZornVec3.dot, Fin.sum_univ_three] }
    let d_nc : InfoGeometry.Physics.NoncommutativeZornBdGDerivations.ZornDerivation ℝ :=
      { toFun := ncZornRot01Fun
        map_add := fun X Y => by
          apply InfoGeometry.Physics.NoncommutativeZornBdGDerivations.NCZorn.ext
          · change (0 : ℝ) = 0 + 0; ring
          · funext i; fin_cases i <;>
              (change _ = _ + _;
               dsimp [ncZornRot01Fun, InfoGeometry.Physics.NoncommutativeZornBdGDerivations.ncZornAdd];
               (try simp); (try ring))
          · funext i; fin_cases i <;>
              (change _ = _ + _;
               dsimp [ncZornRot01Fun, InfoGeometry.Physics.NoncommutativeZornBdGDerivations.ncZornAdd];
               (try simp); (try ring))
          · change (0 : ℝ) = 0 + 0; ring
        leibniz := fun X Y => by
          apply InfoGeometry.Physics.NoncommutativeZornBdGDerivations.NCZorn.ext
          · change (0 : ℝ) = _; dsimp [ncZornRot01Fun, InfoGeometry.Physics.NoncommutativeZornBdGDerivations.ncZornMul,
              InfoGeometry.Physics.NoncommutativeZornBdGDerivations.ncZornAdd,
              InfoGeometry.Physics.NoncommutativeZornBdGDerivations.dotNC]; ring
          · funext i
            change (ncZornRot01Fun (InfoGeometry.Physics.NoncommutativeZornBdGDerivations.ncZornMul X Y)).u i =
              (InfoGeometry.Physics.NoncommutativeZornBdGDerivations.ncZornAdd
                (InfoGeometry.Physics.NoncommutativeZornBdGDerivations.ncZornMul (ncZornRot01Fun X) Y)
                (InfoGeometry.Physics.NoncommutativeZornBdGDerivations.ncZornMul X (ncZornRot01Fun Y))).u i
            fin_cases i <;>
              (dsimp [ncZornRot01Fun, InfoGeometry.Physics.NoncommutativeZornBdGDerivations.ncZornMul,
                  InfoGeometry.Physics.NoncommutativeZornBdGDerivations.ncZornAdd,
                  InfoGeometry.Physics.NoncommutativeZornBdGDerivations.crossNC];
               ring)
          · funext i
            change (ncZornRot01Fun (InfoGeometry.Physics.NoncommutativeZornBdGDerivations.ncZornMul X Y)).v i =
              (InfoGeometry.Physics.NoncommutativeZornBdGDerivations.ncZornAdd
                (InfoGeometry.Physics.NoncommutativeZornBdGDerivations.ncZornMul (ncZornRot01Fun X) Y)
                (InfoGeometry.Physics.NoncommutativeZornBdGDerivations.ncZornMul X (ncZornRot01Fun Y))).v i
            fin_cases i <;>
              (dsimp [ncZornRot01Fun, InfoGeometry.Physics.NoncommutativeZornBdGDerivations.ncZornMul,
                  InfoGeometry.Physics.NoncommutativeZornBdGDerivations.ncZornAdd,
                  InfoGeometry.Physics.NoncommutativeZornBdGDerivations.crossNC];
               ring)
          · change (0 : ℝ) = _; dsimp [ncZornRot01Fun, InfoGeometry.Physics.NoncommutativeZornBdGDerivations.ncZornMul,
              InfoGeometry.Physics.NoncommutativeZornBdGDerivations.ncZornAdd,
              InfoGeometry.Physics.NoncommutativeZornBdGDerivations.dotNC]; ring }
    let D_jord_data : BilinearAlgData ℝ Mat2R :=
      { circ := fun X Y => (1 / 2 : ℝ) • (X * Y + Y * X)
        add_left := fun X Y Z => by simp [add_mul, mul_add, smul_add]; abel
        add_right := fun X Y Z => by simp [add_mul, mul_add, smul_add]; abel
        smul_left := fun r X Y => by simp [smul_add, smul_smul]; ring_nf
        smul_right := fun r X Y => by simp [smul_add, smul_smul]; ring_nf }
    let d_jord : InfoGeometry.Exceptional.AlbertDerivations.JordanDerivation (R := ℝ) D_jord_data.circ :=
      { toFun := fun X => K1_real * X - X * K1_real
        map_add := fun _ _ => by noncomm_ring
        map_smul := fun r X => by
          change K1_real * (r • X) - (r • X) * K1_real = r • (K1_real * X - X * K1_real)
          rw [mul_smul_comm, smul_mul_assoc, smul_sub]
        leibniz := fun X Y => by
          change K1_real * ((1 / 2 : ℝ) • (X * Y + Y * X)) -
              ((1 / 2 : ℝ) • (X * Y + Y * X)) * K1_real =
            (1 / 2 : ℝ) • ((K1_real * X - X * K1_real) * Y + Y * (K1_real * X - X * K1_real)) +
              (1 / 2 : ℝ) • (X * (K1_real * Y - Y * K1_real) + (K1_real * Y - Y * K1_real) * X)
          rw [mul_smul_comm, smul_mul_assoc, ← smul_sub, ← smul_add]
          congr 1
          noncomm_ring }
    let d_f4 : InfoGeometry.Algebra.H3ZornF4Derivations :=
      ⟨(InfoGeometry.Algebra.f4Basis 0).1, (InfoGeometry.Algebra.f4Basis 0).2⟩
    (zornVectorMatrixDerivationEquivDerivations ℝ d_zvm :
        Module.End ℝ (InfoGeometry.Algebra.ZornVectorMatrix ℝ))
        (InfoGeometry.Algebra.ZornVectorMatrix.U 0) ≠ 0 ∧
      (ncZornDerivationEquivIntDerivations ℝ d_nc :
        Module.End ℤ (NCZornCarrier ℝ)) ⟨⟨0, ![1, 0, 0], 0, 0⟩⟩ ≠ 0 ∧
      (jordanDerivationEquivDerivations D_jord_data d_jord :
        Module.End ℝ (BilinearAlgCarrier D_jord_data)) ⟨K2_real⟩ ≠ 0 ∧
      ((h3ZornF4DerivationLane).operatorAction d_f4 InfoGeometry.Algebra.h3_diag₁) ≠ 0 := by
  intro d_zvm d_nc D_jord_data d_jord d_f4
  have hzvm : (zornVectorMatrixDerivationEquivDerivations ℝ d_zvm :
      Module.End ℝ (InfoGeometry.Algebra.ZornVectorMatrix ℝ))
      (InfoGeometry.Algebra.ZornVectorMatrix.U 0) ≠ 0 := by
    intro h0
    have hv := congrArg (fun X : InfoGeometry.Algebra.ZornVectorMatrix ℝ => X.v 1) h0
    simp [d_zvm, InfoGeometry.Algebra.ZornVectorMatrix.U, InfoGeometry.Algebra.ZornVec3.basis] at hv
  have hnc : (ncZornDerivationEquivIntDerivations ℝ d_nc :
      Module.End ℤ (NCZornCarrier ℝ)) ⟨⟨0, ![1, 0, 0], 0, 0⟩⟩ ≠ 0 := by
    intro h0
    have hv := congrArg (fun X : NCZornCarrier ℝ => X.val.u 1) h0
    change (1 : ℝ) = 0 at hv
    norm_num at hv
  have hjord : (jordanDerivationEquivDerivations D_jord_data d_jord :
      Module.End ℝ (BilinearAlgCarrier D_jord_data)) ⟨K2_real⟩ ≠ 0 := by
    intro h0
    have hm := congrArg (fun X : BilinearAlgCarrier D_jord_data => X.val 0 1) h0
    change (K1_real * K2_real - K2_real * K1_real) 0 1 = 0 at hm
    norm_num [K1_real, K2_real, Matrix.mul_apply, Fin.sum_univ_two] at hm
  have hf4 : (h3ZornF4DerivationLane).operatorAction d_f4 InfoGeometry.Algebra.h3_diag₁ ≠ 0 := by
    have hdiag_sq : InfoGeometry.Algebra.candidateJordanMul InfoGeometry.Algebra.h3_diag₁
        InfoGeometry.Algebra.h3_diag₁ = InfoGeometry.Algebra.h3_diag₁ := by
      apply InfoGeometry.Algebra.H3Zorn.ext_h3 <;>
        (simp only [InfoGeometry.Algebra.candidateJordanMul,
          InfoGeometry.Algebra.H3Zorn.T, InfoGeometry.Algebra.H3Zorn.U,
          InfoGeometry.Algebra.H3Zorn.crossProduct, InfoGeometry.Algebra.H3Zorn.adjointQuad,
          InfoGeometry.Algebra.H3Zorn.traceBilin,
          InfoGeometry.Algebra.H3Zorn.add_readback, InfoGeometry.Algebra.H3Zorn.sub_readback,
          InfoGeometry.Algebra.H3Zorn.smul_readback, InfoGeometry.Algebra.H3Zorn.one_readback,
          InfoGeometry.Algebra.h3_diag₁, InfoGeometry.Algebra.ZornVectorMatrix.add,
          InfoGeometry.Algebra.ZornVectorMatrix.sub, InfoGeometry.Algebra.ZornVectorMatrix.neg,
          InfoGeometry.Algebra.ZornVectorMatrix.smul, InfoGeometry.Algebra.ZornVectorMatrix.zero,
          InfoGeometry.Algebra.ZornVectorMatrix.conj, InfoGeometry.Algebra.ZornVectorMatrix.mul,
          InfoGeometry.Algebra.ZornVectorMatrix.norm, InfoGeometry.Algebra.ZornVectorMatrix.trace,
          InfoGeometry.Algebra.ZornVec3.dot, InfoGeometry.Algebra.ZornVec3.cross,
          Fin.sum_univ_three]; try norm_num)
      all_goals (ext i <;> simp)
    have hoff_mul_diag : InfoGeometry.Algebra.candidateJordanMul (InfoGeometry.Algebra.h3_off₁₂ 0)
        InfoGeometry.Algebra.h3_diag₁ = (1 / 2 : ℝ) • InfoGeometry.Algebra.h3_off₁₂ 0 := by
      apply InfoGeometry.Algebra.H3Zorn.ext_h3 <;>
        (simp only [InfoGeometry.Algebra.candidateJordanMul,
          InfoGeometry.Algebra.H3Zorn.T, InfoGeometry.Algebra.H3Zorn.U,
          InfoGeometry.Algebra.H3Zorn.crossProduct, InfoGeometry.Algebra.H3Zorn.adjointQuad,
          InfoGeometry.Algebra.H3Zorn.traceBilin,
          InfoGeometry.Algebra.H3Zorn.add_readback, InfoGeometry.Algebra.H3Zorn.sub_readback,
          InfoGeometry.Algebra.H3Zorn.smul_readback, InfoGeometry.Algebra.H3Zorn.one_readback,
          InfoGeometry.Algebra.h3_diag₁, InfoGeometry.Algebra.h3_off₁₂, InfoGeometry.Algebra.zorn_basis,
          InfoGeometry.Algebra.ZornVectorMatrix.add, InfoGeometry.Algebra.ZornVectorMatrix.sub,
          InfoGeometry.Algebra.ZornVectorMatrix.neg, InfoGeometry.Algebra.ZornVectorMatrix.smul,
          InfoGeometry.Algebra.ZornVectorMatrix.zero, InfoGeometry.Algebra.ZornVectorMatrix.conj,
          InfoGeometry.Algebra.ZornVectorMatrix.mul, InfoGeometry.Algebra.ZornVectorMatrix.norm,
          InfoGeometry.Algebra.ZornVectorMatrix.trace, InfoGeometry.Algebra.ZornVec3.dot,
          InfoGeometry.Algebra.ZornVec3.cross, Fin.sum_univ_three]; try norm_num)
    have hdiag_mul_off : InfoGeometry.Algebra.candidateJordanMul InfoGeometry.Algebra.h3_diag₁
        (InfoGeometry.Algebra.h3_off₁₂ 0) = (1 / 2 : ℝ) • InfoGeometry.Algebra.h3_off₁₂ 0 := by
      rw [InfoGeometry.Algebra.candidateJordanMul_comm, hoff_mul_diag]
    intro h0
    have ha := congrArg (fun X : InfoGeometry.Algebra.H3Zorn ℝ => X.a.a) h0
    dsimp [h3ZornF4DerivationLane, d_f4, InfoGeometry.Algebra.f4Basis] at ha
    change (((InfoGeometry.Algebra.candidateJordanMul InfoGeometry.Algebra.h3_diag₁
        (InfoGeometry.Algebra.candidateJordanMul (InfoGeometry.Algebra.h3_off₁₂ 0)
          InfoGeometry.Algebra.h3_diag₁) -
      InfoGeometry.Algebra.candidateJordanMul (InfoGeometry.Algebra.h3_off₁₂ 0)
        (InfoGeometry.Algebra.candidateJordanMul InfoGeometry.Algebra.h3_diag₁
          InfoGeometry.Algebra.h3_diag₁)).a.a)) = 0 at ha
    rw [hdiag_sq, hoff_mul_diag, InfoGeometry.Algebra.candidateJordanMul_smul_right,
      hdiag_mul_off] at ha
    simp only [InfoGeometry.Algebra.H3Zorn.sub_readback, InfoGeometry.Algebra.H3Zorn.smul_readback,
      InfoGeometry.Algebra.h3_off₁₂, InfoGeometry.Algebra.zorn_basis,
      InfoGeometry.Algebra.ZornVectorMatrix.sub, InfoGeometry.Algebra.ZornVectorMatrix.neg,
      InfoGeometry.Algebra.ZornVectorMatrix.smul] at ha
    norm_num at ha
  exact ⟨hzvm, hnc, hjord, hf4⟩

/-- `T1-F8-04`: Nonzero `IsSquareZeroRingDifferential` and `{differentialPlus, differentialMinus}` inner closure. -/
theorem t1_f8_04_squareZeroAndPeirceSuperanticommutator :
    let N_mod2 : Matrix (Fin 2) (Fin 2) (ZMod 2) := !![0, 1; 0, 0]
    let d_sq0 : Matrix (Fin 2) (Fin 2) (ZMod 2) →+ Matrix (Fin 2) (Fin 2) (ZMod 2) :=
      { toFun := fun X => N_mod2 * X - X * N_mod2
        map_zero' := by simp
        map_add' := fun _ _ => by noncomm_ring }
    have hd_sq0 : InfoGeometry.OperatorAlgebra.PeirceGradedSuperderivations.IsSquareZeroRingDifferential d_sq0 := by
      refine ⟨fun X Y => ?_, fun X => ?_⟩
      · change N_mod2 * (X * Y) - (X * Y) * N_mod2 =
          (N_mod2 * X - X * N_mod2) * Y + X * (N_mod2 * Y - Y * N_mod2)
        noncomm_ring
      · have hN2 : N_mod2 * N_mod2 = 0 := by
          ext i j; fin_cases i <;> fin_cases j <;> decide
        change N_mod2 * (N_mod2 * X - X * N_mod2) - (N_mod2 * X - X * N_mod2) * N_mod2 = 0
        have h1 : N_mod2 * (N_mod2 * X - X * N_mod2) - (N_mod2 * X - X * N_mod2) * N_mod2 =
            (N_mod2 * N_mod2) * X - ((2 : ZMod 2) • (N_mod2 * X * N_mod2)) + X * (N_mod2 * N_mod2) := by
          rw [two_smul]
          noncomm_ring
        rw [h1, hN2, zero_mul, mul_zero]
        have h20 : (2 : ZMod 2) = 0 := by decide
        simp [h20]
    let P3 : FiniteOperatorAlgebra 3 := matrixOp !![(1 : ℂ), 0, 0; 0, 1, 0; 0, 0, 0]
    have hP3 : P3 * P3 = P3 := by
      apply matrixOfOp_injective
      rw [matrixOfOp_mul_eq, show matrixOfOp P3 = !![(1 : ℂ), 0, 0; 0, 1, 0; 0, 0, 0] from matrixOfOp_matrixOp _]
      ext i j; fin_cases i <;> fin_cases j <;>
        { simp only [Matrix.mul_apply, Fin.sum_univ_three, Matrix.of_apply,
            Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
          norm_num }
    let A3 : FiniteOperatorAlgebra 3 := matrixOp !![(0 : ℂ), 0, 1; 0, 0, 0; 0, 0, 0]
    let C3 : FiniteOperatorAlgebra 3 := matrixOp !![(0 : ℂ), 0, 0; 0, 0, 0; 1, 0, 0]
    let X3 : FiniteOperatorAlgebra 3 := matrixOp !![(0 : ℂ), 1, 0; 1, 0, 0; 0, 0, 0]
    let d_anti := superAnticommLinearToDerivations (PureNonCommutativeOperatorSpine.invS_sq hP3)
      (differentialPlusLinear_isOdd (R := ℝ) hP3 A3)
      (differentialMinusLinear_isOdd (R := ℝ) hP3 C3)
    (squareZeroRingDifferentialToDerivations d_sq0 hd_sq0 :
        Module.End ℤ (Matrix (Fin 2) (Fin 2) (ZMod 2))) !![0, 0; 1, 0] ≠ 0 ∧
      Function.Injective (fun d : { d : Matrix (Fin 2) (Fin 2) (ZMod 2) →+
          Matrix (Fin 2) (Fin 2) (ZMod 2) //
          InfoGeometry.OperatorAlgebra.PeirceGradedSuperderivations.IsSquareZeroRingDifferential d } =>
        squareZeroRingDifferentialToDerivations d.1 d.2) ∧
      (d_anti : Module.End ℝ (FiniteOperatorAlgebra 3)) X3 =
        PureNonCommutativeOperatorSpine.genV P3 A3 C3 * X3 -
          X3 * PureNonCommutativeOperatorSpine.genV P3 A3 C3 ∧
      (d_anti : Module.End ℝ (FiniteOperatorAlgebra 3)) X3 ≠ 0 := by
  intro N_mod2 d_sq0 hd_sq0 P3 hP3 A3 C3 X3 d_anti
  have hsq_ne : (squareZeroRingDifferentialToDerivations d_sq0 hd_sq0 :
      Module.End ℤ (Matrix (Fin 2) (Fin 2) (ZMod 2))) !![0, 0; 1, 0] ≠ 0 := by
    intro h0
    have hm := congrArg (fun M : Matrix (Fin 2) (Fin 2) (ZMod 2) => M 0 0) h0
    revert hm; decide
  have hanti_eq : (d_anti : Module.End ℝ (FiniteOperatorAlgebra 3)) X3 =
      PureNonCommutativeOperatorSpine.genV P3 A3 C3 * X3 -
        X3 * PureNonCommutativeOperatorSpine.genV P3 A3 C3 := by
    change InfoGeometry.OperatorAlgebra.PeirceGradedSuperderivations.differentialPlus P3 A3
        (InfoGeometry.OperatorAlgebra.PeirceGradedSuperderivations.differentialMinus P3 C3 X3) +
      InfoGeometry.OperatorAlgebra.PeirceGradedSuperderivations.differentialMinus P3 C3
        (InfoGeometry.OperatorAlgebra.PeirceGradedSuperderivations.differentialPlus P3 A3 X3) = _
    simpa [PureNonCommutativeOperatorSpine.comm] using
      InfoGeometry.OperatorAlgebra.PeirceGradedSuperderivations.differentialPlus_differentialMinus_pair
        A3 C3 X3 hP3
  have hanti_ne : (d_anti : Module.End ℝ (FiniteOperatorAlgebra 3)) X3 ≠ 0 := by
    rw [hanti_eq]
    have hV : matrixOfOp (PureNonCommutativeOperatorSpine.genV P3 A3 C3) =
        !![(1 : ℂ), 0, 0; 0, 0, 0; 0, 0, 1] := by
      dsimp [PureNonCommutativeOperatorSpine.genV, PureNonCommutativeOperatorSpine.anticomm,
        PureNonCommutativeOperatorSpine.conePlus, PureNonCommutativeOperatorSpine.coneMinus]
      simp only [matrixOfOp_add, matrixOfOp_mul_eq, matrixOfOp_sub_eq, matrixOfOp_one_eq]
      rw [show matrixOfOp P3 = !![(1 : ℂ), 0, 0; 0, 1, 0; 0, 0, 0] from matrixOfOp_matrixOp _,
        show matrixOfOp A3 = !![(0 : ℂ), 0, 1; 0, 0, 0; 0, 0, 0] from matrixOfOp_matrixOp _,
        show matrixOfOp C3 = !![(0 : ℂ), 0, 0; 0, 0, 0; 1, 0, 0] from matrixOfOp_matrixOp _]
      ext i j
      simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.sub_apply, Matrix.one_apply,
        Fin.sum_univ_three]
      fin_cases i <;> fin_cases j <;> (simp; try norm_num)
    intro h0
    have hm := congrArg (fun Z : FiniteOperatorAlgebra 3 => matrixOfOp Z 0 1) h0
    rw [matrixOfOp_sub_eq, matrixOfOp_mul_eq, matrixOfOp_mul_eq, hV,
      show matrixOfOp X3 = !![(0 : ℂ), 1, 0; 1, 0, 0; 0, 0, 0] from matrixOfOp_matrixOp _,
      matrixOfOp_zero] at hm
    norm_num [Matrix.mul_apply, Fin.sum_univ_three] at hm
  exact ⟨hsq_ne, squareZeroRingDifferentialToDerivations_injective, hanti_eq, hanti_ne⟩

/-- `T1-F8-05`: Degree-`0` `BraidedDerivation` embeds unconditionally into `derivations`, lifts to `DerivationLieLane`, and evaluates in `OnsagerFormPairing`. -/
theorem t1_f8_05_braidedDegreeZeroEmbedding :
    let B := zmod2SignBicharacter ℝ
    let D_even : InfoGeometry.Canonical.BraidedDerivation.BraidedDerivation (ZMod 2) ℝ Mat2R B :=
      { toFun := fun X => K1_real * X - X * K1_real
        deg := 0
        map_add := fun _ _ => by noncomm_ring
        map_smul := fun r X => by
          change K1_real * (r • X) - (r • X) * K1_real = r • (K1_real * X - X * K1_real)
          rw [mul_smul_comm, smul_mul_assoc, smul_sub]
        leibniz_homogeneous := fun a b => by
          rw [bicharacter_zero_right, Units.val_one, one_smul]
          change K1_real * (a.val * b) - (a.val * b) * K1_real =
            (K1_real * a.val - a.val * K1_real) * b + a.val * (K1_real * b - b * K1_real)
          noncomm_ring }
    let hL : NonAssocDerivation.IsLeibniz ℝ Mat2R (braidedDerivationToLinearMap D_even) := by
      intro x y
      simpa [braidedDerivationToLinearMap, B, D_even, bicharacter_zero_right] using
        D_even.leibniz_homogeneous ⟨x, 0⟩ y
    let d_br : (gradedBraidedDerivationLieLane ℝ Mat2R).L := braidedDerivationToDerivations D_even hL
    let S_mat : OnsagerCasimirSystem Mat2R :=
      { dissipative :=
          { toFun := fun X =>
              { toFun := fun Y => Matrix.trace (star X * Y)
                map_add' := fun Y Z => by rw [Matrix.mul_add, Matrix.trace_add]
                map_smul' := fun r Y => by simp }
            map_add' := fun X Y => by ext Z; simp [Matrix.add_mul, Matrix.trace_add]
            map_smul' := fun r X => by ext Z; simp }
        reversible := 0
        dissipative_symm := fun X Y => by
          change Matrix.trace (star X * Y) = Matrix.trace (star Y * X)
          simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.star_apply,
            star_trivial, Fin.sum_univ_two]
          ring
        reversible_skew := fun _ _ => by simp
        dissipative_nonneg := fun X => by
          change 0 ≤ Matrix.trace (star X * X)
          simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.star_apply,
            star_trivial, Fin.sum_univ_two]
          nlinarith [sq_nonneg (X 0 0), sq_nonneg (X 1 0), sq_nonneg (X 0 1), sq_nonneg (X 1 1)] }
    let P_mat : ParityOnsagerSystem Mat2R :=
      { toOnsagerCasimirSystem := S_mat
        T := ⟨LinearMap.id, fun _ => rfl⟩
        dissipative_T_even := fun _ _ => rfl
        reversible_T_odd := fun X Y => by simp [S_mat] }
    let PP := ParityOnsagerFormPairing.ofValueParity P_mat ![d_br]
    let ω : DerivationOperatorForm (gradedBraidedDerivationLieLane ℝ Mat2R) 1 :=
      oneFormAlternatingLinearEquiv (gradedBraidedDerivationLieLane ℝ Mat2R)
        (exteriorDerivativeZero (gradedBraidedDerivationLieLane ℝ Mat2R) K2_real)
    (gradedBraidedDerivationLieLane ℝ Mat2R).operatorAction d_br K2_real ≠ 0 ∧
      0 < PP.dissipative ω ω ∧
      PP.totalGenerator (PP.T.op ω) (PP.T.op ω) = PP.totalGenerator ω ω := by
  intro B D_even hL d_br S_mat P_mat PP ω
  have hne : (gradedBraidedDerivationLieLane ℝ Mat2R).operatorAction d_br K2_real ≠ 0 := by
    intro h0
    have hm := congrArg (fun M : Mat2R => M 0 1) h0
    change (K1_real * K2_real - K2_real * K1_real) 0 1 = 0 at hm
    norm_num [K1_real, K2_real, Matrix.mul_apply, Fin.sum_univ_two] at hm
  have hpos : 0 < PP.dissipative ω ω := by
    change 0 < Matrix.trace (star (K1_real * K2_real - K2_real * K1_real) *
      (K1_real * K2_real - K2_real * K1_real))
    norm_num [K1_real, K2_real, Matrix.trace, Matrix.diag, Matrix.mul_apply,
      Matrix.star_apply, Fin.sum_univ_two]
  exact ⟨hne, hpos, gradedBraidedAlgebra_onsager_reciprocity PP ω ω⟩

/-- `T2-F8-01`: Typeclass diamond & orphan-instance guard across Zorn/Octonion/CrossProd carriers. -/
theorem t2_f8_01_diamondAndInstanceLeakGuard :
    (inferInstance : NonUnitalNonAssocRing (InfoGeometry.Algebra.ZornVectorMatrix ℝ)) =
        (inferInstance : NonUnitalNonAssocRing (InfoGeometry.Algebra.ZornVectorMatrix ℝ)) ∧
      (inferInstance : NonUnitalNonAssocRing (InfoGeometry.Algebra.H3Zorn ℝ)) =
        (inferInstance : NonUnitalNonAssocRing (InfoGeometry.Algebra.H3Zorn ℝ)) ∧
      (inferInstance : NonUnitalNonAssocRing (InfoGeometry.Canonical.ZornMatrix ℝ)) =
        (inferInstance : NonUnitalNonAssocRing (InfoGeometry.Canonical.ZornMatrix ℝ)) := by
  fail_if_success exact (inferInstance : IsScalarTower ℝ (InfoGeometry.Canonical.ZornMatrix ℝ)
    (InfoGeometry.Canonical.ZornMatrix ℝ))
  fail_if_success exact (inferInstance : SMulCommClass ℝ (InfoGeometry.Canonical.ZornMatrix ℝ)
    (InfoGeometry.Canonical.ZornMatrix ℝ))
  fail_if_success exact (inferInstance : NonUnitalNonAssocRing (Fin 7 → ℝ))
  fail_if_success exact (inferInstance : NonUnitalNonAssocRing
    InfoGeometry.Algebra.SplitOctonionZorn.SplitOctonion)
  fail_if_success exact (inferInstance : NonUnitalNonAssocRing
    (InfoGeometry.Physics.NoncommutativeZornBdGDerivations.NCZorn ℝ))
  fail_if_success exact (inferInstance : NonUnitalNonAssocRing
    (InfoGeometry.Canonical.OperatorCoefficientZornExtension.OpZorn (FiniteHilbertSpace 2)))
  exact ⟨rfl, rfl, rfl⟩

/-- `T2-F8-02`: `squareZero_differential_not_Peirce_commutator_on_nonzero_odd` no-go theorem on nonzero Peirce-odd element. -/
theorem t2_f8_02_squareZeroPeirceNoGo
    (d : FiniteOperatorAlgebra 2 →+ FiniteOperatorAlgebra 2)
    (hd : InfoGeometry.OperatorAlgebra.PeirceGradedSuperderivations.IsSquareZeroRingDifferential d)
    (hdP : d P_d63.1 = 0) :
    let X_odd := PureNonCommutativeOperatorSpine.conePlus P_d63.1 B_tilt
    X_odd ≠ 0 ∧ d X_odd ≠ P_d63.1 * X_odd - X_odd * P_d63.1 := by
  intro X_odd
  have hne : X_odd ≠ 0 := by
    intro h0
    have hm := congrArg (fun Z : FiniteOperatorAlgebra 2 => matrixOfOp Z 0 0) h0
    dsimp [X_odd, PureNonCommutativeOperatorSpine.conePlus] at hm
    rw [matrixOfOp_mul_eq, matrixOfOp_mul_eq, matrixOfOp_sub_eq, matrixOfOp_one_eq,
      show matrixOfOp P_d63.1 = d63TiltedProjection from matrixOfOp_matrixOp _,
      B_tilt, matrixOfOp_matrixOp, matrixOfOp_zero] at hm
    norm_num [d63TiltedProjection, tiltedMatrix, Matrix.mul_apply, Fin.sum_univ_two] at hm
  refine ⟨hne, fun hcompat => hne ?_⟩
  exact InfoGeometry.OperatorAlgebra.PeirceGradedSuperderivations.squareZero_differential_not_Peirce_commutator_on_nonzero_odd
    hd P_d63.property hdP
    (by
      dsimp [X_odd, PureNonCommutativeOperatorSpine.conePlus]
      have h1P : (1 - P_d63.1) * P_d63.1 = 0 := by
        rw [sub_mul, one_mul, P_d63.property, sub_self]
      calc P_d63.1 * (P_d63.1 * B_tilt * (1 - P_d63.1)) * P_d63.1
          = (P_d63.1 * P_d63.1 * B_tilt) * ((1 - P_d63.1) * P_d63.1) := by noncomm_ring
        _ = 0 := by rw [h1P, mul_zero])
    (by
      dsimp [X_odd, PureNonCommutativeOperatorSpine.conePlus]
      have h1P : (1 - P_d63.1) * P_d63.1 = 0 := by
        rw [sub_mul, one_mul, P_d63.property, sub_self]
      calc (1 - P_d63.1) * (P_d63.1 * B_tilt * (1 - P_d63.1)) * (1 - P_d63.1)
          = ((1 - P_d63.1) * P_d63.1) * (B_tilt * (1 - P_d63.1) * (1 - P_d63.1)) := by noncomm_ring
        _ = 0 := by rw [h1P, zero_mul])
    hcompat

private def P3_mat_e2e : Matrix (Fin 3) (Fin 3) ℂ := !![(1 : ℂ), 0, 0; 0, 1, 0; 0, 0, 0]
private def P3_op_e2e : FiniteOperatorAlgebra 3 := matrixOp P3_mat_e2e

private lemma P3_op_e2e_idem : P3_op_e2e * P3_op_e2e = P3_op_e2e := by
  apply matrixOfOp_injective
  rw [matrixOfOp_mul_eq, show matrixOfOp P3_op_e2e = P3_mat_e2e from matrixOfOp_matrixOp _]
  ext i j; fin_cases i <;> fin_cases j <;>
    { simp only [P3_mat_e2e, Matrix.mul_apply, Fin.sum_univ_three, Matrix.of_apply,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
      norm_num }

private def P3_e2e : PeirceCut 3 := ⟨P3_op_e2e, P3_op_e2e_idem⟩
private def A3_e2e : FiniteOperatorAlgebra 3 := matrixOp !![(0 : ℂ), 0, 1; 0, 0, 0; 0, 0, 0]
private def C3_e2e : FiniteOperatorAlgebra 3 := matrixOp !![(0 : ℂ), 0, 0; 0, 0, 0; 1, 0, 0]
private def X3_e2e : FiniteOperatorAlgebra 3 := matrixOp !![(0 : ℂ), 1, 0; 1, 0, 0; 0, 0, 0]
private def Y3_e2e : FiniteOperatorAlgebra 3 := matrixOp !![(1 : ℂ), 1, 0; 1, 0, 0; 0, 0, 0]

/-- `T2-F8-03`: Odd superderivation fails ungraded Leibniz on `X_odd`, while `3×3` `{differentialPlus, differentialMinus}` satisfies ordinary Leibniz with nonzero action (`(d_anti : Module.End ℝ _) X3 ≠ 0`). -/
theorem t2_f8_03_oddSuperderivationVsOrdinaryLeibniz :
    let S := PureNonCommutativeOperatorSpine.invS P_d63.1
    let N := PureNonCommutativeOperatorSpine.conePlus P_d63.1 B_tilt
    let X_odd := PureNonCommutativeOperatorSpine.conePlus P_d63.1 B_tilt
    let Y := B_tilt
    let A3 := A3_e2e
    let C3 := C3_e2e
    let X3 := X3_e2e
    let Y3 := Y3_e2e
    let d_anti : NonAssocDerivation.derivations ℝ (FiniteOperatorAlgebra 3) :=
      superAnticommLinearToDerivations (PureNonCommutativeOperatorSpine.invS_sq P3_e2e.property)
        (differentialPlusLinear_isOdd (R := ℝ) P3_e2e.property A3)
        (differentialMinusLinear_isOdd (R := ℝ) P3_e2e.property C3)
    InfoGeometry.OperatorAlgebra.PeirceGradedSuperderivations.oddDiff S N (X_odd * Y) ≠
        InfoGeometry.OperatorAlgebra.PeirceGradedSuperderivations.oddDiff S N X_odd * Y +
          X_odd * InfoGeometry.OperatorAlgebra.PeirceGradedSuperderivations.oddDiff S N Y ∧
      (d_anti : Module.End ℝ (FiniteOperatorAlgebra 3)) (X3 * Y3) =
        (d_anti : Module.End ℝ (FiniteOperatorAlgebra 3)) X3 * Y3 +
          X3 * (d_anti : Module.End ℝ (FiniteOperatorAlgebra 3)) Y3 ∧
      (d_anti : Module.End ℝ (FiniteOperatorAlgebra 3)) X3 ≠ 0 := by
  intro S N X_odd Y A3 C3 X3 Y3 d_anti
  refine ⟨?_, ?_, ?_⟩
  · rw [InfoGeometry.OperatorAlgebra.PeirceGradedSuperderivations.oddDiff_graded_leibniz
      (PureNonCommutativeOperatorSpine.invS_sq P_d63.property) X_odd Y]
    have htw : InfoGeometry.OperatorAlgebra.PeirceGradedSuperderivations.twist S X_odd = -X_odd :=
      InfoGeometry.OperatorAlgebra.PeirceGradedSuperderivations.twist_odd
        (PureNonCommutativeOperatorSpine.invS_sq P_d63.property)
        (by
          rw [PureNonCommutativeOperatorSpine.invS_mul_conePlus P_d63.property B_tilt,
            PureNonCommutativeOperatorSpine.conePlus_mul_invS P_d63.property B_tilt, neg_neg])
    rw [htw]
    change InfoGeometry.OperatorAlgebra.PeirceGradedSuperderivations.oddDiff S N X_odd * Y +
        (-X_odd) * InfoGeometry.OperatorAlgebra.PeirceGradedSuperderivations.oddDiff S N Y ≠ _
    rw [neg_mul X_odd, ← sub_eq_add_neg]
    intro heq
    have hzero : X_odd * InfoGeometry.OperatorAlgebra.PeirceGradedSuperderivations.oddDiff S N Y +
        X_odd * InfoGeometry.OperatorAlgebra.PeirceGradedSuperderivations.oddDiff S N Y = 0 := by
      rw [show X_odd * InfoGeometry.OperatorAlgebra.PeirceGradedSuperderivations.oddDiff S N Y +
          X_odd * InfoGeometry.OperatorAlgebra.PeirceGradedSuperderivations.oddDiff S N Y =
        (InfoGeometry.OperatorAlgebra.PeirceGradedSuperderivations.oddDiff S N X_odd * Y +
          X_odd * InfoGeometry.OperatorAlgebra.PeirceGradedSuperderivations.oddDiff S N Y) -
        (InfoGeometry.OperatorAlgebra.PeirceGradedSuperderivations.oddDiff S N X_odd * Y -
          X_odd * InfoGeometry.OperatorAlgebra.PeirceGradedSuperderivations.oddDiff S N Y) by abel,
        ← heq, sub_self]
    have hX : matrixOfOp X_odd = !![(1 / 4 : ℂ), -(1 / 4); 1 / 4, -(1 / 4)] := by
      dsimp [X_odd, PureNonCommutativeOperatorSpine.conePlus]
      rw [matrixOfOp_mul_eq, matrixOfOp_mul_eq, matrixOfOp_sub_eq, matrixOfOp_one_eq,
        show matrixOfOp P_d63.1 = d63TiltedProjection from matrixOfOp_matrixOp _,
        matrixOfOp_B_tilt]
      ext i j; fin_cases i <;> fin_cases j <;>
        norm_num [d63TiltedProjection, tiltedMatrix, Matrix.mul_apply, Fin.sum_univ_two]
    have hS : matrixOfOp S = (swapMatrix : Matrix (Fin 2) (Fin 2) ℂ) := by
      dsimp [S, PureNonCommutativeOperatorSpine.invS]
      rw [matrixOfOp_sub_eq, matrixOfOp_sub_eq, matrixOfOp_one_eq,
        show matrixOfOp P_d63.1 = d63TiltedProjection from matrixOfOp_matrixOp _]
      ext i j; fin_cases i <;> fin_cases j <;>
        norm_num [d63TiltedProjection, swapMatrix]
    have hdiffY : matrixOfOp (InfoGeometry.OperatorAlgebra.PeirceGradedSuperderivations.oddDiff S N Y) =
        !![-(1 / 4 : ℂ), 1 / 2; -(1 / 2), 3 / 4] := by
      dsimp [InfoGeometry.OperatorAlgebra.PeirceGradedSuperderivations.oddDiff,
        InfoGeometry.OperatorAlgebra.PeirceGradedSuperderivations.twist]
      rw [matrixOfOp_sub_eq, matrixOfOp_mul_eq, matrixOfOp_mul_eq, matrixOfOp_mul_eq,
        matrixOfOp_mul_eq, show N = X_odd from rfl, hX, hS,
        show Y = B_tilt from rfl, matrixOfOp_B_tilt]
      ext i j; fin_cases i <;> fin_cases j <;>
        norm_num [swapMatrix, tiltedMatrix, Matrix.mul_apply, Fin.sum_univ_two]
    have hm := congrArg (fun Z : FiniteOperatorAlgebra 2 => matrixOfOp Z 0 0) hzero
    rw [matrixOfOp_add, matrixOfOp_mul_eq, hX, hdiffY, matrixOfOp_zero] at hm
    simp only [Matrix.add_apply, Matrix.zero_apply] at hm
    norm_num [Matrix.mul_apply, Fin.sum_univ_two] at hm
  · have hleib : ∀ (d : NonAssocDerivation.derivations ℝ (FiniteOperatorAlgebra 3))
        (x y : FiniteOperatorAlgebra 3),
        (d : Module.End ℝ (FiniteOperatorAlgebra 3)) (x * y) =
          (d : Module.End ℝ (FiniteOperatorAlgebra 3)) x * y +
            x * (d : Module.End ℝ (FiniteOperatorAlgebra 3)) y :=
      fun d x y => derivations_leibniz ℝ (FiniteOperatorAlgebra 3) d x y
    exact hleib d_anti X3 Y3
  · let P3 := P3_e2e.1
    have hd_eq : (d_anti : Module.End ℝ (FiniteOperatorAlgebra 3)) X3 =
        PureNonCommutativeOperatorSpine.genV P3 A3 C3 * X3 -
          X3 * PureNonCommutativeOperatorSpine.genV P3 A3 C3 := by
      have hgen : ∀ (P : PeirceCut 3) (A C X : FiniteOperatorAlgebra 3),
          (superAnticommLinearToDerivations (PureNonCommutativeOperatorSpine.invS_sq P.property)
            (differentialPlusLinear_isOdd (R := ℝ) P.property A)
            (differentialMinusLinear_isOdd (R := ℝ) P.property C) :
            Module.End ℝ (FiniteOperatorAlgebra 3)) X =
          PureNonCommutativeOperatorSpine.genV P.1 A C * X -
            X * PureNonCommutativeOperatorSpine.genV P.1 A C := fun P A C X => by
        change InfoGeometry.OperatorAlgebra.PeirceGradedSuperderivations.differentialPlus P.1 A
            (InfoGeometry.OperatorAlgebra.PeirceGradedSuperderivations.differentialMinus P.1 C X) +
          InfoGeometry.OperatorAlgebra.PeirceGradedSuperderivations.differentialMinus P.1 C
            (InfoGeometry.OperatorAlgebra.PeirceGradedSuperderivations.differentialPlus P.1 A X) = _
        simpa [PureNonCommutativeOperatorSpine.comm] using
          InfoGeometry.OperatorAlgebra.PeirceGradedSuperderivations.differentialPlus_differentialMinus_pair
            A C X P.property
      exact hgen P3_e2e A3 C3 X3
    have hgenV : matrixOfOp (PureNonCommutativeOperatorSpine.genV P3 A3 C3) =
        !![(1 : ℂ), 0, 0; 0, 0, 0; 0, 0, 1] := by
      dsimp [PureNonCommutativeOperatorSpine.genV, PureNonCommutativeOperatorSpine.anticomm,
        PureNonCommutativeOperatorSpine.conePlus, PureNonCommutativeOperatorSpine.coneMinus]
      simp only [matrixOfOp_add, matrixOfOp_mul_eq, matrixOfOp_sub_eq, matrixOfOp_one_eq]
      rw [show matrixOfOp P3 = P3_mat_e2e from matrixOfOp_matrixOp _,
        show matrixOfOp A3 = !![(0 : ℂ), 0, 1; 0, 0, 0; 0, 0, 0] from matrixOfOp_matrixOp _,
        show matrixOfOp C3 = !![(0 : ℂ), 0, 0; 0, 0, 0; 1, 0, 0] from matrixOfOp_matrixOp _]
      ext i j
      simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.sub_apply, Matrix.one_apply,
        Fin.sum_univ_three]
      fin_cases i <;> fin_cases j <;> (simp [P3_mat_e2e]; try norm_num)
    intro h0
    have hm := congrArg (fun M : FiniteOperatorAlgebra 3 => matrixOfOp M 0 1) (hd_eq.symm.trans h0)
    rw [matrixOfOp_sub_eq, matrixOfOp_mul_eq, matrixOfOp_mul_eq, hgenV,
      show matrixOfOp X3 = !![(0 : ℂ), 1, 0; 1, 0, 0; 0, 0, 0] from matrixOfOp_matrixOp _,
      matrixOfOp_zero] at hm
    norm_num [Matrix.mul_apply, Fin.sum_univ_three] at hm

/-- `T2-F8-04`: `GradedBraidedDerivation` degree-`1` fails ungraded Leibniz on odd `X_odd`, whereas degree-`0` `BraidedDerivation` obeys ungraded Leibniz everywhere. -/
theorem t2_f8_04_braidedDegree1VsDegree0Boundary :
    let B := zmod2SignBicharacter ℝ
    let hS := PureNonCommutativeOperatorSpine.invS_sq P_d63.property
    let d_odd := oddTwistSuperderivationToGradedBraided hS
      (differentialPlusLinear ℝ P_d63.1 B_tilt)
      (differentialPlusLinear_isOdd (R := ℝ) P_d63.property B_tilt)
    let X_odd := PureNonCommutativeOperatorSpine.conePlus P_d63.1 B_tilt
    let Y := B_tilt
    let D_even : InfoGeometry.Canonical.BraidedDerivation.BraidedDerivation (ZMod 2) ℝ Mat2R B :=
      { toFun := fun X => K1_real * X - X * K1_real
        deg := 0
        map_add := fun _ _ => by noncomm_ring
        map_smul := fun r X => by
          change K1_real * (r • X) - (r • X) * K1_real = r • (K1_real * X - X * K1_real)
          rw [mul_smul_comm, smul_mul_assoc, smul_sub]
        leibniz_homogeneous := fun a b => by
          rw [bicharacter_zero_right, Units.val_one, one_smul]
          change K1_real * (a.val * b) - (a.val * b) * K1_real =
            (K1_real * a.val - a.val * K1_real) * b + a.val * (K1_real * b - b * K1_real)
          noncomm_ring }
    d_odd.deg = 1 ∧
      d_odd (X_odd * Y) ≠ d_odd X_odd * Y + X_odd * d_odd Y ∧
      ∀ a b : Mat2R, D_even (a * b) = D_even a * b + a * D_even b := by
  intro B hS d_odd X_odd Y D_even
  refine ⟨oddTwistSuperderivationToGradedBraided_deg hS _ _,
    t2_f8_03_oddSuperderivationVsOrdinaryLeibniz.1,
    fun a b => by simpa [B, D_even, bicharacter_zero_right] using D_even.leibniz_homogeneous ⟨a, 0⟩ b⟩

/-- `T2-F8-05`: Non-associative associator non-vanishing alongside Leibniz closure on `ZornVectorMatrix ℝ`. -/
theorem t2_f8_05_nonAssociativityWithLeibniz :
    let X0 : InfoGeometry.Algebra.ZornVectorMatrix ℝ := InfoGeometry.Algebra.ZornVectorMatrix.U 0
    let X1 : InfoGeometry.Algebra.ZornVectorMatrix ℝ := InfoGeometry.Algebra.ZornVectorMatrix.U 1
    let X2 : InfoGeometry.Algebra.ZornVectorMatrix ℝ := InfoGeometry.Algebra.ZornVectorMatrix.U 2
    let d_zvm : InfoGeometry.Algebra.ZornVectorMatrix.Derivation (R := ℝ) :=
      { toFun := fun X => ⟨0, ![-(X.v 1), X.v 0, 0], ![-(X.w 1), X.w 0, 0], 0⟩
        map_add' := fun X Y => by
          ext i <;> simp [InfoGeometry.Algebra.ZornVectorMatrix.add]
          · fin_cases i <;> (simp; try ring)
          · fin_cases i <;> (simp; try ring)
        map_smul' := fun r X => by
          ext i <;> simp [InfoGeometry.Algebra.ZornVectorMatrix.smul]
          · fin_cases i <;> simp
          · fin_cases i <;> simp
        map_mul' := fun X Y => by
          ext i
          · simp [InfoGeometry.Algebra.ZornVectorMatrix.mul,
              InfoGeometry.Algebra.ZornVectorMatrix.add,
              InfoGeometry.Algebra.ZornVec3.dot, Fin.sum_univ_three]
          · fin_cases i <;>
              (simp [InfoGeometry.Algebra.ZornVectorMatrix.mul,
                InfoGeometry.Algebra.ZornVectorMatrix.add,
                InfoGeometry.Algebra.ZornVec3.cross]; try ring)
          · fin_cases i <;>
              (simp [InfoGeometry.Algebra.ZornVectorMatrix.mul,
                InfoGeometry.Algebra.ZornVectorMatrix.add,
                InfoGeometry.Algebra.ZornVec3.cross]; try ring)
          · simp [InfoGeometry.Algebra.ZornVectorMatrix.mul,
              InfoGeometry.Algebra.ZornVectorMatrix.add,
              InfoGeometry.Algebra.ZornVec3.dot, Fin.sum_univ_three] }
    let d_der := zornVectorMatrixDerivationEquivDerivations ℝ d_zvm
    (X0 * X1) * X2 ≠ X0 * (X1 * X2) ∧
      (d_der : Module.End ℝ _) (X0 * X1) = (d_der : Module.End ℝ _) X0 * X1 + X0 * (d_der : Module.End ℝ _) X1 :=
  ⟨InfoGeometry.Algebra.ZornVectorMatrix.nonassociative_witness (R := ℝ),
    (zornVectorMatrixDerivationEquivDerivations ℝ _).property _ _⟩

end GapD_Tests

/-! ## Section 4: Tier 3 — Cross-Feature Pairwise Combinations (`T3-AB`..`T3-AC`) -/

section Tier3_Tests

attribute [local instance 100] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

/-- `T3-AB-01`: Peirce `cutDerivation P_d63` embedded into `finiteGibbsCEParityOnsagerSystem` (`a := B_tilt`, nonzero dissipation, nonzero reversibility & reciprocity). -/
theorem t3_ab_01_peirceCutCeBkmParity :
    let d_cut : Carrier 2 := FrechetBridge.toRealDerivation (cutDerivation P_d63)
    let Q := tiltOp2 + (2 : ℝ) • A_swap
    have hQ : IsSelfAdjoint Q :=
      isSelfAdjoint_add_op tiltOp2_isSelfAdjoint (isSelfAdjoint_real_smul 2 A_swap hA_swap_sa)
    let PS := finiteGibbsCEParityOnsagerSystem H_d63 hH_d63_sa hZ_d63_pos B_tilt Q
      hB_tilt_sa hQ
    let y := innerDerivation (matrixOp !![0, 0; 1, 0])
    ((peirceCutDerivationLieLane 2).operatorAction (peirceCutGenerator P_d63) B_tilt =
        finiteCEOperatorForm 2 B_tilt d_cut) ∧
      0 < PS.dissipative d_cut d_cut ∧
      PS.dissipative d_cut d_cut ≠ 0 ∧
      PS.reversible d_cut y =
        ceCurvatureBKMProbeForm (faithfulGibbsDensity H_d63 hH_d63_sa hZ_d63_pos)
          (continuous_faithfulGibbsDensity_rpow H_d63 hH_d63_sa hZ_d63_pos) B_tilt Q d_cut y ∧
      PS.reversible d_cut y ≠ 0 ∧
      PS.totalGenerator (PS.T.op d_cut) (PS.T.op y) = PS.totalGenerator y d_cut := by
  intro d_cut Q hQ PS y
  have hbridge := gapAB_peirceCut_ceBKM_parity_bridge P_d63 H_d63 B_tilt Q
    hH_d63_sa hZ_d63_pos hB_tilt_sa hQ y
  let D := faithfulGibbsDensity H_d63 hH_d63_sa hZ_d63_pos
  let hpow := continuous_faithfulGibbsDensity_rpow H_d63 hH_d63_sa hZ_d63_pos
  have hdiss_pos : 0 < PS.dissipative d_cut d_cut := by
    rw [hbridge.2.1, centeredCEBKMForm_apply, centeredBKMRealCovariance_self]
    rw [D.bkmRealBilinForm_apply]
    apply D.kuboMoriPairing_self_re_pos _ hpow
    intro h0
    have hmem := (centeredStatistic_eq_zero_iff D hpow _).mp h0
    obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp hmem
    have hm := congrArg (fun Z : GibbsOperator 2 => matrixOfOp Z 0 1) hr
    change matrixOfOp (r • (1 : GibbsOperator 2)) 0 1 =
      matrixOfOp (P_d63.1 * B_tilt - B_tilt * P_d63.1) 0 1 at hm
    rw [matrixOfOp_real_smul, matrixOfOp_one_eq, matrixOfOp_sub_eq, matrixOfOp_mul_eq,
      matrixOfOp_mul_eq, show matrixOfOp P_d63.1 = d63TiltedProjection from matrixOfOp_matrixOp _,
      B_tilt, matrixOfOp_matrixOp] at hm
    norm_num [d63TiltedProjection, tiltedMatrix, Matrix.mul_apply, Fin.sum_univ_two] at hm
  have hcomm_Q : connectionCurvature (realDerivationsLane (GibbsOperator 2))
      (exteriorDerivativeZero (realDerivationsLane (GibbsOperator 2)) B_tilt) d_cut y =
      (-1 / 2 : ℝ) • Q := by
    rw [connectionCurvature, exteriorDerivativeOne_exteriorDerivativeZero, zero_add]
    apply matrixOfOp_injective
    change matrixOfOp ((P_d63.1 * B_tilt - B_tilt * P_d63.1) *
        (matrixOp !![0, 0; 1, 0] * B_tilt - B_tilt * matrixOp !![0, 0; 1, 0]) -
      (matrixOp !![0, 0; 1, 0] * B_tilt - B_tilt * matrixOp !![0, 0; 1, 0]) *
        (P_d63.1 * B_tilt - B_tilt * P_d63.1)) =
      matrixOfOp ((-1 / 2 : ℝ) • Q)
    rw [matrixOfOp_sub_eq, matrixOfOp_mul_eq, matrixOfOp_mul_eq,
      matrixOfOp_sub_eq, matrixOfOp_mul_eq, matrixOfOp_mul_eq,
      matrixOfOp_sub_eq, matrixOfOp_mul_eq, matrixOfOp_mul_eq,
      matrixOfOp_real_smul, show matrixOfOp Q = matrixOfOp tiltOp2 + (2 : ℝ) • matrixOfOp A_swap from by
        dsimp [Q]; rw [matrixOfOp_add]; exact congrArg (matrixOfOp tiltOp2 + ·) (matrixOfOp_real_smul 2 A_swap),
      show matrixOfOp P_d63.1 = d63TiltedProjection from matrixOfOp_matrixOp _,
      matrixOfOp_B_tilt, matrixOfOp_tiltOp2, matrixOfOp_A_swap, matrixOfOp_matrixOp]
    ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [d63TiltedProjection, tiltedMatrix, InfoGeometry.Physics.KleinBottleSewingExact.tilt2,
        swapMatrix, Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct]
  have hQ_ne : Q ≠ 0 := by
    intro h0
    have hm := congrArg matrixOfOp h0
    dsimp [Q] at hm
    rw [matrixOfOp_add, matrixOfOp_real_smul 2 A_swap,
      matrixOfOp_tiltOp2, matrixOfOp_A_swap, matrixOfOp_zero] at hm
    have hm00 := congrFun (congrFun hm 0) 0
    norm_num [InfoGeometry.Physics.KleinBottleSewingExact.tilt2, swapMatrix] at hm00
  have hrev_ne : PS.reversible d_cut y ≠ 0 := by
    rw [hbridge.2.2.1, ceCurvatureBKMProbeForm_apply, hcomm_Q, _root_.map_smul,
      LinearMap.smul_apply, smul_eq_mul]
    have hpos : 0 < D.bkmRealBilinForm hpow Q Q :=
      (D.bkmRealBilinForm_self_pos_iff hpow Q).mpr hQ_ne
    linarith
  exact ⟨hbridge.1, hdiss_pos, ne_of_gt hdiss_pos, hbridge.2.2.1, hrev_ne, hbridge.2.2.2.2⟩

private def P_diag_i_mat : Matrix (Fin 2) (Fin 2) ℂ :=
  !![1 / 2, Complex.I / 2; -Complex.I / 2, 1 / 2]

private def P_diag_i : PeirceCut 2 :=
  ⟨matrixOp P_diag_i_mat, by
    apply matrixOfOp_injective
    change matrixOfOp ((matrixOp P_diag_i_mat).comp (matrixOp P_diag_i_mat)) =
      matrixOfOp (matrixOp P_diag_i_mat)
    rw [matrixOfOp_comp, matrixOfOp_matrixOp]
    ext i j; fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
      simp [P_diag_i_mat, Matrix.mul_apply, Fin.sum_univ_two] <;> ring⟩

private lemma t3_ab_02_F1_eq :
    let K := peirceCutDerivationLieLane 2
    let Γ₁ := exteriorDerivativeZero K B_tilt
    let v : Fin 2 → K.L := ![peirceCutGenerator P_d63, peirceCutGenerator P_diag_i]
    matrixOfOp (ceCurvature K (oneFormAlternatingLinearEquiv K Γ₁) v) =
      !![Complex.I / 2, Complex.I; Complex.I, -Complex.I / 2] := by
  intro K Γ₁ v
  rw [ceCurvature_eq, twoCochainEquivDerivationOperatorForm_apply,
    connectionCurvature, exteriorDerivativeOne_exteriorDerivativeZero, zero_add]
  change matrixOfOp ((P_d63.1 * B_tilt - B_tilt * P_d63.1) *
      (P_diag_i.1 * B_tilt - B_tilt * P_diag_i.1) -
    (P_diag_i.1 * B_tilt - B_tilt * P_diag_i.1) *
      (P_d63.1 * B_tilt - B_tilt * P_d63.1)) = _
  rw [matrixOfOp_sub_eq, matrixOfOp_mul_eq, matrixOfOp_mul_eq,
    matrixOfOp_sub_eq, matrixOfOp_mul_eq, matrixOfOp_mul_eq,
    matrixOfOp_sub_eq, matrixOfOp_mul_eq, matrixOfOp_mul_eq,
    show matrixOfOp P_d63.1 = d63TiltedProjection from matrixOfOp_matrixOp _,
    show matrixOfOp P_diag_i.1 = P_diag_i_mat from matrixOfOp_matrixOp _,
    matrixOfOp_B_tilt]
  ext i j; fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp only [Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, d63TiltedProjection, P_diag_i_mat,
      tiltedMatrix] <;>
    norm_num

private lemma t3_ab_02_F2_eq :
    let K := peirceCutDerivationLieLane 2
    let Γ₂ := exteriorDerivativeZero K tiltOp2
    let v : Fin 2 → K.L := ![peirceCutGenerator P_d63, peirceCutGenerator P_diag_i]
    matrixOfOp (ceCurvature K (oneFormAlternatingLinearEquiv K Γ₂) v) =
      !![2 * Complex.I, 0; 0, -2 * Complex.I] := by
  intro K Γ₂ v
  rw [ceCurvature_eq, twoCochainEquivDerivationOperatorForm_apply,
    connectionCurvature, exteriorDerivativeOne_exteriorDerivativeZero, zero_add]
  change matrixOfOp ((P_d63.1 * tiltOp2 - tiltOp2 * P_d63.1) *
      (P_diag_i.1 * tiltOp2 - tiltOp2 * P_diag_i.1) -
    (P_diag_i.1 * tiltOp2 - tiltOp2 * P_diag_i.1) *
      (P_d63.1 * tiltOp2 - tiltOp2 * P_d63.1)) = _
  rw [matrixOfOp_sub_eq, matrixOfOp_mul_eq, matrixOfOp_mul_eq,
    matrixOfOp_sub_eq, matrixOfOp_mul_eq, matrixOfOp_mul_eq,
    matrixOfOp_sub_eq, matrixOfOp_mul_eq, matrixOfOp_mul_eq,
    show matrixOfOp P_d63.1 = d63TiltedProjection from matrixOfOp_matrixOp _,
    show matrixOfOp P_diag_i.1 = P_diag_i_mat from matrixOfOp_matrixOp _,
    matrixOfOp_tiltOp2]
  ext i j; fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp only [Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, d63TiltedProjection, P_diag_i_mat,
      InfoGeometry.Physics.KleinBottleSewingExact.tilt2] <;>
    norm_num

private lemma t3_ab_02_invS_mat : matrixOfOp (invS P_d63.1) = swapMatrix := by
  dsimp [invS]
  rw [matrixOfOp_sub_eq, matrixOfOp_sub_eq, matrixOfOp_one_eq,
    show matrixOfOp P_d63.1 = d63TiltedProjection from matrixOfOp_matrixOp _]
  ext i j; fin_cases i <;> fin_cases j <;> norm_num [d63TiltedProjection, swapMatrix]

private lemma t3_ab_02_P_plus_1 :
    let K := peirceCutDerivationLieLane 2
    let Γ₁ := exteriorDerivativeZero K B_tilt
    let v : Fin 2 → K.L := ![peirceCutGenerator P_d63, peirceCutGenerator P_diag_i]
    matrixOfOp ((peirceCartanOnsagerSplit P_d63).S.P_plus
      (ceCurvature K (oneFormAlternatingLinearEquiv K Γ₁) v)) =
      !![0, Complex.I; Complex.I, 0] := by
  intro K Γ₁ v
  change matrixOfOp (((2 : ℝ)⁻¹) • (ceCurvature K (oneFormAlternatingLinearEquiv K Γ₁) v +
    invS P_d63.1 * ceCurvature K (oneFormAlternatingLinearEquiv K Γ₁) v * invS P_d63.1)) = _
  rw [matrixOfOp_real_smul, matrixOfOp_add, matrixOfOp_mul_eq, matrixOfOp_mul_eq,
    t3_ab_02_F1_eq, t3_ab_02_invS_mat]
  ext i j; fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, swapMatrix, smul_eq_mul] <;>
    norm_num

private lemma t3_ab_02_P_minus_1 :
    let K := peirceCutDerivationLieLane 2
    let Γ₁ := exteriorDerivativeZero K B_tilt
    let v : Fin 2 → K.L := ![peirceCutGenerator P_d63, peirceCutGenerator P_diag_i]
    matrixOfOp ((peirceCartanOnsagerSplit P_d63).S.P_minus
      (ceCurvature K (oneFormAlternatingLinearEquiv K Γ₁) v)) =
      !![Complex.I / 2, 0; 0, -Complex.I / 2] := by
  intro K Γ₁ v
  change matrixOfOp (((2 : ℝ)⁻¹) • (ceCurvature K (oneFormAlternatingLinearEquiv K Γ₁) v -
    invS P_d63.1 * ceCurvature K (oneFormAlternatingLinearEquiv K Γ₁) v * invS P_d63.1)) = _
  rw [matrixOfOp_real_smul, matrixOfOp_sub_eq, matrixOfOp_mul_eq, matrixOfOp_mul_eq,
    t3_ab_02_F1_eq, t3_ab_02_invS_mat]
  ext i j; fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, swapMatrix, smul_eq_mul] <;>
    norm_num

private lemma t3_ab_02_P_plus_2 :
    let K := peirceCutDerivationLieLane 2
    let Γ₂ := exteriorDerivativeZero K tiltOp2
    let v : Fin 2 → K.L := ![peirceCutGenerator P_d63, peirceCutGenerator P_diag_i]
    matrixOfOp ((peirceCartanOnsagerSplit P_d63).S.P_plus
      (ceCurvature K (oneFormAlternatingLinearEquiv K Γ₂) v)) = 0 := by
  intro K Γ₂ v
  change matrixOfOp (((2 : ℝ)⁻¹) • (ceCurvature K (oneFormAlternatingLinearEquiv K Γ₂) v +
    invS P_d63.1 * ceCurvature K (oneFormAlternatingLinearEquiv K Γ₂) v * invS P_d63.1)) = 0
  rw [matrixOfOp_real_smul, matrixOfOp_add, matrixOfOp_mul_eq, matrixOfOp_mul_eq,
    t3_ab_02_F2_eq, t3_ab_02_invS_mat]
  ext i j; fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.zero_apply,
      swapMatrix, smul_eq_mul] <;>
    norm_num

private lemma t3_ab_02_P_minus_2 :
    let K := peirceCutDerivationLieLane 2
    let Γ₂ := exteriorDerivativeZero K tiltOp2
    let v : Fin 2 → K.L := ![peirceCutGenerator P_d63, peirceCutGenerator P_diag_i]
    matrixOfOp ((peirceCartanOnsagerSplit P_d63).S.P_minus
      (ceCurvature K (oneFormAlternatingLinearEquiv K Γ₂) v)) =
      !![2 * Complex.I, 0; 0, -2 * Complex.I] := by
  intro K Γ₂ v
  change matrixOfOp (((2 : ℝ)⁻¹) • (ceCurvature K (oneFormAlternatingLinearEquiv K Γ₂) v -
    invS P_d63.1 * ceCurvature K (oneFormAlternatingLinearEquiv K Γ₂) v * invS P_d63.1)) = _
  rw [matrixOfOp_real_smul, matrixOfOp_sub_eq, matrixOfOp_mul_eq, matrixOfOp_mul_eq,
    t3_ab_02_F2_eq, t3_ab_02_invS_mat]
  ext i j; fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, swapMatrix, smul_eq_mul] <;>
    norm_num

/-- `T3-AB-02`: `CartanOnsagerSplit` lifted with `ceCurvature_eq` into `ParityOnsagerFormPairing` (nonzero curvatures & pairings). -/
theorem t3_ab_02_cartanSplitParityFormPairing :
    let C := peirceCartanOnsagerSplit P_d63
    let K := peirceCutDerivationLieLane 2
    let Γ₁ := exteriorDerivativeZero K B_tilt
    let Γ₂ := exteriorDerivativeZero K tiltOp2
    let v : Fin 2 → K.L := ![peirceCutGenerator P_d63, peirceCutGenerator P_diag_i]
    let η := hsProbeBilinForm 2 (matrixOp !![0, 1; -1, 0])
    let PS := cartanParityOnsagerSystemOfForms C (hsRealBilinForm 2)
      (hsRealBilinForm_symm 2) (hsRealBilinForm_nonneg 2) η
    let PP := ParityOnsagerFormPairing.ofValueParity PS v
    let F₁ := ceCurvature K (oneFormAlternatingLinearEquiv K Γ₁)
    let F₂ := ceCurvature K (oneFormAlternatingLinearEquiv K Γ₂)
    PP.dissipative (PP.T.op F₁) (PP.T.op F₂) = PP.dissipative F₁ F₂ ∧
      PP.reversible (PP.T.op F₁) (PP.T.op F₂) = -PP.reversible F₁ F₂ ∧
      F₁ = twoCochainEquivDerivationOperatorForm K (connectionCurvature K Γ₁) ∧
      PP.totalGenerator (PP.T.op F₁) (PP.T.op F₂) = PP.totalGenerator F₂ F₁ ∧
      F₁ v ≠ 0 ∧ F₂ v ≠ 0 ∧ PP.dissipative F₁ F₂ ≠ 0 ∧ PP.reversible F₁ F₂ ≠ 0 := by
  intro C K Γ₁ Γ₂ v η PS PP F₁ F₂
  have hbridge := gapAB_cartanSplit_parityFormPairing_bridge C K (hsRealBilinForm 2)
    (hsRealBilinForm_symm 2) (hsRealBilinForm_nonneg 2) η Γ₁ Γ₂ v
  have hF1_eq : matrixOfOp (F₁ v) = !![Complex.I / 2, Complex.I; Complex.I, -Complex.I / 2] :=
    t3_ab_02_F1_eq
  have hF2_eq : matrixOfOp (F₂ v) = !![2 * Complex.I, 0; 0, -2 * Complex.I] :=
    t3_ab_02_F2_eq
  have hF1_ne : F₁ v ≠ 0 := by
    intro h0
    have hm := congrArg (fun M : FiniteOperatorAlgebra 2 => matrixOfOp M 0 1) h0
    rw [hF1_eq, matrixOfOp_zero] at hm
    simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.zero_apply] at hm
    exact Complex.I_ne_zero hm
  have hF2_ne : F₂ v ≠ 0 := by
    intro h0
    have hm := congrArg (fun M : FiniteOperatorAlgebra 2 => matrixOfOp M 0 0) h0
    rw [hF2_eq, matrixOfOp_zero] at hm
    simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.zero_apply, mul_eq_zero,
      OfNat.ofNat_ne_zero, false_or] at hm
    exact Complex.I_ne_zero hm
  have hP_plus_1 : matrixOfOp (C.S.P_plus (F₁ v)) = !![0, Complex.I; Complex.I, 0] :=
    t3_ab_02_P_plus_1
  have hP_minus_1 : matrixOfOp (C.S.P_minus (F₁ v)) = !![Complex.I / 2, 0; 0, -Complex.I / 2] :=
    t3_ab_02_P_minus_1
  have hP_plus_2 : matrixOfOp (C.S.P_plus (F₂ v)) = 0 :=
    t3_ab_02_P_plus_2
  have hP_minus_2 : matrixOfOp (C.S.P_minus (F₂ v)) = !![2 * Complex.I, 0; 0, -2 * Complex.I] :=
    t3_ab_02_P_minus_2
  have hdiss_ne : PP.dissipative F₁ F₂ ≠ 0 := by
    have hdiss_val : PP.dissipative F₁ F₂ = 2 := by
      change (finiteOperatorTrace (star (C.S.P_minus (F₁ v)) * C.S.P_minus (F₂ v))).re = 2
      change (Matrix.trace (matrixOfOp (ContinuousLinearMap.adjoint (C.S.P_minus (F₁ v)) *
        C.S.P_minus (F₂ v)))).re = 2
      rw [matrixOfOp_mul_eq, matrixOfOp_adjoint, hP_minus_1, hP_minus_2]
      simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Fin.sum_univ_two]
      norm_num
    rw [hdiss_val]; norm_num
  have hrev_ne : PP.reversible F₁ F₂ ≠ 0 := by
    have hrev_val : PP.reversible F₁ F₂ = 4 := by
      change (finiteOperatorTrace (star (matrixOp !![0, 1; -1, 0] * C.S.P_plus (F₁ v)) *
          C.S.P_minus (F₂ v))).re -
        (finiteOperatorTrace (star (matrixOp !![0, 1; -1, 0] * C.S.P_plus (F₂ v)) *
          C.S.P_minus (F₁ v))).re = 4
      change (Matrix.trace (matrixOfOp (ContinuousLinearMap.adjoint
          (matrixOp !![0, 1; -1, 0] * C.S.P_plus (F₁ v)) * C.S.P_minus (F₂ v)))).re -
        (Matrix.trace (matrixOfOp (ContinuousLinearMap.adjoint
          (matrixOp !![0, 1; -1, 0] * C.S.P_plus (F₂ v)) * C.S.P_minus (F₁ v)))).re = 4
      rw [matrixOfOp_mul_eq, matrixOfOp_adjoint, matrixOfOp_mul_eq, matrixOfOp_matrixOp,
        hP_plus_1, hP_minus_2, matrixOfOp_mul_eq, matrixOfOp_adjoint, matrixOfOp_mul_eq,
        matrixOfOp_matrixOp, hP_plus_2, hP_minus_1]
      simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Fin.sum_univ_two]
      norm_num
    rw [hrev_val]; norm_num
  exact ⟨hbridge.1, hbridge.2.1, hbridge.2.2.1, hbridge.2.2.2, hF1_ne, hF2_ne, hdiss_ne, hrev_ne⟩

section Tier3_GapBC_L2

open scoped Matrix.Norms.L2Operator

private lemma conjStarAlgEquiv_realMatrix {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) :
    conjStarAlgEquiv n (matrixOp (M.map Complex.ofReal)) = matrixOp (M.map Complex.ofReal) := by
  apply matrixOfOp_injective
  rw [conjStarAlgEquiv_apply, conjOpFun, matrixOfOp_matrixOp, matrixOfOp_matrixOp]
  ext i j
  simp

private lemma conjStarAlgEquiv_B_tilt :
    conjStarAlgEquiv 2 B_tilt = B_tilt := by
  have h : B_tilt = matrixOp (tiltedMatrix.map Complex.ofReal) := by
    apply matrixOfOp_injective
    rw [B_tilt, matrixOfOp_matrixOp, matrixOfOp_matrixOp]
    ext i j; fin_cases i <;> fin_cases j <;> simp [tiltedMatrix]
  rw [h]
  exact conjStarAlgEquiv_realMatrix tiltedMatrix

private lemma conjStarAlgEquiv_A_swap :
    conjStarAlgEquiv 2 A_swap = A_swap := by
  rw [← switchOp2_eq_A_swap]
  exact conj_switchOp2

/-- `T3-BC-01` & `T3-BC-02`: `gapBC_frechetHessian_gibbsTrajectory_secondLaw` along `H(t) := B_tilt + t • A_swap` (`[H(t), H'(t)] ≠ 0`) with strictly non-zero `A1, A2, dissipative, reversible`. -/
theorem t3_bc_01_02_frechetHessianAndGibbsTrajectorySecondLaw :
    let τ := conjStarAlgEquiv 2
    let H : ℝ → GibbsOperator 2 := fun t => B_tilt + t • A_swap
    let a : GibbsOperator 2 := tiltOp2
    let Q : GibbsOperator 2 := Complex.I • tiltOp2
    let D1 := innerFrechetComplexDeriv (Complex.I • switchOp2)
    let D2 := innerFrechetComplexDeriv
      (Complex.I • (switchOp2 + matrixOp !![0, Complex.I; -Complex.I, 0]))
    let rho : ℝ → Matrix (Fin 2) (Fin 2) ℂ := fun t => matrixOfOp (normalizedExponential (H t))
    let hH : ∀ t : ℝ, IsSelfAdjoint (H t) := fun t =>
      isSelfAdjoint_add_op hB_tilt_sa (isSelfAdjoint_real_smul t A_swap hA_swap_sa)
    let hZ : ∀ t : ℝ, 0 < gibbsPartitionReal (H t) := fun t =>
      tracedExponential_re_pos_of_isSelfAdjoint (H t) (hH t)
    (∀ t ∈ Set.Icc (0 : ℝ) 1,
      let x1 := finiteCEFrechetDirection D1
      let x2 := finiteCEFrechetDirection D2
      let A1 := finiteCEOperatorForm 2 a x1
      let A2 := finiteCEOperatorForm 2 a x2
      let PS := finiteGibbsCEParityOnsagerSystemOfAut τ (conjStarAlgEquiv_involutive (n := 2))
        (H t) (hH t) (hZ t) (by
          change τ (B_tilt + t • A_swap) = B_tilt + t • A_swap
          rw [_root_.map_add, _root_.map_smul]
          exact congrArg₂ (· + t • ·) conjStarAlgEquiv_B_tilt conjStarAlgEquiv_A_swap)
        (conjStarAlgEquiv_trace_re (n := 2)) a Q conj_tiltOp2
        (conjStarAlgEquiv_purelyImaginary_odd tiltOp2 conj_tiltOp2)
      frechetExtDeriv (logPartitionOneForm 2) (H t) ![A1, A2] = 0 ∧
        (secondFDerivLogPartitionReadout (H t) A1 A2).re = PS.dissipative x1 x2 ∧
        PS.totalGenerator (PS.T.op x1) (PS.T.op x2) = PS.totalGenerator x2 x1 ∧
        A1 ≠ 0 ∧ A2 ≠ 0 ∧ PS.dissipative x1 x2 ≠ 0 ∧ PS.reversible x1 x2 ≠ 0) ∧
      deriv (fun s => Φ_norm_swap (rho s)) 0 < 0 ∧
      AntitoneOn (fun s => Φ_norm_swap (rho s)) (Set.Icc 0 1) := by
  intro τ H a Q D1 D2 rho hH hZ
  let D : ℝ → FaithfulDensityOperator 2 := fun t => faithfulGibbsDensity (H t) (hH t) (hZ t)
  let sys : ℝ → MetriplecticDissipation.MetriplecticDissipativeSystem (Fin 2) := fun t =>
    { rho := rho t
      H := 0
      grad_F := -matrixOfOp (centeredStatistic (D t) A_swap)
      Onsager := matrixKuboMoriMobility (D t) (continuous_faithfulGibbsDensity_rpow (H t) (hH t) (hZ t)) }
  have hτ_H : ∀ t ∈ Set.Icc (0 : ℝ) 1, τ (H t) = H t := fun t _ => by
    change τ (B_tilt + t • A_swap) = B_tilt + t • A_swap
    rw [_root_.map_add, _root_.map_smul]
    exact congrArg₂ (· + t • ·) conjStarAlgEquiv_B_tilt conjStarAlgEquiv_A_swap
  have ha_fix : τ a = a := by dsimp only [a]; exact conj_tiltOp2
  have hQ_odd : τ Q = -Q := by
    dsimp only [Q]; exact conjStarAlgEquiv_purelyImaginary_odd tiltOp2 conj_tiltOp2
  let M_sigY : GibbsOperator 2 := matrixOp !![0, Complex.I; -Complex.I, 0]
  have hM_sigY_sa : IsSelfAdjoint M_sigY := by
    rw [isSelfAdjoint_iff]
    apply matrixOfOp_injective
    change matrixOfOp (ContinuousLinearMap.adjoint M_sigY) = matrixOfOp M_sigY
    rw [matrixOfOp_adjoint]
    dsimp [M_sigY]
    rw [matrixOfOp_matrixOp]
    ext i j; fin_cases i <;> fin_cases j <;> simp
  have hA1 : IsSelfAdjoint (finiteCEOperatorForm 2 a (finiteCEFrechetDirection D1)) :=
    isSelfAdjoint_I_smul_comm switchOp2 a switchOp2_isSelfAdjoint tiltOp2_isSelfAdjoint
  have hA2 : IsSelfAdjoint (finiteCEOperatorForm 2 a (finiteCEFrechetDirection D2)) :=
    isSelfAdjoint_I_smul_comm (switchOp2 + M_sigY) a
      (isSelfAdjoint_add_op switchOp2_isSelfAdjoint hM_sigY_sa) tiltOp2_isSelfAdjoint
  let L_dΦ : ℝ → (Matrix (Fin 2) (Fin 2) ℂ →ₗ[ℝ] ℝ) := fun t =>
    { toFun := fun V => (Matrix.trace (star (sys t).grad_F * V)).re
      map_add' := fun V W => by rw [Matrix.mul_add, Matrix.trace_add, Complex.add_re]
      map_smul' := fun r V => by
        simp only [RingHom.id_apply]
        rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, Complex.real_smul,
          Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] }
  let dΦ : ℝ → (Matrix (Fin 2) (Fin 2) ℂ →L[ℝ] ℝ) := fun t =>
    { toLinearMap := L_dΦ t
      cont := LinearMap.continuous_of_finiteDimensional (L_dΦ t) }
  have hrho_eq : ∀ t : ℝ, rho t = matrixOfOp (D t).rho := fun t => by
    change matrixOfOp (normalizedExponential (H t)) = matrixOfOp (D t).rho
    rw [faithfulGibbsDensity_rho_eq_normalizedExponential (H t) (hH t) (hZ t)]
  have hrho_deriv : ∀ t ∈ interior (Set.Icc (0 : ℝ) 1),
      HasDerivAt rho (MetriplecticDissipation.stateEvolution (sys t)) t := by
    intro t _
    have hH_deriv : HasDerivAt H A_swap t := hasDerivAt_add_real_smul B_tilt A_swap t
    have hnorm := hasDerivAt_normalizedExponential_centered H (hH t) hA_swap_sa hH_deriv
    have hmat := ((matrixOfOpCLMℝ 2).hasFDerivAt.comp_hasDerivAt t hnorm)
    have hevol : matrixOfOp ((D t).kuboMoriTransform (centeredStatistic (D t) A_swap)) =
        MetriplecticDissipation.stateEvolution (sys t) := by
      simp only [MetriplecticDissipation.stateEvolution, MetriplecticDissipation.unitaryFlow,
        MetriplecticDissipation.commutator, sys, zero_mul, mul_zero, sub_zero, smul_zero, zero_sub]
      change matrixOfOp ((D t).kuboMoriTransform (centeredStatistic (D t) A_swap)) =
        -(matrixKuboMoriMobility (D t) (continuous_faithfulGibbsDensity_rpow (H t) (hH t) (hZ t))
          (-matrixOfOp (centeredStatistic (D t) A_swap)))
      rw [LinearMap.map_neg, neg_neg]
      dsimp only [matrixKuboMoriMobility]
      change matrixOfOp ((D t).kuboMoriTransform (centeredStatistic (D t) A_swap)) =
        matrixOfOp ((D t).kuboMoriTransform (matrixOp (matrixOfOp (centeredStatistic (D t) A_swap))))
      rw [matrixOp_matrixOfOp]
    change HasDerivAt rho (matrixOfOp ((D t).kuboMoriTransform (centeredStatistic (D t) A_swap))) t
      at hmat
    rwa [hevol] at hmat
  have hΦ : ∀ t ∈ interior (Set.Icc (0 : ℝ) 1), HasFDerivAt Φ_norm_swap (dΦ t) (rho t) := by
    intro t _
    rw [hrho_eq t]
    exact Φ_norm_swap_hasFDerivAt (H t) (hH t) (hZ t)
  have hcont : ContinuousOn (fun s => Φ_norm_swap (rho s)) (Set.Icc (0 : ℝ) 1) := by
    intro t _
    have hnorm := hasDerivAt_normalizedExponential_centered H (hH t) hA_swap_sa
      (hasDerivAt_add_real_smul B_tilt A_swap t)
    have hmat := ((matrixOfOpCLMℝ 2).hasFDerivAt.comp_hasDerivAt t hnorm)
    have hΦt : HasFDerivAt Φ_norm_swap (dΦ t) (rho t) := by
      rw [hrho_eq t]; exact Φ_norm_swap_hasFDerivAt (H t) (hH t) (hZ t)
    exact (hΦt.comp_hasDerivAt t hmat).continuousAt.continuousWithinAt
  have hgap := gapBC_frechetHessian_gibbsTrajectory_secondLaw τ (conjStarAlgEquiv_involutive (n := 2))
    H a Q (convex_Icc 0 1) (fun t _ => hH t) hτ_H (conjStarAlgEquiv_trace_re (n := 2))
    ha_fix hQ_odd D1 D2 hA1 hA2 Φ_norm_swap dΦ sys hcont
    (fun _ _ _ => rfl) (fun t _ => by simp [sys]) hrho_deriv hΦ (fun _ _ _ => rfl)
  let x1 := finiteCEFrechetDirection D1
  let x2 := finiteCEFrechetDirection D2
  let A1 := finiteCEOperatorForm 2 a x1
  let A2 := finiteCEOperatorForm 2 a x2
  let E_real : GibbsOperator 2 := (2 : ℝ) • switchOp2
  have hA1_mat : matrixOfOp A1 = !![0, -2 * Complex.I; 2 * Complex.I, 0] := by
    change matrixOfOp ((Complex.I • switchOp2) * tiltOp2 - tiltOp2 * (Complex.I • switchOp2)) = _
    rw [matrixOfOp_sub_eq, matrixOfOp_mul_eq, matrixOfOp_mul_eq, matrixOfOp_complex_smul,
      switchOp2_eq_A_swap, matrixOfOp_A_swap, matrixOfOp_tiltOp2]
    ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [Complex.ext_iff, swapMatrix, InfoGeometry.Physics.KleinBottleSewingExact.tilt2,
        Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct]
  have hA2_split : A2 = A1 + E_real := by
    apply matrixOfOp_injective
    change matrixOfOp ((Complex.I • (switchOp2 + M_sigY)) * tiltOp2 -
        tiltOp2 * (Complex.I • (switchOp2 + M_sigY))) =
      matrixOfOp A1 + matrixOfOp ((2 : ℝ) • switchOp2)
    rw [matrixOfOp_sub_eq, matrixOfOp_mul_eq, matrixOfOp_mul_eq, matrixOfOp_complex_smul,
      matrixOfOp_add, hA1_mat, matrixOfOp_real_smul, switchOp2_eq_A_swap,
      matrixOfOp_A_swap, matrixOfOp_tiltOp2]
    dsimp [M_sigY]
    rw [matrixOfOp_matrixOp]
    ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [Complex.ext_iff, swapMatrix, InfoGeometry.Physics.KleinBottleSewingExact.tilt2,
        Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct]
  have hA1_ne : A1 ≠ 0 := by
    intro h0
    have hm := congrArg (fun M : GibbsOperator 2 => matrixOfOp M 0 1) h0
    rw [hA1_mat, matrixOfOp_zero] at hm
    simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.zero_apply,
      neg_mul, neg_eq_zero, mul_eq_zero, OfNat.ofNat_ne_zero, false_or] at hm
    exact Complex.I_ne_zero hm
  have hA2_ne : A2 ≠ 0 := by
    intro h0
    have hm := congrArg (fun M : GibbsOperator 2 => matrixOfOp M 0 1) h0
    rw [hA2_split, matrixOfOp_add, hA1_mat, matrixOfOp_real_smul, switchOp2_eq_A_swap,
      matrixOfOp_A_swap, matrixOfOp_zero] at hm
    simp only [Matrix.add_apply, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply, swapMatrix] at hm
    have hre := congrArg Complex.re hm
    norm_num at hre
  have hA1_not_gauge : A1 ∉ scalarGauge 2 := by
    apply matrixOp_ne_scalarGauge A1 0 1 (by decide)
    rw [hA1_mat]
    simp [Complex.I_ne_zero]
  have hτ_A1 : τ A1 = -A1 := by
    apply matrixOfOp_injective
    rw [conjStarAlgEquiv_apply, conjOpFun, matrixOfOp_matrixOp, matrixOfOp_neg_eq, hA1_mat]
    ext i j; fin_cases i <;> fin_cases j <;> apply Complex.ext <;> simp
  have hτ_E : τ E_real = E_real := by
    dsimp [E_real]
    rw [_root_.map_smul, conj_switchOp2]
  have hcomm_A1_A2 : A1 * A2 - A2 * A1 = (-8 : ℝ) • Q := by
    apply matrixOfOp_injective
    have hcomm_split : A1 * (A1 + E_real) - (A1 + E_real) * A1 = A1 * E_real - E_real * A1 := by
      noncomm_ring
    rw [hA2_split, hcomm_split, matrixOfOp_sub_eq, matrixOfOp_mul_eq, matrixOfOp_mul_eq,
      matrixOfOp_real_smul, hA1_mat, matrixOfOp_real_smul, switchOp2_eq_A_swap, matrixOfOp_A_swap,
      show Q = Complex.I • tiltOp2 from rfl, matrixOfOp_complex_smul, matrixOfOp_tiltOp2]
    ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [Complex.ext_iff, swapMatrix, InfoGeometry.Physics.KleinBottleSewingExact.tilt2,
        Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct]
  have hQ_ne : Q ≠ 0 := by
    intro h0
    have hm := congrArg (fun M : GibbsOperator 2 => matrixOfOp M 0 0) h0
    dsimp only [Q] at hm
    rw [matrixOfOp_complex_smul, matrixOfOp_tiltOp2, matrixOfOp_zero] at hm
    norm_num [InfoGeometry.Physics.KleinBottleSewingExact.tilt2] at hm
  refine ⟨fun t ht => ?_, (t1_f6_05_freeEnergyMatrixKuboMoriMobility).2.1, hgap.2.2⟩
  have ht1 := hgap.1 t ht
  have hτ_rho_t : τ (D t).rho = (D t).rho :=
    aut_faithfulGibbsDensity_rho τ (H t) (hH t) (hZ t) (hτ_H t ht)
  have hpow_t := continuous_faithfulGibbsDensity_rpow (H t) (hH t) (hZ t)
  have hortho_t : centeredBKMRealCovariance (D t) hpow_t A1 E_real = 0 := by
    have hinv := centeredBKMRealCovariance_aut τ (D t) hpow_t hτ_rho_t
      (conjStarAlgEquiv_trace_re (n := 2)) A1 E_real
    rw [hτ_A1, hτ_E, ← centeredBKMRealCovarianceBilin_apply, _root_.map_neg, LinearMap.neg_apply,
      centeredBKMRealCovarianceBilin_apply] at hinv
    linarith
  have hdiss_t : (finiteGibbsCEParityOnsagerSystemOfAut τ (conjStarAlgEquiv_involutive (n := 2))
      (H t) (hH t) (hZ t) (hτ_H t ht) (conjStarAlgEquiv_trace_re (n := 2)) a Q ha_fix hQ_odd).dissipative
      x1 x2 ≠ 0 := by
    change centeredCEBKMForm (D t) hpow_t a x1 x2 ≠ 0
    rw [centeredCEBKMForm_apply]
    change centeredBKMRealCovariance (D t) hpow_t A1 A2 ≠ 0
    rw [hA2_split, ← centeredBKMRealCovarianceBilin_apply, _root_.map_add,
      centeredBKMRealCovarianceBilin_apply, centeredBKMRealCovarianceBilin_apply,
      hortho_t, add_zero]
    exact ne_of_gt (centeredBKMRealCovariance_self_pos_of_not_scalarGauge (hH t) (hZ t) A1 hA1_not_gauge)
  have hrev_t : (finiteGibbsCEParityOnsagerSystemOfAut τ (conjStarAlgEquiv_involutive (n := 2))
      (H t) (hH t) (hZ t) (hτ_H t ht) (conjStarAlgEquiv_trace_re (n := 2)) a Q ha_fix hQ_odd).reversible
      x1 x2 ≠ 0 := by
    change ceCurvatureBKMProbeForm (D t) hpow_t a Q x1 x2 ≠ 0
    rw [ceCurvatureBKMProbeForm_apply]
    have hcurv : connectionCurvature (realDerivationsLane (GibbsOperator 2))
        (exteriorDerivativeZero (realDerivationsLane (GibbsOperator 2)) a) x1 x2 = (-8 : ℝ) • Q := by
      rw [connectionCurvature, exteriorDerivativeOne_exteriorDerivativeZero, zero_add]
      exact hcomm_A1_A2
    rw [hcurv, ((D t).bkmRealBilinForm hpow_t).map_smul (-8 : ℝ) Q,
      LinearMap.smul_apply, smul_eq_mul]
    have hpos : 0 < (D t).bkmRealBilinForm hpow_t Q Q :=
      ((D t).bkmRealBilinForm_self_pos_iff hpow_t Q).mpr hQ_ne
    linarith
  exact ⟨ht1.1, ht1.2.1, ht1.2.2, hA1_ne, hA2_ne, hdiss_t, hrev_t⟩

end Tier3_GapBC_L2

/-- `T3-AD-01`: `gapAD_peirceCut_superAnticomm_cartan_bridge` on `3×3` `P3, A3, C3, X3` with nonzero `d_anti` & `d_cut`. -/
theorem t3_ad_01_peirceCutSuperAnticommCartan :
    let P3_mat : Matrix (Fin 3) (Fin 3) ℂ := !![(1 : ℂ), 0, 0; 0, 1, 0; 0, 0, 0]
    let P3_op : FiniteOperatorAlgebra 3 := matrixOp P3_mat
    have hP3 : P3_op * P3_op = P3_op := by
      apply matrixOfOp_injective
      rw [matrixOfOp_mul_eq, show matrixOfOp P3_op = P3_mat from matrixOfOp_matrixOp _]
      ext i j; fin_cases i <;> fin_cases j <;>
        { simp only [P3_mat, Matrix.mul_apply, Fin.sum_univ_three, Matrix.of_apply,
            Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
          norm_num }
    let P3 : PeirceCut 3 := ⟨P3_op, hP3⟩
    let A3 : FiniteOperatorAlgebra 3 := matrixOp !![(0 : ℂ), 0, 1; 0, 0, 0; 0, 0, 0]
    let C3 : FiniteOperatorAlgebra 3 := matrixOp !![(0 : ℂ), 0, 0; 0, 0, 0; 1, 0, 0]
    let X3 : FiniteOperatorAlgebra 3 := matrixOp !![(0 : ℂ), 1, 0; 1, 0, 0; 0, 0, 0]
    let d_cut : NonAssocDerivation.derivations ℝ (FiniteOperatorAlgebra 3) :=
      FrechetBridge.toRealDerivation (cutDerivation P3)
    let d_anti : NonAssocDerivation.derivations ℝ (FiniteOperatorAlgebra 3) :=
      superAnticommLinearToDerivations (PureNonCommutativeOperatorSpine.invS_sq P3.property)
        (differentialPlusLinear_isOdd (R := ℝ) P3.property A3)
        (differentialMinusLinear_isOdd (R := ℝ) P3.property C3)
    let S_der := peirceDerivCartanOnsagerSplit P3
    let S_op := peirceSymmetricLieAlgebra P3
    d_cut ∈ S_der.drazinCore ∧
      (d_anti : Module.End ℝ (FiniteOperatorAlgebra 3)) X3 =
        PureNonCommutativeOperatorSpine.genV P3.1 A3 C3 * X3 -
          X3 * PureNonCommutativeOperatorSpine.genV P3.1 A3 C3 ∧
      S_op.P_plus ((peirceCartanTimeReversal P3).op X3) = -S_op.P_plus X3 ∧
      S_op.P_minus ((peirceCartanTimeReversal P3).op X3) = S_op.P_minus X3 ∧
      (d_anti : Module.End ℝ (FiniteOperatorAlgebra 3)) X3 ≠ 0 ∧
      (d_cut : Module.End ℝ (FiniteOperatorAlgebra 3)) A3 ≠ 0 := by
  intro P3_mat P3_op hP3 P3 A3 C3 X3 d_cut d_anti S_der S_op
  have hbridge := gapAD_peirceCut_superAnticomm_cartan_bridge P3 A3 C3 X3
  have hdanti_ne : (d_anti : Module.End ℝ (FiniteOperatorAlgebra 3)) X3 ≠ 0 := by
    have hgenV : matrixOfOp (PureNonCommutativeOperatorSpine.genV P3.1 A3 C3) =
        !![(1 : ℂ), 0, 0; 0, 0, 0; 0, 0, 1] := by
      dsimp [PureNonCommutativeOperatorSpine.genV, PureNonCommutativeOperatorSpine.anticomm,
        PureNonCommutativeOperatorSpine.conePlus, PureNonCommutativeOperatorSpine.coneMinus]
      simp only [matrixOfOp_add, matrixOfOp_mul_eq, matrixOfOp_sub_eq, matrixOfOp_one_eq]
      rw [show matrixOfOp P3.1 = P3_mat from matrixOfOp_matrixOp _,
        show matrixOfOp A3 = !![(0 : ℂ), 0, 1; 0, 0, 0; 0, 0, 0] from matrixOfOp_matrixOp _,
        show matrixOfOp C3 = !![(0 : ℂ), 0, 0; 0, 0, 0; 1, 0, 0] from matrixOfOp_matrixOp _]
      ext i j
      simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.sub_apply, Matrix.one_apply,
        Fin.sum_univ_three]
      fin_cases i <;> fin_cases j <;> (simp [P3_mat]; try norm_num)
    intro h0
    have hcomm0 : PureNonCommutativeOperatorSpine.genV P3.1 A3 C3 * X3 -
        X3 * PureNonCommutativeOperatorSpine.genV P3.1 A3 C3 = 0 :=
      hbridge.2.1.symm.trans h0
    have hm := congrArg (fun M : FiniteOperatorAlgebra 3 => matrixOfOp M 0 1) hcomm0
    rw [matrixOfOp_sub_eq, matrixOfOp_mul_eq, matrixOfOp_mul_eq, hgenV,
      show matrixOfOp X3 = !![(0 : ℂ), 1, 0; 1, 0, 0; 0, 0, 0] from matrixOfOp_matrixOp _,
      matrixOfOp_zero] at hm
    norm_num [Matrix.mul_apply, Fin.sum_univ_three] at hm
  have hdcut_ne : (d_cut : Module.End ℝ (FiniteOperatorAlgebra 3)) A3 ≠ 0 := by
    intro h0
    have hm := congrArg (fun M : FiniteOperatorAlgebra 3 => matrixOfOp M 0 2) h0
    change matrixOfOp (P3.1 * A3 - A3 * P3.1) 0 2 = 0 at hm
    rw [matrixOfOp_sub_eq, matrixOfOp_mul_eq, matrixOfOp_mul_eq,
      show matrixOfOp P3.1 = P3_mat from matrixOfOp_matrixOp _,
      show matrixOfOp A3 = !![(0 : ℂ), 0, 1; 0, 0, 0; 0, 0, 0] from matrixOfOp_matrixOp _] at hm
    norm_num [P3_mat, Matrix.mul_apply, Fin.sum_univ_three] at hm
  exact ⟨hbridge.1, hbridge.2.1, hbridge.2.2.1, hbridge.2.2.2, hdanti_ne, hdcut_ne⟩

/-- `T3-AD-02`: `gapAD_bridgedLane_cartanOnsager_bridge` yields PSD dissipation and master reciprocity on `K := realDerivationLieLane Mat2R`. -/
theorem t3_ad_02_bridgedLaneCartanOnsager :
    let K := realDerivationLieLane Mat2R
    let invMat : Mat2R := !![1, 0; 0, -1]
    have hinv_sq : invMat * invMat = 1 := by
      ext i j; fin_cases i <;> fin_cases j <;>
        norm_num [invMat, Matrix.mul_apply, Fin.sum_univ_two]
    let θ_op : Mat2R →ₗ[ℝ] Mat2R :=
      { toFun := fun X => invMat * X * invMat
        map_add' := fun _ _ => by noncomm_ring
        map_smul' := fun r X => by
          change invMat * (r • X) * invMat = r • (invMat * X * invMat)
          rw [mul_smul_comm, smul_mul_assoc] }
    let conjD : NonAssocDerivation.derivations ℝ Mat2R → NonAssocDerivation.derivations ℝ Mat2R :=
      fun d =>
        ⟨{ toFun := fun X => θ_op ((d : Module.End ℝ Mat2R) (θ_op X))
           map_add' := fun X Y => by simp [_root_.map_add]
           map_smul' := fun r X => by simp [_root_.map_smul] },
         fun X Y => by
           have hmul : ∀ A B : Mat2R, θ_op (A * B) = θ_op A * θ_op B := fun A B => by
             dsimp [θ_op]
             calc invMat * (A * B) * invMat = (invMat * A) * ((1 : Mat2R) * B) * invMat := by
                   rw [one_mul]; noncomm_ring
               _ = (invMat * A) * ((invMat * invMat) * B) * invMat := by rw [hinv_sq]
               _ = (invMat * A * invMat) * (invMat * B * invMat) := by noncomm_ring
           have hinv : ∀ A : Mat2R, θ_op (θ_op A) = A := fun A => by
             dsimp [θ_op]
             calc invMat * (invMat * A * invMat) * invMat =
                 (invMat * invMat) * A * (invMat * invMat) := by noncomm_ring
               _ = A := by rw [hinv_sq, one_mul, mul_one]
           change θ_op ((d : Module.End ℝ Mat2R) (θ_op (X * Y))) =
             θ_op ((d : Module.End ℝ Mat2R) (θ_op X)) * Y +
               X * θ_op ((d : Module.End ℝ Mat2R) (θ_op Y))
           rw [hmul, d.property, θ_op.map_add, hmul, hmul, hinv, hinv]⟩
    let θ_lie : InvolutiveLieAut K.L :=
      ⟨{ toFun := fun D => (conjD (K.act D) : NonAssocDerivation.derivations ℝ Mat2R)
         invFun := fun D => (conjD (K.act D) : NonAssocDerivation.derivations ℝ Mat2R)
         left_inv := fun D => by
           apply K.faithful; apply Subtype.ext; apply LinearMap.ext; intro X
           have hinv : ∀ A : Mat2R, θ_op (θ_op A) = A := fun A => by
             dsimp [θ_op]
             calc invMat * (invMat * A * invMat) * invMat =
                 (invMat * invMat) * A * (invMat * invMat) := by noncomm_ring
               _ = A := by rw [hinv_sq, one_mul, mul_one]
           change θ_op (θ_op (((K.act D) : Module.End ℝ Mat2R) (θ_op (θ_op X)))) = _
           rw [hinv, hinv]
         right_inv := fun D => by
           apply K.faithful; apply Subtype.ext; apply LinearMap.ext; intro X
           have hinv : ∀ A : Mat2R, θ_op (θ_op A) = A := fun A => by
             dsimp [θ_op]
             calc invMat * (invMat * A * invMat) * invMat =
                 (invMat * invMat) * A * (invMat * invMat) := by noncomm_ring
               _ = A := by rw [hinv_sq, one_mul, mul_one]
           change θ_op (θ_op (((K.act D) : Module.End ℝ Mat2R) (θ_op (θ_op X)))) = _
           rw [hinv, hinv]
         map_add' := fun D1 D2 => by
           apply K.faithful; apply Subtype.ext; apply LinearMap.ext; intro X
           change θ_op (((K.act D1 : Module.End ℝ Mat2R) (θ_op X)) +
             ((K.act D2 : Module.End ℝ Mat2R) (θ_op X))) = _
           exact θ_op.map_add _ _
         map_smul' := fun r D => by
           apply K.faithful; apply Subtype.ext; apply LinearMap.ext; intro X
           change θ_op (r • ((K.act D : Module.End ℝ Mat2R) (θ_op X))) = _
           exact θ_op.map_smul r _
         map_lie' := fun {D1 D2} => by
           apply K.faithful; apply Subtype.ext; apply LinearMap.ext; intro X
           have hinv : ∀ A : Mat2R, θ_op (θ_op A) = A := fun A => by
             dsimp [θ_op]
             calc invMat * (invMat * A * invMat) * invMat =
                 (invMat * invMat) * A * (invMat * invMat) := by noncomm_ring
               _ = A := by rw [hinv_sq, one_mul, mul_one]
           change θ_op (((K.act D1 : Module.End ℝ Mat2R) ((K.act D2 : Module.End ℝ Mat2R) (θ_op X))) -
               ((K.act D2 : Module.End ℝ Mat2R) ((K.act D1 : Module.End ℝ Mat2R) (θ_op X)))) =
             θ_op ((K.act D1 : Module.End ℝ Mat2R) (θ_op (θ_op ((K.act D2 : Module.End ℝ Mat2R) (θ_op X))))) -
               θ_op ((K.act D2 : Module.End ℝ Mat2R) (θ_op (θ_op ((K.act D1 : Module.End ℝ Mat2R) (θ_op X)))))
           rw [hinv, hinv, LinearMap.map_sub] },
       fun D => by
         apply K.faithful; apply Subtype.ext; apply LinearMap.ext; intro X
         have hinv : ∀ A : Mat2R, θ_op (θ_op A) = A := fun A => by
           dsimp [θ_op]
           calc invMat * (invMat * A * invMat) * invMat =
               (invMat * invMat) * A * (invMat * invMat) := by noncomm_ring
             _ = A := by rw [hinv_sq, one_mul, mul_one]
         change θ_op (θ_op (((K.act D) : Module.End ℝ Mat2R) (θ_op (θ_op X)))) = _
         rw [hinv, hinv]⟩
    let S := SymmetricLieAlgebra.ofInvolutiveLieAut θ_lie
    let C : CartanOnsagerSplit K.L :=
      { S := S, onsager := S.P_minus, drazinCore := S.𝔨, dissipativeRange := S.𝔭,
        drazinCore_eq_k := rfl, dissipativeRange_eq_p := rfl }
    let g_tr : LinearMap.BilinForm ℝ K.L :=
      { toFun := fun D1 =>
          { toFun := fun D2 =>
              Matrix.trace (star (K.operatorAction D1 K2_real) * K.operatorAction D2 K2_real)
            map_add' := fun D2 D3 => by simp [DerivationLieLane.operatorAction, Matrix.mul_add, Matrix.trace_add]
            map_smul' := fun r D2 => by simp [DerivationLieLane.operatorAction] }
        map_add' := fun D1 D2 => by
          ext D3; simp [DerivationLieLane.operatorAction, Matrix.add_mul, Matrix.trace_add]
        map_smul' := fun r D1 => by
          ext D3; simp [DerivationLieLane.operatorAction] }
    have hg_symm : ∀ x y, g_tr x y = g_tr y x := fun x y => by
      change Matrix.trace (star (K.operatorAction x K2_real) * K.operatorAction y K2_real) =
        Matrix.trace (star (K.operatorAction y K2_real) * K.operatorAction x K2_real)
      simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.star_apply,
        star_trivial, Fin.sum_univ_two]
      ring
    have hg_nonneg : ∀ x, 0 ≤ g_tr x x := fun x => by
      change 0 ≤ Matrix.trace (star (K.operatorAction x K2_real) * K.operatorAction x K2_real)
      simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.star_apply,
        star_trivial, Fin.sum_univ_two]
      nlinarith [sq_nonneg ((K.operatorAction x K2_real) 0 0),
        sq_nonneg ((K.operatorAction x K2_real) 1 0),
        sq_nonneg ((K.operatorAction x K2_real) 0 1),
        sq_nonneg ((K.operatorAction x K2_real) 1 1)]
    let η_ad : LinearMap.BilinForm ℝ K.L :=
      { toFun := fun D1 =>
          { toFun := fun D2 =>
              Matrix.trace (star (K.operatorAction D1 matrixUnit01) * K.operatorAction D2 K2_real)
            map_add' := fun D2 D3 => by
              simp [DerivationLieLane.operatorAction, Matrix.mul_add, Matrix.trace_add]
            map_smul' := fun r D2 => by simp [DerivationLieLane.operatorAction] }
        map_add' := fun D1 D2 => by
          ext D3
          simp [DerivationLieLane.operatorAction, Matrix.add_mul, Matrix.trace_add]
        map_smul' := fun r D1 => by
          ext D3
          simp [DerivationLieLane.operatorAction] }
    let PS := cartanParityOnsagerSystemOfForms C g_tr hg_symm hg_nonneg η_ad
    let d1 : K.L := innerMat2RDeriv K1_real
    let d2 : K.L := innerMat2RDeriv matrixUnit01
    let d_k : K.L := innerMat2RDeriv K2_real
    0 < PS.dissipative d1 d1 ∧
      PS.totalGenerator (PS.T.op d1) (PS.T.op d2) = PS.totalGenerator d2 d1 ∧
      PS.totalGenerator d2 d1 ≠ 0 ∧
      PS.T.op d_k = -d_k ∧
      PS.T.op d_k ≠ d_k ∧
      PS.reversible d_k d1 ≠ 0 ∧
      PS.totalGenerator (PS.T.op d_k) (PS.T.op d1) = PS.totalGenerator d1 d_k ∧
      PS.totalGenerator d1 d_k ≠ 0 := by
  intro K invMat hinv_sq θ_op conjD θ_lie S C g_tr hg_symm hg_nonneg η_ad PS d1 d2 d_k
  have hbridge := gapAD_bridgedLane_cartanOnsager_bridge K θ_lie g_tr hg_symm hg_nonneg η_ad d1 d2
  have hθ_d1 : S.θ d1 = -d1 := by
    have hc : invMat * K1_real * invMat = -K1_real := by
      ext i j; fin_cases i <;> fin_cases j <;>
        norm_num [invMat, K1_real, Matrix.mul_apply, Fin.sum_univ_two]
    apply K.faithful; apply Subtype.ext; apply LinearMap.ext; intro X
    change invMat * (K1_real * (invMat * X * invMat) - (invMat * X * invMat) * K1_real) * invMat =
      -(K1_real * X - X * K1_real)
    calc invMat * (K1_real * (invMat * X * invMat) - (invMat * X * invMat) * K1_real) * invMat
        = (invMat * K1_real * invMat) * X * (invMat * invMat) -
            (invMat * invMat) * X * (invMat * K1_real * invMat) := by noncomm_ring
      _ = -(K1_real * X - X * K1_real) := by rw [hc, hinv_sq]; noncomm_ring
  have hθ_d2 : S.θ d2 = -d2 := by
    have hc : invMat * matrixUnit01 * invMat = -matrixUnit01 := by
      ext i j; fin_cases i <;> fin_cases j <;>
        norm_num [invMat, matrixUnit01, Matrix.mul_apply, Fin.sum_univ_two]
    apply K.faithful; apply Subtype.ext; apply LinearMap.ext; intro X
    change invMat * (matrixUnit01 * (invMat * X * invMat) - (invMat * X * invMat) * matrixUnit01) * invMat =
      -(matrixUnit01 * X - X * matrixUnit01)
    calc invMat * (matrixUnit01 * (invMat * X * invMat) - (invMat * X * invMat) * matrixUnit01) * invMat
        = (invMat * matrixUnit01 * invMat) * X * (invMat * invMat) -
            (invMat * invMat) * X * (invMat * matrixUnit01 * invMat) := by noncomm_ring
      _ = -(matrixUnit01 * X - X * matrixUnit01) := by rw [hc, hinv_sq]; noncomm_ring
  have hθ_dk : S.θ d_k = d_k := by
    have hc : invMat * K2_real * invMat = K2_real := by
      ext i j; fin_cases i <;> fin_cases j <;>
        norm_num [invMat, K2_real, Matrix.mul_apply, Fin.sum_univ_two]
    apply K.faithful; apply Subtype.ext; apply LinearMap.ext; intro X
    change invMat * (K2_real * (invMat * X * invMat) - (invMat * X * invMat) * K2_real) * invMat =
      K2_real * X - X * K2_real
    calc invMat * (K2_real * (invMat * X * invMat) - (invMat * X * invMat) * K2_real) * invMat
        = (invMat * K2_real * invMat) * X * (invMat * invMat) -
            (invMat * invMat) * X * (invMat * K2_real * invMat) := by noncomm_ring
      _ = K2_real * X - X * K2_real := by rw [hc, hinv_sq]; noncomm_ring
  have hPm_d1 : S.P_minus d1 = d1 := by
    change ((2 : ℝ)⁻¹) • (d1 - S.θ d1) = d1
    rw [hθ_d1, sub_neg_eq_add, ← two_smul ℝ d1, smul_smul]; norm_num
  have hPp_d1 : S.P_plus d1 = 0 := by
    change ((2 : ℝ)⁻¹) • (d1 + S.θ d1) = 0
    rw [hθ_d1, add_neg_cancel, smul_zero]
  have hPm_d2 : S.P_minus d2 = d2 := by
    change ((2 : ℝ)⁻¹) • (d2 - S.θ d2) = d2
    rw [hθ_d2, sub_neg_eq_add, ← two_smul ℝ d2, smul_smul]; norm_num
  have hPp_d2 : S.P_plus d2 = 0 := by
    change ((2 : ℝ)⁻¹) • (d2 + S.θ d2) = 0
    rw [hθ_d2, add_neg_cancel, smul_zero]
  have hPp_dk : S.P_plus d_k = d_k := by
    change ((2 : ℝ)⁻¹) • (d_k + S.θ d_k) = d_k
    rw [hθ_dk, ← two_smul ℝ d_k, smul_smul]; norm_num
  have hPm_dk : S.P_minus d_k = 0 := by
    change ((2 : ℝ)⁻¹) • (d_k - S.θ d_k) = 0
    rw [hθ_dk, sub_self, smul_zero]
  have hdiss_pos : 0 < PS.dissipative d1 d1 := by
    change 0 < g_tr (S.P_minus d1) (S.P_minus d1)
    rw [hPm_d1]
    change 0 < Matrix.trace (star (K1_real * K2_real - K2_real * K1_real) *
      (K1_real * K2_real - K2_real * K1_real))
    norm_num [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.star_apply,
      K1_real, K2_real, Fin.sum_univ_two]
  have htot12_ne : PS.totalGenerator d2 d1 ≠ 0 := by
    change g_tr (S.P_minus d2) (S.P_minus d1) +
      (η_ad (S.P_plus d2) (S.P_minus d1) - η_ad (S.P_plus d1) (S.P_minus d2)) ≠ 0
    simp only [hPm_d2, hPm_d1, hPp_d2, hPp_d1, _root_.map_zero, LinearMap.zero_apply,
      sub_zero, add_zero]
    change Matrix.trace (star (matrixUnit01 * K2_real - K2_real * matrixUnit01) *
      (K1_real * K2_real - K2_real * K1_real)) ≠ 0
    norm_num [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.star_apply,
      matrixUnit01, K1_real, K2_real, Fin.sum_univ_two]
  have hT_dk : PS.T.op d_k = -d_k := by
    change -S.θ d_k = -d_k
    rw [hθ_dk]
  have hT_dk_ne : PS.T.op d_k ≠ d_k := by
    rw [hT_dk]
    intro hneg
    have hact := congrArg (fun D : K.L => K.operatorAction D matrixUnit01) hneg
    have hm := congrArg (fun M : Mat2R => M 0 1) hact
    change (-((K2_real * matrixUnit01 - matrixUnit01 * K2_real))) 0 1 =
      (K2_real * matrixUnit01 - matrixUnit01 * K2_real) 0 1 at hm
    norm_num [K2_real, matrixUnit01, Matrix.mul_apply, Fin.sum_univ_two] at hm
  have hrev_dk_d1_ne : PS.reversible d_k d1 ≠ 0 := by
    change η_ad (S.P_plus d_k) (S.P_minus d1) - η_ad (S.P_plus d1) (S.P_minus d_k) ≠ 0
    simp only [hPp_dk, hPm_d1, hPp_d1, hPm_dk, _root_.map_zero, sub_zero]
    change Matrix.trace (star (K2_real * matrixUnit01 - matrixUnit01 * K2_real) *
      (K1_real * K2_real - K2_real * K1_real)) ≠ 0
    norm_num [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.star_apply,
      matrixUnit01, K1_real, K2_real, Fin.sum_univ_two]
  have htot_d1_dk_ne : PS.totalGenerator d1 d_k ≠ 0 := by
    have hd0 : PS.dissipative d1 d_k = 0 := by
      change g_tr (S.P_minus d1) (S.P_minus d_k) = 0
      rw [hPm_dk, map_zero]
    change PS.dissipative d1 d_k + PS.reversible d1 d_k ≠ 0
    rw [hd0, zero_add, PS.reversible_skew]
    exact neg_ne_zero.mpr hrev_dk_d1_ne
  exact ⟨hdiss_pos, hbridge.2, htot12_ne, hT_dk, hT_dk_ne, hrev_dk_d1_ne,
    PS.onsager_casimir_master_reciprocity d_k d1, htot_d1_dk_ne⟩

/-- `T3-DB-01`: `gapDB_modularDerivation_ceBKM_parityForm_bridge` on `GibbsOperator 2` with nonzero actions and nonzero dissipation. -/
theorem t3_db_01_modularDerivationCeBkmParityForm :
    let U := tiltOp2
    let τ := adGammaStarAlgEquiv U tiltOp2_isSelfAdjoint tiltOp2_sq
    let H : GibbsOperator 2 := matrixOp !![2, 0; 0, 1]
    let a : GibbsOperator 2 := matrixOp !![1, 0; 0, 2]
    let Q := A_swap
    have hH : IsSelfAdjoint H := by
      rw [isSelfAdjoint_iff]; apply matrixOfOp_injective
      change matrixOfOp (ContinuousLinearMap.adjoint H) = matrixOfOp H
      dsimp only [H]; rw [matrixOfOp_adjoint, matrixOfOp_matrixOp]
      ext i j; fin_cases i <;> fin_cases j <;> simp
    have hZ : 0 < gibbsPartitionReal H := tracedExponential_re_pos_of_isSelfAdjoint H hH
    have hCommH : Commute H U := by
      rw [Commute, SemiconjBy]; apply matrixOfOp_injective
      dsimp only [H, U]
      rw [matrixOfOp_mul_eq, matrixOfOp_mul_eq, tiltOp2, matrixOfOp_matrixOp, matrixOfOp_matrixOp]
      ext i j; fin_cases i <;> fin_cases j <;>
        norm_num [InfoGeometry.Physics.KleinBottleSewingExact.tilt2, Matrix.mul_apply, Fin.sum_univ_two]
    have ha : τ a = a := by
      change U * a * U = a; apply matrixOfOp_injective
      dsimp only [a, U]
      rw [matrixOfOp_mul_eq, matrixOfOp_mul_eq, tiltOp2, matrixOfOp_matrixOp, matrixOfOp_matrixOp]
      ext i j; fin_cases i <;> fin_cases j <;>
        norm_num [InfoGeometry.Physics.KleinBottleSewingExact.tilt2, Matrix.mul_apply, Fin.sum_univ_two]
    have hQ : τ Q = -Q := by
      apply adGammaStarAlgEquiv_odd_of_anticomm U Q tiltOp2_isSelfAdjoint tiltOp2_sq
      dsimp only [Q, U]
      rw [← switchOp2_eq_A_swap, tiltOp2_switchOp2_anticomm, neg_neg]
    have hτ_H : τ H = H := by
      change U * H * U = H; rw [(hCommH.symm).eq, mul_assoc, tiltOp2_sq, mul_one]
    let D_kms : InfoGeometry.Modular.KMSState.LinearDerivation ℝ (GibbsOperator 2) :=
      kmsStateLinearDerivationEquivDerivations.symm
        (innerDerivation (matrixOp !![0, 1; -(1 / 2 : ℂ), 0]))
    let D_semi : InfoGeometry.Modular.SemidirectExterior.Derivation ℝ (GibbsOperator 2) :=
      semidirectDerivationEquivDerivations.symm
        (innerDerivation (matrixOp !![0, 1; (1 / 2 : ℂ), 0]))
    let d1 : Carrier 2 := kmsStateLinearDerivationEquivDerivations D_kms
    let d2 : Carrier 2 := semidirectDerivationEquivDerivations D_semi
    let PS := finiteGibbsCEParityOnsagerSystemOfAut τ
      (adGammaStarAlgEquiv_involutive U tiltOp2_isSelfAdjoint tiltOp2_sq)
      H hH hZ hτ_H (adGammaStarAlgEquiv_trace_re U tiltOp2_isSelfAdjoint tiltOp2_sq) a Q ha hQ
    let D := faithfulGibbsDensity H hH hZ
    let hpow := continuous_faithfulGibbsDensity_rpow H hH hZ
    PS.dissipative d1 d2 = centeredBKMRealCovariance D hpow (D_kms.toLinearMap a) (D_semi a) ∧
      PS.totalGenerator (PS.T.op d1) (PS.T.op d2) = PS.totalGenerator d2 d1 ∧
      D_kms.toLinearMap a ≠ 0 ∧ D_semi a ≠ 0 ∧ PS.dissipative d1 d2 ≠ 0 := by
  intro U τ H a Q hH hZ hCommH ha hQ hτ_H D_kms D_semi d1 d2 PS D hpow
  have h := gapDB_modularDerivation_ceBKM_parityForm_bridge τ
    (adGammaStarAlgEquiv_involutive U tiltOp2_isSelfAdjoint tiltOp2_sq) H a Q hH hZ hτ_H
    (adGammaStarAlgEquiv_trace_re U tiltOp2_isSelfAdjoint tiltOp2_sq) ha hQ D_kms D_semi
  let X_e01 : GibbsOperator 2 := matrixOp !![0, 1; 0, 0]
  let Z_e10 : GibbsOperator 2 := (1 / 2 : ℝ) • star X_e01
  have hd1_eq : D_kms.toLinearMap a = X_e01 + Z_e10 := by
    apply matrixOfOp_injective
    change matrixOfOp ((matrixOp !![0, 1; -(1 / 2 : ℂ), 0] : GibbsOperator 2) * a -
        a * (matrixOp !![0, 1; -(1 / 2 : ℂ), 0] : GibbsOperator 2)) =
      matrixOfOp (X_e01 + (1 / 2 : ℝ) • ContinuousLinearMap.adjoint X_e01)
    rw [matrixOfOp_sub_eq, matrixOfOp_mul_eq, matrixOfOp_mul_eq, matrixOfOp_add,
      matrixOfOp_real_smul, matrixOfOp_adjoint]
    dsimp only [a, X_e01]
    rw [matrixOfOp_matrixOp, matrixOfOp_matrixOp]
    ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.mul_apply, Fin.sum_univ_two]
  have hd2_eq : D_semi a = X_e01 - Z_e10 := by
    apply matrixOfOp_injective
    change matrixOfOp ((matrixOp !![0, 1; (1 / 2 : ℂ), 0] : GibbsOperator 2) * a -
        a * (matrixOp !![0, 1; (1 / 2 : ℂ), 0] : GibbsOperator 2)) =
      matrixOfOp (X_e01 - (1 / 2 : ℝ) • ContinuousLinearMap.adjoint X_e01)
    rw [matrixOfOp_sub_eq, matrixOfOp_mul_eq, matrixOfOp_mul_eq, matrixOfOp_sub_eq,
      matrixOfOp_real_smul, matrixOfOp_adjoint]
    dsimp only [a, X_e01]
    rw [matrixOfOp_matrixOp, matrixOfOp_matrixOp]
    ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.mul_apply, Fin.sum_univ_two]
  have hd1_ne : D_kms.toLinearMap a ≠ 0 := by
    intro h0
    have hm := congrArg matrixOfOp h0
    rw [hd1_eq] at hm
    dsimp only [Z_e10] at hm
    rw [matrixOfOp_add, matrixOfOp_real_smul,
      show star X_e01 = ContinuousLinearMap.adjoint X_e01 from rfl, matrixOfOp_adjoint,
      show matrixOfOp X_e01 = !![0, 1; 0, 0] from matrixOfOp_matrixOp _, matrixOfOp_zero] at hm
    have hm01 := congrFun (congrFun hm 0) 1
    norm_num at hm01
  have hd2_ne : D_semi a ≠ 0 := by
    intro h0
    have hm := congrArg matrixOfOp h0
    rw [hd2_eq] at hm
    dsimp only [Z_e10] at hm
    rw [matrixOfOp_sub_eq, matrixOfOp_real_smul,
      show star X_e01 = ContinuousLinearMap.adjoint X_e01 from rfl, matrixOfOp_adjoint,
      show matrixOfOp X_e01 = !![0, 1; 0, 0] from matrixOfOp_matrixOp _, matrixOfOp_zero] at hm
    have hm01 := congrFun (congrFun hm 0) 1
    norm_num at hm01
  have hX_not_gauge : X_e01 ∉ scalarGauge 2 := by
    apply matrixOp_ne_scalarGauge X_e01 0 1 (by decide)
    rw [show matrixOfOp X_e01 = !![0, 1; 0, 0] from matrixOfOp_matrixOp _]
    norm_num
  have hcov_X_pos : 0 < centeredBKMRealCovariance D hpow X_e01 X_e01 :=
    centeredBKMRealCovariance_self_pos_of_not_scalarGauge hH hZ X_e01 hX_not_gauge
  have hcov_Z_eq : centeredBKMRealCovariance D hpow Z_e10 Z_e10 =
      (1 / 4 : ℝ) * centeredBKMRealCovariance D hpow X_e01 X_e01 := by
    dsimp only [Z_e10]
    rw [← centeredBKMRealCovarianceBilin_apply,
      (centeredBKMRealCovarianceBilin D hpow).map_smul (1 / 2 : ℝ) (star X_e01),
      LinearMap.smul_apply,
      (centeredBKMRealCovarianceBilin D hpow (star X_e01)).map_smul (1 / 2 : ℝ) (star X_e01),
      smul_eq_mul, smul_eq_mul, centeredBKMRealCovarianceBilin_apply,
      centeredBKMRealCovariance_star]
    ring
  have hdiss_pos : 0 < PS.dissipative d1 d2 := by
    rw [h.1, hd1_eq, hd2_eq, ← centeredBKMRealCovarianceBilin_apply,
      (centeredBKMRealCovarianceBilin D hpow).map_add X_e01 Z_e10, LinearMap.add_apply,
      (centeredBKMRealCovarianceBilin D hpow X_e01).map_sub X_e01 Z_e10,
      (centeredBKMRealCovarianceBilin D hpow Z_e10).map_sub X_e01 Z_e10,
      centeredBKMRealCovarianceBilin_apply, centeredBKMRealCovarianceBilin_apply,
      centeredBKMRealCovarianceBilin_apply, centeredBKMRealCovarianceBilin_apply]
    have hsym : centeredBKMRealCovariance D hpow Z_e10 X_e01 =
        centeredBKMRealCovariance D hpow X_e01 Z_e10 :=
      centeredBKMRealCovariance_symm D hpow Z_e10 X_e01
    rw [hsym, hcov_Z_eq]
    linarith
  exact ⟨h.1, h.2.1, hd1_ne, hd2_ne, ne_of_gt hdiss_pos⟩

private def H3_e2e : GibbsOperator 3 := matrixOp !![(1 : ℂ), 0, 0; 0, 2, 0; 0, 0, 3]
private def B_br_e2e : GibbsOperator 3 := matrixOp !![(1 : ℂ), 0, 0; 0, 0, 1; 0, 1, 0]

private lemma H3_e2e_sa : IsSelfAdjoint H3_e2e := by
  rw [isSelfAdjoint_iff]; apply matrixOfOp_injective
  change matrixOfOp (ContinuousLinearMap.adjoint H3_e2e) = matrixOfOp H3_e2e
  dsimp only [H3_e2e]; rw [matrixOfOp_adjoint, matrixOfOp_matrixOp]
  ext i j; fin_cases i <;> fin_cases j <;> simp

private lemma X3_e2e_sa : IsSelfAdjoint X3_e2e := by
  rw [isSelfAdjoint_iff]; apply matrixOfOp_injective
  change matrixOfOp (ContinuousLinearMap.adjoint X3_e2e) = matrixOfOp X3_e2e
  dsimp only [X3_e2e]; rw [matrixOfOp_adjoint, matrixOfOp_matrixOp]
  ext i j; fin_cases i <;> fin_cases j <;> simp

private def D_br_e2e : GradedBraidedDerivation (ZMod 2) ℝ (GibbsOperator 3)
    (zmod2SignBicharacter ℝ) (fun _ => ⊤) where
  toFun := fun X => B_br_e2e * X - X * B_br_e2e
  deg := 0
  map_add := fun _ _ => by noncomm_ring
  map_smul := fun r X => by
    change B_br_e2e * (r • X) - (r • X) * B_br_e2e = r • (B_br_e2e * X - X * B_br_e2e)
    simp only [real_smul_eq_complex_smul, mul_smul_comm, smul_mul_assoc, smul_sub]
  leibniz_graded := fun g a _ b => by
    change B_br_e2e * (a * b) - (a * b) * B_br_e2e =
      (B_br_e2e * a - a * B_br_e2e) * b +
        ((zmod2SignBicharacter ℝ).β g 0 : ℝ) • (a * (B_br_e2e * b - b * B_br_e2e))
    rw [bicharacter_zero_right, Units.val_one, real_smul_eq_complex_smul,
      Complex.ofReal_one, one_smul]
    simp only [mul_sub, sub_mul, mul_assoc]; abel

private lemma D_br_e2e_isLeibniz :
    NonAssocDerivation.IsLeibniz ℝ (GibbsOperator 3) (gradedBraidedDerivationToLinearMap D_br_e2e) :=
  fun x y => by
    change B_br_e2e * (x * y) - (x * y) * B_br_e2e =
      (B_br_e2e * x - x * B_br_e2e) * y + x * (B_br_e2e * y - y * B_br_e2e)
    simp only [mul_sub, sub_mul, mul_assoc]
    abel

/-- `T3-DB-02`: `gapDB_superBraided_ceBKM_curvature_bridge` on `3×3` `P3, A3, C3, X3` with nonzero `d_super`, `PS.dissipative`, and `PP2.totalGenerator`. -/
theorem t3_db_02_superBraidedCeBkmCurvature :
    let P3 := P3_e2e
    let A3 := A3_e2e
    let C3 := C3_e2e
    let X3 := X3_e2e
    let H3 := H3_e2e
    let hH3_sa := H3_e2e_sa
    let hZ3_pos : 0 < gibbsPartitionReal H3 := tracedExponential_re_pos_of_isSelfAdjoint H3 hH3_sa
    let hX3_sa := X3_e2e_sa
    let D_br := D_br_e2e
    let d_super : Carrier 3 :=
      superAnticommLinearToDerivations (PureNonCommutativeOperatorSpine.invS_sq P3.property)
        (differentialPlusLinear_isOdd (R := ℝ) P3.property A3)
        (differentialMinusLinear_isOdd (R := ℝ) P3.property C3)
    let d_br : Carrier 3 := gradedBraidedDerivationToDerivations D_br D_br_e2e_isLeibniz
    let PS := finiteGibbsCEParityOnsagerSystem H3 hH3_sa hZ3_pos X3 H3 hX3_sa hH3_sa
    let D := faithfulGibbsDensity H3 hH3_sa hZ3_pos
    let hpow := continuous_faithfulGibbsDensity_rpow H3 hH3_sa hZ3_pos
    let K := realDerivationsLane (GibbsOperator 3)
    let PP2 := centeredBKMOnsagerFormPairing_ofValueParity D hpow H3 hH3_sa ![d_super, d_br]
    let Γ_ce := oneFormAlternatingLinearEquiv K (exteriorDerivativeZero K X3)
    PS.dissipative d_super d_br =
        centeredBKMRealCovariance D hpow
          (PureNonCommutativeOperatorSpine.genV P3.1 A3 C3 * X3 -
            X3 * PureNonCommutativeOperatorSpine.genV P3.1 A3 C3) (D_br X3) ∧
      PS.reversible d_super d_br = ceCurvatureBKMProbeForm D hpow X3 H3 d_super d_br ∧
      PP2.totalGenerator (PP2.T.op (ceCurvature K Γ_ce)) (PP2.T.op (ceCurvature K Γ_ce)) =
        PP2.totalGenerator (ceCurvature K Γ_ce) (ceCurvature K Γ_ce) ∧
      d_super ≠ 0 ∧
      PS.dissipative d_super d_br ≠ 0 ∧
      PP2.totalGenerator (ceCurvature K Γ_ce) (ceCurvature K Γ_ce) ≠ 0 := by
  intro P3 A3 C3 X3 H3 hH3_sa hZ3_pos hX3_sa D_br d_super d_br PS D hpow K PP2 Γ_ce
  have hbridge := gapDB_superBraided_ceBKM_curvature_bridge P3 A3 C3 H3 X3 H3
    hH3_sa hZ3_pos hX3_sa hH3_sa D_br D_br_e2e_isLeibniz
  have hgenV : matrixOfOp (PureNonCommutativeOperatorSpine.genV P3.1 A3 C3) =
      !![(1 : ℂ), 0, 0; 0, 0, 0; 0, 0, 1] := by
    dsimp [PureNonCommutativeOperatorSpine.genV, PureNonCommutativeOperatorSpine.anticomm,
      PureNonCommutativeOperatorSpine.conePlus, PureNonCommutativeOperatorSpine.coneMinus]
    simp only [matrixOfOp_add, matrixOfOp_mul_eq, matrixOfOp_sub_eq, matrixOfOp_one_eq]
    rw [show matrixOfOp P3.1 = P3_mat_e2e from matrixOfOp_matrixOp _,
      show matrixOfOp A3 = !![(0 : ℂ), 0, 1; 0, 0, 0; 0, 0, 0] from matrixOfOp_matrixOp _,
      show matrixOfOp C3 = !![(0 : ℂ), 0, 0; 0, 0, 0; 1, 0, 0] from matrixOfOp_matrixOp _]
    ext i j
    simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.sub_apply, Matrix.one_apply,
      Fin.sum_univ_three]
    fin_cases i <;> fin_cases j <;> (simp [P3_mat_e2e]; try norm_num)
  let X_sup : GibbsOperator 3 := matrixOp !![(0 : ℂ), 1, 0; -1, 0, 0; 0, 0, 0]
  let Y_ext : GibbsOperator 3 := matrixOp !![(0 : ℂ), 0, -1; 0, 0, 0; 1, 0, 0]
  have hsuper_eq : PureNonCommutativeOperatorSpine.genV P3.1 A3 C3 * X3 -
      X3 * PureNonCommutativeOperatorSpine.genV P3.1 A3 C3 = X_sup := by
    apply matrixOfOp_injective
    rw [matrixOfOp_sub_eq, matrixOfOp_mul_eq, matrixOfOp_mul_eq, hgenV,
      show matrixOfOp X3 = !![(0 : ℂ), 1, 0; 1, 0, 0; 0, 0, 0] from matrixOfOp_matrixOp _,
      show matrixOfOp X_sup = !![(0 : ℂ), 1, 0; -1, 0, 0; 0, 0, 0] from matrixOfOp_matrixOp _]
    ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.mul_apply, Fin.sum_univ_three]
  have hd_super_X3 : d_super.1 X3 = X_sup := by
    have hpair : d_super.1 X3 =
        PureNonCommutativeOperatorSpine.genV P3.1 A3 C3 * X3 -
          X3 * PureNonCommutativeOperatorSpine.genV P3.1 A3 C3 := by
      change InfoGeometry.OperatorAlgebra.PeirceGradedSuperderivations.differentialPlus P3.1 A3
          (InfoGeometry.OperatorAlgebra.PeirceGradedSuperderivations.differentialMinus P3.1 C3 X3) +
        InfoGeometry.OperatorAlgebra.PeirceGradedSuperderivations.differentialMinus P3.1 C3
          (InfoGeometry.OperatorAlgebra.PeirceGradedSuperderivations.differentialPlus P3.1 A3 X3) = _
      simpa [PureNonCommutativeOperatorSpine.comm] using
        InfoGeometry.OperatorAlgebra.PeirceGradedSuperderivations.differentialPlus_differentialMinus_pair
          A3 C3 X3 P3.property
    exact hpair.trans hsuper_eq
  have hd_br_X3 : D_br X3 = X_sup + Y_ext := by
    apply matrixOfOp_injective
    change matrixOfOp (B_br_e2e * X3 - X3 * B_br_e2e) = matrixOfOp (X_sup + Y_ext)
    rw [matrixOfOp_sub_eq, matrixOfOp_mul_eq, matrixOfOp_mul_eq, matrixOfOp_add,
      show matrixOfOp B_br_e2e = !![(1 : ℂ), 0, 0; 0, 0, 1; 0, 1, 0] from matrixOfOp_matrixOp _,
      show matrixOfOp X3 = !![(0 : ℂ), 1, 0; 1, 0, 0; 0, 0, 0] from matrixOfOp_matrixOp _,
      show matrixOfOp X_sup = !![(0 : ℂ), 1, 0; -1, 0, 0; 0, 0, 0] from matrixOfOp_matrixOp _,
      show matrixOfOp Y_ext = !![(0 : ℂ), 0, -1; 0, 0, 0; 1, 0, 0] from matrixOfOp_matrixOp _]
    ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.mul_apply, Fin.sum_univ_three]
  have hd_super_ne : d_super ≠ 0 := by
    intro h0
    have hX0 : d_super.1 X3 = 0 := by rw [h0]; rfl
    have hm := congrArg (fun M : GibbsOperator 3 => matrixOfOp M 0 1) (hd_super_X3.symm.trans hX0)
    rw [show matrixOfOp X_sup = !![(0 : ℂ), 1, 0; -1, 0, 0; 0, 0, 0] from matrixOfOp_matrixOp _,
      matrixOfOp_zero] at hm
    norm_num at hm
  let U3 : GibbsOperator 3 := matrixOp !![(1 : ℂ), 0, 0; 0, 1, 0; 0, 0, -1]
  have hU3_sa : IsSelfAdjoint U3 := by
    rw [isSelfAdjoint_iff]; apply matrixOfOp_injective
    change matrixOfOp (ContinuousLinearMap.adjoint U3) = matrixOfOp U3
    dsimp only [U3]; rw [matrixOfOp_adjoint, matrixOfOp_matrixOp]
    ext i j; fin_cases i <;> fin_cases j <;> simp
  have hU3_sq : U3 * U3 = 1 := by
    apply matrixOfOp_injective
    rw [matrixOfOp_mul_eq, matrixOfOp_one_eq,
      show matrixOfOp U3 = !![(1 : ℂ), 0, 0; 0, 1, 0; 0, 0, -1] from matrixOfOp_matrixOp _]
    ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.mul_apply, Fin.sum_univ_three]
  let τ3 := adGammaStarAlgEquiv U3 hU3_sa hU3_sq
  have hComm_H3_U3 : Commute H3 U3 := by
    rw [Commute, SemiconjBy]; apply matrixOfOp_injective
    rw [matrixOfOp_mul_eq, matrixOfOp_mul_eq,
      show matrixOfOp H3 = !![(1 : ℂ), 0, 0; 0, 2, 0; 0, 0, 3] from matrixOfOp_matrixOp _,
      show matrixOfOp U3 = !![(1 : ℂ), 0, 0; 0, 1, 0; 0, 0, -1] from matrixOfOp_matrixOp _]
    ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.mul_apply, Fin.sum_univ_three]
  have hτ3_rho : τ3 D.rho = D.rho :=
    adGammaStarAlgEquiv_gibbs_fixed H3 U3 hH3_sa hZ3_pos hU3_sa hU3_sq hComm_H3_U3
  have hτ3_tr := adGammaStarAlgEquiv_trace_re U3 hU3_sa hU3_sq
  have hτ3_X : τ3 X_sup = X_sup := by
    apply matrixOfOp_injective
    change matrixOfOp (U3 * X_sup * U3) = matrixOfOp X_sup
    rw [matrixOfOp_mul_eq, matrixOfOp_mul_eq,
      show matrixOfOp U3 = !![(1 : ℂ), 0, 0; 0, 1, 0; 0, 0, -1] from matrixOfOp_matrixOp _,
      show matrixOfOp X_sup = !![(0 : ℂ), 1, 0; -1, 0, 0; 0, 0, 0] from matrixOfOp_matrixOp _]
    ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.mul_apply, Fin.sum_univ_three]
  have hτ3_Y : τ3 Y_ext = -Y_ext := by
    apply matrixOfOp_injective
    change matrixOfOp (U3 * Y_ext * U3) = matrixOfOp (-Y_ext)
    rw [matrixOfOp_mul_eq, matrixOfOp_mul_eq, matrixOfOp_neg_eq,
      show matrixOfOp U3 = !![(1 : ℂ), 0, 0; 0, 1, 0; 0, 0, -1] from matrixOfOp_matrixOp _,
      show matrixOfOp Y_ext = !![(0 : ℂ), 0, -1; 0, 0, 0; 1, 0, 0] from matrixOfOp_matrixOp _]
    ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.mul_apply, Fin.sum_univ_three]
  have hortho3 : centeredBKMRealCovariance D hpow X_sup Y_ext = 0 := by
    have hinv := centeredBKMRealCovariance_aut τ3 D hpow hτ3_rho hτ3_tr X_sup Y_ext
    rw [hτ3_X, hτ3_Y, ← centeredBKMRealCovarianceBilin_apply, _root_.map_neg,
      centeredBKMRealCovarianceBilin_apply] at hinv
    linarith
  have hXsup_not_gauge : X_sup ∉ scalarGauge 3 := by
    apply matrixOp_ne_scalarGauge X_sup 0 1 (by decide)
    rw [show matrixOfOp X_sup = !![(0 : ℂ), 1, 0; -1, 0, 0; 0, 0, 0] from matrixOfOp_matrixOp _]
    norm_num
  have hdiss_ne : PS.dissipative d_super d_br ≠ 0 := by
    rw [hbridge.1, hsuper_eq, hd_br_X3, ← centeredBKMRealCovarianceBilin_apply,
      (centeredBKMRealCovarianceBilin D hpow X_sup).map_add X_sup Y_ext,
      centeredBKMRealCovarianceBilin_apply, centeredBKMRealCovarianceBilin_apply,
      hortho3, add_zero]
    exact ne_of_gt (centeredBKMRealCovariance_self_pos_of_not_scalarGauge hH3_sa hZ3_pos X_sup hXsup_not_gauge)
  have hcurv_val : ceCurvature K Γ_ce ![d_super, d_br] =
      matrixOp !![(0 : ℂ), 0, 0; 0, 0, 1; 0, -1, 0] := by
    dsimp only [Γ_ce]
    have hvec0 : (![d_super, d_br] 0) = d_super := rfl
    have hvec1 : (![d_super, d_br] 1) = d_br := rfl
    have hcw : ∀ (Γ : DerivationDifferentialForms.OneForm K) (x y : K.L),
        (DerivationDifferentialForms.connectionWedgeSquare K Γ).1 x y = Γ x * Γ y - Γ y * Γ x :=
      fun _ _ _ => rfl
    rw [ceCurvature_eq, twoCochainEquivDerivationOperatorForm_apply, hvec0, hvec1,
      connectionCurvature, exteriorDerivativeOne_exteriorDerivativeZero, zero_add,
      hcw, exteriorDerivativeZero_apply, exteriorDerivativeZero_apply]
    have hdsuper_act : K.operatorAction d_super X3 = X_sup := hd_super_X3
    have hdbr_act : K.operatorAction d_br X3 = X_sup + Y_ext := hd_br_X3
    rw [hdsuper_act, hdbr_act]
    apply matrixOfOp_injective
    rw [matrixOfOp_sub_eq, matrixOfOp_mul_eq, matrixOfOp_mul_eq, matrixOfOp_add,
      show matrixOfOp X_sup = !![(0 : ℂ), 1, 0; -1, 0, 0; 0, 0, 0] from matrixOfOp_matrixOp _,
      show matrixOfOp Y_ext = !![(0 : ℂ), 0, -1; 0, 0, 0; 1, 0, 0] from matrixOfOp_matrixOp _,
      matrixOfOp_matrixOp]
    ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.mul_apply, Fin.sum_univ_three]
  have hcurv_not_gauge : matrixOp !![(0 : ℂ), 0, 0; 0, 0, 1; 0, -1, 0] ∉ scalarGauge 3 := by
    apply matrixOp_ne_scalarGauge _ 1 2 (by decide)
    rw [matrixOfOp_matrixOp]
    norm_num
  have hrev_zero : PP2.reversible (ceCurvature K Γ_ce) (ceCurvature K Γ_ce) = 0 := by
    have hsk := PP2.reversible_skew (ceCurvature K Γ_ce) (ceCurvature K Γ_ce)
    linarith
  have htot_ne : PP2.totalGenerator (ceCurvature K Γ_ce) (ceCurvature K Γ_ce) ≠ 0 := by
    dsimp [OnsagerCasimirSystem.totalGenerator]
    rw [hrev_zero, add_zero, centeredBKMOnsagerFormPairing_ofValueParity_dissipative, hcurv_val]
    exact ne_of_gt (centeredBKMRealCovariance_self_pos_of_not_scalarGauge hH3_sa hZ3_pos _ hcurv_not_gauge)
  exact ⟨hbridge.1, rfl, centeredBKM_ceCurvature_reciprocity PP2 Γ_ce Γ_ce,
    hd_super_ne, hdiss_ne, htot_ne⟩

section Tier3_CD_01_L2

open scoped Matrix.Norms.L2Operator

/-- `T3-CD-01`: `gapCD_modularDerivation_metriplecticFlow_secondLaw` coupling `Modular.TimeSemigroup.Derivation` to `GenericMetriplecticFlow.System`. -/
theorem t3_cd_01_modularDerivationMetriplecticFlow :
    let dZ : NonAssocDerivation.derivations ℤ Mat2R := innerIntDerivation K1_real
    let D_mod : InfoGeometry.Modular.TimeSemigroup.Derivation Mat2R :=
      timeSemigroupDerivationEquivDerivations.symm dZ
    let readout : NonAssocDerivation.derivations ℤ Mat2R →+ Mat2R :=
      { toFun := fun d => (d : Module.End ℤ Mat2R) K2_real
        map_zero' := rfl
        map_add' := fun _ _ => rfl }
    let v_diss : Mat2R := readout (timeSemigroupDerivationEquivDerivations D_mod)
    let Φ : Mat2R → ℝ := fun M => -Matrix.trace (star v_diss * M)
    let dΦ : Mat2R → (Mat2R →L[ℝ] ℝ) := fun _ =>
      let L_dΦ : Mat2R →ₗ[ℝ] ℝ :=
        { toFun := fun M => -Matrix.trace (star v_diss * M)
          map_add' := fun A B => by rw [Matrix.mul_add, Matrix.trace_add, neg_add]
          map_smul' := fun r A => by simp }
      { toLinearMap := L_dΦ
        cont := LinearMap.continuous_of_finiteDimensional L_dΦ }
    let x : ℝ → Mat2R := fun t => t • v_diss
    let sys : ℝ → GenericMetriplecticFlow.System Mat2R := fun _ =>
      { dH := 0
        dS :=
          { toFun := fun M => (1 / 8 : ℝ) * Matrix.trace (star v_diss * M)
            map_add' := fun A B => by rw [Matrix.mul_add, Matrix.trace_add, mul_add]
            map_smul' := fun r A => by
              simp only [RingHom.id_apply, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
              exact mul_left_comm _ _ _ }
        L := 0
        M :=
          { toFun := fun α => (α v_diss) • v_diss
            map_add' := fun α β => by simp [add_smul]
            map_smul' := fun r α => by simp [smul_smul] }
        L_skew := fun _ _ => by simp
        L_entropy_casimir := by simp
        M_symmetric := fun α β => by
          change α ((β v_diss) • v_diss) = β ((α v_diss) • v_diss)
          simp only [_root_.map_smul, smul_eq_mul]
          exact mul_comm _ _
        M_hamiltonian_casimir := by simp
        M_nonneg := fun α => by
          change 0 ≤ α ((α v_diss) • v_diss)
          simp only [_root_.map_smul, smul_eq_mul]
          exact mul_self_nonneg _ }
    (D_mod (K2_real * K2_real) = D_mod K2_real * K2_real + K2_real * D_mod K2_real) ∧
      (∀ t ∈ interior (Set.Icc (0 : ℝ) 1),
        HasDerivAt (fun s => Φ (x s)) (dΦ (x t) ((sys t).M (sys t).dS)) t ∧
        dΦ (x t) ((sys t).M (sys t).dS) ≤ 0) ∧
      AntitoneOn (fun s => Φ (x s)) (Set.Icc 0 1) := by
  intro dZ D_mod readout v_diss Φ dΦ x sys
  have hv_tr : Matrix.trace (star v_diss * v_diss) = 8 := by
    change Matrix.trace (star (K1_real * K2_real - K2_real * K1_real) *
      (K1_real * K2_real - K2_real * K1_real)) = 8
    norm_num [K1_real, K2_real, Matrix.trace, Matrix.diag, Matrix.mul_apply,
      Matrix.star_apply, Fin.sum_univ_two]
  have hdiss_eq : ∀ t ∈ interior (Set.Icc (0 : ℝ) 1),
      (sys t).M (sys t).dS = readout (timeSemigroupDerivationEquivDerivations D_mod) := by
    intro t _
    change ((1 / 8 : ℝ) * Matrix.trace (star v_diss * v_diss)) • v_diss = v_diss
    rw [hv_tr]
    norm_num
  have hcont : ContinuousOn (fun s => Φ (x s)) (Set.Icc 0 1) := by
    have hlin : Continuous (fun s : ℝ => -Matrix.trace (star v_diss * (s • v_diss))) := by
      have heq : (fun s : ℝ => -Matrix.trace (star v_diss * (s • v_diss))) =
          fun s : ℝ => -(s * 8) := by
        funext s
        rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, hv_tr]
      rw [heq]
      exact (continuous_id.mul continuous_const).neg
    exact hlin.continuousOn
  have hΦ : ∀ t ∈ interior (Set.Icc (0 : ℝ) 1), HasFDerivAt Φ (dΦ (x t)) (x t) := fun t _ =>
    (dΦ (x t)).hasFDerivAt
  have hx : ∀ t ∈ interior (Set.Icc (0 : ℝ) 1),
      HasDerivAt x ((sys t).L (sys t).dH +
        readout (timeSemigroupDerivationEquivDerivations D_mod)) t := by
    intro t _
    change HasDerivAt (fun s : ℝ => s • v_diss) (0 + v_diss) t
    rw [zero_add]
    simpa using ((hasDerivAt_id t).smul_const v_diss)
  have hdiss : ∀ t ∈ interior (Set.Icc (0 : ℝ) 1),
      dΦ (x t) (readout (timeSemigroupDerivationEquivDerivations D_mod)) ≤ 0 := by
    intro t _
    change -Matrix.trace (star v_diss * v_diss) ≤ 0
    rw [hv_tr]
    norm_num
  exact gapCD_modularDerivation_metriplecticFlow_secondLaw D_mod readout K2_real sys Φ dΦ x
    (convex_Icc 0 1) hcont hΦ hdiss_eq hx (fun t _ => (dΦ (x t)).map_zero) hdiss

end Tier3_CD_01_L2

/-- `T3-CD-02`: `gapCD_exceptionalSuperDerivation_metriplecticFlow_secondLaw` coupling `H3ZornF4Derivations` (`f4Basis 0`) to `GenericMetriplecticFlow.System ℝ`. -/
theorem t3_cd_02_exceptionalSuperDerivationMetriplecticFlow :
    let d_f4 : InfoGeometry.Algebra.H3ZornF4Derivations :=
      ⟨(InfoGeometry.Algebra.f4Basis 0).1, (InfoGeometry.Algebra.f4Basis 0).2⟩
    let x_zorn := InfoGeometry.Algebra.h3_diag₁
    let y_zorn := InfoGeometry.Algebra.h3_diag₁
    let embed : InfoGeometry.Algebra.H3Zorn ℝ →ₗ[ℝ] ℝ :=
      { toFun := fun Z => Z.a.a
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    let v_val : ℝ := embed (h3ZornF4DerivationLane.operatorAction d_f4 (x_zorn * y_zorn))
    let sys : ℝ → GenericMetriplecticFlow.System ℝ := fun _ =>
      { dH := 0
        dS := (LinearMap.id (R := ℝ) (M := ℝ)).smulRight v_val
        L := 0
        M :=
          { toFun := fun α => (α 1) • 1
            map_add' := fun α β => by
              change (α 1 + β 1) • (1 : ℝ) = α 1 • 1 + β 1 • 1
              rw [add_smul]
            map_smul' := fun r α => by
              change (r • α 1) • (1 : ℝ) = r • (α 1 • 1)
              rw [smul_smul]; rfl }
        L_skew := fun _ _ => by simp
        L_entropy_casimir := by simp
        M_symmetric := fun α β => by
          change α (β 1 • 1) = β (α 1 • 1)
          rw [_root_.map_smul, _root_.map_smul, smul_eq_mul, smul_eq_mul, mul_comm]
        M_hamiltonian_casimir := by simp
        M_nonneg := fun α => by
          change 0 ≤ α (α 1 • 1)
          rw [_root_.map_smul, smul_eq_mul]
          exact mul_self_nonneg (α 1) }
    let H_fn : ℝ → ℝ := fun _ => 0
    let S_fn : ℝ → ℝ := fun r => r * v_val
    let x : ℝ → ℝ := fun t => t * v_val
    h3ZornF4DerivationLane.operatorAction d_f4 (x_zorn * y_zorn) =
        h3ZornF4DerivationLane.operatorAction d_f4 x_zorn * y_zorn +
          x_zorn * h3ZornF4DerivationLane.operatorAction d_f4 y_zorn ∧
      (∀ t ∈ interior (Set.Icc (0 : ℝ) 1),
        HasDerivAt (fun s => H_fn (x s) - 1 * S_fn (x s))
          (-(1 * (sys t).dS (embed (h3ZornF4DerivationLane.operatorAction d_f4 (x_zorn * y_zorn))))) t ∧
        -(1 * (sys t).dS (embed (h3ZornF4DerivationLane.operatorAction d_f4 (x_zorn * y_zorn)))) < 0) ∧
      AntitoneOn (fun s => H_fn (x s) - 1 * S_fn (x s)) (Set.Icc 0 1) := by
  intro d_f4 x_zorn y_zorn embed v_val sys H_fn S_fn x
  have hv_ne : v_val ≠ 0 := by
    intro h0
    have hdiag_sq : InfoGeometry.Algebra.candidateJordanMul InfoGeometry.Algebra.h3_diag₁
        InfoGeometry.Algebra.h3_diag₁ = InfoGeometry.Algebra.h3_diag₁ := by
      apply InfoGeometry.Algebra.H3Zorn.ext_h3 <;>
        (simp only [InfoGeometry.Algebra.candidateJordanMul,
          InfoGeometry.Algebra.H3Zorn.T, InfoGeometry.Algebra.H3Zorn.U,
          InfoGeometry.Algebra.H3Zorn.crossProduct, InfoGeometry.Algebra.H3Zorn.adjointQuad,
          InfoGeometry.Algebra.H3Zorn.traceBilin,
          InfoGeometry.Algebra.H3Zorn.add_readback, InfoGeometry.Algebra.H3Zorn.sub_readback,
          InfoGeometry.Algebra.H3Zorn.smul_readback, InfoGeometry.Algebra.H3Zorn.one_readback,
          InfoGeometry.Algebra.h3_diag₁, InfoGeometry.Algebra.ZornVectorMatrix.add,
          InfoGeometry.Algebra.ZornVectorMatrix.sub, InfoGeometry.Algebra.ZornVectorMatrix.neg,
          InfoGeometry.Algebra.ZornVectorMatrix.smul, InfoGeometry.Algebra.ZornVectorMatrix.zero,
          InfoGeometry.Algebra.ZornVectorMatrix.conj, InfoGeometry.Algebra.ZornVectorMatrix.mul,
          InfoGeometry.Algebra.ZornVectorMatrix.norm, InfoGeometry.Algebra.ZornVectorMatrix.trace,
          InfoGeometry.Algebra.ZornVec3.dot, InfoGeometry.Algebra.ZornVec3.cross,
          Fin.sum_univ_three]; try norm_num)
      all_goals (ext i <;> simp)
    have hoff_mul_diag : InfoGeometry.Algebra.candidateJordanMul (InfoGeometry.Algebra.h3_off₁₂ 0)
        InfoGeometry.Algebra.h3_diag₁ = (1 / 2 : ℝ) • InfoGeometry.Algebra.h3_off₁₂ 0 := by
      apply InfoGeometry.Algebra.H3Zorn.ext_h3 <;>
        (simp only [InfoGeometry.Algebra.candidateJordanMul,
          InfoGeometry.Algebra.H3Zorn.T, InfoGeometry.Algebra.H3Zorn.U,
          InfoGeometry.Algebra.H3Zorn.crossProduct, InfoGeometry.Algebra.H3Zorn.adjointQuad,
          InfoGeometry.Algebra.H3Zorn.traceBilin,
          InfoGeometry.Algebra.H3Zorn.add_readback, InfoGeometry.Algebra.H3Zorn.sub_readback,
          InfoGeometry.Algebra.H3Zorn.smul_readback, InfoGeometry.Algebra.H3Zorn.one_readback,
          InfoGeometry.Algebra.h3_diag₁, InfoGeometry.Algebra.h3_off₁₂, InfoGeometry.Algebra.zorn_basis,
          InfoGeometry.Algebra.ZornVectorMatrix.add, InfoGeometry.Algebra.ZornVectorMatrix.sub,
          InfoGeometry.Algebra.ZornVectorMatrix.neg, InfoGeometry.Algebra.ZornVectorMatrix.smul,
          InfoGeometry.Algebra.ZornVectorMatrix.zero, InfoGeometry.Algebra.ZornVectorMatrix.conj,
          InfoGeometry.Algebra.ZornVectorMatrix.mul, InfoGeometry.Algebra.ZornVectorMatrix.norm,
          InfoGeometry.Algebra.ZornVectorMatrix.trace, InfoGeometry.Algebra.ZornVec3.dot,
          InfoGeometry.Algebra.ZornVec3.cross, Fin.sum_univ_three]; try norm_num)
    have hdiag_mul_off : InfoGeometry.Algebra.candidateJordanMul InfoGeometry.Algebra.h3_diag₁
        (InfoGeometry.Algebra.h3_off₁₂ 0) = (1 / 2 : ℝ) • InfoGeometry.Algebra.h3_off₁₂ 0 := by
      rw [InfoGeometry.Algebra.candidateJordanMul_comm, hoff_mul_diag]
    dsimp [v_val, embed, h3ZornF4DerivationLane, d_f4, x_zorn, y_zorn,
      InfoGeometry.Algebra.f4Basis] at h0
    change (((InfoGeometry.Algebra.candidateJordanMul InfoGeometry.Algebra.h3_diag₁
        (InfoGeometry.Algebra.candidateJordanMul (InfoGeometry.Algebra.h3_off₁₂ 0)
          (InfoGeometry.Algebra.candidateJordanMul InfoGeometry.Algebra.h3_diag₁
            InfoGeometry.Algebra.h3_diag₁)) -
      InfoGeometry.Algebra.candidateJordanMul (InfoGeometry.Algebra.h3_off₁₂ 0)
        (InfoGeometry.Algebra.candidateJordanMul InfoGeometry.Algebra.h3_diag₁
          (InfoGeometry.Algebra.candidateJordanMul InfoGeometry.Algebra.h3_diag₁
            InfoGeometry.Algebra.h3_diag₁))).a.a)) = 0 at h0
    rw [hdiag_sq, hoff_mul_diag, InfoGeometry.Algebra.candidateJordanMul_smul_right,
      hdiag_mul_off, hdiag_sq, hoff_mul_diag] at h0
    simp only [InfoGeometry.Algebra.H3Zorn.sub_readback, InfoGeometry.Algebra.H3Zorn.smul_readback,
      InfoGeometry.Algebra.h3_off₁₂, InfoGeometry.Algebra.zorn_basis,
      InfoGeometry.Algebra.ZornVectorMatrix.sub, InfoGeometry.Algebra.ZornVectorMatrix.neg,
      InfoGeometry.Algebra.ZornVectorMatrix.smul] at h0
    norm_num at h0
  let dH_clm : ℝ → (ℝ →L[ℝ] ℝ) := fun _ => 0
  let dS_clm : ℝ → (ℝ →L[ℝ] ℝ) := fun _ => (ContinuousLinearMap.id ℝ ℝ).smulRight v_val
  have hcont : ContinuousOn (fun s => H_fn (x s) - 1 * S_fn (x s)) (Set.Icc 0 1) :=
    ((continuous_const.sub (continuous_const.mul ((continuous_id.mul continuous_const).mul
      continuous_const)))).continuousOn
  have hS : ∀ t ∈ interior (Set.Icc (0 : ℝ) 1), HasFDerivAt S_fn (dS_clm t) (x t) := by
    intro t _
    have hsm : S_fn = dS_clm t := by
      ext r
      simp [S_fn, dS_clm, smul_eq_mul]
    rw [hsm]
    exact (dS_clm t).hasFDerivAt
  have hx : ∀ t ∈ interior (Set.Icc (0 : ℝ) 1), HasDerivAt x (sys t).flow t := by
    intro t _
    have hflow : (sys t).flow = v_val := by
      simp [GenericMetriplecticFlow.System.flow, sys, v_val, smul_eq_mul]
    rw [hflow]
    simpa using ((hasDerivAt_id t).mul_const v_val)
  have hgap := gapCD_exceptionalSuperDerivation_metriplecticFlow_secondLaw d_f4 x_zorn y_zorn
    embed sys H_fn S_fn (T := 1) (by norm_num) dH_clm dS_clm x (convex_Icc 0 1) hcont
    (fun _ _ _ => rfl) (fun _ _ _ => rfl)
    (fun _ _ => hasFDerivAt_const _ _) hS
    (fun _ _ => by simp [sys, v_val, smul_eq_mul]) hx
  refine ⟨hgap.1, fun t ht => ?_, hgap.2.2⟩
  refine ⟨(hgap.2.1 t ht).2.1, ?_⟩
  have hneg : -(1 * (sys t).dS v_val) = -(v_val * v_val) := by
    simp [sys, smul_eq_mul]
  rw [hneg]
  exact neg_lt_zero.mpr (mul_self_pos.mpr hv_ne)

section Tier3_GapAC_L2

open scoped Matrix.Norms.L2Operator

/-- `T3-AC-01`: `gapAC_cartanSchur_metriplecticFlow_secondLaw` with `𝔨`-reversible and `𝔭`-dissipative flow on `FiniteOperatorAlgebra 2`. -/
theorem t3_ac_01_cartanSchurMetriplecticFlow :
    let u1 : FiniteOperatorAlgebra 2 := A_swap
    let u2 : FiniteOperatorAlgebra 2 := 1
    let up : FiniteOperatorAlgebra 2 := tiltOp2
    let dH_clm : FiniteOperatorAlgebra 2 →L[ℝ] ℝ :=
      { toLinearMap := hsRealBilinForm 2 u1
        cont := LinearMap.continuous_of_finiteDimensional _ }
    let dS_clm : FiniteOperatorAlgebra 2 →L[ℝ] ℝ :=
      { toLinearMap := hsRealBilinForm 2 up
        cont := LinearMap.continuous_of_finiteDimensional _ }
    let sys : ℝ → GenericMetriplecticFlow.System (FiniteOperatorAlgebra 2) := fun _ =>
      { dH := hsRealBilinForm 2 u1
        dS := hsRealBilinForm 2 up
        L :=
          { toFun := fun α => α u2 • u1 - α u1 • u2
            map_add' := fun α β => by
              change (α u2 + β u2) • u1 - (α u1 + β u1) • u2 =
                (α u2 • u1 - α u1 • u2) + (β u2 • u1 - β u1 • u2)
              simp only [real_smul_eq_complex_smul, Complex.ofReal_add]
              rw [add_smul _ _ u1, add_smul _ _ u2]
              abel
            map_smul' := fun r α => by
              change (r * α u2) • u1 - (r * α u1) • u2 = r • (α u2 • u1 - α u1 • u2)
              simp only [smul_sub, smul_smul] }
        M :=
          { toFun := fun α => α up • up
            map_add' := fun α β => by
              change (α up + β up) • up = α up • up + β up • up
              simp only [real_smul_eq_complex_smul, Complex.ofReal_add]
              exact add_smul _ _ up
            map_smul' := fun r α => by
              change (r * α up) • up = r • (α up • up)
              rw [smul_smul] }
        L_skew := fun α β => by
          change α (β u2 • u1 - β u1 • u2) = -β (α u2 • u1 - α u1 • u2)
          simp only [_root_.map_sub, _root_.map_smul, smul_eq_mul]
          ring
        L_entropy_casimir := by
          have hdS1 : dS_clm u1 = 0 := by
            change hsRealBilinForm 2 tiltOp2 A_swap = 0
            rw [hsRealBilinForm_apply, ← switchOp2_eq_A_swap, tiltOp2_isSelfAdjoint.star_eq]
            have hanti : tiltOp2 * switchOp2 = -(switchOp2 * tiltOp2) := by
              rw [tiltOp2_switchOp2_anticomm]
            have htr : finiteOperatorTrace (tiltOp2 * switchOp2) =
                -finiteOperatorTrace (tiltOp2 * switchOp2) := by
              calc finiteOperatorTrace (tiltOp2 * switchOp2)
                  = finiteOperatorTrace (-(switchOp2 * tiltOp2)) := by rw [hanti]
                _ = -finiteOperatorTrace (switchOp2 * tiltOp2) := (finiteOperatorTraceLinear 2).map_neg _
                _ = -finiteOperatorTrace (tiltOp2 * switchOp2) := by rw [finiteOperatorTrace_mul_comm]
            have hre := congrArg Complex.re htr
            rw [Complex.neg_re] at hre
            linarith
          have hdS2 : dS_clm u2 = 0 := by
            change hsRealBilinForm 2 tiltOp2 (1 : FiniteOperatorAlgebra 2) = 0
            rw [hsRealBilinForm_apply, tiltOp2_isSelfAdjoint.star_eq, mul_one]
            change (Matrix.trace (matrixOfOp tiltOp2)).re = 0
            rw [tiltOp2, matrixOfOp_matrixOp]
            norm_num [Matrix.trace, Matrix.diag, InfoGeometry.Physics.KleinBottleSewingExact.tilt2,
              Fin.sum_univ_two]
          change (hsRealBilinForm 2 up u2) • u1 - (hsRealBilinForm 2 up u1) • u2 = 0
          rw [show hsRealBilinForm 2 up u1 = 0 from hdS1, show hsRealBilinForm 2 up u2 = 0 from hdS2,
            real_smul_eq_complex_smul, real_smul_eq_complex_smul, Complex.ofReal_zero,
            zero_smul ℂ u1, zero_smul ℂ u2, sub_self]
        M_symmetric := fun α β => by
          change α (β up • up) = β (α up • up)
          simp only [_root_.map_smul, smul_eq_mul, mul_comm]
        M_hamiltonian_casimir := by
          have hdH_p : dH_clm up = 0 := by
            change hsRealBilinForm 2 A_swap tiltOp2 = 0
            rw [hsRealBilinForm_symm 2 A_swap tiltOp2, hsRealBilinForm_apply,
              ← switchOp2_eq_A_swap, tiltOp2_isSelfAdjoint.star_eq]
            have hanti : tiltOp2 * switchOp2 = -(switchOp2 * tiltOp2) := by
              rw [tiltOp2_switchOp2_anticomm]
            have htr : finiteOperatorTrace (tiltOp2 * switchOp2) =
                -finiteOperatorTrace (tiltOp2 * switchOp2) := by
              calc finiteOperatorTrace (tiltOp2 * switchOp2)
                  = finiteOperatorTrace (-(switchOp2 * tiltOp2)) := by rw [hanti]
                _ = -finiteOperatorTrace (switchOp2 * tiltOp2) := (finiteOperatorTraceLinear 2).map_neg _
                _ = -finiteOperatorTrace (tiltOp2 * switchOp2) := by rw [finiteOperatorTrace_mul_comm]
            have hre := congrArg Complex.re htr
            rw [Complex.neg_re] at hre
            linarith
          change (hsRealBilinForm 2 u1 up) • up = 0
          rw [show hsRealBilinForm 2 u1 up = 0 from hdH_p, real_smul_eq_complex_smul,
            Complex.ofReal_zero, zero_smul ℂ up]
        M_nonneg := fun α => by
          change 0 ≤ α (α up • up)
          simp only [_root_.map_smul, smul_eq_mul]
          exact mul_self_nonneg _ }
    let H_fn : FiniteOperatorAlgebra 2 → ℝ := fun X => dH_clm X
    let S_fn : FiniteOperatorAlgebra 2 → ℝ := fun X => dS_clm X
    let x : ℝ → FiniteOperatorAlgebra 2 := fun t => t • ((sys 0).flow)
    0 ≤ triad_pos.block.effectiveEvenOnsager ∧
      (∀ t ∈ interior (Set.Icc (0 : ℝ) 1),
        (sys t).dH (sys t).flow = 0 ∧
        HasDerivAt (fun s => H_fn (x s) - 1 * S_fn (x s))
          (-(1 * (sys t).dS ((sys t).M (sys t).dS))) t ∧
        -(1 * (sys t).dS ((sys t).M (sys t).dS)) < 0) ∧
      AntitoneOn (fun s => H_fn (x s) - 1 * S_fn (x s)) (Set.Icc 0 1) := by
  intro u1 u2 up dH_clm dS_clm sys H_fn S_fn x
  let C := peirceCartanOnsagerSplit P_d63
  have hForce : triad_pos.entropy.bodyForce ≠ 0 := by norm_num [triad_pos]
  have hu1_k : u1 ∈ C.drazinCore := by
    rw [C.drazinCore_eq_k]
    change u1 ∈ (peirceSymmetricLieAlgebra P_d63).evenSubmodule
    rw [(peirceSymmetricLieAlgebra P_d63).mem_evenSubmodule_iff]
    change invS P_d63.1 * A_swap * invS P_d63.1 = A_swap
    rw [invS_P_d63_eq_A_swap]
    apply matrixOfOp_injective
    rw [matrixOfOp_mul_eq, matrixOfOp_mul_eq, A_swap, matrixOfOp_matrixOp]
    ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [swapMatrix, Matrix.mul_apply, Fin.sum_univ_two]
  have hu2_k : u2 ∈ C.drazinCore := by
    rw [C.drazinCore_eq_k]
    change u2 ∈ (peirceSymmetricLieAlgebra P_d63).evenSubmodule
    rw [(peirceSymmetricLieAlgebra P_d63).mem_evenSubmodule_iff]
    change invS P_d63.1 * 1 * invS P_d63.1 = 1
    rw [mul_one, invS_P_d63_eq_A_swap]
    apply matrixOfOp_injective
    rw [matrixOfOp_mul_eq, matrixOfOp_one_eq, A_swap, matrixOfOp_matrixOp]
    ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [swapMatrix, Matrix.mul_apply, Fin.sum_univ_two]
  have hup_p : up ∈ C.dissipativeRange := by
    rw [C.dissipativeRange_eq_p]
    change up ∈ (peirceSymmetricLieAlgebra P_d63).oddSubmodule
    rw [(peirceSymmetricLieAlgebra P_d63).mem_oddSubmodule_iff]
    change invS P_d63.1 * tiltOp2 * invS P_d63.1 = -tiltOp2
    apply matrixOfOp_injective
    rw [matrixOfOp_neg_eq, matrixOfOp_mul_eq, matrixOfOp_mul_eq, invS_P_d63_eq_A_swap,
      A_swap, tiltOp2, matrixOfOp_matrixOp, matrixOfOp_matrixOp]
    ext i j; fin_cases i <;> fin_cases j <;>
      (simp only [swapMatrix, InfoGeometry.Physics.KleinBottleSewingExact.tilt2,
        Matrix.mul_apply, Matrix.neg_apply, Matrix.of_apply,
        Matrix.cons_val_zero, Matrix.cons_val_one, Fin.sum_univ_two];
        norm_num)
  have hL_k : ∀ t ∈ interior (Set.Icc (0 : ℝ) 1), (sys t).L (sys t).dH ∈ C.drazinCore := by
    intro t _
    exact C.drazinCore.sub_mem (C.drazinCore.smul_mem _ hu1_k) (C.drazinCore.smul_mem _ hu2_k)
  have hM_p : ∀ t ∈ interior (Set.Icc (0 : ℝ) 1), (sys t).M (sys t).dS ∈ C.dissipativeRange := by
    intro t _
    exact C.dissipativeRange.smul_mem _ hup_p
  have hcont : ContinuousOn (fun s => H_fn (x s) - 1 * S_fn (x s)) (Set.Icc 0 1) :=
    ((dH_clm.continuous.comp ((continuous_id).smul continuous_const)).sub
      (continuous_const.mul (dS_clm.continuous.comp ((continuous_id).smul continuous_const)))).continuousOn
  have hx : ∀ t ∈ interior (Set.Icc (0 : ℝ) 1), HasDerivAt x (sys t).flow t := by
    intro t _
    simpa using ((hasDerivAt_id t).smul_const ((sys 0).flow))
  have hgap := gapAC_cartanSchur_metriplecticFlow_secondLaw C triad_pos hForce sys H_fn S_fn
    (T := 1) (by norm_num) (fun _ => dH_clm) (fun _ => dS_clm) x (convex_Icc 0 1) hcont
    (fun _ _ _ => rfl) (fun _ _ _ => rfl)
    (fun _ _ => dH_clm.hasFDerivAt) (fun _ _ => dS_clm.hasFDerivAt)
    hx hL_k hM_p
  have hdS_up : dS_clm up = 2 := by
    change (Matrix.trace (matrixOfOp (star tiltOp2 * tiltOp2))).re = 2
    rw [tiltOp2_isSelfAdjoint.star_eq, tiltOp2_sq, matrixOfOp_one_eq, Matrix.trace_one,
      Fintype.card_fin]
    norm_num
  refine ⟨by norm_num [triad_pos, B_ns, ScalarSchurDrazinBlock.effectiveEvenOnsager], fun t ht => ?_, hgap.2.2⟩
  have hderiv : HasDerivAt (fun s => H_fn (x s) - 1 * S_fn (x s))
      (-(1 * (sys t).dS ((sys t).M (sys t).dS))) t := by
    have hd := (dH_clm.hasFDerivAt.comp_hasDerivAt t (hx t ht)).sub
      ((dS_clm.hasFDerivAt.comp_hasDerivAt t (hx t ht)).const_mul 1)
    have hL0 : (sys t).dS ((sys t).L (sys t).dH) = 0 := by
      rw [(sys t).L_skew, (sys t).L_entropy_casimir, _root_.map_zero, neg_zero]
    have hrate : dH_clm (sys t).flow - 1 * dS_clm (sys t).flow =
        -(1 * (sys t).dS ((sys t).M (sys t).dS)) := by
      change (sys t).dH (sys t).flow - 1 * (sys t).dS ((sys t).L (sys t).dH + (sys t).M (sys t).dS) = _
      rw [(hgap.1 t ht).2.2, _root_.map_add, hL0, zero_add, zero_sub]
    rwa [hrate] at hd
  refine ⟨(hgap.1 t ht).2.2, hderiv, ?_⟩
  have hneg : -(1 * (sys t).dS ((sys t).M (sys t).dS)) = -4 := by
    change -(1 * dS_clm (dS_clm up • up)) = -4
    rw [dS_clm.map_smul, smul_eq_mul, hdS_up]
    norm_num
  rw [hneg]
  norm_num

/-- `T3-AC-02`: `gapAC_peirceCut_matrixKuboMori_secondLaw` + concrete `t = 0` noncommuting Peirce-projected witness. -/
theorem t3_ac_02_peirceCutMatrixKuboMori :
    (∀ (H : ℝ → FiniteOperatorAlgebra 2) (I : Set ℝ), Convex ℝ I →
      ∀ (hH : ∀ t ∈ I, IsSelfAdjoint (H t)),
      (∀ t (ht : t ∈ I), HasDerivAt H
        (gibbsUnitaryVectorField switchOp2 (H t) -
          ((faithfulGibbsDensity (H t) (hH t ht)
            (tracedExponential_re_pos_of_isSelfAdjoint (H t) (hH t ht))).rho -
            (1 / 2 : ℝ) • (1 : FiniteOperatorAlgebra 2))) t) →
      AntitoneOn (fun s => traceNormalizedSquarePotential
        (matrixOfOp ((1 / 2 : ℝ) • (1 : FiniteOperatorAlgebra 2)))
        (matrixOfOp (normalizedExponential (H s)))) I) ∧
      (cutDerivation P_d63 ((peirceCartanLinearEquiv P_d63 tiltOp2).1 : FiniteOperatorAlgebra 2) = 0 ∧
        cutDerivation P_d63 (cutDerivation P_d63 tiltOp2) =
          ((peirceCartanLinearEquiv P_d63 tiltOp2).2 : FiniteOperatorAlgebra 2) ∧
        HasDerivAt
          (fun s : ℝ => traceNormalizedSquarePotential
            (matrixOfOp ((1 / 2 : ℝ) • (1 : FiniteOperatorAlgebra 2)))
            (matrixOfOp (normalizedExponential (tiltOp2 + s •
              (gibbsUnitaryVectorField switchOp2 tiltOp2 -
                ((faithfulGibbsDensity tiltOp2 tiltOp2_isSelfAdjoint
                  (tracedExponential_re_pos_of_isSelfAdjoint tiltOp2 tiltOp2_isSelfAdjoint)).rho -
                  (1 / 2 : ℝ) • (1 : FiniteOperatorAlgebra 2)))))))
          (MetriplecticDissipation.freeEnergyRate
            (evolvingGibbsMetriplecticSystem switchOp2
              ((1 / 2 : ℝ) • (1 : FiniteOperatorAlgebra 2)) tiltOp2 tiltOp2_isSelfAdjoint)) 0 ∧
        deriv
          (fun s : ℝ => traceNormalizedSquarePotential
            (matrixOfOp ((1 / 2 : ℝ) • (1 : FiniteOperatorAlgebra 2)))
            (matrixOfOp (normalizedExponential (tiltOp2 + s •
              (gibbsUnitaryVectorField switchOp2 tiltOp2 -
                ((faithfulGibbsDensity tiltOp2 tiltOp2_isSelfAdjoint
                  (tracedExponential_re_pos_of_isSelfAdjoint tiltOp2 tiltOp2_isSelfAdjoint)).rho -
                  (1 / 2 : ℝ) • (1 : FiniteOperatorAlgebra 2))))))) 0 < 0) := by
  have hσ_sa : IsSelfAdjoint ((1 / 2 : ℝ) • (1 : FiniteOperatorAlgebra 2)) :=
    isSelfAdjoint_real_smul _ _ (by rw [isSelfAdjoint_iff, star_one])
  have hcomm_σ : Commute ((1 / 2 : ℝ) • (1 : FiniteOperatorAlgebra 2)) switchOp2 := by
    rw [Commute, SemiconjBy, real_smul_eq_complex_smul, smul_mul_assoc, mul_smul_comm,
      one_mul, mul_one]
  refine ⟨fun H I hI hH hflow =>
      (gapAC_peirceCut_matrixKuboMori_secondLaw P_d63 switchOp2
        ((1 / 2 : ℝ) • (1 : FiniteOperatorAlgebra 2)) switchOp2_isSelfAdjoint hσ_sa hcomm_σ
        H hI hH hflow).2.2,
    ?_, ?_, ?_⟩
  · rw [(peirceCartanLinearEquiv_apply P_d63 tiltOp2).1]
    exact cutDerivation_evenGrade_zero P_d63 tiltOp2
  · rw [(peirceCartanLinearEquiv_apply P_d63 tiltOp2).2]
    exact cutDerivation_square_eq_oddGrade P_d63 tiltOp2
  · let σ : FiniteOperatorAlgebra 2 := (1 / 2 : ℝ) • (1 : FiniteOperatorAlgebra 2)
    let v0 := gibbsUnitaryVectorField switchOp2 tiltOp2 -
      ((faithfulGibbsDensity tiltOp2 tiltOp2_isSelfAdjoint
        (tracedExponential_re_pos_of_isSelfAdjoint tiltOp2 tiltOp2_isSelfAdjoint)).rho - σ)
    let H_curve : ℝ → FiniteOperatorAlgebra 2 := fun s => tiltOp2 + s • v0
    have hH0 : H_curve 0 = tiltOp2 := ContinuousLinearMap.ext fun _ => by simp [H_curve]
    have hH0_sa : IsSelfAdjoint (H_curve 0) := hH0.symm ▸ tiltOp2_isSelfAdjoint
    have hderiv0 : HasDerivAt H_curve
        (gibbsUnitaryVectorField switchOp2 (H_curve 0) -
          ((faithfulGibbsDensity (H_curve 0) hH0_sa
            (tracedExponential_re_pos_of_isSelfAdjoint (H_curve 0) hH0_sa)).rho - σ)) 0 := by
      have h1 := hasDerivAt_add_real_smul tiltOp2 v0 0
      simpa only [hH0] using h1
    have hres := hasDerivAt_traceNormalizedSquarePotential_gibbsTrajectory switchOp2 σ
      switchOp2_isSelfAdjoint hσ_sa hcomm_σ H_curve (t := 0) hH0_sa hderiv0
    have hhas : HasDerivAt
        (fun s : ℝ => traceNormalizedSquarePotential (matrixOfOp σ)
          (matrixOfOp (normalizedExponential (tiltOp2 + s • v0))))
        (MetriplecticDissipation.freeEnergyRate
          (evolvingGibbsMetriplecticSystem switchOp2 σ tiltOp2 tiltOp2_isSelfAdjoint)) 0 := by
      simpa only [hH0] using hres.1
    refine ⟨hhas, ?_⟩
    rw [hhas.deriv]
    let hZ_t := tracedExponential_re_pos_of_isSelfAdjoint tiltOp2 tiltOp2_isSelfAdjoint
    let D_t := faithfulGibbsDensity tiltOp2 tiltOp2_isSelfAdjoint hZ_t
    let hD_t := continuous_faithfulGibbsDensity_rpow tiltOp2 tiltOp2_isSelfAdjoint hZ_t
    have hD_t_rho : D_t.rho = σ + (Real.tanh 1 / 2) • tiltOp2 := by
      have hexp : NormedSpace.exp tiltOp2 =
          Real.cosh 1 • (1 : FiniteOperatorAlgebra 2) + Real.sinh 1 • tiltOp2 := by
        simpa using exp_real_smul_tiltOp2 1
      have htr1 : finiteOperatorTrace (1 : FiniteOperatorAlgebra 2) = 2 := by
        change Matrix.trace (matrixOfOp (1 : FiniteOperatorAlgebra 2)) = 2
        rw [matrixOfOp_one_eq]; norm_num [Matrix.trace, Matrix.diag, Fin.sum_univ_two]
      have htr_tilt : finiteOperatorTrace tiltOp2 = 0 := by
        change Matrix.trace (matrixOfOp tiltOp2) = 0
        rw [matrixOfOp_tiltOp2]
        norm_num [InfoGeometry.Physics.KleinBottleSewingExact.tilt2, Matrix.trace, Matrix.diag,
          Fin.sum_univ_two]
      have hZ_eq : gibbsPartitionReal tiltOp2 = 2 * Real.cosh 1 := by
        have htr : tracedExponential tiltOp2 = ((2 * Real.cosh 1 : ℝ) : ℂ) := by
          unfold tracedExponential
          rw [hexp, real_smul_eq_complex_smul, real_smul_eq_complex_smul,
            (finiteOperatorTraceCLM 2).map_add, (finiteOperatorTraceCLM 2).map_smul,
            (finiteOperatorTraceCLM 2).map_smul]
          change (Real.cosh 1 : ℂ) • finiteOperatorTrace 1 +
              (Real.sinh 1 : ℂ) • finiteOperatorTrace tiltOp2 = _
          rw [htr1, htr_tilt, smul_eq_mul, smul_eq_mul, mul_zero, add_zero]
          push_cast; ring
        exact congrArg Complex.re htr
      dsimp only [D_t, σ]
      erw [faithfulGibbsDensity_rho_eq_normalizedExponential]
      unfold normalizedExponential
      rw [tracedExponential_eq_gibbsPartitionReal tiltOp2 tiltOp2_isSelfAdjoint, hZ_eq, hexp]
      have hcosh_ne : Real.cosh 1 ≠ 0 := ne_of_gt (Real.cosh_pos 1)
      have hinv_smul : ∀ (c : ℝ) (X : FiniteOperatorAlgebra 2), ((c : ℂ)⁻¹) • X = (c⁻¹ : ℝ) • X := by
        intro c X; rw [← Complex.ofReal_inv, ← real_smul_eq_complex_smul]
      rw [hinv_smul (2 * Real.cosh 1), smul_add, smul_smul, smul_smul]
      congr 1
      · congr 1; field_simp [hcosh_ne]
      · congr 1; rw [Real.tanh_eq_sinh_div_cosh]; field_simp [hcosh_ne]
    have hdiff_eq : D_t.rho - σ = (Real.tanh 1 / 2) • tiltOp2 := by
      rw [hD_t_rho, add_sub_cancel_left]
    have hnot_gauge : D_t.rho - σ ∉ scalarGauge 2 := by
      intro hmem
      obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp hmem
      rw [hdiff_eq] at hr
      have hm0 := congrArg (fun M : FiniteOperatorAlgebra 2 => (matrixOfOp M 0 0).re) hr
      have hm1 := congrArg (fun M : FiniteOperatorAlgebra 2 => (matrixOfOp M 1 1).re) hr
      rw [matrixOfOp_real_smul, matrixOfOp_real_smul, matrixOfOp_one_eq, matrixOfOp_tiltOp2]
        at hm0 hm1
      simp only [InfoGeometry.Physics.KleinBottleSewingExact.tilt2, Matrix.smul_apply,
        Matrix.one_apply, smul_eq_mul, Fin.isValue, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, Complex.one_re, Complex.neg_re, mul_one] at hm0 hm1
      have ht : 0 < Real.tanh 1 := tanh_pos_of_pos one_pos
      linarith
    have hgrad_ne : centeredStatistic D_t (D_t.rho - σ) ≠ 0 :=
      fun h0 => hnot_gauge ((centeredStatistic_eq_zero_iff D_t hD_t (D_t.rho - σ)).mp h0)
    have hgrad_sa : IsSelfAdjoint (centeredStatistic D_t (D_t.rho - σ)) := by
      rw [isSelfAdjoint_iff]
      unfold centeredStatistic
      rw [real_smul_eq_complex_smul]
      change ContinuousLinearMap.adjoint
          ((D_t.rho - σ) - (expectationReal D_t (D_t.rho - σ) : ℂ) • (1 : FiniteOperatorAlgebra 2)) =
        (D_t.rho - σ) - (expectationReal D_t (D_t.rho - σ) : ℂ) • (1 : FiniteOperatorAlgebra 2)
      rw [map_sub]
      change star (D_t.rho - σ) -
          star ((expectationReal D_t (D_t.rho - σ) : ℂ) • (1 : FiniteOperatorAlgebra 2)) = _
      rw [(D_t.strictlyPositive.isSelfAdjoint.sub hσ_sa).star_eq, star_smul, star_one,
        Complex.star_def, Complex.conj_ofReal]
    let sys0 := evolvingGibbsMetriplecticSystem switchOp2 σ tiltOp2 tiltOp2_isSelfAdjoint
    have hstar_gradF : star sys0.grad_F = sys0.grad_F := by
      change (matrixOfOp (centeredStatistic D_t (D_t.rho - σ))).conjTranspose =
        matrixOfOp (centeredStatistic D_t (D_t.rho - σ))
      rw [← matrixOfOp_adjoint, hgrad_sa.adjoint_eq]
    have hrev_zero :
        (Matrix.trace (star sys0.grad_F *
          (-Complex.I • (sys0.H * sys0.rho - sys0.rho * sys0.H)))).re = 0 := by
      rw [hstar_gradF]
      dsimp only [sys0, evolvingGibbsMetriplecticSystem]
      have hcomm_D : Commute switchOp2 D_t.rho = Commute switchOp2 D_t.rho := rfl
      have hgrad_mat : matrixOfOp (centeredStatistic D_t (D_t.rho - σ)) =
          (Real.tanh 1 / 2 : ℂ) • InfoGeometry.Physics.KleinBottleSewingExact.tilt2 -
            (expectationReal D_t (D_t.rho - σ) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
        unfold centeredStatistic
        rw [hdiff_eq, matrixOfOp_sub_eq, matrixOfOp_real_smul, matrixOfOp_real_smul,
          matrixOfOp_tiltOp2, matrixOfOp_one_eq]
        push_cast; rfl
      have hrho_mat : matrixOfOp D_t.rho =
          (1 / 2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) +
            (Real.tanh 1 / 2 : ℂ) • InfoGeometry.Physics.KleinBottleSewingExact.tilt2 := by
        rw [hD_t_rho]
        dsimp only [σ]
        rw [matrixOfOp_add, matrixOfOp_real_smul, matrixOfOp_real_smul,
          matrixOfOp_one_eq, matrixOfOp_tiltOp2]
        simp [Complex.ofReal_div]
      rw [hgrad_mat, hrho_mat]
      have hswitch : matrixOfOp switchOp2 = InfoGeometry.Physics.KleinBottleSewingExact.switch2 :=
        matrixOfOp_matrixOp _
      rw [hswitch]
      simp only [InfoGeometry.Physics.KleinBottleSewingExact.switch2,
        InfoGeometry.Physics.KleinBottleSewingExact.tilt2,
        Matrix.trace, Matrix.diag, Fin.sum_univ_two, Matrix.mul_apply,
        Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply,
        smul_eq_mul, Fin.isValue]
      norm_num
    have hdiss_pos :
        0 < (Matrix.trace (star sys0.grad_F * sys0.Onsager sys0.grad_F)).re := by
      change 0 < (Matrix.trace (star (matrixOfOp (centeredStatistic D_t (D_t.rho - σ))) *
        matrixKuboMoriMobility D_t hD_t (matrixOfOp (centeredStatistic D_t (D_t.rho - σ))))).re
      rw [matrixKuboMoriMobility_trace_eq_bkm D_t hD_t (matrixOfOp (centeredStatistic D_t (D_t.rho - σ))),
        matrixOp_matrixOfOp, hgrad_sa.star_eq]
      exact D_t.kuboMoriPairing_self_re_pos (centeredStatistic D_t (D_t.rho - σ)) hD_t hgrad_ne
    change (Matrix.trace (star sys0.grad_F *
        (-Complex.I • (sys0.H * sys0.rho - sys0.rho * sys0.H) - sys0.Onsager sys0.grad_F))).re < 0
    rw [Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re, hrev_zero, zero_sub]
    exact neg_lt_zero.mpr hdiss_pos

end Tier3_GapAC_L2

end Tier3_Tests

/-! ## Section 5: Tier 4 — Real-World End-to-End Scenarios (`T4-SC-01`..`T4-SC-05`) -/

section Tier4_Tests

attribute [local instance 100] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

/-- `T4-SC-01`: Noncommutative `2×2` Quantum Gibbs–BKM Relaxation Pipeline across all 4 pillars. -/
theorem t4_sc_01_quantumGibbsBkmRelaxationPipeline :
    let S := capstoneQubitSpine
    let D1 := innerFrechetComplexDeriv (Complex.I • tiltOp2)
    let D2 := innerFrechetComplexDeriv (Complex.I • tiltOp2 + tiltOp2 * switchOp2)
    let x1 := finiteCEFrechetDirection D1
    let x2 := finiteCEFrechetDirection D2
    let A1 := finiteCEOperatorForm 2 switchOp2 x1
    let A2 := finiteCEOperatorForm 2 switchOp2 x2
    let a_fam : Fin 2 → GibbsOperator 2 := ![A_swap, B_tilt]
    let ha_fam : ∀ i, IsSelfAdjoint (a_fam i) := fun i => by
      fin_cases i; exact hA_swap_sa; exact hB_tilt_sa
    let datum := gibbsNOperatorFamilyStarErlangenDatum (G := Unit)
      H_d63 hH_d63_sa hZ_d63_pos a_fam ha_fam ![1, 2] B_tilt hB_tilt_sa
    (switchOp2 * tiltOp2 ≠ tiltOp2 * switchOp2) ∧
      (0 < S.ceParitySystem.dissipative x1 x1) ∧
      (0 < (secondFDerivLogPartitionReadout tiltOp2 A1 A2).re) ∧
      (S.ceParitySystem.reversible x1 x2 ≠ 0) ∧
      (frechetExtDeriv (logPartitionOneForm 2) tiltOp2 ![A1, A2] = 0) ∧
      (S.ceParitySystem.totalGenerator (S.ceParitySystem.T.op x1) (S.ceParitySystem.T.op x2) =
        S.ceParitySystem.totalGenerator x2 x1) ∧
      HasJReciprocity datum.onsagerPairing
        (familyTimeReversal 2 (starDerivationTimeReversal 2)).op ∧
      AntitoneOn (fun s : ℝ => Φ_norm_swap (matrixOfOp (normalizedExponential (B_tilt + s • A_swap))))
        (Set.Icc (0 : ℝ) 1) := by
  intro S D1 D2 x1 x2 A1 A2 a_fam ha_fam datum
  have hw := capstone_qubit_nondegenerate_witness
  have herl := t1_f4_06_erlangenDatumSpecialization
  have htraj := t1_f6_05_freeEnergyMatrixKuboMoriMobility
  exact ⟨hw.1, hw.2.1, hw.2.2.1, hw.2.2.2.1, hw.2.2.2.2.1, hw.2.2.2.2.2.1, herl.1, htraj.2.2⟩

/-- `T4-SC-02`: Black-Hole / Peirce `d63` Cartan-Split Metriplectic Evolution (`F1` + `F2` + `F3` + `F6` + `F8` + `F9`) on strictly decreasing Gibbs trajectory. -/
theorem t4_sc_02_blackHolePeirceCartanMetriplectic :
    let K := peirceCutDerivationLieLane 2
    let C := peirceCartanOnsagerSplit P_d63
    let P_sys := cartanParityOnsagerSystemOfForms C (hsRealBilinForm 2)
      (hsRealBilinForm_symm 2) (hsRealBilinForm_nonneg 2) (hsProbeBilinForm 2 tiltOp2)
    let P_conf := conformalBlockCanonicalParityOnsagerSystem conformalBlock_nc
    let P3 : FiniteOperatorAlgebra 3 := matrixOp !![(1 : ℂ), 0, 0; 0, 1, 0; 0, 0, 0]
    let hP3 : P3 * P3 = P3 := by
      apply matrixOfOp_injective
      rw [matrixOfOp_mul_eq, show matrixOfOp P3 = !![(1 : ℂ), 0, 0; 0, 1, 0; 0, 0, 0] from matrixOfOp_matrixOp _]
      ext i j; fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply, Fin.sum_univ_three]
    let A3 : FiniteOperatorAlgebra 3 := matrixOp !![(0 : ℂ), 0, 1; 0, 0, 0; 0, 0, 0]
    let C3 : FiniteOperatorAlgebra 3 := matrixOp !![(0 : ℂ), 0, 0; 0, 0, 0; 1, 0, 0]
    let X3 : FiniteOperatorAlgebra 3 := matrixOp !![(0 : ℂ), 1, 0; 1, 0, 0; 0, 0, 0]
    let d_anti := superAnticommLinearToDerivations (PureNonCommutativeOperatorSpine.invS_sq hP3)
      (differentialPlusLinear_isOdd (R := ℝ) hP3 A3)
      (differentialMinusLinear_isOdd (R := ℝ) hP3 C3)
    let σ_mix : FiniteOperatorAlgebra 2 := (1 / 2 : ℝ) • (1 : FiniteOperatorAlgebra 2)
    let x_k := C.S.P_plus B_tilt
    let x_p := C.S.P_minus B_tilt
    (LinearMap.ker (peirceAdMap P_d63 ∘ₗ peirceAdMap P_d63) = C.S.𝔨 ∧
      LinearMap.range (peirceAdMap P_d63) = C.S.𝔭) ∧
      K.operatorAction ⁅peirceCutGenerator P_diag, peirceCutGenerator P_d63⁆ A_swap ≠ 0 ∧
      P_sys.totalGenerator (P_sys.T.op x_k) (P_sys.T.op x_p) =
        P_sys.totalGenerator x_p x_k ∧
      P_sys.totalGenerator x_p x_k ≠ 0 ∧
      P_sys.reversible x_k x_p ≠ 0 ∧
      0 < P_sys.totalGenerator B_tilt B_tilt ∧
      P_conf.totalGenerator (P_conf.T.op ![0, 1]) (P_conf.T.op ![1, 0]) =
        P_conf.totalGenerator ![1, 0] ![0, 1] ∧
      P_conf.totalGenerator ![1, 0] ![0, 1] ≠ 0 ∧
      0 < P_conf.dissipative ![1, 0] ![1, 0] ∧
      (d_anti : Module.End ℝ (FiniteOperatorAlgebra 3)) X3 ≠ 0 ∧
      AntitoneOn (fun s : ℝ => gibbsRelativePotential σ_mix (H_sol_curve s)) (Set.Icc (0 : ℝ) 1) ∧
      gibbsRelativePotential σ_mix (H_sol_curve 1) < gibbsRelativePotential σ_mix (H_sol_curve 0) :=
  ⟨t1_f3_02_peirceAdKerRange.1,
    t2_f3_03_noncommutingPeirceCuts,
    t1_f1_05_cartanMasterReciprocityAndEntropy.1,
    t1_f1_05_cartanMasterReciprocityAndEntropy.2.1,
    t1_f1_05_cartanMasterReciprocityAndEntropy.2.2.1,
    t1_f1_05_cartanMasterReciprocityAndEntropy.2.2.2.2.1,
    t1_f2_04_conformalOnsagerBlock.2.2.2.2.1,
    t1_f2_04_conformalOnsagerBlock.2.2.2.2.2.1,
    t1_f2_04_conformalOnsagerBlock.2.2.2.1,
    t1_f8_04_squareZeroAndPeirceSuperanticommutator.2.2.2,
    t1_f6_02_gibbsRelativePotentialMetriplectic.2.1,
    t1_f6_02_gibbsRelativePotentialMetriplectic.2.2⟩

/-- `T4-SC-03`: Singular Schur–Drazin Body-Force Dissipation with Defect Projector (`F1` + `F2` + `F6`). -/
theorem t4_sc_03_singularSchurDrazinBodyForcePipeline :
    let hEff_ns : 0 ≤ B_ns.effectiveEvenOnsager := by
      norm_num [B_ns, ScalarSchurDrazinBlock.effectiveEvenOnsager]
    let hEff_sing : 0 ≤ B_sing.effectiveEvenOnsager := by
      norm_num [B_sing, ScalarSchurDrazinBlock.effectiveEvenOnsager]
    let P_ns := scalarEffectiveParityOnsagerSystem B_ns hEff_ns
    let P_sing := scalarEffectiveParityOnsagerSystem B_sing hEff_sing
    let P_tkk := tkkParityOnsagerSystem M_tkk M_tkk_psd M_tkk_dual
    let P_2 := drazinCartanParityOnsagerSystemOfProbe B_real2 (EuclideanSpace.basisFun (Fin 2) ℝ 0) 0
    B_ns.drazinDefectProjector = 0 ∧
      B_ns.effectiveEvenOnsager = 3 ∧
      B_sing.drazinDefectProjector = 1 ∧
      B_sing.effectiveEvenOnsager = 4 ∧
      0 < triad_pos.entropy.production ∧
      0 < P_ns.dissipative 2 2 ∧
      0 < P_sing.dissipative 2 2 ∧
      P_tkk.totalGenerator (P_tkk.T.op (fun _ => 1)) (P_tkk.T.op (fun _ => 2)) =
        P_tkk.totalGenerator (fun _ => 2) (fun _ => 1) ∧
      P_tkk.totalGenerator (fun _ => 2) (fun _ => 1) ≠ 0 ∧
      0 < P_2.dissipative tilt_real2 tilt_real2 ∧
      AntitoneOn (fun s => (fun p : ℝ × ℝ => p.2 ^ 2) (s, Real.exp (-2 * s))) (Set.Icc 0 1) := by
  intro hEff_ns hEff_sing P_ns P_sing P_tkk P_2
  have htkk_ne : P_tkk.totalGenerator (fun _ => 2) (fun _ => 1) ≠ 0 := by
    change tkkSum (fun i => tkkSum (fun j => (2 : ℝ) * M_tkk.entry i j * 1)) + 0 ≠ 0
    norm_num [tkkSum, M_tkk]
  exact ⟨by norm_num [B_ns, ScalarSchurDrazinBlock.drazinDefectProjector],
    t1_f2_01_scalarSchurEffective.1,
    t2_f2_01_singularHiddenBlock.1,
    t2_f2_01_singularHiddenBlock.2.1,
    t2_f2_03_bodyForcePositivityVsZero.1,
    by rw [t1_f2_01_scalarSchurEffective.2.1]; norm_num,
    t2_f2_01_singularHiddenBlock.2.2.2,
    P_tkk.onsager_casimir_master_reciprocity (fun _ => 1) (fun _ => 2),
    htkk_ne,
    t1_f1_04_drazinCartanParityOnsagerSystem.2.2.2.2.2.1,
    t1_f6_01_banachMetriplecticFlow.2.1⟩

/-- `T4-SC-04`: KMS / Modular Tower Exterior-Calculus Gauge & Curvature Pairing (`F4` + `F5` + `F7`) with direct `Modular.*` witnesses. -/
theorem t4_sc_04_kmsModularExteriorCurvaturePipeline :
    let d1 : NonAssocDerivation.derivations ℤ Mat2R := innerIntDerivation K1_real
    let d2 : NonAssocDerivation.derivations ℤ Mat2R := innerIntDerivation K2_real
    let K := realDerivationsLane (GibbsOperator 2)
    let Γ := exteriorDerivativeZero K A_swap
    let D_kms : InfoGeometry.Modular.KMSState.LinearDerivation ℝ (GibbsOperator 2) :=
      kmsStateLinearDerivationEquivDerivations.symm
        (innerDerivation (matrixOp !![0, 1; -(1 / 2 : ℂ), 0]))
    let D_semi : InfoGeometry.Modular.SemidirectExterior.Derivation ℝ (GibbsOperator 2) :=
      semidirectDerivationEquivDerivations.symm
        (innerDerivation (matrixOp !![0, 1; (1 / 2 : ℂ), 0]))
    let K_diag : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℝ :=
      Matrix.fromBlocks matrixUnit01 0 0 matrixUnit01
    let D_outer : InfoGeometry.Modular.TrifoldSurprisalIntertwiningBridge.OuterDerivation (Fin 2) ℝ :=
      { toLinearMap :=
          { toFun := fun X => K_diag * X - X * K_diag
            map_add' := fun _ _ => by noncomm_ring
            map_smul' := fun r X => by
              change K_diag * (r • X) - (r • X) * K_diag = r • (K_diag * X - X * K_diag)
              rw [mul_smul_comm, smul_mul_assoc, smul_sub] }
        leibniz' := fun X Y => by
          change K_diag * (X * Y) - (X * Y) * K_diag =
            (K_diag * X - X * K_diag) * Y + X * (K_diag * Y - Y * K_diag)
          noncomm_ring
        map_one' := by simp
        map_gamma' := by
          change K_diag * InfoGeometry.Modular.TrifoldSurprisalIntertwiningBridge.GammaGrading -
            InfoGeometry.Modular.TrifoldSurprisalIntertwiningBridge.GammaGrading * K_diag = 0
          dsimp [K_diag, InfoGeometry.Modular.TrifoldSurprisalIntertwiningBridge.GammaGrading]
          rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
          simp }
    ⁅d1, d2⁆ ≠ 0 ∧
      D_kms.toLinearMap (matrixOp !![1, 0; 0, 2]) ≠ 0 ∧
      D_semi (matrixOp !![1, 0; 0, 2]) ≠ 0 ∧
      (outerDerivationToDerivations D_outer : Module.End ℝ (Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℝ))
        (Matrix.fromBlocks matrixUnit10 (0 : Mat2R) 0 0) ≠ 0 ∧
      ceCurvature K (oneFormAlternatingLinearEquiv K Γ) =
        twoCochainEquivDerivationOperatorForm K (connectionCurvature K Γ) ∧
      (Matrix.fromBlocks (0 : Mat2R) 1 0 0) *
        (InfoGeometry.Modular.TrifoldSurprisalIntertwiningBridge.GammaGrading :
          Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℝ) ≠
        (InfoGeometry.Modular.TrifoldSurprisalIntertwiningBridge.GammaGrading :
          Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℝ) *
        (Matrix.fromBlocks (0 : Mat2R) 1 0 0) ∧
      (∀ (D : Mat2R → Mat2R), D = (fun X => matrixUnit01 * X - X * matrixUnit01) →
        D (matrixUnit10 * matrixUnit01) ≠
          matrixUnit10 * D matrixUnit01 + matrixUnit01 * D matrixUnit10) ∧
      HasJReciprocity
        (gibbsNOperatorFamilyStarErlangenDatum (G := Unit) H_d63 hH_d63_sa hZ_d63_pos
          ![A_swap, B_tilt] (fun i => by fin_cases i; exact hA_swap_sa; exact hB_tilt_sa)
          ![1, 2] B_tilt hB_tilt_sa).onsagerPairing
        (familyTimeReversal 2 (starDerivationTimeReversal 2)).op := by
  intro d1 d2 K Γ D_kms D_semi K_diag D_outer
  have houter_ne :
      (outerDerivationToDerivations D_outer : Module.End ℝ (Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℝ))
        (Matrix.fromBlocks matrixUnit10 (0 : Mat2R) 0 0) ≠ 0 := by
    intro h0
    have hm := congrArg (fun M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℝ => M (Sum.inl 0) (Sum.inl 0)) h0
    change (K_diag * Matrix.fromBlocks matrixUnit10 (0 : Mat2R) (0 : Mat2R) (0 : Mat2R) -
      Matrix.fromBlocks matrixUnit10 (0 : Mat2R) (0 : Mat2R) (0 : Mat2R) * K_diag)
        (Sum.inl 0) (Sum.inl 0) = 0 at hm
    dsimp [K_diag] at hm
    rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply] at hm
    simp only [Matrix.mul_zero, zero_mul, add_zero, Matrix.fromBlocks_apply₁₁] at hm
    have h00 : (matrixUnit01 * matrixUnit10 - matrixUnit10 * matrixUnit01 : Mat2R) 0 0 = 0 := hm
    norm_num [matrixUnit01, matrixUnit10, Matrix.mul_apply, Fin.sum_univ_two] at h00
  refine ⟨t2_f7_04_modularNonAbelianBracket.1,
    t3_db_01_modularDerivationCeBkmParityForm.2.2.1,
    t3_db_01_modularDerivationCeBkmParityForm.2.2.2.1,
    houter_ne,
    t1_f5_03_ceCurvatureEqAndBkmProbe.1,
    t2_f7_02_outerDerivationProperSubtypeBoundary,
    fun D hD => by subst hD; exact t2_f7_01_scalarDerivationNoncommBoundary.1,
    t1_f4_06_erlangenDatumSpecialization.1⟩

/-- `T4-SC-05`: Exceptional Split-Octonion / Jordan / Super-Braided Non-Associative Derivation Spine (`F7` + `F8` + `F9`). -/
theorem t4_sc_05_exceptionalJordanSuperBraidedPipeline :
    ((InfoGeometry.Algebra.ZornVectorMatrix.U 0 : InfoGeometry.Algebra.ZornVectorMatrix ℝ) *
        InfoGeometry.Algebra.ZornVectorMatrix.U 1) *
        InfoGeometry.Algebra.ZornVectorMatrix.U 2 ≠
      InfoGeometry.Algebra.ZornVectorMatrix.U 0 *
        (InfoGeometry.Algebra.ZornVectorMatrix.U 1 *
          InfoGeometry.Algebra.ZornVectorMatrix.U 2) ∧
      ((h3ZornF4DerivationLane).operatorAction
        ⟨(InfoGeometry.Algebra.f4Basis 0).1, (InfoGeometry.Algebra.f4Basis 0).2⟩
        InfoGeometry.Algebra.h3_diag₁ ≠ 0) ∧
      (∃ X, (splitCayleyDerivationEquivIntDerivations
        InfoGeometry.Lie.RealSplitOctonionDerivation.rot01Derivation :
        Module.End ℤ (InfoGeometry.Canonical.ZornMatrix ℝ)) X ≠ 0) ∧
      ((g2ToBraidDerivationEquivVectorDerivations
        ⟨InfoGeometry.Lie.BaezG2SplitOctonion.rot01G2Derivation.1,
         InfoGeometry.Lie.BaezG2SplitOctonion.rot01G2Derivation.2⟩ :
        Module.End ℝ (InfoGeometry.Algebra.ZornVectorMatrix ℝ))
        (InfoGeometry.Algebra.ZornVectorMatrix.U 0) ≠ 0) ∧
      (oddTwistSuperderivationToGradedBraided
        (PureNonCommutativeOperatorSpine.invS_sq P_d63.property)
        (differentialPlusLinear ℝ P_d63.1 B_tilt)
        (differentialPlusLinear_isOdd (R := ℝ) P_d63.property B_tilt)).deg = 1 := by
  exact ⟨t2_f8_05_nonAssociativityWithLeibniz.1,
    t1_f8_03_zornJordanAndH3ZornDerivations.2.2.2,
    t1_f8_02_splitCayleyAndSplitOctonionDerivations.2.2.1,
    t1_f8_01_threeG2Derivations.2.2,
    t2_f8_04_braidedDegree1VsDegree0Boundary.1⟩

end Tier4_Tests

end InfoGeometry.Canonical.LeibnizDerivationFrechetOnsagerE2ETests
