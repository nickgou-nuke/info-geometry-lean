/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Clifford.Cl11SplitTowerMatrixEquiv
import InfoGeometry.Core.OperatorCliffordDouble
import InfoGeometry.Clifford.Cl30RealMatrixSignature
import InfoGeometry.Clifford.ThreeDHurwitz
import InfoGeometry.Algebra.Zorn.SplitOctonionPeirceG2Unification
import InfoGeometry.Algebra.Zorn.MatrixCayleyDicksonSeparation
import InfoGeometry.Clifford.Cl11TensorTowerLimit
import InfoGeometry.Canonical.BostConnesKMS
import InfoGeometry.Canonical.BostConnesColimitKMSBridge
import Mathlib.Tactic
import Lean.Util.CollectAxioms
import Lean.Elab.Command

set_option autoImplicit false

noncomputable section

namespace PolarizedZ2E2E.Tier2R4

open scoped TensorProduct Matrix
open InfoGeometry.CliffordTower
open InfoGeometry.Clifford.Cl11SplitTowerMatrixEquiv
open InfoGeometry.Core.OperatorCliffordDouble
open InfoGeometry.Clifford.Cl30RealMatrixSignature
open InfoGeometry.Clifford.ThreeDHurwitz
open InfoGeometry.Algebra.Zorn.SplitOctonionPeirceG2Unification
open InfoGeometry.Algebra.Zorn.MatrixCayleyDicksonSeparation
open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Clifford.Cl11TensorTowerLimit
open InfoGeometry.Canonical.BostConnesKMS
open InfoGeometry.Canonical.BostConnesColimitKMSBridge

/-! ## Local non-commutativity witnesses for T16 carrier compliance -/

private def localMat2E01 : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 0, 0]
private def localMat2E10 : Matrix (Fin 2) (Fin 2) ℝ := !![0, 0; 1, 0]

private theorem local_mat2_real_noncomm :
    localMat2E01 * localMat2E10 ≠ localMat2E10 * localMat2E01 := by
  intro h
  have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 0) h
  norm_num [localMat2E01, localMat2E10, Matrix.mul_apply, Fin.sum_univ_two] at h00

private theorem local_mat2_complex_noncomm :
    pauli1 * pauli2 ≠ pauli2 * pauli1 :=
  pauli1_mul_pauli2_ne

private theorem local_mat4_real_noncomm :
    (Matrix.single 0 1 (1 : ℝ) : Matrix (Fin 4) (Fin 4) ℝ) * Matrix.single 1 0 1 ≠
      Matrix.single 1 0 1 * Matrix.single 0 1 1 :=
  mat4R_noncommutative

private theorem local_mat8_real_noncomm :
    ∃ A B : Matrix (Fin 8) (Fin 8) ℝ, A * B ≠ B * A :=
  mat8_noncommutative

/-! ## Feature F13 Boundary & Separation -/

theorem t2_f13_stage_zero_1x1_boundary
    (A : Type*) [Ring A] [Algebra ℝ A] (x : Clsplit 0) (a : A) :
    cliffordTensorEquivMatrix 0 A (x ⊗ₜ[ℝ] a) 0 0 =
      a * algebraMap ℝ A (splitZeroEquivScalars x) := by
  rw [cliffordTensorEquivMatrix_tmul]
  have h0 : splitTowerEquivMatrix 0 x 0 0 = splitZeroEquivScalars x := by
    simp only [splitTowerEquivMatrix, Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply]
    rfl
  simp only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, h0]

theorem t2_f13_end_doubled_nontrivial_vs_subsingleton
    (R M : Type*) [CommSemiring R] [AddCommGroup M] [Module R M] :
    (Nontrivial M → ∃ T₁ T₂ : Module.End R (M × M), T₁ * T₂ ≠ T₂ * T₁) ∧
    (Subsingleton M → ∀ T₁ T₂ : Module.End R (M × M), Commute T₁ T₂) := by
  refine ⟨?_, ?_⟩
  · intro _
    obtain ⟨A, B, hAB⟩ := matrix_end_noncommutative (R := R) (M := M)
    refine ⟨blockMatrixAlgEquiv A, blockMatrixAlgEquiv B, ?_⟩
    exact (blockMatrixAlgEquiv_not_commute_iff A B).mpr hAB
  · intro _ T₁ T₂
    change T₁ * T₂ = T₂ * T₁
    apply LinearMap.ext
    intro x
    exact Subsingleton.elim _ _

theorem t2_f13_diracPlus_sq_commute_boundary_and_witness
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] (A B : Module.End R M) :
    (diracPlus A B ^ 2 = lift (A ^ 2 + B ^ 2) ↔ Commute A B) ∧
    (let A₀ : Module.End ℝ (Fin 2 → ℝ) := Matrix.toLin' !![(0 : ℝ), 1; 0, 0]
     let B₀ : Module.End ℝ (Fin 2 → ℝ) := Matrix.toLin' !![(0 : ℝ), 0; 1, 0]
     diracPlus A₀ B₀ ^ 2 ≠ lift (A₀ ^ 2 + B₀ ^ 2)) := by
  refine ⟨diracPlus_sq_eq_lift_iff A B, ?_⟩
  intro A₀ B₀ hEq
  have hcomm : Commute A₀ B₀ := (diracPlus_sq_eq_lift_iff A₀ B₀).mp hEq
  have hv := congrArg (fun f : Module.End ℝ (Fin 2 → ℝ) => f ![1, 0] 0) hcomm.eq
  norm_num [A₀, B₀, Module.End.mul_apply, Matrix.toLin'_apply, Matrix.mulVec,
    dotProduct, Fin.sum_univ_two] at hv

theorem t2_f13_includeLeft_nontrivial_vs_subsingleton_coeff
    (k : ℕ) (A : Type*) [Ring A] [Algebra ℝ A] :
    (Nontrivial A →
      Function.Injective (Algebra.TensorProduct.includeLeft : Clsplit k →ₐ[ℝ] Clsplit k ⊗[ℝ] A)) ∧
    (Subsingleton A →
      ∀ x y : Clsplit k, x ⊗ₜ[ℝ] (1 : A) = y ⊗ₜ[ℝ] (1 : A)) := by
  refine ⟨fun _ => includeLeft_injective k A, ?_⟩
  intro _ x y
  have h10 : (1 : A) = 0 := Subsingleton.elim 1 0
  rw [h10, TensorProduct.tmul_zero, TensorProduct.tmul_zero]

theorem t2_f13_includeRight_faithful_at_zero_and_all_stages
    (k : ℕ) (A : Type*) [Ring A] [Algebra ℝ A] (a b : A) :
    Function.Injective
      (Algebra.TensorProduct.includeRight : A →ₐ[ℝ] Clsplit 0 ⊗[ℝ] A) ∧
    Function.Injective
      (Algebra.TensorProduct.includeRight : A →ₐ[ℝ] Clsplit k ⊗[ℝ] A) ∧
    (Commute (cliffordTensorEquivMatrix k A ((1 : Clsplit k) ⊗ₜ[ℝ] a))
      (cliffordTensorEquivMatrix k A ((1 : Clsplit k) ⊗ₜ[ℝ] b)) ↔ Commute a b) := by
  exact ⟨includeRight_injective 0 A, includeRight_injective k A,
    cliffordTensorEquivMatrix_one_tmul_commute_iff k A a b⟩

/-! ## Feature F14 Boundary & Separation -/

theorem t2_f14_cl30_not_algEquiv_cl22_and_mat4R :
    ¬ Nonempty (Cl3 1 1 1 ≃ₐ[ℝ] Clsplit 2) ∧
    ¬ Nonempty (Matrix (Fin 2) (Fin 2) ℂ ≃ₐ[ℝ] Matrix (Fin 4) (Fin 4) ℝ) := by
  exact ⟨cl30_not_algEquiv_cl22, mat2C_not_algEquiv_mat4R⟩

theorem t2_f14_central_sq_neg_one_separation :
    (∃ z ∈ Subalgebra.center ℝ (Cl3 1 1 1), z ^ 2 = -1) ∧
    (∀ z ∈ Subalgebra.center ℝ (Clsplit 2), z ^ 2 ≠ -1) ∧
    (∃ z ∈ Subalgebra.center ℝ (Matrix (Fin 2) (Fin 2) ℂ), z ^ 2 = -1) ∧
    (∀ z ∈ Subalgebra.center ℝ (Matrix (Fin 4) (Fin 4) ℝ), z ^ 2 ≠ -1) := by
  exact ⟨cl30_exists_central_sq_neg_one, cl22_no_central_sq_neg_one,
    mat2C_exists_central_sq_neg_one, mat4R_no_central_sq_neg_one⟩

theorem t2_f14_center_not_algEquiv_separation :
    ¬ Nonempty (Subalgebra.center ℝ (Cl3 1 1 1) ≃ₐ[ℝ] Subalgebra.center ℝ (Clsplit 2)) ∧
    ¬ Nonempty (Subalgebra.center ℝ (Matrix (Fin 2) (Fin 2) ℂ) ≃ₐ[ℝ]
      Subalgebra.center ℝ (Matrix (Fin 4) (Fin 4) ℝ)) := by
  exact ⟨cl30_center_not_algEquiv_cl22_center, mat2C_center_not_algEquiv_mat4R_center⟩

theorem t2_f14_cl30_vs_cl11_and_cl03_signature_flip :
    pseudoscalar30 ^ 2 = (-1 : Cl3 1 1 1) ∧
    ((g0 (-1) (-1) (-1) * g1 (-1) (-1) (-1)) * g2 (-1) (-1) (-1)) ^ 2 =
      (1 : Cl3 (-1) (-1) (-1)) ∧
    ¬ Nonempty (Cl3 1 1 1 ≃ₐ[ℝ] Clsplit 1) := by
  refine ⟨pseudoscalar30_sq, ?_, ?_⟩
  · rw [sq, pseudoscalar_sq (-1) (-1) (-1)]
    norm_num
  · rintro ⟨e⟩
    have hdim := LinearEquiv.finrank_eq e.toLinearEquiv
    have h1 : Module.finrank ℝ (Clsplit 1) = 4 := by
      rw [LinearEquiv.finrank_eq (splitTowerEquivMatrix 1).toLinearEquiv]
      simp [Module.finrank_matrix]
    rw [cl30_finrank, h1] at hdim
    omega

theorem t2_f14_cl30_anticomm_vs_noncomm_generators :
    g0 1 1 1 * g1 1 1 1 + g1 1 1 1 * g0 1 1 1 = 0 ∧
    g0 1 1 1 * g1 1 1 1 ≠ g1 1 1 1 * g0 1 1 1 ∧
    (∃ a b : Clsplit 2, a * b ≠ b * a) := by
  refine ⟨?_, cl30_generators_noncommutative, cl22_noncommutative⟩
  simp only [g0_g1_anti, add_neg_cancel, neg_add_cancel]

/-! ## Feature F15 Boundary & Separation (including R5) -/

theorem t2_f15_r5_no_surj_mult_matrix_to_zorn :
    (¬ ∃ f : Matrix (Fin 2) (Fin 2) ℂ → ZornCarrier,
      Function.Surjective f ∧ ∀ A B, f (A * B) = f A * f B) ∧
    (¬ ∀ A B : Matrix (Fin 2) (Fin 2) ℂ,
      mat2CToZornCarrier (A * B) = mat2CToZornCarrier A * mat2CToZornCarrier B) := by
  exact ⟨no_surjective_multiplicative_mat2C_to_zornCarrier,
    mat2CToZornCarrier_not_multiplicative⟩

theorem t2_f15_r5_leftMulEnd_and_mat8_not_multiplicative :
    (∃ x y : ZornCarrier, leftMulEnd (x * y) ≠ leftMulEnd x ∘ₗ leftMulEnd y) ∧
    (∃ x y : ZornCarrier, leftMulMat8 (x * y) ≠ leftMulMat8 x * leftMulMat8 y) ∧
    (leftMulEnd (InfoGeometry.Lie.SplitOctonionImaginaryAction.ex_X.1 *
      InfoGeometry.Lie.SplitOctonionImaginaryAction.ex_Y.1) ≠
      leftMulEnd InfoGeometry.Lie.SplitOctonionImaginaryAction.ex_X.1 ∘ₗ
        leftMulEnd InfoGeometry.Lie.SplitOctonionImaginaryAction.ex_Y.1) ∧
    (leftMulMat8 (InfoGeometry.Lie.SplitOctonionImaginaryAction.ex_X.1 *
      InfoGeometry.Lie.SplitOctonionImaginaryAction.ex_Y.1) ≠
      leftMulMat8 InfoGeometry.Lie.SplitOctonionImaginaryAction.ex_X.1 *
        leftMulMat8 InfoGeometry.Lie.SplitOctonionImaginaryAction.ex_Y.1) := by
  exact ⟨leftMulEnd_not_multiplicative, leftMulMat8_not_multiplicative,
    imaginary_nonmultiplicativity_via_leftMulEnd,
    imaginary_nonmultiplicativity_via_leftMulMat8⟩

theorem t2_f15_peirceP_alternativity_vs_triple_associator :
    leftMulMat8 peirceP * leftMulMat8 peirceP = leftMulMat8 (peirceP * peirceP) ∧
    (peirceP * InfoGeometry.Canonical.ZornMatrix.chiralUpperBasis (R := ℝ) 0) *
        InfoGeometry.Canonical.ZornMatrix.chiralUpperBasis (R := ℝ) 1 ≠
      peirceP * (InfoGeometry.Canonical.ZornMatrix.chiralUpperBasis (R := ℝ) 0 *
        InfoGeometry.Canonical.ZornMatrix.chiralUpperBasis (R := ℝ) 1) := by
  refine ⟨?_, associator_peirceP_upper_witness.2⟩
  rw [leftMulMat8_multiplicative_iff_associator_zero]
  intro z
  unfold zornAssociator
  rw [sub_eq_zero]
  apply InfoGeometry.Canonical.ZornMatrix.ext
  · simp [peirceP, InfoGeometry.Canonical.ZornMatrix.zornPlus,
      InfoGeometry.Canonical.ZornMatrix.mul_def, InfoGeometry.Canonical.ZornMatrix.mul,
      InfoGeometry.Canonical.ZornMatrix.dot, InfoGeometry.Canonical.ZornMatrix.cross]
  · simp [peirceP, InfoGeometry.Canonical.ZornMatrix.zornPlus,
      InfoGeometry.Canonical.ZornMatrix.mul_def, InfoGeometry.Canonical.ZornMatrix.mul,
      InfoGeometry.Canonical.ZornMatrix.dot, InfoGeometry.Canonical.ZornMatrix.cross]
  · funext i; fin_cases i <;>
      simp [peirceP, InfoGeometry.Canonical.ZornMatrix.zornPlus,
        InfoGeometry.Canonical.ZornMatrix.mul_def, InfoGeometry.Canonical.ZornMatrix.mul,
        InfoGeometry.Canonical.ZornMatrix.dot, InfoGeometry.Canonical.ZornMatrix.cross]
  · funext i; fin_cases i <;>
      simp [peirceP, InfoGeometry.Canonical.ZornMatrix.zornPlus,
        InfoGeometry.Canonical.ZornMatrix.mul_def, InfoGeometry.Canonical.ZornMatrix.mul,
        InfoGeometry.Canonical.ZornMatrix.dot, InfoGeometry.Canonical.ZornMatrix.cross]

theorem t2_f15_peirce_bracketing_vs_nonassociativity (x : ZornCarrier) :
    ((peirceP * x) * peirceP = peirceP * (x * peirceP)) ∧
    ((peirceP * x) * (1 - peirceP) = peirceP * (x * (1 - peirceP))) ∧
    (((1 - peirceP) * x) * peirceP = (1 - peirceP) * (x * peirceP)) ∧
    (((1 - peirceP) * x) * (1 - peirceP) = (1 - peirceP) * (x * (1 - peirceP))) ∧
    lrComm (InfoGeometry.Canonical.ZornMatrix.chiralUpperBasis (R := ℝ) 0)
      (InfoGeometry.Canonical.ZornMatrix.chiralUpperBasis (R := ℝ) 1) ≠ 0 ∧
    lrCommMat8 (InfoGeometry.Canonical.ZornMatrix.chiralUpperBasis (R := ℝ) 0)
      (InfoGeometry.Canonical.ZornMatrix.chiralUpperBasis (R := ℝ) 1) ≠ 0 := by
  have hb := peirce_bracketing_P_corners x
  exact ⟨hb.1, hb.2.1, hb.2.2.1, hb.2.2.2,
    lrComm_chiralUpper_witness.2.1, lrComm_chiralUpper_witness.2.2⟩

theorem t2_f15_lrComm_self_zero_and_ell_not_supercomm (x y : ZornCarrier) :
    lrCommMat8 x x = 0 ∧
    lrCommMat8 y x = -lrCommMat8 x y ∧
    ¬ ell * ell = -(ell * ell) := by
  exact ⟨lrCommMat8_self x, lrCommMat8_swap x y, ell_not_supercommutative_odd⟩

/-! ## Feature F16 Boundary & Separation (including R5) -/

theorem t2_f16_r5_limit_noncommutative_witness :
    (∃ x y : Limit, x * y ≠ y * x) ∧
    wittCreationBase * wittAnnihilationBase ≠ wittAnnihilationBase * wittCreationBase := by
  exact ⟨limit_noncommutative, witt_base_noncommutative⟩

theorem t2_f16_r5_tracial_vs_kms_modular_shift_separation
    (Sys : CliffordTowerKMSBridgeSystem)
    (C : BostConnesCuntzSystem Sys.completion.Carrier)
    {β : ℝ} (hβ : 1 < β)
    (h_scale : ∀ n : ℕ+, Sys.modular.σ_imag (S C n) = ((n : ℝ) ^ (-β)) • S C n) :
    Sys.modular.σ_imag ≠ AlgHom.id ℝ Sys.completion.Carrier ∧
    traceKMSBridgeModel.modular.σ_imag =
      AlgHom.id ℝ traceKMSBridgeModel.completion.Carrier ∧
    (∀ a b : traceKMSBridgeModel.completion.Carrier,
      traceKMSBridgeModel.stateCLM (a * b) = traceKMSBridgeModel.stateCLM (b * a)) := by
  refine ⟨bostConnes_kms_requires_nontrivial_modular_shift Sys C hβ h_scale, rfl, ?_⟩
  intro a b
  rw [CliffordTowerKMSBridgeSystem.stateCLM, traceKMSBridgeModel.modular.kms_boundary a b]
  rfl

theorem t2_f16_trace_faithful_limit_vs_off_diag_kms_zero
    (x : Limit)
    (Sys : CliffordTowerKMSBridgeSystem)
    (C : BostConnesCuntzSystem Sys.completion.Carrier)
    {β : ℝ} (hβ : 0 < β)
    (h_scale : ∀ n : ℕ+, Sys.modular.σ_imag (S C n) = ((n : ℝ) ^ (-β)) • S C n)
    (h_scale_star : ∀ n : ℕ+, Sys.modular.σ_imag (star (S C n)) = ((n : ℝ) ^ β) • star (S C n))
    {n m : ℕ+} (hnm : n ≠ m) :
    (limitTrace (star x * x) = 0 ↔ x = 0) ∧
    Sys.stateCLM (S C n * star (S C m)) = 0 := by
  exact ⟨limitTrace_star_mul_self_eq_zero_iff x,
    kms_off_diagonal_projection_zero Sys C hβ h_scale h_scale_star hnm⟩

theorem t2_f16_beta_gt_one_vs_beta_one_divergence {β : ℝ} (hβ : 1 < β) :
    Summable (fun n : ℕ+ => ((n : ℕ) : ℝ) ^ (-β)) ∧
    ∑' n : ℕ+, normalizedBostConnesWeight β n = 1 ∧
    ¬ Summable (fun n : ℕ+ => ((n : ℕ) : ℝ) ^ (-(1 : ℝ))) := by
  refine ⟨summable_bostConnesWeight β hβ, tsum_normalizedBostConnesWeight β hβ, ?_⟩
  intro hsum
  have hsucc : Summable (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ (-(1 : ℝ))) :=
    (summable_pnat_iff_summable_succ (f := fun n : ℕ => (n : ℝ) ^ (-(1 : ℝ)))).mp hsum
  have hnat : Summable (fun n : ℕ => (n : ℝ) ^ (-(1 : ℝ))) :=
    (summable_nat_add_iff 1).mp hsucc
  have hlt : -(1 : ℝ) < -1 := Real.summable_nat_rpow.mp hnat
  exact lt_irrefl _ hlt

theorem t2_f16_centralizer_tracial_vs_isometry_asymmetry
    (Sys : CliffordTowerKMSBridgeSystem)
    {a : Sys.completion.Carrier} (b : Sys.completion.Carrier)
    (ha : Sys.modular.σ_imag a = a)
    (C : BostConnesCuntzSystem Sys.completion.Carrier)
    {β : ℝ} (hβ : 0 < β)
    (h_scale : ∀ n : ℕ+, Sys.modular.σ_imag (S C n) = ((n : ℝ) ^ (-β)) • S C n) :
    Sys.stateCLM (a * b) = Sys.stateCLM (b * a) ∧
    Sys.stateCLM (S C ⟨2, by norm_num⟩ * star (S C ⟨2, by norm_num⟩)) <
      Sys.stateCLM (star (S C ⟨2, by norm_num⟩) * S C ⟨2, by norm_num⟩) := by
  refine ⟨Sys.modular.centralizer_tracial b ha, ?_⟩
  let two : ℕ+ := ⟨2, by norm_num⟩
  rw [kms_diagonal_projection_weight Sys C h_scale two]
  rw [CliffordTowerKMSBridgeSystem.stateCLM, S_isometry C two, Sys.gns.stateCLM_one]
  rw [Real.rpow_neg (by positivity)]
  exact inv_lt_one_of_one_lt₀ (Real.one_lt_rpow (by norm_num [two]) hβ)

end PolarizedZ2E2E.Tier2R4

section E2EAxiomAudit
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut audited : Nat := 0
  for (name, info) in env.constants do
    if (env.getModuleIdxFor? name).isSome then continue
    if name.toString.startsWith "_private." then continue
    match info with
    | .thmInfo _ | .defnInfo _ =>
      if info.isUnsafe || info.isPartial then
        throwError "Unsafe or partial E2E declaration: {name}"
      let axioms ← Lean.collectAxioms name
      for ax in axioms do
        unless allowed.contains ax do
          throwError "Disallowed axiom {ax} in E2E declaration {name}"
      audited := audited + 1
    | .axiomInfo _ =>
      throwError "Disallowed axiom declaration in E2E file: {name}"
    | _ => pure ()
  if audited == 0 then
    throwError "E2EAxiomAudit found 0 declarations in current module"
  logInfo m!"E2E_AXIOM_AUDIT_PASS: {audited} local declarations verified"
end E2EAxiomAudit
