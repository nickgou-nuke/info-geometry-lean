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

namespace PolarizedZ2E2E.Tier1R4

open scoped TensorProduct Matrix InnerProductSpace
open InfoGeometry.CliffordTower
open InfoGeometry.Clifford.Cl11SplitTowerMatrixEquiv
open InfoGeometry.Core.OperatorCliffordDouble
open InfoGeometry.Clifford.Cl30RealMatrixSignature
open InfoGeometry.Clifford.ThreeDHurwitz
open InfoGeometry.Algebra.Zorn.SplitOctonionPeirceG2Unification
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

/-! ## Feature F13: Coefficient-preserving Clifford tower & `End(M × M) ≃ₐ M₂(End M)` -/

theorem t1_f13_clifford_tensor_preserves_coeff_algebra
    (k : ℕ) (A : Type*) [Ring A] [Algebra ℝ A] (a b : A) :
    cliffordTensorEquivMatrix k A ((1 : Clsplit k) ⊗ₜ[ℝ] a) =
      Matrix.scalar (Fin (2 ^ k)) a ∧
    cliffordTensorEquivMatrix k A (((1 : Clsplit k) ⊗ₜ[ℝ] a) * ((1 : Clsplit k) ⊗ₜ[ℝ] b)) =
      Matrix.scalar (Fin (2 ^ k)) (a * b) ∧
    matrixEquivCliffordTensor k A (Matrix.scalar (Fin (2 ^ k)) a) =
      (1 : Clsplit k) ⊗ₜ[ℝ] a := by
  refine ⟨cliffordTensorEquivMatrix_one_tmul k A a, ?_,
    matrixEquivCliffordTensor_scalar k A a⟩
  rw [map_mul, cliffordTensorEquivMatrix_one_tmul, cliffordTensorEquivMatrix_one_tmul, ← map_mul]

theorem t1_f13_clifford_tensor_factor_commutation_and_tmul
    (k : ℕ) (A : Type*) [Ring A] [Algebra ℝ A] (x : Clsplit k) (a : A) :
    Commute (cliffordTensorEquivMatrix k A (x ⊗ₜ[ℝ] (1 : A)))
      (cliffordTensorEquivMatrix k A ((1 : Clsplit k) ⊗ₜ[ℝ] a)) ∧
    cliffordTensorEquivMatrix k A (x ⊗ₜ[ℝ] a) =
      cliffordTensorEquivMatrix k A (x ⊗ₜ[ℝ] (1 : A)) *
        cliffordTensorEquivMatrix k A ((1 : Clsplit k) ⊗ₜ[ℝ] a) := by
  refine ⟨?_, ?_⟩
  · exact (tmul_one_commute_one_tmul k A x a).map (cliffordTensorEquivMatrix k A).toAlgHom
  · rw [← map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

theorem t1_f13_clifford_tensor_preserves_noncomm_matrix_coeff (k : ℕ) :
    let a : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 0, 0]
    let b : Matrix (Fin 2) (Fin 2) ℝ := !![0, 0; 1, 0]
    cliffordTensorEquivMatrix k (Matrix (Fin 2) (Fin 2) ℝ) ((1 : Clsplit k) ⊗ₜ[ℝ] a) *
        cliffordTensorEquivMatrix k (Matrix (Fin 2) (Fin 2) ℝ) ((1 : Clsplit k) ⊗ₜ[ℝ] b) ≠
      cliffordTensorEquivMatrix k (Matrix (Fin 2) (Fin 2) ℝ) ((1 : Clsplit k) ⊗ₜ[ℝ] b) *
        cliffordTensorEquivMatrix k (Matrix (Fin 2) (Fin 2) ℝ) ((1 : Clsplit k) ⊗ₜ[ℝ] a) := by
  exact (cliffordTensorEquivMatrix_one_tmul_not_commute_iff k
    (Matrix (Fin 2) (Fin 2) ℝ) localMat2E01 localMat2E10).mpr local_mat2_real_noncomm

theorem t1_f13_block_matrix_alg_equiv_dirac_sq
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] (A B : Module.End R M) :
    (blockMatrixAlgEquiv !![A, B; B, -A]) ^ 2 =
      block (A ^ 2 + B ^ 2) (A * B - B * A) (-(A * B - B * A)) (A ^ 2 + B ^ 2) ∧
    blockMatrixAlgEquiv.symm
        (block (A ^ 2 + B ^ 2) (A * B - B * A) (-(A * B - B * A)) (A ^ 2 + B ^ 2)) =
      !![A ^ 2 + B ^ 2, A * B - B * A; -(A * B - B * A), A ^ 2 + B ^ 2] := by
  refine ⟨?_, blockMatrixAlgEquiv_symm_block _ _ _ _⟩
  rw [← diracPlus_eq_blockMatrixAlgEquiv, diracPlus_sq]

theorem t1_f13_withLp_and_tower_step_compat
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (A B C D : Module.End R M) (x y : M) (n : ℕ) (X : Clsplit n) :
    withLpBlockMatrixAlgEquiv !![A, B; C, D] (WithLp.toLp 2 (x, y)) =
      WithLp.toLp 2 (A x + B y, C x + D y) ∧
    blockMatrixAlgEquiv (Matrix.scalar (Fin 2) A) = lift A ∧
    cliffordTensorEquivMatrix n ℝ (X ⊗ₜ[ℝ] (1 : ℝ)) = splitTowerEquivMatrix n X := by
  refine ⟨withLpBlockMatrixAlgEquiv_apply !![A, B; C, D] (x, y),
    blockMatrixAlgEquiv_scalar A, ?_⟩
  rw [cliffordTensorEquivMatrix_tmul_one]
  exact Matrix.map_id _

/-! ## Feature F14: Real signature separation `Cl(3,0) ≅ M₂(ℂ)` vs `Cl(2,2) ≅ M₄(ℝ)` -/

theorem t1_f14_cl30_equiv_mat2C_pauli_generators :
    cl30EquivMat2C (g0 1 1 1) = pauli1 ∧
    cl30EquivMat2C (g1 1 1 1) = pauli2 ∧
    cl30EquivMat2C (g2 1 1 1) = pauli3 ∧
    pauli1 * pauli1 = 1 ∧
    pauli1 * pauli2 + pauli2 * pauli1 = 0 ∧
    pauli1ᴴ = pauli1 ∧
    cl30EquivMat2C pseudoscalar30 = Complex.I • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  exact ⟨cl30EquivMat2C_g0, cl30EquivMat2C_g1, cl30EquivMat2C_g2,
    pauli1_sq, pauli1_pauli2_anticomm, pauli1_hermitian, cl30EquivMat2C_pseudoscalar⟩

theorem t1_f14_cl30_center_equiv_complex_dim :
    Nonempty (Subalgebra.center ℝ (Cl3 1 1 1) ≃ₐ[ℝ] ℂ) ∧
    Module.finrank ℝ (Cl3 1 1 1) = 8 ∧
    Module.finrank ℝ (Subalgebra.center ℝ (Cl3 1 1 1)) = 2 ∧
    pseudoscalar30 ∈ Subalgebra.center ℝ (Cl3 1 1 1) ∧
    pseudoscalar30 ^ 2 = -1 := by
  exact ⟨⟨cl30CenterEquivComplex⟩, cl30_finrank, cl30_center_finrank,
    pseudoscalar30_mem_center, pseudoscalar30_sq⟩

theorem t1_f14_cl22_equiv_mat4R_center_real_dim :
    Nonempty (Clsplit 2 ≃ₐ[ℝ] Matrix (Fin 4) (Fin 4) ℝ) ∧
    Nonempty (Subalgebra.center ℝ (Clsplit 2) ≃ₐ[ℝ] ℝ) ∧
    Module.finrank ℝ (Clsplit 2) = 16 ∧
    Module.finrank ℝ (Subalgebra.center ℝ (Clsplit 2)) = 1 := by
  exact ⟨⟨cl22EquivMat4R⟩, ⟨cl22CenterEquivReal⟩, cl22_finrank, cl22_center_finrank⟩

theorem t1_f14_cl30_pauli_preimage_roundtrip (M : Matrix (Fin 2) (Fin 2) ℂ) (z : ℂ) :
    cl30EquivMat2C (cl30Preimage M) = M ∧
    cl30EquivMat2C (complexScalarPreimage z) = z • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  exact ⟨cl30ToMat_cl30Preimage M, cl30ToMat_complexScalarPreimage z⟩

theorem t1_f14_cl30_and_cl22_both_noncommutative :
    g0 1 1 1 * g1 1 1 1 ≠ g1 1 1 1 * g0 1 1 1 ∧
    (∃ a b : Clsplit 2, a * b ≠ b * a) := by
  exact ⟨cl30_generators_noncommutative, cl22_noncommutative⟩

/-! ## Feature F15: Peirce-Zorn-M₈(ℝ)-associator-G₂(₂) unification -/

theorem t1_f15_peirce_zorn_decomposition_and_block_mul (z₁ z₂ : ZornCarrier) :
    peirce11End + conePlusEnd + coneMinusEnd + peirce00End = (1 : EndZorn) ∧
    peirce11End * peirce11End = peirce11End ∧
    conePlusEnd * conePlusEnd = conePlusEnd ∧
    coneMinusEnd * coneMinusEnd = coneMinusEnd ∧
    peirce00End * peirce00End = peirce00End ∧
    peirce11 peirceP (z₁ * z₂) =
      peirce11 peirceP z₁ * peirce11 peirceP z₂ +
        conePlus peirceP z₁ * coneMinus peirceP z₂ := by
  exact ⟨peirce_ends_sum_one, peirce_ends_idempotent.1, peirce_ends_idempotent.2.1,
    peirce_ends_idempotent.2.2.1, peirce_ends_idempotent.2.2.2,
    (zorn_peirce_block_mul z₁ z₂).1⟩

theorem t1_f15_mat8_equiv_end_zorn_and_peirce_diagonals (M : Mat8R) (z : ZornCarrier) :
    endToMat8 (mat8EquivEndZorn M) = M ∧
    mat8EquivEndZorn (endToMat8 (leftMulEnd z)) = leftMulEnd z ∧
    endToMat8 peirce11End = Matrix.diagonal ![1, 0, 0, 0, 0, 0, 0, 0] ∧
    endToMat8 conePlusEnd = Matrix.diagonal ![0, 1, 1, 1, 0, 0, 0, 0] ∧
    endToMat8 coneMinusEnd = Matrix.diagonal ![0, 0, 0, 0, 1, 1, 1, 0] ∧
    endToMat8 peirce00End = Matrix.diagonal ![0, 0, 0, 0, 0, 0, 0, 1] ∧
    Function.Injective leftMulMat8 ∧
    Function.Injective rightMulMat8 := by
  refine ⟨endToMat8.apply_symm_apply M, mat8EquivEndZorn.apply_symm_apply (leftMulEnd z),
    endToMat8_peirce11End, endToMat8_conePlusEnd, endToMat8_coneMinusEnd,
    endToMat8_peirce00End, leftMulMat8_injective, rightMulMat8_injective⟩

theorem t1_f15_lrComm_associator_defect_and_right_alt (x y z : ZornCarrier) :
    lrComm x y z = -zornAssociator x z y ∧
    lrComm x y z = zornAssociator x y z ∧
    mat8EquivEndZorn (lrCommMat8 x y) z = zornAssociator x y z ∧
    lrCommMat8 y x = -lrCommMat8 x y := by
  exact ⟨lrComm_apply_eq_neg_associator x y z, lrComm_apply_eq_associator x y z,
    mat8EquivEndZorn_lrCommMat8_apply_eq_associator x y z, lrCommMat8_swap x y⟩

theorem t1_f15_g2_aut_conjugation_and_peirce_stabilizer
    (φ : InfoGeometry.Canonical.RealSplitOctonionAut) (x y z : ZornCarrier) :
    IsUnit (autMat8 φ) ∧
    autMat8 φ * leftMulMat8 x * (autMat8 φ)⁻¹ = leftMulMat8 (φ.1 x) ∧
    autMat8 φ * rightMulMat8 y * (autMat8 φ)⁻¹ = rightMulMat8 (φ.1 y) ∧
    autMat8 φ * lrCommMat8 x y * (autMat8 φ)⁻¹ = lrCommMat8 (φ.1 x) (φ.1 y) ∧
    φ.1 (zornAssociator x z y) = zornAssociator (φ.1 x) (φ.1 z) (φ.1 y) ∧
    (φ.1 peirceP = peirceP →
      autMat8 φ * endToMat8 peirce11End = endToMat8 peirce11End * autMat8 φ ∧
      autMat8 φ * endToMat8 conePlusEnd = endToMat8 conePlusEnd * autMat8 φ ∧
      autMat8 φ * endToMat8 coneMinusEnd = endToMat8 coneMinusEnd * autMat8 φ ∧
      autMat8 φ * endToMat8 peirce00End = endToMat8 peirce00End * autMat8 φ) := by
  refine ⟨isUnit_autMat8 φ, autMat8_conj_leftMulMat8 φ x, autMat8_conj_rightMulMat8 φ y,
    autMat8_conj_lrCommMat8 φ x y, aut_preserves_zornAssociator φ x z y, ?_⟩
  intro hP
  exact autMat8_commutes_peirceMat8_of_fix_P φ hP

theorem t1_f15_g2_derivation_lie_and_14d_span
    (D : InfoGeometry.Lie.CanonicalZornDerivation.canonicalZornDerivations)
    (x y : ZornCarrier) :
    ⁅endToMat8 D.1, lrCommMat8 x y⁆ = lrCommMat8 (D.1 x) y + lrCommMat8 x (D.1 y) ∧
    InfoGeometry.Lie.SplitOctonionStandardDerivation.directCanonicalStanDerMap x y =
      ⁅leftMulEnd x, leftMulEnd y⁆ + lrComm x y + ⁅rightMulEnd x, rightMulEnd y⁆ ∧
    Module.finrank ℝ InfoGeometry.Lie.CanonicalZornDerivation.canonicalZornDerivations = 14 ∧
    InfoGeometry.Lie.SplitOctonionStandardDerivation.standardDerivationSpan = ⊤ := by
  exact ⟨derivation_lie_lrCommMat8 D x y, directCanonicalStanDerMap_eq_commutator_sum x y,
    g2_derivation_finrank_and_standard_span.1, g2_derivation_finrank_and_standard_span.2⟩

/-! ## Feature F16: Inductive-limit to operator KMS bridge -/

theorem t1_f16_completion_universal_limit_hom
    (C : CliffordTowerCompletion) (n : ℕ) (X : Stage n) (r : ℝ) (x y : Limit) :
    C.limitHom (ofStage n X) = C.stageMap n X ∧
    C.limitHom (x * y) = C.limitHom x * C.limitHom y ∧
    C.limitHom (star x) = star (C.limitHom x) ∧
    C.limitHom (realAlgebraMap r) = algebraMap ℝ C.Carrier r ∧
    C.limitHom (r • x) = r • C.limitHom x := by
  exact ⟨C.limitHom_ofStage n X, map_mul C.limitHom x y, C.limitHom_star x,
    C.limitHom_realAlgebraMap r, C.limitHom_smul r x⟩

theorem t1_f16_gns_state_positivity_and_cs
    (Sys : CliffordTowerKMSBridgeSystem) (n : ℕ) (X : Stage n) (x : Limit)
    (a b : Sys.completion.Carrier) :
    Sys.limitState 1 = 1 ∧
    0 ≤ Sys.limitState (star x * x) ∧
    Sys.limitState (ofStage (n + 1) (stageBond n X)) = Sys.limitState (ofStage n X) ∧
    (Sys.stateCLM (star a * b)) ^ 2 ≤ Sys.stateCLM (star a * a) * Sys.stateCLM (star b * b) ∧
    Sys.stateCLM (star a) = Sys.stateCLM a := by
  refine ⟨Sys.gns.limitState_one, Sys.gns.limitState_star_mul_self_nonneg x, ?_,
    Sys.gns.stateCLM_cauchy_schwarz a b, Sys.gns.stateCLM_star a⟩
  rw [CliffordTowerKMSBridgeSystem.limitState,
    Sys.gns.limitState_stage_readout (n + 1) (stageBond n X),
    Sys.gns.limitState_stage_readout n X,
    Sys.gns.limitState_stage_compat n X]

theorem t1_f16_modular_j_isometry_and_kms_boundary
    (Sys : CliffordTowerKMSBridgeSystem) (ξ η : Sys.gns.Hilbert) (t : ℝ)
    (a : Sys.completion.Carrier) (x y : Limit) :
    ⟪Sys.modular.J ξ, Sys.modular.J η⟫_ℝ = ⟪ξ, η⟫_ℝ ∧
    ‖Sys.modular.J ξ‖ = ‖ξ‖ ∧
    (Sys.modular.σ (-t)).comp (Sys.modular.σ t) =
      ContinuousLinearMap.id ℝ Sys.completion.Carrier ∧
    ⟪Sys.gns.vacuum, (Sys.modular.J.comp ((Sys.gns.rep a).comp Sys.modular.J)) Sys.gns.vacuum⟫_ℝ =
      Sys.stateCLM a ∧
    Sys.limitState (x * y) =
      Sys.stateCLM (Sys.completion.limitHom y * Sys.modular.σ_imag (Sys.completion.limitHom x)) := by
  exact ⟨Sys.modular.J_isometry ξ η, Sys.modular.J_norm ξ, Sys.modular.σ_neg_comp t,
    Sys.modular.modular_conjugation_vector_symmetry a, Sys.modular.kms_boundary_on_limit x y⟩

theorem t1_f16_trace_kms_bridge_model_concrete
    (n : ℕ) (X : Stage n) (x y : Limit)
    (a b : traceKMSBridgeModel.completion.Carrier) :
    traceKMSBridgeModel.limitState 1 = 1 ∧
    traceKMSBridgeModel.limitState (ofStage (n + 1) (stageBond n X)) =
      traceKMSBridgeModel.limitState (ofStage n X) ∧
    traceKMSBridgeModel.stateCLM (a * b) = traceKMSBridgeModel.stateCLM (b * a) ∧
    traceKMSBridgeModel.modular.σ_imag =
      AlgHom.id ℝ traceKMSBridgeModel.completion.Carrier ∧
    limitTrace (ofStage n X) = InfoGeometry.Clifford.Cl11TensorTower.normalizedTrace n X ∧
    limitTrace (x * y) = limitTrace (y * x) := by
  refine ⟨traceKMSBridgeModel.gns.limitState_one, ?_, ?_, rfl,
    limitTrace_ofStage n X, limitTrace_mul_comm x y⟩
  · rw [CliffordTowerKMSBridgeSystem.limitState,
      traceKMSBridgeModel.gns.limitState_stage_readout (n + 1) (stageBond n X),
      traceKMSBridgeModel.gns.limitState_stage_readout n X,
      traceKMSBridgeModel.gns.limitState_stage_compat n X]
  · rw [CliffordTowerKMSBridgeSystem.stateCLM, traceKMSBridgeModel.modular.kms_boundary a b]
    rfl

theorem t1_f16_bostConnes_colimit_kms_partition_bridge
    (Sys : CliffordTowerKMSBridgeSystem)
    (C : BostConnesCuntzSystem Sys.completion.Carrier)
    {β : ℝ} (hβ : 1 < β)
    (h_scale : ∀ n : ℕ+, Sys.modular.σ_imag (S C n) = ((n : ℝ) ^ (-β)) • S C n)
    (h_scale_star : ∀ n : ℕ+, Sys.modular.σ_imag (star (S C n)) = ((n : ℝ) ^ β) • star (S C n)) :
    let Φ := bostConnesKMSProjectionState Sys C hβ h_scale h_scale_star
    Φ.ζβ = (riemannZeta (β : ℂ)).re ∧
    (∀ n : ℕ+, Φ.φ (S C n * star (S C n)) = normalizedBostConnesWeight β n) ∧
    (∑' n : ℕ+, Φ.φ (S C n * star (S C n))) = 1 ∧
    (∀ n : ℕ+, 0 < Φ.φ (S C n * star (S C n))) ∧
    (∀ a : Sys.completion.Carrier, 0 ≤ Φ.φ (star a * a)) ∧
    (∀ (n : ℕ) (X : Stage n),
      Sys.limitState (ofStage (n + 1) (stageBond n X)) = Sys.limitState (ofStage n X)) :=
  bostConnes_colimit_kms_partition_bridge Sys C hβ h_scale h_scale_star

end PolarizedZ2E2E.Tier1R4

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
