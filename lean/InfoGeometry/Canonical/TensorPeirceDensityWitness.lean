/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.TensorPeirceTraceLoss

/-! # Normalized positive dense Peirce witness

The witness is a normalized Gram matrix on the actual full finite stage.
Its colimit image retains positivity in the algebraic sum-of-squares sense,
normalized trace, and noncommutation with the represented cut.
-/

noncomputable section

namespace InfoGeometry.Canonical.TensorPeirceDensityWitness

open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Clifford.Cl11TensorTowerLimit
open InfoGeometry.Clifford.Cl11MarkovJonesEngine
open InfoGeometry.Canonical.Cl11CARPeirceMassCoercivityBridge
open InfoGeometry.Canonical.Cl11FiniteNormalizedTraceState
open InfoGeometry.Canonical.Cl11FiniteTraceGNSAction
open InfoGeometry.Canonical.RealStarColimitUniversal
open InfoGeometry.Canonical.TensorPeirceTraceLoss
open InfoGeometry.Examples.RealMatrixModeWitness
open InfoGeometry.OperatorAlgebra.PeirceSpine
open InfoGeometry.Algebra.DirectLimitSuperClosureLemmas
open InfoGeometry.Canonical.PeirceTetraktysColimitCoercivity

def denseGram : Stage 2 := star (1 + x) * (1 + x)

def denseGramTrace : ℝ := normalizedTrace 2 denseGram

def denseDensity : Stage 2 := denseGramTrace⁻¹ • denseGram

theorem denseGramTrace_pos : 0 < denseGramTrace := by
  have hy : (1 + x : Stage 2) ≠ 0 := by
    intro h
    have he := congrArg (fun A : Stage 2 => A (((0 : Fin 1), 0), 0) (((0 : Fin 1), 0), 0)) h
    change (1 : ℝ) + x (((0 : Fin 1), 0), 0) (((0 : Fin 1), 0), 0) = 0 at he
    norm_num [x] at he
  apply lt_of_le_of_ne
  · exact normalizedTraceState_positive 2 (1 + x)
  · intro hz
    exact hy ((normalizedTrace_star_mul_self_eq_zero_iff 2 (1 + x)).mp hz.symm)

/-- The matrix is positive semidefinite and normalized for the native
finite-stage normalized trace. -/
theorem denseDensity_positive_and_normalized :
    denseDensity.PosSemidef ∧ normalizedTrace 2 denseDensity = 1 := by
  have ht : denseGramTrace ≠ 0 := ne_of_gt denseGramTrace_pos
  constructor
  · exact (Matrix.posSemidef_conjTranspose_mul_self (1 + x)).smul
      (inv_nonneg.mpr denseGramTrace_pos.le)
  · change normalizedTraceLinear 2 (denseGramTrace⁻¹ • denseGram) = 1
    rw [map_smul]
    change denseGramTrace⁻¹ * denseGramTrace = 1
    exact inv_mul_cancel₀ ht

/-- The Gram matrix retains the noncommuting cross term of the dense mode. -/
theorem denseGram_not_commute : ¬ Commute p denseGram := by
  have hpstar : star p = p := p_isSelfAdjoint.star_eq
  have hpxs : p * star x = 0 := by
    have h := congrArg star x_mul_p
    simpa only [star_mul, hpstar, star_zero] using h
  have hxsp : star x * p = star x := by
    have h := congrArg star p_mul_x
    simpa only [star_mul, hpstar] using h
  have hpxsx : p * (star x * x) = 0 := by rw [← mul_assoc, hpxs, zero_mul]
  have hcomm : p * denseGram - denseGram * p = x - star x := by
    unfold denseGram
    simp only [star_add, star_one]
    noncomm_ring [p_mul_x, x_mul_p, hpxs, hxsp, hpxsx]
  intro hc
  have hz : p * denseGram - denseGram * p = 0 := sub_eq_zero.mpr hc.eq
  rw [hcomm] at hz
  have heq : x = star x := sub_eq_zero.mp hz
  have he := congrArg (fun A : Stage 2 => A (((0 : Fin 1), 0), 0) (((0 : Fin 1), 0), 1)) heq
  norm_num [x, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply,
    Matrix.transpose_apply] at he
  change (-(1 / 4) : ℝ) = (1 / 4 : ℝ) at he
  norm_num at he

theorem denseDensity_not_commute : ¬ Commute p denseDensity := by
  intro hc
  apply denseGram_not_commute
  have h := hc.eq
  change p * (denseGramTrace⁻¹ • denseGram) = (denseGramTrace⁻¹ • denseGram) * p at h
  simp only [mul_smul_comm, smul_mul_assoc] at h
  have h' := congrArg (fun A : Stage 2 => denseGramTrace • A) h
  have ht : denseGramTrace ≠ 0 := ne_of_gt denseGramTrace_pos
  change p * denseGram = denseGram * p
  simpa [smul_smul, ht] using h'

/-- A positive normalized full-matrix representative gives a self-adjoint,
normalized colimit element with strictly decreasing quadratic trace under
the dense Peirce pinching. -/
theorem denseDensity_colimit_strict_trace_loss :
    denseDensity.PosSemidef ∧ normalizedTraceLimit (ofStage 2 denseDensity) = 1 ∧
    ¬ Commute (ofStage 2 p) (ofStage 2 denseDensity) ∧
    normalizedTraceLimit
        (evenGrade (ofStage 2 p) (ofStage 2 denseDensity) *
          evenGrade (ofStage 2 p) (ofStage 2 denseDensity)) <
      normalizedTraceLimit (ofStage 2 denseDensity * ofStage 2 denseDensity) := by
  obtain ⟨hpos, htrace⟩ := denseDensity_positive_and_normalized
  have hp : ofStage 2 p * ofStage 2 p = ofStage 2 p := by
    rw [← map_mul, p_isIdempotentElem.eq]
  have hps : star (ofStage 2 p) = ofStage 2 p := by
    rw [← ofStage_star, p_isSelfAdjoint.star_eq]
  have hself : star (ofStage 2 denseDensity) = ofStage 2 denseDensity := by
    rw [← ofStage_star, Matrix.star_eq_conjTranspose, hpos.isHermitian.eq]
  have hnc : ¬ Commute (ofStage 2 p) (ofStage 2 denseDensity) := by
    intro hc
    apply denseDensity_not_commute
    apply (ofStage_injective 2)
    simpa only [map_mul] using hc.eq
  have henergy : 0 < coherenceEnergy (ofStage 2 p) (ofStage 2 denseDensity) := by
    apply lt_of_le_of_ne (coherenceEnergy_nonneg_and_faithful _ _).1
    intro hz
    exact hnc ((coherenceEnergy_nonneg_and_faithful _ _).2.mp hz.symm)
  have hdefect := normalizedTraceLimit_pinching_defect (ofStage 2 p)
    (ofStage 2 denseDensity) hp hps hself
  refine ⟨hpos, ?_, hnc, ?_⟩
  · exact htrace
  · linarith

/-- Every bonding map sends a positive finite matrix to a positive matrix. -/
theorem bondMap_posSemidef {n m : ℕ} (h : n ≤ m) (A : Stage n)
    (hA : A.PosSemidef) : (bondMap stageBond n m h A).PosSemidef := by
  induction m, h using Nat.le_induction with
  | base => simpa [bondMap_refl] using hA
  | succ m hm ih =>
    rw [bondMap_succ stageBond n m hm, RingHom.comp_apply]
    change (matStageEmbed m (bondMap stageBond n m hm A)).PosSemidef
    exact ih.kronecker Matrix.PosSemidef.one

/-- Positive normalized witnesses persist at every finite refinement, and
its Peirce coherence energy is exactly independent of the refinement. -/
theorem denseDensity_all_refinements (m : ℕ) (h : 2 ≤ m) :
    (bondMap stageBond 2 m h denseDensity).PosSemidef ∧
    normalizedTrace m (bondMap stageBond 2 m h denseDensity) = 1 ∧
    0 < stageCoherenceEnergy m (bondMap stageBond 2 m h p)
      (bondMap stageBond 2 m h denseDensity) ∧
    stageCoherenceEnergy m (bondMap stageBond 2 m h p)
      (bondMap stageBond 2 m h denseDensity) =
      stageCoherenceEnergy 2 p denseDensity := by
  have hpos := denseDensity_positive_and_normalized.1
  have hnorm := denseDensity_positive_and_normalized.2
  have hnc := denseDensity_colimit_strict_trace_loss.2.2.1
  have henergy : 0 < coherenceEnergy (ofStage 2 p) (ofStage 2 denseDensity) := by
    apply lt_of_le_of_ne (coherenceEnergy_nonneg_and_faithful _ _).1
    intro hz
    exact hnc ((coherenceEnergy_nonneg_and_faithful _ _).2.mp hz.symm)
  refine ⟨bondMap_posSemidef h denseDensity hpos, ?_, ?_,
    stageCoherenceEnergy_bondMap h p denseDensity⟩
  · rw [(bondMap_star_and_normalizedTrace h denseDensity).2, hnorm]
  · rw [stageCoherenceEnergy_bondMap, ← coherenceEnergy_ofStage]
    exact henergy

/-- Pinching strictly decreases the normalized quadratic trace at every
finite refinement of the positive witness. -/
theorem denseDensity_refinement_strict_trace_loss (m : ℕ) (h : 2 ≤ m) :
    normalizedTrace m
        (evenGrade (bondMap stageBond 2 m h p) (bondMap stageBond 2 m h denseDensity) *
          evenGrade (bondMap stageBond 2 m h p) (bondMap stageBond 2 m h denseDensity)) <
      normalizedTrace m
        (bondMap stageBond 2 m h denseDensity * bondMap stageBond 2 m h denseDensity) := by
  change normalizedTraceLimit (ofStage m
      (evenGrade (bondMap stageBond 2 m h p) (bondMap stageBond 2 m h denseDensity) *
        evenGrade (bondMap stageBond 2 m h p) (bondMap stageBond 2 m h denseDensity))) <
    normalizedTraceLimit (ofStage m
      (bondMap stageBond 2 m h denseDensity * bondMap stageBond 2 m h denseDensity))
  have heven (P X : Stage m) :
      ofStage m (evenGrade P X) = evenGrade (ofStage m P) (ofStage m X) := by
    simp only [evenGrade, map_add, map_mul, map_sub, map_one]
  have hp : ofStage m (bondMap stageBond 2 m h p) = ofStage 2 p :=
    directLimitOf_bondMap stageBond 2 m h p
  have hd : ofStage m (bondMap stageBond 2 m h denseDensity) = ofStage 2 denseDensity :=
    directLimitOf_bondMap stageBond 2 m h denseDensity
  simpa only [map_mul, heven, hp, hd] using denseDensity_colimit_strict_trace_loss.2.2.2

end InfoGeometry.Canonical.TensorPeirceDensityWitness

end
