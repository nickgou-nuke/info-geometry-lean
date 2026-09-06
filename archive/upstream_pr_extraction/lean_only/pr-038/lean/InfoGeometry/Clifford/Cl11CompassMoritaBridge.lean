import InfoGeometry.Clifford.Cl11TensorTowerProjectionRank
import InfoGeometry.Clifford.SplitQ11CausalCone

set_option autoImplicit false

noncomputable section

namespace InfoGeometry.Clifford.Cl11CompassMoritaBridge

open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Clifford.SplitQ11PhaseFlip
open InfoGeometry.Clifford.SplitQ11Projectors
open InfoGeometry.Clifford.SplitQ11CausalCone

/-!
# `Cl(1,1)` compass and Morita-neutral tower bridge

This file connects repository owners that were previously intentionally kept
separate:

* `Cl11Matrix.cl11EquivMat` owns the abstract real Clifford algebra
  `Cl(1,1) ≃ₐ[ℝ] M₂(ℝ)`;
* `TowerMatrix.matEquivFinPowTwo` owns the native dyadic matrix stages;
* `SplitQ11CausalCone` owns the `jGen`/Krein sheet decomposition;
* `SplitQ11Projectors` owns the distinct pseudoscalar `epsGen` decomposition.

No new Clifford carrier, projector family, Bott classifier, or tensor tower is
introduced here.  In particular, the two projector decompositions are kept
distinct: the phase flip fixes the `jGen` sheet projectors but exchanges the
`epsGen` pseudoscalar projectors.
-/

/-- The abstract `Cl(1,1)` algebra maps directly to the repository-native first
matrix stage.  This is an equivalence/readout, not a second stage carrier. -/
noncomputable def cl11EquivStageOne :
    CliffordAlgebra InfoGeometry.Clifford.Cl11Matrix.q11 ≃ₐ[ℝ] MatStage 1 :=
  InfoGeometry.Clifford.Cl11Matrix.cl11EquivMat.trans
    (InfoGeometry.Clifford.TowerMatrix.matEquivFinPowTwo 1).symm

/-- The abstract `Cl(1,1)` owner and native first matrix stage have the same
real dimension through the explicit algebra equivalence. -/
theorem cl11_finrank_eq_stageOne :
    Module.finrank ℝ (CliffordAlgebra InfoGeometry.Clifford.Cl11Matrix.q11) =
      Module.finrank ℝ (MatStage 1) :=
  cl11EquivStageOne.toLinearEquiv.finrank_eq

/-- Each native `Cl(1,1)` matrix-tower step quadruples the real vector-space
dimension.  This is the finite-dimensional Morita stabilization readout behind
`A ↦ A ⊗ I₂`; it does not assert a new Bott residue classifier. -/
theorem matStage_finrank_succ (n : ℕ) :
    Module.finrank ℝ (MatStage (n + 1)) =
      4 * Module.finrank ℝ (MatStage n) := by
  rw [Cl11TensorTower.matStage_finrank, Cl11TensorTower.matStage_finrank]
  simp [pow_succ, Nat.mul_comm]

/-! ## Sheet projectors versus pseudoscalar projectors -/

/-- The canonical phase flip fixes the positive `jGen`/Krein sheet projector.
This contrasts with its exchange action on the `epsGen` pseudoscalar
projectors. -/
@[simp] theorem phaseFlipAlg_kreinPlusProjector :
    phaseFlipAlg kreinPlusProjector = kreinPlusProjector := by
  simp [kreinPlusProjector, splitQuaternionK]

/-- The canonical phase flip fixes the negative `jGen`/Krein sheet projector. -/
@[simp] theorem phaseFlipAlg_kreinMinusProjector :
    phaseFlipAlg kreinMinusProjector = kreinMinusProjector := by
  simp [kreinMinusProjector, splitQuaternionK]

/-- The two pseudoscalar spectral projectors are genuinely distinct. -/
theorem epsPlusProjector_ne_epsMinusProjector :
    epsPlusProjector ≠ epsMinusProjector := by
  intro h
  have hmul := epsPlusProjector_mul_epsMinusProjector
  rw [← h, epsPlusProjector_idempotent] at hmul
  have hsum := epsMinusProjector_add_epsPlusProjector
  rw [← h, hmul] at hsum
  have hzeroOne : (0 : Alg) = 1 := by
    simpa using hsum
  exact zero_ne_one hzeroOne

/-- The positive Krein sheet projector is not the positive pseudoscalar
projector.  The proof uses their different transformation laws under the
repository-owned phase-flip automorphism rather than coordinate expansion. -/
theorem kreinPlusProjector_ne_epsPlusProjector :
    kreinPlusProjector ≠ epsPlusProjector := by
  intro h
  have hmap := congrArg phaseFlipAlg h
  rw [phaseFlipAlg_kreinPlusProjector,
    phaseFlip_apply_epsPlusProjector] at hmap
  exact epsPlusProjector_ne_epsMinusProjector (h.symm.trans hmap)

/-- The negative Krein sheet projector is not the negative pseudoscalar
projector, again because the former is phase-flip fixed while the latter is
exchanged. -/
theorem kreinMinusProjector_ne_epsMinusProjector :
    kreinMinusProjector ≠ epsMinusProjector := by
  intro h
  have hmap := congrArg phaseFlipAlg h
  rw [phaseFlipAlg_kreinMinusProjector,
    phaseFlip_apply_epsMinusProjector] at hmap
  exact epsPlusProjector_ne_epsMinusProjector (hmap.symm.trans h)

end InfoGeometry.Clifford.Cl11CompassMoritaBridge
