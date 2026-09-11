import InfoGeometry.Clifford.Cl11TensorTowerProjectionRank
import InfoGeometry.Algebra.FiniteSpinAlgebra
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

This file connects the repository-owned abstract Clifford algebra, native
matrix stages, and the two distinct projector systems.  It introduces no
second carrier or projector hierarchy.
-/

/-- The abstract `Cl(1,1)` algebra maps to the repository-native first stage. -/
noncomputable def cl11EquivStageOne :
    CliffordAlgebra InfoGeometry.Clifford.Cl11Matrix.q11 ≃ₐ[ℝ] MatStage 1 :=
  InfoGeometry.Clifford.Cl11Matrix.cl11EquivMat.trans
    (InfoGeometry.Clifford.TowerMatrix.matEquivFinPowTwo 1).symm

theorem cl11_finrank_eq_stageOne :
    Module.finrank ℝ (CliffordAlgebra InfoGeometry.Clifford.Cl11Matrix.q11) =
      Module.finrank ℝ (MatStage 1) :=
  cl11EquivStageOne.toLinearEquiv.finrank_eq

theorem matStage_finrank_succ (n : ℕ) :
    Module.finrank ℝ (MatStage (n + 1)) =
      4 * Module.finrank ℝ (MatStage n) := by
  rw [Cl11TensorTower.matStage_finrank, Cl11TensorTower.matStage_finrank]
  simp [pow_succ, Nat.mul_comm]

@[simp] theorem phaseFlipAlg_kreinPlusProjector :
    phaseFlipAlg kreinPlusProjector = kreinPlusProjector := by
  simp [kreinPlusProjector, splitQuaternionK]

@[simp] theorem phaseFlipAlg_kreinMinusProjector :
    phaseFlipAlg kreinMinusProjector = kreinMinusProjector := by
  simp [kreinMinusProjector, splitQuaternionK]

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

theorem kreinPlusProjector_ne_epsPlusProjector :
    kreinPlusProjector ≠ epsPlusProjector := by
  intro h
  have hmap := congrArg phaseFlipAlg h
  rw [phaseFlipAlg_kreinPlusProjector,
    phaseFlip_apply_epsPlusProjector] at hmap
  exact epsPlusProjector_ne_epsMinusProjector (h.symm.trans hmap)

theorem kreinMinusProjector_ne_epsMinusProjector :
    kreinMinusProjector ≠ epsMinusProjector := by
  intro h
  have hmap := congrArg phaseFlipAlg h
  rw [phaseFlipAlg_kreinMinusProjector,
    phaseFlip_apply_epsMinusProjector] at hmap
  exact epsPlusProjector_ne_epsMinusProjector (hmap.symm.trans h)

end InfoGeometry.Clifford.Cl11CompassMoritaBridge
