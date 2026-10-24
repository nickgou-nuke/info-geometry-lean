/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import scratch.FiniteExponentialMotion20261024
import scratch.SeedRealTimeActionAlignmentProbe20261024v2
import InfoGeometry.Canonical.FiniteSeedRepresentationFaithfulness

/-! Uncompiled finite-first consumer for the actual represented seed action.
No existential witness is obtained in a generic dependent represented closure. -/
noncomputable section
open scoped ComplexOrder
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 500000

namespace InfoGeometry.Canonical.SeedFiniteFirstMotion

open CStarStateColimit.Native
open FilteredGNSMatrixRealTime FilteredGNSRepresentedCStarClosure
open CantorBernoulliCStarMatrixTraceState CuntzMatrixTowerInstantiation
open AlgebraicKMSStateColimit FiniteSeedRepresentedRealTime FiniteMatrixGibbsFunctional
open FiniteExponentialMotion ModularFlowExponentialGenerator
open InfoGeometry.Physics.KleinBottleSewingExact

private abbrev stageCStarFamily : ∀ n, CStarAlgebra (CStarMatrixStage n) :=
  fun _n => inferInstance
private abbrev stageOrderFamily : ∀ n, PartialOrder (CStarMatrixStage n) :=
  fun _n => inferInstance
private abbrev stageStarOrderFamily : ∀ n, StarOrderedRing (CStarMatrixStage n) :=
  fun _n => inferInstance
attribute [local instance] stageCStarFamily stageOrderFamily stageStarOrderFamily

variable {k : ℕ}
local notation "E" => (CStarMatrix.ofMatrixStarAlgEquiv :
  MatrixStage k ≃⋆ₐ[ℂ] CStarMatrixStage k)

/-- Pointwise finite naturality before specializing the compatible state family. -/
theorem matrixStageAut_eq_finitePath
    (ω : ContinuousStarInductiveSystem.CompatibleStateFamily
      CStarMatrixStage cstarMatrixInductiveSystem)
    (f : MatrixStage k →⋆ₐ[ℂ]
      representedCStarClosure CStarMatrixStage cstarMatrixInductiveSystem ω)
    (H : MatrixStage k) (hH : H.IsHermitian) (x : MatrixStage k) (t : ℝ) :
    matrixRealTimeAut CStarMatrixStage cstarMatrixInductiveSystem ω f H hH t (f x) =
      f (E.symm (complexExponentialConjugationPath (E H) (E x) t)) := by
  calc
    _ = complexExponentialConjugationPath (f H) (f x) t :=
      InfoGeometry.OperatorAlgebra.expUnitary_conjugation_eq_complexPath
        (matrixGenerator CStarMatrixStage cstarMatrixInductiveSystem ω f H hH) (f x) t
    _ = _ := (finitePath_map f H x t).symm

/-- Actual native seed action, with finite path as its proved application readback. -/
theorem seedRealTimeAut_eq_finitePath
    (H : MatrixStage k) (hH : H.IsHermitian) (β : ℝ) (x : MatrixStage k) (t : ℝ) :
    seedRealTimeAut H hH β t (seedStageHom H hH β x) =
      seedStageHom H hH β
        (E.symm (complexExponentialConjugationPath (E H) (E x) t)) := by
  have ha := SeedRealTimeActionAlignmentProbeV2.seedRealTimeAut_apply_eq_matrixRealTimeAut_probe
    H hH β t x
  have hp := matrixStageAut_eq_finitePath (finiteSeedCompatibleStageStates H hH β)
    (seedStageHom H hH β) H hH x t
  exact ha.trans hp

/-- Choose a finite-stage witness first, then use the accepted actual seed injectivity. -/
theorem seed_exists_realTime_move
    (H : MatrixStage k) (hH : H.IsHermitian) (β : ℝ)
    (x : MatrixStage k) (hc : H*x-x*H ≠ 0) :
    ∃ t : ℝ, seedRealTimeAut H hH β t (seedStageHom H hH β x) ≠
      seedStageHom H hH β x := by
  obtain ⟨t, ht⟩ := finiteStage_exists_path_move H x hc
  refine ⟨t, ?_⟩
  intro he
  have hm := (seedRealTimeAut_eq_finitePath H hH β x t).symm.trans he
  have hx := FiniteSeedRepresentationFaithfulness.seedStageHom_injective H hH β hm
  apply ht
  apply E.symm.injective
  exact hx.trans (E.symm_apply_apply x).symm

/-- The 01 entry of the finite tilt/switch commutator detects every nonzero tilt. -/
theorem tilt_switch_commutator_ne_zero (h : ℝ) (hh : h ≠ 0) :
    (h • tilt2) * switch2 - switch2 * (h • tilt2) ≠ 0 := by
  intro hz
  have he := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 1) hz
  have hc : (h : ℂ) ≠ 0 := by exact_mod_cast hh
  have he' : (2 : ℂ) * (h : ℂ) = 0 := by
    simpa [tilt2, switch2, Matrix.mul_apply, Fin.sum_univ_two,
      RCLike.real_smul_eq_coe_mul, two_mul] using he
  exact (mul_ne_zero (by norm_num : (2 : ℂ) ≠ 0) hc) he'

/-- For every beta and nonzero tilt, the actual represented switch moves at some time. -/
theorem tiltSeed_exists_realTime_move (h β : ℝ) (hh : h ≠ 0) :
    let J := seedStageHom (k := 1) (h • tilt2) (tiltHamiltonian_isHermitian h) β
    ∃ t : ℝ, seedRealTimeAut (k := 1) (h • tilt2)
      (tiltHamiltonian_isHermitian h) β t (J switch2) ≠ J switch2 := by
  exact seed_exists_realTime_move (k := 1) (h • tilt2)
    (tiltHamiltonian_isHermitian h) β switch2 (tilt_switch_commutator_ne_zero h hh)

end InfoGeometry.Canonical.SeedFiniteFirstMotion
