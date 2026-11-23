/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Synthesis.MathlibCliffordUniversalLiftSynthesis
import InfoGeometry.Clifford.ClNNNeutralChevalleyBridge
import InfoGeometry.Clifford.SplitCliffordMatrixEquiv

/-!
# Phase-space Cl(3,3) matrix equivalence

This owner reuses the existing neutral-to-split isometry and the existing
spinor matrix equivalence. It does not introduce a second Clifford algebra.
-/

noncomputable section

open InfoGeometry.Clifford
open InfoGeometry.Clifford.NeutralPhaseSpaceCore
open InfoGeometry.Clifford.ClNNNeutralChevalleyBridge
open InfoGeometry.Clifford.SpinorRep
open InfoGeometry.Synthesis.MathlibCliffordUniversalLiftSynthesis

namespace InfoGeometry.Clifford.Cl33PhaseMatrixEquiv

abbrev Phase3 := (Fin 3 → ℝ) × (Fin 3 → ℝ)

def phaseCoordEquiv : Phase3 ≃ₗ[ℝ] Neutral 3 :=
  (LinearEquiv.refl ℝ (Fin 3 → ℝ)).prodCongr (dualCoordinates 3).symm

theorem phaseCoordEquiv_apply (z : Phase3) :
    phaseCoordEquiv z = (z.1, (dualCoordinates 3).symm z.2) := rfl

def cl33ToTowerIsometry :
    cl33PhaseQuadratic.IsometryEquiv (TowerForm 3) where
  __ := phaseCoordEquiv.trans (neutralToSplit 3)
  map_app' := by
    intro z
    change TowerForm 3 (neutralToSplit 3 (phaseCoordEquiv z)) = cl33PhaseQuadratic z
    rw [Qsplit_neutralToSplit_chevalley]
    rw [chevelleyQsplit_eq_neutralForm]
    rcases z with ⟨u, v⟩
    simpa [phaseCoordEquiv, canonicalNeutralFormUnscaled_apply,
      cl33PhaseQuadratic_apply,
      InfoGeometry.Canonical.ZornSplitOctonionFin8Bridge.vec3Dot,
      Fin.sum_univ_three] using
      (dualCoordinates_eval (n := 3) u ((dualCoordinates 3).symm v)).symm

def cl33AlgEquiv :
    CliffordAlgebra cl33PhaseQuadratic ≃ₐ[ℝ] CliffordAlgebra (TowerForm 3) :=
  CliffordAlgebra.equivOfIsometry cl33ToTowerIsometry

def cl33ToMatrix8 :
    CliffordAlgebra cl33PhaseQuadratic ≃ₐ[ℝ] SpinorMatrix 3 :=
  cl33AlgEquiv.trans
    (InfoGeometry.Clifford.SplitCliffordMatrixEquiv.splitSpinorAlgEquiv 3)

end InfoGeometry.Clifford.Cl33PhaseMatrixEquiv
