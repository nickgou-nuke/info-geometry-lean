/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.PeirceAlgebraTransport
import InfoGeometry.Canonical.Cl11TensorInductiveLimit
import InfoGeometry.Canonical.CliffordCARGeneratorTopological

/-! Peirce orbits commute with the native Clifford tower embeddings and
algebraic colimit injections. No analytic completion is asserted. -/
noncomputable section
namespace InfoGeometry.Canonical.Cl11PeirceOrbitColimit
open InfoGeometry.Clifford.Cl11TensorTower InfoGeometry.Clifford.Cl11TensorTowerLimit
open Cl11TensorInductiveLimit CliffordCARGeneratorTopological
open ReflexiveNilpotentFlows PeirceRotorAction PeirceHyperbolicOrbit PeirceAlgebraTransport

theorem rotor_successor (n : ℕ) (i : Fin n) (c s : ℝ) :
    stageEmbed n (rotor c s (jwAnnihilation n i) (jwCreation n i)) =
      rotor c s (jwAnnihilation (n+1) i.castSucc) (jwCreation (n+1) i.castSucc) := by
  rw [map_rotor]
  simp [stageEmbed_apply, matStageEmbed_jwAnnihilation, matStageEmbed_jwCreation]

theorem movingPlus_colimit (n : ℕ) (i : Fin n) (c s : ℝ) :
    ofStage n (movingPlus c s (jwAnnihilation n i) (jwCreation n i)) =
      movingPlus c s (algebraicAnnihilationElement n i) (algebraicCreationElement n i) := by
  exact map_movingPlus (ofStageAlgHom n) c s _ _

theorem hyperbolicPlus_colimit (n : ℕ) (i : Fin n) (u v : ℝ) :
    ofStage n (hyperbolicPlus u v (jwAnnihilation n i) (jwCreation n i)) =
      hyperbolicPlus u v (algebraicAnnihilationElement n i) (algebraicCreationElement n i) := by
  exact map_hyperbolicPlus (ofStageAlgHom n) u v _ _

end InfoGeometry.Canonical.Cl11PeirceOrbitColimit
