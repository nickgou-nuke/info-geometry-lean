/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.FiveStreamNativeTransport
import InfoGeometry.Canonical.Cl11CARFockColimitBridge
import InfoGeometry.Canonical.Cl11TensorInductiveLimit

/-!
# Five-stream transport on the native Cl(1,1) tensor colimit

The already constructed finite Jordan–Wigner and algebraic-limit CAR pairs
instantiate the seed laws. Rotors and moving poles commute with the actual
stage algebra homomorphism. The presented modular group acts by units of the
existing limit algebra; no replacement limit, completion or faithfulness claim.
-/
noncomputable section

namespace InfoGeometry.Canonical.Cl11FiveStreamColimitTransport

open Cl11CARFockColimitBridge FiveStreamNativeTransport
open DeBruijnRotorAlternationCycle
open InfoGeometry.Core.ParabolicModularRepresentation
open InfoGeometry.Topology.FractalCantorFock

/-- Adapter between the two existing CAR interfaces at their shared seed laws. -/
theorem realCAR_seedPair {A : Type*} [Ring A] (P : RealCARPair A) :
    IsDualSeedPair P.annihilation P.creation := by
  exact carPair_isDualSeedPair
    { ann := P.annihilation, cre := P.creation,
      ann_sq := P.nilpotent_annihilation, cre_sq := P.nilpotent_creation, anti := P.car }

/-- The existing algebraic Cl(1,1) limit carries the PR #206 group representation. -/
def algebraicModularRepresentation (k : ℕ) :
    ModularRelationsGroup →* InfoGeometry.Clifford.Cl11TensorTowerLimit.Limitˣ :=
  let h := realCAR_seedPair (algebraicCARPair k)
  representation h.d_sq h.B_sq h.dBd h.BdB

/-- Finite-stage rotor transport is exact on the actual direct-limit carrier. -/
theorem stage_rotor (k : ℕ) (c s : ℝ) :
    Cl11TensorInductiveLimit.ofStageAlgHom (k + 1)
      (phaseRotor c s (finiteLastCARPair k).annihilation (finiteLastCARPair k).creation) =
    phaseRotor c s (algebraicCARPair k).annihilation (algebraicCARPair k).creation := by
  rw [map_phaseRotor]
  change phaseRotor c s
    (InfoGeometry.Clifford.Cl11TensorTowerLimit.ofStage (k + 1) (finiteLastCARPair k).annihilation)
    (InfoGeometry.Clifford.Cl11TensorTowerLimit.ofStage (k + 1) (finiteLastCARPair k).creation) = _
  rw [finiteLastCARPair_annihilation_to_colimit, finiteLastCARPair_creation_to_colimit]

/-- Moving idempotents, not just their coefficients, survive the stage map. -/
theorem stage_movingPolePlus (k : ℕ) (c s : ℝ) :
    Cl11TensorInductiveLimit.ofStageAlgHom (k + 1)
      (movingPolePlus c s (finiteLastCARPair k).annihilation (finiteLastCARPair k).creation) =
    movingPolePlus c s (algebraicCARPair k).annihilation (algebraicCARPair k).creation := by
  rw [map_movingPolePlus]
  change movingPolePlus c s
    (InfoGeometry.Clifford.Cl11TensorTowerLimit.ofStage (k + 1) (finiteLastCARPair k).annihilation)
    (InfoGeometry.Clifford.Cl11TensorTowerLimit.ofStage (k + 1) (finiteLastCARPair k).creation) = _
  rw [finiteLastCARPair_annihilation_to_colimit, finiteLastCARPair_creation_to_colimit]

/-- The colimit modular generator is the image of the finite quarter-turn rotor. -/
theorem modular_generator_from_stage (k : ℕ) :
    (algebraicModularRepresentation k (PresentedGroup.of false) :
        InfoGeometry.Clifford.Cl11TensorTowerLimit.Limit) =
    Cl11TensorInductiveLimit.ofStageAlgHom (k + 1)
      (phaseRotor (0 : ℝ) 1 (finiteLastCARPair k).annihilation (finiteLastCARPair k).creation) := by
  rw [stage_rotor]
  have h := quarterTurn_eq_modular_generator (R := ℝ) (realCAR_seedPair (algebraicCARPair k))
  exact (congrArg (fun u : InfoGeometry.Clifford.Cl11TensorTowerLimit.Limitˣ =>
    (u : InfoGeometry.Clifford.Cl11TensorTowerLimit.Limit)) h).symm

/-- Along `c * c + s * s = 1`, the algebraic-limit CAR moving poles are idempotent,
    sum to the colimit carrier support, and are mutually orthogonal. -/
theorem colimit_car_movingPolePlus_idem_and_orth (k : ℕ) {c s : ℝ}
    (hc : c * c + s * s = 1) :
    let d := (algebraicCARPair k).annihilation
    let B := (algebraicCARPair k).creation
    movingPolePlus c s d B * movingPolePlus c s d B = movingPolePlus c s d B ∧
    movingPolePlus c s d B + movingPoleMinus c s d B = carrierSupport d B ∧
    movingPolePlus c s d B * movingPoleMinus c s d B = 0 :=
  movingPolePlus_idem_and_orth (realCAR_seedPair (algebraicCARPair k)) hc

/-- Along `c * c + s * s = 1`, the algebraic-limit CAR moving pole satisfies the
    operator-valued chordal displacement square and compression laws. -/
theorem colimit_car_fubini_study_chordal_metric (k : ℕ) {c s : ℝ}
    (hc : c * c + s * s = 1) :
    let d := (algebraicCARPair k).annihilation
    let B := (algebraicCARPair k).creation
    (movingPolePlus c s d B - polePlus d B) *
      (movingPolePlus c s d B - polePlus d B) = (s * s) • carrierSupport d B ∧
    polePlus d B * movingPolePlus c s d B * polePlus d B = (c * c) • polePlus d B :=
  movingPolePlus_chordal_square_and_compression (realCAR_seedPair (algebraicCARPair k)) hc

end InfoGeometry.Canonical.Cl11FiveStreamColimitTransport
