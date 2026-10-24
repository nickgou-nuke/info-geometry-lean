/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.DeBruijnRotorAlternationCycle
import InfoGeometry.Canonical.UnifiedGeometryOperatorSignificance
import InfoGeometry.Canonical.CuntzMatrixAlgebraicTraceFunctional

/-!
# Native rotor and weight transport through the matrix algebraic colimit

All maps and carriers are the existing algebraic ones. No completed state,
analytic KMS condition, or injectivity hypothesis is introduced.
-/
noncomputable section

namespace InfoGeometry.Canonical.RotorColimitTransport
open DeBruijnRotorAlternationCycle

section Ring
variable {A C : Type*} [Ring A] [Ring C]

/-- A ring homomorphism transports the four seed equations. -/
theorem map_seed_pair (f : A →+* C) {d B : A} (h : IsDualSeedPair d B) :
    IsDualSeedPair (f d) (f B) where
  d_sq := by simpa only [map_mul, map_zero] using congrArg f h.d_sq
  B_sq := by simpa only [map_mul, map_zero] using congrArg f h.B_sq
  dBd := by simpa only [map_mul] using congrArg f h.dBd
  BdB := by simpa only [map_mul] using congrArg f h.BdB
end Ring

section Algebra
variable {R A C : Type*} [CommRing R] [Ring A] [Ring C]
variable [Algebra R A] [Algebra R C]

/-- Rotor formation commutes with the actual algebra map. -/
theorem map_phaseRotor (f : A →ₐ[R] C) (c s : R) (d B : A) :
    f (phaseRotor c s d B) = phaseRotor c s (f d) (f B) := by
  simp only [phaseRotor, zeroModeSupport, carrierSupport, polePlus, poleMinus,
    wheelGenerator, map_add, map_sub, map_one, map_mul, map_smul]

/-- Conjugated idempotent expressions transport before imposing normalization. -/
theorem map_movingPolePlus (f : A →ₐ[R] C) (c s : R) (d B : A) :
    f (movingPolePlus c s d B) = movingPolePlus c s (f d) (f B) := by
  simp only [movingPolePlus, polePlus, map_mul, map_phaseRotor]

/-- Stream 3 weights transport on the same pair as the Stream 5 rotor. -/
theorem map_kmsModularWeight (f : A →ₐ[R] C) (u v : R) (d B : A) :
    f (UnifiedGeometryOperatorSignificance.kmsModularWeight u v d B) =
      UnifiedGeometryOperatorSignificance.kmsModularWeight u v (f d) (f B) := by
  simp only [UnifiedGeometryOperatorSignificance.kmsModularWeight,
    UnifiedGeometryOperatorSignificance.projMinus,
    UnifiedGeometryOperatorSignificance.projPlus, map_add, map_smul, map_mul]
end Algebra

section NativeColimit
open CuntzMatrixAlgebraicStarColimit CuntzMatrixAlgebraicTraceFunctional
open CuntzMatrixTowerInstantiation CuntzMatrixTraceTower

/-- A finite-stage seed pair is a pair in the existing filtered algebraic colimit. -/
theorem stage_seed_pair (n : ℕ) {d B : MatrixStage n} (h : IsDualSeedPair d B) :
    IsDualSeedPair (stageInjection n d) (stageInjection n B) :=
  map_seed_pair (stageInjection n).toRingHom h

/-- Exact readback through the native stage injection. -/
theorem stage_movingPolePlus (n : ℕ) (c s : ℂ) (d B : MatrixStage n) :
    stageInjection n (movingPolePlus c s d B) =
      movingPolePlus c s (stageInjection n d) (stageInjection n B) :=
  map_movingPolePlus (stageInjection n).toAlgHom c s d B

/-- The transported normalized rotor observable is genuinely idempotent. -/
theorem colimit_movingPolePlus_idempotent (n : ℕ) {d B : MatrixStage n}
    (h : IsDualSeedPair d B) (c s : ℂ) (hc : c*c+s*s=1) :
    IsIdempotentElem
      (movingPolePlus c s (stageInjection n d) (stageInjection n B)) := by
  exact movingPolePlus_idem (stage_seed_pair n h) c s hc

/-- Moving to a later stage gives precisely the same colimit observable. -/
theorem stage_movingPolePlus_transition {i j : ℕ} (hij : i ≤ j)
    (c s : ℂ) (d B : MatrixStage i) :
    stageInjection j (movingPolePlus c s (concreteMap hij d) (concreteMap hij B)) =
      stageInjection i (movingPolePlus c s d B) := by
  calc
    _ = stageInjection j (concreteMap hij (movingPolePlus c s d B)) :=
      congrArg (stageInjection j)
        (map_movingPolePlus (concreteMap hij).toAlgHom c s d B).symm
    _ = _ := stageInjection_concrete_transition hij _

/-- The actual colimit trace reads the finite rotated observable exactly. -/
theorem trace_movingPolePlus_stage (n : ℕ) (c s : ℂ) (d B : MatrixStage n) :
    traceFunctional (movingPolePlus c s (stageInjection n d) (stageInjection n B)) =
      matrixTraceState n (movingPolePlus c s d B) := by
  rw [← stage_movingPolePlus, traceFunctional_stage]

/-- Squared-weight densities use the same native colimit transport. -/
theorem stage_kmsModularWeight (n : ℕ) (u v : ℂ) (d B : MatrixStage n) :
    stageInjection n (UnifiedGeometryOperatorSignificance.kmsModularWeight u v d B) =
      UnifiedGeometryOperatorSignificance.kmsModularWeight u v
        (stageInjection n d) (stageInjection n B) :=
  map_kmsModularWeight (stageInjection n).toAlgHom u v d B

/-- Weighted rotated-observable expectations retain their finite-stage value. -/
theorem trace_weighted_movingPolePlus_stage (n : ℕ) (u v c s : ℂ)
    (d B : MatrixStage n) :
    traceFunctional
      (UnifiedGeometryOperatorSignificance.kmsModularWeight u v
        (stageInjection n d) (stageInjection n B) *
       movingPolePlus c s (stageInjection n d) (stageInjection n B)) =
      matrixTraceState n
        (UnifiedGeometryOperatorSignificance.kmsModularWeight u v d B *
         movingPolePlus c s d B) := by
  rw [← stage_kmsModularWeight, ← stage_movingPolePlus,
    ← stageInjection_mul, traceFunctional_stage]
end NativeColimit
end InfoGeometry.Canonical.RotorColimitTransport
