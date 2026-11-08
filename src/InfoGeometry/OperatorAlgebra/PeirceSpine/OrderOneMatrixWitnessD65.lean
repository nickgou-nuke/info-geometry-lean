/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSpine.OrderOnePeirceObstruction
import InfoGeometry.OperatorAlgebra.OperatorExtensionExamples
import InfoGeometry.Meta.ArchetypePipeline

/-!
# D₆₅: A nondiagonal matrix witness for a nonzero order-one obstruction

This module instantiates the general Peirce formula on the repository's
nondiagonal, noncommuting 3-by-3 star projections. The diagonal corners obey
order zero, while a concrete two-wave order-one double commutator is nonzero.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceSpine

noncomputable section

open Matrix
open InfoGeometry.Core.PeirceDecomposition
open InfoGeometry.OperatorAlgebra.OperatorExtensionExamples
open InfoGeometry.MetaCompiler

local notation "Mat" => Matrix (Fin 3) (Fin 3) ℂ

/-! ## The D₆₅ causal archetypes -/

inductive OrderOneMatrixD65Stage where
  | noncommutingPeirceCut
  | orderZeroCorners
  | orderOneObstruction
  deriving DecidableEq, Repr

def OrderOneMatrixD65Stage.rank : OrderOneMatrixD65Stage → ℕ
  | .noncommutingPeirceCut => 0
  | .orderZeroCorners => 1
  | .orderOneObstruction => 2

def OrderOneMatrixD65Stage.edge : OrderOneMatrixD65Stage → OrderOneMatrixD65Stage → Prop
  | .noncommutingPeirceCut, .orderZeroCorners => True
  | .noncommutingPeirceCut, .orderOneObstruction => True
  | _, _ => False

def OrderOneMatrixD65Stage.causalLE : OrderOneMatrixD65Stage → OrderOneMatrixD65Stage → Prop
  | .noncommutingPeirceCut, _ => True
  | .orderZeroCorners, .orderZeroCorners => True
  | .orderOneObstruction, .orderOneObstruction => True
  | _, _ => False

theorem OrderOneMatrixD65Stage.causalLE_refl (a : OrderOneMatrixD65Stage) :
    a.causalLE a := by
  cases a <;> simp [causalLE]

theorem OrderOneMatrixD65Stage.causalLE_trans {a b c : OrderOneMatrixD65Stage}
    (hab : a.causalLE b) (hbc : b.causalLE c) : a.causalLE c := by
  cases a <;> cases b <;> cases c <;> simp_all [causalLE]

theorem OrderOneMatrixD65Stage.causalLE_antisymm {a b : OrderOneMatrixD65Stage}
    (hab : a.causalLE b) (hba : b.causalLE a) : a = b := by
  cases a <;> cases b <;> simp_all [causalLE]

theorem OrderOneMatrixD65Stage.edge_causal {a b : OrderOneMatrixD65Stage}
    (h : a.edge b) : a.causalLE b := by
  cases a <;> cases b <;> simp_all [edge, causalLE]

theorem OrderOneMatrixD65Stage.edge_rank_strict {a b : OrderOneMatrixD65Stage}
    (h : a.edge b) : a.rank < b.rank := by
  cases a <;> cases b <;> simp_all [edge, rank]

/-! ## Explicit matrix obstruction -/

def d65LeftCorner : Mat := P
def d65RightCorner : Mat := 1 - P
def d65Forward : Mat := conePlus P Q
def d65Backward : Mat := coneMinus P 0
def d65TwoWaveDirac : Mat := d65Forward + d65Backward

/-- The supported diagonal corners satisfy the order-zero condition. -/
theorem d65_order_zero_corners_commute :
    comm d65LeftCorner d65RightCorner = 0 := by
  have hP : P * P = P := P_isStarProjection.isIdempotentElem.eq
  change comm P (1 - P) = 0
  unfold comm
  noncomm_ring [hP]

/-- The selected off-diagonal Peirce amplitude is nonzero.  The certificate
is its `(0,0)` matrix entry, so the wave source is a genuine matrix witness. -/
theorem d65_forward_wave_nonzero : d65Forward ≠ 0 := by
  intro h
  have hu : conePlus P Q = component10 P Q := by
    simp [conePlus, component10, complementIdempotent]
  have he := congrArg (fun M : Mat => M 0 0) (show conePlus P Q = 0 by
    simpa [d65Forward] using h)
  rw [hu, component10_P_Q] at he
  norm_num at he

/-- The D65 amplitude input is a proof-carrying archetype of a nonzero
off-diagonal matrix wave. -/
def d65ForwardWaveNonzeroArchetype : TypedArchetype Unit .proved where
  name := `InfoGeometry.OperatorAlgebra.PeirceSpine.d65ForwardWaveNonzeroArchetype
  phase := 65
  claim := fun _ => d65Forward ≠ 0
  evidence := fun _ => d65_forward_wave_nonzero

/-- The mixed two-wave order-one obstruction has a nonzero matrix entry for
the fixed nondiagonal projection and amplitude from `OperatorExtensionExamples`.
Thus order zero alone does not imply order one. -/
theorem d65_order_one_obstruction_nonzero :
    comm (comm d65TwoWaveDirac d65LeftCorner) d65RightCorner ≠ 0 := by
  have hP : P * P = P := P_isStarProjection.isIdempotentElem.eq
  have hPcomp : P * (1 - P) = 0 := by noncomm_ring [hP]
  have hcompP : (1 - P) * P = 0 := by noncomm_ring [hP]
  have hcompSq : (1 - P) * (1 - P) = 1 - P := by noncomm_ring [hP]
  let N : Mat := conePlus P Q
  have hNP : N * P = 0 := by
    dsimp [N, conePlus]
    calc
      P * Q * (1 - P) * P = P * Q * ((1 - P) * P) := by noncomm_ring
      _ = 0 := by rw [hcompP]; simp
  have hPN : P * N = N := by
    dsimp [N, conePlus]
    calc
      P * (P * Q * (1 - P)) = (P * P) * Q * (1 - P) := by noncomm_ring
      _ = P * Q * (1 - P) := by rw [hP]
  have hNcomp : N * (1 - P) = N := by
    dsimp [N, conePlus]
    rw [mul_assoc, hcompSq]
  have hcompN : (1 - P) * N = 0 := by
    dsimp [N, conePlus]
    calc
      (1 - P) * (P * Q * (1 - P)) = ((1 - P) * P) * Q * (1 - P) := by
        noncomm_ring
      _ = 0 := by rw [hcompP]; simp
  have hFirst : comm N P = -N := by
    simp [comm, hNP, hPN]
  have hSecond : comm (-N) (1 - P) = -N := by
    simp [comm, hNcomp, hcompN]
  have hBracket :
      comm (comm d65TwoWaveDirac d65LeftCorner) d65RightCorner =
        -conePlus P Q := by
    calc
      _ = comm (comm N P) (1 - P) := by simp [N, d65TwoWaveDirac,
        d65Forward, d65Backward, d65LeftCorner, d65RightCorner, coneMinus]
      _ = comm (-N) (1 - P) := by rw [hFirst]
      _ = -N := hSecond
      _ = -conePlus P Q := rfl
  intro h
  have hu : conePlus P Q = component10 P Q := by
    simp [conePlus, component10, complementIdempotent]
  rw [hBracket] at h
  have he := congrArg (fun M : Mat => M 0 0) h
  rw [hu, component10_P_Q] at he
  norm_num at he

/-- Synthesis: the same nondiagonal model satisfies order zero while the
selected order-one bracket fails to vanish. -/
theorem stage_D65_order_one_matrix_counterexample :
    comm d65LeftCorner d65RightCorner = 0 ∧
    comm (comm d65TwoWaveDirac d65LeftCorner) d65RightCorner ≠ 0 :=
  ⟨d65_order_zero_corners_commute, d65_order_one_obstruction_nonzero⟩

/-- The concrete nondiagonal matrix witness certifies that order zero does not
imply order one for the selected two-wave operator. -/
def d65OrderZeroOrderOneCounterexampleArchetype :
    TypedArchetype Unit .proved where
  name :=
    `InfoGeometry.OperatorAlgebra.PeirceSpine.d65OrderZeroOrderOneCounterexampleArchetype
  phase := 65
  claim := fun _ =>
    comm d65LeftCorner d65RightCorner = 0 ∧
      comm (comm d65TwoWaveDirac d65LeftCorner) d65RightCorner ≠ 0
  evidence := fun _ => stage_D65_order_one_matrix_counterexample

#register_archetype d65OrderZeroOrderOneCounterexampleArchetype
#audit_archetype d65OrderZeroOrderOneCounterexampleArchetype
#register_archetype d65ForwardWaveNonzeroArchetype
#audit_archetype d65ForwardWaveNonzeroArchetype

end

end InfoGeometry.OperatorAlgebra.PeirceSpine
