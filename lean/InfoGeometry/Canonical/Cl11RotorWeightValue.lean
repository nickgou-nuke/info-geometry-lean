/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.Cl11CARPeirceReadback
import InfoGeometry.Canonical.ReflexiveMatrixTrace

/-! Exact normalized trace values for the native last-site Jordan--Wigner
rotor and its Peirce weights. Parameters need not lie on the unit circle. -/
noncomputable section
namespace InfoGeometry.Canonical.Cl11RotorWeightValue
open InfoGeometry.Clifford.Cl11TensorTower InfoGeometry.Clifford.Cl11MarkovJonesEngine
open Cl11CARFockColimitBridge Cl11PeirceWeightTrace
open ReflexiveNilpotentFlows PeirceRotorAction PeirceWeightedTrace

theorem pole_trace (k : ℕ) :
    normalizedTrace (k+1)
      ((finiteLastCARPair k).annihilation * (finiteLastCARPair k).creation) = 1/2 := by
  have h := trace_pair_support_scale (normalizedTraceLinear (k+1))
    (stageTracialFunctional (k+1)).cyclic' (finiteLastCARPair k).car
  have h1 : normalizedTraceLinear (k+1) (1 : MatStage (k+1)) = 1 :=
    cl11MarkovTraceNet.map_one (k+1)
  rw [h1] at h
  change 2 * normalizedTrace (k+1) _ = 1 at h
  linarith

theorem pair_matrix_trace (k : ℕ) (M : Matrix (Fin 2) (Fin 2) ℝ) :
    normalizedTrace (k+1) (pairMatrixLinear
      (finiteLastCARPair k).annihilation (finiteLastCARPair k).creation M) =
      (1/2) * Matrix.trace M := by
  have h := trace_pairMatrixLinear (normalizedTraceLinear (k+1))
    (stageTracialFunctional (k+1)).cyclic'
    (finiteLastCARPair k).nilpotent_annihilation (finiteLastCARPair k).nilpotent_creation
    (finiteLastCARPair k).annihilation_reflexive (finiteLastCARPair k).creation_reflexive M
  change normalizedTrace (k+1) _ = normalizedTrace (k+1) _ * Matrix.trace M at h
  rw [pole_trace] at h
  exact h

theorem weight_matrix (k : ℕ) (a b : ℝ) :
    let C := finiteLastCARPair k
    supportWeight a b C.annihilation C.creation =
      pairMatrixLinear C.annihilation C.creation !![b,0;0,a] := by
  simp [supportWeight, pairMatrixLinear_apply, pairMatrixUnit, add_comm]

theorem rotor_matrix (k : ℕ) (c s : ℝ) :
    let C := finiteLastCARPair k
    movingPlus c s C.annihilation C.creation =
      pairMatrixLinear C.annihilation C.creation !![c*c,-(c*s);-(c*s),s*s] := by
  dsimp only
  rw [movingPlus_expansion (finiteLastCARPair k).nilpotent_annihilation
    (finiteLastCARPair k).nilpotent_creation
    (finiteLastCARPair k).annihilation_reflexive (finiteLastCARPair k).creation_reflexive]
  simp [pairMatrixLinear_apply, pairMatrixUnit, smul_add, neg_smul]
  abel

theorem weighted_rotor_trace (k : ℕ) (a b c s : ℝ) :
    let C := finiteLastCARPair k
    normalizedTrace (k+1) (supportWeight a b C.annihilation C.creation *
      movingPlus c s C.annihilation C.creation) = (b*c*c+a*s*s)/2 := by
  dsimp only
  rw [weight_matrix, rotor_matrix, ← pairMatrixLinear_mul
    (finiteLastCARPair k).nilpotent_annihilation (finiteLastCARPair k).nilpotent_creation
    (finiteLastCARPair k).annihilation_reflexive (finiteLastCARPair k).creation_reflexive,
    pair_matrix_trace]
  simp [Matrix.trace, Matrix.diag, Matrix.mul_apply, Fin.sum_univ_two]
  ring

end InfoGeometry.Canonical.Cl11RotorWeightValue
