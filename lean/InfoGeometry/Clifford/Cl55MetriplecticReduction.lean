/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Clifford.Cl55ParaKahlerMetric
import InfoGeometry.Thermo.BilinearMetriplecticReduction

/-!
# Nontrivial metriplectic reduction on the native (5,5) carrier

The family uses the actual transported symplectic and positive generalized
metrics. A two-mode example has nonzero reversible and dissipative directions,
zero energy rate, and entropy rate 2. It demonstrates nonvacuity of the
construction, not a replacement for the arbitrary-map reduction theorem.
-/

noncomputable section

namespace InfoGeometry.Clifford.Cl55MetriplecticReduction

open Clifford55 Cl55ParaKahlerMetric
open InfoGeometry.Thermo
open InfoGeometry.Thermo.GenericMetriplecticFlow

/-- Actual native-metric specialization, with the Casimir kernels explicit. -/
def reducedSystem (P C : Module.End ℝ V55) (dH dS : Covector V55)
    (hS : P.dualMap dS = 0) (hE : C.dualMap dH = 0) : System V55 :=
  BilinearMetriplecticReduction.system diagonalOmega positiveMetric
    diagonalOmega_nondegenerate positiveMetric_nondegenerate
    diagonalOmega_skew positiveMetric_symm
    (fun x => by
      by_cases hx : x = 0
      · simp [hx]
      · exact (positiveMetric_pos x hx).le)
    P C dH dS hS hE

/-- Projection onto one existing positive/negative Witt coordinate pair. -/
def modeProjection (i : Fin 5) : Module.End ℝ V55 :=
  ((coord5 i).comp fst55).smulRight (e_pos i) +
    ((coord5 i).comp snd55).smulRight (f_neg i)

@[simp] theorem modeProjection_fst (i j : Fin 5) (v : V55) :
    (modeProjection i v).1 j = if j = i then v.1 i else 0 := by
  simp [modeProjection, coord5, fst55, snd55, e_pos, f_neg]

@[simp] theorem modeProjection_snd (i j : Fin 5) (v : V55) :
    (modeProjection i v).2 j = if j = i then v.2 i else 0 := by
  simp [modeProjection, coord5, fst55, snd55, e_pos, f_neg]

@[simp] theorem modeProjection_e_pos (i : Fin 5) :
    modeProjection i (e_pos i) = e_pos i := by
  apply Prod.ext <;> funext j <;> simp [e_pos]

theorem modeProjection_dual_omega (i : Fin 5) :
    (modeProjection i).dualMap (diagonalOmega (e_pos i)) = diagonalOmega (e_pos i) := by
  apply LinearMap.ext
  intro v
  change diagonalOmega (e_pos i) (modeProjection i v) = diagonalOmega (e_pos i) v
  simp

theorem modeProjection_dual_positive (i : Fin 5) :
    (modeProjection i).dualMap (positiveMetric (e_pos i)) = positiveMetric (e_pos i) := by
  apply LinearMap.ext
  intro v
  change positiveMetric (e_pos i) (modeProjection i v) = positiveMetric (e_pos i) v
  simp

/-- Both rates act nontrivially, on distinct native modes. -/
def twoModeSystem : System V55 :=
  reducedSystem (modeProjection 1) (modeProjection 0)
    (diagonalOmega (e_pos 1)) (positiveMetric (e_pos 0))
    (by
      apply LinearMap.ext
      intro v
      change positiveMetric (e_pos 0) (modeProjection 1 v) = 0
      simp)
    (by
      apply LinearMap.ext
      intro v
      change diagonalOmega (e_pos 1) (modeProjection 0 v) = 0
      simp)

theorem twoModeSystem_reversible : twoModeSystem.L twoModeSystem.dH = e_pos 1 := by
  change modeProjection 1 ((diagonalOmega.toDual diagonalOmega_nondegenerate).symm
    ((modeProjection 1).dualMap (diagonalOmega (e_pos 1)))) = _
  rw [modeProjection_dual_omega]
  change modeProjection 1 ((diagonalOmega.toDual diagonalOmega_nondegenerate).symm
    ((diagonalOmega.toDual diagonalOmega_nondegenerate) (e_pos 1))) = _
  simp

theorem twoModeSystem_dissipative : twoModeSystem.M twoModeSystem.dS = e_pos 0 := by
  change modeProjection 0 ((positiveMetric.toDual positiveMetric_nondegenerate).symm
    ((modeProjection 0).dualMap (positiveMetric (e_pos 0)))) = _
  rw [modeProjection_dual_positive]
  change modeProjection 0 ((positiveMetric.toDual positiveMetric_nondegenerate).symm
    ((positiveMetric.toDual positiveMetric_nondegenerate) (e_pos 0))) = _
  simp

theorem twoModeSystem_flow : twoModeSystem.flow = e_pos 1 + e_pos 0 := by
  exact congrArg₂ (· + ·) twoModeSystem_reversible twoModeSystem_dissipative

theorem twoModeSystem_entropy_rate : twoModeSystem.dS twoModeSystem.flow = 2 := by
  rw [twoModeSystem_flow]
  change positiveMetric (e_pos 0) (e_pos 1 + e_pos 0) = 2
  rw [positiveMetric_e_pos]
  norm_num [e_pos]

theorem twoModeSystem_both_nonzero :
    twoModeSystem.L twoModeSystem.dH ≠ 0 ∧ twoModeSystem.M twoModeSystem.dS ≠ 0 := by
  rw [twoModeSystem_reversible, twoModeSystem_dissipative]
  constructor <;> intro h
  · have := congrArg (fun v : V55 => v.1 1) h
    norm_num [e_pos] at this
  · have := congrArg (fun v : V55 => v.1 0) h
    norm_num [e_pos] at this

end InfoGeometry.Clifford.Cl55MetriplecticReduction
