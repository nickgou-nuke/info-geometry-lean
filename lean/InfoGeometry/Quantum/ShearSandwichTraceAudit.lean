/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Quantum.ShearSandwichTrace

open InfoGeometry.Quantum.RelativeEntropyFlow InfoGeometryCore Matrix

#print axioms quantumShearSandwich_trace
#print axioms quantumShearSandwich_trace_eq_iff
#print axioms quantumShearSandwich_maximallyMixed_trace
#print axioms quantumShearSandwich_maximallyMixed_trace_iff
#print axioms quantumShearSandwich_trace_preserving_iff
#print axioms quantumShearSandwich_maximallyMixed_not_trace_preserving

example : Matrix.trace (quantumShearSandwich maximallyMixedState Complex.I) =
    (3 / 2 : ℂ) := by
  rw [quantumShearSandwich_maximallyMixed_trace]
  norm_num

-- A nonzero shear preserves the pure first-coordinate state's trace.
example (δ : ℂ) : Matrix.trace (quantumShearSandwich (!![1, 0; 0, 0] : M2C) δ) = 1 := by
  rw [quantumShearSandwich_trace]
  simp [Matrix.trace_fin_two]

example (ρ : M2C) : Matrix.trace (quantumShearSandwich ρ 0) = Matrix.trace ρ :=
  (quantumShearSandwich_trace_preserving_iff 0).mpr rfl ρ
