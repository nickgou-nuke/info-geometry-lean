/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.BoundaryFibonacciSylvesterResolution
import InfoGeometry.Canonical.BoundaryFibonacciHomObstruction

/-! Audit the concrete rectangular-matrix obstruction and its inhomogeneous
replacement together. This checks no categorical equivalence claim. -/

open InfoGeometry.Canonical.BoundaryFibonacciIntertwinerObstruction
#print axioms firstGeneratorDefect_recovery_identity
#print axioms solveFirstGeneratorDefect_defect
#print axioms firstGeneratorDefect_solve
#print axioms firstGeneratorDefect_eq_iff
#print axioms simultaneousGeneratorDefect_solvable_iff
#print axioms direct_intertwiner_eq_zero
#print axioms firstGeneratorDefect_ker_eq_bot
#print axioms simultaneousGeneratorDefect_ker_eq_bot
#print axioms InfoGeometry.Canonical.BoundaryFibonacciHomObstruction.mem_B3FibonacciHom_iff
#print axioms InfoGeometry.Canonical.BoundaryFibonacciHomObstruction.B3FibonacciHom_eq_bot
#print axioms InfoGeometry.Canonical.BoundaryFibonacciHomObstruction.B3FibonacciHom_subsingleton
