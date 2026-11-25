/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.H3ZornE6RootSystem
import Mathlib.Algebra.Lie.SerreConstruction

/-!
# Serre-generator map for the split Albert `E₆` stabilizer

The local Albert owner has a 78-dimensional Chevalley basis and proves the six
simple triples satisfy the Chevalley--Serre relations. This file starts the
carrier bridge to Mathlib's quotient-defined `LieAlgebra.e₆`: it defines the
free-Lie evaluation and records the exact generator images. The quotient map
still requires proving that the full Serre ideal lies in the evaluation
kernel; this module does not claim that quotient descent or a Lie equivalence.
-/

noncomputable section

namespace InfoGeometry.Algebra

open H3Zorn
open InfoGeometry.Exceptional.CFSGPort.Chevalley

attribute [local instance 100] LieRing.ofAssociativeRing

/-- Evaluate the six Cartan, positive-root, and negative-root generators in
the already constructed split Albert cubic stabilizer. -/
def h3zornE6SerreGenerator
    (g : CartanMatrix.Generators (Fin 6)) : h3zornCubicStabilizer :=
  match g with
  | .H i => e6SimpleH i
  | .E i => e6SimpleE i
  | .F i => e6SimpleF i

/-- The universal Lie homomorphism from the free Lie algebra on the E₆ Serre
generators to the split Albert cubic stabilizer. -/
def h3zornE6FreeSerreEval :
    FreeLieAlgebra ℝ (CartanMatrix.Generators (Fin 6)) →ₗ⁅ℝ⁆
      h3zornCubicStabilizer :=
  FreeLieAlgebra.lift ℝ h3zornE6SerreGenerator

@[simp] theorem h3zornE6FreeSerreEval_H (i : Fin 6) :
    h3zornE6FreeSerreEval
      (FreeLieAlgebra.of ℝ (CartanMatrix.Generators.H i)) = e6SimpleH i := by
  simp [h3zornE6FreeSerreEval, h3zornE6SerreGenerator]

@[simp] theorem h3zornE6FreeSerreEval_E (i : Fin 6) :
    h3zornE6FreeSerreEval
      (FreeLieAlgebra.of ℝ (CartanMatrix.Generators.E i)) = e6SimpleE i := by
  simp [h3zornE6FreeSerreEval, h3zornE6SerreGenerator]

@[simp] theorem h3zornE6FreeSerreEval_F (i : Fin 6) :
    h3zornE6FreeSerreEval
      (FreeLieAlgebra.of ℝ (CartanMatrix.Generators.F i)) = e6SimpleF i := by
  simp [h3zornE6FreeSerreEval, h3zornE6SerreGenerator]

/-- The local and Mathlib E₆ Cartan matrices agree. -/
theorem h3zornE6_cartan_eq_mathlib :
    (fun i j : Fin 6 => Tag.cartan .E6 i j) = CartanMatrix.E 6 := by
  change Tag.cartan .E6 = CartanMatrix.E 6
  exact Tag.cartan_E6_eq_mathlib

end InfoGeometry.Algebra
