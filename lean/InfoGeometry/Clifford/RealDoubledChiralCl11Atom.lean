/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.OperatorAlgebra.RealDoubledChiralKrein
import InfoGeometry.OperatorAlgebra.RealDoubledChiralKreinComplements
import InfoGeometry.OperatorAlgebra.RealDoubledChiralKreinPhaseReal

/-!
# Real doubled chiral Cl(1,1) atom

This owner records the two opposite Peirce blocks of the mirror symmetry and
the four exact products of the chiral grading with the complex structure.
All statements are theorem-backed on the existing real doubled carrier.
-/

noncomputable section

open InfoGeometry.Krein
open InfoGeometry.OperatorAlgebra.RealDoubledChiralKrein

namespace InfoGeometry.Clifford.RealDoubledChiralCl11Atom

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

abbrev leftProj : EndH₂ (E := E) := leftChiralProjector (E := E)
abbrev rightProj : EndH₂ (E := E) := rightChiralProjector (E := E)
abbrev mirror : EndH₂ (E := E) := etaChiral (E := E)
abbrev phase : EndH₂ (E := E) := chiralComplexStructure (E := E)

def downOp : EndH₂ (E := E) :=
  (leftProj E).comp ((mirror E).comp (rightProj E))

def upOp : EndH₂ (E := E) :=
  (rightProj E).comp ((mirror E).comp (leftProj E))

theorem downOp_sq : (downOp E).comp (downOp E) = 0 := by
  apply ContinuousLinearMap.ext
  intro u
  apply DoubledSpace.ext <;>
    simp [downOp, leftProj, rightProj, mirror, leftChiralProjector,
      rightChiralProjector, etaChiral, gamma5, spectral_epsilon, modular_j,
      one_div, sub_eq_add_neg] <;> module

theorem upOp_sq : (upOp E).comp (upOp E) = 0 := by
  apply ContinuousLinearMap.ext
  intro u
  apply DoubledSpace.ext <;>
    simp [upOp, leftProj, rightProj, mirror, leftChiralProjector,
      rightChiralProjector, etaChiral, gamma5, spectral_epsilon, modular_j,
      one_div, sub_eq_add_neg] <;> module

theorem downOp_upOp : (downOp E).comp (upOp E) = leftProj E := by
  apply ContinuousLinearMap.ext
  intro u
  apply DoubledSpace.ext <;>
    simp [downOp, upOp, leftProj, rightProj, mirror, leftChiralProjector,
      rightChiralProjector, etaChiral, gamma5, spectral_epsilon, modular_j,
      one_div, sub_eq_add_neg] <;> module

theorem upOp_downOp : (upOp E).comp (downOp E) = rightProj E := by
  apply ContinuousLinearMap.ext
  intro u
  apply DoubledSpace.ext <;>
    simp [downOp, upOp, leftProj, rightProj, mirror, leftChiralProjector,
      rightChiralProjector, etaChiral, gamma5, spectral_epsilon, modular_j,
      one_div, sub_eq_add_neg] <;> module

theorem downOp_add_upOp : downOp E + upOp E = mirror E := by
  apply ContinuousLinearMap.ext
  intro u
  apply DoubledSpace.ext <;>
    simp [downOp, upOp, leftProj, rightProj, mirror,
      leftChiralProjector, rightChiralProjector, etaChiral, gamma5,
      spectral_epsilon, modular_j, one_div, sub_eq_add_neg] <;> module

theorem mirror_phase : (mirror E).comp (phase E) = gamma5 (E := E) := by
  apply ContinuousLinearMap.ext
  intro u
  apply DoubledSpace.ext <;>
    simp [mirror, phase, chiralComplexStructure, gamma5, etaChiral,
      spectral_epsilon, modular_j] <;> module

theorem phase_mirror : (phase E).comp (mirror E) = -(gamma5 (E := E)) := by
  apply ContinuousLinearMap.ext
  intro u
  apply DoubledSpace.ext <;>
    simp [mirror, phase, chiralComplexStructure, gamma5, etaChiral,
      spectral_epsilon, modular_j] <;> module

theorem gamma5_phase : (gamma5 (E := E)).comp (phase E) = -(mirror E) := by
  apply ContinuousLinearMap.ext
  intro u
  apply DoubledSpace.ext <;>
    simp [mirror, phase, chiralComplexStructure, gamma5, etaChiral,
      spectral_epsilon, modular_j] <;> module

theorem phase_gamma5 : (phase E).comp (gamma5 (E := E)) = mirror E := by
  apply ContinuousLinearMap.ext
  intro u
  apply DoubledSpace.ext <;>
    simp [mirror, phase, chiralComplexStructure, gamma5, etaChiral,
      spectral_epsilon, modular_j]

end InfoGeometry.Clifford.RealDoubledChiralCl11Atom
