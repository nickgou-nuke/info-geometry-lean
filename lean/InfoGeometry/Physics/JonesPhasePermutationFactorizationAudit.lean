/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Physics.JonesPhasePermutationFactorization

namespace InfoGeometry.Physics.JonesPhasePermutationFactorization
open B3PresentedGroup JonesPhaseCharacter

example : (phase ((PresentedGroup.of B3Gen.sig0 : B3) * PresentedGroup.of B3Gen.sig0) : ℂ) = -1 :=
  phase_generator_square B3Gen.sig0

example (g : B3) : phaseRemoved g =
    JonesPermutationAction.rho
      (InfoGeometry.Projective.ProjectiveNullBoundaryBraidEquivariance.braidPermutation g) := by
  rw [phaseRemoved_eq_permutation, MonoidHom.comp_apply]

#print axioms rho_sigma1
#print axioms rho_sigma2
#print axioms phaseRemoved_eq_permutation
#print axioms jones_phase_permutation_factorization
#print axioms scalarUnit_injective
#print axioms same_permutation_jones_eq_iff_phase_eq

end InfoGeometry.Physics.JonesPhasePermutationFactorization
