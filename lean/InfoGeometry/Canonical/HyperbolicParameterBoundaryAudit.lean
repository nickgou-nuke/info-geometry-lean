/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.HyperbolicParameterBoundary

open InfoGeometry.Canonical.HyperbolicParameterBoundary
#print axioms integer_hyperbola_iff
#print axioms rational_parameters
#print axioms seeds_noncommuting
#print axioms boost_inverse
#print axioms elliptic_generator_not_boost_inverse
#print axioms boosted_pole_explicit
#print axioms boosted_pole_idempotent
#print axioms boosted_displacement_square

example : ¬ ∃ u v : ℤ, u*u-v*v=1 ∧ v≠0 := by
  rintro ⟨u,v,h,hv⟩
  exact hv ((integer_hyperbola_iff u v).mp h).2

example : boost * boostInv = 1 := boost_inverse.1
