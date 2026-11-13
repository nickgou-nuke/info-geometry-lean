/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Clifford.SplitAtomQuaternion
import InfoGeometry.Algebra.StrictUpperBCH3
import InfoGeometry.Geometry.AssociativeBianchi
import InfoGeometry.OperatorAlgebra.WeightedPermutationHolonomy

/-!
# Clifford pairs, exact BCH coordinates, and operator curvature

The imported owners describe independent algebraic branches. The substantive
bridge here uses the constructed nested quaternion pair as connection
potentials. Its curvature has the stated constant-axis value when the corresponding
base derivatives annihilate those axes. Zero derivations provide an explicit
realization; the existing gauge owner then transports this curvature by units.

The coefficient ring may itself be `Module.End R M` with no finite-dimensional
hypothesis. No continuum limit, Clifford classification over arbitrary scalar
rings, compact Lie group, or analytic field theory is inferred.
-/

namespace InfoGeometry.Canonical.CliffordHolonomyCurvature

open InfoGeometry.Clifford.SplitAtomDoubling
open InfoGeometry.Clifford.SplitAtomQuaternion
open InfoGeometry.Geometry.AssociativeGaugeConnection

variable {B : Type*} [Ring B]

/-- The derivative correction and the actual quaternion commutator. -/
theorem spinor_curvature_formula (D E : Module.End ℤ (Block2 (Block2 B))) :
    curvature D E firstAxis secondAxis =
      D secondAxis - E firstAxis + 2 * thirdAxis := by
  rw [curvature, add_sub_assoc, first_second_commutator]

/-- The constant value occurs exactly when the two derivative terms cancel. -/
theorem spinor_curvature_eq_iff (D E : Module.End ℤ (Block2 (Block2 B))) :
    curvature D E firstAxis secondAxis = 2 * thirdAxis ↔
      D secondAxis = E firstAxis := by
  simp only [spinor_curvature_formula, add_eq_right, sub_eq_zero]

/-- A constant-axis specialization with explicit sufficient hypotheses. -/
theorem spinor_curvature
    (D E : Module.End ℤ (Block2 (Block2 B)))
    (hD : D secondAxis = 0) (hE : E firstAxis = 0) :
    curvature D E firstAxis secondAxis = 2 * thirdAxis := by
  simpa only [curvature, hD, hE, sub_self, zero_add] using
    (first_second_commutator (B := B))

/-- A constructed constant-curvature example over every coefficient ring. -/
theorem spinor_curvature_zero :
    curvature (0 : Module.End ℤ (Block2 (Block2 B))) 0 firstAxis secondAxis =
      2 * thirdAxis :=
  spinor_curvature 0 0 rfl rfl

/-- The curvature acts on unrestricted nested operator matrices. -/
theorem spinor_curvature_action
    (D E : Module.End ℤ (Block2 (Block2 B)))
    (hD : IsLeibniz D) (hE : IsLeibniz E)
    (hcomm : ∀ X, D (E X) = E (D X))
    (hDaxis : D secondAxis = 0) (hEaxis : E firstAxis = 0)
    (X : Block2 (Block2 B)) :
    covariantDerivative D firstAxis (covariantDerivative E secondAxis X) -
      covariantDerivative E secondAxis (covariantDerivative D firstAxis X) =
        (2 * thirdAxis) * X := by
  rw [curvature_action D E hD hE hcomm, spinor_curvature D E hDaxis hEaxis]

/-- Existing affine gauge transport applied to the actual constant spinor
curvature, with arbitrary units of the full operator matrix ring. -/
theorem spinor_curvature_zero_gauge (u : (Block2 (Block2 B))ˣ) :
    curvature (0 : Module.End ℤ (Block2 (Block2 B))) 0
      (gaugePotential (R := ℤ) 0 firstAxis u) (gaugePotential (R := ℤ) 0 secondAxis u) =
        conjugate u (2 * thirdAxis) := by
  have hzero : IsLeibniz (0 : Module.End ℤ (Block2 (Block2 B))) := by
    intro X Y
    simp
  rw [curvature_gauge_covariant 0 0 hzero hzero (fun _ => rfl), spinor_curvature_zero]

end InfoGeometry.Canonical.CliffordHolonomyCurvature
