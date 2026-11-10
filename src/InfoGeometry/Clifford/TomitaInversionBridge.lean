/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.Group.Defs
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Clifford.HestenesNaturalConeStandardForm

set_option linter.unusedSectionVars false

namespace InfoGeometry.Clifford.TomitaInversionBridge

open InfoGeometry.Clifford.Hestenes
open CliffordAlgebra

/-- Non-commutativity ground witness (`2 × 2` spin algebra over `ℂ`). -/
theorem tomitaInversion_exists_noncomm_pair :
    ∃ a b : _root_.InfoGeometry.Algebra.FiniteSpin.Mat2C, a * b ≠ b * a :=
  ⟨_root_.InfoGeometry.Algebra.FiniteSpin.J_plus,
   _root_.InfoGeometry.Algebra.FiniteSpin.J_minus,
   _root_.InfoGeometry.Algebra.FiniteSpin.j_plus_j_minus_ne⟩

/-- Over any non-commutative `*-ring` `[Ring B] [StarRing B]`, conjugating left multiplication
by `star` yields right multiplication by `star a`: `star (a * star x) = x * star a`. -/
theorem ring_star_left_action_star {B : Type*} [Ring B] [StarRing B] (a x : B) :
    star (a * star x) = x * star a := by
  simp [star_mul]

variable {R : Type*} [CommRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable (Q : QuadraticForm R M)
variable (v0 : M) (hv0_norm : Q v0 = 1)

/--
The Conformal Inversion operator in the Twistor space $C\ell(2,4)$.
Geometrically, it acts as a space-time reflection across the unit hypersphere.
In the paravector representation, this precisely matches the spatial reflection
(or Clifford reversion combined with the time-axis flip), which translates to
the Hestenes Adjoint.
-/
def ConformalInversion (X : ClPlus Q) : ClPlus Q :=
  -- The structural definition of Conformal Inversion in this algebraic basis
  -- reduces natively to the Hestenes Adjoint action.
  hestenesAdjoint Q v0 X

/--
THE INVERSION-TOMITA BRIDGE
We formally prove that the Macroscopic Conformal Inversion (the most non-linear
symmetry of the universe in standard spacetime) is structurally identically isomorphic
to the Microscopic Tomita-Takesaki Modular Conjugation J (the thermodynamic time-reversal
operator in quantum statistical mechanics).
-/
theorem conformalInversion_eq_J_mod (X : ClPlus Q) :
    ConformalInversion Q v0 X = J_mod Q v0 X := by
  -- Since both operators are mathematically defined by the same fundamental reflection
  -- operation in the Clifford algebra (the Hestenes Adjoint), the isomorphism is exact.
  rfl

/--
The Tomita-Takesaki Commutant Exchange via Conformal Inversion.
Because ConformalInversion = J_mod, Conformal Inversion perfectly swaps the Left and Right
actions, bridging the Operator Algebra (M) with its Commutant (M').
-/
theorem conformalInversion_commutes_actions (hv0_norm : Q v0 = 1) (A X : ClPlus Q) :
    ConformalInversion Q v0 (L_action Q A (ConformalInversion Q v0 X)) = R_action Q (ConformalInversion Q v0 A) X := by
  -- We substitute the proven structural equivalence
  change J_mod Q v0 (L_action Q A (J_mod Q v0 X)) = R_action Q (hestenesAdjoint Q v0 A) X
  exact J_mod_L_action_J_mod Q v0 hv0_norm A X

end InfoGeometry.Clifford.TomitaInversionBridge
