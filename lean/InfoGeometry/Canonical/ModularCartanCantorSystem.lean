import InfoGeometry.Canonical.RelativePotentialCountBridge
import InfoGeometry.Krein.DoubledSpace
import InfoGeometry.Meta.Architecture
import Mathlib.Tactic.NoncommRing

open scoped InnerProductSpace

/-!
# InfoGeometry.Canonical.ModularCartanCantorSystem

Bounded real-doubled root lemmas for modular twin cylinders and projective
count potentials.

This file does not formalize full type-III Tomita--Takesaki standard form.
It records the theorem-safe part of the dictionary already supported by the
repo:

* a modular reflection is represented by an involutive bounded operator `J`;
* the doubled pair involution sends `(A, B)` to `(J B J, J A J)`;
* selfdual and anti-selfdual twin pairs are fixed/negated by this involution;
* dyadic cylinder splitting is preserved by modular reflection;
* count-cylinder logarithmic increments are projective: common positive
  rescaling of the weights does not change the increment.

The type-III words "volume", "determinant", and "barrier" are therefore routed
through projective count potentials and modular reflection data, not asserted
as canonical traces or determinants.
-/

namespace InfoGeometry.Canonical.ModularCartanCantorSystem

open InfoGeometry.Krein
open InfoGeometry.Canonical.RelativePotentialCountBridge

section DoubledOperatorReflection

variable {E : Type 0}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

noncomputable local instance : NormedRing EndH := inferInstance
noncomputable local instance : NormedAlgebra ℝ EndH := inferInstance
local instance : IsTopologicalRing EndH := inferInstance
local instance : CompleteSpace EndH := inferInstance
local instance : SMulCommClass ℝ EndH EndH := inferInstance
local instance : IsScalarTower ℝ EndH EndH := inferInstance

/-- Modular twin of an operator under an involutive real doubled reflection. -/
@[rep_depth operator]
noncomputable def modularTwin (J A : EndH) : EndH :=
  J * A * J

/-- If `J² = 1`, modular twinning is involutive. -/
@[rep_depth operator]
theorem modularTwin_modularTwin_of_involutive
    {J A : EndH}
    (hJ : J * J = 1) :
    modularTwin (E := E) J (modularTwin (E := E) J A) = A := by
  unfold modularTwin
  calc
    J * (J * A * J) * J = (J * J) * A * (J * J) := by
      noncomm_ring
    _ = 1 * A * 1 := by
      rw [hJ]
    _ = A := by
      simp

/--
Cartan-style doubled involution on left/right operator pairs:
`Θ(A,B) = (J B J, J A J)`.
-/
@[rep_depth operator]
noncomputable def pairTheta (J : EndH) (X : EndH × EndH) : EndH × EndH :=
  (modularTwin (E := E) J X.2, modularTwin (E := E) J X.1)

/-- `Θ² = 1` when the reflecting operator has square `1`. -/
@[rep_depth operator]
theorem pairTheta_pairTheta_of_involutive
    {J : EndH}
    (hJ : J * J = 1)
    (X : EndH × EndH) :
    pairTheta (E := E) J (pairTheta (E := E) J X) = X := by
  cases X with
  | mk A B =>
      apply Prod.ext
      · exact modularTwin_modularTwin_of_involutive (E := E) hJ
      · exact modularTwin_modularTwin_of_involutive (E := E) hJ

/-- Selfdual diagonal twin pair `(A, JAJ)`. -/
@[rep_depth operator]
noncomputable def selfDualTwinPair (J A : EndH) : EndH × EndH :=
  (A, modularTwin (E := E) J A)

/-- Anti-selfdual normal twin pair `(A, -JAJ)`. -/
@[rep_depth operator]
noncomputable def antiSelfDualTwinPair (J A : EndH) : EndH × EndH :=
  (A, -modularTwin (E := E) J A)

/-- The selfdual twin pair is fixed by the Cartan pair involution. -/
@[rep_depth operator]
theorem pairTheta_selfDualTwinPair
    {J A : EndH}
    (hJ : J * J = 1) :
    pairTheta (E := E) J (selfDualTwinPair (E := E) J A)
      = selfDualTwinPair (E := E) J A := by
  apply Prod.ext
  · exact modularTwin_modularTwin_of_involutive (E := E) hJ
  · rfl

/-- The anti-selfdual twin pair is negated by the Cartan pair involution. -/
@[rep_depth operator]
theorem pairTheta_antiSelfDualTwinPair
    {J A : EndH}
    (hJ : J * J = 1) :
    pairTheta (E := E) J (antiSelfDualTwinPair (E := E) J A)
      = -antiSelfDualTwinPair (E := E) J A := by
  apply Prod.ext
  · calc
      modularTwin (E := E) J (-modularTwin (E := E) J A)
          = -modularTwin (E := E) J (modularTwin (E := E) J A) := by
            unfold modularTwin
            noncomm_ring
      _ = -A := by
            rw [modularTwin_modularTwin_of_involutive (E := E) hJ]
  · simp [pairTheta, antiSelfDualTwinPair]

/--
Modular twinning preserves a dyadic cylinder split.

This is the bounded-operator shadow of `p_w = p_{w0} + p_{w1}` being reflected
to the commutant/twin lane.
-/
@[rep_depth operator]
theorem modularTwin_preserves_cylinder_split
    {J p p0 p1 : EndH}
    (h : p = p0 + p1) :
    modularTwin (E := E) J p
      = modularTwin (E := E) J p0 + modularTwin (E := E) J p1 := by
  rw [h]
  unfold modularTwin
  noncomm_ring

/-- The selfdual twin cylinder also splits into selfdual twin children. -/
@[rep_depth operator]
theorem selfDualTwinPair_preserves_cylinder_split
    {J p p0 p1 : EndH}
    (h : p = p0 + p1) :
    selfDualTwinPair (E := E) J p
      = selfDualTwinPair (E := E) J p0 + selfDualTwinPair (E := E) J p1 := by
  apply Prod.ext
  · exact h
  · exact modularTwin_preserves_cylinder_split (E := E) (J := J) h

end DoubledOperatorReflection

section ProjectiveCountCylinders

variable {Word : Type*}

/-- Negative logarithmic cylinder potential from a positive weight profile. -/
@[rep_depth projective]
noncomputable def cylinderLogPotential (weight : Word → ℝ) (w : Word) : ℝ :=
  -Real.log (weight w)

/--
Negative logarithmic branch increment:
`-log(weight child / weight parent)`.
-/
@[rep_depth projective]
noncomputable def cylinderLogIncrement
    (weight : Word → ℝ)
    (parent child : Word) : ℝ :=
  -Real.log (weight child / weight parent)

/--
The cylinder logarithmic increment is projective: common positive rescaling of
the cylinder weights does not change it.
-/
@[rep_depth projective]
theorem cylinderLogIncrement_common_pos_smul
    (weight : Word → ℝ)
    (parent child : Word)
    {c : ℝ}
    (hc : 0 < c) :
    cylinderLogIncrement (fun w => c * weight w) parent child
      = cylinderLogIncrement weight parent child := by
  unfold cylinderLogIncrement
  have hratio :
      c * weight child / (c * weight parent) = weight child / weight parent := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      (mul_div_mul_left (weight child) (weight parent) hc.ne')
  rw [hratio]

/--
Existing count-side modular Hamiltonian profiles already have projective
invariance under common positive rescaling.
-/
@[rep_depth projective]
theorem relativeCountModularProfile_projective_rescale
    {n : Nat}
    (counts ref : RelativeCounts n)
    {c : ℝ}
    (hc : 0 < c) :
    relativeCountModularProfile n (c • counts) (c • ref)
      = relativeCountModularProfile n counts ref :=
  relativeCountModularProfile_common_pos_smul (n := n) c hc counts ref

end ProjectiveCountCylinders

end InfoGeometry.Canonical.ModularCartanCantorSystem
