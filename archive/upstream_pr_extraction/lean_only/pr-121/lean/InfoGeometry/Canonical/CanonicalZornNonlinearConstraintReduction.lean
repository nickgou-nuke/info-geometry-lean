/- SPDX-License-Identifier: Apache-2.0 -/

import InfoGeometry.Canonical.CanonicalZornDerivativeFiniteReadout
import Mathlib.Analysis.Calculus.FDeriv.Comp

/-!
# Local nonlinear reduction of the canonical Zorn automorphism constraints

The full nonlinear automorphism constraint has codomain `TangentConstraintValues`,
whereas its derivative at the identity has only a 50-dimensional range.  The
linear inclusion

`range (dF_1) ⊆ TangentConstraintValues`

does not imply that the nonlinear values of `F` lie in that range.  Accordingly,
this file does **not** corestrict the nonlinear constraint to the derivative
range.

Instead, for any genuine continuous-linear readout

`P : TangentConstraintValues →L[ℝ] W`,

we form the always-defined reduced nonlinear map `P ∘ F`.  Vanishing of the
full constraint automatically implies vanishing of the reduced constraint.
The converse is isolated as the exact local-completeness property that must be
proved for a concrete 50-dimensional readout before applying implicit-function
machinery to the actual automorphism locus.
-/

namespace InfoGeometry.Canonical

noncomputable section

open Filter
open scoped Topology

variable {W : Type*}
variable [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- A reduced nonlinear constraint obtained by applying an honest continuous
linear readout to the full ambient automorphism constraint.  This construction
requires no claim that nonlinear constraint values lie in the derivative
range. -/
def reducedAutomorphismConstraintReadout
    (P : TangentConstraintValues →L[ℝ] W) : EndCZ → W :=
  fun A => P (ambientAutomorphismConstraintReadout A)

@[simp] theorem reducedAutomorphismConstraintReadout_apply
    (P : TangentConstraintValues →L[ℝ] W) (A : EndCZ) :
    reducedAutomorphismConstraintReadout P A =
      P (ambientAutomorphismConstraintReadout A) :=
  rfl

/-- The reduced nonlinear constraint vanishes at the identity because the full
constraint does. -/
@[simp] theorem reducedAutomorphismConstraintReadout_one_zero
    (P : TangentConstraintValues →L[ℝ] W) :
    reducedAutomorphismConstraintReadout P
        (ContinuousLinearMap.id ℝ CZ) = 0 := by
  rw [reducedAutomorphismConstraintReadout_apply,
    ambientAutomorphismConstraintReadout_one_zero]
  exact P.map_zero

/-- The strict derivative of the reduced constraint is the readout composed
with the already-proved tangent constraint differential. -/
theorem hasStrictFDerivAt_reducedAutomorphismConstraintReadout
    (P : TangentConstraintValues →L[ℝ] W) :
    HasStrictFDerivAt
      (reducedAutomorphismConstraintReadout P)
      (P.comp tangentConstraintReadoutContinuous)
      (ContinuousLinearMap.id ℝ CZ) := by
  simpa [reducedAutomorphismConstraintReadout, Function.comp_def] using
    P.hasStrictFDerivAt.comp
      (ContinuousLinearMap.id ℝ CZ)
      hasStrictFDerivAt_ambientAutomorphismConstraintReadout

/-- Vanishing of the full 520-dimensional constraint always implies vanishing
of every linear reduced readout. -/
theorem reducedAutomorphismConstraintReadout_eq_zero_of_ambient_eq_zero
    (P : TangentConstraintValues →L[ℝ] W)
    {A : EndCZ}
    (hA : ambientAutomorphismConstraintReadout A = 0) :
    reducedAutomorphismConstraintReadout P A = 0 := by
  rw [reducedAutomorphismConstraintReadout_apply, hA]
  exact P.map_zero

/-- Exact missing nonlinear theorem packaged as a reusable property.

A readout is locally complete at the identity when, in some neighborhood of
the identity, its vanishing forces all of the ambient nonlinear constraints to
vanish.  This is the local redundancy statement for the omitted constraints.
It is deliberately not supplied as structure data for any concrete readout. -/
def IsLocallyCompleteAutomorphismConstraintReadout
    (P : TangentConstraintValues →L[ℝ] W) : Prop :=
  ∀ᶠ A in 𝓝 (ContinuousLinearMap.id ℝ CZ),
    reducedAutomorphismConstraintReadout P A = 0 →
      ambientAutomorphismConstraintReadout A = 0

/-- A locally complete reduced readout cuts out exactly the same zero locus as
the full nonlinear automorphism constraint in a neighborhood of the identity. -/
theorem eventually_ambient_zero_iff_reduced_zero
    (P : TangentConstraintValues →L[ℝ] W)
    (hP : IsLocallyCompleteAutomorphismConstraintReadout P) :
    ∀ᶠ A in 𝓝 (ContinuousLinearMap.id ℝ CZ),
      ambientAutomorphismConstraintReadout A = 0 ↔
        reducedAutomorphismConstraintReadout P A = 0 := by
  filter_upwards [hP] with A hcomplete
  constructor
  · intro hfull
    exact reducedAutomorphismConstraintReadout_eq_zero_of_ambient_eq_zero P hfull
  · intro hreduced
    exact hcomplete hreduced

/-- Equivalent orientation of the previous local zero-locus theorem, convenient
for using the reduced equations as the local defining equations. -/
theorem eventually_reduced_zero_iff_ambient_zero
    (P : TangentConstraintValues →L[ℝ] W)
    (hP : IsLocallyCompleteAutomorphismConstraintReadout P) :
    ∀ᶠ A in 𝓝 (ContinuousLinearMap.id ℝ CZ),
      reducedAutomorphismConstraintReadout P A = 0 ↔
        ambientAutomorphismConstraintReadout A = 0 := by
  filter_upwards [eventually_ambient_zero_iff_reduced_zero P hP] with A hA
  exact hA.symm

end

end InfoGeometry.Canonical
