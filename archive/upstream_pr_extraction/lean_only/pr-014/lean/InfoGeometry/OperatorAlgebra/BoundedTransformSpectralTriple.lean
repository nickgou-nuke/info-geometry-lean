/-
InfoGeometry/OperatorAlgebra/BoundedTransformSpectralTriple.lean

Bounded Cayley and bounded-transform sockets for spectral triples.

This module avoids committing to a full unbounded-operator/domain API.

Instead, an unbounded spectral generator is represented by bounded proxies:

* Cayley transform:
    U = (D - K)(D + K)^(-1)

* bounded transform:
    F = D(1 + D^2)^(-1/2)

The analytic facts that these proxies come from a closed, densely-defined
self-adjoint operator are carried as proof/certificate fields.
-/

import Mathlib
import InfoGeometry.OperatorAlgebra.SpectralTriple

noncomputable section

namespace InfoGeometry.OperatorAlgebra.BoundedTransformSpectralTriple

open InfoGeometry.OperatorAlgebra.SpectralTriple
open InfoGeometry.Geometry.PhaseErlanger

set_option linter.dupNamespace false

/-! ## 1. Closed unbounded source socket -/

/--
A closed, densely-defined self-adjoint source operator socket.

This deliberately does not define a full unbounded operator API. It records
the analytic source data as proof-carrying certificates.
-/
structure ClosedSelfAdjointSource
    (H : Type*) [NormedAddCommGroup H] [NormedSpace ℝ H] where
  /-- Domain carrier or graph object, left abstract. -/
  Domain : Type*

  /-- Formal action of the unbounded generator on its domain. -/
  apply : Domain → H

  /-- Inclusion of the domain into the Hilbert/Krein carrier. -/
  includeDomain : Domain → H

  /-- Densely-defined certificate. -/
  denselyDefined_law : Prop
  denselyDefined_certificate :
    denselyDefined_law

  /-- Closed-graph certificate. -/
  closedGraph_law : Prop
  closedGraph_certificate :
    closedGraph_law

  /-- Self-adjoint or Krein-self-adjoint certificate. -/
  selfAdjoint_law : Prop
  selfAdjoint_certificate :
    selfAdjoint_law

/-! ## 2. Bounded Cayley transform datum -/

/--
Bounded Cayley transform datum for a spectral generator.

For a genuine unbounded self-adjoint `D`, this is intended as

`U = (D - K)(D + K)^(-1)`.

The actual domain/resolvent theorem is carried as `cayley_source_law`.
-/
structure CayleyTransformDatum
    (H : Type*) [NormedAddCommGroup H] [NormedSpace ℝ H]
    (K : PhaseAxis H) where
  /-- Bounded Cayley transform. -/
  U : SpectralTriple.EndR H

  /-- The Cayley transform is phase-compatible. -/
  U_phase_linear :
    PhaseLinear K.K U

  /-- Unitary/isometric law, model-dependent. -/
  unitary_law : Prop
  unitary_certificate :
    unitary_law

  /--
  Source law: `U` is the Cayley transform of the intended closed operator.
  This is where `(D + K)^(-1)` and the resolvent theorem enter.
  -/
  cayley_source_law : Prop
  cayley_source_certificate :
    cayley_source_law

  /--
  Recovery/domain law: the Cayley transform determines the unbounded source on
  the appropriate domain, e.g. via `(1 - U)` range data.
  -/
  recovery_law : Prop
  recovery_certificate :
    recovery_law

namespace CayleyTransformDatum

variable
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {K : PhaseAxis H}

variable (C : CayleyTransformDatum H K)

/-- Re-export phase-linearity of the Cayley transform. -/
theorem phase_linear :
    PhaseLinear K.K C.U :=
  C.U_phase_linear

end CayleyTransformDatum

/-! ## 3. Bounded phase-resolvent and Cayley formula -/

/-- The phase axis is phase-linear relative to itself. -/
theorem phaseLinear_self
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (K : SpectralTriple.EndR H) :
    PhaseLinear K K :=
  rfl

/--
A bounded phase-resolvent datum for `D + K`.

This is the finite/bounded version of saying that `-K` lies in the resolvent
set of the spectral generator.  It supplies the inverse of `D + K` together
with its phase-linearity.
-/
structure PhaseResolventDatum
    (H : Type*) [NormedAddCommGroup H] [NormedSpace ℝ H]
    (K : PhaseAxis H)
    (D : SpectralTriple.EndR H) where
  /-- Supplied inverse for `D + K`. -/
  denomInv : SpectralTriple.EndR H

  /-- Right inverse law. -/
  denom_right :
    (D + K.K).comp denomInv = ContinuousLinearMap.id ℝ H

  /-- Left inverse law. -/
  denom_left :
    denomInv.comp (D + K.K) = ContinuousLinearMap.id ℝ H

  /-- Phase-compatibility of `D`. -/
  D_phase_linear :
    PhaseLinear K.K D

  /-- Phase-compatibility of the denominator inverse. -/
  denomInv_phase_linear :
    PhaseLinear K.K denomInv

/-- The bounded Cayley transform `U = (D - K)(D + K)^(-1)`. -/
def boundedCayley
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {K : PhaseAxis H}
    (D : SpectralTriple.EndR H)
    (R : PhaseResolventDatum H K D) :
    SpectralTriple.EndR H :=
  (D - K.K).comp R.denomInv

/--
The bounded Cayley transform is phase-linear, derived from phase-linearity of
`D`, `K`, and the supplied phase-resolvent inverse.
-/
theorem boundedCayley_phase_linear
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {K : PhaseAxis H}
    (D : SpectralTriple.EndR H)
    (R : PhaseResolventDatum H K D) :
    PhaseLinear K.K (boundedCayley D R) := by
  dsimp [boundedCayley]
  exact
    PhaseLinear.comp
      (PhaseLinear.sub R.D_phase_linear (phaseLinear_self K.K))
      R.denomInv_phase_linear

namespace PhaseResolventDatum

variable
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {K : PhaseAxis H}
    {D : SpectralTriple.EndR H}

variable (R : PhaseResolventDatum H K D)

/-- The Cayley transform associated to the phase resolvent. -/
def cayley : SpectralTriple.EndR H :=
  boundedCayley D R

/-- Re-export phase-linearity of the associated Cayley transform. -/
theorem cayley_phase_linear :
    PhaseLinear K.K R.cayley :=
  boundedCayley_phase_linear D R

end PhaseResolventDatum

/--
Concrete bounded Cayley formula datum.

This is useful for the current bounded `SpectralGenerator` socket, where `D`
already lives in `EndR H`.

The inverse of `D + K` is supplied by the phase-resolvent datum. The Cayley
transform and inverse laws are then derived, not carried as parallel
hypotheses.
-/
structure BoundedCayleyFormulaDatum
    (H : Type*) [NormedAddCommGroup H] [NormedSpace ℝ H]
    (K : PhaseAxis H) where
  /-- Bounded spectral generator. -/
  D : SpectralTriple.EndR H

  /-- Phase-resolvent data for `D + K`. -/
  resolvent :
    PhaseResolventDatum H K D

namespace BoundedCayleyFormulaDatum

variable
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {K : PhaseAxis H}

variable (C : BoundedCayleyFormulaDatum H K)

/-- The denominator inverse supplied by the phase-resolvent datum. -/
def denomInv : SpectralTriple.EndR H :=
  C.resolvent.denomInv

/-- The Cayley transform supplied by the phase-resolvent formula. -/
def cayley : SpectralTriple.EndR H :=
  boundedCayley C.D C.resolvent

/-- Re-export the right inverse law from the phase-resolvent datum. -/
theorem denom_right :
    (C.D + K.K).comp C.denomInv = ContinuousLinearMap.id ℝ H :=
  C.resolvent.denom_right

/-- Re-export the left inverse law from the phase-resolvent datum. -/
theorem denom_left :
    C.denomInv.comp (C.D + K.K) = ContinuousLinearMap.id ℝ H :=
  C.resolvent.denom_left

/-- Re-export the bounded Cayley formula. -/
theorem formula :
    C.cayley = (C.D - K.K).comp C.denomInv :=
  rfl

/-- Re-export phase-linearity of the bounded Cayley transform. -/
theorem phase_linear :
    PhaseLinear K.K C.cayley :=
  boundedCayley_phase_linear C.D C.resolvent

end BoundedCayleyFormulaDatum

/-! ## 4. Bounded transform datum -/

/--
Bounded transform datum for a spectral generator.

For an unbounded self-adjoint `D`, this is intended as

`F = D(1 + D^2)^(-1/2)`.

The functional-calculus construction is carried as proof data.
-/
structure BoundedTransformDatum
    (H : Type*) [NormedAddCommGroup H] [NormedSpace ℝ H]
    (K : PhaseAxis H) where
  /-- Bounded transform of the spectral generator. -/
  F : SpectralTriple.EndR H

  /-- Phase-compatibility of the bounded transform. -/
  F_phase_linear :
    PhaseLinear K.K F

  /-- Self-adjoint/Krein-self-adjoint certificate. -/
  selfAdjoint_law : Prop
  selfAdjoint_certificate :
    selfAdjoint_law

  /-- Contraction or boundedness certificate. -/
  bounded_transform_law : Prop
  bounded_transform_certificate :
    bounded_transform_law

  /-- Summability/Fredholm/compact-defect certificate. -/
  fredholm_or_summability_law : Prop
  fredholm_or_summability_certificate :
    fredholm_or_summability_law

  /--
  Source law: `F` is the bounded transform of the intended unbounded spectral
  generator.
  -/
  source_transform_law : Prop
  source_transform_certificate :
    source_transform_law

namespace BoundedTransformDatum

variable
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {K : PhaseAxis H}

variable (B : BoundedTransformDatum H K)

/-- Re-export phase-linearity. -/
theorem phase_linear :
    PhaseLinear K.K B.F :=
  B.F_phase_linear

end BoundedTransformDatum

/-! ## 5. Bridge from unbounded source to bounded spectral triple -/

/--
Unbounded-to-bounded spectral generator bridge.

This packages the closed unbounded source together with its bounded Cayley and
bounded-transform proxies.

Downstream spectral-triple modules should reason through the bounded proxies
unless they explicitly need domain calculus.
-/
structure UnboundedSpectralBridge
    (H : Type*) [NormedAddCommGroup H] [NormedSpace ℝ H]
    (K : PhaseAxis H) where
  /-- Closed, densely-defined source generator. -/
  source :
    ClosedSelfAdjointSource H

  /-- Cayley transform proxy. -/
  cayley :
    CayleyTransformDatum H K

  /-- Bounded transform proxy. -/
  boundedTransform :
    BoundedTransformDatum H K

  /--
  Compatibility law between the Cayley proxy and bounded-transform proxy.
  This is model-dependent.
  -/
  cayley_boundedTransform_compatible_law : Prop

  /-- Proof/certificate of compatibility. -/
  cayley_boundedTransform_compatible_certificate :
    cayley_boundedTransform_compatible_law

/-! ## 6. Bounded-transform spectral triple socket -/

/--
A phase-real spectral triple equipped with a bounded-transform proxy.

This is the preferred Lean-facing replacement for directly carrying an
unbounded `D` through all downstream modules.
-/
structure BoundedTransformSpectralTriple
    (A H : Type*)
    [Ring A] [Star A]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] where
  /-- Underlying bounded spectral triple socket. -/
  triple :
    PhaseRealSpectralTriple A H

  /--
  Optional Cayley transform proxy.

  Kasparov-style modules may only need the bounded transform `F`, while
  phase/resolvent geometry can supply the Cayley proxy `U`.
  -/
  cayley :
    Option (CayleyTransformDatum H triple.phaseAxis)

  /-- Bounded transform of the intended spectral generator. -/
  boundedTransform :
    BoundedTransformDatum H triple.phaseAxis

  /--
  Metric sensor compatibility.

  This is where the model states that commutator/Lipschitz readouts using the
  bounded transform agree with the intended unbounded spectral geometry.
  -/
  metric_sensor_compatibility_law : Prop

  /-- Proof/certificate of the metric compatibility law. -/
  metric_sensor_compatibility_certificate :
    metric_sensor_compatibility_law

namespace BoundedTransformSpectralTriple

variable
    {A H : Type*}
    [Ring A] [Star A]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]

variable (T : BoundedTransformSpectralTriple A H)

/-- Re-export the bounded transform phase-linearity. -/
theorem boundedTransform_phase_linear :
    PhaseLinear T.triple.phaseAxis.K T.boundedTransform.F :=
  BoundedTransformDatum.phase_linear T.boundedTransform

/-- If a Cayley proxy is supplied, it is phase-linear. -/
theorem cayley_phase_linear_of_some
    {C : CayleyTransformDatum H T.triple.phaseAxis}
    (hC : T.cayley = some C) :
    PhaseLinear T.triple.phaseAxis.K C.U := by
  have _supplied := hC
  exact C.phase_linear

/-- Re-export the underlying Lipschitz seminorm. -/
def lipschitz
    (a : A) : ℝ :=
  T.triple.lipschitz a

/-- Lipschitz seminorm is nonnegative. -/
theorem lipschitz_nonneg
    (a : A) :
    0 ≤ T.lipschitz a :=
  T.triple.lipschitz_nonneg a

end BoundedTransformSpectralTriple

/-! ## 7. Owner target -/

/--
Owner target for installing a bounded-transform spectral triple.
-/
def BoundedTransformSpectralTripleOwnerTarget
    (A H : Type*)
    [Ring A] [Star A]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] : Prop :=
  Nonempty (BoundedTransformSpectralTriple A H)

end InfoGeometry.OperatorAlgebra.BoundedTransformSpectralTriple
