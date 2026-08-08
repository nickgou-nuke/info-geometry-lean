import InfoGeometry.Meta.Architecture
import Mathlib.Tactic

/-!
# InfoGeometry.Canonical.HodgeDiracLaplacianBridge

Thin algebraic Hodge--Dirac--Laplacian socket.

This file does not construct a global Hodge theory and does not assert a
signature-independent `*² = -1` law.  The Hodge/phase convention is supplied as
an explicit predicate.  The theorem-level payload is the elementary algebraic
readback:

```text
{Q, *} = 0  ->  [Q², *] = 0.
```

Thus an odd Dirac/supercharge operator has a Hodge-even square, provided the
chosen Hodge/phase axis anticommutes with it.
-/

namespace InfoGeometry.Canonical.HodgeDiracLaplacianBridge

/--
Carrier for a Hodge/Dirac/Laplacian readout.

The carrier is the native nested product `Op × (Op × (Op × Op))`; its four
coordinates are exposed by the accessors below.  No custom evidence structure
is needed for a tuple of operators.
-/
@[rep_depth operator]
abbrev HodgeDiracLaplacianCarrier (Op : Type*) :=
  Op × (Op × (Op × Op))

def hodgeStar {Op : Type*} (C : HodgeDiracLaplacianCarrier Op) : Op :=
  C.1

def dirac {Op : Type*} (C : HodgeDiracLaplacianCarrier Op) : Op :=
  C.2.1

def laplacian {Op : Type*} (C : HodgeDiracLaplacianCarrier Op) : Op :=
  C.2.2.1

def centralReadout {Op : Type*} (C : HodgeDiracLaplacianCarrier Op) : Op :=
  C.2.2.2

/--
Phase convention for the Hodge star.

This is intentionally external: `*² = -1` depends on degree, dimension, and
signature convention.
-/
@[rep_depth operator]
def IsHodgePhase {Op : Type*} [Ring Op] (C : HodgeDiracLaplacianCarrier Op) : Prop :=
  hodgeStar C * hodgeStar C = -(1 : Op)

/-- The Dirac/supercharge anticommutes with the supplied Hodge/phase axis. -/
@[rep_depth operator]
def IsDiracHodgeChiral {Op : Type*} [Ring Op]
    (C : HodgeDiracLaplacianCarrier Op) : Prop :=
  dirac C * hodgeStar C = -(hodgeStar C * dirac C)

/-- The Laplacian is supplied as the square of the Dirac/supercharge. -/
@[rep_depth operator]
def IsLaplacianFromDirac {Op : Type*} [Ring Op]
    (C : HodgeDiracLaplacianCarrier Op) : Prop :=
  laplacian C = dirac C * dirac C

/-- Direct readback of the supplied Hodge phase convention. -/
@[rep_depth operator]
theorem hodge_phase_sq_eq_neg_one
    {Op : Type*} [Ring Op]
    (C : HodgeDiracLaplacianCarrier Op)
    (hStar : IsHodgePhase C) :
    hodgeStar C * hodgeStar C = -(1 : Op) :=
  hStar

/-- Direct readback of the supplied Dirac/Hodge chirality law. -/
@[rep_depth operator]
theorem dirac_anticommutes_hodge
    {Op : Type*} [Ring Op]
    (C : HodgeDiracLaplacianCarrier Op)
    (hChiral : IsDiracHodgeChiral C) :
    dirac C * hodgeStar C = -(hodgeStar C * dirac C) :=
  hChiral

/-- Direct readback that the Laplacian is the Dirac square. -/
@[rep_depth operator]
theorem laplacian_eq_dirac_sq_of_closure
    {Op : Type*} [Ring Op]
    (C : HodgeDiracLaplacianCarrier Op)
    (hDelta : IsLaplacianFromDirac C) :
    laplacian C = dirac C * dirac C :=
  hDelta

/--
Algebraic Hodge--Dirac--Laplacian theorem.

If the Dirac/supercharge anticommutes with the Hodge/phase operator, then its
square commutes with that Hodge/phase operator.
-/
@[rep_depth operator]
theorem dirac_sq_commutes_hodge
    {Op : Type*} [Ring Op]
    (star Q : Op)
    (hAnti : Q * star = -(star * Q)) :
    (Q * Q) * star = star * (Q * Q) := by
  calc
    (Q * Q) * star = Q * (Q * star) := by
      rw [mul_assoc]
    _ = Q * (-(star * Q)) := by
      rw [hAnti]
    _ = -(Q * (star * Q)) := by
      simp
    _ = -((Q * star) * Q) := by
      rw [mul_assoc]
    _ = -((-(star * Q)) * Q) := by
      rw [hAnti]
    _ = star * (Q * Q) := by
      simp [mul_assoc]

/-- Carrier-level version: the Dirac square commutes with the supplied Hodge axis. -/
@[rep_depth operator]
theorem dirac_sq_commutes_hodge_of_chiral
    {Op : Type*} [Ring Op]
    (C : HodgeDiracLaplacianCarrier Op)
    (hChiral : IsDiracHodgeChiral C) :
    (dirac C * dirac C) * hodgeStar C =
      hodgeStar C * (dirac C * dirac C) :=
  dirac_sq_commutes_hodge (hodgeStar C) (dirac C) hChiral

/-- If `Δ = Q²`, then the supplied Laplacian commutes with the Hodge axis. -/
@[rep_depth operator]
theorem laplacian_commutes_hodge_of_dirac_closure
    {Op : Type*} [Ring Op]
    (C : HodgeDiracLaplacianCarrier Op)
    (hChiral : IsDiracHodgeChiral C)
    (hDelta : IsLaplacianFromDirac C) :
    laplacian C * hodgeStar C =
      hodgeStar C * laplacian C := by
  rw [hDelta]
  exact dirac_sq_commutes_hodge_of_chiral C hChiral

/--
Central readout remains property-gated.

This is intentionally a property-gated interface for downstream affine/Sugawara
calibration. No central-charge theorem is asserted in this Hodge/Dirac bridge.
-/
@[rep_depth operator]
abbrev CentralReadoutWitness
    {Op : Type*} [Ring Op]
    (C : HodgeDiracLaplacianCarrier Op) : Prop :=
  ∀ A : Op, Commute (centralReadout C) A

/--
Owner-facing central-readout gate: the bridge exports only a supplied property
whose readout is tied to the carrier readout.
-/
@[rep_depth operator]
def IsCentralReadoutFromLaplacianAnomaly
    {Op : Type*} [Ring Op]
    (C : HodgeDiracLaplacianCarrier Op) : Prop :=
  ∀ A : Op, Commute (centralReadout C) A

/-- Readback from a central/anomaly property to the carrier readout. -/
@[rep_depth operator]
theorem centralReadout_eq_carrier_of_property
    {Op : Type*} [Ring Op]
    (C : HodgeDiracLaplacianCarrier Op)
    (W : CentralReadoutWitness C) :
    centralReadout C = centralReadout C ∧
      IsCentralReadoutFromLaplacianAnomaly C :=
  ⟨rfl, W⟩

/-- A genuine centrality property transfers to the carrier readout. -/
@[rep_depth operator]
theorem centralReadout_isCentral_of_property
    {Op : Type*} [Ring Op]
    (C : HodgeDiracLaplacianCarrier Op)
    (W : CentralReadoutWitness C) :
    IsCentralReadoutFromLaplacianAnomaly C := by
  exact W

end InfoGeometry.Canonical.HodgeDiracLaplacianBridge
