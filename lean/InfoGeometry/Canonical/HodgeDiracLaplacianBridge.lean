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

`centralReadout` is deliberately only a field.  This module does not identify it
with a Virasoro/Kac--Moody central charge; that belongs to the affine/Sugawara
lane after the relevant current data are supplied.
-/
@[rep_depth operator]
structure HodgeDiracLaplacianCarrier (Op : Type*) where
  /-- Supplied Hodge star / phase / chirality operator. -/
  hodgeStar : Op

  /-- Supplied Dirac or supercharge-like odd operator. -/
  dirac : Op

  /-- Supplied Laplacian or even Hamiltonian-like operator. -/
  laplacian : Op

  /-- Supplied central/anomaly readout token. -/
  centralReadout : Op

/--
Phase convention for the Hodge star.

This is intentionally external: `*² = -1` depends on degree, dimension, and
signature convention.
-/
@[rep_depth operator]
def IsHodgePhase {Op : Type*} [Ring Op] (C : HodgeDiracLaplacianCarrier Op) : Prop :=
  C.hodgeStar * C.hodgeStar = -(1 : Op)

/-- The Dirac/supercharge anticommutes with the supplied Hodge/phase axis. -/
@[rep_depth operator]
def IsDiracHodgeChiral {Op : Type*} [Ring Op]
    (C : HodgeDiracLaplacianCarrier Op) : Prop :=
  C.dirac * C.hodgeStar = -(C.hodgeStar * C.dirac)

/-- The Laplacian is supplied as the square of the Dirac/supercharge. -/
@[rep_depth operator]
def IsLaplacianFromDirac {Op : Type*} [Ring Op]
    (C : HodgeDiracLaplacianCarrier Op) : Prop :=
  C.laplacian = C.dirac * C.dirac

/-- Direct readback of the supplied Hodge phase convention. -/
@[rep_depth operator]
theorem hodge_phase_sq_eq_neg_one
    {Op : Type*} [Ring Op]
    (C : HodgeDiracLaplacianCarrier Op)
    (hStar : IsHodgePhase C) :
    C.hodgeStar * C.hodgeStar = -(1 : Op) :=
  hStar

/-- Direct readback of the supplied Dirac/Hodge chirality law. -/
@[rep_depth operator]
theorem dirac_anticommutes_hodge
    {Op : Type*} [Ring Op]
    (C : HodgeDiracLaplacianCarrier Op)
    (hChiral : IsDiracHodgeChiral C) :
    C.dirac * C.hodgeStar = -(C.hodgeStar * C.dirac) :=
  hChiral

/-- Direct readback that the Laplacian is the Dirac square. -/
@[rep_depth operator]
theorem laplacian_eq_dirac_sq_of_closure
    {Op : Type*} [Ring Op]
    (C : HodgeDiracLaplacianCarrier Op)
    (hDelta : IsLaplacianFromDirac C) :
    C.laplacian = C.dirac * C.dirac :=
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
    (C.dirac * C.dirac) * C.hodgeStar =
      C.hodgeStar * (C.dirac * C.dirac) :=
  dirac_sq_commutes_hodge C.hodgeStar C.dirac hChiral

/-- If `Δ = Q²`, then the supplied Laplacian commutes with the Hodge axis. -/
@[rep_depth operator]
theorem laplacian_commutes_hodge_of_dirac_closure
    {Op : Type*} [Ring Op]
    (C : HodgeDiracLaplacianCarrier Op)
    (hChiral : IsDiracHodgeChiral C)
    (hDelta : IsLaplacianFromDirac C) :
    C.laplacian * C.hodgeStar =
      C.hodgeStar * C.laplacian := by
  rw [hDelta]
  exact dirac_sq_commutes_hodge_of_chiral C hChiral

/--
Central readout remains witness-gated.

This is intentionally a witness-gated interface for downstream affine/Sugawara
calibration. No central-charge theorem is asserted in this Hodge/Dirac bridge.
-/
@[rep_depth operator]
abbrev CentralReadoutWitness
    {Op : Type*} [Ring Op]
    (C : HodgeDiracLaplacianCarrier Op) : Type _ :=
  Σ' centralReadout : Op,
    centralReadout = C.centralReadout ∧
      ∀ A : Op, Commute centralReadout A

namespace CentralReadoutWitness

abbrev centralReadout
    {Op : Type*} [Ring Op]
    {C : HodgeDiracLaplacianCarrier Op}
    (W : CentralReadoutWitness C) : Op :=
  W.1

abbrev centralReadout_eq_carrier
    {Op : Type*} [Ring Op]
    {C : HodgeDiracLaplacianCarrier Op}
    (W : CentralReadoutWitness C) :
    W.centralReadout = C.centralReadout :=
  W.2.1

abbrev centrality
    {Op : Type*} [Ring Op]
    {C : HodgeDiracLaplacianCarrier Op}
    (W : CentralReadoutWitness C) :
    ∀ A : Op, Commute W.centralReadout A :=
  W.2.2

end CentralReadoutWitness

/--
Owner-facing central-readout gate: the bridge exports only a supplied witness
whose readout is tied to the carrier readout.
-/
@[rep_depth operator]
def IsCentralReadoutFromLaplacianAnomaly
    {Op : Type*} [Ring Op]
    (C : HodgeDiracLaplacianCarrier Op) : Prop :=
  ∀ A : Op, Commute C.centralReadout A

/-- Readback from a central/anomaly witness to the carrier readout. -/
@[rep_depth operator]
theorem centralReadout_eq_carrier_of_witness
    {Op : Type*} [Ring Op]
    (C : HodgeDiracLaplacianCarrier Op)
    (W : CentralReadoutWitness C) :
    W.centralReadout = C.centralReadout :=
  W.centralReadout_eq_carrier

/-- Readback that the central/anomaly gate supplies a carrier-tied readout. -/
@[rep_depth operator]
theorem centralReadout_is_witness_gated
    {Op : Type*} [Ring Op]
    (C : HodgeDiracLaplacianCarrier Op)
    (h : IsCentralReadoutFromLaplacianAnomaly C) :
    IsCentralReadoutFromLaplacianAnomaly C :=
  h

/-- A genuine centrality witness transfers to the carrier readout. -/
@[rep_depth operator]
theorem centralReadout_isCentral_of_witness
    {Op : Type*} [Ring Op]
    (C : HodgeDiracLaplacianCarrier Op)
    (W : CentralReadoutWitness C) :
    IsCentralReadoutFromLaplacianAnomaly C := by
  intro A
  rw [← W.centralReadout_eq_carrier]
  exact W.centrality A

end InfoGeometry.Canonical.HodgeDiracLaplacianBridge
