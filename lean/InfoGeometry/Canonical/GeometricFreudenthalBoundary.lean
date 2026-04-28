import Mathlib
import InfoGeometry.Canonical.GeometricCalculusSurgery

/-!
# InfoGeometry/Canonical/GeometricFreudenthalBoundary.lean

Structural bridge between real Clifford/Stokes boundary flux and the
Freudenthal charge horizon.

This file does not assert that the geometric flux theorem has been proved.
It provides the witness interface by which a scalar readout of the Stokes
flux projector may be identified with the Freudenthal quartic invariant.
-/

namespace InfoGeometry.Canonical.GeometricCalculus

open MeasureTheory
open Topology

noncomputable section

/--
Freudenthal charge data.

`I4` is the quartic invariant of the charge vector.

`horizon` is the rank-collapse / small-black-hole boundary, represented
abstractly as the zero locus of `I4`.

`entropy` is kept as a field because different normalizations may occur in
different physical conventions. The default expected normalization is

`entropy q = π * sqrt |I4 q|`.
-/
structure FreudenthalChargeDatum
    (Q : Type*) [NormedAddCommGroup Q] [NormedSpace ℝ Q] where
  I4 : Q → ℝ
  horizon : Set Q
  entropy : Q → ℝ

  horizon_iff_quartic_zero :
    ∀ q : Q, q ∈ horizon ↔ I4 q = 0

  entropy_formula :
    ∀ q : Q, entropy q = Real.pi * Real.sqrt |I4 q|

/--
The logarithmic Freudenthal barrier.

This is a symbolic potential. Its analytic divergence at `I4 = 0` should later
be stated as a limit theorem, not as an equality at the boundary point.
-/
def freudenthalPotential
    {Q : Type*} [NormedAddCommGroup Q] [NormedSpace ℝ Q]
    (D : FreudenthalChargeDatum Q)
    (q : Q) : ℝ :=
  - Real.log |D.I4 q|

/--
A Stokes/Freudenthal bridge.

The bridge says that the scalar readout of the geometric Stokes flux projector
is exactly the Freudenthal quartic invariant.

This is the correct structural statement:

`readout (∫_{∂Ω(q)} dS · R(p)) = I4(q)`.

Entropy and horizon statements are then derived from the Freudenthal datum.
-/
structure StokesFreudenthalBridge
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {Q : Type*} [NormedAddCommGroup Q] [NormedSpace ℝ Q]
    {ρ : ParavectorRepresentation P E}
    {A : RealEnd E}
    (D : FreudenthalChargeDatum Q) where

  /-- Clifford resolvent field for the operator whose flux is measured. -/
  R : CliffordResolventField ρ A

  /-- Charge-dependent geometric boundary. -/
  boundary : Q → DirectedBoundary P E

  /-- Charge-dependent normalization of the flux integral. -/
  normalization : Q → ℝ

  /-- Stokes/Clifford witness for every charge boundary. -/
  stokesWitness :
    ∀ q : Q, StokesFluxWitness R (boundary q) (normalization q)

  /-- Scalar extraction from an operator-valued flux. -/
  scalarReadout : RealEnd E → ℝ

  /--
  Fundamental flux/quartic readout.

  This is the bridge from microscopic geometric flux to the macroscopic
  Freudenthal invariant.
  -/
  flux_eq_quartic :
    ∀ q : Q,
      scalarReadout
        (geometricFluxProjector (boundary q) R.R (normalization q))
        = D.I4 q

namespace StokesFreudenthalBridge

variable
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {Q : Type*} [NormedAddCommGroup Q] [NormedSpace ℝ Q]
    {ρ : ParavectorRepresentation P E}
    {A : RealEnd E}
    {D : FreudenthalChargeDatum Q}

/-- The scalar flux assigned to a charge state. -/
def flux
    (W : StokesFreudenthalBridge (ρ := ρ) (A := A) D)
    (q : Q) : ℝ :=
  W.scalarReadout
    (geometricFluxProjector (W.boundary q) W.R.R (W.normalization q))

/-- The scalar flux is the Freudenthal quartic invariant. -/
theorem flux_eq_I4
    (W : StokesFreudenthalBridge (ρ := ρ) (A := A) D)
    (q : Q) :
    W.flux q = D.I4 q := by
  simpa [flux] using W.flux_eq_quartic q

/--
The geometric flux vanishes exactly on the Freudenthal horizon.
-/
theorem horizon_iff_flux_zero
    (W : StokesFreudenthalBridge (ρ := ρ) (A := A) D)
    (q : Q) :
    q ∈ D.horizon ↔ W.flux q = 0 := by
  constructor
  · intro hq
    have hI4 : D.I4 q = 0 := (D.horizon_iff_quartic_zero q).mp hq
    rw [W.flux_eq_I4 q, hI4]
  · intro hflux
    apply (D.horizon_iff_quartic_zero q).mpr
    rwa [W.flux_eq_I4 q] at hflux

/--
Entropy readout through the geometric flux.

This is the safe derived statement:

`S(q) = π √|flux(q)|`.
-/
theorem entropy_eq_sqrt_abs_flux
    (W : StokesFreudenthalBridge (ρ := ρ) (A := A) D)
    (q : Q) :
    D.entropy q = Real.pi * Real.sqrt |W.flux q| := by
  calc
    D.entropy q = Real.pi * Real.sqrt |D.I4 q| := D.entropy_formula q
    _ = Real.pi * Real.sqrt |W.flux q| := by
      rw [← W.flux_eq_I4 q]

end StokesFreudenthalBridge

end

end InfoGeometry.Canonical.GeometricCalculus
