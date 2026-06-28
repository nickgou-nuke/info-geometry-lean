import InfoGeometry.Canonical.GeometricMonodromy

/-!
# Geometric Stokes boundary readout, theorem-safe layer

This file records the kernel-checked algebraic consequence of a certified
boundary-angle readout.  External scripts may certify that a concrete planar
current has total boundary angle `2π`; this Lean file does **not** prove a full
analytic Stokes theorem, a distributional de Rham theorem, a GNS construction,
or vacuum annihilation in a Hilbert completion.

Closed content: if the defect boundary angle is `2π`, then the spinorial
half-angle transport is the parity element `-1`, and every real-linear state
reads it as the negative of the unit expectation.

`boundaryAngleDefect_half`, `defect_spinor_transport_eq_neg_one`,
`defect_bivectorExp_half_eq_neg_one`, and the state-level readouts are closed
algebra/trigonometry consequences of the certified angle `2π`.

The interpretation of `boundaryAngleDefect` as the boundary integral of the
planar current is supplied by external scripts:
`proofs/m2_monodromy_defect.m2`, `proofs/sympy_geometric_stokes.py`,
`proofs/sage_geometric_stokes.sage`, and
`proofs/gap_spinorial_monodromy.gap`.
-/

noncomputable section

namespace InfoGeometry.Canonical.GeometricStokes

open InfoGeometry.Canonical.GeometricMonodromy

variable {AInf : Type*} [Ring AInf] [Algebra ℝ AInf]

/-- Certified boundary angle for one positive loop around the model defect. -/
def boundaryAngleDefect : ℝ :=
  2 * Real.pi

/-- Compatibility name for the certified defect angle. -/
def defectBoundaryAngle : ℝ :=
  boundaryAngleDefect

/-- Formal boundary bivector integral once a global real bivector `J` is chosen. -/
def boundaryIntegralDefect (J : AInf) : AInf :=
  boundaryAngleDefect • J

/-- Compatibility name for the formal Stokes bivector residue. -/
def stokesBivectorResidue (J : AInf) : AInf :=
  defectBoundaryAngle • J

/-- The spinorial half-angle associated to the certified defect angle is `π`. -/
theorem boundaryAngleDefect_half :
    boundaryAngleDefect / 2 = Real.pi := by
  unfold boundaryAngleDefect
  ring

@[simp] theorem defectBoundaryAngle_eq :
    defectBoundaryAngle = 2 * Real.pi := by
  rfl

theorem defectBoundaryAngle_half :
    defectBoundaryAngle / 2 = Real.pi := by
  unfold defectBoundaryAngle
  exact boundaryAngleDefect_half

/-- The Stokes residue is definitionally the `2π` multiple of the bivector. -/
theorem stokesBivectorResidue_eq_two_pi_smul (J : AInf) :
    stokesBivectorResidue J = (2 * Real.pi) • J := by
  rfl

/-- The defect boundary readout gives the spinorial parity flip. -/
theorem defect_spinor_transport_eq_neg_one (J : AInf) :
    spinorTransport J boundaryAngleDefect = -(1 : AInf) := by
  unfold boundaryAngleDefect
  exact spinorial_monodromy_around_pole J

/-- Feeding the certified Stokes boundary angle into spinorial transport gives `-1`. -/
theorem stokes_spinorial_parity_flip (J : AInf) :
    spinorTransport J defectBoundaryAngle = -(1 : AInf) := by
  unfold defectBoundaryAngle
  exact defect_spinor_transport_eq_neg_one J

/-- Two certified Stokes loops give the identity spinorial transport. -/
theorem stokes_spinorial_double_loop_identity (J : AInf) :
    spinorTransport J (2 * defectBoundaryAngle) = (1 : AInf) := by
  unfold defectBoundaryAngle boundaryAngleDefect
  have h : 2 * (2 * Real.pi) = 4 * Real.pi := by ring
  rw [h]
  exact spinorial_double_loop_identity J

/-- The same statement written directly with the Euler expression. -/
theorem defect_bivectorExp_half_eq_neg_one (J : AInf) :
    bivectorExp J (boundaryAngleDefect / 2) = -(1 : AInf) := by
  rw [boundaryAngleDefect_half]
  exact bivectorExp_pi J

/-- A real-linear state reads the defect spin transport as minus the unit readout. -/
theorem state_defect_spinor_transport
    (ω : AInf →ₗ[ℝ] ℝ) (J : AInf) :
    ω (spinorTransport J boundaryAngleDefect) = -ω (1 : AInf) := by
  rw [defect_spinor_transport_eq_neg_one]
  exact map_neg ω 1

/-- A real-linear state reads the Stokes spinorial parity flip as sign reversal. -/
theorem stokes_state_parity_flip
    (ω : AInf →ₗ[ℝ] ℝ) (J : AInf) :
    ω (spinorTransport J defectBoundaryAngle) = -ω (1 : AInf) := by
  rw [stokes_spinorial_parity_flip]
  exact map_neg ω 1

/-- Direct Euler-expression form of the same state-level parity readout. -/
theorem state_defect_bivectorExp_half
    (ω : AInf →ₗ[ℝ] ℝ) (J : AInf) :
    ω (bivectorExp J (boundaryAngleDefect / 2)) = -ω (1 : AInf) := by
  rw [defect_bivectorExp_half_eq_neg_one]
  exact map_neg ω 1

/-- Combining the certified angle with the generic monodromy boundary current:
its state readout cancels by linearity. -/
theorem state_defect_monodromyBoundaryCurrent_zero
    (ω : AInf →ₗ[ℝ] ℝ) (J X : AInf) :
    ω (monodromyBoundaryCurrent J X) = 0 :=
  monodromyBoundaryCurrent_state_zero ω J X

/-- The Stokes boundary pair is the spinorially transported unit channel plus itself. -/
def stokesVacuumBoundaryPair (J : AInf) : AInf :=
  spinorTransport J defectBoundaryAngle + (1 : AInf)

/-- The Stokes boundary pair is algebraically zero after one certified loop. -/
theorem stokesVacuumBoundaryPair_eq_zero (J : AInf) :
    stokesVacuumBoundaryPair J = 0 := by
  unfold stokesVacuumBoundaryPair
  rw [stokes_spinorial_parity_flip]
  simp

/-- Any real-linear state kills the Stokes boundary pair. -/
theorem stokes_vacuum_boundary_pair_state_zero
    (ω : AInf →ₗ[ℝ] ℝ) (J : AInf) :
    ω (stokesVacuumBoundaryPair J) = 0 := by
  rw [stokesVacuumBoundaryPair_eq_zero]
  exact map_zero ω

/-- The Stokes boundary pair is the existing monodromy boundary current at `X = 1`. -/
theorem stokesVacuumBoundaryPair_eq_monodromyBoundaryCurrent_one (J : AInf) :
    stokesVacuumBoundaryPair J = monodromyBoundaryCurrent J (1 : AInf) := by
  unfold stokesVacuumBoundaryPair monodromyBoundaryCurrent defectBoundaryAngle boundaryAngleDefect
  simp [add_comm]

/-- The complete Lean packet for the external D-module/geometric-Stokes witnesses. -/
theorem geometric_stokes_spinorial_monodromy_packet
    (ω : AInf →ₗ[ℝ] ℝ) (J : AInf) :
    stokesBivectorResidue J = (2 * Real.pi) • J ∧
      spinorTransport J defectBoundaryAngle = -(1 : AInf) ∧
      ω (spinorTransport J defectBoundaryAngle) = -ω (1 : AInf) ∧
      ω (stokesVacuumBoundaryPair J) = 0 := by
  exact ⟨
    stokesBivectorResidue_eq_two_pi_smul J,
    stokes_spinorial_parity_flip J,
    stokes_state_parity_flip ω J,
    stokes_vacuum_boundary_pair_state_zero ω J⟩

end InfoGeometry.Canonical.GeometricStokes
