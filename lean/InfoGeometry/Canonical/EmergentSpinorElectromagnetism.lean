import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import InfoGeometry.Clifford.DiracPauliGamma
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# InfoGeometry.Canonical.EmergentSpinorElectromagnetism

This module provides the mathematically rigorous resolution to the 
Quaternionic trace grade-parity obstruction (formalized in 
`QuaternionicElectromagnetism.lean`).

Because the macroscopic Quaternionic effective field $Q(x)$ is strictly 
even-graded, bare traces of odd-graded insertions like $\gamma_\mu$ identically 
vanish. To generate the unified geometric fields (the vielbein $e^a_\mu$ and 
the $U(1)$ gauge potential $A_\mu$), the trace must be taken over the 
fundamental internal degrees of freedom: the Spin-1/2 Dirac fields.

This module formalizes the finite spinor-bilinear escape route from the bare
Clifford trace obstruction. It does not prove continuum electromagnetic or
gravitational dynamics. It proves exact component formulas and concrete
nonzero spinor witnesses for the corresponding finite bilinears.

#### BUCKET 1: CLOSED FINITE THEOREMS
The Dirac adjoint and `4 × 4` matrix bilinear are expanded into closed
component formulas for `γ0`, `γ5 γ0`, and `γ5 γ1`. Concrete spinor witnesses
evaluate these bilinears to nonzero values.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES
None.

#### BUCKET 3: OPEN CLOSURE DEBT
This file does not construct a smooth `U(1)` bundle, Maxwell equations,
Einstein-Cartan field equations, Noether currents, or non-Abelian gauge
dynamics.
-/

namespace InfoGeometry.Canonical.EmergentSpinorElectromagnetism

open Matrix
open Complex
open InfoGeometry.Clifford.DiracPauliGamma

/-- 
Dirac adjoint spinor $\bar{\Psi} = \Psi^\dagger \gamma_0$.
We define it as a row vector. 
-/
def diracAdjoint (Psi : DiracSpinor) : Fin 4 → ℂ :=
  fun j => (star Psi 0) * gamma0 0 j + 
           (star Psi 1) * gamma0 1 j + 
           (star Psi 2) * gamma0 2 j + 
           (star Psi 3) * gamma0 3 j

/--
The inner product representing $\bar{\Psi} M \Psi$ for a 4x4 matrix $M$.
-/
def spinorBilinear (Psi : DiracSpinor) (M : DiracMatrix) (Phi : DiracSpinor) : ℂ :=
  let barPsi := diracAdjoint Psi
  (barPsi 0 * (M 0 0 * Phi 0 + M 0 1 * Phi 1 + M 0 2 * Phi 2 + M 0 3 * Phi 3)) +
  (barPsi 1 * (M 1 0 * Phi 0 + M 1 1 * Phi 1 + M 1 2 * Phi 2 + M 1 3 * Phi 3)) +
  (barPsi 2 * (M 2 0 * Phi 0 + M 2 1 * Phi 1 + M 2 2 * Phi 2 + M 2 3 * Phi 3)) +
  (barPsi 3 * (M 3 0 * Phi 0 + M 3 1 * Phi 1 + M 3 2 * Phi 2 + M 3 3 * Phi 3))

/--
The spinor bilinear for the emergent vielbein temporal component
$e^0_0 \sim \bar{\Psi} \gamma_0 \partial_0 \Psi$ has the explicit closed form
`(star Psi 0) * dPsi 0 + (star Psi 1) * dPsi 1 + (star Psi 2) * dPsi 2 +
(star Psi 3) * dPsi 3`.
-/
theorem vielbein_temporal_closed_form (Psi dPsi : DiracSpinor) :
    spinorBilinear Psi gamma0 dPsi = 
      (star Psi 0) * dPsi 0 + (star Psi 1) * dPsi 1 + 
      (star Psi 2) * dPsi 2 + (star Psi 3) * dPsi 3 := by
  simp [spinorBilinear, diracAdjoint, gamma0]

/--
The spinor bilinear for the temporal axial component
$A_0 \sim \bar{\Psi} \gamma_5 \gamma_0 \Psi$ has the explicit closed form 
`-(star Psi 0) * Psi 2 - (star Psi 1) * Psi 3 -
 (star Psi 2) * Psi 0 - (star Psi 3) * Psi 1`.
-/
theorem axial_temporal_closed_form (Psi : DiracSpinor) :
    spinorBilinear Psi (gamma5 * gamma0) Psi = 
      -(star Psi 0) * Psi 2 - (star Psi 1) * Psi 3 
      -(star Psi 2) * Psi 0 - (star Psi 3) * Psi 1 := by
  simp [spinorBilinear, diracAdjoint, gamma0, gamma5, Matrix.mul_apply,
    Fin.sum_univ_succ]
  ring

/--
The spinor bilinear for the spatial axial component
$A_1 \sim \bar{\Psi} \gamma_5 \gamma_1 \Psi$ has the explicit closed form
`-(star Psi 0) * Psi 1 - (star Psi 1) * Psi 0 -
(star Psi 2) * Psi 3 - (star Psi 3) * Psi 2`.
-/
theorem axial_spatial_closed_form (Psi : DiracSpinor) :
    spinorBilinear Psi (gamma5 * gamma1) Psi = 
      -(star Psi 0) * Psi 1 - (star Psi 1) * Psi 0 
      -(star Psi 2) * Psi 3 - (star Psi 3) * Psi 2 := by
  simp [spinorBilinear, diracAdjoint, gamma0, gamma1, gamma5, Matrix.mul_apply,
    Fin.sum_univ_succ]
  ring

/-- A concrete spinor witness with nonzero temporal Dirac bilinear. -/
def spinorWitnessTemporal : DiracSpinor :=
  ![1, 0, 1, 0]

/-- A concrete spinor witness with nonzero spatial Dirac bilinear. -/
def spinorWitnessSpatial : DiracSpinor :=
  ![1, 1, 0, 0]

/-- A concrete spinor witness with nonzero temporal vielbein bilinear. -/
def spinorWitnessGravity : DiracSpinor :=
  ![1, 0, 0, 0]

/-- The temporal vielbein readout is nonzero for an explicit witness. -/
theorem vielbein_temporal_witness_nonzero :
    spinorBilinear spinorWitnessGravity gamma0 spinorWitnessGravity = 1 := by
  rw [vielbein_temporal_closed_form]
  simp [spinorWitnessGravity]

/-- The electromagnetic temporal axial bilinear is nonzero for an explicit witness. -/
theorem a_mu_temporal_witness_nonzero :
    spinorBilinear spinorWitnessTemporal (gamma5 * gamma0) spinorWitnessTemporal = -2 := by
  rw [axial_temporal_closed_form]
  simp [spinorWitnessTemporal]
  ring_nf

/-- The electromagnetic spatial axial bilinear is nonzero for an explicit witness. -/
theorem a_mu_spatial_witness_nonzero :
    spinorBilinear spinorWitnessSpatial (gamma5 * gamma1) spinorWitnessSpatial = -2 := by
  rw [axial_spatial_closed_form]
  simp [spinorWitnessSpatial]
  ring_nf

/-- The temporal vielbein witness is genuinely nonzero. -/
theorem vielbein_temporal_witness_ne_zero :
    spinorBilinear spinorWitnessGravity gamma0 spinorWitnessGravity ≠ 0 := by
  rw [vielbein_temporal_witness_nonzero]
  norm_num

/-- The temporal axial witness is genuinely nonzero. -/
theorem axial_temporal_witness_ne_zero :
    spinorBilinear spinorWitnessTemporal (gamma5 * gamma0) spinorWitnessTemporal ≠ 0 := by
  rw [a_mu_temporal_witness_nonzero]
  norm_num

/-- The spatial axial witness is genuinely nonzero. -/
theorem axial_spatial_witness_ne_zero :
    spinorBilinear spinorWitnessSpatial (gamma5 * gamma1) spinorWitnessSpatial ≠ 0 := by
  rw [a_mu_spatial_witness_nonzero]
  norm_num

end InfoGeometry.Canonical.EmergentSpinorElectromagnetism
