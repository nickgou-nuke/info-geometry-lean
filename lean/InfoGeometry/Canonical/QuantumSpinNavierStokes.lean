import InfoGeometry.Canonical.NavierStokesBridge
import Mathlib.Tactic

/-!
# Quantum-spin readback for the linearized fluid bridge

This module names the two canonical linear polarization channels already owned
by NavierStokesBridge:

* spinVelocity is the skew-adjoint/vorticity channel;
* strainVelocity is the self-adjoint/strain channel.

The two-sheet frame below is a finite linear readback. It does not introduce
a spatial or temporal Navier--Stokes PDE, a pressure projection, viscosity
estimates, a blow-up theorem, or a physical superluminal propagation claim.
-/

noncomputable section

namespace InfoGeometry.Canonical.QuantumSpinNavierStokes

open scoped InnerProductSpace

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The spin/vorticity channel of a linearized velocity Jacobian. -/
noncomputable def spinVelocity
    (u : VelocityField E) : VelocityField E :=
  vorticity u

/-- The strain channel of a linearized velocity Jacobian. -/
noncomputable def strainVelocity
    (u : VelocityField E) : VelocityField E :=
  strainRate u

/-- A two-sheeted linear frame with spin and strain channels. -/
structure TwoSheetSpinFrame where
  spin : VelocityField E
  strain : VelocityField E

/-- Canonical two-sheet frame extracted from one linearized velocity field. -/
noncomputable def twoSheetSpinFrame
    (u : VelocityField E) : TwoSheetSpinFrame (E := E) where
  spin := spinVelocity u
  strain := strainVelocity u

@[simp] theorem twoSheetSpinFrame_spin (u : VelocityField E) :
    (twoSheetSpinFrame u).spin = spinVelocity u :=
  rfl

@[simp] theorem twoSheetSpinFrame_strain (u : VelocityField E) :
    (twoSheetSpinFrame u).strain = strainVelocity u :=
  rfl

/-- The named spin channel is exactly the existing vorticity readout. -/
@[simp] theorem spinVelocity_eq_vorticity (u : VelocityField E) :
    spinVelocity u = vorticity u :=
  rfl

/-- The named strain channel is exactly the existing strain readout. -/
@[simp] theorem strainVelocity_eq_strainRate (u : VelocityField E) :
    strainVelocity u = strainRate u :=
  rfl

/-- The spin channel is skew-adjoint. -/
theorem adjoint_spinVelocity_eq_neg (u : VelocityField E) :
    ContinuousLinearMap.adjoint (spinVelocity u) = -spinVelocity u := by
  simpa [spinVelocity] using
    (adjoint_vorticity_eq_neg (E := E) u)

/-- The strain channel is self-adjoint. -/
theorem adjoint_strainVelocity_eq_self (u : VelocityField E) :
    ContinuousLinearMap.adjoint (strainVelocity u) = strainVelocity u := by
  simpa [strainVelocity] using
    (adjoint_strainRate_eq_self (E := E) u)

/-- The two channels reconstruct the original linearized velocity field. -/
theorem twoSheetSpinFrame_reconstruct (u : VelocityField E) :
    (twoSheetSpinFrame u).strain + (twoSheetSpinFrame u).spin = u := by
  simpa [twoSheetSpinFrame, spinVelocity, strainVelocity] using
    (strainRate_add_vorticity_eq (E := E) u)

/-- Reconstruction is independent of whether the two sheets are read first or second. -/
theorem twoSheetSpinFrame_reconstruct_spin_first (u : VelocityField E) :
    (twoSheetSpinFrame u).spin + (twoSheetSpinFrame u).strain = u := by
  simpa [add_comm] using twoSheetSpinFrame_reconstruct (E := E) u

/-- The canonical spin channel is trace-free in finite dimension. -/
theorem spinVelocity_isDivergenceFree
    [FiniteDimensional ℝ E] (u : VelocityField E) :
    IsDivergenceFree (spinVelocity u) := by
  simpa [spinVelocity] using
    (vorticity_isDivergenceFree (E := E) u)

/-- Exact skew polarization of a velocity field. -/
def IsSpinPolarized (u : VelocityField E) : Prop :=
  ContinuousLinearMap.adjoint u = -u

/-- Exact self-adjoint polarization of a velocity field. -/
def IsStrainPolarized (u : VelocityField E) : Prop :=
  ContinuousLinearMap.adjoint u = u

/-- A spin-polarized velocity is unchanged by vorticity extraction. -/
theorem spinVelocity_eq_self_of_spinPolarized
    {u : VelocityField E} (h : IsSpinPolarized u) :
    spinVelocity u = u := by
  simpa [spinVelocity, IsSpinPolarized] using
    (vorticity_eq_self_of_skew (E := E) (u := u) h)

/-- A strain-polarized velocity has no spin channel. -/
theorem spinVelocity_eq_zero_of_strainPolarized
    {u : VelocityField E} (h : IsStrainPolarized u) :
    spinVelocity u = 0 := by
  simpa [spinVelocity, IsStrainPolarized] using
    (vorticity_eq_zero_of_self_adjoint (E := E) (u := u) h)

/-- The linearized spin-closure residual of a spin-polarized velocity vanishes. -/
theorem spinClosureResidual_eq_zero_of_spinPolarized
    {u : VelocityField E} (h : IsSpinPolarized u) :
    vorticityClosureResidual u = 0 := by
  exact vorticityClosureResidual_eq_zero_of_skew (E := E) h

/-- The two-sheet frame has a skew spin sheet. -/
theorem twoSheetSpinFrame_spin_is_skew
    (u : VelocityField E) :
    ContinuousLinearMap.adjoint (twoSheetSpinFrame u).spin =
      -(twoSheetSpinFrame u).spin := by
  simpa [twoSheetSpinFrame, spinVelocity] using
    (adjoint_vorticity_eq_neg (E := E) u)

/-- The two-sheet frame has a self-adjoint strain sheet. -/
theorem twoSheetSpinFrame_strain_is_self_adjoint
    (u : VelocityField E) :
    ContinuousLinearMap.adjoint (twoSheetSpinFrame u).strain =
      (twoSheetSpinFrame u).strain := by
  simpa [twoSheetSpinFrame, strainVelocity] using
    (adjoint_strainRate_eq_self (E := E) u)

end InfoGeometry.Canonical.QuantumSpinNavierStokes
