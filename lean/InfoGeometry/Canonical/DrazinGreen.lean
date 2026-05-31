import InfoGeometry.Canonical.Drazin
import InfoGeometry.Meta.Architecture

/-!
# InfoGeometry.Canonical.DrazinGreen

Drazin inverse as an algebraic Green operator on the regular Drazin sector.

This module is a theorem-facing readback over `InfoGeometry.Canonical.Drazin`.
It does not assert global PDE/Fredholm solvability.  It proves the precise
algebraic obstruction statement for the canonical Drazin-Green representative:

`A * (D * f) = f` iff the Drazin residue `Q_D * f` vanishes.

Kernel/integral Green-function language is kept in a separate witness packet.
-/

noncomputable section

namespace InfoGeometry.Canonical.DrazinGreen

open InfoGeometry.Canonical.Drazin

section Ring

variable {R : Type*} [Ring R]

/-- Drazin regular projector `P_D = A * D`. -/
@[rep_depth operator]
def DrazinRegularProjector (A D : R) : R :=
  IsDrazinInverse.projection A D

/-- Drazin residue projector `Q_D = 1 - A * D`. -/
@[rep_depth operator]
def DrazinResidueProjector (A D : R) : R :=
  IsDrazinInverse.complementaryProjection A D

/-- The Drazin inverse read as the algebraic Green operator. -/
@[rep_depth operator]
def DrazinGreenOperator (_A D : R) : R :=
  D

/-- The Green reconstruction always returns the regular projection of the source. -/
@[rep_depth operator]
theorem drazinGreen_reconstructs_regular_part
    {A D : R} {k : ℕ}
    (_h : IsDrazinInverse A D k)
    (f : R) :
    A * (DrazinGreenOperator A D * f)
      = DrazinRegularProjector A D * f := by
  unfold DrazinGreenOperator DrazinRegularProjector
  simp [IsDrazinInverse.projection, mul_assoc]

/-- The Drazin residue is killed by the Drazin index power. -/
@[rep_depth operator]
theorem A_pow_mul_DrazinResidueProjector_eq_zero
    {A D : R} {k : ℕ}
    (h : IsDrazinInverse A D k) :
    A ^ k * DrazinResidueProjector A D = 0 := by
  simpa [DrazinResidueProjector] using
    IsDrazinInverse.power_mul_complementaryProjection_eq_zero h

/--
If the source has no Drazin residue, then the Drazin Green operator gives an
exact solution for the canonical representative `u_D = D * f`.
-/
@[rep_depth operator]
theorem drazinGreen_solves_of_residue_zero
    {A D : R} {k : ℕ}
    (h : IsDrazinInverse A D k)
    {f : R}
    (hf : DrazinResidueProjector A D * f = 0) :
    A * (DrazinGreenOperator A D * f) = f := by
  have hPQ :
      DrazinRegularProjector A D + DrazinResidueProjector A D = (1 : R) := by
    simpa [DrazinRegularProjector, DrazinResidueProjector] using
      (IsDrazinInverse.projection_add_complementaryProjection (a := A) (b := D))
  calc
    A * (DrazinGreenOperator A D * f)
        = DrazinRegularProjector A D * f := by
            exact drazinGreen_reconstructs_regular_part h f
    _ = (DrazinRegularProjector A D + DrazinResidueProjector A D) * f := by
            rw [add_mul, hf, add_zero]
    _ = (1 : R) * f := by
            rw [hPQ]
    _ = f := by
            simp

/--
If the Drazin Green representative solves exactly, then the source has no
Drazin residue.
-/
@[rep_depth operator]
theorem residue_zero_of_drazinGreen_solves
    {A D : R} {k : ℕ}
    (h : IsDrazinInverse A D k)
    {f : R}
    (hsol : A * (DrazinGreenOperator A D * f) = f) :
    DrazinResidueProjector A D * f = 0 := by
  have hrec :
      A * (DrazinGreenOperator A D * f)
        = DrazinRegularProjector A D * f :=
    drazinGreen_reconstructs_regular_part h f
  have hfP : f = DrazinRegularProjector A D * f :=
    hsol.symm.trans hrec
  have hQP :
      DrazinResidueProjector A D * DrazinRegularProjector A D = 0 := by
    simpa [DrazinRegularProjector, DrazinResidueProjector] using
      IsDrazinInverse.complementaryProjection_mul_projection h
  calc
    DrazinResidueProjector A D * f
        = DrazinResidueProjector A D * (DrazinRegularProjector A D * f) := by
            exact congrArg (fun y => DrazinResidueProjector A D * y) hfP
    _ = (DrazinResidueProjector A D * DrazinRegularProjector A D) * f := by
            rw [mul_assoc]
    _ = 0 := by
            rw [hQP]
            simp

/--
Exact solvability by the canonical Drazin Green representative is equivalent to
vanishing Drazin residue of the source.
-/
@[rep_depth operator]
theorem drazinGreen_solves_iff_residue_zero
    {A D : R} {k : ℕ}
    (h : IsDrazinInverse A D k)
    {f : R} :
    A * (DrazinGreenOperator A D * f) = f
      ↔ DrazinResidueProjector A D * f = 0 := by
  constructor
  · exact residue_zero_of_drazinGreen_solves h
  · exact drazinGreen_solves_of_residue_zero h

end Ring

/--
Analytic kernel packet for a Drazin Green operator.

This is extra structure: it says that the algebraic Drazin Green operator has a
kernel representation on a chosen space.  The ring theorem above does not supply
this analytic witness.
-/
@[rep_depth operator]
structure DrazinGreenKernelPacket
    (Space : Type*) (R : Type*) [Ring R] where
  A : R
  D : R
  index : ℕ
  hDrazin : IsDrazinInverse A D index
  GreenKernel : Space → Space → ℝ
  kernelRepresentsGreen : Prop
  kernelRepresentsGreen_sorry : kernelRepresentsGreen

namespace DrazinGreenKernelPacket

variable {Space : Type*} {R : Type*} [Ring R]
variable (K : DrazinGreenKernelPacket Space R)

/-- The packet's operator is a Drazin Green operator for its Drazin witness. -/
@[rep_depth operator]
def greenOperator : R :=
  DrazinGreenOperator K.A K.D

/-- The supplied kernel representation witness is available only at this layer. -/
@[rep_depth operator]
theorem kernel_represents_green :
    K.kernelRepresentsGreen :=
  K.kernelRepresentsGreen_sorry

end DrazinGreenKernelPacket

end InfoGeometry.Canonical.DrazinGreen
