/-
InfoGeometry/Optics/FiniteJonesKasparovBoundary.lean

Finite optical Kasparov boundary readouts.

This file deploys the finite Jones/Stinespring/Bregman branch against the
smallest Kasparov-style defect surface.

For the constructive phase-free diagonal Jones channel,

  R = diag(cos theta_s, cos theta_p),

the visible block is self-adjoint, so the optical Stinespring defect

  I - R^H R

is the algebraic involutive defect

  1 - R^2.

The module proves this equality and then reads it three ways:

  optics:       visible defect
  environment: hidden gain
  heat:         Frobenius-Bregman heat
-/

import Mathlib.Tactic
import InfoGeometry.Geometry.ConstructiveKasparov
import InfoGeometry.Optics.FiniteJonesBregman
import InfoGeometry.Optics.FiniteJonesStinespringConstructive

noncomputable section

namespace InfoGeometry.Optics.FiniteJonesKasparovBoundary

open InfoGeometry.Geometry.ConstructiveKasparov
open InfoGeometry.Optics.FiniteJonesModel
open InfoGeometry.Optics.FiniteJonesBregman
open InfoGeometry.Optics.FiniteJonesStinespringConstructive

/-! ## 1. Phase-free diagonal optical defect as `1 - R²` -/

/--
For the phase-free diagonal constructive channel, the visible Jones block is
self-adjoint.
-/
theorem visibleBlock_conjTranspose_eq_self
    (D : ConstructiveJonesStinespring) :
    Matrix.conjTranspose D.R = D.R := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ConstructiveJonesStinespring.R, visibleBlock, diagJones, Matrix.conjTranspose,
      ← Complex.cos_conj]

/--
Finite optical Kasparov defect for the constructive diagonal Jones channel:

`P = 1 - R²`.
-/
def kasparovDefect
    (D : ConstructiveJonesStinespring) : JonesMat :=
  1 - D.R * D.R

/--
The finite optical Kasparov defect is definitionally `1 - R²`.
-/
theorem kasparovDefect_eq_one_sub_square
    (D : ConstructiveJonesStinespring) :
    kasparovDefect D = 1 - D.R * D.R :=
  rfl

/--
For phase-free diagonal channels, the Stinespring optical defect `I - RᴴR`
is the Kasparov-style defect `1 - R²`.
-/
theorem visibleDefect_eq_kasparovDefect
  (D : ConstructiveJonesStinespring) :
    D.visibleDefect = kasparovDefect D := by
  unfold ConstructiveJonesStinespring.visibleDefect
  unfold InfoGeometry.Optics.FiniteJonesStinespring.opticalDefect
  unfold kasparovDefect
  have hstar : star D.R = D.R := by
    exact visibleBlock_conjTranspose_eq_self D
  rw [hstar]

/--
The finite optical Kasparov defect equals hidden environment gain.
-/
theorem kasparovDefect_eq_environmentGain
    (D : ConstructiveJonesStinespring) :
    kasparovDefect D = D.environmentGain := by
  rw [← visibleDefect_eq_kasparovDefect D]
  exact D.visibleDefect_eq_environmentGain

/--
The finite Stinespring heat is the Frobenius-Bregman readout of the Kasparov
defect.
-/
theorem finiteHeat_eq_kasparovDefectBregman
    (D : ConstructiveJonesStinespring) :
    finiteStinespringHeat D.toStinespringIsometry =
      frobeniusBregman (kasparovDefect D) 0 := by
  dsimp [finiteStinespringHeat]
  rw [← visibleDefect_eq_kasparovDefect D]
  rfl

/--
The finite Stinespring heat is also the hidden-environment Bregman readout.
-/
theorem finiteHeat_eq_environmentGainBregman
    (D : ConstructiveJonesStinespring) :
    finiteStinespringHeat D.toStinespringIsometry =
      frobeniusBregman D.environmentGain 0 := by
  rw [finiteHeat_eq_kasparovDefectBregman D]
  rw [kasparovDefect_eq_environmentGain D]

/-! ## 2. Finite projected-kernel index readout -/

/--
Two Jones channels as finite modes.
-/
inductive JonesMode where
  | s
  | p
deriving DecidableEq, Repr

/--
The optical kernel projection readout used by the finite Kasparov bridge.

This remains a finite readout function: it maps a defect matrix to the list of
projected defect modes selected by the model.
-/
def FiniteOpticalKernelReadout :=
  (JonesMat → List JonesMode) × (JonesMode → KernelGrade)

namespace FiniteOpticalKernelReadout

variable (K : FiniteOpticalKernelReadout)

/-- Read a defect matrix as a finite list of projected modes. -/
abbrev modesOfDefect : JonesMat → List JonesMode := K.1

/-- Grade of each projected optical mode. -/
abbrev grade : JonesMode → KernelGrade := K.2

/-- Construct a finite optical kernel readout from its two maps. -/
def mk (modesOfDefect : JonesMat → List JonesMode)
    (grade : JonesMode → KernelGrade) : FiniteOpticalKernelReadout :=
  (modesOfDefect, grade)

/--
The constructive Kasparov datum associated to a finite optical kernel readout.
-/
def toConstructiveKasparovDatum :
    ConstructiveKasparovDatum
      ConstructiveJonesStinespring JonesMat JonesMat JonesMode where
  F := fun D => D.R
  defectToKernelProjection := id
  kernelBasisOfProjection := K.modesOfDefect
  grade := K.grade

/--
The projected kernel basis is the finite readout of the optical Kasparov defect.
-/
theorem kernelBasis_eq_modesOf_kasparovDefect
    (D : ConstructiveJonesStinespring) :
    K.toConstructiveKasparovDatum.kernelBasis D =
      K.modesOfDefect (kasparovDefect D) :=
  rfl

/--
The finite optical index is the finite graded index of the projected defect
modes.
-/
def index
    (D : ConstructiveJonesStinespring) : ℤ :=
  K.toConstructiveKasparovDatum.index D

/--
If the projected optical defect modes are empty, the finite optical index is
zero.
-/
theorem index_eq_zero_of_no_projected_modes
    {D : ConstructiveJonesStinespring}
    (hD : K.modesOfDefect (kasparovDefect D) = []) :
    K.index D = 0 := by
  dsimp [index]
  apply K.toConstructiveKasparovDatum.index_eq_zero_of_projected_kernel_empty
  exact hD

/--
A nonzero finite optical index produces an explicit projected optical mode.
-/
theorem exists_projected_mode_of_index_ne_zero
    {D : ConstructiveJonesStinespring}
    (hD : K.index D ≠ 0) :
    ∃ m : JonesMode, m ∈ K.modesOfDefect (kasparovDefect D) := by
  have h :=
    K.toConstructiveKasparovDatum.exists_projected_kernel_mode_of_index_ne_zero
      (x := D)
      (by simpa [index] using hD)
  simpa [kernelBasis_eq_modesOf_kasparovDefect] using h

end FiniteOpticalKernelReadout

end InfoGeometry.Optics.FiniteJonesKasparovBoundary
