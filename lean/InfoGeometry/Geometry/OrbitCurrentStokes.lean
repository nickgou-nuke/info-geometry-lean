/-
InfoGeometry/Geometry/OrbitCurrentStokes.lean

Orbit-current Stokes dictionary.

This file does not prove analytic contour integration or a residue theorem.
It packages the invariant Stokes shape

  orbit boundary pairing = surface defect pairing

and gives a finite readback from `FiniteDefectStokesModel`.
-/

import InfoGeometry.Geometry.FiniteDefectStokesModel
import InfoGeometry.Geometry.VerifiedCauchyKernel
import InfoGeometry.Meta.Architecture

noncomputable section

namespace InfoGeometry.Geometry.OrbitCurrentStokes

/--
An orbit-current Stokes datum.

`orbitIntegral x ω` is the boundary/current pairing along the orbit of `x`.
`surfaceIntegral x η` is the filled-surface pairing.
`d` is the supplied differential/defect operator on forms.

The only law is Stokes on closed orbits.  This is a witness surface, not an
existence theorem for surfaces, currents, or analytic contours.
-/
@[rep_depth geometry]
structure OrbitCurrentStokesDatum
    (Time State Form Value : Type*) where
  flow : Time → State → State
  period : Time
  isClosedOrbit : State → Prop
  orbitIntegral : State → Form → Value
  surfaceIntegral : State → Form → Value
  d : Form → Form
  stokes_law :
    ∀ x ω,
      isClosedOrbit x →
        orbitIntegral x ω = surfaceIntegral x (d ω)

namespace OrbitCurrentStokesDatum

variable {Time State Form Value : Type*}
variable (S : OrbitCurrentStokesDatum Time State Form Value)

/-- Direct Stokes readback for a closed orbit. -/
theorem orbitIntegral_eq_surfaceIntegral_d
    {x : State}
    (hx : S.isClosedOrbit x)
    (ω : Form) :
    S.orbitIntegral x ω = S.surfaceIntegral x (S.d ω) :=
  S.stokes_law x ω hx

end OrbitCurrentStokesDatum

/--
Defect specialization of an orbit-current Stokes datum.

`primitiveForm` is a form whose differential is the supplied defect current.
The residue is deliberately just a model-supplied readout of the orbit pairing;
normalization by `2π`, phase axes, or winding numbers belongs to the backend.
-/
@[rep_depth geometry]
structure DefectOrbitCurrentDatum
    (Time State Form Value : Type*) extends
      OrbitCurrentStokesDatum Time State Form Value where
  defectCurrent : Form
  primitiveForm : Form
  defect_law : d primitiveForm = defectCurrent
  residue : State → Value
  residue_law :
    ∀ x,
      isClosedOrbit x →
        residue x = orbitIntegral x primitiveForm

namespace DefectOrbitCurrentDatum

variable {Time State Form Value : Type*}
variable (D : DefectOrbitCurrentDatum Time State Form Value)

/-- The residue is the orbit-current pairing of the primitive form. -/
theorem residue_eq_orbitIntegral
    {x : State}
    (hx : D.isClosedOrbit x) :
    D.residue x = D.orbitIntegral x D.primitiveForm :=
  D.residue_law x hx

/-- The primitive orbit-current pairing is the surface pairing of the defect. -/
theorem orbitIntegral_primitive_eq_surfaceIntegral_defect
    {x : State}
    (hx : D.isClosedOrbit x) :
    D.orbitIntegral x D.primitiveForm =
      D.surfaceIntegral x D.defectCurrent := by
  rw [D.toOrbitCurrentStokesDatum.orbitIntegral_eq_surfaceIntegral_d hx]
  rw [D.defect_law]

/-- The residue is the defect surface pairing on closed orbits. -/
theorem residue_eq_surfaceIntegral_defect
    {x : State}
    (hx : D.isClosedOrbit x) :
    D.residue x = D.surfaceIntegral x D.defectCurrent := by
  rw [D.residue_eq_orbitIntegral hx]
  exact D.orbitIntegral_primitive_eq_surfaceIntegral_defect hx

end DefectOrbitCurrentDatum

/--
Resolvent orbit-current socket.

This records that a verified Cauchy/resolvent kernel family supplies the form
being integrated around an orbit.  It does not assert a Riesz projection or
Drazin projector formula; those require separate spectral-contour hypotheses.
-/
@[rep_depth geometry]
structure ResolventOrbitCurrentDatum
    {Value : Type*} [NormedRing Value] [NormedAlgebra ℝ Value]
    (Time State Form : Type*)
    (K Z : Value) where
  stokes : OrbitCurrentStokesDatum Time State Form Value
  kernelFamily : VerifiedCauchyKernel.VerifiedKernelFamily K Z
  kernelForm : ℝ → Form
  kernelForm_law : Prop
  kernelForm_witness : kernelForm_law

namespace ResolventOrbitCurrentDatum

variable {Value : Type*} [NormedRing Value] [NormedAlgebra ℝ Value]
variable {Time State Form : Type*} {K Z : Value}
variable (R : ResolventOrbitCurrentDatum Time State Form K Z)

/-- The supplied kernel-form compatibility law. -/
theorem kernelForm_law_holds :
    R.kernelForm_law :=
  R.kernelForm_witness

end ResolventOrbitCurrentDatum

/-! ## Finite defect Stokes readback -/

open InfoGeometry.Geometry.FiniteDefectStokesModel

/--
The finite one-point defect model as an orbit-current Stokes datum.

The orbit and surface pairings are the already-owned finite Stokes pairings.
The `Form` parameter is `Unit`, because this readback exposes only the single
certified finite defect form.
-/
def finiteDefectOrbitCurrentStokesDatum :
    OrbitCurrentStokesDatum Unit Unit Unit Mat2 where
  flow := fun _ x => x
  period := ()
  isClosedOrbit := fun _ => True
  orbitIntegral := fun _ _ => defectBackend.boundaryIntegral () ccForm
  surfaceIntegral := fun _ _ => defectBackend.volumeIntegral () (fun _ => boundedDirac.P)
  d := fun _ => ()
  stokes_law := by
    intro x ω hx
    exact boundaryIntegral_eq_volumeIntegral_defect

/-- The finite defect Stokes readback has boundary pairing equal to the defect surface pairing. -/
theorem finiteDefect_orbitIntegral_eq_surfaceIntegral :
    finiteDefectOrbitCurrentStokesDatum.orbitIntegral () () =
      finiteDefectOrbitCurrentStokesDatum.surfaceIntegral () () :=
  finiteDefectOrbitCurrentStokesDatum.stokes_law () () True.intro

/--
The finite one-point defect model as a defect orbit-current datum.

The residue is the finite boundary integral, so the defect surface law is
exactly the existing finite defect Stokes theorem.
-/
def finiteDefectOrbitCurrentDatum :
    DefectOrbitCurrentDatum Unit Unit Unit Mat2 where
  toOrbitCurrentStokesDatum := finiteDefectOrbitCurrentStokesDatum
  defectCurrent := ()
  primitiveForm := ()
  defect_law := rfl
  residue := fun _ => defectBackend.boundaryIntegral () ccForm
  residue_law := by
    intro x hx
    rfl

/-- In the finite model, the orbit-current residue is the defect projector `P`. -/
theorem finiteDefect_residue_eq_P :
    finiteDefectOrbitCurrentDatum.residue () = P :=
  boundaryIntegral_ccForm

/-- In the finite model, the orbit-current residue equals the defect surface pairing. -/
theorem finiteDefect_residue_eq_surfaceIntegral_defect :
    finiteDefectOrbitCurrentDatum.residue () =
      finiteDefectOrbitCurrentDatum.surfaceIntegral () finiteDefectOrbitCurrentDatum.defectCurrent :=
  finiteDefectOrbitCurrentDatum.residue_eq_surfaceIntegral_defect True.intro

end InfoGeometry.Geometry.OrbitCurrentStokes

