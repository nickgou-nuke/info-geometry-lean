import InfoGeometry.Canonical.BerryRotorBridge
import InfoGeometry.Canonical.HestenesRealStructures
import InfoGeometry.Canonical.RealStokesGaussHomology
import InfoGeometry.Meta.Architecture

/-!
# InfoGeometry.Canonical.RealRotorGaussHestenesBridge

Real Hestenes/Krein replacement for scalar-complex phase language.

This module records the theorem-safe owner lane:

* the role commonly denoted by scalar `i` is carried by a real rotor/phase axis;
* generalized integral readout is real Stokes/Gauss incidence pairing;
* complex contour/residue language is only an optional representation shadow.

No complex analytic theorem is asserted here.
-/

noncomputable section

namespace InfoGeometry.Canonical.RealRotorGaussHestenesBridge

open InfoGeometry.Canonical.RealIncidenceHomology
open InfoGeometry.Canonical.RealIncidenceChains

/--
Real replacement for the scalar imaginary unit.

`J` is a real operator/bivector/phase axis with `J² = -1`. In Hestenes/Krein
language this is the geometric phase axis, not scalar complex analysis.
-/
@[rep_depth krein]
structure RealRotorPhaseAxis
    (Op : Type*) [Ring Op] where
  J : Op
  J_sq : J * J = -1

namespace RealRotorPhaseAxis

variable {Op : Type*} [Ring Op]

/-- Readback: the real phase axis squares to `-1`. -/
@[rep_depth krein]
theorem square_eq_neg_one (R : RealRotorPhaseAxis Op) :
    R.J * R.J = -1 :=
  R.J_sq

end RealRotorPhaseAxis

/--
Abstract real rotor phase calculus.

The exponential/rotor map is supplied as real geometric data. This avoids
building phase transport from scalar-complex exponentials.
-/
@[rep_depth operator]
structure RealRotorCalculus
    (Biv Rotor : Type*)
    [AddCommGroup Biv] [Module ℝ Biv]
    [LieRing Biv] [LieAlgebra ℝ Biv]
    [Group Rotor] [BerryRotorBridge.BivectorPhaseAlgebra Biv Rotor] where
  rotorOfBivector : Biv → Rotor
  rotor_law : rotorOfBivector =
    BerryRotorBridge.BivectorPhaseAlgebra.expBiv
  phaseLineReadout : Biv → Prop
  phaseLineReadout_iff :
    ∀ X, phaseLineReadout X ↔
      BerryRotorBridge.BivectorPhaseAlgebra.phaseLine (Biv := Biv) (Rotor := Rotor) X

namespace RealRotorCalculus

variable
  {Biv Rotor : Type*}
  [AddCommGroup Biv] [Module ℝ Biv]
  [LieRing Biv] [LieAlgebra ℝ Biv]
  [Group Rotor] [BerryRotorBridge.BivectorPhaseAlgebra Biv Rotor]

/-- Rotor readout is definitionally the supplied real bivector exponential. -/
@[rep_depth operator]
theorem rotorOfBivector_eq_exp (R : RealRotorCalculus Biv Rotor) :
    R.rotorOfBivector = BerryRotorBridge.BivectorPhaseAlgebra.expBiv :=
  R.rotor_law

/-- Phase-line membership is the real bivector line, not a complex scalar line. -/
@[rep_depth operator]
theorem phaseLineReadout_iff_phaseLine
    (R : RealRotorCalculus Biv Rotor) (X : Biv) :
    R.phaseLineReadout X ↔
      BerryRotorBridge.BivectorPhaseAlgebra.phaseLine (Biv := Biv) (Rotor := Rotor) X :=
  R.phaseLineReadout_iff X

end RealRotorCalculus

/--
Real generalized-integral readout.

`boundaryReadout` and `bulkReadout` are arbitrary real readouts, connected by an
explicit Gauss/Stokes witness. This is the correct socket for generalized
integrals, avoiding contour-residue assumptions.
-/
@[rep_depth transport]
structure RealGaussStokesReadout
    (Chain Boundary : Type*) where
  boundaryOf : Chain → Boundary
  boundaryReadout : Boundary → ℝ
  bulkReadout : Chain → ℝ
  gaussStokes_law : ∀ c, boundaryReadout (boundaryOf c) = bulkReadout c

namespace RealGaussStokesReadout

variable {Chain Boundary : Type*}

/-- Re-export the supplied real Gauss/Stokes law. -/
@[rep_depth transport]
theorem boundary_eq_bulk
    (G : RealGaussStokesReadout Chain Boundary) (c : Chain) :
    G.boundaryReadout (G.boundaryOf c) = G.bulkReadout c :=
  G.gaussStokes_law c

end RealGaussStokesReadout

/--
Repo-owned finite incidence Stokes/Gauss readback:
`<∂₁ c, φ>₀ = <c, δ⁰φ>₁` over the real numbers.
-/
@[rep_depth transport]
theorem incidence_real_stokes_gauss
    {A : DAG.TripleSystem}
    [DecidableEq A.Obj]
    (c : RealIncidenceChains.Incidence.OneChains A)
    (φ : RealIncidenceHomology.Incidence.ZeroCochain A) :
    RealStokesGaussHomology.Incidence.pairZero
        (A := A)
        (RealIncidenceChains.Incidence.boundaryOne A c)
        φ
      =
    RealStokesGaussHomology.Incidence.pairOne
        (A := A)
        c
        (RealIncidenceHomology.Incidence.zeroCoboundary φ) := by
  exact RealStokesGaussHomology.Incidence.pairing_boundaryOne_eq_pairing_zeroCoboundary
    (A := A) c φ

/--
Guardrail packet: scalar-complex language is not the owner lane.

The real owner lane is Hestenes/Krein rotor phase plus real Gauss/Stokes
readout. Complex notation may be used later only as a calibrated shadow.
-/
@[rep_depth operator]
structure RealGeometryReplacesComplexAnalysisGuard where
  scalar_i_replaced_by_real_rotor : Prop
  contour_residue_replaced_by_real_gauss_stokes : Prop
  complex_analysis_is_optional_shadow : Prop
  scalar_i_replaced_by_real_rotor_witness :
    scalar_i_replaced_by_real_rotor
  contour_residue_replaced_by_real_gauss_stokes_witness :
    contour_residue_replaced_by_real_gauss_stokes
  complex_analysis_is_optional_shadow_witness :
    complex_analysis_is_optional_shadow

namespace RealGeometryReplacesComplexAnalysisGuard

/-- Real rotor phase is the owner replacement for scalar `i`. -/
@[rep_depth operator]
theorem scalar_i_replaced
    (G : RealGeometryReplacesComplexAnalysisGuard) :
    G.scalar_i_replaced_by_real_rotor :=
  G.scalar_i_replaced_by_real_rotor_witness

/-- Real Gauss/Stokes is the owner replacement for contour-residue language. -/
@[rep_depth operator]
theorem contour_residue_replaced
    (G : RealGeometryReplacesComplexAnalysisGuard) :
    G.contour_residue_replaced_by_real_gauss_stokes :=
  G.contour_residue_replaced_by_real_gauss_stokes_witness

/-- Complex analysis remains only a calibrated optional shadow. -/
@[rep_depth operator]
theorem complex_shadow_optional
    (G : RealGeometryReplacesComplexAnalysisGuard) :
    G.complex_analysis_is_optional_shadow :=
  G.complex_analysis_is_optional_shadow_witness

end RealGeometryReplacesComplexAnalysisGuard

/--
Full real rotor/Gauss/Hestenes bridge packet.

This is a canonical socket for reformulating phase/integral statements in real
geometric algebra language before any optional complex representation is chosen.
-/
@[rep_depth operator]
structure RealRotorGaussHestenesBridge
    (Op Chain Boundary : Type*) [Ring Op] where
  phaseAxis : RealRotorPhaseAxis Op
  gaussStokes : RealGaussStokesReadout Chain Boundary
  guard : RealGeometryReplacesComplexAnalysisGuard
  hestenesKreinReadout : Op → ℝ
  rotorReadout : Op → Op
  rotorReadout_preserves_real_lane : Prop
  rotorReadout_preserves_real_lane_witness :
    rotorReadout_preserves_real_lane

namespace RealRotorGaussHestenesBridge

variable {Op Chain Boundary : Type*} [Ring Op]

/-- The Hestenes phase axis replaces scalar `i` by a real square-minus-one axis. -/
@[rep_depth krein]
theorem phaseAxis_sq
    (B : RealRotorGaussHestenesBridge Op Chain Boundary) :
    B.phaseAxis.J * B.phaseAxis.J = -1 :=
  B.phaseAxis.J_sq

/-- The bridge readout uses real Gauss/Stokes. -/
@[rep_depth transport]
theorem gaussStokes_law
    (B : RealRotorGaussHestenesBridge Op Chain Boundary) (c : Chain) :
    B.gaussStokes.boundaryReadout (B.gaussStokes.boundaryOf c)
      = B.gaussStokes.bulkReadout c :=
  B.gaussStokes.gaussStokes_law c

/-- Complex analysis is only an optional representation shadow for this bridge. -/
@[rep_depth operator]
theorem complex_shadow_optional
    (B : RealRotorGaussHestenesBridge Op Chain Boundary) :
    B.guard.complex_analysis_is_optional_shadow :=
  B.guard.complex_analysis_is_optional_shadow_witness

/-- Rotor readout stays in the declared real lane. -/
@[rep_depth operator]
theorem rotorReadout_preserves_real_lane_holds
    (B : RealRotorGaussHestenesBridge Op Chain Boundary) :
    B.rotorReadout_preserves_real_lane :=
  B.rotorReadout_preserves_real_lane_witness

end RealRotorGaussHestenesBridge

end InfoGeometry.Canonical.RealRotorGaussHestenesBridge
