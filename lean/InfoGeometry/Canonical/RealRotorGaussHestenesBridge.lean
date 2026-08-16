import InfoGeometry.Canonical.BerryRotorBridge
import InfoGeometry.Canonical.HestenesRealStructures
import InfoGeometry.Canonical.RealStokesGaussHomology
import InfoGeometry.Meta.Architecture

/-!
# Real rotor and incidence Gauss/Stokes readouts

This owner contains two independent, theorem-backed finite interfaces:

* a real phase axis whose square is `-1` and whose rotor map is tied to the
  existing bivector-phase owner;
* the concrete finite incidence pairing theorem supplied by
  `RealStokesGaussHomology`.

It deliberately does not claim a replacement theorem for complex analysis,
contour residues, or analytic continuation.
-/

noncomputable section

namespace InfoGeometry.Canonical.RealRotorGaussHestenesBridge

open InfoGeometry.Canonical.RealIncidenceHomology
open InfoGeometry.Canonical.RealIncidenceChains

/-! ## Real phase-axis data -/

/-/-- A real operator carrying the phase-axis relation `J² = -1`. -/
@[rep_depth krein]
structure RealRotorPhaseAxis (Op : Type*) [Ring Op] where
  J : Op
  J_sq : J * J = -1

namespace RealRotorPhaseAxis

variable {Op : Type*} [Ring Op]

/-/-- Read back the defining phase-axis relation. -/
@[rep_depth krein]
theorem square_eq_neg_one (R : RealRotorPhaseAxis Op) :
    R.J * R.J = -1 :=
  R.J_sq

end RealRotorPhaseAxis

/-/-- A real rotor calculus tied to the existing bivector exponential owner. -/
@[rep_depth operator]
structure RealRotorCalculus
    (Biv Rotor : Type*)
    [AddCommGroup Biv] [Module ℝ Biv]
    [LieRing Biv] [LieAlgebra ℝ Biv]
    [Group Rotor] [BerryRotorBridge.BivectorPhaseAlgebra Biv Rotor] where
  rotorOfBivector : Biv → Rotor
  rotor_eq_exp : rotorOfBivector =
    BerryRotorBridge.BivectorPhaseAlgebra.expBiv
  phaseLineReadout : Biv → Prop
  phaseLineReadout_iff :
    ∀ X, phaseLineReadout X ↔
      BerryRotorBridge.BivectorPhaseAlgebra.phaseLine
        (Biv := Biv) (Rotor := Rotor) X

namespace RealRotorCalculus

variable
  {Biv Rotor : Type*}
  [AddCommGroup Biv] [Module ℝ Biv]
  [LieRing Biv] [LieAlgebra ℝ Biv]
  [Group Rotor] [BerryRotorBridge.BivectorPhaseAlgebra Biv Rotor]

/-/-- The rotor map is the existing bivector exponential. -/
@[rep_depth operator]
theorem rotorOfBivector_eq_exp (R : RealRotorCalculus Biv Rotor) :
    R.rotorOfBivector = BerryRotorBridge.BivectorPhaseAlgebra.expBiv :=
  R.rotor_eq_exp

/-/-- The phase-line readout agrees with the existing phase-line predicate. -/
@[rep_depth operator]
theorem phaseLineReadout_iff_phaseLine
    (R : RealRotorCalculus Biv Rotor) (X : Biv) :
    R.phaseLineReadout X ↔
      BerryRotorBridge.BivectorPhaseAlgebra.phaseLine
        (Biv := Biv) (Rotor := Rotor) X :=
  R.phaseLineReadout_iff X

end RealRotorCalculus

/-! ## Generic and concrete Gauss/Stokes readouts -/

/-/-- A supplied real boundary/bulk readout law.

The actual finite incidence theorem below is independent of this generic
interface; this structure is retained only for callers that already have a
boundary operator and a scalar pairing. -/
@[rep_depth transport]
structure RealGaussStokesReadout (Chain Boundary : Type*) where
  boundaryOf : Chain → Boundary
  boundaryReadout : Boundary → ℝ
  bulkReadout : Chain → ℝ
  gaussStokes_law : ∀ c, boundaryReadout (boundaryOf c) = bulkReadout c

namespace RealGaussStokesReadout

variable {Chain Boundary : Type*}

/-/-- Read back the supplied boundary/bulk law. -/
@[rep_depth transport]
theorem boundary_eq_bulk
    (G : RealGaussStokesReadout Chain Boundary) (c : Chain) :
    G.boundaryReadout (G.boundaryOf c) = G.bulkReadout c :=
  G.gaussStokes_law c

end RealGaussStokesReadout

/-/-- Concrete finite incidence Stokes/Gauss pairing theorem:
`⟪∂₁ c, φ⟫₀ = ⟪c, δ⁰φ⟫₁`. -/
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

end InfoGeometry.Canonical.RealRotorGaussHestenesBridge
