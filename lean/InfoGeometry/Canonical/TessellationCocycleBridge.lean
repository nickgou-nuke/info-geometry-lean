import InfoGeometry.Algebraic.ExactPhaseCocycle
import InfoGeometry.Algebraic.CartanCocycle
import InfoGeometry.Tessellation.Incidence
import InfoGeometry.Tessellation.VolumeTransport
import InfoGeometry.Tessellation.WilsonLoop

/-!
# InfoGeometry.Canonical.TessellationCocycleBridge

Canonical bridge between the finite tessellation incidence/transport lane and
the explicit cocycle owners.

This file does not invent a new theorem. It packages the existing owners that
matter for the incidence/cocycle reading:

* supported lightray incidence is square-zero;
* unit conjugation preserves determinant and trace;
* Wilson-loop defect vanishes exactly for flat loops;
* exact phase and Cartan cocycle data remain explicit compatibility-based
  cocycle surfaces.

The bridge is intentionally conservative: cocycle compatibility hypotheses stay
visible rather than being collapsed into a stronger unconditional theorem.
-/

namespace InfoGeometry.Canonical.TessellationCocycleBridge

open InfoGeometry.Tessellation
open InfoGeometry.Algebraic
open InfoGeometry.Algebraic.Cartan

section Tessellation

variable {A : Type*} [Semiring A]

/-- Supported lightray incidence is square-zero. -/
theorem supported_lightray_square_zero
    {src tgt : Diamond A}
    (L : SupportedLightray A src tgt) :
    L.N * L.N = 0 :=
  InfoGeometry.Tessellation.supported_lightray_square_zero L

end Tessellation

section Transport

open scoped Matrix
open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {R : Type*} [CommRing R]

/-- Determinant rigidity under supported-incidence transport. -/
theorem det_supported_lightray_conj
    {P Q N : Matrix ι ι R}
    (hPQ : P * Q = 0) (hQN : Q * N = N) (hNP : N * P = N)
    (A : Matrix ι ι R) :
    Matrix.det (unitConj (supportedLightrayFlowUnit hPQ hQN hNP) A) =
      Matrix.det A :=
  InfoGeometry.Tessellation.det_supported_lightray_conj hPQ hQN hNP A

/-- Trace rigidity under supported-incidence transport. -/
theorem trace_supported_lightray_conj
    {P Q N : Matrix ι ι R}
    (hPQ : P * Q = 0) (hQN : Q * N = N) (hNP : N * P = N)
    (A : Matrix ι ι R) :
    Matrix.trace (unitConj (supportedLightrayFlowUnit hPQ hQN hNP) A) =
      Matrix.trace A :=
  InfoGeometry.Tessellation.trace_supported_lightray_conj hPQ hQN hNP A

/-- A Wilson loop is flat exactly when its defect vanishes. -/
theorem wilsonLoop_defect_eq_zero_iff_flat
    {B : Type*} [Ring B] {base : Diamond B}
    (L : WilsonLoop B base) :
    InfoGeometry.Tessellation.WilsonLoop.defect L = (0 : B) ↔
      InfoGeometry.Tessellation.WilsonLoop.Flat L :=
  by
    simp [InfoGeometry.Tessellation.WilsonLoop.defect,
      InfoGeometry.Tessellation.WilsonLoop.Flat, sub_eq_zero]

/-- Flat loops have zero defect. -/
theorem wilsonLoop_defect_eq_zero_of_flat
    {B : Type*} [Ring B] {base : Diamond B}
    {L : WilsonLoop B base}
    (hL : InfoGeometry.Tessellation.WilsonLoop.Flat L) :
    InfoGeometry.Tessellation.WilsonLoop.defect L = (0 : B) :=
  InfoGeometry.Tessellation.WilsonLoop.defect_eq_zero_of_flat hL

/-- Zero defect implies flatness. -/
theorem wilsonLoop_flat_of_defect_eq_zero
    {B : Type*} [Ring B] {base : Diamond B}
    {L : WilsonLoop B base}
    (hL : InfoGeometry.Tessellation.WilsonLoop.defect L = (0 : B)) :
    InfoGeometry.Tessellation.WilsonLoop.Flat L :=
  InfoGeometry.Tessellation.WilsonLoop.flat_of_defect_eq_zero hL

end Transport

section Cocycles

/-- The exact Berry phase normalizes at the identity. -/
theorem exactBerryPhase_one
    {R : Type*} [PhaseRotorGroup R]
    (k : ℤ) (τ : UpperHalfPlane) :
    exactBerryPhase (R := R) k 1 τ = 1 :=
  InfoGeometry.Algebraic.exactBerryPhase_one (R := R) k τ

/-- Exact phase cocycles stay explicit under the compatibility property. -/
noncomputable abbrev exactModularBerryCocycle
    {R : Type*} [PhaseRotorGroup R] {k : ℤ}
    (h : ExactPhaseCompatibility (R := R) k) :
    InfoGeometry.Canonical.Algebraic.MulActionCocycle
      ModularGroup UpperHalfPlane R :=
  InfoGeometry.Algebraic.exactModularBerryCocycle (R := R) (k := k) h

end Cocycles

end InfoGeometry.Canonical.TessellationCocycleBridge
