import InfoGeometry.Topology.V4RootSystem
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.WallpaperKleinBottlePresentation
import InfoGeometry.Topology.WallpaperToWeylBridge
import InfoGeometry.Categorical.ModularDoubledRealHopfTransport

/-!
# Varlamov V₄ / trifactor / Klein-glide bridge

This module links three already finite sockets:

* the Varlamov-style `A₁ × A₁` Klein-four sign-root table;
* the tripotent/trifactor spectrum `{-1,0,+1}`;
* the pointwise `pg` wallpaper relation `G T_y G⁻¹ = T_y⁻¹`.

The bridge is deliberately small.  It proves only finite cycle/readout identities
and imports the exact pointwise glide relation.  It does **not** classify real
Clifford algebras, prove a `Cl(1,1)` representation equivalence, construct a
Klein-bottle quotient manifold, or assert a physical triality theorem.
-/

noncomputable section

namespace InfoGeometry.Topology.VarlamovV4TrifactorKleinBridge

open InfoGeometry.Topology.V4RootSystem
open InfoGeometry.Topology.Wallpaper
open InfoGeometry.Topology.WallpaperKleinBottlePresentation
open InfoGeometry.Topology.WallpaperToWeylBridge
open InfoGeometry.CondensedMatter.NonOrientableWeylSemimetal
open InfoGeometryCore

/-- Interpret the three tripotent branches as the three non-identity `V₄` labels. -/
def sectorLabel : TripotentState → NontrivialV4
  | TripotentState.neg => NontrivialV4.x
  | TripotentState.zero => NontrivialV4.y
  | TripotentState.pos => NontrivialV4.xy

/-- The induced `V₄` element attached to a tripotent branch. -/
def sectorV4 (s : TripotentState) : V4Group :=
  NontrivialV4.toV4 (sectorLabel s)

/-- The tripotent branch cycle and the non-identity `V₄` cycle are aligned. -/
theorem sectorLabel_trialityCycle (s : TripotentState) :
    sectorLabel (TripotentState.trialityCycle s) =
      NontrivialV4.trialityCycle (sectorLabel s) := by
  cases s <;> rfl

/-- Cycling a tripotent branch three times returns the same attached `V₄` element. -/
theorem sectorV4_trialityCube (s : TripotentState) :
    sectorV4 (TripotentState.trialityCycle
      (TripotentState.trialityCycle (TripotentState.trialityCycle s))) = sectorV4 s := by
  cases s <;> rfl

/-- Every tripotent branch maps to a non-identity `V₄` reflection label. -/
theorem sectorV4_ne_identity (s : TripotentState) : sectorV4 s ≠ V4Group.I := by
  cases s <;> decide

/-- Each tripotent-labelled `V₄` element is an involution. -/
theorem sectorV4_involution (s : TripotentState) :
    sectorV4 s * sectorV4 s = V4Group.I := by
  cases s <;> rfl

/-- A finite witness bundling the tripotent/V₄ cycle with a `pg` Klein relation. -/
abbrev VarlamovTrifactorKleinWitness : Type :=
  Σ' _klein : KleinBottlePresentationWitness,
    (∀ s : TripotentState,
      sectorV4 (TripotentState.trialityCycle
        (TripotentState.trialityCycle (TripotentState.trialityCycle s))) = sectorV4 s) ∧
      (∀ s : TripotentState, sectorV4 s * sectorV4 s = V4Group.I) ∧
        (∀ s : TripotentState, sectorV4 s ≠ V4Group.I)

namespace VarlamovTrifactorKleinWitness

abbrev klein (W : VarlamovTrifactorKleinWitness) : KleinBottlePresentationWitness :=
  W.1

abbrev sector_cycle_cube (W : VarlamovTrifactorKleinWitness) :
    ∀ s : TripotentState,
      sectorV4 (TripotentState.trialityCycle
        (TripotentState.trialityCycle (TripotentState.trialityCycle s))) = sectorV4 s :=
  W.2.1

abbrev sector_involution (W : VarlamovTrifactorKleinWitness) :
    ∀ s : TripotentState, sectorV4 s * sectorV4 s = V4Group.I :=
  W.2.2.1

abbrev sector_nonidentity (W : VarlamovTrifactorKleinWitness) :
    ∀ s : TripotentState, sectorV4 s ≠ V4Group.I :=
  W.2.2.2

end VarlamovTrifactorKleinWitness

/-- Read back the finite Klein-bottle presentation relation from any bridge witness. -/
theorem witness_klein_relation (W : VarlamovTrifactorKleinWitness) (p : Lattice2D) :
    W.klein.glide (W.klein.yTranslation (W.klein.glide.symm p)) =
      W.klein.yTranslation.symm p :=
  W.klein.glide_conjugates_yTranslation_to_inverse p

end InfoGeometry.Topology.VarlamovV4TrifactorKleinBridge

end noncomputable section
