import InfoGeometry.Topology.V4RootSystem
import InfoGeometry.Topology.WallpaperKleinBottlePresentation

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
structure VarlamovTrifactorKleinWitness where
  klein : KleinBottlePresentationWitness
  sector_cycle_cube : ∀ s : TripotentState,
    sectorV4 (TripotentState.trialityCycle
      (TripotentState.trialityCycle (TripotentState.trialityCycle s))) = sectorV4 s
  sector_involution : ∀ s : TripotentState, sectorV4 s * sectorV4 s = V4Group.I
  sector_nonidentity : ∀ s : TripotentState, sectorV4 s ≠ V4Group.I

/-- The concrete wallpaper `pg` action together with the finite Varlamov/trifactor data. -/
def concreteVarlamovTrifactorKleinWitness : VarlamovTrifactorKleinWitness where
  klein := WallpaperGroupPG.kleinBottlePresentation concretePG
  sector_cycle_cube := sectorV4_trialityCube
  sector_involution := sectorV4_involution
  sector_nonidentity := sectorV4_ne_identity

/-- Read back the finite Klein-bottle presentation relation from any bridge witness. -/
theorem witness_klein_relation (W : VarlamovTrifactorKleinWitness) (p : Lattice2D) :
    W.klein.glide (W.klein.yTranslation (W.klein.glide.symm p)) =
      W.klein.yTranslation.symm p :=
  W.klein.glide_conjugates_yTranslation_to_inverse p

/-- Concrete bridge packet: V₄/trifactor cycling plus the `pg` glide relation. -/
theorem concrete_varlamov_trifactor_klein_packet (p : Lattice2D) :
    (∀ s : TripotentState,
      sectorV4 (TripotentState.trialityCycle
        (TripotentState.trialityCycle (TripotentState.trialityCycle s))) = sectorV4 s) ∧
    (∀ s : TripotentState, sectorV4 s * sectorV4 s = V4Group.I) ∧
    (∀ s : TripotentState, sectorV4 s ≠ V4Group.I) ∧
    concreteVarlamovTrifactorKleinWitness.klein.glide
        (concreteVarlamovTrifactorKleinWitness.klein.yTranslation
          (concreteVarlamovTrifactorKleinWitness.klein.glide.symm p)) =
      concreteVarlamovTrifactorKleinWitness.klein.yTranslation.symm p := by
  exact ⟨sectorV4_trialityCube, sectorV4_involution, sectorV4_ne_identity,
    witness_klein_relation concreteVarlamovTrifactorKleinWitness p⟩

end InfoGeometry.Topology.VarlamovV4TrifactorKleinBridge

end noncomputable section
