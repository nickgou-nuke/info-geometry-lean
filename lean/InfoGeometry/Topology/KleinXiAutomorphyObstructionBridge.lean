import InfoGeometry.Topology.ZetaCenteredCoordinateBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Affine Klein deck action and the scalar-descent obstruction

This owner puts the centered zeta coordinates on the affine universal cover.
It records the translation/glide relations and the exact consequence of
scalar descent under the glide: vertical periodicity by twice the glide
parameter.  It does not assert that the actual completed zeta function has
this periodicity, nor that it descends as a scalar function to a Klein
quotient.
-/

noncomputable section

namespace InfoGeometry.Topology.KleinXiAutomorphyObstructionBridge

open InfoGeometry.Topology.ZetaCenteredCoordinate
open InfoGeometry.Topology.ZetaCenteredCoordinate.ZetaFlowPoint

def affineTranslation (L : ℝ) (p : ZetaFlowPoint) : ZetaFlowPoint :=
  ⟨p.u + L, p.tau⟩

def affineGlide (T : ℝ) (p : ZetaFlowPoint) : ZetaFlowPoint :=
  ⟨-p.u, p.tau + T⟩

def affineGlideInv (T : ℝ) (p : ZetaFlowPoint) : ZetaFlowPoint :=
  ⟨-p.u, p.tau - T⟩

def affineVerticalTranslation (T : ℝ) (p : ZetaFlowPoint) : ZetaFlowPoint :=
  ⟨p.u, p.tau + T⟩

def criticalCore (tau : ℝ) : ZetaFlowPoint :=
  ⟨0, tau⟩

@[simp] theorem affineTranslation_apply_u (L : ℝ) (p : ZetaFlowPoint) :
    (affineTranslation L p).u = p.u + L := rfl

@[simp] theorem affineTranslation_apply_tau (L : ℝ) (p : ZetaFlowPoint) :
    (affineTranslation L p).tau = p.tau := rfl

@[simp] theorem affineGlide_apply_u (T : ℝ) (p : ZetaFlowPoint) :
    (affineGlide T p).u = -p.u := rfl

@[simp] theorem affineGlide_apply_tau (T : ℝ) (p : ZetaFlowPoint) :
    (affineGlide T p).tau = p.tau + T := rfl

@[simp] theorem affineGlideInv_apply_u (T : ℝ) (p : ZetaFlowPoint) :
    (affineGlideInv T p).u = -p.u := rfl

@[simp] theorem affineGlideInv_apply_tau (T : ℝ) (p : ZetaFlowPoint) :
    (affineGlideInv T p).tau = p.tau - T := rfl

theorem affineGlide_inv_left (T : ℝ) (p : ZetaFlowPoint) :
    affineGlide T (affineGlideInv T p) = p := by
  dsimp [affineGlide, affineGlideInv]
  ext <;> ring

theorem affineGlide_inv_right (T : ℝ) (p : ZetaFlowPoint) :
    affineGlideInv T (affineGlide T p) = p := by
  dsimp [affineGlide, affineGlideInv]
  ext <;> ring

theorem affineGlide_conjugates_translation (L T : ℝ) (p : ZetaFlowPoint) :
    affineGlide T (affineTranslation L (affineGlideInv T p)) =
      affineTranslation (-L) p := by
  dsimp [affineGlide, affineTranslation, affineGlideInv]
  ext <;> ring

theorem affineGlide_square (T : ℝ) (p : ZetaFlowPoint) :
    affineGlide T (affineGlide T p) =
      affineVerticalTranslation (2 * T) p := by
  dsimp [affineGlide, affineVerticalTranslation]
  ext <;> ring

theorem affineGlide_preserves_criticalCore (T tau : ℝ) :
    affineGlide T (criticalCore tau) = criticalCore (tau + T) := by
  dsimp [affineGlide, criticalCore]
  ext <;> ring

theorem affineGlide_reverses_transverse_coordinate
    (T : ℝ) (p : ZetaFlowPoint) :
    (affineGlide T p).u = -p.u := rfl

def ScalarGlideInvariant (T : ℝ) (F : ZetaFlowPoint → α) : Prop :=
  ∀ p, F (affineGlide T p) = F p

theorem scalarGlideInvariant_implies_vertical_periodicity
    {α : Type*} (T : ℝ) (F : ZetaFlowPoint → α)
    (hF : ScalarGlideInvariant T F) (p : ZetaFlowPoint) :
    F (affineVerticalTranslation (2 * T) p) = F p := by
  rw [← affineGlide_square T p]
  exact (hF (affineGlide T p)).trans (hF p)

theorem scalarGlideInvariant_implies_vertical_periodicity_on_core
    {α : Type*} (T : ℝ) (F : ZetaFlowPoint → α) (τ : ℝ)
    (hF : ScalarGlideInvariant T F) :
    F (criticalCore (τ + 2 * T)) = F (criticalCore τ) := by
  have h := scalarGlideInvariant_implies_vertical_periodicity
    T F hF (criticalCore τ)
  simpa [affineVerticalTranslation, criticalCore, add_assoc,
    add_left_comm, add_comm] using h

end InfoGeometry.Topology.KleinXiAutomorphyObstructionBridge
