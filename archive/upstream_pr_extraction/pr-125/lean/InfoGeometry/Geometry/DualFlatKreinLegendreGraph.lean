import InfoGeometry.Clifford.NeutralPhaseSpaceCore
import Mathlib.Tactic

/-!
# Dual-flat Legendre graphs in a neutral primal/dual carrier

The carrier is `V × V*`, not two geometric sheets.  The existing neutral
bilinear form is reused.  A symmetric linear duality map supplies the finite
Hessian/Legendre graph; its induced neutral metric is the symmetric duality
pairing and the canonical skew form vanishes on the graph.

Convexity and smooth Legendre theory are intentionally separate assumptions.
-/

namespace InfoGeometry.Geometry.DualFlatKreinLegendreGraph

open InfoGeometry.Clifford.NeutralPhaseSpaceCore

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

abbrev DualCarrier (V : Type*) [AddCommGroup V] [Module ℝ V] :=
  PhaseSpaceCarrier V
abbrev Covector (V : Type*) [AddCommGroup V] [Module ℝ V] :=
  Module.Dual ℝ V

/-- The canonical skew pairing on the primal/dual carrier. -/
def canonicalSymplectic (X Y : DualCarrier V) : ℝ :=
  Y.2 X.1 - X.2 Y.1

/-- The normalized neutral pairing used for the primal/dual graph metric. -/
noncomputable def normalizedNeutralPairing (X Y : DualCarrier V) : ℝ :=
  (1 / 2 : ℝ) * canonicalNeutralBilin X Y

/-- Primal/dual grading of the neutral carrier. -/
def primalDualGrading (X : DualCarrier V) : DualCarrier V :=
  (X.1, -X.2)

/-- A linear duality map is symmetric when it defines a Hessian pairing. -/
def IsSymmetricDuality (L : V →ₗ[ℝ] Covector V) : Prop :=
  ∀ u v, (L u) v = (L v) u

/-- Tangent lift of a primal vector to the graph of a duality map. -/
def graphLift (L : V →ₗ[ℝ] Covector V) (u : V) : DualCarrier V :=
  (u, L u)

theorem neutralPairing_symmetric (X Y : DualCarrier V) :
    normalizedNeutralPairing X Y = normalizedNeutralPairing Y X := by
  unfold normalizedNeutralPairing
  rw [canonicalNeutralBilin_apply, canonicalNeutralBilin_apply]
  ring

theorem canonicalSymplectic_skew (X Y : DualCarrier V) :
    canonicalSymplectic X Y = -canonicalSymplectic Y X := by
  unfold canonicalSymplectic
  ring

theorem primal_isotropic (u v : V) :
    normalizedNeutralPairing (u, 0) (v, 0) = 0 := by
  simp [normalizedNeutralPairing, canonicalNeutralBilin_apply]

theorem dual_isotropic (α β : Covector V) :
    normalizedNeutralPairing (0, α) (0, β) = 0 := by
  simp [normalizedNeutralPairing, canonicalNeutralBilin_apply]

theorem grading_squared (X : DualCarrier V) :
    primalDualGrading (primalDualGrading X) = X := by
  rcases X with ⟨u, α⟩
  simp [primalDualGrading]

theorem graph_neutral_pairing
    (L : V →ₗ[ℝ] Covector V)
    (hL : IsSymmetricDuality L)
    (u v : V) :
    normalizedNeutralPairing (graphLift L u) (graphLift L v) = (L u) v := by
  unfold normalizedNeutralPairing
  rw [canonicalNeutralBilin_apply]
  dsimp [graphLift]
  rw [hL u v]
  ring

theorem graph_symplectic_isotropic
    (L : V →ₗ[ℝ] Covector V)
    (hL : IsSymmetricDuality L)
    (u v : V) :
    canonicalSymplectic (graphLift L u) (graphLift L v) = 0 := by
  unfold canonicalSymplectic graphLift
  rw [hL u v]
  ring

theorem graph_is_lagrangian_in_finite_pairing_sense
    (L : V →ₗ[ℝ] Covector V)
    (hL : IsSymmetricDuality L)
    (u v : V) :
    canonicalSymplectic (graphLift L u) (graphLift L v) = 0 :=
  graph_symplectic_isotropic L hL u v

end InfoGeometry.Geometry.DualFlatKreinLegendreGraph
