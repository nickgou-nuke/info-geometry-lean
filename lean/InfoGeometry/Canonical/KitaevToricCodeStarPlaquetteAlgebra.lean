import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra

noncomputable section

namespace InfoGeometry.Canonical.KitaevToricCodeStarPlaquetteAlgebra

/-!
# Kitaev 2D Toric Code Star & Plaquette Anyonic Commutation Algebra

This module formalizes the topological $Z_2$ stabilizer algebra of the Kitaev 2D Toric Code:
- Local Pauli $X$ and $Z$ operator relations at edge intersections
- Star operator $A_s = X_1 X_2$ involutivity ($A_s^2 = 1$)
- Plaquette operator $B_p = Z_1 Z_2$ involutivity ($B_p^2 = 1$)
- Global Star-Plaquette Commutation $[A_s, B_p] = 0$ ($A_s B_p = B_p A_s$)
- Stabilizer Ground State Projector Idempotency: $P_s^2 = P_s$ for $P_s = \frac{1}{2}(1 + A_s)$.

Proved Theorems:
1. Star Operator Involutivity: $A_s^2 = 1$
2. Plaquette Operator Involutivity: $B_p^2 = 1$
3. Star and Plaquette Commutation: $[A_s, B_p] = 0$ ($A_s B_p = B_p A_s$)
4. Stabilizer Ground State Projector Idempotency: $P_s^2 = P_s$.
-/

variable {R : Type*} [Ring R]

/-- Local Pauli X and Z operator relations for a 2-edge intersection between Star s and Plaquette p. -/
structure ToricCodeLocalIntersection (R : Type*) [Ring R] where
  X1 : R
  X2 : R
  Z1 : R
  Z2 : R

/-- Star operator Product A_s = X₁ X₂. -/
def StarOperator2 (g : ToricCodeLocalIntersection R) : R :=
  g.X1 * g.X2

/-- Plaquette operator Product B_p = Z₁ Z₂. -/
def PlaquetteOperator2 (g : ToricCodeLocalIntersection R) : R :=
  g.Z1 * g.Z2

/-- **Theorem**: Star Operator Involutivity: A_s² = 1. -/
theorem star_operator_square (g : ToricCodeLocalIntersection R)
    (h_X1_sq : g.X1 * g.X1 = 1)
    (h_X2_sq : g.X2 * g.X2 = 1)
    (h_comm_X1_X2 : g.X1 * g.X2 = g.X2 * g.X1) :
    StarOperator2 g * StarOperator2 g = 1 := by
  dsimp [StarOperator2]
  have h_assoc : g.X1 * g.X2 * (g.X1 * g.X2) = g.X1 * (g.X2 * g.X1) * g.X2 := by noncomm_ring
  rw [h_assoc, ← h_comm_X1_X2, ← mul_assoc, h_X1_sq, one_mul, h_X2_sq]

/-- **Theorem**: Plaquette Operator Involutivity: B_p² = 1. -/
theorem plaquette_operator_square (g : ToricCodeLocalIntersection R)
    (h_Z1_sq : g.Z1 * g.Z1 = 1)
    (h_Z2_sq : g.Z2 * g.Z2 = 1)
    (h_comm_Z1_Z2 : g.Z1 * g.Z2 = g.Z2 * g.Z1) :
    PlaquetteOperator2 g * PlaquetteOperator2 g = 1 := by
  dsimp [PlaquetteOperator2]
  have h_assoc : g.Z1 * g.Z2 * (g.Z1 * g.Z2) = g.Z1 * (g.Z2 * g.Z1) * g.Z2 := by noncomm_ring
  rw [h_assoc, ← h_comm_Z1_Z2, ← mul_assoc, h_Z1_sq, one_mul, h_Z2_sq]

/-- **Theorem**: Star and Plaquette Commutation: [A_s, B_p] = 0 (A_s B_p = B_p A_s). -/
theorem star_plaquette_commutation (g : ToricCodeLocalIntersection R)
    (h_anti1 : g.X1 * g.Z1 = -(g.Z1 * g.X1))
    (h_anti2 : g.X2 * g.Z2 = -(g.Z2 * g.X2))
    (h_comm_X1_Z2 : g.X1 * g.Z2 = g.Z2 * g.X1)
    (h_comm_X2_Z1 : g.X2 * g.Z1 = g.Z1 * g.X2) :
    StarOperator2 g * PlaquetteOperator2 g = PlaquetteOperator2 g * StarOperator2 g := by
  dsimp [StarOperator2, PlaquetteOperator2]
  have h1 : g.X1 * g.X2 * (g.Z1 * g.Z2) = g.X1 * (g.X2 * g.Z1) * g.Z2 := by noncomm_ring
  have h2 : g.X1 * (g.Z1 * g.X2) * g.Z2 = (g.X1 * g.Z1) * (g.X2 * g.Z2) := by noncomm_ring
  have h3 : (- (g.Z1 * g.X1)) * (- (g.Z2 * g.X2)) = g.Z1 * g.X1 * (g.Z2 * g.X2) := by noncomm_ring
  have h4 : g.Z1 * g.X1 * (g.Z2 * g.X2) = g.Z1 * (g.X1 * g.Z2) * g.X2 := by noncomm_ring
  have h5 : g.Z1 * (g.Z2 * g.X1) * g.X2 = g.Z1 * g.Z2 * (g.X1 * g.X2) := by noncomm_ring
  rw [h1, h_comm_X2_Z1, h2, h_anti1, h_anti2, h3, h4, h_comm_X1_Z2, h5]

/-- **Theorem**: Stabilizer Projector Idempotent Property for A_s² = 1. -/
theorem stabilizer_projector_idempotent {S : Type*} [Ring S] [Algebra ℝ S]
    (As : S) (h : As * As = 1) :
    (algebraMap ℝ S (1/2) * (1 + As)) * (algebraMap ℝ S (1/2) * (1 + As)) = algebraMap ℝ S (1/2) * (1 + As) := by
  have h_comm : (1 + As) * algebraMap ℝ S (1/2) = algebraMap ℝ S (1/2) * (1 + As) := (Algebra.commutes (1/2 : ℝ) (1 + As)).symm
  have h_exp : (1 + As) * (1 + As) = 2 * (1 + As) := by
    calc (1 + As) * (1 + As) = 1 + As + As + As * As := by noncomm_ring
    _ = 1 + As + As + 1 := by rw [h]
    _ = 2 * (1 + As) := by noncomm_ring
  calc (algebraMap ℝ S (1/2) * (1 + As)) * (algebraMap ℝ S (1/2) * (1 + As))
    _ = algebraMap ℝ S (1/2) * ((1 + As) * algebraMap ℝ S (1/2)) * (1 + As) := by noncomm_ring
    _ = algebraMap ℝ S (1/2) * (algebraMap ℝ S (1/2) * (1 + As)) * (1 + As) := by rw [h_comm]
    _ = (algebraMap ℝ S (1/2) * algebraMap ℝ S (1/2)) * ((1 + As) * (1 + As)) := by noncomm_ring
    _ = algebraMap ℝ S (1/4) * (2 * (1 + As)) := by rw [← map_mul (algebraMap ℝ S)]; norm_num; rw [h_exp]
    _ = (algebraMap ℝ S (1/4) * algebraMap ℝ S 2) * (1 + As) := by rw [← map_ofNat (algebraMap ℝ S)]; noncomm_ring
    _ = algebraMap ℝ S (1/2) * (1 + As) := by rw [← map_mul (algebraMap ℝ S)]; norm_num

end InfoGeometry.Canonical.KitaevToricCodeStarPlaquetteAlgebra
