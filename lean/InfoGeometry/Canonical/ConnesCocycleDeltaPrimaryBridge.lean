import InfoGeometry.Canonical.RelativeModularSingularization
import InfoGeometry.Meta.Architecture

open scoped InnerProductSpace

/-!
# InfoGeometry.Canonical.ConnesCocycleDeltaPrimaryBridge

Conservative bridge from Connes cocycle witnesses to the finite/support
`Δ`-primary owner lane.

This file stays intentionally finite and support-compressed:

- no unbounded affiliated functional calculus,
- no crossed-product construction claims,
- no promotion of interface data to full Type-III owner completeness.
-/

namespace ConnesCocycleDeltaPrimaryBridge

open InfoGeometry.Canonical.PositiveRayCore
open RelativeModularOperator
open RelativeModularSingularization
open InfoGeometry.Volume.ConnesCocycle

section TypeIIIToFiniteSupport

variable {E : Type 0}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {n : ℕ} [Nonempty (Fin n)]

/-- Finite `Δ` shadow induced by a Type-III RN interface readout. -/
@[rep_depth operator]
noncomputable def deltaFiniteShadow
    (rho : ℝ)
    (q q0 : PositiveRay (Fin n)) : Matrix (Fin n) (Fin n) ℝ :=
  rho • relativeModularOperator (n := n) q q0

/--
-- theorem-class: lower bridge identification
Finite shadow chain law induced from the owner cocycle
`relativeModularOperator_cocycle`.
-/
@[rep_depth operator]
theorem deltaFiniteShadow_chain
    (rho : ℝ)
    (q q0 q1 : PositiveRay (Fin n)) :
    deltaFiniteShadow (n := n) rho q q1
      =
    deltaFiniteShadow (n := n) rho q q0
      * relativeModularOperator (n := n) q0 q1 := by
  unfold deltaFiniteShadow
  rw [relativeModularOperator_cocycle]
  rw [smul_mul_assoc]

/-- Support-compressed finite `Δ` shadow for a fixed finite support projector. -/
@[rep_depth operator]
noncomputable def deltaFiniteSupportShadow
    (rho : ℝ)
    (s : Finset (Fin n))
    (q q0 : PositiveRay (Fin n)) : Matrix (Fin n) (Fin n) ℝ :=
  supportProjector (n := n) s * deltaFiniteShadow (n := n) rho q q0

/--
-- theorem-class: transport lemma
Support-compressed finite shadow chain law.
-/
@[rep_depth operator]
theorem deltaFiniteSupportShadow_chain
    (rho : ℝ)
    (s : Finset (Fin n))
    (q q0 q1 : PositiveRay (Fin n)) :
    deltaFiniteSupportShadow (n := n) rho s q q1
      =
    deltaFiniteSupportShadow (n := n) rho s q q0
      * relativeModularOperator (n := n) q0 q1 := by
  unfold deltaFiniteSupportShadow
  rw [deltaFiniteShadow_chain (n := n) rho q q0 q1]
  simp [mul_assoc]

/--
-- theorem-class: capstone consumer theorem
Bridge package combining:
1) Connes cocycle chaining on the Type-III interface flow,
2) finite `Δ`-shadow state composition,
3) support-compressed finite `Δ`-shadow composition.
-/
@[rep_depth transport, capstone]
theorem connes_to_deltaFiniteSupport_package
    (σ : AdditiveModularFlow (H := E))
    (u : ℝ → AlgebraEnd E)
    (hCocycle : IsConnesCocycle σ u)
    (rho : ℝ)
    (s : Finset (Fin n))
    (q q0 q1 : PositiveRay (Fin n))
    (a b : ℝ) :
    (u (a + b) = u a * σ a (u b))
      ∧
    (deltaFiniteShadow (n := n) rho q q1
        =
      deltaFiniteShadow (n := n) rho q q0
        * relativeModularOperator (n := n) q0 q1)
      ∧
    (deltaFiniteSupportShadow (n := n) rho s q q1
        =
      deltaFiniteSupportShadow (n := n) rho s q q0
        * relativeModularOperator (n := n) q0 q1) := by
  refine ⟨?_, ?_, ?_⟩
  · exact hCocycle a b
  · exact deltaFiniteShadow_chain (n := n) rho q q0 q1
  · exact deltaFiniteSupportShadow_chain (n := n) rho s q q0 q1

end TypeIIIToFiniteSupport

end ConnesCocycleDeltaPrimaryBridge
