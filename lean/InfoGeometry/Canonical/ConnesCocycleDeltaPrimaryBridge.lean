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

namespace InfoGeometry.Canonical.ConnesCocycleDeltaPrimaryBridge

open InfoGeometry.Canonical.PositiveRayCore
open RelativeModularOperator
open RelativeModularSingularization
open InfoGeometry.Volume.ConnesCocycle

section TypeIIIToFiniteSupport

variable {E : Type 0}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {n : ℕ} [Nonempty (Fin n)]

/-- Finite `Δ` operator readout from the relative-modular owner. -/
@[rep_depth operator]
noncomputable def deltaFiniteOperator
    (q q0 : PositiveRay (Fin n)) : Matrix (Fin n) (Fin n) ℝ :=
  relativeModularOperator (n := n) q q0

/--
-- theorem-class: lower bridge identification
Finite shadow chain law induced from the owner cocycle
`relativeModularOperator_cocycle`.
-/
@[rep_depth operator]
theorem deltaFiniteOperator_chain
    (q q0 q1 : PositiveRay (Fin n)) :
    deltaFiniteOperator (n := n) q q1
      =
    deltaFiniteOperator (n := n) q q0
      * relativeModularOperator (n := n) q0 q1 := by
  exact relativeModularOperator_cocycle (n := n) q q0 q1

/-- Support-compressed finite `Δ` operator for a fixed finite support projector. -/
@[rep_depth operator]
noncomputable def deltaFiniteSupportOperator
    (s : Finset (Fin n))
    (q q0 : PositiveRay (Fin n)) : Matrix (Fin n) (Fin n) ℝ :=
  supportProjector (n := n) s * deltaFiniteOperator (n := n) q q0

/--
-- theorem-class: transport lemma
Support-compressed finite shadow chain law.
-/
@[rep_depth operator]
theorem deltaFiniteSupportOperator_chain
    (s : Finset (Fin n))
    (q q0 q1 : PositiveRay (Fin n)) :
    deltaFiniteSupportOperator (n := n) s q q1
      =
    deltaFiniteSupportOperator (n := n) s q q0
      * relativeModularOperator (n := n) q0 q1 := by
  unfold deltaFiniteSupportOperator
  rw [deltaFiniteOperator_chain (n := n) q q0 q1]
  simp [mul_assoc]

/--
-- theorem-class: capstone consumer theorem
Bridge package combining:
1) Connes cocycle chaining on the Type-III interface flow,
2) finite `Δ`-operator state composition,
3) support-compressed finite `Δ`-operator composition.
-/
@[rep_depth transport, capstone]
theorem connes_to_deltaFiniteSupport_package
    (σ : AdditiveModularFlow (H := E))
    (u : ℝ → AlgebraEnd E)
    (hCocycle : IsConnesCocycle σ u)
    (s : Finset (Fin n))
    (q q0 q1 : PositiveRay (Fin n))
    (a b : ℝ) :
    (u (a + b) = u a * σ a (u b))
      ∧
    (deltaFiniteOperator (n := n) q q1
        =
      deltaFiniteOperator (n := n) q q0
        * relativeModularOperator (n := n) q0 q1)
      ∧
    (deltaFiniteSupportOperator (n := n) s q q1
        =
      deltaFiniteSupportOperator (n := n) s q q0
        * relativeModularOperator (n := n) q0 q1) := by
  refine ⟨?_, ?_, ?_⟩
  · exact hCocycle a b
  · exact deltaFiniteOperator_chain (n := n) q q0 q1
  · exact deltaFiniteSupportOperator_chain (n := n) s q q0 q1

end TypeIIIToFiniteSupport

end InfoGeometry.Canonical.ConnesCocycleDeltaPrimaryBridge
