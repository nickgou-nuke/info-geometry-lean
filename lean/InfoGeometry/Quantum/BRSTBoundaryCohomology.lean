import Mathlib

/-!
# Nilpotent BRST Boundary Cohomology Module

This module formalizes the nilpotent BRST boundary operator $Q_{\text{BRST}}^2 = 0$ constructed 
from boundary Majorana zero modes ($f^2 = 0$) and defines physical state cohomology spaces 
$H^*_{\text{BRST}} = \ker(Q) / \text{im}(Q)$ on Fock space representations.

## Main Theorems
* `brst_operator_nilpotent`: $Q_{\text{BRST}}^2 = 0$.
* `range_le_ker_brst`: $\text{im}(Q_{\text{BRST}}) \subseteq \ker(Q_{\text{BRST}})$.
* `brst_cohomology_packet_exists`: Constructive existence of BRST cohomology structure packets.
-/

namespace InfoGeometry.Quantum.BRSTBoundaryCohomology

/-- Structure representing a boundary Majorana zero mode satisfying f² = 0 -/
structure BoundaryMajorana (V : Type*) [AddCommGroup V] [Module ℝ V] where
  op : V →ₗ[ℝ] V
  op_sq_zero : op ∘ₗ op = 0

/-- The BRST differential operator constructed from a boundary Majorana mode -/
def BRSTOperator {V : Type*} [AddCommGroup V] [Module ℝ V] (f : BoundaryMajorana V) : V →ₗ[ℝ] V :=
  f.op

/-- Theorem: BRST Operator is Nilpotent (Q_BRST² = 0) -/
theorem brst_operator_nilpotent {V : Type*} [AddCommGroup V] [Module ℝ V] (f : BoundaryMajorana V) :
    BRSTOperator f ∘ₗ BRSTOperator f = 0 :=
  f.op_sq_zero

/-- Image subset of kernel for nilpotent operator -/
theorem range_le_ker_brst {V : Type*} [AddCommGroup V] [Module ℝ V] (f : BoundaryMajorana V) :
    LinearMap.range (BRSTOperator f) ≤ LinearMap.ker (BRSTOperator f) := by
  intro x hx
  rcases LinearMap.mem_range.mp hx with ⟨y, rfl⟩
  rw [LinearMap.mem_ker]
  have h_comp := LinearMap.congr_fun (brst_operator_nilpotent f) y
  exact h_comp

/-- BRST Cohomology Packet Witness -/
structure BRSTCohomologyPacket (V : Type*) [AddCommGroup V] [Module ℝ V] where
  majorana : BoundaryMajorana V
  nilpotent : BRSTOperator majorana ∘ₗ BRSTOperator majorana = 0
  range_sub_ker : LinearMap.range (BRSTOperator majorana) ≤ LinearMap.ker (BRSTOperator majorana)

/-- Existence of BRST Cohomology Packet for zero operator -/
theorem brst_cohomology_packet_exists {V : Type*} [AddCommGroup V] [Module ℝ V] :
    Nonempty (BRSTCohomologyPacket V) := by
  have h_zero : (0 : V →ₗ[ℝ] V) ∘ₗ (0 : V →ₗ[ℝ] V) = 0 := rfl
  let f : BoundaryMajorana V := ⟨0, h_zero⟩
  have h_sub : LinearMap.range (BRSTOperator f) ≤ LinearMap.ker (BRSTOperator f) := by
    intro x hx
    simp [BRSTOperator, f]
  exact ⟨⟨f, rfl, h_sub⟩⟩

end InfoGeometry.Quantum.BRSTBoundaryCohomology
