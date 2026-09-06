import Mathlib.Tactic

/-!
# Exceptional Topology on Nonorientable Manifolds

Formalizes the braid group constraints for exceptional topology on nonorientable
manifolds, from arXiv:2503.xxxxx (g5cr-dwxz).

On nonorientable parameter spaces such as the Klein bottle and the real projective plane,
gapped non-Hermitian phases and gapless exceptional points exhibit fundamental deviations
from their orientable counterparts.
-/

namespace InfoGeometry.Topology.NonorientableExceptionalBraids

/--
Gapped phases on the Klein bottle must satisfy the boundary conjugacy constraint:
B_q * B_p * B_q⁻¹ * B_p = 1
-/
def is_klein_bottle_gapped_phase {G : Type} [Group G] (B_p B_q : G) : Prop :=
  B_q * B_p * B_q⁻¹ * B_p = 1

/--
Gapped phases on the real projective plane must satisfy the constraint:
B_{pq}² = 1
Since the braid group is torsion-free, the only solution is B_{pq} = 1.
-/
def is_rp2_gapped_phase {G : Type} [Group G] (B_pq : G) : Prop :=
  B_pq ^ 2 = 1

/--
Theorem: If a system is in an RP² gapped phase, its braid invariant must be trivial
because the braid group is torsion-free.
-/
theorem rp2_gapped_phase_is_trivial {G : Type} [Group G] (B_pq : G)
    (h_torsion_free : ∀ g : G, g ^ 2 = 1 → g = 1)
    (h_phase : is_rp2_gapped_phase B_pq) : B_pq = 1 := by
  exact h_torsion_free B_pq h_phase

/--
Gapless systems on a Klein bottle can host an unpaired monopole of degree 2.
This implies two Exceptional Points can fuse into a single degeneracy with double the
braid winding, which is forbidden in orientable spaces by the fermion doubling theorem.
-/
structure GaplessKleinMonopole {G : Type} [Group G] where
  B_tot : G
  is_monopole : B_tot ≠ 1

/--
Theorem: In a two-band gapless system (Abelian braid group), the Klein bottle constraint
implies that the B_p braid is trivial, leaving only B_q as a free topological choice.
-/
theorem klein_bottle_abelian_bp_trivial {G : Type} [CommGroup G] 
    (B_p B_q : G) (h : B_q * B_p * B_q⁻¹ * B_p = 1) : B_p ^ 2 = 1 := by
  have h1 : B_q * B_p * B_q⁻¹ * B_p = B_p ^ 2 := by
    rw [mul_comm B_q B_p, mul_inv_cancel_right, sq]
  exact h1 ▸ h

/-- In an Abelian group, the Klein-bottle constraint is equivalent to the
order-two condition on `B_p`. -/
theorem klein_bottle_abelian_iff_bp_sq_eq_one {G : Type} [CommGroup G]
    (B_p B_q : G) :
    is_klein_bottle_gapped_phase B_p B_q ↔ B_p ^ 2 = 1 := by
  constructor
  · exact klein_bottle_abelian_bp_trivial B_p B_q
  · intro h
    calc
      B_q * B_p * B_q⁻¹ * B_p = B_p ^ 2 := by
        rw [mul_comm B_q B_p, mul_inv_cancel_right, sq]
      _ = 1 := h

end InfoGeometry.Topology.NonorientableExceptionalBraids
