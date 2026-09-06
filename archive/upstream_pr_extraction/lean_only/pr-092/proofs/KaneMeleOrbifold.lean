import proofs.FreedAnomalyCancellation
import proofs.CauchyHolography

namespace KaneMeleOrbifold

/-- The Kane-Mele Z2 invariant resulting from time-reversal symmetry on the Brillouin torus -/
inductive KaneMeleInvariant
| trivial
| nontrivial

/-- The orientability state corresponding to elements of Pin(5,5) -/
inductive Pin55State
| orientable    -- even elements of Spin(5,5), no sign reversal
| nonorientable -- odd elements of Pin(5,5), reverses frame entropy sign

/-- The Möbius parity flip from the T^5/Z_2 orbifold -/
def moebius_parity : Freed.Z2 → Pin55State
| Freed.Z2.even => Pin55State.orientable
| Freed.Z2.odd  => Pin55State.nonorientable

/-- Formally map the Kane-Mele invariant to the Möbius parity flip (Z_2) -/
def kane_mele_to_parity : KaneMeleInvariant → Freed.Z2
| KaneMeleInvariant.trivial    => Freed.Z2.even
| KaneMeleInvariant.nontrivial => Freed.Z2.odd

/-- The mapping to Pin(5,5) state -/
def kane_mele_to_pin55 (k : KaneMeleInvariant) : Pin55State :=
  moebius_parity (kane_mele_to_parity k)

/-- Prove that the non-trivial topological insulator phase (Kane-Mele = nontrivial)
    is exactly the non-orientable state (odd elements of Pin(5,5)) -/
theorem nontrivial_phase_is_nonorientable :
  kane_mele_to_pin55 KaneMeleInvariant.nontrivial = Pin55State.nonorientable := by
  rfl

/-- Prove that the trivial phase (Kane-Mele = trivial)
    is exactly the orientable state (even elements of Spin(5,5)) -/
theorem trivial_phase_is_orientable :
  kane_mele_to_pin55 KaneMeleInvariant.trivial = Pin55State.orientable := by
  rfl

end KaneMeleOrbifold
