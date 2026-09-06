import InfoGeometry.Algebra.Zorn.G2ChevalleyPoincareCombinatorics
import InfoGeometry.Algebra.Zorn.G2TwoSylowPCAutomorphisms

/-!
# The verified PC positive-root packet

`positiveRootPacket` in `G2SteinbergPositiveRoots` is a separate root-system
carrier.  Its closure is not the order-64 PC subgroup.  This owner therefore
introduces the root labels for the verified PC carrier without identifying the
two different packets.
-/

namespace InfoGeometry.Algebra.Zorn.G2PCPositiveRootPacket

open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem
open InfoGeometry.Algebra.Zorn.G2Combinatorics
open InfoGeometry.Algebra.Zorn.G2TwoSylowPCAutomorphisms

private def pcRootIndex : G2PositiveRoot → Fin 6
  | .alpha => 0
  | .beta => 1
  | .alpha_add_beta => 2
  | .two_alpha_beta => 3
  | .three_alpha_beta => 4
  | .three_alpha_two_beta => 5

/-- The six positive-root labels attached to the verified PC generators. -/
def pcPositiveRootPacket : G2PositiveRoot → SplitOctF2Aut
  | α => pcGenerator (pcRootIndex α)

theorem pcPositiveRootPacket_eq (α : G2PositiveRoot) :
    pcPositiveRootPacket α = pcGenerator (pcRootIndex α) := by
  rfl

theorem pcPositiveRootPacket_mem_pcSubgroup (α : G2PositiveRoot) :
    pcPositiveRootPacket α ∈ pcSubgroup := by
  rw [pcPositiveRootPacket_eq]
  exact pcGenerator_mem_pcSubgroup _

theorem pcPositiveRootPacket_range_eq_pcGenerator_range :
    Set.range pcPositiveRootPacket = Set.range pcGenerator := by
  ext g
  constructor
  · rintro ⟨α, rfl⟩
    cases α <;> exact ⟨_, (pcPositiveRootPacket_eq _).symm⟩
  · rintro ⟨i, rfl⟩
    fin_cases i
    · exact ⟨.alpha, (pcPositiveRootPacket_eq .alpha).symm⟩
    · exact ⟨.beta, (pcPositiveRootPacket_eq .beta).symm⟩
    · exact ⟨.alpha_add_beta, (pcPositiveRootPacket_eq .alpha_add_beta).symm⟩
    · exact ⟨.two_alpha_beta, (pcPositiveRootPacket_eq .two_alpha_beta).symm⟩
    · exact ⟨.three_alpha_beta, (pcPositiveRootPacket_eq .three_alpha_beta).symm⟩
    · exact ⟨.three_alpha_two_beta, (pcPositiveRootPacket_eq .three_alpha_two_beta).symm⟩

theorem pcPositiveRootSubgroup_eq_pcSubgroup :
    Subgroup.closure (Set.range pcPositiveRootPacket) = pcSubgroup := by
  rw [pcPositiveRootPacket_range_eq_pcGenerator_range]
  rfl

end InfoGeometry.Algebra.Zorn.G2PCPositiveRootPacket
