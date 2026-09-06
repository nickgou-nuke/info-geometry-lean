import InfoGeometry.Algebra.Zorn.G2RootPCAlignment
import InfoGeometry.Algebra.Zorn.G2CanonicalPCCollector
import InfoGeometry.Algebra.Zorn.G2BruhatResidual
import InfoGeometry.Algebra.Zorn.G2TwoPCRecovery

namespace InfoGeometry.Algebra.Zorn.G2RootResidualGenerators

open InfoGeometry.Algebra.Zorn.G2RootPCAlignment
open InfoGeometry.Algebra.Zorn.G2PCPositiveRootPacket
open InfoGeometry.Algebra.Zorn.G2TwoSylowPCAutomorphisms
open InfoGeometry.Algebra.Zorn.G2TwoPCSubgroupClosure
open InfoGeometry.Algebra.Zorn.G2TwoPCConcreteFacts
open InfoGeometry.Algebra.Zorn.G2BruhatResidual
open InfoGeometry.Algebra.Zorn.G2CanonicalPCCollector
open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem

noncomputable def rootResidualGenerator
    (α : InfoGeometry.Algebra.Zorn.G2Combinatorics.G2PositiveRoot) :
    SplitOctF2Aut := pcPositiveRootPacket α

theorem rootResidualGenerator_eq_pcGenerator
    (α : InfoGeometry.Algebra.Zorn.G2Combinatorics.G2PositiveRoot) :
    rootResidualGenerator α = pcGenerator (rootPCAlignment α) := by
  exact pcPositiveRootPacket_eq_aligned_generator α

theorem rootResidualGenerator_mem_unipotentSubgroup
    (α : InfoGeometry.Algebra.Zorn.G2Combinatorics.G2PositiveRoot) :
    rootResidualGenerator α ∈ unipotentSubgroup := by
  rw [rootResidualGenerator_eq_pcGenerator]
  exact ⟨oneAt (rootPCAlignment α), pcWord_oneAt_eq_generator _⟩

theorem rootResidualGenerator_mem_topResidualSubgroup
    (α : InfoGeometry.Algebra.Zorn.G2Combinatorics.G2PositiveRoot) :
    rootResidualGenerator α ∈ residualSubgroup (3, false) := by
  rw [residualSubgroup_top_parameter]
  exact rootResidualGenerator_mem_unipotentSubgroup α

theorem rootResidualGenerator_injective :
    Function.Injective rootResidualGenerator := by
  intro α β h
  have hpc :
      G2TwoSylowSubgroup.pcWord (oneAtBit (rootPCAlignment α) true) =
      G2TwoSylowSubgroup.pcWord (oneAtBit (rootPCAlignment β) true) := by
    calc
      G2TwoSylowSubgroup.pcWord (oneAtBit (rootPCAlignment α) true) =
          pcGenerator (rootPCAlignment α) := by
            change G2TwoSylowSubgroup.pcWord (oneAt (rootPCAlignment α)) = _
            exact pcWord_oneAt_eq_generator (rootPCAlignment α)
      _ = rootResidualGenerator α :=
        (rootResidualGenerator_eq_pcGenerator α).symm
      _ = rootResidualGenerator β := h
      _ = pcGenerator (rootPCAlignment β) :=
        rootResidualGenerator_eq_pcGenerator β
      _ = G2TwoSylowPCAutomorphisms.pcWord
          (oneAtBit (rootPCAlignment β) true) := by
            change _ = G2TwoSylowSubgroup.pcWord (oneAt (rootPCAlignment β))
            exact (pcWord_oneAt_eq_generator (rootPCAlignment β)).symm
  have he : oneAtBit (rootPCAlignment α) true =
      oneAtBit (rootPCAlignment β) true :=
    G2TwoPCRecovery.pcWord_injective hpc
  have hi : rootPCAlignment α = rootPCAlignment β := by
    by_contra hne
    have hv := congrFun he (rootPCAlignment α)
    simp [oneAtBit, oneAt] at hv
    have hv' : rootPCAlignment β = rootPCAlignment α := by
      simpa only [rootPCAlignment_apply] using hv
    exact hne hv'.symm
  exact rootPCAlignment.injective hi

theorem rootResidualGenerator_range_eq_pcGenerator_range :
    Set.range rootResidualGenerator = Set.range pcGenerator := by
  simpa [rootResidualGenerator] using
    pcPositiveRootPacket_range_eq_pcGenerator_range

theorem rootResidualGenerator_range_card :
    Nat.card (Set.range rootResidualGenerator) = 6 := by
  rw [Nat.card_range_of_injective rootResidualGenerator_injective]
  simpa using InfoGeometry.Algebra.Zorn.G2Combinatorics.positive_roots_card

end InfoGeometry.Algebra.Zorn.G2RootResidualGenerators
