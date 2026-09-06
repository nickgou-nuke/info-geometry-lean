import InfoGeometry.Algebra.Zorn.G2TwoBasisRigidity
import InfoGeometry.Algebra.Zorn.G2PeirceFibration
import InfoGeometry.Algebra.Zorn.G2PeircePrefixCarrierFacts

namespace InfoGeometry.Algebra.Zorn.G2AdmissibleBasisCardinalityBridge

open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem
open InfoGeometry.Algebra.Zorn.G2PeirceFibration

theorem natCard_aut_eq_natCard_admissibleBasis7 :
    Nat.card SplitOctF2Aut =
      Nat.card {v : Fin 7 → SplitOctF2 // admissibleBasis7 v} := by
  exact Nat.card_congr admissibleBasis7Equiv

theorem fintypeCard_aut_eq_fintypeCard_admissibleBasis7 :
    Fintype.card SplitOctF2Aut =
      Fintype.card {v : Fin 7 → SplitOctF2 // admissibleBasis7 v} := by
  exact Fintype.card_congr admissibleBasis7Equiv

theorem natCard_admissibleBasis7_eq_peirceFibrationCard :
    Nat.card {v : Fin 7 → SplitOctF2 // admissibleBasis7 v} =
      Nat.card
        (Σ (p : NontrivialIdempotent),
          Σ (x : PeircePlusFiber p), ResidualFiber p x) := by
  exact Nat.card_congr peirceFibrationEquiv

theorem fintypeCard_admissibleBasis7_eq_peirceFibrationCard
    [Fintype NontrivialIdempotent]
    [∀ p : NontrivialIdempotent, Fintype (PeircePlusFiber p)]
    [∀ (p : NontrivialIdempotent) (x : PeircePlusFiber p),
      Fintype (ResidualFiber p x)] :
    Fintype.card {v : Fin 7 → SplitOctF2 // admissibleBasis7 v} =
      Fintype.card
        (Σ (p : NontrivialIdempotent),
          Σ (x : PeircePlusFiber p), ResidualFiber p x) := by
  exact Fintype.card_congr peirceFibrationEquiv

theorem fintypeCard_admissibleBasis7_eq_peirceFibrationCard_native :
    Fintype.card {v : Fin 7 → SplitOctF2 // admissibleBasis7 v} =
      Fintype.card
        (Σ (p : NontrivialIdempotent),
          Σ (x : PeircePlusFiber p), ResidualFiber p x) := by
  exact Fintype.card_congr peirceFibrationEquiv

end InfoGeometry.Algebra.Zorn.G2AdmissibleBasisCardinalityBridge
