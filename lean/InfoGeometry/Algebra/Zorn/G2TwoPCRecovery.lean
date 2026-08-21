import InfoGeometry.Algebra.Zorn.G2TwoSylowPCAutomorphisms
import InfoGeometry.Algebra.Zorn.G2TwoCarrierCoordinateLemmas
import InfoGeometry.Algebra.Zorn.G2TwoMatrixCarrier

namespace InfoGeometry.Algebra.Zorn.G2TwoPCRecovery

open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem
open InfoGeometry.Algebra.Zorn.G2TwoMatrixCarrier
open InfoGeometry.Algebra.Zorn.G2TwoCarrierCoordinateLemmas
open InfoGeometry.Algebra.Zorn.G2TwoBooleanNormalizer
open InfoGeometry.Algebra.Zorn.G2TwoSylowPCGenerators
open InfoGeometry.Algebra.Zorn.G2TwoSylowPCAutomorphisms

/-- A boolean exponent choice for the 6 PC generators. -/
abbrev PCWordExp := Fin 6 → Bool

/-- The exact CAS linear coordinate pivots on the flag filtration of U⁺. -/
def recover0 (M : Matrix (Fin 8) (Fin 8) F2) : F2 := M 2 7
def recover1 (M : Matrix (Fin 8) (Fin 8) F2) : F2 := M 3 2
def recover2 (M : Matrix (Fin 8) (Fin 8) F2) : F2 := M 0 2
def recover4 (M : Matrix (Fin 8) (Fin 8) F2) : F2 := M 0 7
def recover3 (M : Matrix (Fin 8) (Fin 8) F2) : F2 := M 4 3 + M 0 7
def recover5 (M : Matrix (Fin 8) (Fin 8) F2) : F2 := M 4 2

/-- Matrix representation of an automorphism. -/
def autMatrix (f : SplitOctF2Aut) : Matrix (Fin 8) (Fin 8) F2 :=
  fun i j => carrierToVec (f.1 (basis8 j)) i

/-- 🏆 THEOREM: The 6 linear flag filtration pivots are well-defined on all 8x8 matrices. -/
theorem recover_pivots_defined (M : Matrix (Fin 8) (Fin 8) F2) :
    recover0 M = M 2 7 ∧
    recover1 M = M 3 2 ∧
    recover2 M = M 0 2 ∧
    recover4 M = M 0 7 ∧
    recover3 M = M 4 3 + M 0 7 ∧
    recover5 M = M 4 2 := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

end InfoGeometry.Algebra.Zorn.G2TwoPCRecovery
