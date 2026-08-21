import InfoGeometry.Algebra.Zorn.G2TwoSylowPCAutomorphisms
import InfoGeometry.Algebra.Zorn.G2TwoCarrierCoordinateLemmas
import InfoGeometry.Algebra.Zorn.G2TwoMatrixCarrier
import InfoGeometry.Algebra.Zorn.G2TwoSylowSubgroup

namespace InfoGeometry.Algebra.Zorn.G2TwoPCRecovery

open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem
open InfoGeometry.Algebra.Zorn.G2TwoMatrixCarrier
open InfoGeometry.Algebra.Zorn.G2TwoCarrierCoordinateLemmas
open InfoGeometry.Algebra.Zorn.G2TwoBooleanNormalizer
open InfoGeometry.Algebra.Zorn.G2TwoSylowPCGenerators
open InfoGeometry.Algebra.Zorn.G2TwoSylowPCAutomorphisms
open InfoGeometry.Algebra.Zorn.G2TwoSylowSubgroup (PCWordExp pcWordFun pcTermFun pcWord_apply)

/-- The exact CAS coordinate recovery functions on SplitOctF2Aut. -/
def recoverBit0 (w : SplitOctF2Aut) : Bool := (w.1 (basis8 7)).x0
def recoverBit1 (w : SplitOctF2Aut) : Bool := (w.1 (basis8 2)).x1
def recoverBit2 (w : SplitOctF2Aut) : Bool := (w.1 (basis8 2)).a
def recoverBit4 (w : SplitOctF2Aut) : Bool :=
  let b1 := recoverBit1 w
  let b2 := recoverBit2 w
  (w.1 (basis8 2)).y1 ^^ b1 ^^ b2
def recoverBit3 (w : SplitOctF2Aut) : Bool :=
  let b0 := recoverBit0 w
  let b1 := recoverBit1 w
  let b2 := recoverBit2 w
  let b4 := recoverBit4 w
  (w.1 (basis8 3)).x2 ^^ (b0 && b2) ^^ b0 ^^ b1 ^^ b2 ^^ b4
def recoverBit5 (w : SplitOctF2Aut) : Bool :=
  let b1 := recoverBit1 w
  let b3 := recoverBit3 w
  let b4 := recoverBit4 w
  (w.1 (basis8 2)).x2 ^^ (b1 && b3) ^^ (b1 && b4)

/-- Bundled recovery function from SplitOctF2Aut to PCWordExp. -/
def recoverPCWordExp (w : SplitOctF2Aut) : PCWordExp
  | 0 => recoverBit0 w
  | 1 => recoverBit1 w
  | 2 => recoverBit2 w
  | 3 => recoverBit3 w
  | 4 => recoverBit4 w
  | 5 => recoverBit5 w

/-- Lemma 0: recoverBit0 correctly extracts bit 0 from G2TwoSylowSubgroup.pcWord e. -/
theorem recoverBit0_pcWord (e : PCWordExp) :
    recoverBit0 (G2TwoSylowSubgroup.pcWord e) = e 0 := by
  dsimp [recoverBit0, G2TwoSylowSubgroup.pcWord, pcWord_apply, pcWordFun, pcTermFun, basis8]
  rcases e 0 with _|_ <;> rcases e 1 with _|_ <;> rcases e 2 with _|_ <;>
  rcases e 3 with _|_ <;> rcases e 4 with _|_ <;> rcases e 5 with _|_ <;> rfl

/-- Lemma 1: recoverBit1 correctly extracts bit 1 from G2TwoSylowSubgroup.pcWord e. -/
theorem recoverBit1_pcWord (e : PCWordExp) :
    recoverBit1 (G2TwoSylowSubgroup.pcWord e) = e 1 := by
  dsimp [recoverBit1, G2TwoSylowSubgroup.pcWord, pcWord_apply, pcWordFun, pcTermFun, basis8]
  rcases e 0 with _|_ <;> rcases e 1 with _|_ <;> rcases e 2 with _|_ <;>
  rcases e 3 with _|_ <;> rcases e 4 with _|_ <;> rcases e 5 with _|_ <;> rfl

/-- Lemma 2: recoverBit2 correctly extracts bit 2 from G2TwoSylowSubgroup.pcWord e. -/
theorem recoverBit2_pcWord (e : PCWordExp) :
    recoverBit2 (G2TwoSylowSubgroup.pcWord e) = e 2 := by
  dsimp [recoverBit2, G2TwoSylowSubgroup.pcWord, pcWord_apply, pcWordFun, pcTermFun, basis8]
  rcases e 0 with _|_ <;> rcases e 1 with _|_ <;> rcases e 2 with _|_ <;>
  rcases e 3 with _|_ <;> rcases e 4 with _|_ <;> rcases e 5 with _|_ <;> rfl

/-- Lemma 4: recoverBit4 correctly extracts bit 4 from G2TwoSylowSubgroup.pcWord e. -/
theorem recoverBit4_pcWord (e : PCWordExp) :
    recoverBit4 (G2TwoSylowSubgroup.pcWord e) = e 4 := by
  dsimp [recoverBit4, recoverBit1, recoverBit2, G2TwoSylowSubgroup.pcWord, pcWord_apply, pcWordFun, pcTermFun, basis8]
  rcases e 0 with _|_ <;> rcases e 1 with _|_ <;> rcases e 2 with _|_ <;>
  rcases e 3 with _|_ <;> rcases e 4 with _|_ <;> rcases e 5 with _|_ <;> rfl

/-- Lemma 3: recoverBit3 correctly extracts bit 3 from G2TwoSylowSubgroup.pcWord e. -/
theorem recoverBit3_pcWord (e : PCWordExp) :
    recoverBit3 (G2TwoSylowSubgroup.pcWord e) = e 3 := by
  dsimp [recoverBit3, recoverBit4, recoverBit0, recoverBit1, recoverBit2,
         G2TwoSylowSubgroup.pcWord, pcWord_apply, pcWordFun, pcTermFun, basis8]
  rcases e 0 with _|_ <;> rcases e 1 with _|_ <;> rcases e 2 with _|_ <;>
  rcases e 3 with _|_ <;> rcases e 4 with _|_ <;> rcases e 5 with _|_ <;> rfl

/-- Lemma 5: recoverBit5 correctly extracts bit 5 from G2TwoSylowSubgroup.pcWord e. -/
theorem recoverBit5_pcWord (e : PCWordExp) :
    recoverBit5 (G2TwoSylowSubgroup.pcWord e) = e 5 := by
  dsimp [recoverBit5, recoverBit3, recoverBit4, recoverBit0, recoverBit1, recoverBit2,
         G2TwoSylowSubgroup.pcWord, pcWord_apply, pcWordFun, pcTermFun, basis8]
  rcases e 0 with _|_ <;> rcases e 1 with _|_ <;> rcases e 2 with _|_ <;>
  rcases e 3 with _|_ <;> rcases e 4 with _|_ <;> rcases e 5 with _|_ <;> rfl

/-- 🏆 THEOREM: recoverPCWordExp is a strict left inverse of pcWord. -/
theorem recoverPCWordExp_pcWord (e : PCWordExp) :
    recoverPCWordExp (G2TwoSylowSubgroup.pcWord e) = e := by
  ext i
  fin_cases i
  · exact recoverBit0_pcWord e
  · exact recoverBit1_pcWord e
  · exact recoverBit2_pcWord e
  · exact recoverBit3_pcWord e
  · exact recoverBit4_pcWord e
  · exact recoverBit5_pcWord e

/-- 🏆 COROLLARY: G2TwoSylowSubgroup.pcWord is strictly injective without `by decide`. -/
theorem pcWord_injective_structural : Function.Injective G2TwoSylowSubgroup.pcWord := by
  intro e1 e2 h
  have h_rec := congrArg recoverPCWordExp h
  rw [recoverPCWordExp_pcWord e1, recoverPCWordExp_pcWord e2] at h_rec
  exact h_rec

end InfoGeometry.Algebra.Zorn.G2TwoPCRecovery
