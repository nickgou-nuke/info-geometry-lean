import InfoGeometry.Algebra.Zorn.G2TwoSylowSubgroup
import InfoGeometry.Algebra.Zorn.G2TwoPCNormalForm

namespace InfoGeometry.Algebra.Zorn.G2TwoPCConcreteFacts

open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem
open InfoGeometry.Algebra.Zorn.G2TwoSylowPCAutomorphisms
open InfoGeometry.Algebra.Zorn.G2TwoSylowSubgroup
open InfoGeometry.Algebra.Zorn.G2TwoPCNormalForm

def oneAt (i : Fin 6) : PCWordExp := fun j => i = j

def oneAtBit (i : Fin 6) (b : Bool) : PCWordExp :=
  if b then oneAt i else zeroPC

theorem pcWord_zero_eq_one :
    G2TwoSylowSubgroup.pcWord (fun _ : Fin 6 => false) = 1 := by
  dsimp [G2TwoSylowSubgroup.pcWord, G2TwoSylowSubgroup.pcTerm]
  simp

theorem pcWord_oneAt_eq_generator (i : Fin 6) :
    G2TwoSylowSubgroup.pcWord (oneAt i) = pcGenerator i := by
  fin_cases i <;>
    simp [oneAt, G2TwoSylowSubgroup.pcWord,
      G2TwoSylowSubgroup.pcTerm, pcGenerator]

theorem pcGenerator_mem_pcWord_range (i : Fin 6) :
    pcGenerator i ∈ Set.range G2TwoSylowSubgroup.pcWord := by
  exact ⟨oneAt i, pcWord_oneAt_eq_generator i⟩

theorem pcWord_oneAtBit (i : Fin 6) (b : Bool) :
    G2TwoSylowSubgroup.pcWord (oneAtBit i b) =
      if b then pcGenerator i else 1 := by
  dsimp [oneAtBit]
  split
  · exact pcWord_oneAt_eq_generator i
  · exact pcWord_zero_eq_one

theorem pcWord_factorized (e : PCWordExp) :
    G2TwoSylowSubgroup.pcWord e =
      G2TwoSylowSubgroup.pcWord (oneAtBit 0 (e 0)) *
      G2TwoSylowSubgroup.pcWord (oneAtBit 1 (e 1)) *
      G2TwoSylowSubgroup.pcWord (oneAtBit 2 (e 2)) *
      G2TwoSylowSubgroup.pcWord (oneAtBit 3 (e 3)) *
      G2TwoSylowSubgroup.pcWord (oneAtBit 4 (e 4)) *
      G2TwoSylowSubgroup.pcWord (oneAtBit 5 (e 5)) := by
  simp only [pcWord_oneAtBit]
  dsimp [G2TwoSylowSubgroup.pcWord, G2TwoSylowSubgroup.pcTerm,
    oneAtBit, oneAt, zeroPC]

end InfoGeometry.Algebra.Zorn.G2TwoPCConcreteFacts
