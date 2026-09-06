import InfoGeometry.OperatorAlgebra.ChiralOperatorEnvelope

namespace InfoGeometry.OperatorAlgebra

open ChiralOperatorEnvelope

/-!
# Integer charge filtration for chiral operator words

The charge is attached first to formal associative words.  This records the
candidate integer grading without identifying higher operator words with the
eight-dimensional Zorn symbols.
-/

abbrev ChiralWord := List ChiralGenerator

def chargeSector (r : Int) : Set ChiralWord :=
  {w | wordDegree w = r}

def operatorWordProduct {R : Type*} [CommRing R]
    (u v : ChiralWord) : ChiralOperatorEnvelope R :=
  word (R := R) (u ++ v)

theorem operatorWordProduct_eq_mul {R : Type*} [CommRing R]
    (u v : ChiralWord) :
    operatorWordProduct (R := R) u v =
      word (R := R) u * word (R := R) v :=
  word_append u v

theorem charge_concat (u v : ChiralWord) :
    wordDegree (u ++ v) = wordDegree u + wordDegree v :=
  wordDegree_append u v

def positivePairWord (i j : Fin 3) : ChiralWord :=
  [.sPlus i, .sPlus j]

def negativePairWord (i j : Fin 3) : ChiralWord :=
  [.sMinus i, .sMinus j]

def mixedPlusMinusWord (i j : Fin 3) : ChiralWord :=
  [.sPlus i, .sMinus j]

def mixedMinusPlusWord (i j : Fin 3) : ChiralWord :=
  [.sMinus i, .sPlus j]

theorem positivePairWord_charge (i j : Fin 3) :
    wordDegree (positivePairWord i j) = 2 := by
  simp [positivePairWord, wordDegree, generatorDegree]

theorem negativePairWord_charge (i j : Fin 3) :
    wordDegree (negativePairWord i j) = -2 := by
  simp [negativePairWord, wordDegree, generatorDegree]

theorem mixedPlusMinusWord_charge (i j : Fin 3) :
    wordDegree (mixedPlusMinusWord i j) = 0 := by
  simp [mixedPlusMinusWord, wordDegree, generatorDegree]

theorem mixedMinusPlusWord_charge (i j : Fin 3) :
    wordDegree (mixedMinusPlusWord i j) = 0 := by
  simp [mixedMinusPlusWord, wordDegree, generatorDegree]

theorem positivePairWord_mem_chargeSector (i j : Fin 3) :
    positivePairWord i j ∈ chargeSector 2 :=
  positivePairWord_charge i j

theorem negativePairWord_mem_chargeSector (i j : Fin 3) :
    negativePairWord i j ∈ chargeSector (-2) :=
  negativePairWord_charge i j

theorem mixedPlusMinusWord_mem_chargeSector (i j : Fin 3) :
    mixedPlusMinusWord i j ∈ chargeSector 0 :=
  mixedPlusMinusWord_charge i j

theorem mixedMinusPlusWord_mem_chargeSector (i j : Fin 3) :
    mixedMinusPlusWord i j ∈ chargeSector 0 :=
  mixedMinusPlusWord_charge i j

end InfoGeometry.OperatorAlgebra

