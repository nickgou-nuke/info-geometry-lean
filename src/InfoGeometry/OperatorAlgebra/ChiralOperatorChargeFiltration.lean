/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.ChiralOperatorEnvelope
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.OperatorAlgebra

open ChiralOperatorEnvelope

/-!
# Integer charge filtration for chiral operator words

The charge is attached first to formal associative words and their direct
evaluation in any non-commutative operator ring `A`, as well as in the
universal free envelope. This records the candidate integer grading without
identifying higher operator words with the eight-dimensional Zorn symbols.
-/

abbrev ChiralWord := List ChiralGenerator

def chargeSector (r : Int) : Set ChiralWord :=
  {w | wordDegree w = r}

def evalOperatorWordProduct {A : Type*} [Ring A]
    (ρ : ChiralGenerator → A) (u v : ChiralWord) : A :=
  evalWord ρ (u ++ v)

theorem evalOperatorWordProduct_eq_mul {A : Type*} [Ring A]
    (ρ : ChiralGenerator → A) (u v : ChiralWord) :
    evalOperatorWordProduct ρ u v =
      evalWord ρ u * evalWord ρ v :=
  evalWord_append ρ u v

def operatorWordProduct {R : Type*} [CommSemiring R]
    (u v : ChiralWord) : ChiralOperatorEnvelope R :=
  word (R := R) (u ++ v)

theorem operatorWordProduct_eq_mul {R : Type*} [CommSemiring R]
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
