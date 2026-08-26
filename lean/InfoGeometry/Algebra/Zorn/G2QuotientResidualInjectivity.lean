import InfoGeometry.Algebra.Zorn.G2OneCellQuotientTransport

namespace InfoGeometry.Algebra.Zorn.G2QuotientResidualInjectivity

open InfoGeometry.Algebra.Zorn.G2CASFactorizationCarrier
open InfoGeometry.Algebra.Zorn.G2CanonicalPCCollector
open InfoGeometry.Algebra.Zorn.G2FlagOrbitPartitionCertificate
open InfoGeometry.Algebra.Zorn.G2FlagWordCertificate
open InfoGeometry.Algebra.Zorn.G2OneCellQuotientTransport
open InfoGeometry.Algebra.Zorn.G2TwoPCSubgroupClosure
open InfoGeometry.Algebra.Zorn.G2TwoPCNormalForm

def factorTokenExponent (t : FactorToken) : PCWordExp :=
  if t.2 = 1 then
    oneAt t.1
  else if t.2 = -1 then
    pcInverse (oneAt t.1)
  else
    zeroPC

def factorWordExponent : FactorWord → PCWordExp
  | [] => zeroPC
  | t :: w => pcCombine (factorTokenExponent t) (factorWordExponent w)

def ValidFactorWord (w : FactorWord) : Prop :=
  ∀ t ∈ w, t.2 = 1 ∨ t.2 = -1

def residualWord (k : Fin 12) (i : Fin 189) : PCWordExp :=
  factorWordExponent (leftFactorWord k i)

theorem factorTokenExponent_pcWord
    (t : FactorToken)
    (ht : t.2 = 1 ∨ t.2 = -1) :
    tokenAutomorphism t =
      G2TwoSylowSubgroup.pcWord (factorTokenExponent t) := by
  rcases ht with rfl | rfl
  · simp [factorTokenExponent, tokenAutomorphism,
      pcWord_oneAt_eq_generator]
  · simp [factorTokenExponent, tokenAutomorphism,
      pcWord_oneAt_eq_generator,
      pcWord_inv]

theorem factorWordExponent_collect
    (w : FactorWord)
    (hw : ValidFactorWord w) :
    collect w =
      G2TwoSylowSubgroup.pcWord (factorWordExponent w) := by
  induction w with
  | nil =>
      simp [collect, factorWordExponent, pcWord_zeroPC_eq_one]
  | cons t w ih =>
      have ht := hw t (by simp)
      have hw' : ∀ u ∈ w, u.2 = 1 ∨ u.2 = -1 := by
        intro u hu
        exact hw u (by simp [hu])
      simp only [collect, factorWordExponent]
      rw [factorTokenExponent_pcWord t ht, ih hw']
      exact (pcWord_mul_pcWord _ _).symm

theorem residualWord_collect_of_valid
    (k : Fin 12) (i : Fin 189)
    (hvalid : ValidFactorWord (leftFactorWord k i)) :
    collect (leftFactorWord k i) =
      G2TwoSylowSubgroup.pcWord (residualWord k i) := by
  exact factorWordExponent_collect (leftFactorWord k i) hvalid

theorem residualWord_eq_of_collect_eq
    (k : Fin 12) (i j : Fin 189)
    (hi : ValidFactorWord (leftFactorWord k i))
    (hj : ValidFactorWord (leftFactorWord k j))
    (hcollect : collect (leftFactorWord k i) =
      collect (leftFactorWord k j)) :
    residualWord k i = residualWord k j := by
  apply G2TwoSylowSubgroup.pcWord_injective
  rw [← residualWord_collect_of_valid k i hi,
    ← residualWord_collect_of_valid k j hj]
  exact hcollect

theorem residualWord_injective_on_cell_0 :
    ∀ i j : Fin 189,
        i ∈ orbitCells 0 → j ∈ orbitCells 0 →
        residualWord 0 i = residualWord 0 j → i = j := by
  intro i j hi hj _
  have hi0 : i = 0 := by
    simpa [orbitCells, flagCells] using hi
  have hj0 : j = 0 := by
    simpa [orbitCells, flagCells] using hj
  exact hi0.trans hj0.symm

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem residualWord_injective_on_cell_1 :
    ∀ i j : Fin 189,
        i ∈ orbitCells 1 → j ∈ orbitCells 1 →
        residualWord 1 i = residualWord 1 j → i = j := by
  native_decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem residualWord_injective_on_cell_2 :
    ∀ i j : Fin 189,
        i ∈ orbitCells 2 → j ∈ orbitCells 2 →
        residualWord 2 i = residualWord 2 j → i = j := by
  native_decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem residualWord_injective_on_cell_3 :
    ∀ i j : Fin 189,
        i ∈ orbitCells 3 → j ∈ orbitCells 3 →
        residualWord 3 i = residualWord 3 j → i = j := by
  native_decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem residualWord_injective_on_cell_4 :
    ∀ i j : Fin 189,
        i ∈ orbitCells 4 → j ∈ orbitCells 4 →
        residualWord 4 i = residualWord 4 j → i = j := by
  native_decide

theorem residualWord_injective_on_cell_5 :
    ∀ i j : Fin 189,
        i ∈ orbitCells 5 → j ∈ orbitCells 5 →
        residualWord 5 i = residualWord 5 j → i = j := by
  intro i j hi hj h
  have hi' : i = 15 ∨ i = 17 ∨ i = 159 ∨ i = 160 := by
    simpa [orbitCells, flagCells] using hi
  have hj' : j = 15 ∨ j = 17 ∨ j = 159 ∨ j = 160 := by
    simpa [orbitCells, flagCells] using hj
  rcases hi' with rfl | rfl | rfl | rfl <;>
    rcases hj' with rfl | rfl | rfl | rfl
  all_goals try rfl
  all_goals
    exfalso
    exact (by decide) h

theorem residualWord_injective_on_cell_6 :
    ∀ i j : Fin 189,
        i ∈ orbitCells 6 → j ∈ orbitCells 6 →
        residualWord 6 i = residualWord 6 j → i = j := by
  intro i j hi hj h
  have hi' : i = 1 ∨ i = 2 := by
    simpa [orbitCells, flagCells] using hi
  have hj' : j = 1 ∨ j = 2 := by
    simpa [orbitCells, flagCells] using hj
  rcases hi' with rfl | rfl <;> rcases hj' with rfl | rfl
  · rfl
  · exfalso
    exact (show residualWord 6 1 ≠ residualWord 6 2 by decide) h
  · exfalso
    exact (show residualWord 6 2 ≠ residualWord 6 1 by decide) h
  · rfl

theorem residualWord_injective_on_cell_7 :
    ∀ i j : Fin 189,
        i ∈ orbitCells 7 → j ∈ orbitCells 7 →
        residualWord 7 i = residualWord 7 j → i = j := by
  intro i j hi hj h
  have hi' : i = 16 ∨ i = 161 := by
    simpa [orbitCells, flagCells] using hi
  have hj' : j = 16 ∨ j = 161 := by
    simpa [orbitCells, flagCells] using hj
  rcases hi' with rfl | rfl <;> rcases hj' with rfl | rfl
  · rfl
  · exfalso
    exact (show residualWord 7 16 ≠ residualWord 7 161 by decide) h
  · exfalso
    exact (show residualWord 7 161 ≠ residualWord 7 16 by decide) h
  · rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem residualWord_injective_on_cell_8 :
    ∀ i j : Fin 189,
        i ∈ orbitCells 8 → j ∈ orbitCells 8 →
        residualWord 8 i = residualWord 8 j → i = j := by
  native_decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem residualWord_injective_on_cell_9 :
    ∀ i j : Fin 189,
        i ∈ orbitCells 9 → j ∈ orbitCells 9 →
        residualWord 9 i = residualWord 9 j → i = j := by
  native_decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem residualWord_injective_on_cell_10 :
    ∀ i j : Fin 189,
        i ∈ orbitCells 10 → j ∈ orbitCells 10 →
        residualWord 10 i = residualWord 10 j → i = j := by
  native_decide

theorem residualWord_injective_on_cell_11 :
    ∀ i j : Fin 189,
        i ∈ orbitCells 11 → j ∈ orbitCells 11 →
        residualWord 11 i = residualWord 11 j → i = j := by
  intro i j hi hj h
  have hi' : i = 25 ∨ i = 26 ∨ i = 46 ∨ i = 47 ∨
      i = 72 ∨ i = 74 ∨ i = 177 ∨ i = 179 := by
    simpa [orbitCells, flagCells] using hi
  have hj' : j = 25 ∨ j = 26 ∨ j = 46 ∨ j = 47 ∨
      j = 72 ∨ j = 74 ∨ j = 177 ∨ j = 179 := by
    simpa [orbitCells, flagCells] using hj
  rcases hi' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try rfl
  all_goals
    exfalso
    exact (by decide) h

theorem residualWord_injective_on_cell (k : Fin 12) :
    ∀ i j : Fin 189,
        i ∈ orbitCells k → j ∈ orbitCells k →
        residualWord k i = residualWord k j → i = j := by
  fin_cases k
  · exact residualWord_injective_on_cell_0
  · exact residualWord_injective_on_cell_1
  · exact residualWord_injective_on_cell_2
  · exact residualWord_injective_on_cell_3
  · exact residualWord_injective_on_cell_4
  · exact residualWord_injective_on_cell_5
  · exact residualWord_injective_on_cell_6
  · exact residualWord_injective_on_cell_7
  · exact residualWord_injective_on_cell_8
  · exact residualWord_injective_on_cell_9
  · exact residualWord_injective_on_cell_10
  · exact residualWord_injective_on_cell_11

end InfoGeometry.Algebra.Zorn.G2QuotientResidualInjectivity
