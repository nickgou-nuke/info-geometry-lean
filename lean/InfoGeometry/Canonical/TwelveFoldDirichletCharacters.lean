import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.NumberTheory.LegendreSymbol.ZModChar
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic

/-!
# Dirichlet characters at level twelve

This file owns the multiplicative character table modulo `12`.  It is kept
separate from the additive `ZMod 12` character and from the operator spectrum:
the domain here is the unit group `(ZMod 12)ˣ` and the values are complex.

The two quadratic characters are obtained natively by changing level from
`4` and `3`; their product is the mixed level-twelve character.
-/

noncomputable section

namespace InfoGeometry.Canonical.TwelveFoldDirichlet

open MulChar

abbrev Character12 := DirichletCharacter ℂ 12

def chiMinus4 : Character12 :=
  (DirichletCharacter.changeLevel (by norm_num : 4 ∣ 12) ZMod.χ₄).ringHomComp
    (Int.castRingHom ℂ)

def chiMinus3 : Character12 :=
  (DirichletCharacter.changeLevel (by norm_num : 3 ∣ 12)
    (quadraticChar (ZMod 3))).ringHomComp (Int.castRingHom ℂ)

def chiTwelve : Character12 := chiMinus4 * chiMinus3

def chiMinus3AtLevelThree : DirichletCharacter ℂ 3 :=
  (quadraticChar (ZMod 3)).ringHomComp (Int.castRingHom ℂ)

def chiMinus4AtLevelFour : DirichletCharacter ℂ 4 :=
  ZMod.χ₄.ringHomComp (Int.castRingHom ℂ)

def unitOne : (ZMod 12)ˣ := ZMod.unitOfCoprime 1 (by norm_num)
def unitFive : (ZMod 12)ˣ := ZMod.unitOfCoprime 5 (by norm_num)
def unitSeven : (ZMod 12)ˣ := ZMod.unitOfCoprime 7 (by norm_num)
def unitEleven : (ZMod 12)ˣ := ZMod.unitOfCoprime 11 (by norm_num)

lemma unitOne_cast_four : ZMod.cast (R := ZMod 4) (unitOne : ZMod 12) = 1 := by
  change (1 : ZMod 4) = 1
  rfl

lemma unitFive_cast_four : ZMod.cast (R := ZMod 4) (unitFive : ZMod 12) = 1 := by
  change (5 : ZMod 4) = 1
  decide

lemma unitSeven_cast_four : ZMod.cast (R := ZMod 4) (unitSeven : ZMod 12) = 3 := by
  change (7 : ZMod 4) = 3
  decide

lemma unitEleven_cast_four : ZMod.cast (R := ZMod 4) (unitEleven : ZMod 12) = 3 := by
  change (11 : ZMod 4) = 3
  decide

lemma unitOne_cast_three : ZMod.cast (R := ZMod 3) (unitOne : ZMod 12) = 1 := by
  change (1 : ZMod 3) = 1
  rfl

lemma unitFive_cast_three : ZMod.cast (R := ZMod 3) (unitFive : ZMod 12) = 2 := by
  change (5 : ZMod 3) = 2
  decide

lemma unitSeven_cast_three : ZMod.cast (R := ZMod 3) (unitSeven : ZMod 12) = 1 := by
  change (7 : ZMod 3) = 1
  decide

lemma unitEleven_cast_three : ZMod.cast (R := ZMod 3) (unitEleven : ZMod 12) = 2 := by
  change (11 : ZMod 3) = 2
  decide

lemma unitFive_cast_two : ZMod.cast (R := ZMod 2) (unitFive : ZMod 12) = 1 := by
  change (5 : ZMod 2) = 1
  decide

lemma unitSeven_cast_two : ZMod.cast (R := ZMod 2) (unitSeven : ZMod 12) = 1 := by
  change (7 : ZMod 2) = 1
  decide

lemma unitOne_cast_one : ZMod.cast (R := ZMod 1) (unitOne : ZMod 12) = 0 := by
  change (1 : ZMod 1) = 0
  decide

lemma unitFive_cast_one : ZMod.cast (R := ZMod 1) (unitFive : ZMod 12) = 0 := by
  change (5 : ZMod 1) = 0
  decide

lemma unitOne_cast_two : ZMod.cast (R := ZMod 2) (unitOne : ZMod 12) = 1 := by
  change (1 : ZMod 2) = 1
  rfl

lemma unitOne_cast_six : ZMod.cast (R := ZMod 6) (unitOne : ZMod 12) = 1 := by
  change (1 : ZMod 6) = 1
  rfl

lemma unitSeven_cast_six : ZMod.cast (R := ZMod 6) (unitSeven : ZMod 12) = 1 := by
  change (7 : ZMod 6) = 1
  decide

lemma chiMinus4_unitOne : chiMinus4 (unitOne : ZMod 12) = 1 := by
  simp only [chiMinus4, ringHomComp_apply]
  rw [DirichletCharacter.changeLevel_eq_cast_of_dvd ZMod.χ₄ (by norm_num) unitOne]
  rw [unitOne_cast_four]
  norm_num

lemma chiMinus4_unitFive : chiMinus4 (unitFive : ZMod 12) = 1 := by
  simp only [chiMinus4, ringHomComp_apply]
  rw [DirichletCharacter.changeLevel_eq_cast_of_dvd ZMod.χ₄ (by norm_num) unitFive]
  rw [unitFive_cast_four]
  norm_num

lemma chiMinus4_unitSeven : chiMinus4 (unitSeven : ZMod 12) = -1 := by
  simp only [chiMinus4, ringHomComp_apply]
  rw [DirichletCharacter.changeLevel_eq_cast_of_dvd ZMod.χ₄ (by norm_num) unitSeven]
  rw [unitSeven_cast_four]
  change ((-1 : ℤ) : ℂ) = -1
  norm_num

lemma chiMinus4_unitEleven : chiMinus4 (unitEleven : ZMod 12) = -1 := by
  simp only [chiMinus4, ringHomComp_apply]
  rw [DirichletCharacter.changeLevel_eq_cast_of_dvd ZMod.χ₄ (by norm_num) unitEleven]
  rw [unitEleven_cast_four]
  change ((-1 : ℤ) : ℂ) = -1
  norm_num

lemma not_isSquare_two_zmod_three : ¬ IsSquare (2 : ZMod 3) := by
  intro h
  rcases h with ⟨x, hx⟩
  fin_cases x
  · exact (by decide : (2 : ZMod 3) ≠ 0) hx
  · exact (by decide : (2 : ZMod 3) ≠ 1) hx
  · change (2 : ZMod 3) = (2 : ZMod 3) ^ 2 at hx
    have hs : (2 : ZMod 3) ^ 2 = 1 := by decide
    have hneq : (2 : ZMod 3) ≠ 1 := by decide
    exact hneq (hs ▸ hx)

lemma chiMinus3_unitOne : chiMinus3 (unitOne : ZMod 12) = 1 := by
  simp only [chiMinus3, ringHomComp_apply]
  rw [DirichletCharacter.changeLevel_eq_cast_of_dvd (quadraticChar (ZMod 3))
    (by norm_num) unitOne]
  rw [unitOne_cast_three]
  norm_num [quadraticChar_apply, quadraticCharFun]

lemma chiMinus3_unitFive : chiMinus3 (unitFive : ZMod 12) = -1 := by
  simp only [chiMinus3, ringHomComp_apply]
  rw [DirichletCharacter.changeLevel_eq_cast_of_dvd (quadraticChar (ZMod 3))
    (by norm_num) unitFive]
  rw [unitFive_cast_three]
  have h2 : (2 : ZMod 3) ≠ 0 := by decide
  simp [quadraticChar_apply, quadraticCharFun, not_isSquare_two_zmod_three, h2]

lemma chiMinus3_unitSeven : chiMinus3 (unitSeven : ZMod 12) = 1 := by
  simp only [chiMinus3, ringHomComp_apply]
  rw [DirichletCharacter.changeLevel_eq_cast_of_dvd (quadraticChar (ZMod 3))
    (by norm_num) unitSeven]
  rw [unitSeven_cast_three]
  norm_num [quadraticChar_apply, quadraticCharFun]

lemma chiMinus3_unitEleven : chiMinus3 (unitEleven : ZMod 12) = -1 := by
  simp only [chiMinus3, ringHomComp_apply]
  rw [DirichletCharacter.changeLevel_eq_cast_of_dvd (quadraticChar (ZMod 3))
    (by norm_num) unitEleven]
  rw [unitEleven_cast_three]
  have h2 : (2 : ZMod 3) ≠ 0 := by decide
  simp [quadraticChar_apply, quadraticCharFun, not_isSquare_two_zmod_three, h2]

lemma chiTwelve_unitOne : chiTwelve (unitOne : ZMod 12) = 1 := by
  simp [chiTwelve, chiMinus4_unitOne, chiMinus3_unitOne]

lemma chiTwelve_unitFive : chiTwelve (unitFive : ZMod 12) = -1 := by
  simp [chiTwelve, chiMinus4_unitFive, chiMinus3_unitFive]

lemma chiTwelve_unitSeven : chiTwelve (unitSeven : ZMod 12) = -1 := by
  simp [chiTwelve, chiMinus4_unitSeven, chiMinus3_unitSeven]

lemma chiTwelve_unitEleven : chiTwelve (unitEleven : ZMod 12) = 1 := by
  simp [chiTwelve, chiMinus4_unitEleven, chiMinus3_unitEleven]

lemma chiTwelve_eq_product : chiTwelve = chiMinus4 * chiMinus3 := rfl

/-- The Dirichlet extension vanishes on every nonunit residue class. -/
lemma chiTwelve_nonunit (a : ZMod 12) (ha : ¬ IsUnit a) : chiTwelve a = 0 := by
  exact MulChar.map_nonunit chiTwelve ha

lemma chiMinus3_factorsThrough_three : chiMinus3.FactorsThrough 3 := by
  refine ⟨by norm_num, chiMinus3AtLevelThree, ?_⟩
  ext a
  simp [chiMinus3, chiMinus3AtLevelThree, DirichletCharacter.changeLevel,
    MulChar.ringHomComp]

lemma chiMinus3_conductor_dvd_three : chiMinus3.conductor ∣ 3 := by
  apply DirichletCharacter.conductor_dvd_of_mem_conductorSet chiMinus3 (by norm_num)
  change chiMinus3.FactorsThrough 3
  exact chiMinus3_factorsThrough_three

lemma chiMinus3_conductor_eq_three : chiMinus3.conductor = 3 := by
  have hd := chiMinus3_conductor_dvd_three
  have hpos : 0 < chiMinus3.conductor :=
    Nat.pos_of_ne_zero (DirichletCharacter.conductor_ne_zero chiMinus3 (by norm_num))
  have hne : chiMinus3 ≠ (1 : Character12) := by
    intro h
    have hv := congrArg (fun χ : Character12 => χ (unitFive : ZMod 12)) h
    dsimp at hv
    rw [chiMinus3_unitFive] at hv
    norm_num at hv
  have hc1 : chiMinus3.conductor ≠ 1 := by
    intro hc
    apply hne
    exact (DirichletCharacter.eq_one_iff_conductor_eq_one (χ := chiMinus3)
      (by norm_num)).2 hc
  rcases (Nat.dvd_prime (by norm_num : Nat.Prime 3)).mp hd with h | h
  · exact False.elim (hc1 h)
  · exact h

lemma chiMinus4_factorsThrough_four : chiMinus4.FactorsThrough 4 := by
  refine ⟨by norm_num, chiMinus4AtLevelFour, ?_⟩
  ext a
  simp [chiMinus4, chiMinus4AtLevelFour, DirichletCharacter.changeLevel,
    MulChar.ringHomComp]

lemma chiMinus4_conductor_dvd_four : chiMinus4.conductor ∣ 4 := by
  apply DirichletCharacter.conductor_dvd_of_mem_conductorSet chiMinus4 (by norm_num)
  change chiMinus4.FactorsThrough 4
  exact chiMinus4_factorsThrough_four

lemma chiMinus4_conductor_ne_two : chiMinus4.conductor ≠ 2 := by
  intro hc
  have hfac : chiMinus4.FactorsThrough 2 := by
    simpa [hc] using chiMinus4.factorsThrough_conductor
  obtain ⟨hdiv, χ₂, hχ⟩ := hfac
  have h5 := congrArg (fun χ : Character12 => χ (unitFive : ZMod 12)) hχ
  have h7 := congrArg (fun χ : Character12 => χ (unitSeven : ZMod 12)) hχ
  dsimp at h5 h7
  have h5' : (DirichletCharacter.changeLevel hdiv χ₂) (unitFive : ZMod 12) =
      χ₂ (1 : ZMod 2) := by
    rw [DirichletCharacter.changeLevel_eq_cast_of_dvd χ₂ hdiv unitFive]
    rw [unitFive_cast_two]
  have h7' : (DirichletCharacter.changeLevel hdiv χ₂) (unitSeven : ZMod 12) =
      χ₂ (1 : ZMod 2) := by
    rw [DirichletCharacter.changeLevel_eq_cast_of_dvd χ₂ hdiv unitSeven]
    rw [unitSeven_cast_two]
  rw [chiMinus4_unitFive, h5'] at h5
  rw [chiMinus4_unitSeven, h7'] at h7
  have : (1 : ℂ) = -1 := h5.trans h7.symm
  norm_num at this

lemma chiMinus4_conductor_eq_four : chiMinus4.conductor = 4 := by
  have hd := chiMinus4_conductor_dvd_four
  have hne1 : chiMinus4.conductor ≠ 1 := by
    intro hc
    have hne : chiMinus4 ≠ (1 : Character12) := by
      intro h
      have hv := congrArg (fun χ : Character12 => χ (unitSeven : ZMod 12)) h
      dsimp at hv
      rw [chiMinus4_unitSeven] at hv
      norm_num at hv
    apply hne
    exact (DirichletCharacter.eq_one_iff_conductor_eq_one (χ := chiMinus4)
      (by norm_num)).2 hc
  have hne2 := chiMinus4_conductor_ne_two
  have hle : chiMinus4.conductor ≤ 4 := Nat.le_of_dvd (by norm_num) hd
  interval_cases hcval : chiMinus4.conductor <;> simp_all

lemma factorsThrough_eval_eq {χ : Character12} {d : ℕ}
    (hχ : χ.FactorsThrough d) (a b : (ZMod 12)ˣ)
    (hab : ZMod.cast (R := ZMod d) (a : ZMod 12) =
      ZMod.cast (R := ZMod d) (b : ZMod 12)) :
    χ (a : ZMod 12) = χ (b : ZMod 12) := by
  obtain ⟨hd, χd, hχ⟩ := hχ
  have ha := congrArg (fun χ : Character12 => χ (a : ZMod 12)) hχ
  have hb := congrArg (fun χ : Character12 => χ (b : ZMod 12)) hχ
  dsimp at ha hb
  rw [DirichletCharacter.changeLevel_eq_cast_of_dvd χd hd a] at ha
  rw [DirichletCharacter.changeLevel_eq_cast_of_dvd χd hd b] at hb
  rw [hab] at ha
  exact ha.trans hb.symm

lemma chiTwelve_not_factorsThrough_one : ¬ chiTwelve.FactorsThrough 1 := by
  intro h
  have hv := factorsThrough_eval_eq h unitOne unitFive
    (unitOne_cast_one.trans unitFive_cast_one.symm)
  rw [chiTwelve_unitOne, chiTwelve_unitFive] at hv
  norm_num at hv

lemma chiTwelve_not_factorsThrough_two : ¬ chiTwelve.FactorsThrough 2 := by
  intro h
  have hv := factorsThrough_eval_eq h unitOne unitFive
    (unitOne_cast_two.trans unitFive_cast_two.symm)
  rw [chiTwelve_unitOne, chiTwelve_unitFive] at hv
  norm_num at hv

lemma chiTwelve_not_factorsThrough_three : ¬ chiTwelve.FactorsThrough 3 := by
  intro h
  have hv := factorsThrough_eval_eq h unitOne unitSeven
    (unitOne_cast_three.trans unitSeven_cast_three.symm)
  rw [chiTwelve_unitOne, chiTwelve_unitSeven] at hv
  norm_num at hv

lemma chiTwelve_not_factorsThrough_four : ¬ chiTwelve.FactorsThrough 4 := by
  intro h
  have hv := factorsThrough_eval_eq h unitOne unitFive
    (unitOne_cast_four.trans unitFive_cast_four.symm)
  rw [chiTwelve_unitOne, chiTwelve_unitFive] at hv
  norm_num at hv

lemma chiTwelve_not_factorsThrough_six : ¬ chiTwelve.FactorsThrough 6 := by
  intro h
  have hv := factorsThrough_eval_eq h unitOne unitSeven
    (unitOne_cast_six.trans unitSeven_cast_six.symm)
  rw [chiTwelve_unitOne, chiTwelve_unitSeven] at hv
  norm_num at hv

lemma chiTwelve_conductor_eq_twelve : chiTwelve.conductor = 12 := by
  have hd := chiTwelve.conductor_dvd_level
  have hne0 := chiTwelve.conductor_ne_zero (by norm_num)
  have hne1 : chiTwelve.conductor ≠ 1 := by
    intro hc
    apply chiTwelve_not_factorsThrough_one
    simpa [hc] using chiTwelve.factorsThrough_conductor
  have hne2 : chiTwelve.conductor ≠ 2 := by
    intro hc
    apply chiTwelve_not_factorsThrough_two
    simpa [hc] using chiTwelve.factorsThrough_conductor
  have hne3 : chiTwelve.conductor ≠ 3 := by
    intro hc
    apply chiTwelve_not_factorsThrough_three
    simpa [hc] using chiTwelve.factorsThrough_conductor
  have hne4 : chiTwelve.conductor ≠ 4 := by
    intro hc
    apply chiTwelve_not_factorsThrough_four
    simpa [hc] using chiTwelve.factorsThrough_conductor
  have hne6 : chiTwelve.conductor ≠ 6 := by
    intro hc
    apply chiTwelve_not_factorsThrough_six
    simpa [hc] using chiTwelve.factorsThrough_conductor
  have hle : chiTwelve.conductor ≤ 12 := Nat.le_of_dvd (by norm_num) hd
  interval_cases hcval : chiTwelve.conductor <;> simp_all

end InfoGeometry.Canonical.TwelveFoldDirichlet
