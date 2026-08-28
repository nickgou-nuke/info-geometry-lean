import InfoGeometry.Exceptional.CircularSplitOctonionContactLift

/-! The circular mixed contact bracket readback into the existing zero-grade
operator and scale components. -/
namespace InfoGeometry.Exceptional.Freudenthal

noncomputable section

variable {J : Type*} [AddCommGroup J] [Module ℝ J]
variable (D : CubicJordanDatum J)

abbrev CircularZeroGrade (D : CubicJordanDatum J) :=
  SymplecticTKKZero D × ℝ

def circularZeroInject (z : CircularZeroGrade D) : FiveGradedCarrier D :=
  ⟨0, 0, z.1, z.2, 0, 0⟩

theorem circularZeroInject_injective :
    Function.Injective (circularZeroInject (D := D)) := by
  intro z w h
  apply Prod.ext
  · exact congrArg FiveGradedCarrier.zero_symp h
  · exact congrArg FiveGradedCarrier.zero_scale h

def circularZeroReadback
    (rootMapPlus rootMapMinus : Fin 3 → J)
    (a b : CircularChargeAtom) : CircularZeroGrade D :=
  (mixedSymplecticBracket D
      (circularCharge rootMapPlus rootMapMinus a)
      (circularCharge rootMapPlus rootMapMinus b),
    FreudenthalCharge.symplecticForm D
      (circularCharge rootMapPlus rootMapMinus a)
      (circularCharge rootMapPlus rootMapMinus b))

theorem circularZeroReadback_swap
    (rootMapPlus rootMapMinus : Fin 3 → J)
    (a b : CircularChargeAtom) :
    circularZeroReadback D rootMapPlus rootMapMinus b a =
      ((circularZeroReadback D rootMapPlus rootMapMinus a b).1,
        -(circularZeroReadback D rootMapPlus rootMapMinus a b).2) := by
  apply Prod.ext
  · exact mixedSymplecticBracket_swap D
      (circularCharge rootMapPlus rootMapMinus b)
      (circularCharge rootMapPlus rootMapMinus a)
  · change FreudenthalCharge.symplecticForm D
      (circularCharge rootMapPlus rootMapMinus b)
      (circularCharge rootMapPlus rootMapMinus a) =
      -FreudenthalCharge.symplecticForm D
        (circularCharge rootMapPlus rootMapMinus a)
        (circularCharge rootMapPlus rootMapMinus b)
    rw [FreudenthalCharge.symplectic_form_skew D
      (circularCharge rootMapPlus rootMapMinus a)
      (circularCharge rootMapPlus rootMapMinus b)]

theorem circular_mixed_bracket_eq_zeroGrade
    (rootMapPlus rootMapMinus : Fin 3 → J)
    (a b : CircularChargeAtom) :
    fiveGradedBracket D
        (toMinusOne D rootMapPlus rootMapMinus a)
      (toPlusOne D rootMapPlus rootMapMinus b) =
      circularZeroInject D (circularZeroReadback D rootMapPlus rootMapMinus a b) := by
  rw [circular_mixed_bracket_readback]
  apply FiveGradedCarrier.ext <;>
    simp [circularZeroInject, circularZeroReadback]

theorem circular_zeroGrade_scale_poles
    (rootMapPlus rootMapMinus : Fin 3 → J) :
    (circularZeroReadback D rootMapPlus rootMapMinus
      .plusPole .minusPole).2 = 1 := by
  exact omega_poles D

theorem circular_zeroGrade_scale_roots
    (rootMapPlus rootMapMinus : Fin 3 → J)
    (h_ortho : ∀ i j : Fin 3,
      D.traceBilin (rootMapPlus i) (rootMapMinus j) = if i = j then 1 else 0)
    (i j : Fin 3) :
    (circularZeroReadback D rootMapPlus rootMapMinus
      (.plusRoot i) (.minusRoot j)).2 = if i = j then 1 else 0 := by
  exact omega_roots D rootMapPlus rootMapMinus h_ortho i j

theorem circular_zeroGrade_scale_same_chirality
    (rootMapPlus rootMapMinus : Fin 3 → J) (i j : Fin 3) :
    (circularZeroReadback D rootMapPlus rootMapMinus
      (.plusRoot i) (.plusRoot j)).2 = 0 ∧
    (circularZeroReadback D rootMapPlus rootMapMinus
      (.minusRoot i) (.minusRoot j)).2 = 0 := by
  exact ⟨omega_roots_same_plus D rootMapPlus i j,
    omega_roots_same_minus D rootMapMinus i j⟩

theorem circular_zeroGrade_root_operator_plus
    (rootMapPlus rootMapMinus : Fin 3 → J)
    (h_ortho : ∀ i j : Fin 3,
      D.traceBilin (rootMapPlus i) (rootMapMinus j) = if i = j then 1 else 0)
    (i j k : Fin 3) :
    (mixedSymplecticBracket D
      (embedPlusRoot rootMapPlus i) (embedMinusRoot rootMapMinus j) :
        Module.End ℝ (FreudenthalCharge J)) (embedPlusRoot rootMapPlus k) =
      (-(if j = k then (1 : ℝ) else 0)) • embedPlusRoot rootMapPlus i := by
  simpa only [mixedSymplecticBracket_val] using
    rankTwo_roots_on_plus D rootMapPlus rootMapMinus h_ortho i j k

theorem circular_zeroGrade_root_operator_minus
    (rootMapPlus rootMapMinus : Fin 3 → J)
    (h_ortho : ∀ i j : Fin 3,
      D.traceBilin (rootMapPlus i) (rootMapMinus j) = if i = j then 1 else 0)
    (i j k : Fin 3) :
    (mixedSymplecticBracket D
      (embedPlusRoot rootMapPlus i) (embedMinusRoot rootMapMinus j) :
        Module.End ℝ (FreudenthalCharge J)) (embedMinusRoot rootMapMinus k) =
      (if i = k then (1 : ℝ) else 0) • embedMinusRoot rootMapMinus j := by
  simpa only [mixedSymplecticBracket_val] using
    rankTwo_roots_on_minus D rootMapPlus rootMapMinus h_ortho i j k

theorem circular_zeroGrade_pole_operator_plus
    :
    (mixedSymplecticBracket D embedPlusPole embedMinusPole :
        Module.End ℝ (FreudenthalCharge J)) embedPlusPole =
      -embedPlusPole := by
  simpa only [mixedSymplecticBracket_val] using
    rankTwo_pole_on_plus D

theorem circular_zeroGrade_pole_operator_minus
    :
    (mixedSymplecticBracket D embedPlusPole embedMinusPole :
        Module.End ℝ (FreudenthalCharge J)) embedMinusPole =
      embedMinusPole := by
  simpa only [mixedSymplecticBracket_val] using
    rankTwo_pole_on_minus D

theorem circular_zeroGrade_pole_operator_root_plus
    (rootMapPlus : Fin 3 → J) (i : Fin 3) :
    (mixedSymplecticBracket D embedPlusPole embedMinusPole :
        Module.End ℝ (FreudenthalCharge J))
      (embedPlusRoot rootMapPlus i) = 0 := by
  rw [mixedSymplecticBracket_val, symplecticRankTwo_apply]
  have h₁ : FreudenthalCharge.symplecticForm D embedMinusPole
      (embedPlusRoot rootMapPlus i) = 0 := by
    simp [FreudenthalCharge.symplecticForm, embedMinusPole, embedPlusRoot]
  have h₂ : FreudenthalCharge.symplecticForm D embedPlusPole
      (embedPlusRoot rootMapPlus i) = 0 :=
    omega_pole_root_plus D rootMapPlus i
  rw [h₁, h₂]
  simp

theorem circular_zeroGrade_pole_operator_root_minus
    (rootMapMinus : Fin 3 → J) (i : Fin 3) :
    (mixedSymplecticBracket D embedPlusPole embedMinusPole :
        Module.End ℝ (FreudenthalCharge J))
      (embedMinusRoot rootMapMinus i) = 0 := by
  rw [mixedSymplecticBracket_val, symplecticRankTwo_apply]
  have h₁ : FreudenthalCharge.symplecticForm D embedMinusPole
      (embedMinusRoot rootMapMinus i) = 0 :=
    omega_pole_root_minus D rootMapMinus i
  have h₂ : FreudenthalCharge.symplecticForm D embedPlusPole
      (embedMinusRoot rootMapMinus i) = 0 := by
    simp [FreudenthalCharge.symplecticForm, embedPlusPole, embedMinusRoot]
  rw [h₁, h₂]
  simp

theorem circular_mixed_reverse_zeroGrade_readback
    (rootMapPlus rootMapMinus : Fin 3 → J)
    (a b : CircularChargeAtom) :
    fiveGradedBracket D
        (toPlusOne D rootMapPlus rootMapMinus a)
        (toMinusOne D rootMapPlus rootMapMinus b) =
      circularZeroInject D
        (-(circularZeroReadback D rootMapPlus rootMapMinus b a).1,
          -(circularZeroReadback D rootMapPlus rootMapMinus b a).2) := by
  rw [fiveGradedBracket_skew]
  rw [circular_mixed_bracket_eq_zeroGrade]
  apply FiveGradedCarrier.ext <;>
    simp [circularZeroInject, circularZeroReadback,
      mixedSymplecticBracket_swap D]

theorem circular_zeroGrade_root_operator_pole_plus
    (rootMapPlus rootMapMinus : Fin 3 → J) (i : Fin 3) :
    (mixedSymplecticBracket D
      (embedPlusRoot rootMapPlus i) (embedMinusRoot rootMapMinus i) :
        Module.End ℝ (FreudenthalCharge J)) embedPlusPole = 0 := by
  rw [mixedSymplecticBracket_val, symplecticRankTwo_apply]
  simp [FreudenthalCharge.symplecticForm, embedPlusPole,
    embedPlusRoot, embedMinusRoot]

theorem circular_zeroGrade_root_operator_pole_minus
    (rootMapPlus rootMapMinus : Fin 3 → J) (i : Fin 3) :
    (mixedSymplecticBracket D
      (embedPlusRoot rootMapPlus i) (embedMinusRoot rootMapMinus i) :
        Module.End ℝ (FreudenthalCharge J)) embedMinusPole = 0 := by
  rw [mixedSymplecticBracket_val, symplecticRankTwo_apply]
  simp [FreudenthalCharge.symplecticForm, embedPlusRoot,
    embedMinusRoot, embedMinusPole]

end
end InfoGeometry.Exceptional.Freudenthal
