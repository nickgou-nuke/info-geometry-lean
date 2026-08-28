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

def circularZeroReadback
    (rootMapPlus rootMapMinus : Fin 3 → J)
    (a b : CircularChargeAtom) : CircularZeroGrade D :=
  (mixedSymplecticBracket D
      (circularCharge rootMapPlus rootMapMinus a)
      (circularCharge rootMapPlus rootMapMinus b),
    FreudenthalCharge.symplecticForm D
      (circularCharge rootMapPlus rootMapMinus a)
      (circularCharge rootMapPlus rootMapMinus b))

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

end
end InfoGeometry.Exceptional.Freudenthal
