import InfoGeometry.Exceptional.FreudenthalFiveGradedLieClosure

/-!
# Coordinate sector membership for the Freudenthal five-grade carrier

This owner turns the existing sector injections into explicit membership
predicates.  It proves only the three corresponding bracket-closure cases;
it does not install a full Lie-algebra instance or identify a physical model.
-/

noncomputable section

namespace InfoGeometry.Exceptional.Freudenthal

variable {J : Type*} [AddCommGroup J] [Module ℝ J]
variable (D : CubicJordanDatum J)

def InMinusTwo (u : FiveGradedCarrier D) : Prop :=
  u.minus1 = 0 ∧ u.zero_symp = 0 ∧ u.zero_scale = 0 ∧ u.plus1 = 0 ∧ u.plus2 = 0

def InZero (u : FiveGradedCarrier D) : Prop :=
  u.minus2 = 0 ∧ u.minus1 = 0 ∧ u.plus1 = 0 ∧ u.plus2 = 0

def InPlusTwo (u : FiveGradedCarrier D) : Prop :=
  u.minus2 = 0 ∧ u.minus1 = 0 ∧ u.zero_symp = 0 ∧ u.zero_scale = 0 ∧ u.plus1 = 0

theorem inj_minus_mem (x : FreudenthalCharge J) : InMinusTwo D (genEminus D x) := by
  simp [InMinusTwo, genEminus]

theorem inj_zero_mem (T : SymplecticTKKZero D) (h : ℝ) :
    InZero D ⟨0, 0, T, h, 0, 0⟩ := by
  simp [InZero]

theorem inj_plus_mem (x : FreudenthalCharge J) : InPlusTwo D (genEplus D x) := by
  simp [InPlusTwo, genEplus]

theorem bracket_minus_one_closure (x y : FreudenthalCharge J) :
    InMinusTwo D
      (fiveGradedBracket D (injChargeMinus D x) (injChargeMinus D y)) := by
  rw [fiveGradedBracket_chargeMinus_chargeMinus]
  simp [InMinusTwo]

theorem bracket_plus_one_closure (x y : FreudenthalCharge J) :
    InPlusTwo D
      (fiveGradedBracket D (injChargePlus D x) (injChargePlus D y)) := by
  rw [fiveGradedBracket_chargePlus_chargePlus]
  simp [InPlusTwo]

theorem bracket_mixed_closure (x y : FreudenthalCharge J) :
    InZero D
      (fiveGradedBracket D (injChargeMinus D x) (injChargePlus D y)) := by
  rw [fiveGradedBracket_chargeMinus_chargePlus]
  simp [InZero]

end InfoGeometry.Exceptional.Freudenthal
