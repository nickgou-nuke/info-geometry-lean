import proofs.SplitOctonionChiralClosure
import proofs.TwoSheetChiralTKKDerivations

/-!
# The one-sheet Jordan algebra and its TKK bridge

The positive Peirce sheet is closed under the symmetrized Zorn product, but
not under either raw Zorn multiplication or its commutator.  This file proves
its Jordan identity directly from its coordinate formula and embeds the sheet
in the concrete five-graded matrix envelope.  The resulting Jordan-pair
triple operator is exactly the adjoint action of the mixed grade-zero bracket.
-/

noncomputable section

namespace OneSheetChiralAlgebra

open SplitOctonionChiralClosure
open CanonicalZornFiveGradedClosure
open TKKJordanPairData TKKJordanPairData.TKKGrade

abbrev Zorn := SplitOctonionChiralClosure.Zorn
abbrev Vec3 := SplitOctonionChiralClosure.Vec3
abbrev L := CanonicalZornFiveGradedClosure.ConformalMatrix

/-- `W₊ = span {u₊, σ₁⁺, σ₂⁺, σ₃⁺}`. -/
def oneSheet (a : ℂ) (u : Vec3) : Zorn :=
  add (smul a uPlus) (sigmaPlus u)

/-- Normalized symmetrized Zorn product. -/
def jordan (X Y : Zorn) : Zorn := smul (1 / 2) (antiComm X Y)

def lie (X Y : Zorn) : Zorn := comm X Y

def assoc (X Y Z : Zorn) : Zorn :=
  sub (mul (mul X Y) Z) (mul X (mul Y Z))

/-- The positive sheet is closed under the Jordan product. -/
theorem oneSheet_jordan_formula (a b : ℂ) (u v : Vec3) :
    jordan (oneSheet a u) (oneSheet b v) =
      oneSheet (a * b) (fun i => (a * v i + b * u i) / 2) := by
  apply SplitOctonionBraidSU3.zorn_ext
  · simp [jordan, oneSheet, antiComm, mul, add, smul,
      SplitOctonionBraidSU3.zornMul, SplitOctonionBraidSU3.zornAdd,
      SplitOctonionBraidSU3.zornSmul, SplitOctonionBraidSU3.dot3,
      uPlus, sigmaPlus]
    ring
  · funext i
    simp [jordan, oneSheet, antiComm, mul, add, smul,
      SplitOctonionBraidSU3.zornMul, SplitOctonionBraidSU3.zornAdd,
      SplitOctonionBraidSU3.zornSmul, uPlus, sigmaPlus]
    fin_cases i <;> simp [SplitOctonionBraidSU3.cross3] <;> ring
  · funext i
    simp [jordan, oneSheet, antiComm, mul, add, smul,
      SplitOctonionBraidSU3.zornMul, SplitOctonionBraidSU3.zornAdd,
      SplitOctonionBraidSU3.zornSmul, uPlus, sigmaPlus,
      SplitOctonionBraidSU3.cross3]
    fin_cases i <;> simp <;> ring
  · simp [jordan, oneSheet, antiComm, mul, add, smul,
      SplitOctonionBraidSU3.zornMul, SplitOctonionBraidSU3.zornAdd,
      SplitOctonionBraidSU3.zornSmul, SplitOctonionBraidSU3.dot3,
      uPlus, sigmaPlus]

/-- Kernel-checked Jordan identity on the complete four-dimensional sheet. -/
theorem oneSheet_jordan_identity (a b : ℂ) (u v : Vec3) :
    jordan
        (jordan (oneSheet a u) (oneSheet a u))
        (jordan (oneSheet a u) (oneSheet b v)) =
      jordan (oneSheet a u)
        (jordan
          (jordan (oneSheet a u) (oneSheet a u))
          (oneSheet b v)) := by
  rw [oneSheet_jordan_formula, oneSheet_jordan_formula,
    oneSheet_jordan_formula, oneSheet_jordan_formula,
    oneSheet_jordan_formula]
  apply SplitOctonionBraidSU3.zorn_ext
  · simp [oneSheet, add, smul, uPlus, sigmaPlus,
      SplitOctonionBraidSU3.zornAdd, SplitOctonionBraidSU3.zornSmul]
    ring
  · funext i
    simp [oneSheet, add, smul, uPlus, sigmaPlus,
      SplitOctonionBraidSU3.zornAdd, SplitOctonionBraidSU3.zornSmul]
    ring
  · funext i
    simp [oneSheet, add, smul, uPlus, sigmaPlus,
      SplitOctonionBraidSU3.zornAdd, SplitOctonionBraidSU3.zornSmul]
  · simp [oneSheet, add, smul, uPlus, sigmaPlus,
      SplitOctonionBraidSU3.zornAdd, SplitOctonionBraidSU3.zornSmul]

/-- The raw commutator of two positive colours exits into the minus sheet. -/
theorem oneSheet_lie_escape :
    lie (sigmaPlus (axis 0)) (sigmaPlus (axis 1)) =
      smul 2 (sigmaMinus (axis 2)) := by
  rw [show lie (sigmaPlus (axis 0)) (sigmaPlus (axis 1)) =
      comm (sigmaPlus (axis 0)) (sigmaPlus (axis 1)) from rfl,
    plus_plus_comm]
  congr 2
  funext i
  fin_cases i <;> simp [cross, axis, SplitOctonionBraidSU3.cross3]

/-- A concrete associator escaping to the opposite Peirce sheet. -/
theorem oneSheet_associator_witness :
    assoc (sigmaPlus (axis 0)) (sigmaPlus (axis 1)) uPlus =
      sigmaMinus (axis 2) := by
  apply SplitOctonionBraidSU3.zorn_ext
  all_goals
    simp [assoc, mul, sub, uPlus, sigmaPlus, sigmaMinus, axis,
      SplitOctonionBraidSU3.zornMul, SplitOctonionBraidSU3.zornSub,
      SplitOctonionBraidSU3.dot3, SplitOctonionBraidSU3.cross3]
  · funext i
    fin_cases i <;> simp [axis, SplitOctonionBraidSU3.cross3]
  · funext i
    fin_cases i <;> simp [axis, SplitOctonionBraidSU3.cross3]

/-! ## Explicit bridge into the verified five-graded TKK envelope -/

def positive (X : Zorn) : L := zornPositive X
def negative (X : Zorn) : L := zornNegative X

/-- Mixed positive/negative brackets are the degree-zero operators. -/
def derived (X Y : Zorn) : L := ⁅negative Y, positive X⁆

theorem oneSheet_tkk_grades (a b : ℂ) (u v : Vec3) :
    positive (oneSheet a u) ∈ conformalGrade p1 ∧
    negative (oneSheet b v) ∈ conformalGrade m1 ∧
    derived (oneSheet a u) (oneSheet b v) ∈ conformalGrade z0 := by
  exact ⟨zornPositive_mem _, zornNegative_mem _,
    zorn_mixed_bracket_mem_grade_zero _ _⟩

/-- The Jordan-pair triple operator in the positive TKK sector. -/
def tkkTriple (X Y Z : Zorn) : L :=
  ⁅⁅positive X, negative Y⁆, positive Z⁆

/-- The triple operator is precisely (up to the forced bracket orientation)
the adjoint action of the verified degree-zero derived matrix. -/
theorem tkkTriple_eq_derived_action (X Y Z : Zorn) :
    tkkTriple X Y Z =
      -TwoSheetChiralTKKDerivations.innerAction
        (TwoSheetChiralTKKDerivations.D Y X) (positive Z) := by
  change ⁅⁅zornPositive X, zornNegative Y⁆, zornPositive Z⁆ =
    -⁅⁅zornNegative Y, zornPositive X⁆, zornPositive Z⁆
  calc
    ⁅⁅zornPositive X, zornNegative Y⁆, zornPositive Z⁆ =
        ⁅-⁅zornNegative Y, zornPositive X⁆, zornPositive Z⁆ := by
          congr 1
          exact (lie_skew (x := zornPositive X) (y := zornNegative Y)).symm
    _ = -⁅⁅zornNegative Y, zornPositive X⁆, zornPositive Z⁆ := by simp

theorem oneSheet_tkkTriple_mem (a b c : ℂ) (u v w : Vec3) :
    tkkTriple (oneSheet a u) (oneSheet b v) (oneSheet c w) ∈
      conformalGrade p1 := by
  rw [tkkTriple_eq_derived_action]
  exact Submodule.neg_mem _
    (TwoSheetChiralTKKDerivations.D_action_closed
      (oneSheet b v) (oneSheet a u) p1 (positive (oneSheet c w))
      (zornPositive_mem _))

theorem oneSheet_tkk_bridge_synthesis (a b c : ℂ) (u v w : Vec3) :
    jordan (oneSheet a u) (oneSheet b v) =
        oneSheet (a * b) (fun i => (a * v i + b * u i) / 2) ∧
    derived (oneSheet a u) (oneSheet b v) ∈ conformalGrade z0 ∧
    tkkTriple (oneSheet a u) (oneSheet b v) (oneSheet c w) =
      -TwoSheetChiralTKKDerivations.innerAction
        (TwoSheetChiralTKKDerivations.D (oneSheet b v) (oneSheet a u))
        (positive (oneSheet c w)) ∧
    tkkTriple (oneSheet a u) (oneSheet b v) (oneSheet c w) ∈
      conformalGrade p1 := by
  exact ⟨oneSheet_jordan_formula _ _ _ _,
    zorn_mixed_bracket_mem_grade_zero _ _,
    tkkTriple_eq_derived_action _ _ _, oneSheet_tkkTriple_mem _ _ _ _ _ _⟩

end OneSheetChiralAlgebra

end noncomputable section
