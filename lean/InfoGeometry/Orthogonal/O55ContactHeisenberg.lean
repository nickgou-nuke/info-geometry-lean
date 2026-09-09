import InfoGeometry.Orthogonal.O55ContactGrading

/-! Finite Heisenberg-sector carrier for the `(5,5)` contact grading. -/

noncomputable section
namespace InfoGeometry.Orthogonal.O55Contact

def IsVectorWeight (k : ℤ) (x : Vector55) : Prop :=
  ∀ i, contactEulerEnd x i = (k : ℝ) * x i

def splitRankTwoEnd (u v : Vector55) : End55 where
  toFun x := splitPairing v x • u - splitPairing u x • v
  map_add' x y := by
    ext i
    simp [splitPairing_add_right]
    ring
  map_smul' c x := by
    ext i
    simp [splitPairing_smul_right]
    ring

def splitRankTwo (u v : Vector55) : O55Lie :=
  ⟨splitRankTwoEnd u v, by
    intro x y
    simp [splitRankTwoEnd, splitPairing_comm]
    ring⟩

@[simp] theorem splitRankTwoEnd_apply (u v x : Vector55) :
  splitRankTwoEnd u v x = splitPairing v x • u - splitPairing u x • v := rfl

theorem splitRankTwo_grade
    {a b : ℤ} {u v : Vector55}
    (hu : IsVectorWeight a u)
    (hv : IsVectorWeight b v) :
    splitRankTwo u v ∈ realContactGradeSpace (a + b) := by
  unfold IsVectorWeight at hu hv
  change endCommutator contactEulerEnd (splitRankTwoEnd u v) =
    ((a + b : ℤ) : ℝ) • splitRankTwoEnd u v
  apply LinearMap.ext
  intro x
  have hu' : contactEulerEnd u = (a : ℝ) • u := by
    funext i
    simpa using hu i
  have hv' : contactEulerEnd v = (b : ℝ) • v := by
    funext i
    simpa using hv i
  have hBu : splitPairing u (contactEulerEnd x) =
      -(a : ℝ) * splitPairing u x := by
    have h := contactEuler_isSplitSkew u x
    rw [hu', splitPairing_smul_left] at h
    linarith
  have hBv : splitPairing v (contactEulerEnd x) =
      -(b : ℝ) * splitPairing v x := by
    have h := contactEuler_isSplitSkew v x
    rw [hv', splitPairing_smul_left] at h
    linarith
  simp only [endCommutator_apply, splitRankTwoEnd_apply,
    map_sub, map_smul, hu', hv', hBu, hBv, Int.cast_add,
    LinearMap.smul_apply, smul_sub, smul_smul]
  module

theorem splitRankTwo_bracket (u v w z : Vector55) :
    ⁅splitRankTwo u v, splitRankTwo w z⁆ =
      splitPairing v w • splitRankTwo u z -
      splitPairing u w • splitRankTwo v z -
      splitPairing v z • splitRankTwo u w +
      splitPairing u z • splitRankTwo v w := by
  apply Subtype.ext
  apply LinearMap.ext
  intro x
  change (splitRankTwoEnd u v (splitRankTwoEnd w z x) -
      splitRankTwoEnd w z (splitRankTwoEnd u v x)) = _
  simp [splitRankTwo, splitRankTwoEnd]
  rw [splitPairing_comm z u, splitPairing_comm z v,
    splitPairing_comm w u, splitPairing_comm w v]
  module

abbrev Outer2 := Fin 2 → ℝ
abbrev Middle6 := Fin 6 → ℝ

def outerPairing (a b : Outer2) : ℝ := a 0 * b 0 + a 1 * b 1
def outerArea (a b : Outer2) : ℝ := a 0 * b 1 - a 1 * b 0
def middlePairing (w z : Middle6) : ℝ :=
  w 0 * z 0 + w 1 * z 1 + w 2 * z 2 -
    w 3 * z 3 - w 4 * z 4 - w 5 * z 5

def embedOuterMinus (a : Outer2) : Vector55 :=
  ![a 0, a 1, 0, 0, 0, 0, 0, 0, 0, 0]
def embedMiddle (w : Middle6) : Vector55 :=
  ![0, 0, w 0, w 1, w 2, w 3, w 4, w 5, 0, 0]
def embedOuterPlus (a : Outer2) : Vector55 :=
  ![0, 0, 0, 0, 0, 0, 0, 0, a 0, a 1]

@[simp] theorem pairing_outerMinus_outerMinus (a b : Outer2) :
    splitPairing (embedOuterMinus a) (embedOuterMinus b) = 0 := by
  simp [splitPairing, embedOuterMinus]
@[simp] theorem pairing_outerPlus_outerPlus (a b : Outer2) :
    splitPairing (embedOuterPlus a) (embedOuterPlus b) = 0 := by
  simp [splitPairing, embedOuterPlus]
@[simp] theorem pairing_outerMinus_outerPlus (a b : Outer2) :
    splitPairing (embedOuterMinus a) (embedOuterPlus b) = outerPairing a b := by
  simp [splitPairing, embedOuterMinus, embedOuterPlus, outerPairing]
@[simp] theorem pairing_outerPlus_outerMinus (a b : Outer2) :
    splitPairing (embedOuterPlus a) (embedOuterMinus b) = outerPairing a b := by
  simp [splitPairing, embedOuterMinus, embedOuterPlus, outerPairing]
@[simp] theorem pairing_middle_middle (w z : Middle6) :
    splitPairing (embedMiddle w) (embedMiddle z) = middlePairing w z := by
  simp [splitPairing, embedMiddle, middlePairing]
@[simp] theorem pairing_outerMinus_middle (a : Outer2) (w : Middle6) :
    splitPairing (embedOuterMinus a) (embedMiddle w) = 0 := by
  simp [splitPairing, embedOuterMinus, embedMiddle]
@[simp] theorem pairing_outerPlus_middle (a : Outer2) (w : Middle6) :
    splitPairing (embedOuterPlus a) (embedMiddle w) = 0 := by
  simp [splitPairing, embedOuterPlus, embedMiddle]

theorem embedded_weight_packet :
    (∀ a : Outer2, IsVectorWeight (-1) (embedOuterMinus a)) ∧
      (∀ w : Middle6, IsVectorWeight 0 (embedMiddle w)) ∧
      (∀ a : Outer2, IsVectorWeight 1 (embedOuterPlus a)) := by
  constructor
  · intro a i
    fin_cases i <;> simp [IsVectorWeight, contactEulerEnd, contactWeightR,
      contactWeight, embedOuterMinus]
  constructor
  · intro w i
    fin_cases i <;> simp [IsVectorWeight, contactEulerEnd, contactWeightR,
      contactWeight, embedMiddle]
  · intro a i
    fin_cases i <;> simp [IsVectorWeight, contactEulerEnd, contactWeightR,
      contactWeight, embedOuterPlus]

end InfoGeometry.Orthogonal.O55Contact
