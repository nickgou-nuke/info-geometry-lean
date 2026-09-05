import InfoGeometry.Orthogonal.O55TwoBoundarySelection

/-!
# Five Witt pairs and the full grading label

The contact decomposition `2 + 6 + 2` and the split-signature decomposition
`5 + 5` are distinct structures on the same ten-dimensional carrier.  Five
normalized hyperbolic pairs are constructed explicitly, with an exact
synthesis formula.
-/

noncomputable section

namespace InfoGeometry.Orthogonal.O55Contact

def wittPlus : Fin 5 → Vector55 :=
  ![coordinateVector 0,
    coordinateVector 1,
    coordinateVector 2 + coordinateVector 5,
    coordinateVector 3 + coordinateVector 6,
    coordinateVector 4 + coordinateVector 7]

def wittMinus : Fin 5 → Vector55 :=
  ![coordinateVector 8,
    coordinateVector 9,
    (1 / 2 : ℝ) • (coordinateVector 2 - coordinateVector 5),
    (1 / 2 : ℝ) • (coordinateVector 3 - coordinateVector 6),
    (1 / 2 : ℝ) • (coordinateVector 4 - coordinateVector 7)]

@[simp] theorem wittPlus_null (i : Fin 5) :
    splitPairing (wittPlus i) (wittPlus i) = 0 := by
  fin_cases i <;> norm_num [wittPlus, splitPairing, coordinateVector]

@[simp] theorem wittMinus_null (i : Fin 5) :
    splitPairing (wittMinus i) (wittMinus i) = 0 := by
  fin_cases i <;>
    norm_num [wittMinus, splitPairing, coordinateVector] <;> ring

@[simp] theorem wittPlus_wittMinus (i j : Fin 5) :
    splitPairing (wittPlus i) (wittMinus j) = if i = j then 1 else 0 := by
  fin_cases i <;> fin_cases j <;>
    norm_num [wittPlus, wittMinus, splitPairing, coordinateVector] <;> ring

@[simp] theorem wittPlus_pairing (i j : Fin 5) :
    splitPairing (wittPlus i) (wittPlus j) = 0 := by
  fin_cases i <;> fin_cases j <;>
    norm_num [wittPlus, splitPairing, coordinateVector]

@[simp] theorem wittMinus_pairing (i j : Fin 5) :
    splitPairing (wittMinus i) (wittMinus j) = 0 := by
  fin_cases i <;> fin_cases j <;>
    norm_num [wittMinus, splitPairing, coordinateVector] <;> ring

def wittPlusCoefficient (x : Vector55) : Fin 5 → ℝ :=
  ![x 0, x 1,
    (x 2 + x 5) / 2,
    (x 3 + x 6) / 2,
    (x 4 + x 7) / 2]

def wittMinusCoefficient (x : Vector55) : Fin 5 → ℝ :=
  ![x 8, x 9,
    x 2 - x 5,
    x 3 - x 6,
    x 4 - x 7]

def wittSynthesis (a b : Fin 5 → ℝ) : Vector55 :=
  ∑ i : Fin 5, a i • wittPlus i + b i • wittMinus i

theorem witt_reconstruction (x : Vector55) :
    wittSynthesis (wittPlusCoefficient x) (wittMinusCoefficient x) = x := by
  funext j
  fin_cases j <;>
    simp [wittSynthesis, wittPlusCoefficient, wittMinusCoefficient,
      wittPlus, wittMinus, coordinateVector, Fin.sum_univ_succ] <;> ring

theorem wittPlusCoefficient_eq_pairing (x : Vector55) (i : Fin 5) :
    wittPlusCoefficient x i = splitPairing x (wittMinus i) := by
  fin_cases i <;>
    simp [wittPlusCoefficient, wittMinus, splitPairing,
      coordinateVector] <;> ring

theorem wittMinusCoefficient_eq_pairing (x : Vector55) (i : Fin 5) :
    wittMinusCoefficient x i = splitPairing x (wittPlus i) := by
  fin_cases i <;>
    simp [wittMinusCoefficient, wittPlus, splitPairing,
      coordinateVector] <;> ring

structure WittSheetLabel where
  index : Fin 5
  positive : Bool
  deriving DecidableEq, Repr

def WittSheetLabel.vector (q : WittSheetLabel) : Vector55 :=
  if q.positive then wittPlus q.index else wittMinus q.index

def WittSheetLabel.swap (q : WittSheetLabel) : WittSheetLabel :=
  ⟨q.index, !q.positive⟩

@[simp] theorem WittSheetLabel.swap_swap (q : WittSheetLabel) :
    q.swap.swap = q := by
  cases q
  simp [WittSheetLabel.swap]

structure FullMultiGrade where
  contact : ℤ
  parity : ZMod 2
  parity_eq : parity = (contact : ZMod 2)
  witt : Fin 5
  positiveSheet : Bool

def FullMultiGrade.opposite (d : FullMultiGrade) : FullMultiGrade where
  contact := -d.contact
  parity := d.parity
  parity_eq := by
    rw [d.parity_eq]
    change (d.contact : ZMod 2) = -((d.contact : ZMod 2))
    ring
  witt := d.witt
  positiveSheet := !d.positiveSheet

@[simp] theorem FullMultiGrade.opposite_opposite (d : FullMultiGrade) :
    d.opposite.opposite = d := by
  cases d
  apply FullMultiGrade.ext <;> simp [FullMultiGrade.opposite]

theorem full_multigrading_packet (x : Vector55) :
    wittSynthesis (wittPlusCoefficient x) (wittMinusCoefficient x) = x ∧
      (∀ i : Fin 5, splitPairing (wittPlus i) (wittPlus i) = 0) ∧
      (∀ i : Fin 5, splitPairing (wittMinus i) (wittMinus i) = 0) ∧
      (∀ i : Fin 5, splitPairing (wittPlus i) (wittMinus i) = 1) := by
  exact ⟨witt_reconstruction x, wittPlus_null,
    wittMinus_null, fun i => by simp⟩

end InfoGeometry.Orthogonal.O55Contact
