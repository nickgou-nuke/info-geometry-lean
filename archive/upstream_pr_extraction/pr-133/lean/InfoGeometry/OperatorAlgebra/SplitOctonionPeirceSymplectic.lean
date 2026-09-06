import InfoGeometry.OperatorAlgebra.SplitOctonionSymplecticFoundation

/-!
# The native Peirce polarized carrier

This owner records the honest finite-dimensional bridge suggested by the
`up`/`down` Zorn slots.  It uses two explicit three-coordinate integer
vectors; it does not identify this carrier with a Hilbert space, a twistor
space, or a modular-flow representation.
-/

namespace InfoGeometry.OperatorAlgebra.SplitOctonions.PeirceSymplectic

open InfoGeometry.OperatorAlgebra.SplitOctonions.Multiplication

abbrev Vector3 := Fin 3 → ℤ

@[ext]
structure Carrier where
  plus : Vector3
  minus : Vector3
  deriving DecidableEq

def addCarrier (X Y : Carrier) : Carrier :=
  ⟨fun i => X.plus i + Y.plus i, fun i => X.minus i + Y.minus i⟩

instance : Add Carrier where
  add := addCarrier

instance : Zero Carrier where
  zero := ⟨0, 0⟩

def pairing (X Y : Carrier) : ℤ :=
  ∑ i, (X.plus i * Y.minus i - Y.plus i * X.minus i)

theorem pairing_add_left (X Y Z : Carrier) :
    pairing (X + Y) Z = pairing X Z + pairing Y Z := by
  change (∑ i, ((X.plus i + Y.plus i) * Z.minus i -
      Z.plus i * (X.minus i + Y.minus i))) =
    (∑ i, (X.plus i * Z.minus i - Z.plus i * X.minus i)) +
      ∑ i, (Y.plus i * Z.minus i - Z.plus i * Y.minus i)
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem pairing_add_right (X Y Z : Carrier) :
    pairing X (Y + Z) = pairing X Y + pairing X Z := by
  change (∑ i, (X.plus i * (Y.minus i + Z.minus i) -
      (Y.plus i + Z.plus i) * X.minus i)) =
    (∑ i, (X.plus i * Y.minus i - Y.plus i * X.minus i)) +
      ∑ i, (X.plus i * Z.minus i - Z.plus i * X.minus i)
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  ring

def plusCoordinates (X : SplitOct) : Vector3
  | 0 => X.x0
  | 1 => X.x1
  | 2 => X.x2

def minusCoordinates (X : SplitOct) : Vector3
  | 0 => X.y0
  | 1 => X.y1
  | 2 => X.y2

def coordinates (X : SplitOct) : Carrier :=
  ⟨plusCoordinates X, minusCoordinates X⟩

def basisVector (i : Fin 3) : Vector3 :=
  fun j => if j = i then 1 else 0

theorem plusCoordinates_up (i : Fin 3) :
    plusCoordinates (up i) = basisVector i := by
  fin_cases i <;> funext j <;> fin_cases j <;> rfl

theorem minusCoordinates_down (i : Fin 3) :
    minusCoordinates (down i) = basisVector i := by
  fin_cases i <;> funext j <;> fin_cases j <;> rfl

theorem plusCoordinates_down (i : Fin 3) :
    plusCoordinates (down i) = 0 := by
  fin_cases i <;> funext j <;> fin_cases j <;> rfl

theorem minusCoordinates_up (i : Fin 3) :
    minusCoordinates (up i) = 0 := by
  fin_cases i <;> funext j <;> fin_cases j <;> rfl

theorem pairing_coordinates_up_down (i j : Fin 3) :
    pairing (coordinates (up i)) (coordinates (down j)) =
      if i = j then 1 else 0 := by
  rw [show coordinates (up i) = ⟨basisVector i, 0⟩ by
        simp [coordinates, plusCoordinates_up, minusCoordinates_up],
      show coordinates (down j) = ⟨0, basisVector j⟩ by
        simp [coordinates, plusCoordinates_down, minusCoordinates_down]]
  by_cases h : i = j <;> simp [pairing, basisVector, h, eq_comm]

theorem pairing_coordinates_down_up (i j : Fin 3) :
    pairing (coordinates (down i)) (coordinates (up j)) =
      if i = j then -1 else 0 := by
  rw [show coordinates (down i) = ⟨0, basisVector i⟩ by
        simp [coordinates, plusCoordinates_down, minusCoordinates_down],
      show coordinates (up j) = ⟨basisVector j, 0⟩ by
        simp [coordinates, plusCoordinates_up, minusCoordinates_up]]
  by_cases h : i = j <;> simp [pairing, basisVector, h, eq_comm]

theorem pairing_coordinates_up_up (i j : Fin 3) :
    pairing (coordinates (up i)) (coordinates (up j)) = 0 := by
  rw [show coordinates (up i) = ⟨basisVector i, 0⟩ by
        simp [coordinates, plusCoordinates_up, minusCoordinates_up],
      show coordinates (up j) = ⟨basisVector j, 0⟩ by
        simp [coordinates, plusCoordinates_up, minusCoordinates_up]]
  simp [pairing]

theorem pairing_coordinates_down_down (i j : Fin 3) :
    pairing (coordinates (down i)) (coordinates (down j)) = 0 := by
  rw [show coordinates (down i) = ⟨0, basisVector i⟩ by
        simp [coordinates, plusCoordinates_down, minusCoordinates_down],
      show coordinates (down j) = ⟨0, basisVector j⟩ by
        simp [coordinates, plusCoordinates_down, minusCoordinates_down]]
  simp [pairing]

theorem pairing_skew (X Y : Carrier) :
    pairing X Y = -pairing Y X := by
  unfold pairing
  calc
    (∑ i, (X.plus i * Y.minus i - Y.plus i * X.minus i)) =
        ∑ i, - (Y.plus i * X.minus i - X.plus i * Y.minus i) := by
          apply Finset.sum_congr rfl
          intro i hi
          ring
    _ = -∑ i, (Y.plus i * X.minus i - X.plus i * Y.minus i) := by
      rw [Finset.sum_neg_distrib]

theorem pairing_alternating (X : Carrier) : pairing X X = 0 := by
  simp [pairing]

theorem pairing_left_nondegenerate
    (X : Carrier)
    (hX : ∀ Y : Carrier, pairing X Y = 0) :
    X = 0 := by
  have hplus : X.plus = 0 := by
    funext i
    let Y : Carrier := ⟨0, fun j => if j = i then 1 else 0⟩
    have h := hX Y
    simp [pairing, Y] at h
    exact h
  have hminus : X.minus = 0 := by
    funext i
    let Y : Carrier := ⟨fun j => if j = i then 1 else 0, 0⟩
    have h := hX Y
    simp [pairing, Y] at h
    exact h
  cases X with
  | mk plus minus =>
      change plus = 0 at hplus
      change minus = 0 at hminus
      subst plus
      subst minus
      rfl

theorem pairing_right_nondegenerate
    (X : Carrier)
    (hX : ∀ Y : Carrier, pairing Y X = 0) :
    X = 0 := by
  apply pairing_left_nondegenerate X
  intro Y
  rw [pairing_skew]
  simp [hX Y]

/-!
## Scalar extension of the polarized carrier

The integer carrier above is useful for native coordinate readouts.  The
following carrier is the real scalar extension needed by the symplectic and
twistor layers; it is deliberately defined as a product of two genuine real
modules rather than identified with a Hilbert or twistor space.
-/

abbrev RealVector3 := Fin 3 → ℝ
abbrev RealCarrier := RealVector3 × RealVector3

def realPairing (X Y : RealCarrier) : ℝ :=
  ∑ i, (X.1 i * Y.2 i - Y.1 i * X.2 i)

theorem realPairing_skew (X Y : RealCarrier) :
    realPairing X Y = -realPairing Y X := by
  unfold realPairing
  calc
    (∑ i, (X.1 i * Y.2 i - Y.1 i * X.2 i)) =
        ∑ i, -(Y.1 i * X.2 i - X.1 i * Y.2 i) := by
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = -∑ i, (Y.1 i * X.2 i - X.1 i * Y.2 i) := by
      rw [Finset.sum_neg_distrib]

theorem realPairing_alternating (X : RealCarrier) :
    realPairing X X = 0 := by
  simp [realPairing]

theorem realPairing_left_nondegenerate
    (X : RealCarrier)
    (hX : ∀ Y : RealCarrier, realPairing X Y = 0) :
    X = 0 := by
  have hplus : X.1 = 0 := by
    funext i
    let Y : RealCarrier :=
      ⟨0, fun j => if j = i then 1 else 0⟩
    have h := hX Y
    simp [realPairing, Y] at h
    exact h
  have hminus : X.2 = 0 := by
    funext i
    let Y : RealCarrier :=
      ⟨fun j => if j = i then 1 else 0, 0⟩
    have h := hX Y
    simp [realPairing, Y] at h
    exact h
  exact Prod.ext hplus hminus

theorem realPairing_right_nondegenerate
    (X : RealCarrier)
    (hX : ∀ Y : RealCarrier, realPairing Y X = 0) :
    X = 0 := by
  apply realPairing_left_nondegenerate X
  intro Y
  rw [realPairing_skew]
  simp [hX Y]

end InfoGeometry.OperatorAlgebra.SplitOctonions.PeirceSymplectic
