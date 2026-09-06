import InfoGeometry.Clifford.Cl55CARSpinAutomorphism
import InfoGeometry.Optics.OperatorLiftCarrier

/-!
# Operator lift of the `Cl(5,5)` CAR algebra

The entries below are endomorphisms of the Clifford algebra itself.  Thus the
matrix action is a genuine operator-valued lift; no commutativity or scalar
coordinate interpretation is used.
-/

noncomputable section

namespace InfoGeometry.Clifford.Clifford55

open InfoGeometry.Optics.OperatorLiftCarrier

abbrev Cl55Operator := Module.End ℝ Cl55

/-- Left multiplication by a Clifford element, viewed as an `ℝ`-linear operator. -/
def leftAction55 (a : Cl55) : Cl55Operator :=
  LinearMap.mulLeft ℝ a

@[simp] theorem leftAction55_apply (a x : Cl55) :
    leftAction55 a x = a * x := by
  rfl

theorem leftAction55_mul (a b : Cl55) :
    leftAction55 (a * b) = leftAction55 a * leftAction55 b := by
  ext x
  simp [leftAction55, LinearMap.mulLeft_apply, Module.End.mul_apply]

theorem leftAction55_add (a b : Cl55) :
    leftAction55 (a + b) = leftAction55 a + leftAction55 b := by
  ext x
  simp [leftAction55, add_mul]

theorem leftAction55_zero :
    leftAction55 (0 : Cl55) = 0 := by
  ext x
  simp [leftAction55]

theorem leftAction55_neg (a : Cl55) :
    leftAction55 (-a) = -leftAction55 a := by
  ext x
  simp [leftAction55]

theorem leftAction55_sub (a b : Cl55) :
    leftAction55 (a - b) = leftAction55 a - leftAction55 b := by
  ext x
  simp [leftAction55, sub_mul]

theorem leftAction55_one :
    leftAction55 (1 : Cl55) = 1 := by
  ext x
  simp [leftAction55]

theorem leftAction55_commutator (a b : Cl55) :
    leftAction55 (a * b - b * a) =
      leftAction55 a * leftAction55 b - leftAction55 b * leftAction55 a := by
  rw [leftAction55_sub, leftAction55_mul, leftAction55_mul]

theorem spinTransport_leftAction55_commutator
    (g : Spin55) (a b : Cl55) :
    leftAction55 (spinCliffordRingEquiv g (a * b - b * a)) =
      leftAction55 (spinCliffordRingEquiv g a) *
          leftAction55 (spinCliffordRingEquiv g b) -
        leftAction55 (spinCliffordRingEquiv g b) *
          leftAction55 (spinCliffordRingEquiv g a) := by
  rw [map_sub, map_mul, map_mul, leftAction55_commutator]

/-- The full operator-entry matrix algebra on the doubled `Cl(5,5)` carrier. -/
abbrev Cl55OperatorMatrix :=
  OperatorMatrix (R := ℝ) (W := Cl55)

/-- A noncommutative four-entry Clifford operator packet. -/
def cl55OperatorMatrix (a b c d : Cl55) : Cl55OperatorMatrix :=
  !![leftAction55 a, leftAction55 b;
     leftAction55 c, leftAction55 d]

@[simp] theorem cl55OperatorMatrix_apply
    (a b c d : Cl55) (v : Fin 2 → Cl55) (i : Fin 2) :
    matrixAction (cl55OperatorMatrix a b c d) v i =
      ∑ j : Fin 2, (cl55OperatorMatrix a b c d) i j (v j) := by
  exact matrixAction_apply _ _ _

theorem cl55OperatorMatrix_mul_action
    (A B : Cl55OperatorMatrix) :
    matrixAction (A * B) = matrixAction A * matrixAction B := by
  exact matrixAction_mul_end A B

theorem cl55CAR_leftAction_anticommutator (i : Fin 5) :
    leftAction55 (annihilation55 i) * leftAction55 (creation55 i) +
        leftAction55 (creation55 i) * leftAction55 (annihilation55 i) = 1 := by
  rw [← leftAction55_mul, ← leftAction55_mul, ← leftAction55_add]
  calc
    leftAction55
        (annihilation55 i * creation55 i + creation55 i * annihilation55 i) =
        leftAction55 (1 : Cl55) :=
      congrArg leftAction55 (annihilation55_creation55_anticommutator i)
    _ = 1 := leftAction55_one

theorem cl55CAR_leftAction_anticommutator_offdiag (i j : Fin 5) (h : i ≠ j) :
    leftAction55 (annihilation55 i) * leftAction55 (creation55 j) +
        leftAction55 (creation55 j) * leftAction55 (annihilation55 i) = 0 := by
  rw [← leftAction55_mul, ← leftAction55_mul, ← leftAction55_add]
  calc
    leftAction55
        (annihilation55 i * creation55 j + creation55 j * annihilation55 i) =
        leftAction55 (0 : Cl55) :=
      congrArg leftAction55
        (by simpa [h] using annihilation55_creation55_anticommutator_eq i j)
    _ = 0 := leftAction55_zero

theorem cl55CAR_leftAction_anticommutator_general (i j : Fin 5) :
    leftAction55 (annihilation55 i) * leftAction55 (creation55 j) +
        leftAction55 (creation55 j) * leftAction55 (annihilation55 i) =
      if i = j then 1 else 0 := by
  by_cases h : i = j
  · subst j
    simpa using cl55CAR_leftAction_anticommutator i
  · simpa [if_neg h] using cl55CAR_leftAction_anticommutator_offdiag i j h

theorem spinTransport_leftAction55_mul
    (g : Spin55) (a x : Cl55) :
    spinCliffordRingEquiv g (leftAction55 a x) =
      leftAction55 (spinCliffordRingEquiv g a)
        (spinCliffordRingEquiv g x) := by
  change spinCliffordRingEquiv g (a * x) =
    spinCliffordRingEquiv g a * spinCliffordRingEquiv g x
  exact InfoGeometry.Clifford.ChiralLorentzCARLift.unitConjugation_mul
    (spinGroup.toUnits g) a x

theorem spinTransport_cl55CAR_leftAction_anticommutator (g : Spin55) (i : Fin 5) :
    leftAction55 (spinCliffordRingEquiv g (annihilation55 i)) *
          leftAction55 (spinCliffordRingEquiv g (creation55 i)) +
        leftAction55 (spinCliffordRingEquiv g (creation55 i)) *
          leftAction55 (spinCliffordRingEquiv g (annihilation55 i)) = 1 := by
  rw [← leftAction55_mul, ← leftAction55_mul, ← leftAction55_add]
  calc
    leftAction55
        (spinCliffordRingEquiv g (annihilation55 i) *
          spinCliffordRingEquiv g (creation55 i) +
        spinCliffordRingEquiv g (creation55 i) *
          spinCliffordRingEquiv g (annihilation55 i)) =
        leftAction55 (1 : Cl55) :=
      congrArg leftAction55 (spinCliffordRingEquiv_car_anticommutator g i)
    _ = 1 := leftAction55_one

theorem spinTransport_cl55CAR_leftAction_anticommutator_general
    (g : Spin55) (i j : Fin 5) :
    leftAction55 (spinCliffordRingEquiv g (annihilation55 i)) *
          leftAction55 (spinCliffordRingEquiv g (creation55 j)) +
        leftAction55 (spinCliffordRingEquiv g (creation55 j)) *
          leftAction55 (spinCliffordRingEquiv g (annihilation55 i)) =
      if i = j then 1 else 0 := by
  by_cases h : i = j
  · subst j
    simpa using spinTransport_cl55CAR_leftAction_anticommutator g i
  · simpa [h, ← leftAction55_mul, ← leftAction55_add, map_mul, map_add,
      map_zero, leftAction55_zero] using
      congrArg leftAction55
        (spinCliffordRingEquiv_annihilation55_creation55_anticommutator_eq g i j)

end InfoGeometry.Clifford.Clifford55
