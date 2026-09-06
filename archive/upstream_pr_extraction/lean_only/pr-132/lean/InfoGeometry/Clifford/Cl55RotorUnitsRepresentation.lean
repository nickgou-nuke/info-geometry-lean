import InfoGeometry.Clifford.Cl55WindingMonodromyRepresentation

/-! Unit-valued packaging of the already-proved discrete rotor laws. -/

noncomputable section

namespace InfoGeometry.Clifford.Cl55RotorUnitsRepresentation

open InfoGeometry.Clifford.Cl55WindingMonodromyRepresentation

variable {A : Type*} [Ring A] [Algebra ℝ A]
variable {Γ : Type*} [Group Γ]

theorem discreteRotor_inv_left (B : A) (hB : B * B = -(1 : A))
    (theta0 : ℝ) (n : ℤ) :
    discreteRotor B theta0 (-n) * discreteRotor B theta0 n = 1 := by
  rw [← discreteRotor_add B hB theta0]
  simp [discreteRotor_zero]

theorem discreteRotor_inv_right (B : A) (hB : B * B = -(1 : A))
    (theta0 : ℝ) (n : ℤ) :
    discreteRotor B theta0 n * discreteRotor B theta0 (-n) = 1 := by
  rw [← discreteRotor_add B hB theta0]
  simp [discreteRotor_zero]

def discreteRotorUnit (B : A) (hB : B * B = -(1 : A))
    (theta0 : ℝ) (n : ℤ) : Aˣ where
  val := discreteRotor B theta0 n
  inv := discreteRotor B theta0 (-n)
  val_inv := discreteRotor_inv_right B hB theta0 n
  inv_val := discreteRotor_inv_left B hB theta0 n

def discreteRotorUnitsHom (B : A) (hB : B * B = -(1 : A))
    (theta0 : ℝ) : Multiplicative ℤ →* Aˣ where
  toFun n := discreteRotorUnit B hB theta0 (Multiplicative.toAdd n)
  map_one' := by
    apply Units.ext
    change discreteRotor B theta0 (Multiplicative.toAdd (1 : Multiplicative ℤ)) = 1
    simp [discreteRotor_zero]
  map_mul' := by
    intro m n
    apply Units.ext
    change discreteRotor B theta0 (Multiplicative.toAdd m + Multiplicative.toAdd n) =
      discreteRotor B theta0 (Multiplicative.toAdd m) *
        discreteRotor B theta0 (Multiplicative.toAdd n)
    exact discreteRotor_add B hB theta0 _ _

def windingRotorUnitsHom (B : A) (hB : B * B = -(1 : A))
    (theta0 : ℝ) (w : Γ →* Multiplicative ℤ) : Γ →* Aˣ :=
  (discreteRotorUnitsHom B hB theta0).comp w

theorem windingRotorUnitsHom_apply (B : A) (hB : B * B = -(1 : A))
    (theta0 : ℝ) (w : Γ →* Multiplicative ℤ) (gamma : Γ) :
    (windingRotorUnitsHom B hB theta0 w gamma : A) =
      discreteRotor B theta0 (Multiplicative.toAdd (w gamma)) := by
  rfl

end InfoGeometry.Clifford.Cl55RotorUnitsRepresentation
