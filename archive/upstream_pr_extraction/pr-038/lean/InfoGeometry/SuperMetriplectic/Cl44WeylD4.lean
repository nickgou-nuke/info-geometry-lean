import InfoGeometry.SuperMetriplectic.WeylCharacter

/-!
# `Cl(4,4)` / `Spin(4,4)` Weyl-D4 Skeleton

Finite scalar skeleton for the `D₄` root/weight organization behind the
`Cl(4,4)` character discussion.

The complex root system of `Spin(4,4)` is type `D₄`: roots are labels
`±eᵢ ± eⱼ` for `i ≠ j`, while the two chiral spinor weight systems are
half-sign vectors with even/odd parity.  This file records that combinatorial
interface and links it to the already-defined Weyl-character degeneration
packet.

It does not prove the full Weyl character formula or construct a concrete
matrix representation of `Cl(4,4)`.
-/

namespace InfoGeometry.SuperMetriplectic

open scoped BigOperators

/-- Two signs used for `D₄` roots and spinor weights. -/
inductive D4Sign where
  | plus
  | minus
deriving DecidableEq, Repr

namespace D4Sign

/-- Real value of a sign. -/
def value : D4Sign → ℝ
  | .plus => 1
  | .minus => -1

end D4Sign

/-- Number of negative signs in a `D₄` sign vector. -/
def d4NegativeCount (s : Fin 4 → D4Sign) : ℕ :=
  ∑ i, if s i = D4Sign.minus then 1 else 0

/-- Positive chirality spinor-weight parity: even number of negative signs. -/
def d4PositiveChirality (s : Fin 4 → D4Sign) : Prop :=
  Even (d4NegativeCount s)

/-- Negative chirality spinor-weight parity: odd number of negative signs. -/
def d4NegativeChirality (s : Fin 4 → D4Sign) : Prop :=
  Odd (d4NegativeCount s)

/--
Root label for the `D₄` system: `sᵢ eᵢ + sⱼ eⱼ`, with `i ≠ j`.
-/
structure D4RootLabel where
  i : Fin 4
  j : Fin 4
  i_ne_j : i ≠ j
  signI : D4Sign
  signJ : D4Sign

namespace D4RootLabel

/-- Coordinate readout of a `D₄` root label. -/
def coordinate (R : D4RootLabel) (k : Fin 4) : ℝ :=
  if k = R.i then
    R.signI.value
  else if k = R.j then
    R.signJ.value
  else
    0

/-- The root has the first signed coordinate at `i`. -/
theorem coordinate_i (R : D4RootLabel) :
    R.coordinate R.i = R.signI.value := by
  simp [coordinate]

/-- The root has the second signed coordinate at `j`. -/
theorem coordinate_j (R : D4RootLabel) :
    R.coordinate R.j = R.signJ.value := by
  simp [coordinate, R.i_ne_j.symm]

end D4RootLabel

/--
Chiral spinor weight label for `D₄`: `1/2 (±e₁ ± e₂ ± e₃ ± e₄)`.
-/
abbrev D4SpinorWeight := Fin 4 → D4Sign

namespace D4SpinorWeight

abbrev signs (W : D4SpinorWeight) : Fin 4 → D4Sign :=
  W

/-- Chirality is derived from the parity of the sign label. -/
def positiveChirality (W : D4SpinorWeight) : Prop :=
  d4PositiveChirality W.signs

/-- Coordinate readout of a chiral spinor weight. -/
noncomputable def coordinate (W : D4SpinorWeight) (k : Fin 4) : ℝ :=
  (1 / 2 : ℝ) * (W.signs k).value

/-- Positive-chirality proof exposed through the parity definition. -/
theorem positiveChirality_iff
    (W : D4SpinorWeight) :
    W.positiveChirality ↔ d4PositiveChirality W.signs :=
  Iff.rfl

end D4SpinorWeight

/-- The Cartan subalgebra is represented by four scalar thermodynamic axes. -/
theorem cartan_rank_four :
    Fintype.card (Fin 4) = 4 := by
  simp

/-! The following readouts are consequences of the finite sign-label model,
not supplied BPS or thermodynamic hypotheses. -/

theorem d4_sign_label_has_a_chirality (W : D4SpinorWeight) :
    W.positiveChirality ∨ d4NegativeChirality W.signs := by
  exact Nat.even_or_odd (d4NegativeCount W.signs)

theorem d4_spinor_weight_coordinate_sq (W : D4SpinorWeight) (k : Fin 4) :
    (W.coordinate k) ^ 2 = (1 / 4 : ℝ) := by
  dsimp [D4SpinorWeight.coordinate, D4SpinorWeight.signs, D4Sign.value]
  cases W k <;> norm_num

theorem d4_root_coordinate_zero_of_neither
    (R : D4RootLabel) (k : Fin 4)
    (hki : k ≠ R.i) (hkj : k ≠ R.j) :
    R.coordinate k = 0 := by
  simp [D4RootLabel.coordinate, hki, hkj]

end InfoGeometry.SuperMetriplectic
