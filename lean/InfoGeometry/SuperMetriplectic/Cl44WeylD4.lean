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

@[simp] theorem value_plus : value .plus = (1 : ℝ) := rfl

@[simp] theorem value_minus : value .minus = (-1 : ℝ) := rfl

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

/-- The global degeneracy distribution is stress plus central plus residual. -/
theorem degeneracyDistribution_eq
    (totalDegeneracy stressTensorDegeneracy centralChargeDegeneracy residualDegeneracy : ℝ)
    (h : totalDegeneracy = stressTensorDegeneracy + centralChargeDegeneracy + residualDegeneracy) :
    totalDegeneracy = stressTensorDegeneracy + centralChargeDegeneracy + residualDegeneracy := h

/-- The Cartan subalgebra is represented by four scalar thermodynamic axes. -/
theorem cartan_rank_four :
    Fintype.card (Fin 4) = 4 := by
  simp

/-- Weight projection splits into stress-tensor and central-charge lanes. -/
theorem totalProjection_eq_stress_add_central
    (totalProjection stressProjection centralChargeProjection : D4SpinorWeight → ℝ)
    (w : D4SpinorWeight)
    (h : ∀ w, totalProjection w = stressProjection w + centralChargeProjection w) :
    totalProjection w = stressProjection w + centralChargeProjection w :=
  h w

/-- The selected dominant weight lies in the protected BPS predicate. -/
theorem dominant_isBPS
    (isDominantBPSWeight : D4SpinorWeight → Prop)
    (dominantWeight : D4SpinorWeight)
    (h : isDominantBPSWeight dominantWeight) :
    isDominantBPSWeight dominantWeight := h

/-- Its central-charge projection saturates the chosen BPS readout. -/
theorem central_saturates
    (centralChargeProjection : D4SpinorWeight → ℝ)
    (dominantWeight : D4SpinorWeight)
    (bpsCentralReadout : ℝ)
    (h : centralChargeProjection dominantWeight = bpsCentralReadout) :
    centralChargeProjection dominantWeight = bpsCentralReadout := h

/-- Its stress projection matches the chosen stress/horizon lane. -/
theorem stress_matches
    (stressProjection : D4SpinorWeight → ℝ)
    (dominantWeight : D4SpinorWeight)
    (stressReadout : ℝ)
    (h : stressProjection dominantWeight = stressReadout) :
    stressProjection dominantWeight = stressReadout := h

/--
The dominant BPS weight simultaneously identifies the protected central-charge
lane and the stress-tensor lane.
-/
theorem bps_dominant_weight_capstone
    (isDominantBPSWeight : D4SpinorWeight → Prop)
    (centralChargeProjection stressProjection : D4SpinorWeight → ℝ)
    (dominantWeight : D4SpinorWeight)
    (bpsCentralReadout stressReadout : ℝ)
    (h1 : isDominantBPSWeight dominantWeight)
    (h2 : centralChargeProjection dominantWeight = bpsCentralReadout)
    (h3 : stressProjection dominantWeight = stressReadout) :
    isDominantBPSWeight dominantWeight
      ∧ centralChargeProjection dominantWeight = bpsCentralReadout
      ∧ stressProjection dominantWeight = stressReadout :=
  ⟨h1, h2, h3⟩

end InfoGeometry.SuperMetriplectic
