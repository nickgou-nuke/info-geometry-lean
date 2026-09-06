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
structure D4SpinorWeight where
  signs : Fin 4 → D4Sign
  positiveChirality : Prop
  chiralityProof :
    positiveChirality ↔ d4PositiveChirality signs

namespace D4SpinorWeight

/-- Coordinate readout of a chiral spinor weight. -/
noncomputable def coordinate (W : D4SpinorWeight) (k : Fin 4) : ℝ :=
  (1 / 2 : ℝ) * (W.signs k).value

/-- Positive-chirality proof exposed through the parity definition. -/
theorem positiveChirality_iff
    (W : D4SpinorWeight) :
    W.positiveChirality ↔ d4PositiveChirality W.signs :=
  W.chiralityProof

end D4SpinorWeight

/--
Cartan skeleton for the split `Cl(4,4)`/`Spin(4,4)` character lane.

`cartanTemperature` is the rank-four Cartan thermodynamic vector.  The stress
and central-charge projections are supplied scalar readouts of how a spinor
weight contributes to the two macroscopic lanes.
-/
structure Cl44D4CartanCharacterSkeleton where
  cartanTemperature : Fin 4 → ℝ
  stressProjection : D4SpinorWeight → ℝ
  centralChargeProjection : D4SpinorWeight → ℝ
  stressCentralDistribution : Cl44WeylCharacterDistribution
  totalProjection : D4SpinorWeight → ℝ
  totalProjection_eq :
    ∀ w, totalProjection w = stressProjection w + centralChargeProjection w

namespace Cl44D4CartanCharacterSkeleton

/-- The Cartan subalgebra is represented by four scalar thermodynamic axes. -/
theorem cartan_rank_four
    (_C : Cl44D4CartanCharacterSkeleton) :
    Fintype.card (Fin 4) = 4 := by
  simp

/-- Weight projection splits into stress-tensor and central-charge lanes. -/
theorem totalProjection_eq_stress_add_central
    (C : Cl44D4CartanCharacterSkeleton)
    (w : D4SpinorWeight) :
    C.totalProjection w = C.stressProjection w + C.centralChargeProjection w :=
  C.totalProjection_eq w

/-- The global degeneracy distribution is stress plus central plus residual. -/
theorem degeneracyDistribution_eq
    (C : Cl44D4CartanCharacterSkeleton) :
    C.stressCentralDistribution.totalDegeneracy =
      C.stressCentralDistribution.stressTensorDegeneracy
        + C.stressCentralDistribution.centralChargeDegeneracy
        + C.stressCentralDistribution.residualDegeneracy :=
  C.stressCentralDistribution.total_eq

end Cl44D4CartanCharacterSkeleton

/--
BPS-dominant character packet.

The dominant weights for the protected sector are exactly those whose central
charge projection saturates the selected BPS readout and whose stress
projection is compatible with the horizon/stress lane.  Dominance itself is
kept as a supplied predicate, because this file does not own the analytic
asymptotics of character coefficients.
-/
structure Cl44BPSDominantCharacterPacket where
  skeleton : Cl44D4CartanCharacterSkeleton
  dominantWeight : D4SpinorWeight
  bpsCentralReadout : ℝ
  stressReadout : ℝ
  isDominantBPSWeight : D4SpinorWeight → Prop
  dominantWeight_isBPS :
    isDominantBPSWeight dominantWeight
  centralProjection_saturates :
    skeleton.centralChargeProjection dominantWeight = bpsCentralReadout
  stressProjection_matches :
    skeleton.stressProjection dominantWeight = stressReadout

namespace Cl44BPSDominantCharacterPacket

/-- The selected dominant weight lies in the protected BPS predicate. -/
theorem dominant_isBPS
    (P : Cl44BPSDominantCharacterPacket) :
    P.isDominantBPSWeight P.dominantWeight :=
  P.dominantWeight_isBPS

/-- Its central-charge projection saturates the chosen BPS readout. -/
theorem central_saturates
    (P : Cl44BPSDominantCharacterPacket) :
    P.skeleton.centralChargeProjection P.dominantWeight = P.bpsCentralReadout :=
  P.centralProjection_saturates

/-- Its stress projection matches the chosen stress/horizon lane. -/
theorem stress_matches
    (P : Cl44BPSDominantCharacterPacket) :
    P.skeleton.stressProjection P.dominantWeight = P.stressReadout :=
  P.stressProjection_matches

/--
The dominant BPS weight simultaneously identifies the protected central-charge
lane and the stress-tensor lane.
-/
theorem bps_dominant_weight_capstone
    (P : Cl44BPSDominantCharacterPacket) :
    P.isDominantBPSWeight P.dominantWeight
      ∧ P.skeleton.centralChargeProjection P.dominantWeight = P.bpsCentralReadout
      ∧ P.skeleton.stressProjection P.dominantWeight = P.stressReadout :=
  ⟨P.dominant_isBPS, P.central_saturates, P.stress_matches⟩

end Cl44BPSDominantCharacterPacket

end InfoGeometry.SuperMetriplectic
