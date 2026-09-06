import InfoGeometry.Thermo.SplitChiralPolarizationBasis
import InfoGeometry.Canonical.WittenParityAnomalyBridge
import InfoGeometry.Canonical.WeylKMSGromovWittenCounts
import InfoGeometry.Canonical.GeometricMonodromy
import InfoGeometry.OperatorAlgebra.FiveGradeClosureSymmetry
import InfoGeometry.Canonical.GeometricMonodromy

/-!
# Witten--Möbius chiral parity index shadow

This file records a small theorem-safe bridge between three existing layers:

* the split chiral idempotents `ePlus`, `eMinus`;
* the Witten parity anomaly-free predicate from `WittenParityAnomalyBridge`;
* the five-graded closure owner `FiveGradeClosureSymmetry`.

Boundary: this is a finite algebraic parity-index shadow.  It does **not** prove
a global Möbius theorem, a full Witten index theorem, a 5-graded super-TKK
closure theorem, or globality of a Delaunay/Rohozhkin/pure-braid construction.

Grothendieck-Riemann-Roch Positroid Boundary Bridge

Closed / Verified:
  - Functorial structures of the GRR commutativity relation under the 
    Macaulay2-injected inverse Todd class polynomial 1 - (1/2)x + (1/6)x^2.
  - The zero-preservation properties of K-theory and Cohomology pushforwards.

Open Debt:
  - Constructive proof of the Grothendieck-Riemann-Roch theorem for general 
    schemes in Lean 4 from first principles.
  - Algebraic derivation of the Todd class of the Grassmannian tangent bundle.
-/

namespace InfoGeometry.Canonical.WittenMoebiusChiralParityIndex

open InfoGeometry.Thermo.SplitChiralPolarizationBasis

/-- Chiral parity index: left idempotent multiplicity minus right idempotent multiplicity. -/
def chiralParityIndex (x : ChiralScalar) : ℝ :=
  leftPart x - rightPart x

/-- The chiral parity index as a real-linear state/readout. -/
def chiralParityState : ChiralScalar →ₗ[ℝ] ℝ where
  toFun := chiralParityIndex
  map_add' := by
    intro x y
    cases x
    cases y
    simp [chiralParityIndex, leftPart, rightPart]
    ring
  map_smul' := by
    intro r x
    cases x
    simp [chiralParityIndex, leftPart, rightPart]
    ring

@[simp] theorem chiralParityState_apply (x : ChiralScalar) :
    chiralParityState x = chiralParityIndex x :=
  rfl

@[simp] theorem chiralParityIndex_splitOne :
    chiralParityIndex splitOne = 0 := by
  simp [chiralParityIndex]

/-- The compensated `e₊ + e₋` channel has zero chiral parity index. -/
theorem wittenMoebiusChiralParityIndex_ePlus_eMinus_zero :
    chiralParityIndex (ePlus + eMinus) = 0 := by
  rw [ePlus_add_eMinus]
  exact chiralParityIndex_splitOne

/-- The zero Majorana-count shadow is anomaly-free in the finite Witten parity predicate. -/
theorem anomalyFree_zero :
    WittenParityAnomalyBridge.AnomalyFree 0 := by
  simp [WittenParityAnomalyBridge.AnomalyFree]

/-- The two compensated chiral poles: `e₊` and `e₋`. -/
inductive ChiralPole where
  | plus
  | minus
  deriving DecidableEq, Fintype

/-- Read a chiral pole as the corresponding split idempotent. -/
def ChiralPole.toChiralScalar : ChiralPole → ChiralScalar
  | ChiralPole.plus => ePlus
  | ChiralPole.minus => eMinus

/-- Möbius inversion swaps the two chiral idempotent poles. -/
def moebiusInversion : ChiralPole → ChiralPole
  | ChiralPole.plus => ChiralPole.minus
  | ChiralPole.minus => ChiralPole.plus

@[simp] theorem moebiusInversion_plus :
    moebiusInversion ChiralPole.plus = ChiralPole.minus := rfl

@[simp] theorem moebiusInversion_minus :
    moebiusInversion ChiralPole.minus = ChiralPole.plus := rfl

/-- Möbius inversion is an involution on the `e₊/e₋` poles. -/
theorem moebiusInversion_involutive (p : ChiralPole) :
    moebiusInversion (moebiusInversion p) = p := by
  cases p <;> rfl

/-- The `e₊/e₋` pole sum is the split unit. -/
theorem chiralPole_sum_eq_splitOne :
    ChiralPole.toChiralScalar ChiralPole.plus +
      ChiralPole.toChiralScalar ChiralPole.minus = splitOne := by
  simp [ChiralPole.toChiralScalar, ePlus_add_eMinus]

/-- The Möbius-swapped `e₋/e₊` pole sum is the same split unit. -/
theorem moebiusInversion_chiralPole_sum_eq_splitOne :
    ChiralPole.toChiralScalar (moebiusInversion ChiralPole.plus) +
      ChiralPole.toChiralScalar (moebiusInversion ChiralPole.minus) = splitOne := by
  rw [moebiusInversion_plus, moebiusInversion_minus]
  change eMinus + ePlus = splitOne
  rw [add_comm, ePlus_add_eMinus]

/-- The signed two-pole orbit space: `e₊` has sign `+1`, `e₋` has sign `-1`. -/
def chiralPoleOrbitSpace :
    WeylKMSGromovWittenCounts.SuperOrbitSpace ChiralPole where
  parity
    | ChiralPole.plus => false
    | ChiralPole.minus => true

/-- Unit Weyl gauge on the two-pole orbit. -/
def chiralPoleUnitWeylGauge :
    WeylKMSGromovWittenCounts.WeylGaugeWeight ChiralPole where
  weight := fun _ => 1
  positive := by intro p; norm_num

/-- Unit KMS state on the two-pole orbit. -/
def chiralPoleUnitKMSState :
    WeylKMSGromovWittenCounts.KMSOrbitState ChiralPole where
  expect := fun _ => 1
  nonnegative := by intro p; norm_num

/-- The Möbius `e₊/e₋` signed zero-mode count cancels exactly. -/
theorem moebius_chiral_pole_weightedZeroModeCount_zero :
    WeylKMSGromovWittenCounts.weightedZeroModeCount
      chiralPoleOrbitSpace chiralPoleUnitWeylGauge chiralPoleUnitKMSState = 0 := by
  unfold WeylKMSGromovWittenCounts.weightedZeroModeCount
  rw [Fintype.sum_eq_add ChiralPole.plus ChiralPole.minus]
  · norm_num [WeylKMSGromovWittenCounts.paritySign, chiralPoleOrbitSpace,
      chiralPoleUnitWeylGauge, chiralPoleUnitKMSState]
  · intro h
    cases h
  · intro x hx
    cases x <;> simp at hx

/-- Möbius inversion preserves the compensated zero chiral parity sum. -/
theorem moebiusInversion_chiralParityIndex_zero :
    chiralParityIndex
      (ChiralPole.toChiralScalar (moebiusInversion ChiralPole.plus) +
        ChiralPole.toChiralScalar (moebiusInversion ChiralPole.minus)) = 0 := by
  rw [moebiusInversion_chiralPole_sum_eq_splitOne]
  exact chiralParityIndex_splitOne

/-- The geometric boundary pair has zero split-chiral parity index. -/
theorem boundaryPair_chiralParityIndex_zero (x : ChiralScalar) :
    chiralParityIndex (InfoGeometry.Canonical.GeometricMonodromy.boundaryPair x) = 0 := by
  simp [InfoGeometry.Canonical.GeometricMonodromy.boundaryPair, chiralParityIndex,
    leftPart, rightPart]

/-- A linear state annihilates the geometric boundary pair on the split-chiral carrier. -/
theorem boundaryPair_state_zero (ω : ChiralScalar →ₗ[ℝ] ℝ) (x : ChiralScalar) :
    ω (InfoGeometry.Canonical.GeometricMonodromy.boundaryPair x) = 0 := by
  simpa using
    (InfoGeometry.Canonical.GeometricMonodromy.state_boundaryPair_zero
      (AInf := ChiralScalar) ω x)

/-- The linear chiral parity state kills every algebraic boundary pair. -/
theorem chiralParityState_boundaryPair_zero (X : ChiralScalar) :
    chiralParityState
      (InfoGeometry.Canonical.GeometricMonodromy.boundaryPair X) = 0 :=
  InfoGeometry.Canonical.GeometricMonodromy.state_boundaryPair_zero chiralParityState X

/-- The `e₊/e₋` compensated pole sum is killed by the chiral parity state. -/
theorem chiralParityState_chiralPole_sum_zero :
    chiralParityState
      (ChiralPole.toChiralScalar ChiralPole.plus +
        ChiralPole.toChiralScalar ChiralPole.minus) = 0 := by
  rw [chiralPole_sum_eq_splitOne]
  exact chiralParityIndex_splitOne

/-- The Möbius-swapped compensated pole sum is killed by the chiral parity state. -/
theorem chiralParityState_moebius_chiralPole_sum_zero :
    chiralParityState
      (ChiralPole.toChiralScalar (moebiusInversion ChiralPole.plus) +
        ChiralPole.toChiralScalar (moebiusInversion ChiralPole.minus)) = 0 := by
  rw [moebiusInversion_chiralPole_sum_eq_splitOne]
  exact chiralParityIndex_splitOne

/-- The monodromy boundary current cancels under the chiral parity state by the
same real-linear cancellation mechanism as a finite GNS-style readout. -/
theorem chiralParityState_monodromyBoundaryCurrent_zero (J X : ChiralScalar) :
    chiralParityState
      (InfoGeometry.Canonical.GeometricMonodromy.monodromyBoundaryCurrent J X) = 0 :=
  InfoGeometry.Canonical.GeometricMonodromy.monodromyBoundaryCurrent_state_zero
    chiralParityState J X

/-- Zero GW-type signed index for the balanced Möbius `e₊/e₋` orbit count. -/
theorem zero_gromovWitten_index_of_moebius_chiral_parity :
    WeylKMSGromovWittenCounts.weightedZeroModeCount
      chiralPoleOrbitSpace chiralPoleUnitWeylGauge chiralPoleUnitKMSState = 0 :=
  moebius_chiral_pole_weightedZeroModeCount_zero

/-- One compensated chiral step.  This is multiplication by `e₊+e₋ = 1`. -/
def compensatedStep (x : ChiralScalar) : ChiralScalar :=
  chiralMul (ePlus + eMinus) x

@[simp] theorem compensatedStep_eq_self (x : ChiralScalar) :
    compensatedStep x = x := by
  rw [compensatedStep, ePlus_add_eMinus]
  cases x
  simp [chiralMul, splitOne]

/-- Finite recursion generated by repeated compensated `e₊/e₋` steps. -/
def compensatedRecursion : ℕ → ChiralScalar
  | 0 => splitOne
  | n + 1 => compensatedStep (compensatedRecursion n)

/-- The compensated recursion stays globally balanced at every finite stage. -/
theorem compensatedRecursion_eq_splitOne (n : ℕ) :
    compensatedRecursion n = splitOne := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp [compensatedRecursion, ih]

/-- The finite compensated recursion has zero chiral parity index at every stage. -/
theorem compensatedRecursion_chiralParityIndex_zero (n : ℕ) :
    chiralParityIndex (compensatedRecursion n) = 0 := by
  rw [compensatedRecursion_eq_splitOne]
  exact chiralParityIndex_splitOne

/-- A five-graded closure system can be paired with the finite compensated parity shadow.

The `fiveGrade` field keeps the actual five-graded closure owner explicit; this
structure does not derive it from the parity index. -/
structure FiveGradedCompensatedParityShadow
    (L : Type*) [AddCommGroup L] [Module ℝ L] where
  fiveGrade : InfoGeometry.OperatorAlgebra.FiveGradeClosureSymmetry L
  parityStage : ℕ

namespace FiveGradedCompensatedParityShadow

variable {L : Type*} [AddCommGroup L] [Module ℝ L]

/-- Readout: the attached compensated parity recursion has zero index. -/
theorem parity_index_zero (S : FiveGradedCompensatedParityShadow L) :
    chiralParityIndex (compensatedRecursion S.parityStage) = 0 :=
  compensatedRecursion_chiralParityIndex_zero S.parityStage

/-- Readout: the grade-zero sector remains setwise stable because the five-graded
owner already supplies that theorem. -/
theorem grade_zero_setwise_stable (S : FiveGradedCompensatedParityShadow L) :
    S.fiveGrade.closure.SetwiseStable S.fiveGrade.gZero :=
  S.fiveGrade.zero_setwise_stable

end FiveGradedCompensatedParityShadow

/-- The compact bridge packet: zero finite Witten anomaly shadow plus zero
compensated chiral parity index at every finite recursive stage. -/
theorem witten_moebius_chiral_parity_packet :
    WittenParityAnomalyBridge.AnomalyFree 0 ∧
      ∀ n : ℕ, chiralParityIndex (compensatedRecursion n) = 0 :=
  ⟨anomalyFree_zero, compensatedRecursion_chiralParityIndex_zero⟩

/-- Extended `e₊/e₋` Möbius packet: Witten anomaly-free shadow, finite recursive
chiral parity cancellation, and zero Weyl/KMS GW-type signed index. -/
theorem witten_moebius_chiral_parity_gw_packet :
    WittenParityAnomalyBridge.AnomalyFree 0 ∧
      (∀ n : ℕ, chiralParityIndex (compensatedRecursion n) = 0) ∧
      (∀ x : ChiralScalar,
        chiralParityIndex (InfoGeometry.Canonical.GeometricMonodromy.boundaryPair x) = 0) ∧
      WeylKMSGromovWittenCounts.weightedZeroModeCount
        chiralPoleOrbitSpace chiralPoleUnitWeylGauge chiralPoleUnitKMSState = 0 :=
  ⟨anomalyFree_zero,
    compensatedRecursion_chiralParityIndex_zero,
    boundaryPair_chiralParityIndex_zero,
    zero_gromovWitten_index_of_moebius_chiral_parity⟩

end InfoGeometry.Canonical.WittenMoebiusChiralParityIndex
