import Mathlib.Tactic
import DAG.GraphHodgeBridge
import InfoGeometry.Canonical.CantorCuntzBasis
import InfoGeometry.Krein.DoubledSpace

/-!
# Cuntz Map on the Real Doubled Hestenes--Krein Boundary

This file isolates the finite algebraic content of the Cuntz-map clock:

* the canonical two-branch Cuntz transfer map
  `X ↦ S_left * X * S_left^* + S_right * X * S_right^*`;
* the fixed-readout theorem under explicit KMS/Jaynes branch weights;
* the transport of this map into operators on `DoubledSpace E`;
* the DAG graph-Hodge packet sharing the same real doubled Hestenes--Krein
  carrier.

The file intentionally does not prove uniqueness of the KMS state, norm
contraction, complete positivity, or equality with a continuous modular flow.
Those are genuine proof debt unless the required positivity, norm, trace, and
classification hypotheses are supplied.

#### BUCKET 1: CLOSED FINITE THEOREMS
The algebraic Cuntz map, unitality from the Cuntz range partition, weighted
fixed-readout laws, and transport through a real doubled Krein representation.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES
The discrete modular step is identified with the Cuntz map only when its
pointwise equality property is supplied.

#### BUCKET 3: OPEN CLOSURE DEBT
Uniqueness, contractive convergence, CPTP positivity, and continuous modular
flow classification.
-/

open scoped InnerProductSpace

noncomputable section

namespace InfoGeometry.Canonical.CuntzMapKreinBridge

open InfoGeometry.Krein
open InfoGeometry.Topology

variable {Op : Type*} [Ring Op] [StarRing Op]

/-! ## Algebraic two-branch Cuntz map -/

/-- The two-branch canonical Cuntz transfer map on an abstract star ring. -/
@[rep_depth operator]
def cuntzMapTwo (S_left S_right : Op) (X : Op) : Op :=
  S_left * X * star S_left + S_right * X * star S_right

theorem cuntzMapTwo_additive
    (S_left S_right X Y : Op) :
    cuntzMapTwo S_left S_right (X + Y) =
      cuntzMapTwo S_left S_right X + cuntzMapTwo S_left S_right Y := by
  simp [cuntzMapTwo, add_mul, mul_add, add_assoc, add_left_comm]

theorem cuntzMapTwo_zero (S_left S_right : Op) :
    cuntzMapTwo S_left S_right 0 = 0 := by
  simp [cuntzMapTwo]

theorem cuntzMapTwo_mul_of_cuntz_relations
    (S_left S_right X Y : Op)
    (hLL : star S_left * S_left = 1)
    (hRR : star S_right * S_right = 1)
    (hLR : star S_left * S_right = 0)
    (hRL : star S_right * S_left = 0) :
    cuntzMapTwo S_left S_right (X * Y) =
      cuntzMapTwo S_left S_right X * cuntzMapTwo S_left S_right Y := by
  have hLL' :
      S_left * X * star S_left * S_left * Y * star S_left =
        S_left * X * Y * star S_left := by
    rw [mul_assoc (S_left * X) (star S_left) S_left, hLL]
    simp [mul_assoc]
  have hLR' :
      S_left * X * star S_left * S_right * Y * star S_right = 0 := by
    rw [mul_assoc (S_left * X) (star S_left) S_right, hLR]
    simp
  have hRL' :
      S_right * X * star S_right * S_left * Y * star S_left = 0 := by
    rw [mul_assoc (S_right * X) (star S_right) S_left, hRL]
    simp
  have hRR' :
      S_right * X * star S_right * S_right * Y * star S_right =
        S_right * X * Y * star S_right := by
    rw [mul_assoc (S_right * X) (star S_right) S_right, hRR]
    simp [mul_assoc]
  unfold cuntzMapTwo
  simp only [add_mul, mul_add]
  simp only [← mul_assoc]
  rw [hLL', hRL', hLR', hRR']
  simp

theorem cuntzMapTwo_star
    (S_left S_right X : Op) :
    cuntzMapTwo S_left S_right (star X) =
      star (cuntzMapTwo S_left S_right X) := by
  simp [cuntzMapTwo, star_add, star_mul, mul_assoc]

@[simp]
theorem cuntzMapTwo_apply (S_left S_right X : Op) :
    cuntzMapTwo S_left S_right X =
      S_left * X * star S_left + S_right * X * star S_right := by
  rfl

/-- The Cuntz map attached to an existing `O_2` carrier. -/
@[rep_depth operator]
def cuntzCarrierMap (C : InfoGeometry.Algebra.Cuntz.CuntzNAlgebra (N := 2) Op) (X : Op) : Op :=
  cuntzMapTwo (InfoGeometry.Topology.CuntzO2Carrier.S_left C)
    (InfoGeometry.Topology.CuntzO2Carrier.S_right C) X

@[simp]
theorem cuntzCarrierMap_apply (C : InfoGeometry.Algebra.Cuntz.CuntzNAlgebra (N := 2) Op) (X : Op) :
    cuntzCarrierMap C X =
      InfoGeometry.Topology.CuntzO2Carrier.S_left C * X * star (InfoGeometry.Topology.CuntzO2Carrier.S_left C) + InfoGeometry.Topology.CuntzO2Carrier.S_right C * X * star (InfoGeometry.Topology.CuntzO2Carrier.S_right C) := by
  rfl

/--
The two-branch Cuntz map preserves the unit whenever the Cuntz range
projections partition the unit.
-/
@[rep_depth operator]
theorem cuntzMapTwo_one_of_partition
    {S_left S_right : Op}
    (hpartition : S_left * star S_left + S_right * star S_right = (1 : Op)) :
    cuntzMapTwo S_left S_right 1 = 1 := by
  simp [cuntzMapTwo, hpartition]

/-- The carrier-owned Cuntz map preserves the unit by the `O_2` relation. -/
@[rep_depth operator]
theorem cuntzCarrierMap_one (C : InfoGeometry.Algebra.Cuntz.CuntzNAlgebra (N := 2) Op) :
    cuntzCarrierMap C 1 = 1 := by
  exact cuntzMapTwo_one_of_partition (S_left := InfoGeometry.Topology.CuntzO2Carrier.S_left C) (S_right := InfoGeometry.Topology.CuntzO2Carrier.S_right C)
    (InfoGeometry.Topology.CuntzO2Carrier.range_sum C)

/-! ## Real KMS/Jaynes readout fixed by the Cuntz map -/

/--
Weighted fixed-readout theorem.

If a real additive Krein/KMS readout scales the two Cuntz branches by weights
`w_left` and `w_right`, and those weights sum to one, then the readout is fixed
by one Cuntz-map clock tick.
-/
@[rep_depth operator]
theorem real_additive_readout_fixed_of_branch_scaling
    (φ : Op →+ ℝ) (S_left S_right X : Op) (w_left w_right : ℝ)
    (hweights : w_left + w_right = 1)
    (hleft : φ (S_left * X * star S_left) = w_left * φ X)
    (hright : φ (S_right * X * star S_right) = w_right * φ X) :
    φ (cuntzMapTwo S_left S_right X) = φ X := by
  calc
    φ (cuntzMapTwo S_left S_right X)
        = w_left * φ X + w_right * φ X := by
          simp [cuntzMapTwo, hleft, hright]
    _ = (w_left + w_right) * φ X := by ring
    _ = φ X := by
          rw [hweights]
          ring

/--
The symmetric Jaynes/KMS branch law: two half-weight branches make the real
readout an exact fixed point of the Cuntz-map clock.
-/
@[rep_depth operator]
theorem real_additive_readout_fixed_of_half_branch_scaling
    (φ : Op →+ ℝ) (S_left S_right X : Op)
    (hleft : φ (S_left * X * star S_left) = (1 / 2 : ℝ) * φ X)
    (hright : φ (S_right * X * star S_right) = (1 / 2 : ℝ) * φ X) :
    φ (cuntzMapTwo S_left S_right X) = φ X := by
  exact real_additive_readout_fixed_of_branch_scaling
    (φ := φ) (S_left := S_left) (S_right := S_right) (X := X)
    (w_left := (1 / 2 : ℝ)) (w_right := (1 / 2 : ℝ))
    (by norm_num) hleft hright

/-- Carrier form of the symmetric fixed-readout theorem. -/
@[rep_depth operator]
theorem cuntzCarrierMap_real_additive_readout_fixed_of_half_branch_scaling
    (C : InfoGeometry.Algebra.Cuntz.CuntzNAlgebra (N := 2) Op) (φ : Op →+ ℝ) (X : Op)
    (hleft : φ (InfoGeometry.Topology.CuntzO2Carrier.S_left C * X * star (InfoGeometry.Topology.CuntzO2Carrier.S_left C)) = (1 / 2 : ℝ) * φ X)
    (hright : φ (InfoGeometry.Topology.CuntzO2Carrier.S_right C * X * star (InfoGeometry.Topology.CuntzO2Carrier.S_right C)) = (1 / 2 : ℝ) * φ X) :
    φ (cuntzCarrierMap C X) = φ X := by
  exact real_additive_readout_fixed_of_half_branch_scaling
    (φ := φ) (S_left := InfoGeometry.Topology.CuntzO2Carrier.S_left C) (S_right := InfoGeometry.Topology.CuntzO2Carrier.S_right C) (X := X)
    hleft hright

/-! ## Discrete modular step -/

/--
Discrete modular clock data.

This records the precise condition under which the Cuntz map is the modular
clock tick in the finite rational/DAG shadow: the supplied step `sigma` is
pointwise the canonical two-branch Cuntz map.
-/
@[rep_depth operator]
abbrev DiscreteCuntzModularStep (Op : Type*) [Ring Op] [StarRing Op] := Op × Op

namespace DiscreteCuntzModularStep

variable {Op : Type*} [Ring Op] [StarRing Op]

abbrev S_left (M : DiscreteCuntzModularStep Op) : Op := M.1
abbrev S_right (M : DiscreteCuntzModularStep Op) : Op := M.2

/-- The discrete modular step is the canonical two-branch Cuntz map. -/
def sigma (M : DiscreteCuntzModularStep Op) : Op → Op :=
  cuntzMapTwo M.S_left M.S_right

variable (M : DiscreteCuntzModularStep Op)

/-- The defining equation for the discrete modular step. -/
@[rep_depth operator]
theorem apply_eq_cuntzMap (X : Op) :
    M.sigma X = cuntzMapTwo M.S_left M.S_right X :=
  rfl

/-- Fixed real readout for a witnessed discrete modular Cuntz step. -/
@[rep_depth operator]
theorem real_additive_readout_fixed_of_half_branch_scaling
    (φ : Op →+ ℝ) (X : Op)
    (hleft : φ (M.S_left * X * star M.S_left) = (1 / 2 : ℝ) * φ X)
    (hright : φ (M.S_right * X * star M.S_right) = (1 / 2 : ℝ) * φ X) :
    φ (M.sigma X) = φ X := by
  rw [M.apply_eq_cuntzMap X]
  exact CuntzMapKreinBridge.real_additive_readout_fixed_of_half_branch_scaling
    (φ := φ) (S_left := M.S_left) (S_right := M.S_right) (X := X)
    hleft hright

end DiscreteCuntzModularStep

/-! ## Real doubled Hestenes--Krein representation transport -/

/-- Operator ring on the real doubled Hestenes--Krein carrier. -/
abbrev DoubledKreinEnd
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] :=
  DoubledSpace E →L[ℝ] DoubledSpace E

/--
Representation of a Cuntz algebra shadow on the real doubled
Hestenes--Krein carrier.
-/
@[rep_depth krein]
structure RealDoubledKreinCuntzRepresentation
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (Op : Type*) [Ring Op] [StarRing Op] where
  rho : Op →+* DoubledKreinEnd E
  S_left : Op
  S_right : Op
  left_isometry :
    rho (star S_left * S_left) = 1
  right_isometry :
    rho (star S_right * S_right) = 1
  orthogonal_ranges :
    rho (star S_left * S_right) = 0 ∧
      rho (star S_right * S_left) = 0
  range_partition :
    rho (S_left * star S_left + S_right * star S_right) = 1

namespace RealDoubledKreinCuntzRepresentation

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (R : RealDoubledKreinCuntzRepresentation E Op)

/-- The Cuntz-map clock transports through a ring representation. -/
@[rep_depth krein]
theorem map_cuntzMapTwo (X : Op) :
    R.rho (cuntzMapTwo R.S_left R.S_right X) =
      R.rho R.S_left * R.rho X * R.rho (star R.S_left) +
        R.rho R.S_right * R.rho X * R.rho (star R.S_right) := by
  simp [cuntzMapTwo]

theorem map_cuntzMapTwo_mul_of_cuntz_relations
    (X Y : Op)
    (hLL : star R.S_left * R.S_left = 1)
    (hRR : star R.S_right * R.S_right = 1)
    (hLR : star R.S_left * R.S_right = 0)
    (hRL : star R.S_right * R.S_left = 0) :
    R.rho (cuntzMapTwo R.S_left R.S_right (X * Y)) =
      R.rho (cuntzMapTwo R.S_left R.S_right X) *
        R.rho (cuntzMapTwo R.S_left R.S_right Y) := by
  rw [cuntzMapTwo_mul_of_cuntz_relations
    R.S_left R.S_right X Y hLL hRR hLR hRL]
  exact R.rho.map_mul _ _

/-- The transported unit clock follows from the algebraic partition relation. -/
@[rep_depth krein]
theorem map_cuntzMapTwo_one_of_partition
    (hpartition :
      R.S_left * star R.S_left + R.S_right * star R.S_right = (1 : Op)) :
    R.rho (cuntzMapTwo R.S_left R.S_right 1) = 1 := by
  rw [cuntzMapTwo_one_of_partition (S_left := R.S_left) (S_right := R.S_right)
    hpartition]
  simp

/-- The represented Cuntz map is unital from its image-level range partition. -/
@[rep_depth krein]
theorem map_cuntzMapTwo_one :
    R.rho (cuntzMapTwo R.S_left R.S_right 1) = 1 := by
  calc
    R.rho (cuntzMapTwo R.S_left R.S_right 1) =
        R.rho (R.S_left * star R.S_left +
          R.S_right * star R.S_right) := by
      simp [cuntzMapTwo]
    _ = 1 := R.range_partition

end RealDoubledKreinCuntzRepresentation

/-! ## Native graph readouts -/

@[rep_depth krein]
theorem graph_J_eq_modular_j
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {α : Type*} [BEq α] [Hashable α]
    (G : DAG.RealDoubledKreinGraphHodgeData E α) :
    G.J = modular_j (E := E) :=
  G.J_eq

@[rep_depth krein]
theorem graph_epsilon_eq_spectral_epsilon
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {α : Type*} [BEq α] [Hashable α]
    (G : DAG.RealDoubledKreinGraphHodgeData E α) :
    G.ε = spectral_epsilon (E := E) :=
  G.epsilon_eq

@[rep_depth krein]
theorem graph_clock_eq_clockAxis
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {α : Type*} [BEq α] [Hashable α]
    (G : DAG.RealDoubledKreinGraphHodgeData E α) :
    G.K = clockAxis (E := E) :=
  G.K_eq

end InfoGeometry.Canonical.CuntzMapKreinBridge
