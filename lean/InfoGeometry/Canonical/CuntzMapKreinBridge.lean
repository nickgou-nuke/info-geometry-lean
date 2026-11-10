import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import DAG.GraphHodgeBridge
import InfoGeometry.Canonical.CantorCuntzBasis
import InfoGeometry.Krein.DoubledSpace

/-!
# Cuntz Map on the Real Doubled Hestenes--Krein Boundary

This file isolates the finite algebraic content of the Cuntz-map clock:

* the canonical two-branch Cuntz endomorphism
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
pointwise equality witness is supplied.

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

/-- The two-branch canonical Cuntz endomorphism on an abstract star ring. -/
@[rep_depth operator]
def cuntzMapTwo (S_left S_right : Op) (X : Op) : Op :=
  S_left * X * star S_left + S_right * X * star S_right

/- The formula is already the definition.  Expose the useful algebraic law
instead: Cuntz isometries with orthogonal ranges make the two-branch map
multiplicative. -/
theorem cuntzMapTwo_mul
    (S_left S_right X Y : Op)
    (hleft : star S_left * S_left = 1)
    (hright : star S_right * S_right = 1)
    (hlr : star S_left * S_right = 0)
    (hrl : star S_right * S_left = 0) :
    cuntzMapTwo S_left S_right X * cuntzMapTwo S_left S_right Y =
      cuntzMapTwo S_left S_right (X * Y) := by
  have branch_mul {S : Op} (hS : star S * S = 1) :
      (S * X * star S) * (S * Y * star S) = S * (X * Y) * star S := by
    calc
      (S * X * star S) * (S * Y * star S) = S * X * (star S * S) * Y * star S := by
        noncomm_ring
      _ = S * X * 1 * Y * star S := by rw [hS]
      _ = S * (X * Y) * star S := by noncomm_ring
  have branch_cross {S T : Op} (hST : star S * T = 0) :
      (S * X * star S) * (T * Y * star T) = 0 := by
    calc
      (S * X * star S) * (T * Y * star T) = S * X * (star S * T) * Y * star T := by
        noncomm_ring
      _ = 0 := by rw [hST]; noncomm_ring
  unfold cuntzMapTwo
  have hll := branch_mul hleft
  have hrr := branch_mul hright
  have hlr' := branch_cross hlr
  have hrl' := branch_cross hrl
  calc
    (S_left * X * star S_left + S_right * X * star S_right) *
        (S_left * Y * star S_left + S_right * Y * star S_right) =
      (S_left * X * star S_left) * (S_left * Y * star S_left) +
      (S_left * X * star S_left) * (S_right * Y * star S_right) +
      (S_right * X * star S_right) * (S_left * Y * star S_left) +
      (S_right * X * star S_right) * (S_right * Y * star S_right) := by
        simp only [mul_add, add_mul, add_assoc]
        abel
    _ = S_left * (X * Y) * star S_left + S_right * (X * Y) * star S_right := by
      rw [hll, hlr', hrl', hrr]
      simp

/-- The Cuntz map attached to an existing `O_2` carrier. -/
@[rep_depth operator]
def cuntzCarrierMap (C : CuntzO2Carrier Op) (X : Op) : Op :=
  cuntzMapTwo C.S_left C.S_right X

theorem cuntzCarrierMap_mul (C : CuntzO2Carrier Op) (X Y : Op) :
    cuntzCarrierMap C X * cuntzCarrierMap C Y = cuntzCarrierMap C (X * Y) := by
  exact cuntzMapTwo_mul C.S_left C.S_right X Y C.left_isometry C.right_isometry
    C.orthogonal_ranges.1 C.orthogonal_ranges.2

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
theorem cuntzCarrierMap_one (C : CuntzO2Carrier Op) :
    cuntzCarrierMap C 1 = 1 := by
  exact cuntzMapTwo_one_of_partition (S_left := C.S_left) (S_right := C.S_right)
    C.range_sum

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
    (C : CuntzO2Carrier Op) (φ : Op →+ ℝ) (X : Op)
    (hleft : φ (C.S_left * X * star C.S_left) = (1 / 2 : ℝ) * φ X)
    (hright : φ (C.S_right * X * star C.S_right) = (1 / 2 : ℝ) * φ X) :
    φ (cuntzCarrierMap C X) = φ X := by
  exact real_additive_readout_fixed_of_half_branch_scaling
    (φ := φ) (S_left := C.S_left) (S_right := C.S_right) (X := X)
    hleft hright

/-! ## Discrete modular step -/

/--
Discrete modular clock data.

This records the precise condition under which the Cuntz map is the modular
clock tick in the finite rational/DAG shadow: the supplied step `sigma` is
pointwise the canonical two-branch Cuntz map.
-/
@[rep_depth operator]
structure DiscreteCuntzModularStep (Op : Type*) [Ring Op] [StarRing Op] where
  S_left : Op
  S_right : Op
  sigma : Op → Op
  sigma_eq_cuntzMap : ∀ X, sigma X = cuntzMapTwo S_left S_right X

namespace DiscreteCuntzModularStep

variable (M : DiscreteCuntzModularStep Op)

/-- A witnessed discrete step inherits multiplicativity when its branches
satisfy the Cuntz isometry and orthogonality relations. -/
theorem mul
    (hleft : star M.S_left * M.S_left = 1)
    (hright : star M.S_right * M.S_right = 1)
    (hlr : star M.S_left * M.S_right = 0)
    (hrl : star M.S_right * M.S_left = 0)
    (X Y : Op) :
    M.sigma X * M.sigma Y = M.sigma (X * Y) := by
  rw [M.sigma_eq_cuntzMap X, M.sigma_eq_cuntzMap Y, M.sigma_eq_cuntzMap (X * Y)]
  exact cuntzMapTwo_mul M.S_left M.S_right X Y hleft hright hlr hrl

/-- Fixed real readout for a witnessed discrete modular Cuntz step. -/
@[rep_depth operator]
theorem real_additive_readout_fixed_of_half_branch_scaling
    (φ : Op →+ ℝ) (X : Op)
    (hleft : φ (M.S_left * X * star M.S_left) = (1 / 2 : ℝ) * φ X)
    (hright : φ (M.S_right * X * star M.S_right) = (1 / 2 : ℝ) * φ X) :
    φ (M.sigma X) = φ X := by
  rw [M.sigma_eq_cuntzMap X]
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

/-- The transported unit clock follows from the algebraic partition relation. -/
@[rep_depth krein]
theorem map_cuntzMapTwo_one_of_partition
    (hpartition :
      R.S_left * star R.S_left + R.S_right * star R.S_right = (1 : Op)) :
    R.rho (cuntzMapTwo R.S_left R.S_right 1) = 1 := by
  rw [cuntzMapTwo_one_of_partition (S_left := R.S_left) (S_right := R.S_right)
    hpartition]
  simp

end RealDoubledKreinCuntzRepresentation

/-! ## DAG packet sharing the same real doubled Krein carrier -/

/--
The finite DAG Hodge packet and the Cuntz-map clock share the same real doubled
Hestenes--Krein carrier.
-/
@[rep_depth krein]
structure DAGCuntzClockPacket
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (α : Type*) [BEq α] [Hashable α]
    (Op : Type*) [Ring Op] [StarRing Op] where
  graph : DAG.RealDoubledKreinGraphHodgePacket E α
  cuntz : RealDoubledKreinCuntzRepresentation E Op

namespace DAGCuntzClockPacket

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {α : Type*} [BEq α] [Hashable α]
    (P : DAGCuntzClockPacket E α Op)

/-- The graph packet's derived doubled operators satisfy the real `Cl(1,1)`
relations, while its clock operator squares to minus the identity. -/
@[rep_depth krein]
theorem graph_cl11_and_clock_relations :
    (P.graph.J).comp P.graph.J = ContinuousLinearMap.id ℝ (DAG.RealDoubledKreinDAGCarrier E) ∧
    (P.graph.ε).comp P.graph.ε = ContinuousLinearMap.id ℝ (DAG.RealDoubledKreinDAGCarrier E) ∧
    (P.graph.J).comp P.graph.ε = -((P.graph.ε).comp P.graph.J) ∧
    (P.graph.K).comp P.graph.K = -(ContinuousLinearMap.id ℝ (DAG.RealDoubledKreinDAGCarrier E)) := by
  exact ⟨P.graph.J_involution, P.graph.epsilon_involution,
    P.graph.J_epsilon_anticommute, P.graph.K_square⟩

end DAGCuntzClockPacket

end InfoGeometry.Canonical.CuntzMapKreinBridge
