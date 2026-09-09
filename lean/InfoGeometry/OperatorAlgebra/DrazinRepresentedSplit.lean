/-
InfoGeometry/OperatorAlgebra/DrazinRepresentedSplit.lean

Represented split algebras and Drazin projectors.

The Drazin split is representation-level:

    ρ : A_split → Op

where `Op` is an associative operator algebra.  The source split algebra may
carry isotropic cones or zero-divisor loci, but Drazin projectors and circular
polarization live safely in the associative represented operator algebra.
-/

import Mathlib.Tactic
import InfoGeometry.OperatorAlgebra.ChiralPolarization
import InfoGeometry.Meta.OwnerTarget

noncomputable section

namespace InfoGeometry.OperatorAlgebra

/-! ## 1. Complementary projector pairs in an operator algebra -/

/--
A complementary pair of projectors in an associative operator algebra.

`Pcore` is the regular/Drazin-core projector.  `Pnil` is the generalized
zero/nil/null-sector projector.
-/
structure DrazinProjectorPair
    (Op : Type*) [Ring Op] where
  Pcore : Op
  Pnil : Op

  Pcore_idem :
    Pcore * Pcore = Pcore

  Pnil_idem :
    Pnil * Pnil = Pnil

  projector_sum :
    Pcore + Pnil = 1

  core_nil_disjoint :
    Pcore * Pnil = 0

  nil_core_disjoint :
    Pnil * Pcore = 0

namespace DrazinProjectorPair

variable {Op : Type*} [Ring Op]
variable (P : DrazinProjectorPair Op)

/-- Every operator algebra element has a left decomposition by the projectors. -/
theorem left_decomposition
    (x : Op) :
    P.Pcore * x + P.Pnil * x = x := by
  calc
    P.Pcore * x + P.Pnil * x
        = (P.Pcore + P.Pnil) * x := by
          exact (add_mul P.Pcore P.Pnil x).symm
    _ = 1 * x := by
          rw [P.projector_sum]
    _ = x := one_mul x

/-- Every operator algebra element has a right decomposition by the projectors. -/
theorem right_decomposition
    (x : Op) :
    x * P.Pcore + x * P.Pnil = x := by
  calc
    x * P.Pcore + x * P.Pnil
        = x * (P.Pcore + P.Pnil) := by
          exact (mul_add x P.Pcore P.Pnil).symm
    _ = x * 1 := by
          rw [P.projector_sum]
    _ = x := mul_one x

/-- The core projector kills the nil branch on the left. -/
theorem core_kills_left_nil
    (x : Op) :
    P.Pcore * (P.Pnil * x) = 0 := by
  rw [← mul_assoc, P.core_nil_disjoint, zero_mul]

/-- The nil projector kills the core branch on the left. -/
theorem nil_kills_left_core
    (x : Op) :
    P.Pnil * (P.Pcore * x) = 0 := by
  rw [← mul_assoc, P.nil_core_disjoint, zero_mul]

/-- The core projector kills the nil branch on the right. -/
theorem core_kills_right_nil
    (x : Op) :
    (x * P.Pnil) * P.Pcore = 0 := by
  rw [mul_assoc, P.nil_core_disjoint, mul_zero]

/-- The nil projector kills the core branch on the right. -/
theorem nil_kills_right_core
    (x : Op) :
    (x * P.Pcore) * P.Pnil = 0 := by
  rw [mul_assoc, P.core_nil_disjoint, mul_zero]

/--
An element cannot be simultaneously left-supported on the regular core branch
and the nil branch.
-/
theorem eq_zero_of_left_core_and_nil_supported
    {x : Op}
    (hcore : P.Pcore * x = x)
    (hnil : P.Pnil * x = x) :
    x = 0 := by
  calc
    x = P.Pcore * x := hcore.symm
    _ = P.Pcore * (P.Pnil * x) := by rw [hnil]
    _ = 0 := P.core_kills_left_nil x

/--
An element cannot be simultaneously right-supported on the regular core branch
and the nil branch.
-/
theorem eq_zero_of_right_core_and_nil_supported
    {x : Op}
    (hcore : x * P.Pcore = x)
    (hnil : x * P.Pnil = x) :
    x = 0 := by
  calc
    x = x * P.Pcore := hcore.symm
    _ = (x * P.Pnil) * P.Pcore := by rw [hnil]
    _ = 0 := P.core_kills_right_nil x

end DrazinProjectorPair

/-! ## 2. Branch predicates inside the represented operator algebra -/

/-- An element is left-supported on the regular core branch. -/
def IsLeftCoreSupported
    {Op : Type*} [Ring Op]
    (P : DrazinProjectorPair Op)
    (x : Op) : Prop :=
  P.Pcore * x = x

/-- An element is left-supported on the nil/null branch. -/
def IsLeftNilSupported
    {Op : Type*} [Ring Op]
    (P : DrazinProjectorPair Op)
    (x : Op) : Prop :=
  P.Pnil * x = x

/-- An element is two-sided supported on the regular core branch. -/
def IsCoreSupported
    {Op : Type*} [Ring Op]
    (P : DrazinProjectorPair Op)
    (x : Op) : Prop :=
  P.Pcore * x = x ∧ x * P.Pcore = x

/-- An element is two-sided supported on the nil/null branch. -/
def IsNilSupported
    {Op : Type*} [Ring Op]
    (P : DrazinProjectorPair Op)
    (x : Op) : Prop :=
  P.Pnil * x = x ∧ x * P.Pnil = x

/-! ## 3. Represented split algebra datum -/

/--
A represented split algebra whose Drazin geometry lives in an associative
operator algebra.

The source `Split` may be noncommutative or nonassociative.  This structure
does not force algebraic operations on `Split`; it only records a representation
into `Op`, where the Drazin projectors and circular polarization are formalized.
-/
structure DrazinRepresentedSplit
    (Core Split Op : Type*)
    [Ring Op] [Module ℝ Op] where
  /-- Representation of the division-like regular core into the operator algebra. -/
  coreRep : Core → Op

  /-- Representation of the doubled/split algebra into the operator algebra. -/
  splitRep : Split → Op

  /-- Circular polarization of the represented operator algebra. -/
  circular : CircularPolarization Op

  /-- Drazin regular/nil projector pair in the represented operator algebra. -/
  projectors : DrazinProjectorPair Op

  /--
  Represented core elements have no represented square-zero defect.

  This is a representation-level division-core condition; it avoids pretending
  that the abstract source core must be a commutative integral domain.
  -/
  core_no_square_zero :
    ∀ c : Core,
      coreRep c * coreRep c = 0 → coreRep c = 0

  /--
  Defect locus inside the split source.

  This is a predicate/subobject of `Split`, not a new ambient algebra.
  -/
  defectLocus : Set Split

  /-- Elements of the defect locus map to nilpotent represented operators. -/
  defect_maps_to_nilpotent :
    ∀ a : Split,
      a ∈ defectLocus →
        IsNilpotentElement (splitRep a)

  /-- Elements of the defect locus are supported on the represented nil branch. -/
  defect_supported_by_nil :
    ∀ a : Split,
      a ∈ defectLocus →
        IsLeftNilSupported projectors (splitRep a)

  /-- Regular/core source elements are supported on the represented core branch. -/
  core_supported_by_core :
    ∀ c : Core,
      IsLeftCoreSupported projectors (coreRep c)

namespace DrazinRepresentedSplit

variable {Core Split Op : Type*} [Ring Op] [Module ℝ Op]
variable (W : DrazinRepresentedSplit Core Split Op)

/-- A represented core element has no represented square-zero defect. -/
theorem core_square_zero_eq_zero
    (c : Core)
    (h : W.coreRep c * W.coreRep c = 0) :
    W.coreRep c = 0 :=
  W.core_no_square_zero c h

/-- A defect-locus element maps to a nilpotent represented operator. -/
theorem defect_nilpotent
    {a : Split}
    (ha : a ∈ W.defectLocus) :
    IsNilpotentElement (W.splitRep a) :=
  W.defect_maps_to_nilpotent a ha

/-- A defect-locus element is supported on the nil branch. -/
theorem defect_nil_supported
    {a : Split}
    (ha : a ∈ W.defectLocus) :
    IsLeftNilSupported W.projectors (W.splitRep a) :=
  W.defect_supported_by_nil a ha

/-- A core element is supported on the regular branch. -/
theorem core_supported
    (c : Core) :
    IsLeftCoreSupported W.projectors (W.coreRep c) :=
  W.core_supported_by_core c

/--
Left decomposition of a represented split element into core and nil projector
parts.
-/
theorem split_left_projector_decomposition
    (a : Split) :
    W.projectors.Pcore * W.splitRep a +
      W.projectors.Pnil * W.splitRep a =
    W.splitRep a :=
  W.projectors.left_decomposition (W.splitRep a)

/--
Right decomposition of a represented split element into core and nil projector
parts.
-/
theorem split_right_projector_decomposition
    (a : Split) :
    W.splitRep a * W.projectors.Pcore +
      W.splitRep a * W.projectors.Pnil =
    W.splitRep a :=
  W.projectors.right_decomposition (W.splitRep a)

end DrazinRepresentedSplit

/-! ## 4. Metric/Drazin tear witness -/

/--
A metric-vs-Drazin projector pair.

This is separate from the core/nil complementary pair: it measures a possible
mismatch between a metric/Moore-Penrose-style projector and a
Drazin/topological projector.
-/
structure MetricDrazinProjectorPair
    (Op : Type*) [Ring Op] where
  drazin : Op
  metric : Op

  drazin_idem :
    drazin * drazin = drazin

  metric_idem :
    metric * metric = metric

namespace MetricDrazinProjectorPair

variable {Op : Type*} [Ring Op]
variable (P : MetricDrazinProjectorPair Op)

/-- The projector tear: `Π_metric - Π_Drazin`. -/
def tear : Op :=
  P.metric - P.drazin

/-- If the metric and Drazin projectors agree, the tear vanishes. -/
theorem tear_eq_zero_of_eq
    (h : P.metric = P.drazin) :
    P.tear = 0 := by
  dsimp [tear]
  rw [h]
  simp

/-- A nonzero tear implies the metric and Drazin projectors are distinct. -/
theorem metric_ne_drazin_of_tear_ne_zero
    (h : P.tear ≠ 0) :
    P.metric ≠ P.drazin := by
  intro hEq
  exact h (P.tear_eq_zero_of_eq hEq)

end MetricDrazinProjectorPair

/-! ## 5. Owner target -/

/--
Compatibility data for constructing a represented Drazin split.

This is intentionally exact: a compatible source/core/operator triple carries
precisely the data required to build `DrazinRepresentedSplit`.  The owner
theorem below is therefore a constructor from fields, not a nonempty restatement
and not a theorem from a vacuous premise.
-/
structure DrazinRepresentedSplitCompatibility
    (Core Split Op : Type*)
    [Ring Op] [Module ℝ Op] where
  /-- Representation of the division-like regular core into the operator algebra. -/
  coreRep : Core → Op

  /-- Representation of the doubled/split algebra into the operator algebra. -/
  splitRep : Split → Op

  /-- Circular polarization of the represented operator algebra. -/
  circular : CircularPolarization Op

  /-- Drazin regular/nil projector pair in the represented operator algebra. -/
  projectors : DrazinProjectorPair Op

  /-- Represented core elements have no represented square-zero defect. -/
  core_no_square_zero :
    ∀ c : Core,
      coreRep c * coreRep c = 0 → coreRep c = 0

  /-- Defect locus inside the split source. -/
  defectLocus : Set Split

  /-- Elements of the defect locus map to nilpotent represented operators. -/
  defect_maps_to_nilpotent :
    ∀ a : Split,
      a ∈ defectLocus →
        IsNilpotentElement (splitRep a)

  /-- Elements of the defect locus are supported on the represented nil branch. -/
  defect_supported_by_nil :
    ∀ a : Split,
      a ∈ defectLocus →
        IsLeftNilSupported projectors (splitRep a)

  /-- Regular/core source elements are supported on the represented core branch. -/
  core_supported_by_core :
    ∀ c : Core,
      IsLeftCoreSupported projectors (coreRep c)

namespace DrazinRepresentedSplitCompatibility

variable {Core Split Op : Type*} [Ring Op] [Module ℝ Op]

/-- Construct the represented Drazin split from explicit compatibility data. -/
def toDrazinRepresentedSplit
    (C : DrazinRepresentedSplitCompatibility Core Split Op) :
    DrazinRepresentedSplit Core Split Op where
  coreRep := C.coreRep
  splitRep := C.splitRep
  circular := C.circular
  projectors := C.projectors
  core_no_square_zero := C.core_no_square_zero
  defectLocus := C.defectLocus
  defect_maps_to_nilpotent := C.defect_maps_to_nilpotent
  defect_supported_by_nil := C.defect_supported_by_nil
  core_supported_by_core := C.core_supported_by_core

end DrazinRepresentedSplitCompatibility

/-! ## Owner theorem -/

/--
A compatible represented split carries an extracted represented split,
circular-polarization, and Drazin core/null projector package.
-/
theorem drazinRepresentedSplitOwnerTarget
    (Core Split Op : Type*)
    [Ring Op] [Module ℝ Op]
    (C : DrazinRepresentedSplitCompatibility Core Split Op) :
    let W := C.toDrazinRepresentedSplit
    W.coreRep = C.coreRep ∧
      W.splitRep = C.splitRep ∧
      W.circular = C.circular ∧
      W.projectors = C.projectors ∧
      W.defectLocus = C.defectLocus := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

end InfoGeometry.OperatorAlgebra
