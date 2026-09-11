/-
InfoGeometry/OperatorAlgebra/SymmetryInvariants.lean

Symmetry-invariant operator structures.

Principle:

  observed geometry = invariant or equivariant operator data.

This file formalizes the general algebraic layer underneath the later
PhaseErlanger, Drazin, Siegel, spectral, and automorphic modules.

The ambient object is a represented operator algebra `Op` with a symmetry
action by ring automorphisms. Geometry is then reconstructed from invariant
operators, invariant projectors, supported sectors, invariant predicates,
readouts, pairings, and projector decompositions.
-/

import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.OperatorAlgebra.ChiralPolarization
import InfoGeometry.OperatorAlgebra.DrazinRepresentedSplit
import InfoGeometry.OperatorAlgebra.ErlangenConformalInvariant
import InfoGeometry.Meta.OwnerTarget

noncomputable section

namespace InfoGeometry.OperatorAlgebra

universe uG uOp uβ uOut uOp₂

/-! ## 1. Symmetry actions by ring automorphisms -/

/--
A symmetry action of a group `G` on an operator algebra `Op`.

Each symmetry acts by a ring automorphism. The action laws are recorded
pointwise to keep rewriting predictable.
-/
structure SymmetryAction
    (G : Type uG)
    (Op : Type uOp)
    [Group G] [Ring Op] where
  /-- The ring automorphism associated to a symmetry element. -/
  act : G → Op ≃+* Op

  /-- The identity group element acts trivially. -/
  act_one :
    ∀ x : Op, act 1 x = x

  /-- Multiplication in the group composes the corresponding actions. -/
  act_mul :
    ∀ g h : G, ∀ x : Op, act (g * h) x = act g (act h x)

namespace SymmetryAction

variable {G Op : Type*} [Group G] [Ring Op]
variable (α : SymmetryAction G Op)

@[simp]
theorem act_one_apply
    (x : Op) :
    α.act 1 x = x :=
  α.act_one x

@[simp]
theorem act_mul_apply
    (g h : G)
    (x : Op) :
    α.act (g * h) x = α.act g (α.act h x) :=
  α.act_mul g h x

@[simp]
theorem act_zero
    (g : G) :
    α.act g (0 : Op) = 0 := by
  simp

@[simp]
theorem act_one_ring
    (g : G) :
    α.act g (1 : Op) = 1 := by
  simp

@[simp]
theorem act_add
    (g : G)
    (x y : Op) :
    α.act g (x + y) = α.act g x + α.act g y := by
  simp

@[simp]
theorem act_neg
    (g : G)
    (x : Op) :
    α.act g (-x) = -α.act g x := by
  simp

@[simp]
theorem act_sub
    (g : G)
    (x y : Op) :
    α.act g (x - y) = α.act g x - α.act g y := by
  simp [sub_eq_add_neg]

@[simp]
theorem act_mul_op
    (g : G)
    (x y : Op) :
    α.act g (x * y) = α.act g x * α.act g y := by
  simp

/-- The inverse action undoes the action. -/
theorem act_inv_act
    (g : G)
    (x : Op) :
    α.act g⁻¹ (α.act g x) = x := by
  rw [← α.act_mul_apply g⁻¹ g x]
  simp

/-- The action undoes the inverse action. -/
theorem act_act_inv
    (g : G)
    (x : Op) :
    α.act g (α.act g⁻¹ x) = x := by
  rw [← α.act_mul_apply g g⁻¹ x]
  simp

end SymmetryAction

/-! ## 2. Invariant operators and the fixed subring -/

/--
An operator is invariant under a symmetry action.
-/
def IsInvariant
    {G Op : Type*} [Group G] [Ring Op]
    (α : SymmetryAction G Op)
    (x : Op) : Prop :=
  ∀ g : G, α.act g x = x

/--
Invariant operators as a set inside the fixed ambient algebra.
-/
def invariantSet
    {G Op : Type*} [Group G] [Ring Op]
    (α : SymmetryAction G Op) : Set Op :=
  {x : Op | IsInvariant α x}

namespace IsInvariant

variable {G Op : Type*} [Group G] [Ring Op]
variable (α : SymmetryAction G Op)

/-- Zero is invariant. -/
theorem zero :
    IsInvariant α (0 : Op) := by
  intro g
  simp

/-- One is invariant. -/
theorem one :
    IsInvariant α (1 : Op) := by
  intro g
  simp

/-- Sums of invariant operators are invariant. -/
theorem add
    {x y : Op}
    (hx : IsInvariant α x)
    (hy : IsInvariant α y) :
    IsInvariant α (x + y) := by
  intro g
  simp [hx g, hy g]

/-- Negatives of invariant operators are invariant. -/
theorem neg
    {x : Op}
    (hx : IsInvariant α x) :
    IsInvariant α (-x) := by
  intro g
  simp [hx g]

/-- Differences of invariant operators are invariant. -/
theorem sub
    {x y : Op}
    (hx : IsInvariant α x)
    (hy : IsInvariant α y) :
    IsInvariant α (x - y) := by
  simpa [sub_eq_add_neg] using add α hx (neg α hy)

/-- Products of invariant operators are invariant. -/
theorem mul
    {x y : Op}
    (hx : IsInvariant α x)
    (hy : IsInvariant α y) :
    IsInvariant α (x * y) := by
  intro g
  simp [hx g, hy g]

end IsInvariant

/-- The fixed operator subring `Op^G`. -/
def invariantSubring
    {G Op : Type*} [Group G] [Ring Op]
    (α : SymmetryAction G Op) :
    Subring Op where
  carrier := {x : Op | IsInvariant α x}
  zero_mem' := IsInvariant.zero α
  one_mem' := IsInvariant.one α
  add_mem' := by
    intro x y hx hy
    exact IsInvariant.add α hx hy
  neg_mem' := by
    intro x hx
    exact IsInvariant.neg α hx
  mul_mem' := by
    intro x y hx hy
    exact IsInvariant.mul α hx hy

@[simp]
theorem mem_invariantSubring_iff
    {G Op : Type*} [Group G] [Ring Op]
    (α : SymmetryAction G Op)
    (x : Op) :
    x ∈ invariantSubring α ↔ IsInvariant α x :=
  Iff.rfl

/-! ## 3. Projectors, invariant projectors, and supported sectors -/

/-- An algebraic projector/idempotent. -/
def IsProjector
    {Op : Type*} [Ring Op]
    (p : Op) : Prop :=
  p * p = p

/--
An invariant projector is an idempotent fixed by the symmetry action.
-/
def IsInvariantProjector
    {G Op : Type*} [Group G] [Ring Op]
    (α : SymmetryAction G Op)
    (p : Op) : Prop :=
  IsProjector p ∧ IsInvariant α p

/--
Left support condition: `x` lies in the sector cut out by `p`.
-/
def IsSupportedOn
    {Op : Type*} [Ring Op]
    (p x : Op) : Prop :=
  p * x = x

/-- Right support condition. -/
def IsRightSupportedOn
    {Op : Type*} [Ring Op]
    (p x : Op) : Prop :=
  x * p = x

/-- Two-sided support condition. -/
def IsBiSupportedOn
    {Op : Type*} [Ring Op]
    (p x : Op) : Prop :=
  IsSupportedOn p x ∧ IsRightSupportedOn p x

namespace Projector

variable {G Op : Type*} [Group G] [Ring Op]
variable (α : SymmetryAction G Op)

theorem one_isProjector :
    IsProjector (1 : Op) := by
  simp [IsProjector]

theorem zero_isProjector :
    IsProjector (0 : Op) := by
  simp [IsProjector]

theorem one_isInvariantProjector :
    IsInvariantProjector α (1 : Op) :=
  ⟨one_isProjector, IsInvariant.one α⟩

theorem zero_isInvariantProjector :
    IsInvariantProjector α (0 : Op) :=
  ⟨zero_isProjector, IsInvariant.zero α⟩

/-- Ring automorphisms preserve projectors. -/
theorem image_isProjector
    {p : Op}
    (hp : IsProjector p)
    (g : G) :
    IsProjector (α.act g p) := by
  unfold IsProjector at hp ⊢
  calc
    α.act g p * α.act g p
        = α.act g (p * p) := by
          exact (α.act_mul_op g p p).symm
    _ = α.act g p := by
          rw [hp]

/--
If `p` is invariant and `x` is supported on `p`, then every symmetry translate
of `x` is also supported on `p`.
-/
theorem supported_image
    {p x : Op}
    (hp : IsInvariant α p)
    (hx : IsSupportedOn p x)
    (g : G) :
    IsSupportedOn p (α.act g x) := by
  unfold IsSupportedOn at hx ⊢
  calc
    p * α.act g x
        = α.act g p * α.act g x := by
          rw [hp g]
    _ = α.act g (p * x) := by
          exact (α.act_mul_op g p x).symm
    _ = α.act g x := by
          rw [hx]

/--
Support on an invariant projector is itself an invariant predicate.
-/
theorem supported_image_iff
    {p x : Op}
    (hp : IsInvariant α p)
    (g : G) :
    IsSupportedOn p (α.act g x) ↔ IsSupportedOn p x := by
  constructor
  · intro hx
    have h := supported_image α hp hx g⁻¹
    have hcomp : α.act g⁻¹ (α.act g x) = x :=
      α.act_inv_act g x
    simpa [hcomp] using h
  · intro hx
    exact supported_image α hp hx g

/--
Right support on an invariant projector is invariant under the symmetry action.
-/
theorem right_supported_image
    {p x : Op}
    (hp : IsInvariant α p)
    (hx : IsRightSupportedOn p x)
    (g : G) :
    IsRightSupportedOn p (α.act g x) := by
  unfold IsRightSupportedOn at hx ⊢
  calc
    α.act g x * p
        = α.act g x * α.act g p := by
          rw [hp g]
    _ = α.act g (x * p) := by
          exact (α.act_mul_op g x p).symm
    _ = α.act g x := by
          rw [hx]

/-- Two-sided support on an invariant projector is invariant. -/
theorem biSupported_image
    {p x : Op}
    (hp : IsInvariant α p)
    (hx : IsBiSupportedOn p x)
    (g : G) :
    IsBiSupportedOn p (α.act g x) :=
  ⟨supported_image α hp hx.1 g, right_supported_image α hp hx.2 g⟩

end Projector

/-! ## 4. Complementary projector decompositions -/

/--
A pair of complementary idempotents.

This is the common algebraic skeleton behind Drazin core/nil splitting,
boundary/cuspidal splitting, and chiral left/right splitting.
-/
structure ComplementaryProjectors
    (Op : Type uOp)
    [Ring Op] where
  p : Op
  q : Op

  p_idempotent :
    IsProjector p

  q_idempotent :
    IsProjector q

  sum_eq_one :
    p + q = 1

  pq_zero :
    p * q = 0

  qp_zero :
    q * p = 0

namespace ComplementaryProjectors

variable {Op : Type uOp}
variable [Ring Op]

/-- The `p`-supported component of `x`. -/
def pComponent
    (P : ComplementaryProjectors Op)
    (x : Op) : Op :=
  P.p * x

/-- The `q`-supported component of `x`. -/
def qComponent
    (P : ComplementaryProjectors Op)
    (x : Op) : Op :=
  P.q * x

/-- Every element decomposes into its two left-supported components. -/
theorem left_decomposition
    (P : ComplementaryProjectors Op)
    (x : Op) :
    P.pComponent x + P.qComponent x = x := by
  unfold pComponent qComponent
  calc
    P.p * x + P.q * x
        = (P.p + P.q) * x := by
          rw [add_mul]
    _ = x := by
          rw [P.sum_eq_one, one_mul]

/-- The `p`-component is supported on `p`. -/
theorem pComponent_supported
    (P : ComplementaryProjectors Op)
    (x : Op) :
    IsSupportedOn P.p (P.pComponent x) := by
  unfold IsSupportedOn pComponent
  calc
    P.p * (P.p * x)
        = (P.p * P.p) * x := by
          rw [mul_assoc]
    _ = P.p * x := by
          rw [P.p_idempotent]

/-- The `q`-component is supported on `q`. -/
theorem qComponent_supported
    (P : ComplementaryProjectors Op)
    (x : Op) :
    IsSupportedOn P.q (P.qComponent x) := by
  unfold IsSupportedOn qComponent
  calc
    P.q * (P.q * x)
        = (P.q * P.q) * x := by
          rw [mul_assoc]
    _ = P.q * x := by
          rw [P.q_idempotent]

end ComplementaryProjectors

/-- A symmetry-invariant complementary projector decomposition. -/
structure InvariantProjectorDecomposition
    {G Op : Type*} [Group G] [Ring Op]
    (α : SymmetryAction G Op) where
  projectors : ComplementaryProjectors Op

  p_invariant :
    IsInvariant α projectors.p

  q_invariant :
    IsInvariant α projectors.q

namespace InvariantProjectorDecomposition

variable {G Op : Type*} [Group G] [Ring Op]
variable {α : SymmetryAction G Op}

/-- The `p`-sector support condition is invariant under the action. -/
theorem p_supported_image_iff
    (P : InvariantProjectorDecomposition α)
    (g : G)
    (x : Op) :
    IsSupportedOn P.projectors.p (α.act g x) ↔
      IsSupportedOn P.projectors.p x :=
  Projector.supported_image_iff α P.p_invariant g

/-- The `q`-sector support condition is invariant under the action. -/
theorem q_supported_image_iff
    (P : InvariantProjectorDecomposition α)
    (g : G)
    (x : Op) :
    IsSupportedOn P.projectors.q (α.act g x) ↔
      IsSupportedOn P.projectors.q x :=
  Projector.supported_image_iff α P.q_invariant g

end InvariantProjectorDecomposition

/-! ## 5. Invariant predicates, readouts, and pairings -/

/--
An invariant predicate on the operator algebra.

Examples: defect loci, nilpotent loci, regular loci, support loci,
spectral-branch predicates.
-/
def InvariantPredicate
    {G Op : Type*}
    [Group G] [Ring Op]
    (α : SymmetryAction G Op) :=
  {pred : Op → Prop //
    ∀ g : G, ∀ x : Op,
      pred (α.act g x) ↔ pred x}

namespace InvariantPredicate

variable {G Op : Type*} [Group G] [Ring Op]
variable {α : SymmetryAction G Op}
variable (P : InvariantPredicate α)

abbrev pred : Op → Prop := P.1

theorem invariant
    (g : G) (x : Op) :
    P.pred (α.act g x) ↔ P.pred x :=
  P.2 g x

def mk
    (pred : Op → Prop)
    (invariant : ∀ g : G, ∀ x : Op,
      pred (α.act g x) ↔ pred x) :
    InvariantPredicate α :=
  ⟨pred, invariant⟩

end InvariantPredicate

/--
An invariant readout is a coordinate-independent observable of the operator
algebra.

Examples: trace-like quantities, index-like quantities, spectral multiplicities,
dimension readouts, entropy readouts.
-/
def InvariantReadout
    {G : Type uG} {Op : Type uOp}
    [Group G] [Ring Op]
    (α : SymmetryAction G Op)
    (β : Type uβ) :=
  {read : Op → β //
    ∀ g : G, ∀ x : Op,
      read (α.act g x) = read x}

namespace InvariantReadout

variable {G : Type uG} {Op : Type uOp}
variable [Group G] [Ring Op]
variable {α : SymmetryAction G Op} {β : Type uβ}
variable (R : InvariantReadout α β)

abbrev read : Op → β := R.1

theorem invariant
    (g : G) (x : Op) :
    R.read (α.act g x) = R.read x :=
  R.2 g x

def mk
    (read : Op → β)
    (invariant : ∀ g : G, ∀ x : Op,
      read (α.act g x) = read x) :
    InvariantReadout α β :=
  ⟨read, invariant⟩

end InvariantReadout

/--
An invariant binary pairing.

Examples: trace pairings, cyclic cocycles, metric pairings, intersection forms.
-/
def InvariantPairing
    {G : Type uG} {Op : Type uOp}
    [Group G] [Ring Op]
    (α : SymmetryAction G Op)
    (β : Type uβ) :=
  {pair : Op → Op → β //
    ∀ g : G, ∀ x y : Op,
      pair (α.act g x) (α.act g y) = pair x y}

namespace InvariantPairing

variable {G : Type uG} {Op : Type uOp}
variable [Group G] [Ring Op]
variable {α : SymmetryAction G Op} {β : Type uβ}
variable (P : InvariantPairing α β)

abbrev pair : Op → Op → β := P.1

theorem invariant
    (g : G) (x y : Op) :
    P.pair (α.act g x) (α.act g y) = P.pair x y :=
  P.2 g x y

def mk
    (pair : Op → Op → β)
    (invariant : ∀ g : G, ∀ x y : Op,
      pair (α.act g x) (α.act g y) = pair x y) :
    InvariantPairing α β :=
  ⟨pair, invariant⟩

end InvariantPairing

/--
A covariant readout between two symmetry representations.

This is the correct abstraction when a quantity transforms naturally rather
than being fixed.
-/
def CovariantReadout
    {G : Type uG} {Op : Type uOp} {β : Type uβ}
    [Group G] [Ring Op]
    (α : SymmetryAction G Op)
    (targetAct : G → β → β) :=
  {read : Op → β //
    ∀ g : G, ∀ x : Op,
      read (α.act g x) = targetAct g (read x)}

namespace CovariantReadout

variable {G : Type uG} {Op : Type uOp} {β : Type uβ}
variable [Group G] [Ring Op]
variable {α : SymmetryAction G Op}
variable {targetAct : G → β → β}
variable (R : CovariantReadout α targetAct)

abbrev read : Op → β := R.1

theorem covariance
    (g : G) (x : Op) :
    R.read (α.act g x) = targetAct g (R.read x) :=
  R.2 g x

def mk
    (read : Op → β)
    (covariance : ∀ g : G, ∀ x : Op,
      read (α.act g x) = targetAct g (read x)) :
    CovariantReadout α targetAct :=
  ⟨read, covariance⟩

end CovariantReadout

/-! ## 6. Defect loci as invariant subobjects inside one ambient algebra -/

/--
A defect locus is an invariant predicate inside the ambient operator algebra.

The defect is not a new universe or a new algebra. It is a symmetry-stable
subobject of the represented operator algebra.
-/
def DefectLocus
    {G : Type uG} {Op : Type uOp}
    [Group G] [Ring Op]
    (α : SymmetryAction G Op) :=
  {locus : Op → Prop //
    ∀ g : G, ∀ x : Op,
      locus (α.act g x) ↔ locus x}

namespace DefectLocus

variable {G : Type uG} {Op : Type uOp} [Group G] [Ring Op]
variable {α : SymmetryAction G Op}
variable (D : DefectLocus α)

abbrev locus : Op → Prop := D.1

theorem invariant
    (g : G) (x : Op) :
    D.locus (α.act g x) ↔ D.locus x :=
  D.2 g x

def mk
    (locus : Op → Prop)
    (invariant : ∀ g : G, ∀ x : Op,
      locus (α.act g x) ↔ locus x) :
    DefectLocus α :=
  ⟨locus, invariant⟩

end DefectLocus

/-- A defect locus supported by an invariant projector. -/
structure ProjectorSupportedDefect
    {G : Type uG} {Op : Type uOp}
    [Group G] [Ring Op]
    (α : SymmetryAction G Op) where
  projector : Op
  projector_invariant :
    IsInvariantProjector α projector

  defect : DefectLocus α

  supported :
    ∀ x : Op,
      defect.locus x →
        IsSupportedOn projector x

namespace ProjectorSupportedDefect

variable {G : Type uG} {Op : Type uOp}
variable [Group G] [Ring Op]
variable {α : SymmetryAction G Op}

/-- Projector-supported defects remain supported after applying a symmetry. -/
theorem supported_after_action
    (D : ProjectorSupportedDefect α)
    {x : Op}
    (hx : D.defect.locus x)
    (g : G) :
    IsSupportedOn D.projector (α.act g x) := by
  have hp : IsInvariant α D.projector :=
    D.projector_invariant.2
  have hs : IsSupportedOn D.projector x :=
    D.supported x hx
  exact Projector.supported_image α hp hs g

/-- The defect predicate itself is invariant. -/
theorem locus_after_action_iff
    (D : ProjectorSupportedDefect α)
    (g : G)
    (x : Op) :
    D.defect.locus (α.act g x) ↔ D.defect.locus x :=
  D.defect.invariant g x

end ProjectorSupportedDefect

/-! ## 7. Geometric-origin package -/

/--
A compact package for the operator-origin principle of geometry.

The visible geometry is reconstructed from:

* an ambient operator algebra;
* a symmetry action;
* invariant projectors;
* invariant defect predicates;
* invariant readouts and pairings.

Concrete modules can extend this with spectra, Drazin inverses, traces,
cyclic cocycles, Dirac operators, Siegel projectors, or automorphic data.
-/
structure GeometricOriginData
    (G : Type uG)
    (Op : Type uOp)
    [Group G] [Ring Op] where
  symmetry : SymmetryAction G Op

  projectorDecompositions :
    Set (InvariantProjectorDecomposition symmetry)

  defectPredicates :
    Set (DefectLocus symmetry)

  invariantPredicates :
    Set (InvariantPredicate symmetry)

/-! ## 8. Owner theorems -/

/--
Every symmetry action has a nonempty invariant subring: at least `0` and `1`
are invariant.
-/
theorem symmetryInvariantOwnerTarget :
  ∀ (G : Type uG) [Group G],
  ∀ (Op : Type uOp) [Ring Op],
  ∀ α : SymmetryAction G Op,
    IsInvariant α (1 : Op) := by
  intro G _ Op _ α
  exact IsInvariant.one α

/--
Every symmetry action has at least the trivial invariant projectors `0` and `1`.
-/
theorem invariantProjectorOwnerTarget :
  ∀ (G : Type uG) [Group G],
  ∀ (Op : Type uOp) [Ring Op],
  ∀ α : SymmetryAction G Op,
    IsInvariantProjector α (1 : Op) := by
  intro G _ Op _ α
  exact Projector.one_isInvariantProjector α

/-- Trivial invariant packet: unit lies in the invariant subring and is an invariant projector. -/
theorem trivialInvariant_unit_packet
    (G : Type uG) [Group G]
    (Op : Type uOp) [Ring Op]
    (α : SymmetryAction G Op) :
    (⟨1, IsInvariant.one α⟩ : invariantSubring α).val = 1 ∧
      IsInvariantProjector α (1 : Op) := by
  exact ⟨rfl, Projector.one_isInvariantProjector α⟩

/-! ## 9. Real-linear operator symmetry actions -/

/--
A real-linear multiplicative symmetry action on an operator algebra.

The action is deliberately bundled as a family of real-linear maps, plus
multiplicativity and group-action laws. This is enough to define invariant
operators as a submodule and to prove that products and commutators of
invariants are invariant.
-/
abbrev OperatorSymmetryAction
    (G : Type uG) (Op : Type uOp)
    [Group G] [Ring Op] [Algebra ℝ Op] :=
  ErlangenConformalInvariant.GroupAction G Op

namespace OperatorSymmetryAction

variable {G : Type uG} {Op : Type uOp}
variable [Group G] [Ring Op] [Algebra ℝ Op]

def act (S : OperatorSymmetryAction G Op) : G → Op ≃ₐ[ℝ] Op :=
  fun g => S.toFun g⁻¹

theorem act_id (S : OperatorSymmetryAction G Op) (x : Op) :
    S.act 1 x = x := by
  change S.toFun (1⁻¹) x = x
  simp only [inv_one]
  rw [S.map_one']
  rfl

theorem act_mul (S : OperatorSymmetryAction G Op)
    (g h : G) (x : Op) :
    S.act (g * h) x = S.act g (S.act h x) := by
  change S.toFun ((g * h)⁻¹) x =
    S.toFun g⁻¹ (S.toFun h⁻¹ x)
  rw [mul_inv_rev, S.map_mul']
  simp

theorem map_one (S : OperatorSymmetryAction G Op) (g : G) :
    S.act g 1 = 1 := (S.act g).map_one

theorem map_mul (S : OperatorSymmetryAction G Op)
    (g : G) (x y : Op) :
    S.act g (x * y) = S.act g x * S.act g y :=
  (S.act g).map_mul x y

end OperatorSymmetryAction

/-- Convert a linear operator symmetry action into a ring-automorphism action. -/
def toSymmetryAction
    {G : Type uG} {Op : Type uOp}
    [Group G] [Ring Op] [Algebra ℝ Op]
    (S : OperatorSymmetryAction G Op) : SymmetryAction G Op where
  act g := (S.act g).toRingEquiv
  act_one x := OperatorSymmetryAction.act_id S x
  act_mul g h x := OperatorSymmetryAction.act_mul S g h x

namespace OperatorSymmetryAction

variable
    {G : Type uG} {Op : Type uOp}
    [Group G] [Ring Op] [Algebra ℝ Op]

variable (S : OperatorSymmetryAction G Op)

@[simp]
theorem act_one_apply
    (x : Op) :
    S.act 1 x = x :=
  S.act_id x

theorem act_mul_apply
    (g h : G)
    (x : Op) :
    S.act (g * h) x = S.act g (S.act h x) :=
  S.act_mul g h x

@[simp]
theorem act_map_zero
    (g : G) :
    S.act g (0 : Op) = 0 := by
  simp

theorem act_map_sub
    (g : G)
    (x y : Op) :
    S.act g (x - y) = S.act g x - S.act g y :=
  (S.act g).map_sub x y

@[simp]
theorem act_smul
    (g : G)
    (c : ℝ)
    (x : Op) :
    S.act g (c • x) = c • S.act g x :=
  (S.act g).toLinearMap.map_smul c x

/-! ### Invariant operators -/

/-- An operator is invariant if every symmetry element fixes it. -/
def IsInvariant
    (x : Op) : Prop :=
  ∀ g : G, S.act g x = x

/-- The invariant operators form a real submodule of the ambient algebra. -/
def invariantSubmodule : Submodule ℝ Op where
  carrier := {x : Op | S.IsInvariant x}
  zero_mem' := by
    intro g
    simp
  add_mem' := by
    intro x y hx hy g
    calc
      S.act g (x + y) = S.act g x + S.act g y :=
        (S.act g).toLinearMap.map_add x y
      _ = x + y := by rw [hx g, hy g]
  smul_mem' := by
    intro a x hx g
    calc
      S.act g (a • x) = a • S.act g x :=
        (S.act g).toLinearMap.map_smul a x
      _ = a • x := by rw [hx g]

@[simp]
theorem mem_invariantSubmodule_iff
    (x : Op) :
    x ∈ S.invariantSubmodule ↔ S.IsInvariant x :=
  Iff.rfl

/-- Products of invariant operators are invariant. -/
theorem invariant_mul
    {x y : Op}
    (hx : S.IsInvariant x)
    (hy : S.IsInvariant y) :
    S.IsInvariant (x * y) := by
  intro g
  rw [S.map_mul g x y, hx g, hy g]

/-- The fixed-point law for invariant operators. -/
theorem invariant_act_eq
    {x : Op}
    (hx : S.IsInvariant x)
    (g : G) :
    S.act g x = x :=
  hx g

/-! ### Projectors and supported sectors -/

/-- An idempotent/projector in the ambient operator algebra. -/
def IsProjector
    (p : Op) : Prop :=
  p * p = p

/-- An invariant projector. -/
def IsInvariantProjector
    (p : Op) : Prop :=
  IsProjector p ∧ S.IsInvariant p

/-- A left support condition: `x` lies in the sector cut out by `p`. -/
def IsSupportedOn
    (p x : Op) : Prop :=
  p * x = x

/-- A two-sided support condition. -/
def IsTwoSidedSupportedOn
    (p x : Op) : Prop :=
  p * x = x ∧ x * p = x

/-- The image of a projector under a symmetry is again a projector. -/
theorem projector_after_action
    {p : Op}
    (hp : IsProjector p)
    (g : G) :
    IsProjector (S.act g p) := by
  dsimp [IsProjector]
  calc
    S.act g p * S.act g p
        = S.act g (p * p) := by
          exact (S.map_mul g p p).symm
    _ = S.act g p := by
          rw [hp]

/--
If `p` is invariant and `x` is supported on `p`, then every translate of `x`
is also supported on `p`.
-/
theorem supported_action_of_invariant_projector
    {p x : Op}
    (hp : S.IsInvariant p)
    (hx : IsSupportedOn p x)
    (g : G) :
    IsSupportedOn p (S.act g x) := by
  dsimp [IsSupportedOn]
  have h := congrArg (fun z : Op => S.act g z) hx
  change S.act g (p * x) = S.act g x at h
  rw [S.map_mul g p x, hp g] at h
  exact h

/--
If `p` and `x` are invariant, then the supported component `p * x` is
invariant.
-/
theorem invariant_supported_component
    {p x : Op}
    (hp : S.IsInvariant p)
    (hx : S.IsInvariant x) :
    S.IsInvariant (p * x) :=
  S.invariant_mul hp hx

/-! ### Commutators as invariant readouts -/

/-- The operator commutator. -/
def commutator
    (x y : Op) : Op :=
  x * y - y * x

omit [Algebra ℝ Op] in
@[simp]
theorem commutator_self
    (x : Op) :
    commutator x x = 0 := by
  simp [commutator]

/-- The commutator of invariant operators is invariant. -/
theorem invariant_commutator
    {x y : Op}
    (hx : S.IsInvariant x)
    (hy : S.IsInvariant y) :
    S.IsInvariant (commutator x y) := by
  intro g
  dsimp [commutator]
  rw [S.act_map_sub, S.map_mul g x y, S.map_mul g y x, hx g, hy g]

/-! ### Invariant complementary projector pairs -/

/--
A symmetry-invariant complementary pair of projectors.

This is the generic pattern behind Drazin core/nil splitting, boundary/cuspidal
splitting, chiral left/right splitting, and other projector geometries.
-/
structure InvariantProjectorPair where
  Pregular : Op
  Pdefect : Op

  regular_idem :
    Pregular * Pregular = Pregular

  defect_idem :
    Pdefect * Pdefect = Pdefect

  projector_sum :
    Pregular + Pdefect = 1

  regular_defect_disjoint :
    Pregular * Pdefect = 0

  defect_regular_disjoint :
    Pdefect * Pregular = 0

  regular_invariant :
    S.IsInvariant Pregular

  defect_invariant :
    S.IsInvariant Pdefect

namespace InvariantProjectorPair

variable
    {S : OperatorSymmetryAction G Op}

variable (P : S.InvariantProjectorPair)

/-- Every element decomposes on the left into regular and defect pieces. -/
theorem left_decomposition
    (x : Op) :
    P.Pregular * x + P.Pdefect * x = x := by
  calc
    P.Pregular * x + P.Pdefect * x
        = (P.Pregular + P.Pdefect) * x := by
          exact (add_mul P.Pregular P.Pdefect x).symm
    _ = 1 * x := by
          rw [P.projector_sum]
    _ = x := one_mul x

/-- Every element decomposes on the right into regular and defect pieces. -/
theorem right_decomposition
    (x : Op) :
    x * P.Pregular + x * P.Pdefect = x := by
  calc
    x * P.Pregular + x * P.Pdefect
        = x * (P.Pregular + P.Pdefect) := by
          exact (mul_add x P.Pregular P.Pdefect).symm
    _ = x * 1 := by
          rw [P.projector_sum]
    _ = x := mul_one x

/-- The regular component of an invariant element is invariant. -/
theorem regular_component_invariant
    {x : Op}
    (hx : S.IsInvariant x) :
    S.IsInvariant (P.Pregular * x) :=
  S.invariant_mul P.regular_invariant hx

/-- The defect component of an invariant element is invariant. -/
theorem defect_component_invariant
    {x : Op}
    (hx : S.IsInvariant x) :
    S.IsInvariant (P.Pdefect * x) :=
  S.invariant_mul P.defect_invariant hx

/-- The regular projector kills the defect branch on the left. -/
theorem regular_kills_left_defect
    (x : Op) :
    P.Pregular * (P.Pdefect * x) = 0 := by
  rw [← mul_assoc, P.regular_defect_disjoint, zero_mul]

/-- The defect projector kills the regular branch on the left. -/
theorem defect_kills_left_regular
    (x : Op) :
    P.Pdefect * (P.Pregular * x) = 0 := by
  rw [← mul_assoc, P.defect_regular_disjoint, zero_mul]

end InvariantProjectorPair

/-! ### Equivariant maps -/

/-- A linear map between two symmetry systems that commutes with the actions. -/
structure EquivariantLinearMap
    {Op₂ : Type uOp₂}
    [Ring Op₂] [Algebra ℝ Op₂]
    (S₂ : OperatorSymmetryAction G Op₂) where
  toLinearMap : Op →ₗ[ℝ] Op₂

  equivariant :
    ∀ (g : G) (x : Op),
      toLinearMap (S.act g x) =
        S₂.act g (toLinearMap x)

namespace EquivariantLinearMap

variable
    {S : OperatorSymmetryAction G Op}
    {Op₂ : Type uOp₂}
    [Ring Op₂] [Algebra ℝ Op₂]
    {S₂ : OperatorSymmetryAction G Op₂}

variable (F : S.EquivariantLinearMap S₂)

/-- Equivariant maps send invariant elements to invariant elements. -/
theorem maps_invariants_to_invariants
    {x : Op}
    (hx : S.IsInvariant x) :
    S₂.IsInvariant (F.toLinearMap x) := by
  intro g
  rw [← F.equivariant g x, hx g]

end EquivariantLinearMap

/-- A multiplicative equivariant map between operator algebras. -/
structure EquivariantAlgebraMap
    {Op₂ : Type uOp₂}
    [Ring Op₂] [Algebra ℝ Op₂]
    (S₂ : OperatorSymmetryAction G Op₂) where
  toLinearMap : Op →ₐ[ℝ] Op₂

  equivariant :
    ∀ (g : G) (x : Op),
      toLinearMap (S.act g x) =
        S₂.act g (toLinearMap x)

namespace EquivariantAlgebraMap

variable
    {S : OperatorSymmetryAction G Op}
    {Op₂ : Type uOp₂}
    [Ring Op₂] [Algebra ℝ Op₂]
    {S₂ : OperatorSymmetryAction G Op₂}

variable (F : S.EquivariantAlgebraMap S₂)

theorem map_one : F.toLinearMap 1 = 1 := F.toLinearMap.map_one

theorem map_mul (x y : Op) :
    F.toLinearMap (x * y) = F.toLinearMap x * F.toLinearMap y :=
  F.toLinearMap.map_mul x y

/-- Equivariant algebra maps send invariant elements to invariant elements. -/
theorem maps_invariants_to_invariants
    {x : Op}
    (hx : S.IsInvariant x) :
    S₂.IsInvariant (F.toLinearMap x) := by
  intro g
  rw [← F.equivariant g x, hx g]

/-- Equivariant algebra maps send projectors to projectors. -/
theorem maps_projector_to_projector
    {p : Op}
    (hp : IsProjector p) :
    IsProjector (F.toLinearMap p) := by
  dsimp [IsProjector] at hp ⊢
  rw [← EquivariantAlgebraMap.map_mul F p p, hp]

/-- Equivariant algebra maps send invariant projectors to invariant projectors. -/
theorem maps_invariant_projector_to_invariant_projector
    {p : Op}
    (hp : S.IsInvariantProjector p) :
    S₂.IsInvariantProjector (F.toLinearMap p) :=
  ⟨EquivariantAlgebraMap.maps_projector_to_projector F hp.1,
    EquivariantAlgebraMap.maps_invariants_to_invariants F hp.2⟩

/-- Equivariant algebra maps preserve commutators. -/
theorem map_commutator
    (x y : Op) :
    F.toLinearMap (commutator x y) =
      commutator (F.toLinearMap x) (F.toLinearMap y) := by
  dsimp [commutator]
  calc
    F.toLinearMap (x * y - y * x) =
        F.toLinearMap (x * y) - F.toLinearMap (y * x) :=
      F.toLinearMap.toLinearMap.map_sub (x * y) (y * x)
    _ = F.toLinearMap x * F.toLinearMap y -
          F.toLinearMap y * F.toLinearMap x := by
      rw [EquivariantAlgebraMap.map_mul F x y,
        EquivariantAlgebraMap.map_mul F y x]

end EquivariantAlgebraMap

/-! ### Invariant readouts -/

/--
An invariant readout is a scalar/categorical/geometric observable that is
unchanged by the chosen symmetry action.
-/
def InvariantReadout
    (Out : Type uOut) :=
  {read : Op → Out //
    ∀ (g : G) (x : Op),
      read (S.act g x) = read x}

namespace InvariantReadout

variable
    {Out : Type uOut}
    (R : S.InvariantReadout Out)

abbrev read : Op → Out := R.1

theorem invariant
    (g : G) (x : Op) :
    R.1 (S.act g x) = R.1 x :=
  R.2 g x

def mk
    (read : Op → Out)
    (invariant : ∀ (g : G) (x : Op),
      read (S.act g x) = read x) :
    S.InvariantReadout Out :=
  ⟨read, invariant⟩

/-- Re-export the readout invariance law. -/
theorem apply_action
    (g : G)
    (x : Op) :
    R.1 (S.act g x) = R.1 x :=
  R.2 g x

/-- Invariant elements evaluate trivially under the symmetry action. -/
theorem apply_invariant
    {x : Op}
    (hx : S.IsInvariant x)
    (g : G) :
    R.1 (S.act g x) = R.1 x := by
  rw [hx g]

end InvariantReadout

/-! ### Invariant sets and concrete sector sockets -/

/--
A subset of the ambient operator algebra is invariant if it is stable under
the symmetry action.
-/
def IsInvariantSet
    (A : Set Op) : Prop :=
  ∀ (g : G) {x : Op}, x ∈ A → S.act g x ∈ A

/-- The fixed operator set. -/
def fixedSet : Set Op :=
  {x : Op | S.IsInvariant x}

/-- Right support condition for a projector image. -/
def IsRightSupportedOn
    (p x : Op) : Prop :=
  x * p = x

/-- Two-sided support condition for a projector image. -/
def IsBiSupportedOn
    (p x : Op) : Prop :=
  IsSupportedOn p x ∧ IsRightSupportedOn p x

/-- The left projector image as a subset of the ambient algebra. -/
def leftImage
    (p : Op) : Set Op :=
  {x : Op | IsSupportedOn p x}

/-- The right projector image as a subset of the ambient algebra. -/
def rightImage
    (p : Op) : Set Op :=
  {x : Op | IsRightSupportedOn p x}

/-- The two-sided projector image as a subset of the ambient algebra. -/
def biImage
    (p : Op) : Set Op :=
  {x : Op | IsBiSupportedOn p x}

/--
If `p` is invariant, then the left image of `p` is invariant under the
symmetry action.
-/
theorem leftImage_invariant
    {p : Op}
    (hp : S.IsInvariant p) :
    S.IsInvariantSet (leftImage p) := by
  intro g x hx
  dsimp [leftImage, IsSupportedOn] at hx ⊢
  calc
    p * S.act g x
        = S.act g p * S.act g x := by rw [hp g]
    _ = S.act g (p * x) := by
        exact (S.map_mul g p x).symm
    _ = S.act g x := by rw [hx]

/-- If `p` is invariant, then the right image of `p` is invariant. -/
theorem rightImage_invariant
    {p : Op}
    (hp : S.IsInvariant p) :
    S.IsInvariantSet (rightImage p) := by
  intro g x hx
  dsimp [rightImage, IsRightSupportedOn] at hx ⊢
  calc
    S.act g x * p
        = S.act g x * S.act g p := by rw [hp g]
    _ = S.act g (x * p) := by
        exact (S.map_mul g x p).symm
    _ = S.act g x := by rw [hx]

/-- If `p` is invariant, then its two-sided image is invariant. -/
theorem biImage_invariant
    {p : Op}
    (hp : S.IsInvariant p) :
    S.IsInvariantSet (biImage p) := by
  intro g x hx
  exact ⟨
    S.leftImage_invariant hp g hx.1,
    S.rightImage_invariant hp g hx.2
  ⟩

/-! ### Invariant chiral polarization -/

/--
A circular polarization is invariant under a symmetry action if its chiral
involution is invariant.

The projectors then become invariant because they are defined from `χ`.
-/
def PreservesCircularPolarization
    (C : CircularPolarization Op) : Prop :=
  S.IsInvariant C.chi

/-- If the symmetry preserves `χ`, it preserves the left circular projector. -/
theorem invariant_P_left_of_preserves_chi
    (C : CircularPolarization Op)
    (hC : S.PreservesCircularPolarization C) :
    S.IsInvariant C.P_left := by
  intro g
  calc
    S.act g C.P_left
        = S.act g ((1 / 2 : ℝ) • ((1 : Op) + C.chi)) := by
          rw [C.P_left_def]
    _ = (1 / 2 : ℝ) • S.act g ((1 : Op) + C.chi) := by
          exact (S.act g).toLinearMap.map_smul _ _
    _ = (1 / 2 : ℝ) • ((1 : Op) + C.chi) := by
          congr 1
          calc
            S.act g ((1 : Op) + C.chi) = S.act g 1 + S.act g C.chi :=
              (S.act g).toLinearMap.map_add _ _
            _ = (1 : Op) + C.chi := by rw [S.map_one, hC g]
    _ = C.P_left := by
          exact C.P_left_def.symm

/-- If the symmetry preserves `χ`, it preserves the right circular projector. -/
theorem invariant_P_right_of_preserves_chi
    (C : CircularPolarization Op)
    (hC : S.PreservesCircularPolarization C) :
    S.IsInvariant C.P_right := by
  intro g
  have hsub :
    S.act g ((1 : Op) - C.chi) =
        (1 : Op) - C.chi := by
    calc
      S.act g ((1 : Op) - C.chi) =
          S.act g 1 - S.act g C.chi :=
        (S.act g).toLinearMap.map_sub _ _
      _ = (1 : Op) - C.chi := by rw [S.map_one, hC g]
  calc
    S.act g C.P_right
        = S.act g ((1 / 2 : ℝ) • ((1 : Op) - C.chi)) := by
          rw [C.P_right_def]
    _ = (1 / 2 : ℝ) • S.act g ((1 : Op) - C.chi) := by
          exact (S.act g).toLinearMap.map_smul _ _
    _ = (1 / 2 : ℝ) • ((1 : Op) - C.chi) := by
          rw [hsub]
    _ = C.P_right := by
          exact C.P_right_def.symm

/--
The left chiral sector is invariant under a symmetry preserving the circular
polarization.
-/
theorem leftChiralSector_invariant
    (C : CircularPolarization Op)
    (hC : S.PreservesCircularPolarization C) :
    S.IsInvariantSet (leftImage C.P_left) :=
  S.leftImage_invariant
    (S.invariant_P_left_of_preserves_chi C hC)

/--
The right chiral sector is invariant under a symmetry preserving the circular
polarization.
-/
theorem rightChiralSector_invariant
    (C : CircularPolarization Op)
    (hC : S.PreservesCircularPolarization C) :
    S.IsInvariantSet (leftImage C.P_right) :=
  S.leftImage_invariant
    (S.invariant_P_right_of_preserves_chi C hC)

/-! ### Invariant Drazin branches -/

/--
A Drazin projector pair is invariant if both the regular/core projector and
the nil/null projector are invariant.
-/
def PreservesDrazinProjectors
    (P : DrazinProjectorPair Op) : Prop :=
  S.IsInvariant P.Pcore ∧ S.IsInvariant P.Pnil

/-- The regular Drazin core branch is invariant. -/
theorem coreBranch_invariant
    (P : DrazinProjectorPair Op)
    (hP : S.PreservesDrazinProjectors P) :
    S.IsInvariantSet (leftImage P.Pcore) :=
  S.leftImage_invariant hP.1

/-- The nil/null Drazin branch is invariant. -/
theorem nilBranch_invariant
    (P : DrazinProjectorPair Op)
    (hP : S.PreservesDrazinProjectors P) :
    S.IsInvariantSet (leftImage P.Pnil) :=
  S.leftImage_invariant hP.2

/--
A symmetry-invariant Drazin split geometry: circular polarization plus
regular/nil projectors, all preserved by the symmetry action.
-/
structure InvariantDrazinGeometry where
  /-- Circular/chiral polarization. -/
  circular : CircularPolarization Op

  /-- Drazin core/null projectors. -/
  projectors : DrazinProjectorPair Op

  /-- The symmetry preserves the circular polarization. -/
  preserves_circular :
    S.PreservesCircularPolarization circular

  /-- The symmetry preserves the Drazin projectors. -/
  preserves_drazin :
    S.PreservesDrazinProjectors projectors

namespace InvariantDrazinGeometry

variable {S : OperatorSymmetryAction G Op}
variable (Geom : S.InvariantDrazinGeometry)

/-- The left chiral sector of an invariant Drazin geometry is invariant. -/
theorem left_chiral_invariant :
    S.IsInvariantSet (leftImage Geom.circular.P_left) :=
  S.leftChiralSector_invariant
    Geom.circular
    Geom.preserves_circular

/-- The right chiral sector of an invariant Drazin geometry is invariant. -/
theorem right_chiral_invariant :
    S.IsInvariantSet (leftImage Geom.circular.P_right) :=
  S.rightChiralSector_invariant
    Geom.circular
    Geom.preserves_circular

/-- The regular core branch of an invariant Drazin geometry is invariant. -/
theorem core_invariant :
    S.IsInvariantSet (leftImage Geom.projectors.Pcore) :=
  S.coreBranch_invariant
    Geom.projectors
    Geom.preserves_drazin

/-- The nil/null branch of an invariant Drazin geometry is invariant. -/
theorem nil_invariant :
    S.IsInvariantSet (leftImage Geom.projectors.Pnil) :=
  S.nilBranch_invariant
    Geom.projectors
    Geom.preserves_drazin

end InvariantDrazinGeometry

/--
Owner target for reconstructing geometry from invariant operator structure.

A future concrete theorem should instantiate this from a represented operator
system, a symmetry action, circular polarization, Drazin projectors, and
trace/weight/spectral readouts.
-/
@[owner_target_tag]
def GeometricOriginOwnerTarget : Prop :=
  ∃ S : OperatorSymmetryAction G Op,
  ∃ Geom : S.InvariantDrazinGeometry,
    S.IsInvariantSet (leftImage Geom.circular.P_left) ∧
      S.IsInvariantSet (leftImage Geom.circular.P_right) ∧
      S.IsInvariantSet (leftImage Geom.projectors.Pcore) ∧
      S.IsInvariantSet (leftImage Geom.projectors.Pnil)

end OperatorSymmetryAction

/-! ## 10. Linear operator-geometry origin datum -/

/--
A minimal operator-geometric origin datum.

This packages the ambient operator algebra with a symmetry action and a family
of readouts. Concrete geometry modules should refine this with spectra,
projectors, traces, cyclic cocycles, Drazin data, Siegel data, or metric data.
-/
structure OperatorGeometryOrigin
    (G : Type uG) (Op : Type uOp) [Group G] [Ring Op] [Algebra ℝ Op] where
  symmetry :
    OperatorSymmetryAction G Op

  /--
  Optional regular/defect projector pair, when a geometry supplies one.

  The owner includes the Drazin inverse and the resulting invariant regular,
  defect, and chiral projector geometry.
  -/
  projectorGeometry : Option symmetry.InvariantDrazinGeometry

namespace OperatorGeometryOrigin

variable {G : Type uG} {Op : Type uOp}
variable [Group G] [Ring Op] [Algebra ℝ Op]

/-- Historical readback derived from the presence of concrete projector
geometry rather than stored as an evidence marker. -/
def has_projector_geometry (O : OperatorGeometryOrigin G Op) : Prop :=
  O.projectorGeometry.isSome

theorem has_projector_geometry_iff_exists
    (O : OperatorGeometryOrigin G Op) :
    O.has_projector_geometry ↔
      ∃ geometry : O.symmetry.InvariantDrazinGeometry,
        O.projectorGeometry = some geometry := by
  cases h : O.projectorGeometry with
  | none =>
      simp [has_projector_geometry, h]
  | some geometry =>
      simp [has_projector_geometry, h]

end OperatorGeometryOrigin

/--
The formal slogan as a proposition schema:

A geometry has an invariant operator origin when it is supplied with a symmetry
action on one fixed ambient operator algebra.
-/
def HasInvariantOperatorOrigin
    (G : Type uG) (Op : Type uOp)
    [Group G] [Ring Op] [Algebra ℝ Op] : Prop :=
  ∃ S : OperatorSymmetryAction G Op,
    (∀ x : Op, S.act 1 x = x)
      ∧ (∀ (g h : G) (x : Op), S.act (g * h) x = S.act g (S.act h x))
      ∧ (∀ g : G, S.act g (1 : Op) = 1)
      ∧ (∀ (g : G) (x y : Op), S.act g (x * y) = S.act g x * S.act g y)

theorem hasInvariantOperatorOrigin_of_operatorSymmetryAction
    (G : Type uG) (Op : Type uOp)
    [Group G] [Ring Op] [Algebra ℝ Op]
    (S : OperatorSymmetryAction G Op) :
    HasInvariantOperatorOrigin G Op := by
  exact ⟨S, S.act_id, S.act_mul, S.map_one, S.map_mul⟩

end InfoGeometry.OperatorAlgebra
