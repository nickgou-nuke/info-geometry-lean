/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.OperatorAlgebra.ChiralPolarization
import InfoGeometry.OperatorAlgebra.DrazinRepresentedSplit
import InfoGeometry.OperatorAlgebra.ErlangenConformalInvariant
import InfoGeometry.Meta.OwnerTarget

/-!
# InfoGeometry.OperatorAlgebra.SymmetryInvariants

Symmetry-invariant operator structures and theorems.

Principle:

  observed geometry = invariant or equivariant operator data.

This file formalizes the general algebraic layer underneath the later
PhaseErlanger, Drazin, Siegel, spectral, and automorphic modules.

The ambient object is a represented operator algebra `Op` with a symmetry
action by ring automorphisms. Geometry is then reconstructed from invariant
operators, invariant projectors, supported sectors, invariant predicates,
readouts, pairings, and projector decompositions.

### Three-Bucket Audit Map (`audit-proof` Policy)

#### BUCKET 1 — Proved Kernel Content
- `SymmetryAction` algebraic laws (`act_inv_act`, `act_act_inv`),
- `IsInvariant` subring closure (`invariantSubring`),
- `Projector` invariance and support transport (`supported_image_iff`, `biSupported_image`),
- `ComplementaryProjectors` decomposition (`left_decomposition`, `pComponent_supported`, `qComponent_supported`),
- `OperatorSymmetryAction` real-linear invariance, commutator invariance (`invariant_commutator`),
  equivariant algebra-map preservation (`maps_projector_to_projector`, `map_commutator`),
  chiral polarization invariance (`invariant_P_left_of_preserves_chi`, `invariant_P_right_of_preserves_chi`),
  and Drazin branch invariance (`coreBranch_invariant`, `nilBranch_invariant`).

#### BUCKET 2 — Conditional / Interface Boundaries
- Requires `[Group G]`, `[Ring Op]`, and (in Section 7) `[Algebra ℝ Op]`.

#### BUCKET 3 — Open / Unformalized
- Infinite-dimensional spectral decompositions beyond algebraic projectors.
-/

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

/-- Trivial symmetry action where every group element acts by the identity ring automorphism. -/
instance instInhabitedSymmetryAction {G : Type uG} {Op : Type uOp} [Group G] [Ring Op] :
    Inhabited (SymmetryAction G Op) :=
  ⟨{ act := fun _ => RingEquiv.refl Op
     act_one := fun _ => rfl
     act_mul := fun _ _ _ => rfl }⟩

namespace SymmetryAction

variable {G Op : Type*} [Group G] [Ring Op]
variable (α : SymmetryAction G Op)

/-- The identity group element acts as the identity on `Op`. -/
@[simp]
theorem act_one_apply
    (x : Op) :
    α.act 1 x = x := by
  have h := α.act_one x
  exact h

/-- Group multiplication acts by composition on `Op`. -/
@[simp]
theorem act_mul_apply
    (g h : G)
    (x : Op) :
    α.act (g * h) x = α.act g (α.act h x) := by
  have h0 := α.act_mul g h x
  exact h0

/-- Every symmetry element preserves `0`. -/
@[simp]
theorem act_zero
    (g : G) :
    α.act g (0 : Op) = 0 := by
  simp

/-- Every symmetry element preserves `1`. -/
@[simp]
theorem act_one_ring
    (g : G) :
    α.act g (1 : Op) = 1 := by
  simp

/-- Every symmetry element preserves addition. -/
@[simp]
theorem act_add
    (g : G)
    (x y : Op) :
    α.act g (x + y) = α.act g x + α.act g y := by
  simp

/-- Every symmetry element commutes with negation. -/
@[simp]
theorem act_neg
    (g : G)
    (x : Op) :
    α.act g (-x) = -α.act g x := by
  simp

/-- Every symmetry element preserves subtraction. -/
@[simp]
theorem act_sub
    (g : G)
    (x y : Op) :
    α.act g (x - y) = α.act g x - α.act g y := by
  simp [sub_eq_add_neg]

/-- Every symmetry element preserves multiplication. -/
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

/-- Membership in `invariantSubring α` is equivalent to `IsInvariant α`. -/
@[simp]
theorem mem_invariantSubring_iff
    {G Op : Type*} [Group G] [Ring Op]
    (α : SymmetryAction G Op)
    (x : Op) :
    x ∈ invariantSubring α ↔ IsInvariant α x := by
  constructor <;> intro h <;> exact h

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

/-- The identity operator `1` is a projector (`1 * 1 = 1`). -/
theorem one_isProjector :
    IsProjector (1 : Op) := by
  simp [IsProjector]

/-- The zero operator `0` is a projector (`0 * 0 = 0`). -/
theorem zero_isProjector :
    IsProjector (0 : Op) := by
  simp [IsProjector]

/-- The identity operator `1` is an invariant projector. -/
theorem one_isInvariantProjector :
    IsInvariantProjector α (1 : Op) := by
  dsimp [IsInvariantProjector]
  exact ⟨one_isProjector, IsInvariant.one α⟩

/-- The zero operator `0` is an invariant projector. -/
theorem zero_isInvariantProjector :
    IsInvariantProjector α (0 : Op) := by
  dsimp [IsInvariantProjector]
  exact ⟨zero_isProjector, IsInvariant.zero α⟩

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
    IsBiSupportedOn p (α.act g x) := by
  dsimp [IsBiSupportedOn]
  exact ⟨supported_image α hp hx.1 g, right_supported_image α hp hx.2 g⟩

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

/-- Trivial complementary projector pair `(1, 0)` in any ring `Op`. -/
instance instInhabitedComplementaryProjectors {Op : Type uOp} [Ring Op] :
    Inhabited (ComplementaryProjectors Op) :=
  ⟨{ p := 1
     q := 0
     p_idempotent := Projector.one_isProjector
     q_idempotent := Projector.zero_isProjector
     sum_eq_one := add_zero 1
     pq_zero := mul_zero 1
     qp_zero := zero_mul 1 }⟩

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

/-- For an invariant projector `P.p`, the `p`-sector support condition is invariant under `α.act g`. -/
theorem p_supported_image_iff
    {G : Type*} [Group G]
    (α : SymmetryAction G Op)
    (P : ComplementaryProjectors Op)
    (hp : IsInvariant α P.p)
    (g : G)
    (x : Op) :
    IsSupportedOn P.p (α.act g x) ↔
      IsSupportedOn P.p x := by
  have h := Projector.supported_image_iff α hp g (x := x)
  exact h

/-- For an invariant projector `P.q`, the `q`-sector support condition is invariant under `α.act g`. -/
theorem q_supported_image_iff
    {G : Type*} [Group G]
    (α : SymmetryAction G Op)
    (P : ComplementaryProjectors Op)
    (hq : IsInvariant α P.q)
    (g : G)
    (x : Op) :
    IsSupportedOn P.q (α.act g x) ↔
      IsSupportedOn P.q x := by
  have h := Projector.supported_image_iff α hq g (x := x)
  exact h

end ComplementaryProjectors

/-! ## 5. Owner theorems -/

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

/-! ## 6. Real-linear operator symmetry actions -/

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

/-- Left group action on `Op` induced by `S.toFun g⁻¹`. -/
def act (S : OperatorSymmetryAction G Op) : G → Op ≃ₐ[ℝ] Op :=
  fun g => S.toFun g⁻¹

/-- The identity group element acts as the identity on `Op`. -/
theorem act_id (S : OperatorSymmetryAction G Op) (x : Op) :
    S.act 1 x = x := by
  change S.toFun (1⁻¹) x = x
  simp only [inv_one]
  rw [S.map_one']
  rfl

/-- Group multiplication acts by composition on `Op`. -/
theorem act_mul (S : OperatorSymmetryAction G Op)
    (g h : G) (x : Op) :
    S.act (g * h) x = S.act g (S.act h x) := by
  change S.toFun ((g * h)⁻¹) x =
    S.toFun g⁻¹ (S.toFun h⁻¹ x)
  rw [mul_inv_rev, S.map_mul']
  simp

/-- Each symmetry element preserves the identity `1 : Op`. -/
theorem map_one (S : OperatorSymmetryAction G Op) (g : G) :
    S.act g 1 = 1 := by
  have h := (S.act g).map_one
  exact h

/-- Each symmetry element preserves multiplication on `Op`. -/
theorem map_mul (S : OperatorSymmetryAction G Op)
    (g : G) (x y : Op) :
    S.act g (x * y) = S.act g x * S.act g y := by
  have h := (S.act g).map_mul x y
  exact h

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

/-- Applying `S.act 1` fixes `x`. -/
@[simp]
theorem act_one_apply
    (x : Op) :
    S.act 1 x = x := by
  have h := S.act_id x
  exact h

/-- Applying `S.act (g * h)` composes `S.act g` and `S.act h`. -/
theorem act_mul_apply
    (g h : G)
    (x : Op) :
    S.act (g * h) x = S.act g (S.act h x) := by
  have h0 := S.act_mul g h x
  exact h0

/-- Each symmetry element maps `0` to `0`. -/
@[simp]
theorem act_map_zero
    (g : G) :
    S.act g (0 : Op) = 0 := by
  simp

/-- Each symmetry element distributes over subtraction. -/
theorem act_map_sub
    (g : G)
    (x y : Op) :
    S.act g (x - y) = S.act g x - S.act g y := by
  have h := (S.act g).map_sub x y
  exact h

/-- Each symmetry element commutes with real scalar multiplication. -/
@[simp]
theorem act_smul
    (g : G)
    (c : ℝ)
    (x : Op) :
    S.act g (c • x) = c • S.act g x := by
  have h := (S.act g).toLinearMap.map_smul c x
  exact h

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

/-- Membership in `S.invariantSubmodule` is equivalent to `S.IsInvariant`. -/
@[simp]
theorem mem_invariantSubmodule_iff
    (x : Op) :
    x ∈ S.invariantSubmodule ↔ S.IsInvariant x := by
  constructor <;> intro h <;> exact h

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
    S.act g x = x := by
  dsimp [IsInvariant] at hx
  exact hx g

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
/-- The commutator of any operator with itself vanishes. -/
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

/-! ### Equivariant algebra maps -/

/-- Equivariant linear maps send invariant elements to invariant elements. -/
theorem maps_invariants_to_invariants
    {Op₂ : Type uOp₂} [Ring Op₂] [Algebra ℝ Op₂]
    (S₂ : OperatorSymmetryAction G Op₂)
    (F : Op →ₗ[ℝ] Op₂)
    (heq : ∀ (g : G) (x : Op), F (S.act g x) = S₂.act g (F x))
    {x : Op}
    (hx : S.IsInvariant x) :
    S₂.IsInvariant (F x) := by
  intro g
  rw [← heq g x, hx g]

/-- Algebra homomorphisms send projectors to projectors. -/
theorem maps_projector_to_projector
    {Op₂ : Type uOp₂} [Ring Op₂] [Algebra ℝ Op₂]
    (F : Op →ₐ[ℝ] Op₂)
    {p : Op}
    (hp : IsProjector p) :
    IsProjector (F p) := by
  dsimp [IsProjector] at hp ⊢
  rw [← _root_.map_mul F p p, hp]

/-- Algebra homomorphisms preserve commutators. -/
theorem map_commutator
    {Op₂ : Type uOp₂} [Ring Op₂] [Algebra ℝ Op₂]
    (F : Op →ₐ[ℝ] Op₂)
    (x y : Op) :
    F (commutator x y) = commutator (F x) (F y) := by
  dsimp [commutator]
  rw [map_sub, _root_.map_mul F x y, _root_.map_mul F y x]

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
    S.IsInvariantSet (leftImage C.P_left) := by
  have h := S.leftImage_invariant (S.invariant_P_left_of_preserves_chi C hC)
  exact h

/--
The right chiral sector is invariant under a symmetry preserving the circular
polarization.
-/
theorem rightChiralSector_invariant
    (C : CircularPolarization Op)
    (hC : S.PreservesCircularPolarization C) :
    S.IsInvariantSet (leftImage C.P_right) := by
  have h := S.leftImage_invariant (S.invariant_P_right_of_preserves_chi C hC)
  exact h

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
    S.IsInvariantSet (leftImage P.Pcore) := by
  have h := S.leftImage_invariant hP.1
  exact h

/-- The nil/null Drazin branch is invariant. -/
theorem nilBranch_invariant
    (P : DrazinProjectorPair Op)
    (hP : S.PreservesDrazinProjectors P) :
    S.IsInvariantSet (leftImage P.Pnil) := by
  have h := S.leftImage_invariant hP.2
  exact h

end OperatorSymmetryAction

/-- Every real-linear `OperatorSymmetryAction` yields a ring-automorphism `SymmetryAction` whose unit is an invariant projector. -/
theorem hasInvariantOperatorOrigin_of_operatorSymmetryAction
    {G : Type uG} {Op : Type uOp}
    [Group G] [Ring Op] [Algebra ℝ Op]
    (S : OperatorSymmetryAction G Op) :
    IsInvariantProjector (toSymmetryAction S) (1 : Op) := by
  have h := Projector.one_isInvariantProjector (toSymmetryAction S)
  exact h

end InfoGeometry.OperatorAlgebra
