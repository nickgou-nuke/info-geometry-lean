/-
InfoGeometry/OperatorAlgebra/ClosureInvolution.lean

Fixed equalizers for closure involutions.

This module records the strict algebraic survivor of a closure symmetry:

  survivor = {x | theta x = x}.

Layer-specific names such as center, Tomita fixed vector, grade-zero sector,
Majorana diagonal, winding invariant, or BPS survivor require additional
witnesses.  The base theorem here is only the linear fixed/anti-fixed
decomposition induced by an involution.

The projection formulas use division by `2`, so this module is intentionally
over `ℝ`.  Generalizing to other scalar rings would require an explicit
invertibility-of-two hypothesis.
-/

import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra

noncomputable section

namespace InfoGeometry.OperatorAlgebra.ClosureInvolution

/--
A linear closure involution.

Intended examples include charge conjugation `e⁻ ↔ e⁺`, grade reversal
`g₋k ↔ g₊k`, and linearized Tomita/Möbius closure symmetries.
-/
structure LinearClosureInvolution
    (V : Type*) [AddCommGroup V] [Module ℝ V] where
  /-- The closure symmetry. -/
  theta : V →ₗ[ℝ] V

  /-- The closure symmetry squares to the identity. -/
  theta_involutive :
    ∀ v : V, theta (theta v) = v

namespace LinearClosureInvolution

variable
    {V : Type*} [AddCommGroup V] [Module ℝ V]

variable (C : LinearClosureInvolution V)

/-- Fixed points of the closure involution. -/
def Fixed : Submodule ℝ V where
  carrier := {v : V | C.theta v = v}
  zero_mem' := by
    simp
  add_mem' := by
    intro x y hx hy
    dsimp at hx hy ⊢
    rw [C.theta.map_add, hx, hy]
  smul_mem' := by
    intro a x hx
    dsimp at hx ⊢
    rw [C.theta.map_smul, hx]

/-- Anti-fixed points of the closure involution. -/
def AntiFixed : Submodule ℝ V where
  carrier := {v : V | C.theta v = -v}
  zero_mem' := by
    simp
  add_mem' := by
    intro x y hx hy
    dsimp at hx hy ⊢
    rw [C.theta.map_add, hx, hy]
    abel
  smul_mem' := by
    intro a x hx
    dsimp at hx ⊢
    rw [C.theta.map_smul, hx]
    simp

/-- Membership in the fixed sector is exactly invariance under `theta`. -/
theorem mem_fixed_iff
    (v : V) :
    v ∈ C.Fixed ↔ C.theta v = v :=
  Iff.rfl

/-- Membership in the anti-fixed sector is exactly sign reversal under `theta`. -/
theorem mem_antiFixed_iff
    (v : V) :
    v ∈ C.AntiFixed ↔ C.theta v = -v :=
  Iff.rfl

/-- Pointwise form of involutivity. -/
theorem theta_theta
    (v : V) :
    C.theta (C.theta v) = v :=
  C.theta_involutive v

/-- If `v` is fixed, then `θ v = v`. -/
theorem theta_eq_self_of_fixed
    {v : V}
    (hv : v ∈ C.Fixed) :
    C.theta v = v :=
  (C.mem_fixed_iff v).mp hv

/-- If `v` is anti-fixed, then `θ v = -v`. -/
theorem theta_eq_neg_of_antiFixed
    {v : V}
    (hv : v ∈ C.AntiFixed) :
    C.theta v = -v :=
  (C.mem_antiFixed_iff v).mp hv

/--
If `theta` swaps `x` and `y`, then the diagonal `x + y` survives.
-/
theorem diagonal_fixed_of_swap
    {x y : V}
    (hxy : C.theta x = y)
    (hyx : C.theta y = x) :
    x + y ∈ C.Fixed := by
  change C.theta (x + y) = x + y
  rw [C.theta.map_add, hxy, hyx]
  abel

/--
If `theta` swaps `x` and `y`, then the difference `x - y` is anti-fixed.
-/
theorem difference_antiFixed_of_swap
    {x y : V}
    (hxy : C.theta x = y)
    (hyx : C.theta y = x) :
    x - y ∈ C.AntiFixed := by
  change C.theta (x - y) = -(x - y)
  rw [C.theta.map_sub, hxy, hyx]
  abel

/--
If `theta` swaps `x` and `y`, then the difference transforms by a minus sign.
-/
theorem difference_anti_fixed_of_swap
    {x y : V}
    (hxy : C.theta x = y)
    (hyx : C.theta y = x) :
    C.theta (x - y) = -(x - y) :=
  (C.mem_antiFixed_iff (x - y)).mp
    (C.difference_antiFixed_of_swap hxy hyx)

/--
Every element maps to a fixed diagonal after adding its closure image.
-/
theorem diagonal_with_image_fixed
    (x : V) :
    x + C.theta x ∈ C.Fixed := by
  apply C.diagonal_fixed_of_swap
  · rfl
  · exact C.theta_involutive x

/--
The closure anti-diagonal is anti-fixed.
-/
theorem anti_diagonal_with_image
    (x : V) :
    x - C.theta x ∈ C.AntiFixed := by
  apply C.difference_antiFixed_of_swap
  · rfl
  · exact C.theta_involutive x

/--
The closure anti-diagonal transforms by a minus sign.
-/
theorem theta_anti_diagonal_with_image
    (x : V) :
    C.theta (x - C.theta x) = -(x - C.theta x) :=
  (C.mem_antiFixed_iff (x - C.theta x)).mp
    (C.anti_diagonal_with_image x)

/-- Fixed/Majorana part of an element. -/
def fixedPart
    (x : V) : V :=
  (1 / 2 : ℝ) • (x + C.theta x)

/-- Anti-fixed/chiral-imbalance part of an element. -/
def antiPart
    (x : V) : V :=
  (1 / 2 : ℝ) • (x - C.theta x)

/-- The fixed part lies in the fixed sector. -/
theorem fixedPart_mem
    (x : V) :
    C.fixedPart x ∈ C.Fixed := by
  unfold fixedPart
  exact C.Fixed.smul_mem (1 / 2 : ℝ) (C.diagonal_with_image_fixed x)

/-- The anti-fixed part lies in the anti-fixed sector. -/
theorem antiPart_mem
    (x : V) :
    C.antiPart x ∈ C.AntiFixed := by
  unfold antiPart
  exact C.AntiFixed.smul_mem (1 / 2 : ℝ) (C.anti_diagonal_with_image x)

/-- The anti-fixed part is anti-invariant. -/
theorem antiPart_anti_fixed
    (x : V) :
    C.theta (C.antiPart x) = -C.antiPart x :=
  (C.mem_antiFixed_iff (C.antiPart x)).mp (C.antiPart_mem x)

/-- The fixed part is invariant. -/
theorem theta_fixedPart
    (x : V) :
    C.theta (C.fixedPart x) = C.fixedPart x :=
  (C.mem_fixed_iff (C.fixedPart x)).mp (C.fixedPart_mem x)

/-- The anti-fixed part is anti-invariant. -/
theorem theta_antiPart
    (x : V) :
    C.theta (C.antiPart x) = -C.antiPart x :=
  C.antiPart_anti_fixed x

/-- The fixed projection is invariant under applying `theta` to the input. -/
theorem fixedPart_theta
    (x : V) :
    C.fixedPart (C.theta x) = C.fixedPart x := by
  unfold fixedPart
  rw [C.theta_involutive x]
  module

/-- The anti-fixed projection changes sign under applying `theta` to the input. -/
theorem antiPart_theta
    (x : V) :
    C.antiPart (C.theta x) = -C.antiPart x := by
  unfold antiPart
  rw [C.theta_involutive x]
  module

/--
Every element decomposes into its fixed and anti-fixed parts.
-/
theorem fixed_add_anti_decomposition
    (x : V) :
    C.fixedPart x + C.antiPart x = x := by
  unfold fixedPart antiPart
  module

/-- The closure image is the fixed part minus the anti-fixed part. -/
theorem fixed_sub_anti_decomposition
    (x : V) :
    C.fixedPart x - C.antiPart x = C.theta x := by
  unfold fixedPart antiPart
  module

/-- The fixed projection is identity on fixed elements. -/
theorem fixedPart_eq_self_of_fixed
    {x : V}
    (hx : x ∈ C.Fixed) :
    C.fixedPart x = x := by
  have htheta : C.theta x = x :=
    (C.mem_fixed_iff x).mp hx
  unfold fixedPart
  rw [htheta]
  module

/-- The anti-fixed projection vanishes on fixed elements. -/
theorem antiPart_eq_zero_of_fixed
    {x : V}
    (hx : x ∈ C.Fixed) :
    C.antiPart x = 0 := by
  have htheta : C.theta x = x :=
    (C.mem_fixed_iff x).mp hx
  unfold antiPart
  rw [htheta]
  module

/-- The fixed projection vanishes on anti-fixed elements. -/
theorem fixedPart_eq_zero_of_antiFixed
    {x : V}
    (hx : x ∈ C.AntiFixed) :
    C.fixedPart x = 0 := by
  have htheta : C.theta x = -x :=
    (C.mem_antiFixed_iff x).mp hx
  unfold fixedPart
  rw [htheta]
  module

/-- The anti-fixed projection is identity on anti-fixed elements. -/
theorem antiPart_eq_self_of_antiFixed
    {x : V}
    (hx : x ∈ C.AntiFixed) :
    C.antiPart x = x := by
  have htheta : C.theta x = -x :=
    (C.mem_antiFixed_iff x).mp hx
  unfold antiPart
  rw [htheta]
  module

/-- The fixed projection is idempotent. -/
theorem fixedPart_idempotent
    (x : V) :
    C.fixedPart (C.fixedPart x) = C.fixedPart x :=
  C.fixedPart_eq_self_of_fixed (C.fixedPart_mem x)

/-- The anti-fixed projection is idempotent. -/
theorem antiPart_idempotent
    (x : V) :
    C.antiPart (C.antiPart x) = C.antiPart x :=
  C.antiPart_eq_self_of_antiFixed (C.antiPart_mem x)

/-- The fixed projection kills the anti-fixed projection. -/
theorem fixedPart_antiPart_eq_zero
    (x : V) :
    C.fixedPart (C.antiPart x) = 0 :=
  C.fixedPart_eq_zero_of_antiFixed (C.antiPart_mem x)

/-- The anti-fixed projection kills the fixed projection. -/
theorem antiPart_fixedPart_eq_zero
    (x : V) :
    C.antiPart (C.fixedPart x) = 0 :=
  C.antiPart_eq_zero_of_fixed (C.fixedPart_mem x)

/--
A submodule is setwise stable under the closure involution.

This is weaker than pointwise survival: `theta` may preserve a sector while
moving its individual elements.
-/
def SetwiseStable
    (S : Submodule ℝ V) : Prop :=
  ∀ v : V, v ∈ S → C.theta v ∈ S

/-- Fixed elements in a stable sector are genuine pointwise survivors. -/
theorem fixed_mem_of_stable
    {S : Submodule ℝ V}
    (_hS : C.SetwiseStable S)
    {v : V}
    (hv : v ∈ S)
    (hfix : v ∈ C.Fixed) :
    v ∈ S ∧ C.theta v = v :=
  ⟨hv, (C.mem_fixed_iff v).mp hfix⟩

/-- Setwise stability gives membership of the closure image, not pointwise fixedness. -/
theorem image_mem_of_stable
    {S : Submodule ℝ V}
    (hS : C.SetwiseStable S)
    {v : V}
    (hv : v ∈ S) :
    C.theta v ∈ S :=
  hS v hv

/--
If a sector is setwise stable and contains `v`, then it contains the fixed
projection of `v`.
-/
theorem fixedPart_mem_of_stable
    {S : Submodule ℝ V}
    (hS : C.SetwiseStable S)
    {v : V}
    (hv : v ∈ S) :
    C.fixedPart v ∈ S := by
  unfold fixedPart
  exact S.smul_mem (1 / 2 : ℝ)
    (S.add_mem hv (hS v hv))

/--
If a sector is setwise stable and contains `v`, then it contains the anti-fixed
projection of `v`.
-/
theorem antiPart_mem_of_stable
    {S : Submodule ℝ V}
    (hS : C.SetwiseStable S)
    {v : V}
    (hv : v ∈ S) :
    C.antiPart v ∈ S := by
  unfold antiPart
  exact S.smul_mem (1 / 2 : ℝ)
    (S.sub_mem hv (hS v hv))

/--
A setwise-stable sector contains both closure projections of each of its
elements.
-/
theorem projections_mem_of_stable
    {S : Submodule ℝ V}
    (hS : C.SetwiseStable S)
    {v : V}
    (hv : v ∈ S) :
    C.fixedPart v ∈ S ∧ C.antiPart v ∈ S :=
  ⟨C.fixedPart_mem_of_stable hS hv,
    C.antiPart_mem_of_stable hS hv⟩

/-! ## Projection operators and constructive splitting -/

/--
Linear projection onto the fixed sector.

This is the constructive projector `P₊ x = (1 / 2) • (x + θ x)`.
-/
def fixedProjection : V →ₗ[ℝ] V where
  toFun := fun x => C.fixedPart x
  map_add' := by
    intro x y
    unfold fixedPart
    rw [C.theta.map_add]
    module
  map_smul' := by
    intro a x
    unfold fixedPart
    rw [C.theta.map_smul]
    simp [smul_add, smul_smul, mul_comm]

/--
Linear projection onto the anti-fixed sector.

This is the constructive projector `P₋ x = (1 / 2) • (x - θ x)`.
-/
def antiProjection : V →ₗ[ℝ] V where
  toFun := fun x => C.antiPart x
  map_add' := by
    intro x y
    unfold antiPart
    rw [C.theta.map_add]
    module
  map_smul' := by
    intro a x
    unfold antiPart
    rw [C.theta.map_smul]
    simp [smul_sub, smul_smul, mul_comm]

@[simp]
theorem fixedProjection_apply
    (x : V) :
    C.fixedProjection x = C.fixedPart x :=
  rfl

@[simp]
theorem antiProjection_apply
    (x : V) :
    C.antiProjection x = C.antiPart x :=
  rfl

/-- The fixed projection lands in the fixed sector. -/
theorem fixedProjection_mem_fixed
    (x : V) :
    C.fixedProjection x ∈ C.Fixed :=
  C.fixedPart_mem x

/-- The anti projection lands in the anti-fixed sector. -/
theorem antiProjection_mem_antiFixed
    (x : V) :
    C.antiProjection x ∈ C.AntiFixed :=
  C.antiPart_mem x

/-- The fixed projection is idempotent. -/
theorem fixedProjection_idempotent
    (x : V) :
    C.fixedProjection (C.fixedProjection x) = C.fixedProjection x :=
  C.fixedPart_idempotent x

/-- The anti-fixed projection is idempotent. -/
theorem antiProjection_idempotent
    (x : V) :
    C.antiProjection (C.antiProjection x) = C.antiProjection x :=
  C.antiPart_idempotent x

/-- The fixed projection kills the anti-fixed projection. -/
theorem fixedProjection_antiProjection_eq_zero
    (x : V) :
    C.fixedProjection (C.antiProjection x) = 0 :=
  C.fixedPart_antiPart_eq_zero x

/-- The anti-fixed projection kills the fixed projection. -/
theorem antiProjection_fixedProjection_eq_zero
    (x : V) :
    C.antiProjection (C.fixedProjection x) = 0 :=
  C.antiPart_fixedPart_eq_zero x

/-- The two projection maps add to the identity. -/
theorem fixedProjection_add_antiProjection
    (x : V) :
    C.fixedProjection x + C.antiProjection x = x :=
  C.fixed_add_anti_decomposition x

/-- The closure involution is the fixed projection minus the anti-fixed projection. -/
theorem fixedProjection_sub_antiProjection
    (x : V) :
    C.fixedProjection x - C.antiProjection x = C.theta x :=
  C.fixed_sub_anti_decomposition x

/-- The fixed projection is fixed under `theta`. -/
theorem theta_fixedProjection
    (x : V) :
    C.theta (C.fixedProjection x) = C.fixedProjection x :=
  C.theta_fixedPart x

/-- The anti-fixed projection changes sign under `theta`. -/
theorem theta_antiProjection
    (x : V) :
    C.theta (C.antiProjection x) = -C.antiProjection x :=
  C.theta_antiPart x

/-- Projection form of `fixedPart_theta`. -/
theorem fixedProjection_theta
    (x : V) :
    C.fixedProjection (C.theta x) = C.fixedProjection x := by
  simpa using C.fixedPart_theta x

/-- Projection form of `antiPart_theta`. -/
theorem antiProjection_theta
    (x : V) :
    C.antiProjection (C.theta x) = -C.antiProjection x := by
  simpa using C.antiPart_theta x

/-- The range of the fixed projection is exactly the fixed sector. -/
theorem range_fixedProjection_eq_fixed :
    LinearMap.range C.fixedProjection = C.Fixed := by
  apply le_antisymm
  · intro y hy
    rcases hy with ⟨x, hx⟩
    rw [← hx]
    exact C.fixedProjection_mem_fixed x
  · intro y hy
    refine ⟨y, ?_⟩
    simpa using C.fixedPart_eq_self_of_fixed hy

/-- The range of the anti-fixed projection is exactly the anti-fixed sector. -/
theorem range_antiProjection_eq_antiFixed :
    LinearMap.range C.antiProjection = C.AntiFixed := by
  apply le_antisymm
  · intro y hy
    rcases hy with ⟨x, hx⟩
    rw [← hx]
    exact C.antiProjection_mem_antiFixed x
  · intro y hy
    refine ⟨y, ?_⟩
    simpa using C.antiPart_eq_self_of_antiFixed hy

/-- The kernel of the fixed projection is the anti-fixed sector. -/
theorem ker_fixedProjection_eq_antiFixed :
    LinearMap.ker C.fixedProjection = C.AntiFixed := by
  apply le_antisymm
  · intro x hx
    have hfixedZero : C.fixedPart x = 0 := by
      simpa using hx
    have hdecomp :
        C.fixedPart x + C.antiPart x = x :=
      C.fixed_add_anti_decomposition x
    have htheta :
        C.fixedPart x - C.antiPart x = C.theta x :=
      C.fixed_sub_anti_decomposition x
    have hantiPart_eq_x :
        C.antiPart x = x := by
      rw [hfixedZero] at hdecomp
      simpa using hdecomp
    have htheta_eq :
        C.theta x = -x := by
      rw [← htheta]
      rw [hfixedZero]
      simp [hantiPart_eq_x]
    exact (C.mem_antiFixed_iff x).mpr htheta_eq
  · intro x hx
    simpa using C.fixedPart_eq_zero_of_antiFixed hx

/-- The kernel of the anti-fixed projection is the fixed sector. -/
theorem ker_antiProjection_eq_fixed :
    LinearMap.ker C.antiProjection = C.Fixed := by
  apply le_antisymm
  · intro x hx
    have hantiZero : C.antiPart x = 0 := by
      simpa using hx
    have hdecomp :
        C.fixedPart x + C.antiPart x = x :=
      C.fixed_add_anti_decomposition x
    have htheta :
        C.fixedPart x - C.antiPart x = C.theta x :=
      C.fixed_sub_anti_decomposition x
    have hfixedPart_eq_x :
        C.fixedPart x = x := by
      rw [hantiZero] at hdecomp
      simpa using hdecomp
    have htheta_eq :
        C.theta x = x := by
      rw [← htheta]
      rw [hantiZero]
      simp [hfixedPart_eq_x]
    exact (C.mem_fixed_iff x).mpr htheta_eq
  · intro x hx
    simpa using C.antiPart_eq_zero_of_fixed hx

/-- The fixed sector is setwise stable under the closure involution. -/
theorem Fixed_setwiseStable :
    C.SetwiseStable C.Fixed := by
  intro v hv
  rw [C.mem_fixed_iff] at hv ⊢
  rw [C.theta_involutive v]
  exact hv.symm

/-- The anti-fixed sector is setwise stable under the closure involution. -/
theorem AntiFixed_setwiseStable :
    C.SetwiseStable C.AntiFixed := by
  intro v hv
  rw [C.mem_antiFixed_iff] at hv ⊢
  rw [C.theta_involutive v]
  rw [hv]
  simp

/-- Stable sectors are closed under the fixed projection. -/
theorem fixedProjection_mem_of_stable
    {S : Submodule ℝ V}
    (hS : C.SetwiseStable S)
    {x : V}
    (hx : x ∈ S) :
    C.fixedProjection x ∈ S :=
  C.fixedPart_mem_of_stable hS hx

/-- Stable sectors are closed under the anti-fixed projection. -/
theorem antiProjection_mem_of_stable
    {S : Submodule ℝ V}
    (hS : C.SetwiseStable S)
    {x : V}
    (hx : x ∈ S) :
    C.antiProjection x ∈ S :=
  C.antiPart_mem_of_stable hS hx

/--
If `x` is fixed, then `theta` acts trivially on `x`.

This is a named re-export for downstream modules that want a theorem rather
than unfolding `Fixed`.
-/
theorem theta_eq_self_of_mem_fixed
    {x : V}
    (hx : x ∈ C.Fixed) :
    C.theta x = x :=
  (C.mem_fixed_iff x).mp hx

/--
If `x` is anti-fixed, then `theta` acts by sign reversal on `x`.

This is a named re-export for downstream modules that want a theorem rather
than unfolding `AntiFixed`.
-/
theorem theta_eq_neg_self_of_mem_antiFixed
    {x : V}
    (hx : x ∈ C.AntiFixed) :
    C.theta x = -x :=
  (C.mem_antiFixed_iff x).mp hx

end LinearClosureInvolution

end InfoGeometry.OperatorAlgebra.ClosureInvolution
