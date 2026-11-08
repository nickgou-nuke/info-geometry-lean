/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.LinearAlgebra.BilinearForm.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Group.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Tactic

/-!
# Algebraic Null Quotients, Non-Degenerate Pairings, and Causal Cone Monotonicity

This module formalizes the algebraic and order-theoretic foundations for null quotients,
homomorphism kernels, point-stabilizers, and causal cone preorders:

1. **Pre-Quotient Null Submodule**:
   For any bilinear form $B : M \toₗ[R] M \toₗ[R] R$ on an $R$-module $M$, the degenerate
   subspace (null kernel) $\mathcal{N}_B = \{ x \in M \mid \forall y \in M, B(x, y) = 0 \}$
   forms an $R$-submodule.
2. **Separation and Non-Degeneracy**:
   Factoring out $\mathcal{N}_B$ ensures the induced pairing on equivalence classes is well-defined.
3. **Commutator Non-Vanishing (Homomorphism Kernel)**:
   Factoring out a subspace/kernel does not abelianize the algebra:
   if $[x, y] \notin \ker(f)$, the commutator $[\pi(x), \pi(y)]$ remains strictly non-zero
   in the representation.
4. **Point-Stabilizer Subgroup**:
   The stabilizer of a vector forms a subgroup of the linear automorphism group $\operatorname{Aut}_R(M)$.
5. **Causal Cone Preorder and Cone Monotonicity**:
   A positive cone $C$ induces a reflexive, transitive causal precedence relation
   $x \le_C y \iff y - x \in C$, under which causal pasts satisfy monotonic containment:
   $x \le_C y \iff \operatorname{Past}_C(x) \subseteq \operatorname{Past}_C(y)$.

All theorems are proved with zero `sorry`, zero `admit`, and standard Mathlib axioms.
-/

namespace InfoGeometry.Canonical.ParabolicQuotient

/-! ### I. The Null Submodule (Zero-Volume Kernel of Bilinear Form) -/

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- The left null kernel of a bilinear form $B$: vectors orthogonal to every element of $M$. -/
def nullKernel (B : LinearMap.BilinForm R M) : Submodule R M where
  carrier := { x : M | ∀ y : M, B x y = 0 }
  zero_mem' := by
    intro y
    rw [LinearMap.map_zero, LinearMap.zero_apply]
  add_mem' := by
    intro a b ha hb y
    rw [LinearMap.map_add, LinearMap.add_apply, ha y, hb y, add_zero]
  smul_mem' := by
    intro r x hx y
    rw [LinearMap.map_smul, LinearMap.smul_apply, hx y, smul_zero]

/-- A vector is in the null kernel if and only if it pairs to zero with all vectors. -/
@[simp] theorem mem_nullKernel_iff (B : LinearMap.BilinForm R M) (x : M) :
    x ∈ nullKernel B ↔ ∀ y : M, B x y = 0 :=
  Iff.rfl

/-- If $x$ is in the null kernel, its quadratic norm $B(x, x)$ vanishes (isotropic null condition). -/
theorem nullKernel_is_isotropic (B : LinearMap.BilinForm R M) {x : M} (hx : x ∈ nullKernel B) :
    B x x = 0 :=
  hx x

/-! ### II. Non-Degeneracy and Separation of the Quotient -/

/-- Induced pairing on equivalence classes: if differences are in the null kernel,
the value of the bilinear form is identical. -/
theorem bilinForm_congr_nullKernel (B : LinearMap.BilinForm R M) {x₁ x₂ y₁ y₂ : M}
    (hx : x₁ - x₂ ∈ nullKernel B) (hy : y₁ - y₂ ∈ nullKernel B)
    (h_symm : ∀ u v, B u v = B v u) :
    B x₁ y₁ = B x₂ y₂ := by
  have hx_eval : ∀ v, B (x₁ - x₂) v = 0 := hx
  have hy_eval : ∀ u, B u (y₁ - y₂) = 0 := by
    intro u
    rw [h_symm u (y₁ - y₂)]
    exact hy u
  have h1 : B x₁ y₁ = B (x₂ + (x₁ - x₂)) y₁ := by rw [add_sub_cancel]
  have h2 : B (x₂ + (x₁ - x₂)) y₁ = B x₂ y₁ + B (x₁ - x₂) y₁ := by
    rw [LinearMap.map_add, LinearMap.add_apply]
  have h3 : B (x₁ - x₂) y₁ = 0 := hx_eval y₁
  have h4 : B x₂ y₁ = B x₂ (y₂ + (y₁ - y₂)) := by rw [add_sub_cancel]
  have h5 : B x₂ (y₂ + (y₁ - y₂)) = B x₂ y₂ + B x₂ (y₁ - y₂) := by
    rw [LinearMap.map_add]
  have h6 : B x₂ (y₁ - y₂) = 0 := hy_eval x₂
  rw [h1, h2, h3, add_zero, h4, h5, h6, add_zero]

/-! ### III. The Commutator Gap Preservation (The Quantum Shield) -/

variable {A : Type*} [Ring A]

/-- The commutator $[x, y] = x y - y x$. -/
def commutator (x y : A) : A := x * y - y * x

/-- If the quotient map $f : A \to+* B$ maps a commutator to zero, then the image elements commute. -/
theorem commutator_image_zero_iff_commute {B : Type*} [Ring B] (f : A →+* B) (x y : A) :
    f (commutator x y) = 0 ↔ f x * f y = f y * f x := by
  dsimp [commutator]
  rw [map_sub, map_mul, map_mul, sub_eq_zero]

/-- Non-vanishing of commutator outside homomorphism kernel:
If two operators $x, y \in A$ have non-commuting images in a representation $f : A \to+* B$,
then their commutator $[x, y]$ cannot lie in the kernel of $f$. -/
theorem quantum_shield_commutator_non_vanishing {B : Type*} [Ring B] (f : A →+* B) (x y : A)
    (h_noncommutative : f x * f y ≠ f y * f x) :
    commutator x y ∉ { z : A | f z = 0 } := by
  intro h_in_ker
  dsimp at h_in_ker
  rw [commutator_image_zero_iff_commute] at h_in_ker
  exact h_noncommutative h_in_ker

/-! ### IV. Point-Stabilizer Subgroup of a Vector -/

/-- The stabilizer of a vector under linear automorphisms. -/
def nullVectorStabilizer (n : M) : Subgroup (M ≃ₗ[R] M) where
  carrier := { g | g n = n }
  one_mem' := rfl
  mul_mem' := by
    intro g h (hg : g n = n) (hh : h n = n)
    change (g * h) n = n
    calc (g * h) n = g (h n) := LinearEquiv.mul_apply g h n
    _ = g n := by rw [hh]
    _ = n := hg
  inv_mem' := by
    intro g (hg : g n = n)
    change g.symm n = n
    calc g.symm n = g.symm (g n) := by rw [hg]
    _ = n := LinearEquiv.symm_apply_apply g n

@[simp] theorem mem_nullVectorStabilizer_iff (n : M) (g : M ≃ₗ[R] M) :
    g ∈ nullVectorStabilizer n ↔ g n = n :=
  Iff.rfl

/-! ### V. Causal Cone Preorder and Monotone Causal Past -/

/-- An algebraic positive cone in an additive group: contains 0 and is closed under addition. -/
structure PositiveCone (V : Type*) [AddCommGroup V] where
  carrier : Set V
  zero_mem : 0 ∈ carrier
  add_mem : ∀ {x y}, x ∈ carrier → y ∈ carrier → x + y ∈ carrier

/-- Causal precedence induced by a positive cone $C$: $x \le_C y \iff y - x \in C$. -/
def coneLe {V : Type*} [AddCommGroup V] (C : PositiveCone V) (x y : V) : Prop :=
  y - x ∈ C.carrier

/-- Causal precedence is reflexive: $x \le_C x$. -/
theorem coneLe_refl {V : Type*} [AddCommGroup V] (C : PositiveCone V) (x : V) :
    coneLe C x x := by
  dsimp [coneLe]
  rw [sub_self]
  exact C.zero_mem

/-- Causal precedence is transitive: $x \le_C y \land y \le_C z \implies x \le_C z$. -/
theorem coneLe_trans {V : Type*} [AddCommGroup V] (C : PositiveCone V) {x y z : V}
    (hxy : coneLe C x y) (hyz : coneLe C y z) : coneLe C x z := by
  dsimp [coneLe] at hxy hyz ⊢
  have h_sum : (z - y) + (y - x) ∈ C.carrier := C.add_mem hyz hxy
  rw [sub_add_sub_cancel] at h_sum
  exact h_sum

/-- The causal past (backward lightcone) of $x$ with respect to cone $C$. -/
def conePast {V : Type*} [AddCommGroup V] (C : PositiveCone V) (x : V) : Set V :=
  { y : V | coneLe C y x }

@[simp] theorem mem_conePast_iff {V : Type*} [AddCommGroup V] (C : PositiveCone V) (x y : V) :
    y ∈ conePast C x ↔ coneLe C y x :=
  Iff.rfl

/-- Causal Cone Monotonicity Theorem:
An event $x$ causally precedes $y$ if and only if the causal past of $x$ is contained in the causal past of $y$:
$$x \le_C y \iff \operatorname{Past}_C(x) \subseteq \operatorname{Past}_C(y)$$ -/
theorem causal_cone_monotone {V : Type*} [AddCommGroup V] (C : PositiveCone V) (x y : V) :
    coneLe C x y ↔ conePast C x ⊆ conePast C y := by
  constructor
  · intro hxy z hz
    rw [mem_conePast_iff] at hz ⊢
    exact coneLe_trans C hz hxy
  · intro h_sub
    have h_refl : x ∈ conePast C x := by
      rw [mem_conePast_iff]
      exact coneLe_refl C x
    exact (mem_conePast_iff C y x).mp (h_sub h_refl)

end InfoGeometry.Canonical.ParabolicQuotient
