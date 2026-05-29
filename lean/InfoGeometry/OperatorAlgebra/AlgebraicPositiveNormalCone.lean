import Mathlib
import InfoGeometry.Convex.SelfDualCone

/-!
# InfoGeometry.OperatorAlgebra.AlgebraicPositiveNormalCone

Algebraic positive and normal cones for star-algebraic operator geometry.

This file adds the finite/algebraic layer suggested by the symmetric-cone and
von-Neumann-positive-cone viewpoint, without asserting analytic von Neumann
algebra theorems.  The definitions are deliberately elementary:

* a positive element is one presented as `star y * y`;
* a normal element commutes with its star-adjoint;
* every algebraically positive element is self-adjoint;
* every self-adjoint element is normal;
* a Cartan involution gives compact and hyperbolic eigenspaces;
* Cayley compactification is represented by an explicit map plus an explicit
  theorem hypothesis that it sends hyperbolic elements into the compact sector.

No spectral theorem.
No von Neumann algebra closure theorem.
No normal-state cone construction.
No topological or analytic completion claim.
-/

namespace InfoGeometry.OperatorAlgebra.AlgebraicPositiveNormalCone

/-! ## Inductive invariant principle -/

/--
The bare induction principle for an invariant transported by a successor map.

This is the kernel-level essence used below: a base point has an invariant, and
one successor step preserves it, so every finite iterate has it.  No limit,
completion, or analytic continuation is asserted.
-/
theorem inductiveInvariant_iterate {α : Type*} (P : α → Prop) (next : α → α)
    {x₀ : α} (h0 : P x₀) (hstep : ∀ x : α, P x → P (next x)) :
    ∀ n : ℕ, P ((next^[n]) x₀) := by
  intro n
  induction n with
  | zero => simpa using h0
  | succ n ih =>
      simpa [Function.iterate_succ_apply'] using hstep ((next^[n]) x₀) ih

/-! ## Algebraic positivity and normality -/

variable {A : Type*} [NonUnitalNonAssocSemiring A] [StarMul A]

/-- Algebraic positivity: `x` is presented as `star y * y`. -/
def IsAlgebraicallyPositive (x : A) : Prop :=
  ∃ y : A, x = star y * y

/-- Algebraic normality: an element commutes with its adjoint. -/
def IsNormalElement (x : A) : Prop :=
  star x * x = x * star x

/-- Algebraic self-adjointness. -/
def IsSelfAdjointElement (x : A) : Prop :=
  star x = x

/-- The algebraic positive cone as a set. -/
def algebraicPositiveCone (A : Type*) [NonUnitalNonAssocSemiring A] [StarMul A] : Set A :=
  {x : A | IsAlgebraicallyPositive x}

/-- The normal cone/locus as a set. -/
def normalCone (A : Type*) [NonUnitalNonAssocSemiring A] [StarMul A] : Set A :=
  {x : A | IsNormalElement x}

/-- Every algebraically positive element is self-adjoint. -/
theorem IsAlgebraicallyPositive.self_adjoint
    {x : A} (hx : IsAlgebraicallyPositive x) :
    IsSelfAdjointElement x := by
  rcases hx with ⟨y, rfl⟩
  unfold IsSelfAdjointElement
  simp [star_mul]

/-- Every self-adjoint element is normal. -/
theorem IsSelfAdjointElement.normal [Semigroup A]
    {x : A} (hx : IsSelfAdjointElement x) :
    IsNormalElement x := by
  unfold IsNormalElement IsSelfAdjointElement at *
  rw [hx]

/-- Every algebraically positive element is normal. -/
theorem IsAlgebraicallyPositive.normal [Semigroup A]
    {x : A} (hx : IsAlgebraicallyPositive x) :
    IsNormalElement x :=
  hx.self_adjoint.normal

/-- Membership readback for the algebraic positive cone. -/
theorem mem_algebraicPositiveCone_iff (x : A) :
    x ∈ algebraicPositiveCone A ↔ IsAlgebraicallyPositive x :=
  Iff.rfl

/-- Membership readback for the normal cone. -/
theorem mem_normalCone_iff (x : A) :
    x ∈ normalCone A ↔ IsNormalElement x :=
  Iff.rfl

/-- Algebraic positivity is preserved along every finite iterate of a positivity-preserving map. -/
theorem IsAlgebraicallyPositive.iterate_of_preserving
    (f : A → A) {x₀ : A}
    (h0 : IsAlgebraicallyPositive x₀)
    (hf : ∀ x : A, IsAlgebraicallyPositive x → IsAlgebraicallyPositive (f x)) :
    ∀ n : ℕ, IsAlgebraicallyPositive ((f^[n]) x₀) :=
  inductiveInvariant_iterate IsAlgebraicallyPositive f h0 hf

/-- Algebraic normality is preserved along every finite iterate of a normality-preserving map. -/
theorem IsNormalElement.iterate_of_preserving
    (f : A → A) {x₀ : A}
    (h0 : IsNormalElement x₀)
    (hf : ∀ x : A, IsNormalElement x → IsNormalElement (f x)) :
    ∀ n : ℕ, IsNormalElement ((f^[n]) x₀) :=
  inductiveInvariant_iterate IsNormalElement f h0 hf

/-! ## Cartan eigenspace split -/

section Cartan

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- A real Cartan involution on a carrier. -/
structure CartanInvolution where
  /-- The involutive linear operator. -/
  theta : V →ₗ[ℝ] V
  /-- Involutivity. -/
  theta_sq : theta.comp theta = LinearMap.id

namespace CartanInvolution

/-- Compact/even eigenspace of a Cartan involution. -/
def IsCompact (θ : CartanInvolution (V := V)) (x : V) : Prop :=
  θ.theta x = x

/-- Hyperbolic/odd eigenspace of a Cartan involution. -/
def IsHyperbolic (θ : CartanInvolution (V := V)) (x : V) : Prop :=
  θ.theta x = -x

/-- Applying the Cartan involution twice is the identity on elements. -/
theorem theta_theta (θ : CartanInvolution (V := V)) (x : V) :
    θ.theta (θ.theta x) = x := by
  have h := congrArg (fun f : V →ₗ[ℝ] V => f x) θ.theta_sq
  simpa [LinearMap.comp_apply] using h

/-- Compact elements are fixed by the involution. -/
theorem compact_apply {θ : CartanInvolution (V := V)} {x : V}
    (hx : θ.IsCompact x) :
    θ.theta x = x :=
  hx

/-- Hyperbolic elements are negated by the involution. -/
theorem hyperbolic_apply {θ : CartanInvolution (V := V)} {x : V}
    (hx : θ.IsHyperbolic x) :
    θ.theta x = -x :=
  hx

/-- Compact Cartan-sector membership is preserved along finite iterates of a sector-preserving map. -/
theorem IsCompact.iterate_of_preserving
    (θ : CartanInvolution (V := V)) (f : V → V) {x₀ : V}
    (h0 : θ.IsCompact x₀)
    (hf : ∀ x : V, θ.IsCompact x → θ.IsCompact (f x)) :
    ∀ n : ℕ, θ.IsCompact ((f^[n]) x₀) :=
  inductiveInvariant_iterate θ.IsCompact f h0 hf

/-- Hyperbolic Cartan-sector membership is preserved along finite iterates of a sector-preserving map. -/
theorem IsHyperbolic.iterate_of_preserving
    (θ : CartanInvolution (V := V)) (f : V → V) {x₀ : V}
    (h0 : θ.IsHyperbolic x₀)
    (hf : ∀ x : V, θ.IsHyperbolic x → θ.IsHyperbolic (f x)) :
    ∀ n : ℕ, θ.IsHyperbolic ((f^[n]) x₀) :=
  inductiveInvariant_iterate θ.IsHyperbolic f h0 hf

end CartanInvolution

end Cartan

/-! ## Algebraic Cayley compactification interface -/

section Cayley

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/--
A Cayley compactification interface for a Cartan split.

The map is explicit data; the compactification theorem is an explicit theorem
hypothesis, not an analytic continuation result.
-/
structure AlgebraicCayleyCompactification (θ : CartanInvolution (V := V)) where
  /-- Algebraic Cayley transform/readout. -/
  cayleyTransform : V → V
  /-- Hyperbolic elements are sent into the compact/even eigenspace. -/
  maps_hyperbolic_to_compact : ∀ x : V, θ.IsHyperbolic x → θ.IsCompact (cayleyTransform x)

namespace AlgebraicCayleyCompactification

/-- Readback theorem for the compactness of Cayley images of hyperbolic elements. -/
theorem cayley_compact {θ : CartanInvolution (V := V)}
    (C : AlgebraicCayleyCompactification θ)
    {x : V} (hx : θ.IsHyperbolic x) :
    θ.IsCompact (C.cayleyTransform x) :=
  C.maps_hyperbolic_to_compact x hx

end AlgebraicCayleyCompactification

end Cayley

end InfoGeometry.OperatorAlgebra.AlgebraicPositiveNormalCone
