import Mathlib
import InfoGeometry.Canonical.ChiralLightConeTensorTower

/-!
# InfoGeometry.Canonical.CantorCliffordFunctionModel

Boundary-function carrier for the symbolic chiral Cantor-type boundary.

This module sits between:

* `ChiralLightConeTensorTower`, which owns the symbolic boundary carrier;
* future `CuntzCantorBoundary`, which may install Cuntz/IFS operators;
* future `CantorSpectralTriple`, which may install measure, Hilbert space,
  Dirac operator, and spectral-triple witnesses.

This file does not assert:

* a homeomorphism with the standard Cantor set;
* a Cuntz algebra representation;
* an infinite tensor-product theorem;
* a spectral triple;
* any Clifford action on `C(ChiralBoundary)` beyond prefix/cylinder readouts.
-/

noncomputable section

namespace InfoGeometry.Canonical.CantorCliffordFunctionModel

open InfoGeometry.Canonical.ChiralLightConeTensorTower

/-! ## 1. Boundary functions -/

/-- A boundary function on the symbolic chiral Cantor-type boundary. -/
abbrev BoundaryFunction
    (Value : Type*) :=
  ChiralBoundary → Value

/--
A bundled boundary-function space.

This is deliberately just a carrier. Topology, measure, norm, Hilbert
structure, and spectral-triple structure are later witnesses.
-/
@[rep_depth krein]
structure BoundaryFunctionSpace
    (Value : Type*) where
  /-- Function on the infinite symbolic boundary. -/
  function : BoundaryFunction Value

namespace BoundaryFunctionSpace

variable {Value : Type*}

/-- Extensional equality for bundled boundary functions. -/
@[ext, rep_depth krein]
theorem ext
    {F G : BoundaryFunctionSpace Value}
    (h : ∀ ξ : ChiralBoundary, F.function ξ = G.function ξ) :
    F = G := by
  cases F
  cases G
  simp only at h
  simp [funext h]

end BoundaryFunctionSpace

/-! ## 2. Prefix cylinders -/

/--
A boundary sequence extends a finite causal word if it agrees with that word on
all finite prefix positions.
-/
@[rep_depth krein]
def BoundaryExtendsPrefix
    {n : ℕ}
    (w : CausalWord n)
    (ξ : ChiralBoundary) : Prop :=
  ∀ k : Fin n, ξ k.1 = w k

/-- The cylinder set determined by a finite causal word. -/
@[rep_depth krein]
def prefixCylinder
    {n : ℕ}
    (w : CausalWord n) : Set ChiralBoundary :=
  {ξ | BoundaryExtendsPrefix w ξ}

/--
The canonical boundary obtained from a finite word and constant tail lies in
the word's prefix cylinder.
-/
@[rep_depth krein]
theorem toBoundary_mem_prefixCylinder
    {n : ℕ}
    (w : CausalWord n)
    (tail : CausalArrow) :
    CausalWord.toBoundary w tail ∈ prefixCylinder w := by
  intro k
  exact CausalWord.toBoundary_of_lt w tail k.2

/-- Membership in a prefix cylinder is exactly prefix agreement. -/
@[rep_depth krein]
theorem mem_prefixCylinder_iff
    {n : ℕ}
    (w : CausalWord n)
    (ξ : ChiralBoundary) :
    ξ ∈ prefixCylinder w ↔ BoundaryExtendsPrefix w ξ :=
  Iff.rfl

/-! ## 3. Cylinder restriction readouts -/

/--
Restrict a boundary function to a finite prefix cylinder.

Outside the cylinder the function is set to `0`.
-/
@[rep_depth krein]
def restrictToCylinder
    {Value : Type*} [Zero Value]
    {n : ℕ}
    (w : CausalWord n)
    (f : BoundaryFunction Value) :
    BoundaryFunction Value := by
  classical
  exact fun ξ =>
    if ξ ∈ prefixCylinder w then f ξ else 0

/-- Inside the cylinder, restriction agrees with the original function. -/
@[simp, rep_depth krein]
theorem restrictToCylinder_eq_of_mem
    {Value : Type*} [Zero Value]
    {n : ℕ}
    (w : CausalWord n)
    (f : BoundaryFunction Value)
    {ξ : ChiralBoundary}
    (hξ : ξ ∈ prefixCylinder w) :
    restrictToCylinder w f ξ = f ξ := by
  classical
  simp [restrictToCylinder, hξ]

/-- Outside the cylinder, restriction vanishes. -/
@[simp, rep_depth krein]
theorem restrictToCylinder_eq_zero_of_not_mem
    {Value : Type*} [Zero Value]
    {n : ℕ}
    (w : CausalWord n)
    (f : BoundaryFunction Value)
    {ξ : ChiralBoundary}
    (hξ : ξ ∉ prefixCylinder w) :
    restrictToCylinder w f ξ = 0 := by
  classical
  simp [restrictToCylinder, hξ]

/-- Cylinder restriction is idempotent. -/
@[rep_depth krein]
theorem restrictToCylinder_idem
    {Value : Type*} [Zero Value]
    {n : ℕ}
    (w : CausalWord n)
    (f : BoundaryFunction Value) :
    restrictToCylinder w (restrictToCylinder w f) =
      restrictToCylinder w f := by
  classical
  funext ξ
  by_cases hξ : ξ ∈ prefixCylinder w
  · simp [restrictToCylinder, hξ]
  · simp [restrictToCylinder, hξ]

/-! ## 4. Head/tail maps on the boundary -/

/-- Prepend one causal arrow to a boundary sequence. -/
@[rep_depth krein]
def consBoundary
    (a : CausalArrow)
    (ξ : ChiralBoundary) : ChiralBoundary :=
  fun k =>
    match k with
    | 0 => a
    | Nat.succ m => ξ m

/-- Remove the first causal arrow from a boundary sequence. -/
@[rep_depth krein]
def tailBoundary
    (ξ : ChiralBoundary) : ChiralBoundary :=
  fun k => ξ (k + 1)

@[simp, rep_depth krein]
theorem consBoundary_zero
    (a : CausalArrow)
    (ξ : ChiralBoundary) :
    consBoundary a ξ 0 = a := by
  rfl

@[simp, rep_depth krein]
theorem consBoundary_succ
    (a : CausalArrow)
    (ξ : ChiralBoundary)
    (k : ℕ) :
    consBoundary a ξ (Nat.succ k) = ξ k := by
  rfl

@[simp, rep_depth krein]
theorem tailBoundary_consBoundary
    (a : CausalArrow)
    (ξ : ChiralBoundary) :
    tailBoundary (consBoundary a ξ) = ξ := by
  funext k
  rfl

/-- The first symbol readout. -/
@[rep_depth krein]
def headBoundary
    (ξ : ChiralBoundary) : CausalArrow :=
  ξ 0

@[simp, rep_depth krein]
theorem headBoundary_consBoundary
    (a : CausalArrow)
    (ξ : ChiralBoundary) :
    headBoundary (consBoundary a ξ) = a := by
  rfl

/-- Every boundary decomposes as head followed by tail. -/
@[simp, rep_depth krein]
theorem cons_head_tail
    (ξ : ChiralBoundary) :
    consBoundary (headBoundary ξ) (tailBoundary ξ) = ξ := by
  funext k
  cases k with
  | zero => rfl
  | succ m => rfl

/-! ## 5. Finite-prefix insertion -/

/-- Prefix a finite causal word to an infinite boundary code. -/
@[rep_depth krein]
def prefixWordBoundary
    {n : ℕ}
    (w : CausalWord n)
    (ξ : ChiralBoundary) :
    ChiralBoundary :=
  fun k =>
    if h : k < n then
      w ⟨k, h⟩
    else
      ξ (k - n)

@[simp, rep_depth krein]
theorem prefixWordBoundary_of_lt
    {n : ℕ}
    (w : CausalWord n)
    (ξ : ChiralBoundary)
    {k : ℕ}
    (hk : k < n) :
    prefixWordBoundary w ξ k = w ⟨k, hk⟩ := by
  simp [prefixWordBoundary, hk]

@[simp, rep_depth krein]
theorem prefixWordBoundary_tail
    {n : ℕ}
    (w : CausalWord n)
    (ξ : ChiralBoundary)
    (k : ℕ) :
    prefixWordBoundary w ξ (n + k) = ξ k := by
  have hnot : ¬ n + k < n := by omega
  simp [prefixWordBoundary, hnot]

@[rep_depth krein]
theorem prefixWordBoundary_extends_prefix
    {n : ℕ}
    (w : CausalWord n)
    (ξ : ChiralBoundary) :
    BoundaryExtendsPrefix w (prefixWordBoundary w ξ) := by
  intro k
  exact prefixWordBoundary_of_lt w ξ k.2

/-! ## 6. Prefix shift / pullback operators -/

/--
Pull back a boundary function along the prefixing map `ξ ↦ a :: ξ`.

This is the safe pre-Cuntz operation. It is not yet a Cuntz isometry.
-/
@[rep_depth krein]
def prefixPullback
    {Value : Type*}
    (a : CausalArrow)
    (f : BoundaryFunction Value) :
    BoundaryFunction Value :=
  fun ξ => f (consBoundary a ξ)

/-- Pull back a boundary function along finite-prefix insertion. -/
@[rep_depth krein]
def prefixWordPullback
    {Value : Type*} {n : ℕ}
    (w : CausalWord n)
    (f : BoundaryFunction Value) :
    BoundaryFunction Value :=
  fun ξ => f (prefixWordBoundary w ξ)

/-- Tail pullback, evaluating a function after forgetting the first symbol. -/
@[rep_depth krein]
def tailPullback
    {Value : Type*}
    (f : BoundaryFunction Value) :
    BoundaryFunction Value :=
  fun ξ => f (tailBoundary ξ)

/-- Pulling back by prefix and then tail recovers the prefixed evaluation. -/
@[simp, rep_depth krein]
theorem tailPullback_prefixPullback_eval
    {Value : Type*}
    (a : CausalArrow)
    (f : BoundaryFunction Value)
    (ξ : ChiralBoundary) :
    tailPullback (prefixPullback a f) (consBoundary a ξ) = f (consBoundary a ξ) := by
  rfl

/-- Prefix pullback respects function equality. -/
@[rep_depth krein]
theorem prefixPullback_congr
    {Value : Type*}
    {f g : BoundaryFunction Value}
    (hfg : f = g)
    (a : CausalArrow) :
    prefixPullback a f = prefixPullback a g := by
  rw [hfg]

/-- Finite-prefix pullback evaluates by inserting the finite prefix. -/
@[simp, rep_depth krein]
theorem prefixWordPullback_apply
    {Value : Type*} {n : ℕ}
    (w : CausalWord n)
    (f : BoundaryFunction Value)
    (ξ : ChiralBoundary) :
    prefixWordPullback w f ξ = f (prefixWordBoundary w ξ) := by
  rfl

/-! ## 7. Future Cuntz/IFS socket boundary -/

/--
A pre-Cuntz boundary action package.

This records the carrier operations that a future Cuntz/IFS module may refine
into actual isometries satisfying Cuntz laws. This structure itself does not
assert those laws.
-/
@[rep_depth krein]
structure PrefixBoundaryAction
    (Value : Type*) where
  /-- Pullback along `u⁺` prefix. -/
  plusPullback :
    BoundaryFunction Value → BoundaryFunction Value
  /-- Pullback along `u⁻` prefix. -/
  minusPullback :
    BoundaryFunction Value → BoundaryFunction Value
  /-- Tail pullback. -/
  tail :
    BoundaryFunction Value → BoundaryFunction Value

/-- Canonical pre-Cuntz prefix action on boundary functions. -/
@[rep_depth krein]
def canonicalPrefixBoundaryAction
    (Value : Type*) :
    PrefixBoundaryAction Value where
  plusPullback := prefixPullback ChiralArrow.plus
  minusPullback := prefixPullback ChiralArrow.minus
  tail := tailPullback

end InfoGeometry.Canonical.CantorCliffordFunctionModel
