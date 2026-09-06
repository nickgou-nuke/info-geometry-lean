import Mathlib.Tactic
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

namespace BoundaryFunctionSpace

variable {Value : Type*}

/-- Extensional equality for bundled boundary functions. -/
@[ext, rep_depth krein]
theorem ext
    {F G : (ChiralBoundary → Value)}
    (h : ∀ ξ : ChiralBoundary, F ξ = G ξ) :
    F = G := by
  exact funext h

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
    (f : (ChiralBoundary → Value)) :
    (ChiralBoundary → Value) := by
  classical
  exact fun ξ =>
    if ξ ∈ prefixCylinder w then f ξ else 0

/-- Inside the cylinder, restriction agrees with the original function. -/
@[simp, rep_depth krein]
theorem restrictToCylinder_eq_of_mem
    {Value : Type*} [Zero Value]
    {n : ℕ}
    (w : CausalWord n)
    (f : (ChiralBoundary → Value))
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
    (f : (ChiralBoundary → Value))
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
    (f : (ChiralBoundary → Value)) :
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

@[simp, rep_depth krein]
theorem prefixWordBoundary_one_eq_consBoundary
    (a : CausalArrow)
    (ξ : ChiralBoundary) :
    prefixWordBoundary (fun _ : Fin 1 => a) ξ = consBoundary a ξ := by
  funext k
  cases k with
  | zero => rfl
  | succ m =>
      simp [prefixWordBoundary, consBoundary]

/-! ## 6. Prefix shift / pullback operators -/

/--
Pull back a boundary function along the prefixing map `ξ ↦ a :: ξ`.

This is the safe pre-Cuntz operation. It is not yet a Cuntz isometry.
-/
@[rep_depth krein]
def prefixPullback
    {Value : Type*}
    (a : CausalArrow)
    (f : (ChiralBoundary → Value)) :
    (ChiralBoundary → Value) :=
  fun ξ => f (consBoundary a ξ)

/-- Pull back a boundary function along finite-prefix insertion. -/
@[rep_depth krein]
def prefixWordPullback
    {Value : Type*} {n : ℕ}
    (w : CausalWord n)
    (f : (ChiralBoundary → Value)) :
    (ChiralBoundary → Value) :=
  fun ξ => f (prefixWordBoundary w ξ)

/-- Tail pullback, evaluating a function after forgetting the first symbol. -/
@[rep_depth krein]
def tailPullback
    {Value : Type*}
    (f : (ChiralBoundary → Value)) :
    (ChiralBoundary → Value) :=
  fun ξ => f (tailBoundary ξ)

/-- Pulling back by prefix and then tail recovers the prefixed evaluation. -/
@[simp, rep_depth krein]
theorem tailPullback_prefixPullback_eval
    {Value : Type*}
    (a : CausalArrow)
    (f : (ChiralBoundary → Value))
    (ξ : ChiralBoundary) :
    tailPullback (prefixPullback a f) (consBoundary a ξ) = f (consBoundary a ξ) := by
  rfl

@[simp, rep_depth krein]
theorem prefixPullback_tailPullback
    {Value : Type*}
    (a : CausalArrow)
    (f : (ChiralBoundary → Value))
    (ξ : ChiralBoundary) :
    prefixPullback a (tailPullback f) ξ = f ξ := by
  change f (tailBoundary (consBoundary a ξ)) = f ξ
  rw [tailBoundary_consBoundary]

theorem prefixPullback_surjective
    {Value : Type*}
    (a : CausalArrow) :
    Function.Surjective (prefixPullback a :
      (ChiralBoundary → Value) → (ChiralBoundary → Value)) := by
  intro f
  refine ⟨tailPullback f, ?_⟩
  funext ξ
  exact prefixPullback_tailPullback a f ξ

theorem tailPullBack_injective
    {Value : Type*} :
    Function.Injective (tailPullback :
      (ChiralBoundary → Value) → (ChiralBoundary → Value)) := by
  intro f g h
  funext ξ
  have h' := congrFun h (consBoundary ChiralArrow.plus ξ)
  simpa [prefixPullback, tailPullback, tailBoundary_consBoundary] using h'

@[simp, rep_depth krein]
theorem tailPullback_prefixPullback_apply
    {Value : Type*}
    (a : CausalArrow)
    (f : (ChiralBoundary → Value))
    (ξ : ChiralBoundary) :
    tailPullback (prefixPullback a f) ξ =
      f (consBoundary a (tailBoundary ξ)) := by
  rfl

/-- Prefix pullback respects function equality. -/
@[rep_depth krein]
theorem prefixPullback_congr
    {Value : Type*}
    {f g : (ChiralBoundary → Value)}
    (hfg : f = g)
    (a : CausalArrow) :
    prefixPullback a f = prefixPullback a g := by
  rw [hfg]

@[simp, rep_depth krein]
theorem prefixPullback_apply
    {Value : Type*}
    (a : CausalArrow)
    (f : (ChiralBoundary → Value))
    (ξ : ChiralBoundary) :
    prefixPullback a f ξ = f (consBoundary a ξ) := by
  rfl

theorem prefixPullback_add
    {Value : Type*} [Add Value]
    (a : CausalArrow)
    (f g : ChiralBoundary → Value) :
    prefixPullback a (f + g) =
      prefixPullback a f + prefixPullback a g := by
  funext ξ
  rfl

theorem prefixPullback_smul
    {R Value : Type*} [SMul R Value]
    (a : CausalArrow)
    (r : R)
    (f : ChiralBoundary → Value) :
    prefixPullback a (r • f) =
      r • prefixPullback a f := by
  funext ξ
  rfl

theorem prefixPullback_zero
    {Value : Type*} [Zero Value]
    (a : CausalArrow) :
    prefixPullback a (0 : ChiralBoundary → Value) = 0 := by
  funext ξ
  rfl

theorem prefixPullback_mul
    {Value : Type*} [Mul Value]
    (a : CausalArrow)
    (f g : ChiralBoundary → Value) :
    prefixPullback a (f * g) =
      prefixPullback a f * prefixPullback a g := by
  funext ξ
  rfl

theorem prefixPullback_star
    {Value : Type*} [Star Value]
    (a : CausalArrow)
    (f : ChiralBoundary → Value) :
    prefixPullback a (star f) =
      star (prefixPullback a f) := by
  funext ξ
  rfl

@[simp, rep_depth krein]
theorem prefixPullback_tailBoundary
    {Value : Type*}
    (a : CausalArrow)
    (f : (ChiralBoundary → Value))
    (ξ : ChiralBoundary) :
    prefixPullback a f (tailBoundary (consBoundary a ξ)) =
      f (consBoundary a ξ) := by
  rw [tailBoundary_consBoundary]
  rfl

@[simp, rep_depth krein]
theorem prefixPullback_comp
    {Value : Type*}
    (a b : CausalArrow)
    (f : (ChiralBoundary → Value))
    (ξ : ChiralBoundary) :
    prefixPullback a (prefixPullback b f) ξ =
      f (consBoundary b (consBoundary a ξ)) := by
  rfl

theorem prefixPullback_comp_fun
    {Value : Type*}
    (a b : CausalArrow)
    (f : (ChiralBoundary → Value)) :
    prefixPullback a (prefixPullback b f) =
      fun ξ => f (consBoundary b (consBoundary a ξ)) := by
  funext ξ
  exact prefixPullback_comp a b f ξ

theorem prefixPullback_comp_eq_prefixWordPullback_two
    {Value : Type*}
    (a b : CausalArrow)
    (f : (ChiralBoundary → Value)) :
    prefixPullback a (prefixPullback b f) =
      prefixWordPullback (fun k : Fin 2 => if k = 0 then b else a) f := by
  funext ξ
  apply congrArg f
  funext k
  cases k with
  | zero => rfl
  | succ k =>
      cases k with
      | zero => rfl
      | succ k => simp [prefixWordBoundary]

theorem tailPullback_prefixPullback_fun
    {Value : Type*}
    (a : CausalArrow)
    (f : (ChiralBoundary → Value)) :
    tailPullback (prefixPullback a f) =
      fun ξ => f (consBoundary a (tailBoundary ξ)) := by
  funext ξ
  exact tailPullback_prefixPullback_apply a f ξ

/-- Finite-prefix pullback evaluates by inserting the finite prefix. -/
@[simp, rep_depth krein]
theorem prefixWordPullback_apply
    {Value : Type*} {n : ℕ}
    (w : CausalWord n)
    (f : (ChiralBoundary → Value))
    (ξ : ChiralBoundary) :
    prefixWordPullback w f ξ = f (prefixWordBoundary w ξ) := by
  rfl

@[simp, rep_depth krein]
theorem prefixWordPullback_one_eq_prefixPullback
    {Value : Type*}
    (a : CausalArrow)
    (f : (ChiralBoundary → Value)) :
    prefixWordPullback (fun _ : Fin 1 => a) f = prefixPullback a f := by
  funext ξ
  simp [prefixWordPullback, prefixPullback,
    prefixWordBoundary_one_eq_consBoundary]

theorem prefixWordPullback_add
    {Value : Type*} [Add Value] {n : ℕ}
    (w : CausalWord n)
    (f g : ChiralBoundary → Value) :
    prefixWordPullback w (f + g) =
      prefixWordPullback w f + prefixWordPullback w g := by
  funext ξ
  rfl

theorem prefixWordPullback_smul
    {R Value : Type*} [SMul R Value] {n : ℕ}
    (w : CausalWord n)
    (r : R)
    (f : ChiralBoundary → Value) :
    prefixWordPullback w (r • f) =
      r • prefixWordPullback w f := by
  funext ξ
  rfl

theorem prefixWordPullback_zero
    {Value : Type*} [Zero Value] {n : ℕ}
    (w : CausalWord n) :
    prefixWordPullback w (0 : ChiralBoundary → Value) = 0 := by
  funext ξ
  rfl

theorem prefixWordPullback_mul
    {Value : Type*} [Mul Value] {n : ℕ}
    (w : CausalWord n)
    (f g : ChiralBoundary → Value) :
    prefixWordPullback w (f * g) =
      prefixWordPullback w f * prefixWordPullback w g := by
  funext ξ
  rfl

theorem prefixWordPullback_star
    {Value : Type*} [Star Value] {n : ℕ}
    (w : CausalWord n)
    (f : ChiralBoundary → Value) :
    prefixWordPullback w (star f) =
      star (prefixWordPullback w f) := by
  funext ξ
  rfl

end InfoGeometry.Canonical.CantorCliffordFunctionModel
