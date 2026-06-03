import Mathlib

/-!
# InfoGeometry.OperatorAlgebra.SelfDualConeColimit

Directed-colimit theorem for self-dual cone carriers.

This file proves the finite-to-colimit carrier step separately from analytic
Tomita--Takesaki, Type III, predual, KMS, or compactification claims.

#### BUCKET 1: CLOSED FINITE/COLIMIT THEOREMS
[selfDualCone_closed_under_carrier_step,
 selfDualCone_directed_system_compatible,
 isSelfDualCone_iUnion_nat,
 selfDualCone_extends_to_colimit]

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT PREMISES
The colimit theorem is conditional on:
* monotone inclusion of finite/staged carriers;
* self-duality at each stage;
* an explicit dual-exhaustion premise for the directed union.

#### BUCKET 3: OPEN CLOSURE DEBT
No analytic standard-form theorem is claimed here.  A concrete module must still
prove the dual-exhaustion premise for its chosen operator-algebra carrier.
-/

namespace InfoGeometry.OperatorAlgebra.SelfDualConeColimit

/--
Self-duality of a cone-like carrier `K` with respect to a real pairing.

This is a purely order/algebraic predicate: membership in `K` is equivalent to
nonnegative pairing against every element of `K`.
-/
def IsSelfDualCone {E : Type*} (pairing : E → E → ℝ) (K : Set E) : Prop :=
  ∀ x, x ∈ K ↔ ∀ y, y ∈ K → 0 ≤ pairing x y

/--
Finite carrier-step lemma for an increasing family of self-dual cones.

If `x` and `y` lie in stages `i` and `j`, then both lie in the common finite
stage `max i j`, so the stagewise self-duality hypothesis yields the
nonnegative pairing statement there.
-/
theorem selfDualCone_closed_under_carrier_step
    {E : Type*}
    (pairing : E → E → ℝ)
    (K : ℕ → Set E)
    (hmono : Monotone K)
    (hself : ∀ n : ℕ, IsSelfDualCone pairing (K n))
    {i j : ℕ} {x y : E}
    (hx : x ∈ K i)
    (hy : y ∈ K j) :
    0 ≤ pairing x y := by
  have hxmax : x ∈ K (max i j) :=
    hmono (Nat.le_max_left i j) hx
  have hymax : y ∈ K (max i j) :=
    hmono (Nat.le_max_right i j) hy
  exact (hself (max i j) x).mp hxmax y hymax

/--
Directed-system compatibility of stagewise self-dual cones.

This is the finite owner-side content needed before passing to the colimit:
pairings between elements coming from different stages are already controlled in
a common finite carrier stage.
-/
theorem selfDualCone_directed_system_compatible
    {E : Type*}
    (pairing : E → E → ℝ)
    (K : ℕ → Set E)
    (hmono : Monotone K)
    (hself : ∀ n : ℕ, IsSelfDualCone pairing (K n)) :
    ∀ ⦃i j : ℕ⦄ ⦃x y : E⦄,
      x ∈ K i → y ∈ K j → 0 ≤ pairing x y := by
  intro i j x y hx hy
  exact selfDualCone_closed_under_carrier_step pairing K hmono hself hx hy

/--
Finite-to-colimit positivity, one staged element at a time.

If `x` is in a finite carrier stage, then it pairs nonnegatively with every
element of the directed union.
-/
theorem selfDualCone_stage_mem_pairing_nonneg_iUnion
    {E : Type*}
    (pairing : E → E → ℝ)
    (K : ℕ → Set E)
    (hmono : Monotone K)
    (hself : ∀ n : ℕ, IsSelfDualCone pairing (K n))
    {n : ℕ} {x : E}
    (hx : x ∈ K n) :
    ∀ y, y ∈ Set.iUnion K → 0 ≤ pairing x y := by
  intro y hy
  rcases Set.mem_iUnion.mp hy with ⟨j, hyj⟩
  exact selfDualCone_closed_under_carrier_step pairing K hmono hself hx hyj

/--
Finite-to-colimit positivity for two elements of the directed union.

Both elements have finite-stage witnesses, hence both lie in a common finite
carrier where self-duality gives nonnegative pairing.
-/
theorem selfDualCone_iUnion_pairing_nonneg
    {E : Type*}
    (pairing : E → E → ℝ)
    (K : ℕ → Set E)
    (hmono : Monotone K)
    (hself : ∀ n : ℕ, IsSelfDualCone pairing (K n))
    {x y : E}
    (hx : x ∈ Set.iUnion K)
    (hy : y ∈ Set.iUnion K) :
    0 ≤ pairing x y := by
  rcases Set.mem_iUnion.mp hx with ⟨i, hxi⟩
  rcases Set.mem_iUnion.mp hy with ⟨j, hyj⟩
  exact selfDualCone_closed_under_carrier_step pairing K hmono hself hxi hyj

/--
Directed colimit of self-dual cone carriers.

If `K n` is an increasing sequence of self-dual carriers, then its directed
union is self-dual once the reverse direction is supplied by the explicit
dual-exhaustion premise:

`(∀ y ∈ ⋃ n, K n, 0 ≤ pairing x y) → x ∈ ⋃ n, K n`.

The forward direction is the finite carrier argument: for `x ∈ K i` and
`y ∈ K j`, both lie in the common finite stage `K (max i j)`, where
self-duality gives nonnegativity.
-/
theorem isSelfDualCone_iUnion_nat
    {E : Type*}
    (pairing : E → E → ℝ)
    (K : ℕ → Set E)
    (hmono : Monotone K)
    (hself : ∀ n : ℕ, IsSelfDualCone pairing (K n))
    (hdual_exhaustive :
      ∀ x, (∀ y, y ∈ Set.iUnion K → 0 ≤ pairing x y) → x ∈ Set.iUnion K) :
    IsSelfDualCone pairing (Set.iUnion K) := by
  intro x
  constructor
  · intro hx y hy
    exact selfDualCone_iUnion_pairing_nonneg pairing K hmono hself hx hy
  · intro hpositive
    exact hdual_exhaustive x hpositive

/--
Owner-side colimit extension theorem for an increasing self-dual cone carrier.

This is a named facade over `isSelfDualCone_iUnion_nat`, emphasizing the
finite-carrier-to-colimit extension step and keeping it separate from later
analytic modular-theory claims.
-/
theorem selfDualCone_extends_to_colimit
    {E : Type*}
    (pairing : E → E → ℝ)
    (K : ℕ → Set E)
    (hmono : Monotone K)
    (hself : ∀ n : ℕ, IsSelfDualCone pairing (K n))
    (hdual_exhaustive :
      ∀ x, (∀ y, y ∈ Set.iUnion K → 0 ≤ pairing x y) → x ∈ Set.iUnion K) :
    IsSelfDualCone pairing (Set.iUnion K) := by
  exact isSelfDualCone_iUnion_nat pairing K hmono hself hdual_exhaustive

end InfoGeometry.OperatorAlgebra.SelfDualConeColimit
