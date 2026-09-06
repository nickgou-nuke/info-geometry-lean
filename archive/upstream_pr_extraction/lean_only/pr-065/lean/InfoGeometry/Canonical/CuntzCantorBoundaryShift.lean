import Mathlib.Tactic
import InfoGeometry.Canonical.UHFInductiveColimitBoundary

/-!
# Cuntz-Cantor Boundary Shift

This module adds the finite boundary-action layer for the binary Cuntz-style
prefix shifts on the Cantor carrier used by `UHFInductiveColimitBoundary`.

The closed layer is deliberately topological/algebraic and finite-stage:
* prepend a binary branch bit to a Cantor boundary point;
* drop the head bit with the tail map;
* prove branch injectivity, disjointness, and cover;
* prove branch pullback of a finite cylinder is again a finite cylinder.

No Hilbert-space representation, C*-completion, Cuntz partial isometry theorem,
KMS state, measure theory, or zeta/RH consequence is asserted here.

#### BUCKET 1: CLOSED FINITE THEOREMS
`tail_prependBit`, `prependBit_head`, `prependBit_injective`,
`prependBit_tail_of_head`, `prependBit_range_cover`,
`prependBit_false_true_disjoint`, `boundaryPrefix_prependBit`, and
`cylinder_branch_pullback`.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES
None.

#### BUCKET 3: OPEN CLOSURE DEBT
Full Cuntz `O₂` partial-isometry representation, Hilbert-space adjoints,
orthogonal range projections, KMS dynamics, and analytic/zeta interpretations.
-/

noncomputable section

namespace InfoGeometry.Canonical.CuntzCantorBoundaryShift

open InfoGeometry.Canonical.UHFInductiveColimitBoundary

/-- Prepend one branch bit to an infinite Cantor boundary point. -/
def prependBit (b : Bool) (x : (ℕ → Bool)) : (ℕ → Bool) :=
  fun n => if n = 0 then b else x (n - 1)

/-- Drop the head bit of an infinite Cantor boundary point. -/
def tail (x : (ℕ → Bool)) : (ℕ → Bool) :=
  fun n => x (n + 1)

/-- Finite prefix obtained by prepending a branch bit to a word. -/
def branchPrefix (n : ℕ) (b : Bool) (w : BitWord n) : BitWord (n + 1) :=
  fun i =>
    if h : i.1 = 0 then b
    else w ⟨i.1 - 1, by omega⟩

@[simp] theorem prependBit_zero (b : Bool) (x : (ℕ → Bool)) :
    prependBit b x 0 = b := by
  simp [prependBit]

@[simp] theorem prependBit_succ (b : Bool) (x : (ℕ → Bool)) (n : ℕ) :
    prependBit b x (n + 1) = x n := by
  simp [prependBit]

@[simp] theorem tail_apply (x : (ℕ → Bool)) (n : ℕ) :
    tail x n = x (n + 1) := rfl

theorem continuous_prependBit (b : Bool) :
    Continuous (prependBit b) := by
  apply continuous_pi
  intro n
  cases n with
  | zero => exact continuous_const
  | succ n =>
      simpa [prependBit] using (continuous_apply n :
        Continuous (fun x : (ℕ → Bool) => x n))

theorem continuous_tail :
    Continuous tail := by
  apply continuous_pi
  intro n
  simpa [tail] using (continuous_apply (n + 1) :
    Continuous (fun x : (ℕ → Bool) => x (n + 1)))

/-- Dropping the head after prepending a branch bit recovers the old boundary. -/
theorem tail_prependBit (b : Bool) (x : (ℕ → Bool)) :
    tail (prependBit b x) = x := by
  ext n
  simp [tail]

theorem tail_surjective :
    Function.Surjective tail := by
  intro x
  exact ⟨prependBit false x, tail_prependBit false x⟩

/-- The head of a prepended boundary is the prepended branch bit. -/
theorem prependBit_head (b : Bool) (x : (ℕ → Bool)) :
    prependBit b x 0 = b := by
  simp

/-- Each fixed branch-prepend map is injective. -/
theorem prependBit_injective (b : Bool) :
    Function.Injective (prependBit b) := by
  intro x y hxy
  have htail := congrArg tail hxy
  simpa [tail_prependBit] using htail

/-- A boundary whose head is `b` is recovered by prepending `b` to its tail. -/
theorem prependBit_tail_of_head {x : (ℕ → Bool)} {b : Bool} (h : x 0 = b) :
    prependBit b (tail x) = x := by
  ext n
  cases n with
  | zero =>
      simpa using h.symm
  | succ n =>
      simp [tail]

/-- The two branch maps cover the full Cantor boundary. -/
theorem prependBit_range_cover (x : (ℕ → Bool)) :
    x ∈ Set.range (prependBit false) ∪ Set.range (prependBit true) := by
  cases hx : x 0
  · left
    exact ⟨tail x, prependBit_tail_of_head hx⟩
  · right
    exact ⟨tail x, prependBit_tail_of_head hx⟩

/-- The two branch ranges are disjoint. -/
theorem prependBit_false_true_disjoint :
    Disjoint (Set.range (prependBit false)) (Set.range (prependBit true)) := by
  rw [Set.disjoint_left]
  intro x hxFalse hxTrue
  rcases hxFalse with ⟨a, rfl⟩
  rcases hxTrue with ⟨b, h⟩
  have hhead := congrFun h 0
  simp at hhead

@[simp] theorem branchPrefix_zero (n : ℕ) (b : Bool) (w : BitWord n) :
    branchPrefix n b w ⟨0, Nat.succ_pos n⟩ = b := by
  simp [branchPrefix]

@[simp] theorem branchPrefix_succ (n : ℕ) (b : Bool) (w : BitWord n) (i : Fin n) :
    branchPrefix n b w ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩ = w i := by
  simp [branchPrefix]

/-- Prefixes commute with branch prepending. -/
theorem boundaryPrefix_prependBit (n : ℕ) (b : Bool) (x : (ℕ → Bool)) :
    boundaryPrefix (n + 1) (prependBit b x) =
      branchPrefix n b (boundaryPrefix n x) := by
  ext i
  by_cases h : i.1 = 0
  · simp [boundaryPrefix, branchPrefix, prependBit, h]
  · simp [boundaryPrefix, branchPrefix, prependBit, h]

/-- Pull back a stage `n+1` diagonal observable along a branch. -/
def branchPullback (n : ℕ) (b : Bool) (f : DiagAlg (n + 1)) : DiagAlg n :=
  fun w => f (branchPrefix n b w)

@[simp] theorem branchPullback_zero (n : ℕ) (b : Bool) :
    branchPullback n b (0 : DiagAlg (n + 1)) = 0 := by
  rfl

@[simp] theorem branchPullback_one (n : ℕ) (b : Bool) :
    branchPullback n b (1 : DiagAlg (n + 1)) = 1 := by
  rfl

theorem branchPullback_add
    (n : ℕ) (b : Bool) (f g : DiagAlg (n + 1)) :
    branchPullback n b (f + g) =
      branchPullback n b f + branchPullback n b g := by
  rfl

theorem branchPullback_mul
    (n : ℕ) (b : Bool) (f g : DiagAlg (n + 1)) :
    branchPullback n b (f * g) =
      branchPullback n b f * branchPullback n b g := by
  rfl

theorem branchPullback_star
    (n : ℕ) (b : Bool) (f : DiagAlg (n + 1)) :
    branchPullback n b (star f) =
      star (branchPullback n b f) := by
  rfl

theorem branchPullback_smul
    (n : ℕ) (b : Bool) (c : ℂ) (f : DiagAlg (n + 1)) :
    branchPullback n b (c • f) =
      c • branchPullback n b f := by
  rfl

theorem branchPullback_surjective
    (n : ℕ) (b : Bool) :
    Function.Surjective (branchPullback n b) := by
  intro g
  let f : DiagAlg (n + 1) := fun w =>
    if w ⟨0, Nat.succ_pos n⟩ = b then
      g (fun i => w ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩)
    else 0
  refine ⟨f, ?_⟩
  funext w
  change
    (if branchPrefix n b w ⟨0, Nat.succ_pos n⟩ = b then
        g (fun i => branchPrefix n b w
          ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩)
      else 0) = g w
  rw [branchPrefix_zero]
  rw [if_pos rfl]
  apply congrArg g
  funext i
  exact branchPrefix_succ n b w i

theorem branchPullback_eq_zero_iff
    (n : ℕ) (b : Bool) (f : DiagAlg (n + 1)) :
    branchPullback n b f = 0 ↔
      ∀ w : BitWord n, f (branchPrefix n b w) = 0 := by
  constructor
  · intro h w
    have hw := congrFun h w
    simpa [branchPullback] using hw
  · intro h
    funext w
    simp [branchPullback, h]

theorem branchPrefix_head_tail (n : ℕ) (w : BitWord (n + 1)) :
    branchPrefix n (w ⟨0, Nat.succ_pos n⟩)
        (fun i : Fin n => w ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩) = w := by
  funext i
  by_cases hi : i.1 = 0
  · have hi0 : i = (0 : Fin (n + 1)) := Fin.ext hi
    subst i
    rfl
  · simp [branchPrefix, hi]
    apply congrArg w
    apply Fin.ext
    exact Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hi)

theorem branchPullback_pair_injective (n : ℕ) :
    Function.Injective (fun f : DiagAlg (n + 1) =>
      (branchPullback n false f, branchPullback n true f)) := by
  intro f g h
  funext w
  let tail : BitWord n :=
    fun i => w ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩
  have htail :
      branchPrefix n (w ⟨0, Nat.succ_pos n⟩) tail = w := by
    simpa [tail] using branchPrefix_head_tail n w
  cases hb : w ⟨0, Nat.succ_pos n⟩ with
  | false =>
      have htailFalse : branchPrefix n false tail = w := by
        rw [← hb]
        exact htail
      have hh : branchPullback n false f tail =
          branchPullback n false g tail :=
        congrFun (congrArg (fun p => p.1) h) tail
      calc
        f w = f (branchPrefix n false tail) := by rw [htailFalse]
        _ = g (branchPrefix n false tail) := by simpa [branchPullback] using hh
        _ = g w := by rw [htailFalse]
  | true =>
      have htailTrue : branchPrefix n true tail = w := by
        rw [← hb]
        exact htail
      have hh : branchPullback n true f tail =
          branchPullback n true g tail :=
        congrFun (congrArg (fun p => p.2) h) tail
      calc
        f w = f (branchPrefix n true tail) := by rw [htailTrue]
        _ = g (branchPrefix n true tail) := by simpa [branchPullback] using hh
        _ = g w := by rw [htailTrue]

theorem branchPullback_pair_surjective (n : ℕ) :
    Function.Surjective (fun f : DiagAlg (n + 1) =>
      (branchPullback n false f, branchPullback n true f)) := by
  intro p
  let f : DiagAlg (n + 1) := fun z =>
    if z ⟨0, Nat.succ_pos n⟩ = false then
      p.1 (fun i => z ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩)
    else
      p.2 (fun i => z ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩)
  refine ⟨f, ?_⟩
  apply Prod.ext
  · funext w
    change f (branchPrefix n false w) = p.1 w
    dsimp [f]
    change (if branchPrefix n false w ⟨0, Nat.succ_pos n⟩ = false then _ else _) = _
    rw [branchPrefix_zero]
    apply congrArg p.1
    funext i
    exact branchPrefix_succ n false w i
  · funext w
    change f (branchPrefix n true w) = p.2 w
    dsimp [f]
    change (if branchPrefix n true w ⟨0, Nat.succ_pos n⟩ = false then _ else _) = _
    rw [branchPrefix_zero]
    simp only [Bool.true_eq_false, if_false]
    apply congrArg p.2
    funext i
    exact branchPrefix_succ n true w i

theorem branchPullback_pair_bijective (n : ℕ) :
    Function.Bijective (fun f : DiagAlg (n + 1) =>
      (branchPullback n false f, branchPullback n true f)) :=
  ⟨branchPullback_pair_injective n, branchPullback_pair_surjective n⟩

theorem branchPullback_pair_one (n : ℕ) :
    (branchPullback n false (1 : DiagAlg (n + 1)),
      branchPullback n true (1 : DiagAlg (n + 1))) =
      (1 : DiagAlg n × DiagAlg n) := by
  apply Prod.ext
  · exact branchPullback_one n false
  · exact branchPullback_one n true

theorem branchPullback_pair_add
    (n : ℕ) (f g : DiagAlg (n + 1)) :
    (branchPullback n false (f + g), branchPullback n true (f + g)) =
      (branchPullback n false f, branchPullback n true f) +
        (branchPullback n false g, branchPullback n true g) := by
  apply Prod.ext
  · exact branchPullback_add n false f g
  · exact branchPullback_add n true f g

theorem branchPullback_pair_mul
    (n : ℕ) (f g : DiagAlg (n + 1)) :
    (branchPullback n false (f * g), branchPullback n true (f * g)) =
      (branchPullback n false f, branchPullback n true f) *
        (branchPullback n false g, branchPullback n true g) := by
  apply Prod.ext
  · exact branchPullback_mul n false f g
  · exact branchPullback_mul n true f g

theorem branchPullback_pair_star
    (n : ℕ) (f : DiagAlg (n + 1)) :
    (branchPullback n false (star f), branchPullback n true (star f)) =
      star (branchPullback n false f, branchPullback n true f) := by
  apply Prod.ext
  · exact branchPullback_star n false f
  · exact branchPullback_star n true f

/-- Pulling a finite cylinder back along a branch is again a finite cylinder. -/
theorem cylinder_branch_pullback (n : ℕ) (b : Bool) (f : DiagAlg (n + 1)) :
    (fun x : (ℕ → Bool) => cylinder (n + 1) f (prependBit b x)) =
      cylinder n (branchPullback n b f) := by
  ext x
  simp [cylinder, branchPullback, boundaryPrefix_prependBit]

/-- Branch pullbacks of finite cylinders remain in the finite cylinder colimit. -/
theorem branch_pullback_mem_colimit (n : ℕ) (b : Bool) (f : DiagAlg (n + 1)) :
    cylinder n (branchPullback n b f) ∈ CylinderColimit := by
  exact cylinder_mem_colimit n (branchPullback n b f)

/-- Synthesis theorem combining branch coverage and cylinder pullback coherence. -/
theorem finite_cuntz_cantor_shift_synthesis :
    Function.Injective (prependBit false) ∧
    Function.Injective (prependBit true) ∧
    Disjoint (Set.range (prependBit false)) (Set.range (prependBit true)) ∧
    (∀ x : (ℕ → Bool), x ∈ Set.range (prependBit false) ∪ Set.range (prependBit true)) ∧
    (∀ n : ℕ, ∀ b : Bool, ∀ f : DiagAlg (n + 1),
      (fun x : (ℕ → Bool) => cylinder (n + 1) f (prependBit b x)) =
        cylinder n (branchPullback n b f)) ∧
    (∀ n : ℕ, ∀ b : Bool, ∀ f : DiagAlg (n + 1),
      cylinder n (branchPullback n b f) ∈ CylinderColimit) :=
  ⟨prependBit_injective false, prependBit_injective true, prependBit_false_true_disjoint,
   prependBit_range_cover, cylinder_branch_pullback, branch_pullback_mem_colimit⟩

end InfoGeometry.Canonical.CuntzCantorBoundaryShift

end noncomputable section
