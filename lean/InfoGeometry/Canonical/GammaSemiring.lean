import Mathlib.Algebra.Group.Defs
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Algebra.Ring.Defs
import Mathlib.Tactic

/-!
# Binary Gamma-Semiring Laws and Left Gamma-Ideals

This file formalizes the finite algebraic core of binary non-commutative
Gamma-semirings without introducing a proof-carrying carrier object.  A
Gamma-semiring is represented by an explicit ternary operation together with
the predicate `IsGammaSemiringOp`; a left Gamma-ideal is represented by a set
and the predicate `IsLeftGammaIdeal`.

## Audit Protocol Map
- BUCKET 1: CLOSED FINITE THEOREMS:
  `gammaSemiring_op_add_left`, `gammaSemiring_op_add_right`,
  `gammaSemiring_op_add_middle`, `gammaSemiring_op_assoc`,
  `gammaSemiring_op_zero_left`, `gammaSemiring_op_zero_right`,
  `gammaSemiring_op_zero_middle`, `standardGammaOp_isGammaSemiringOp`,
  `leftGammaIdeal_zero_mem`, `leftGammaIdeal_add_mem`,
  `leftGammaIdeal_left_mem`, `mem_leftGammaIdealInter`,
  `leftGammaIdealInter_is_left_ideal`.
- BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT HYPOTHESES:
  `leftGammaIdealInter_is_left_ideal` is conditional on the explicit premises
  that the two input sets are left Gamma-ideals for the supplied operation.
- BUCKET 3: OPEN CLOSURE DEBT:
  Homomorphisms of Gamma-semirings, right and two-sided Gamma-ideals, quotient
  Gamma-semirings, projective bi-Gamma-modules, and idempotent lifting for
  nilpotent Gamma-ideals are not asserted here.
-/

universe u v

namespace InfoGeometry.Canonical

/-- A binary Gamma-operation on `S` with middle parameters in `Gamma`. -/
def GammaOp (S : Type u) (Gamma : Type v) : Type (max u v) :=
  S → Gamma → S → S

/-- Predicate expressing the binary non-commutative Gamma-semiring laws for an operation. -/
def IsGammaSemiringOp {S : Type u} {Gamma : Type v}
    [AddCommMonoid S] [AddCommMonoid Gamma] (op : GammaOp S Gamma) : Prop :=
  (∀ (a b : S) (gamma : Gamma) (c : S),
      op (a + b) gamma c = op a gamma c + op b gamma c) ∧
    (∀ (a : S) (gamma : Gamma) (b c : S),
      op a gamma (b + c) = op a gamma b + op a gamma c) ∧
    (∀ (a : S) (gamma₁ gamma₂ : Gamma) (b : S),
      op a (gamma₁ + gamma₂) b = op a gamma₁ b + op a gamma₂ b) ∧
    (∀ (a : S) (gamma₁ : Gamma) (b : S) (gamma₂ : Gamma) (c : S),
      op (op a gamma₁ b) gamma₂ c = op a gamma₁ (op b gamma₂ c)) ∧
    (∀ (gamma : Gamma) (b : S), op 0 gamma b = 0) ∧
    (∀ (a : S) (gamma : Gamma), op a gamma 0 = 0) ∧
    (∀ (a b : S), op a 0 b = 0)

theorem gammaSemiring_op_add_left {S : Type u} {Gamma : Type v}
    [AddCommMonoid S] [AddCommMonoid Gamma] {op : GammaOp S Gamma}
    (h : IsGammaSemiringOp op) :
    ∀ (a b : S) (gamma : Gamma) (c : S),
      op (a + b) gamma c = op a gamma c + op b gamma c := by
  exact h.1

theorem gammaSemiring_op_add_right {S : Type u} {Gamma : Type v}
    [AddCommMonoid S] [AddCommMonoid Gamma] {op : GammaOp S Gamma}
    (h : IsGammaSemiringOp op) :
    ∀ (a : S) (gamma : Gamma) (b c : S),
      op a gamma (b + c) = op a gamma b + op a gamma c := by
  exact h.2.1

theorem gammaSemiring_op_add_middle {S : Type u} {Gamma : Type v}
    [AddCommMonoid S] [AddCommMonoid Gamma] {op : GammaOp S Gamma}
    (h : IsGammaSemiringOp op) :
    ∀ (a : S) (gamma₁ gamma₂ : Gamma) (b : S),
      op a (gamma₁ + gamma₂) b = op a gamma₁ b + op a gamma₂ b := by
  exact h.2.2.1

theorem gammaSemiring_op_assoc {S : Type u} {Gamma : Type v}
    [AddCommMonoid S] [AddCommMonoid Gamma] {op : GammaOp S Gamma}
    (h : IsGammaSemiringOp op) :
    ∀ (a : S) (gamma₁ : Gamma) (b : S) (gamma₂ : Gamma) (c : S),
      op (op a gamma₁ b) gamma₂ c = op a gamma₁ (op b gamma₂ c) := by
  exact h.2.2.2.1

theorem gammaSemiring_op_zero_left {S : Type u} {Gamma : Type v}
    [AddCommMonoid S] [AddCommMonoid Gamma] {op : GammaOp S Gamma}
    (h : IsGammaSemiringOp op) :
    ∀ (gamma : Gamma) (b : S), op 0 gamma b = 0 := by
  exact h.2.2.2.2.1

theorem gammaSemiring_op_zero_right {S : Type u} {Gamma : Type v}
    [AddCommMonoid S] [AddCommMonoid Gamma] {op : GammaOp S Gamma}
    (h : IsGammaSemiringOp op) :
    ∀ (a : S) (gamma : Gamma), op a gamma 0 = 0 := by
  exact h.2.2.2.2.2.1

theorem gammaSemiring_op_zero_middle {S : Type u} {Gamma : Type v}
    [AddCommMonoid S] [AddCommMonoid Gamma] {op : GammaOp S Gamma}
    (h : IsGammaSemiringOp op) :
    ∀ (a b : S), op a 0 b = 0 := by
  exact h.2.2.2.2.2.2

/-- The canonical Gamma-operation on a semiring, with the same type as middle parameters. -/
def standardGammaOp (S : Type u) [Semiring S] : GammaOp S S :=
  fun a gamma b => a * gamma * b

/-- Any ordinary semiring satisfies the Gamma-semiring laws via `a gamma b = a * gamma * b`. -/
theorem standardGammaOp_isGammaSemiringOp (S : Type u) [Semiring S] :
    IsGammaSemiringOp (standardGammaOp S) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a b gamma c
    dsimp [standardGammaOp]
    rw [add_mul, add_mul]
  · intro a gamma b c
    dsimp [standardGammaOp]
    rw [mul_add]
  · intro a gamma₁ gamma₂ b
    dsimp [standardGammaOp]
    rw [mul_add, add_mul]
  · intro a gamma₁ b gamma₂ c
    dsimp [standardGammaOp]
    simp only [mul_assoc]
  · intro gamma b
    dsimp [standardGammaOp]
    simp only [zero_mul]
  · intro a gamma
    dsimp [standardGammaOp]
    simp only [mul_zero]
  · intro a b
    dsimp [standardGammaOp]
    simp only [mul_zero, zero_mul]

variable {S : Type u} {Gamma : Type v}
variable [AddCommMonoid S]

/-- Predicate for a left Gamma-ideal of a Gamma-operation. -/
def IsLeftGammaIdeal (op : GammaOp S Gamma) (I : Set S) : Prop :=
  (0 : S) ∈ I ∧
    (∀ {x y : S}, x ∈ I → y ∈ I → x + y ∈ I) ∧
    (∀ (s : S) (gamma : Gamma) {x : S}, x ∈ I → op s gamma x ∈ I)

theorem leftGammaIdeal_zero_mem {op : GammaOp S Gamma} {I : Set S}
    (hI : IsLeftGammaIdeal op I) : (0 : S) ∈ I := by
  exact hI.1

theorem leftGammaIdeal_add_mem {op : GammaOp S Gamma} {I : Set S}
    (hI : IsLeftGammaIdeal op I) :
    ∀ {x y : S}, x ∈ I → y ∈ I → x + y ∈ I := by
  exact hI.2.1

theorem leftGammaIdeal_left_mem {op : GammaOp S Gamma} {I : Set S}
    (hI : IsLeftGammaIdeal op I) :
    ∀ (s : S) (gamma : Gamma) {x : S}, x ∈ I → op s gamma x ∈ I := by
  exact hI.2.2

/-- The set-theoretic intersection used for left Gamma-ideals. -/
def leftGammaIdealInter (I J : Set S) : Set S :=
  I ∩ J

omit [AddCommMonoid S] in
@[simp]
theorem mem_leftGammaIdealInter {I J : Set S} {x : S} :
    x ∈ leftGammaIdealInter I J ↔ x ∈ I ∧ x ∈ J :=
  Iff.rfl

/-- The intersection of two left Gamma-ideals is a left Gamma-ideal. -/
theorem leftGammaIdealInter_is_left_ideal
    (op : GammaOp S Gamma) {I J : Set S}
    (hI : IsLeftGammaIdeal op I) (hJ : IsLeftGammaIdeal op J) :
    IsLeftGammaIdeal op (leftGammaIdealInter I J) := by
  rcases hI with ⟨hI_zero, hI_add, hI_left⟩
  rcases hJ with ⟨hJ_zero, hJ_add, hJ_left⟩
  refine ⟨?_, ?_, ?_⟩
  · exact ⟨hI_zero, hJ_zero⟩
  · intro x y hx hy
    exact ⟨hI_add hx.1 hy.1, hJ_add hx.2 hy.2⟩
  · intro s gamma x hx
    exact ⟨hI_left s gamma hx.1, hJ_left s gamma hx.2⟩

end InfoGeometry.Canonical
