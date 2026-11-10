/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Vertex Algebra via the Borcherds Identity

This module gives a purely algebraic vertex-algebra interface. A field is an
integer-indexed family of bilinear mode operations; no formal Laurent series,
topological completion, contour integral, or analytic convergence is used.

The Borcherds identity is represented by finite `Finset.range` sums together
with a positive cutoff after which both summand families vanish. Thus the usual
formally-infinite identity is stored as finite algebraic data.
-/

namespace InfoGeometry.Algebra.Vertex

open scoped BigOperators
open InfoGeometry.Algebra.FiniteSpin

/-- Non-commutativity witness for the finite spin algebra carrier. -/
theorem exists_noncomm_pair :
    ∃ x y : Mat2C, x * y ≠ y * x :=
  ⟨J_plus, J_minus, j_plus_j_minus_ne⟩

section DivisionRingBinom

variable (D : Type*) [DivisionRing D]

/-- Ordered generalized integer binomial coefficient over any `[DivisionRing D]`,
defined via `List.range` product so no commutative multiplication is required. -/
def intBinomList (n : ℤ) (i : ℕ) : D :=
  ((List.range i).map (fun j : ℕ => ((n - (j : ℤ) : ℤ) : D))).prod /
    (Nat.factorial i : D)

@[simp]
theorem intBinomList_zero (n : ℤ) : intBinomList D n 0 = 1 := by
  simp [intBinomList]

@[simp]
theorem intBinomList_one (n : ℤ) : intBinomList D n 1 = (n : D) := by
  simp [intBinomList]

/-- Over any `[DivisionRing D]`, `intBinomList D 0 i = 0` for `i > 0` because the
leading factor `j = 0` in `List.range i` is `0`. -/
@[simp]
theorem intBinomList_zero_of_pos (i : ℕ) (hi : 0 < i) :
    intBinomList D 0 i = 0 := by
  rcases Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hi) with ⟨m, rfl⟩
  unfold intBinomList
  rw [List.range_succ_eq_map, List.map_cons, List.prod_cons]
  simp

end DivisionRingBinom

section FieldVertexSection

variable (k : Type*) [Field k]

/-- Generalized binomial coefficient with an integer upper argument. -/
def intBinom (n : ℤ) (i : ℕ) : k :=
  (∏ j ∈ Finset.range i, ((n - (j : ℤ) : ℤ) : k)) /
    (Nat.factorial i : k)

@[simp]
theorem intBinom_zero (n : ℤ) : intBinom k n 0 = 1 := by
  simp [intBinom]

@[simp]
theorem intBinom_one (n : ℤ) : intBinom k n 1 = (n : k) := by
  simp [intBinom]

/-- The generalized binomial coefficient `0 choose i` vanishes for `i > 0`. -/
@[simp]
theorem intBinom_zero_of_pos (i : ℕ) (hi : 0 < i) :
    intBinom k 0 i = 0 := by
  unfold intBinom
  have hmem : 0 ∈ Finset.range i :=
    Finset.mem_range.mpr hi
  have hnum :
      (∏ j ∈ Finset.range i,
        (((0 : ℤ) - (j : ℤ) : ℤ) : k)) = 0 := by
    apply Finset.prod_eq_zero hmem
    simp
  rw [hnum]
  exact zero_div _

variable {k : Type*} {V : Type*}
variable [Field k] [CharZero k] [AddCommGroup V] [Module k V]

/-- Integer-indexed bilinear mode operations `a_(n) b`. -/
abbrev Mode :=
  ℤ → V →ₗ[k] V →ₗ[k] V

/-- The `i`th summand on the iterate side of the Borcherds identity. -/
def borcherdsLhsTerm (mode : Mode (k := k) (V := V))
    (m n ell : ℤ) (a b c : V) (i : ℕ) : V :=
  intBinom k m i •
    mode (m + ell - (i : ℤ)) (mode (n + (i : ℤ)) a b) c

/-- The `i`th summand on the commutator side of the Borcherds identity. -/
def borcherdsRhsTerm (mode : Mode (k := k) (V := V))
    (m n ell : ℤ) (a b c : V) (i : ℕ) : V :=
  (((-1 : k) ^ i) * intBinom k n i) •
    (mode (m + n - (i : ℤ)) a (mode (ell + (i : ℤ)) b c) -
      ((-1 : k) ^ n) •
        mode (n + ell - (i : ℤ)) b (mode (m + (i : ℤ)) a c))

/-- A vertex algebra presented by modes and the finite Borcherds identity. -/
class VertexAlgebra (k : Type*) (V : Type*)
    [Field k] [CharZero k] [AddCommGroup V] [Module k V] where
  vacuum : V
  translation : V →ₗ[k] V
  mode : Mode (k := k) (V := V)
  truncation :
    ∀ a b : V, ∃ N : ℤ, ∀ n : ℤ, N ≤ n → mode n a b = 0
  vacuum_mode_negOne :
    ∀ a : V, mode (-1) vacuum a = a
  vacuum_mode_of_ne_negOne :
    ∀ n : ℤ, n ≠ -1 → ∀ a : V, mode n vacuum a = 0
  creation :
    ∀ a : V, mode (-1) a vacuum = a
  creation_of_nonneg :
    ∀ n : ℤ, 0 ≤ n → ∀ a : V, mode n a vacuum = 0
  translation_vacuum :
    translation vacuum = 0
  translation_commutator :
    ∀ n : ℤ, ∀ a b : V,
      translation (mode n a b) - mode n a (translation b) =
        mode n (translation a) b
  translation_derivative :
    ∀ n : ℤ, ∀ a b : V,
      mode n (translation a) b = (-n : k) • mode (n - 1) a b
  /-- Borcherds identity with an explicit common positive finite cutoff. -/
  borcherds :
    ∀ (m n ell : ℤ) (a b c : V), ∃ N : ℕ,
      0 < N ∧
        (∀ i : ℕ, N ≤ i →
          borcherdsLhsTerm mode m n ell a b c i = 0 ∧
          borcherdsRhsTerm mode m n ell a b c i = 0) ∧
        (∑ i ∈ Finset.range N,
            borcherdsLhsTerm mode m n ell a b c i) =
          ∑ i ∈ Finset.range N,
            borcherdsRhsTerm mode m n ell a b c i

namespace VertexAlgebra

variable (A : VertexAlgebra k V)

@[simp]
theorem vacuum_mode (n : ℤ) (a : V) :
    A.mode n A.vacuum a = if n = -1 then a else 0 := by
  split_ifs with h
  · subst n
    exact A.vacuum_mode_negOne a
  · exact A.vacuum_mode_of_ne_negOne n h a

@[simp]
theorem mode_negOne_vacuum (a : V) :
    A.mode (-1) a A.vacuum = a :=
  A.creation a

theorem mode_vacuum_of_nonneg (n : ℤ) (hn : 0 ≤ n) (a : V) :
    A.mode n a A.vacuum = 0 :=
  A.creation_of_nonneg n hn a

end VertexAlgebra

/-- A conformal vertex algebra whose Virasoro operators are modes of a
distinguished conformal vector. -/
class ConformalVertexAlgebra (k : Type*) (V : Type*)
    [Field k] [CharZero k] [AddCommGroup V] [Module k V]
    extends VertexAlgebra k V where
  conformalVector : V
  centralCharge : k
  L : ℤ → V →ₗ[k] V
  L_eq_mode :
    ∀ n : ℤ,
      L n = toVertexAlgebra.mode (n + 1) conformalVector
  L_negOne_eq_translation :
    L (-1) = toVertexAlgebra.translation
  virasoro :
    ∀ m n : ℤ,
      L m * L n - L n * L m =
        ((m - n : ℤ) : k) • L (m + n) +
          (if m + n = 0 then
            ((((m : k) ^ 3 - (m : k)) * centralCharge / 12) •
              (LinearMap.id : V →ₗ[k] V))
          else 0)

/-- An integral symmetric lattice whose norm is even. -/
structure EvenIntegralLattice (L : Type*) [AddCommGroup L] where
  pairing : L →+ L →+ ℤ
  symmetric : ∀ x y, pairing x y = pairing y x
  even : ∀ x, Even (pairing x x)

/-- Concrete ground inhabitant of `EvenIntegralLattice` over `ℤ` with doubled product `(x, y) ↦ 2 * x * y`. -/
def intEvenLattice : EvenIntegralLattice ℤ where
  pairing :=
    { toFun := fun x =>
        { toFun := fun y => 2 * x * y
          map_zero' := by ring
          map_add' := fun y z => by ring }
      map_zero' := AddMonoidHom.ext fun y => by change 2 * (0 : ℤ) * y = 0; ring
      map_add' := fun x₁ x₂ => AddMonoidHom.ext fun y => by
        change 2 * (x₁ + x₂) * y = 2 * x₁ * y + 2 * x₂ * y
        ring }
  symmetric x y := by change 2 * x * y = 2 * y * x; ring
  even x := ⟨x * x, by change 2 * x * x = x * x + x * x; ring⟩

/-- Algebraic lattice-vertex-algebra data. -/
class LatticeVertexAlgebra (k : Type*) (V : Type*) (L : Type*)
    [Field k] [CharZero k] [AddCommGroup V] [Module k V]
    [AddCommGroup L]
    extends VertexAlgebra k V where
  lattice : EvenIntegralLattice L
  latticeEmbedding : L →+ V

/-- A conformal vertex algebra equipped with a specified group action.

Analytic moonshine assertions are intentionally outside this algebraic owner.
-/
class MonsterVOA (k : Type*) (V : Type*) (G : Type*)
    [Field k] [CharZero k] [AddCommGroup V] [Module k V]
    [Group G]
    extends ConformalVertexAlgebra k V where
  action : G →* (V ≃ₗ[k] V)
  preservesConformalVector :
    ∀ g : G,
      action g conformalVector = conformalVector

end FieldVertexSection

/-- Concrete ground inhabitant of `VertexAlgebra` on the zero module `PUnit` over `ℚ`. -/
@[instance_reducible]
def unitVertexAlgebra : VertexAlgebra ℚ PUnit where
  vacuum := 0
  translation := 0
  mode := fun _ => 0
  truncation := fun _ _ => ⟨0, fun _ _ => rfl⟩
  vacuum_mode_negOne := fun _ => Subsingleton.elim _ _
  vacuum_mode_of_ne_negOne := fun _ _ _ => rfl
  creation := fun _ => Subsingleton.elim _ _
  creation_of_nonneg := fun _ _ _ => rfl
  translation_vacuum := rfl
  translation_commutator := fun _ _ _ => Subsingleton.elim _ _
  translation_derivative := fun _ _ _ => Subsingleton.elim _ _
  borcherds := fun _ _ _ _ _ _ =>
    ⟨1, Nat.one_pos, ⟨fun _ _ => ⟨Subsingleton.elim _ _, Subsingleton.elim _ _⟩,
      Subsingleton.elim _ _⟩⟩

/-- Concrete ground inhabitant of `ConformalVertexAlgebra` on `PUnit` over `ℚ`. -/
@[instance_reducible]
def unitConformalVertexAlgebra : ConformalVertexAlgebra ℚ PUnit where
  __ := unitVertexAlgebra
  conformalVector := 0
  centralCharge := 0
  L := fun _ => 0
  L_eq_mode := fun _ => rfl
  L_negOne_eq_translation := rfl
  virasoro := fun _ _ => Subsingleton.elim _ _

/-- Concrete ground inhabitant of `LatticeVertexAlgebra` on `PUnit` over `ℚ` with `intEvenLattice`. -/
@[instance_reducible]
def unitLatticeVertexAlgebra : LatticeVertexAlgebra ℚ PUnit ℤ where
  __ := unitVertexAlgebra
  lattice := intEvenLattice
  latticeEmbedding := 0

/-- Concrete ground inhabitant of `MonsterVOA` on `PUnit` over `ℚ` with `Multiplicative PUnit`. -/
@[instance_reducible]
def unitMonsterVOA : MonsterVOA ℚ PUnit (Multiplicative PUnit) where
  __ := unitConformalVertexAlgebra
  action := 1
  preservesConformalVector := fun _ => Subsingleton.elim _ _

end InfoGeometry.Algebra.Vertex
