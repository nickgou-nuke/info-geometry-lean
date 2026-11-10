/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Clifford.Cl11TensorTowerLimit
import InfoGeometry.Algebra.DirectLimitSuperClosureLemmas

/-!
# Recursive commutators on the unbounded `Cl(1,1)` operator colimit

The coefficient operators live in the existing algebraic direct limit of the
growing full-matrix Clifford stages.  A natural number in this file is a finite
commutator depth or a finite head cutoff; it does not bound the dimension of
the limit algebra.  We prove stage compatibility for every finite recursive
commutator depth, a common-head representative theorem for any pair of limit
operators, and transport of coherent recursive operator families to the
same limit value.

## BUCKET 1: Proved in the existing algebraic Clifford colimit

The stage injections, direct-limit representative principle, and infinite
dimensionality are owned by imported modules. This file proves recursive
commutator transport and common-head representation.

## BUCKET 2: Conditional consequences

No theorem here assumes an external certificate or an unproved operator law.

## BUCKET 3: Open boundary

No analytic completion, infinite commutator series, or continuity claim is
made here.
-/

noncomputable section

namespace InfoGeometry.Clifford.Cl11RecursiveCommutatorColimit

open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Clifford.Cl11TensorTowerLimit
open InfoGeometry.Algebra.DirectLimitSuperClosureLemmas

/-- The associative-ring commutator, with its order fixed as `xy - yx`. -/
def commutator {R : Type*} [Ring R] (x y : R) : R := x * y - y * x

/-- `k` successive adjoint commutators by `a`, starting from `x`.

The recursion depth is finite for each value of `k`; the operator carrier may
be the infinite-dimensional direct limit. -/
def iteratedCommutator {R : Type*} [Ring R] (a : R) : ℕ → R → R
  | 0, x => x
  | k + 1, x => commutator a (iteratedCommutator a k x)

/-- A ring homomorphism preserves the ordered commutator `xy - yx`. -/
@[simp]
theorem map_commutator {R S : Type*} [Ring R] [Ring S]
    (f : R →+* S) (x y : R) :
    f (commutator x y) = commutator (f x) (f y) := by
  calc
    f (commutator x y) = f (x * y) - f (y * x) := by
      exact map_sub f (x * y) (y * x)
    _ = f x * f y - f y * f x := by
      rw [map_mul, map_mul]

/-- Ring homomorphisms preserve every finite recursive commutator word. -/
theorem map_iteratedCommutator {R S : Type*} [Ring R] [Ring S]
    (f : R →+* S) (a x : R) (k : ℕ) :
    f (iteratedCommutator a k x) =
      iteratedCommutator (f a) k (f x) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      simp [iteratedCommutator, ih, map_commutator]

/-- The tower bond preserves all recursive commutators, at every head stage. -/
theorem stageEmbed_iteratedCommutator (n k : ℕ) (a x : Stage n) :
    stageEmbed n (iteratedCommutator a k x) =
      iteratedCommutator (stageEmbed n a) k (stageEmbed n x) := by
  simpa [stageBond] using
    map_iteratedCommutator (stageBond n) a x k

/-- The canonical map into the actual colimit preserves all recursive
commutators at any common finite head stage. -/
theorem ofStage_iteratedCommutator (n k : ℕ) (a x : Stage n) :
    ofStage n (iteratedCommutator a k x) =
      iteratedCommutator (ofStage n a) k (ofStage n x) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      simp only [iteratedCommutator, commutator, ofStage_sub,
        ofStage_mul, ih]

/-- Every pair of operators in the direct limit has representatives at one
common finite Clifford head.  This is the common-stage content of filteredness,
not a finite-dimensionality assertion about `Limit`. -/
theorem exists_common_head_representatives (a x : Limit) :
    ∃ n : ℕ, ∃ aₙ xₙ : Stage n,
      ofStage n aₙ = a ∧ ofStage n xₙ = x := by
  induction a, x using DirectLimit.induction₂ with
  | _ n aₙ xₙ => exact ⟨n, aₙ, xₙ, rfl, rfl⟩

/-- Every finite list of operators in the direct limit has representatives at
one common finite tensor head. The head may grow with the list; the limit
operator algebra itself is not assigned a finite matrix dimension. -/
theorem exists_common_head_representatives_list (xs : List Limit) :
    ∃ n : ℕ, ∃ xsₙ : List (Stage n), xsₙ.map (ofStage n) = xs := by
  induction xs with
  | nil => exact ⟨0, [], rfl⟩
  | cons x xs ih =>
      obtain ⟨n, xsₙ, hxs⟩ := ih
      obtain ⟨m, xₘ, hxₘ⟩ :=
        DirectLimit.exists_eq_mk
          (f := fun i j h => bondMap stageBond i j h) x
      let N := max m n
      have hmN : m ≤ N := Nat.le_max_left m n
      have hnN : n ≤ N := Nat.le_max_right m n
      refine ⟨N, bondMap stageBond m N hmN xₘ ::
        xsₙ.map (bondMap stageBond n N hnN), ?_⟩
      simp only [List.map_cons]
      rw [List.map_map]
      simp only [List.cons.injEq]
      constructor
      · change directLimitOf stageBond N (bondMap stageBond m N hmN xₘ) = x
        calc
          directLimitOf stageBond N (bondMap stageBond m N hmN xₘ) =
              directLimitOf stageBond m xₘ :=
                directLimitOf_bondMap stageBond m N hmN xₘ
          _ = x := by simpa [ofStage] using hxₘ.symm
      · rw [← hxs]
        apply List.map_congr_left
        intro y hy
        exact directLimitOf_bondMap stageBond n N hnN y

/-- The product of a finite family of limit operators is the image of the
ordered product of representatives at a single finite head. This is the
finite-expression transport law for the algebraic operator colimit. -/
theorem finite_operator_product_has_common_head (xs : List Limit) :
    ∃ n : ℕ, ∃ xsₙ : List (Stage n),
      xsₙ.map (ofStage n) = xs ∧ ofStage n xsₙ.prod = xs.prod := by
  obtain ⟨n, xsₙ, hxs⟩ := exists_common_head_representatives_list xs
  refine ⟨n, xsₙ, hxs, ?_⟩
  rw [map_list_prod, hxs]

/-- Any finite-depth commutator word on two arbitrary limit operators is
represented by the same recursive word at a common finite tensor head. -/
theorem iteratedCommutator_has_common_head (a x : Limit) (k : ℕ) :
    ∃ n : ℕ, ∃ aₙ xₙ : Stage n,
      ofStage n aₙ = a ∧ ofStage n xₙ = x ∧
      iteratedCommutator a k x =
        ofStage n (iteratedCommutator aₙ k xₙ) := by
  induction a, x using DirectLimit.induction₂ with
  | _ n aₙ xₙ =>
      exact ⟨n, aₙ, xₙ, rfl, rfl,
        (ofStage_iteratedCommutator n k aₙ xₙ).symm⟩

/-- One finite tensor head represents the entire natural-number-indexed
iterated-commutator orbit generated by any two elements of the colimit. The
head depends on the two starting operators, but not on the commutator depth. -/
theorem iteratedCommutator_orbit_has_uniform_head (a x : Limit) :
    ∃ n : ℕ, ∃ aₙ xₙ : Stage n,
      ofStage n aₙ = a ∧ ofStage n xₙ = x ∧
      ∀ k : ℕ,
        iteratedCommutator a k x =
          ofStage n (iteratedCommutator aₙ k xₙ) := by
  obtain ⟨n, aₙ, xₙ, ha, hx⟩ := exists_common_head_representatives a x
  refine ⟨n, aₙ, xₙ, ha, hx, ?_⟩
  intro k
  calc
    iteratedCommutator a k x =
        iteratedCommutator (ofStage n aₙ) k (ofStage n xₙ) := by
          rw [ha, hx]
    _ = ofStage n (iteratedCommutator aₙ k xₙ) :=
      (ofStage_iteratedCommutator n k aₙ xₙ).symm

/-- Equality between recursive commutator words represented at different
finite heads is detected exactly at their common head `max n m`. Thus the
algebraic direct limit creates no extra equality between finite operator words:
any equality in `Limit` is already visible after transporting both words to a
single finite tensor stage. The statement is uniform in the finite
commutator depth and makes no finite-dimensionality claim about `Limit`. -/
theorem iteratedCommutator_eq_iff_common_head
    (n m : ℕ) (aₙ xₙ : Stage n) (bₘ yₘ : Stage m) :
    (∀ k : ℕ,
      iteratedCommutator (ofStage n aₙ) k (ofStage n xₙ) =
        iteratedCommutator (ofStage m bₘ) k (ofStage m yₘ)) ↔
    (∀ k : ℕ,
      iteratedCommutator
          (bondMap stageBond n (max n m) (Nat.le_max_left n m) aₙ) k
          (bondMap stageBond n (max n m) (Nat.le_max_left n m) xₙ) =
        iteratedCommutator
          (bondMap stageBond m (max n m) (Nat.le_max_right n m) bₘ) k
          (bondMap stageBond m (max n m) (Nat.le_max_right n m) yₘ)) := by
  let N := max n m
  let fa := bondMap stageBond n N (Nat.le_max_left n m)
  let fb := bondMap stageBond m N (Nat.le_max_right n m)
  have hfa (k : ℕ) :
      iteratedCommutator (ofStage n aₙ) k (ofStage n xₙ) =
        ofStage N (iteratedCommutator (fa aₙ) k (fa xₙ)) := by
    calc
      iteratedCommutator (ofStage n aₙ) k (ofStage n xₙ) =
          ofStage n (iteratedCommutator aₙ k xₙ) :=
        (ofStage_iteratedCommutator n k aₙ xₙ).symm
      _ = ofStage N (fa (iteratedCommutator aₙ k xₙ)) := by
        exact (directLimitOf_bondMap stageBond n N (Nat.le_max_left n m) _).symm
      _ = ofStage N (iteratedCommutator (fa aₙ) k (fa xₙ)) := by
        rw [map_iteratedCommutator]
  have hfb (k : ℕ) :
      iteratedCommutator (ofStage m bₘ) k (ofStage m yₘ) =
        ofStage N (iteratedCommutator (fb bₘ) k (fb yₘ)) := by
    calc
      iteratedCommutator (ofStage m bₘ) k (ofStage m yₘ) =
          ofStage m (iteratedCommutator bₘ k yₘ) :=
        (ofStage_iteratedCommutator m k bₘ yₘ).symm
      _ = ofStage N (fb (iteratedCommutator bₘ k yₘ)) := by
        exact (directLimitOf_bondMap stageBond m N (Nat.le_max_right n m) _).symm
      _ = ofStage N (iteratedCommutator (fb bₘ) k (fb yₘ)) := by
        rw [map_iteratedCommutator]
  have hinj : Function.Injective (ofStage N) :=
    directLimitOf_injective stageBond (fun j => matStageEmbed_injective j) N
  constructor
  · intro h k
    apply hinj
    rw [← hfa k, ← hfb k]
    exact h k
  · intro h k
    rw [hfa k, hfb k]
    exact congrArg (ofStage N) (h k)

/-- A coherent pair of stagewise operator families has a coherent recursive
commutator family at every fixed finite depth. -/
theorem stageEmbed_coherent_iteratedCommutator
    (A X : ∀ n : ℕ, Stage n)
    (hA : ∀ n, stageEmbed n (A n) = A (n + 1))
    (hX : ∀ n, stageEmbed n (X n) = X (n + 1)) (k : ℕ) :
    ∀ n, stageEmbed n (iteratedCommutator (A n) k (X n)) =
      iteratedCommutator (A (n + 1)) k (X (n + 1)) := by
  intro n
  rw [stageEmbed_iteratedCommutator, hA n, hX n]

/-- Coherent recursive commutators at all finite heads agree in the algebraic
colimit with their initial head value. -/
theorem coherent_iteratedCommutator_in_limit
    (A X : ∀ n : ℕ, Stage n)
    (hA : ∀ n, stageEmbed n (A n) = A (n + 1))
    (hX : ∀ n, stageEmbed n (X n) = X (n + 1)) (k n : ℕ) :
    ofStage n (iteratedCommutator (A n) k (X n)) =
      ofStage 0 (iteratedCommutator (A 0) k (X 0)) := by
  let W : ∀ m : ℕ, Stage m := fun m => iteratedCommutator (A m) k (X m)
  have hW : ∀ m, stageEmbed m (W m) = W (m + 1) :=
    stageEmbed_coherent_iteratedCommutator A X hA hX k
  exact finite_sequence_constant_in_limit W hW n

/-! ## Residual reconstruction in the operator colimit

The cited hyperbolic residual-quantization construction uses a non-associative
gyrogroup law and a specific left-cancellation identity.  The theorem below
formalizes only the algebraic pattern that transfers without that geometry:
in the additive group of the actual operator colimit, subtracting each
increment from the residual and then aggregating the increments in reverse
nested order reconstructs the starting operator.  The finite list is a finite
sequence of operators in `Limit`; it does not bound the dimension of `Limit`.
-/

/-- The residual after successively removing a finite list of operator
increments. -/
def operatorResidual {R : Type*} [Ring R] : List R → R → R
  | [], residual => residual
  | increment :: increments, residual =>
      operatorResidual increments (residual - increment)

/-- Reverse-nested reconstruction of a finite list of increments and a tail. -/
def reverseOperatorAggregate {R : Type*} [Ring R] : List R → R → R
  | [], tail => tail
  | increment :: increments, tail =>
      increment + reverseOperatorAggregate increments tail

/-- A ring homomorphism transports the residual recursion without changing
the order in which increments are removed. -/
theorem map_operatorResidual {R S : Type*} [Ring R] [Ring S]
    (f : R →+* S) (increments : List R) (initial : R) :
    f (operatorResidual increments initial) =
      operatorResidual (increments.map f) (f initial) := by
  induction increments generalizing initial with
  | nil => rfl
  | cons increment increments ih =>
      simp only [operatorResidual, List.map_cons, map_sub, ih]

/-- A ring homomorphism transports the reverse-nested reconstruction while
preserving the order of its operator increments. -/
theorem map_reverseOperatorAggregate {R S : Type*} [Ring R] [Ring S]
    (f : R →+* S) (increments : List R) (tail : R) :
    f (reverseOperatorAggregate increments tail) =
      reverseOperatorAggregate (increments.map f) (f tail) := by
  induction increments generalizing tail with
  | nil => rfl
  | cons increment increments ih =>
      simp only [reverseOperatorAggregate, List.map_cons, map_add, ih]

/-- Removing increments from the residual and restoring them in reverse-nested
order exactly recovers the initial operator. -/
theorem reverseOperatorAggregate_operatorResidual
    {R : Type*} [Ring R] (increments : List R) (initial : R) :
    reverseOperatorAggregate increments (operatorResidual increments initial) =
      initial := by
  induction increments generalizing initial with
  | nil => rfl
  | cons increment increments ih =>
      simp only [operatorResidual, reverseOperatorAggregate, ih]
      abel

/-- The operator residual/reconstruction identity holds in the actual
potentially infinite-dimensional `Cl(1,1)` direct limit. -/
theorem cl11_limit_operator_residual_reconstruction
    (increments : List Limit) (initial : Limit) :
    reverseOperatorAggregate increments
        (operatorResidual increments initial) = initial := by
  induction increments generalizing initial with
  | nil => rfl
  | cons increment increments ih =>
      simp only [operatorResidual, reverseOperatorAggregate]
      rw [ih]
      abel

/-- The same residual reconstruction is compatible with every finite Clifford
head: applying the canonical colimit map before or after the whole finite
calculation gives the same operator. -/
theorem cl11_stage_operator_residual_compatibility
    (n : ℕ) (increments : List (Stage n)) (initial : Stage n) :
    ofStage n
        (reverseOperatorAggregate increments
          (operatorResidual increments initial)) =
      reverseOperatorAggregate (increments.map (ofStage n))
        (operatorResidual (increments.map (ofStage n)) (ofStage n initial)) := by
  induction increments generalizing initial with
  | nil => rfl
  | cons increment increments ih =>
      simp only [operatorResidual, reverseOperatorAggregate, List.map_cons,
        map_add]
      rw [ih]
      simp only [map_sub]

/-- Reconstructing a finite stagewise operator residual remains exact after
passing to the direct limit. -/
theorem cl11_stage_operator_residual_reconstruction
    (n : ℕ) (increments : List (Stage n)) (initial : Stage n) :
    ofStage n
        (reverseOperatorAggregate increments
          (operatorResidual increments initial)) = ofStage n initial := by
  rw [cl11_stage_operator_residual_compatibility]
  exact reverseOperatorAggregate_operatorResidual
    (increments.map (ofStage n)) (ofStage n initial)

/-- Every finite residual/reconstruction calculation on arbitrary operators
of the `Cl(1,1)` direct limit is already calculable at one common finite
tensor head. The selected head contains representatives of every increment
and the initial operator, and the canonical map from that head preserves the
ordered residual and the reverse-nested reconstruction. The tail value is an
operator of the unbounded direct limit; only the calculation has finite
support. -/
theorem cl11_limit_residual_calculation_has_common_head
    (increments : List Limit) (initial : Limit) :
    ∃ n : ℕ, ∃ incrementsₙ : List (Stage n), ∃ initialₙ : Stage n,
      incrementsₙ.map (ofStage n) = increments ∧
      ofStage n initialₙ = initial ∧
      ofStage n (operatorResidual incrementsₙ initialₙ) =
        operatorResidual increments initial ∧
      ofStage n
          (reverseOperatorAggregate incrementsₙ
            (operatorResidual incrementsₙ initialₙ)) =
        reverseOperatorAggregate increments
          (operatorResidual increments initial) := by
  obtain ⟨n, incrementsₙ, hincrements⟩ :=
    exists_common_head_representatives_list increments
  obtain ⟨m, initialₘ, hinitial⟩ :=
    DirectLimit.exists_eq_mk
      (f := fun i j h => bondMap stageBond i j h) initial
  let N := max n m
  let f := bondMap stageBond n N (Nat.le_max_left n m)
  let g := bondMap stageBond m N (Nat.le_max_right n m)
  let incrementsN := incrementsₙ.map f
  let initialN := g initialₘ
  have hf (x : Stage n) : ofStage N (f x) = ofStage n x := by
    exact directLimitOf_bondMap stageBond n N (Nat.le_max_left n m) x
  have hg : ofStage N initialN = initial := by
    calc
      ofStage N initialN = ofStage m initialₘ := by
        exact directLimitOf_bondMap stageBond m N (Nat.le_max_right n m) initialₘ
      _ = initial := by simpa [ofStage] using hinitial.symm
  have hincN : incrementsN.map (ofStage N) = increments := by
    dsimp [incrementsN]
    rw [List.map_map]
    calc
      List.map (fun x => ofStage N (f x)) incrementsₙ =
          List.map (ofStage n) incrementsₙ := by
            apply List.map_congr_left
            intro x hx
            exact hf x
      _ = increments := hincrements
  have hres : ofStage N (operatorResidual incrementsN initialN) =
      operatorResidual increments initial := by
    rw [map_operatorResidual]
    rw [hincN, hg]
  have hagg : ofStage N
      (reverseOperatorAggregate incrementsN
        (operatorResidual incrementsN initialN)) =
      reverseOperatorAggregate increments
        (operatorResidual increments initial) := by
    rw [map_reverseOperatorAggregate, hincN, hres]
  exact ⟨N, incrementsN, initialN, hincN, hg, hres, hagg⟩

end InfoGeometry.Clifford.Cl11RecursiveCommutatorColimit
