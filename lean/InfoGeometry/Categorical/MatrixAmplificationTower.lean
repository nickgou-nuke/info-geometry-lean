/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Algebra.MatrixAmplification
import InfoGeometry.Categorical.SequentialRingColimit
import Mathlib.CategoryTheory.Limits.Filtered
import Mathlib.CategoryTheory.Limits.HasLimits

/-!
# Faithful recursive matrix amplification

For a finite index type `n`, the full matrix endofunctor on `RingCat` has the
natural unital amplification `a ↦ Matrix.scalar n a`. Iterating it gives an
actual ring diagram and algebraic colimit using the repository's existing
direct-limit owner and its native categorical universal property.

A nonempty index makes every stage inclusion injective. With two distinct
indices and a nontrivial seed, the successive images are strictly increasing
subrings, the limit carrier is infinite, and explicit matrix-unit commutators
remain nonzero in the limit. No star, norm or analytic completion is assumed.
-/

noncomputable section

namespace InfoGeometry.Categorical.MatrixAmplificationTower

open CategoryTheory CategoryTheory.Limits
open InfoGeometry.Algebra.DirectLimitSuperClosureLemmas
open InfoGeometry.Algebra.MatrixAmplification

universe u

variable (n : Type u) [Fintype n] [DecidableEq n]

/-- Full matrices and entrywise ring homomorphisms form an endofunctor of
the category of arbitrary associative unital rings. -/
def matrixFunctor : RingCat.{u} ⥤ RingCat.{u} where
  obj A := RingCat.of (Matrix n n A)
  map f := RingCat.ofHom f.hom.mapMatrix
  map_id A := by
    ext M i j
    rfl
  map_comp f g := by
    ext M i j
    rfl

/-- Scalar amplification is natural even for noncommutative coefficients. -/
def amplification : 𝟭 RingCat.{u} ⟶ matrixFunctor n where
  app A := RingCat.ofHom (Matrix.scalar n)
  naturality A B f := by
    apply RingCat.hom_ext
    apply RingHom.ext
    intro a
    change Matrix.scalar n (f.hom a) = f.hom.mapMatrix (Matrix.scalar n a)
    ext i j
    by_cases h : i = j
    · subst j
      simp [Matrix.scalar_apply, RingHom.mapMatrix_apply]
    · simp [Matrix.scalar_apply, RingHom.mapMatrix_apply, h]

/-- Iterated full matrix rings, with the original ring at stage zero. -/
def stage (A : RingCat.{u}) : ℕ → RingCat.{u}
  | 0 => A
  | k + 1 => (matrixFunctor n).obj (stage A k)

/-- The successor homomorphism is the component of the natural amplification. -/
def bond (A : RingCat.{u}) (k : ℕ) : stage n A k →+* stage n A (k + 1) :=
  (amplification n).app (stage n A k) |>.hom

/-- The full matrix tower as a native diagram over the directed poset `ℕ`. -/
abbrev diagram (A : RingCat.{u}) : ℕ ⥤ RingCat.{u} :=
  SequentialRingColimit.diagram (bond n A)

/-- The carrier is the existing native algebraic direct limit, not a new quotient. -/
abbrev Limit (A : RingCat.{u}) : Type u :=
  DirectLimitSuperClosure (bond n A)

/-- The canonical stage ring homomorphism into the algebraic colimit. -/
abbrev inclusion (A : RingCat.{u}) (k : ℕ) : stage n A k →+* Limit n A :=
  directLimitOf (bond n A) k

/-- The concrete cocone satisfies the native categorical universal property. -/
def colimitWitness (A : RingCat.{u}) :
    IsColimit (SequentialRingColimit.cocone (bond n A)) :=
  SequentialRingColimit.isColimit (bond n A)

/-- The categorical colimit exists because the concrete cocone is colimiting. -/
instance (A : RingCat.{u}) : HasColimit (diagram n A) :=
  HasColimit.mk ⟨SequentialRingColimit.cocone (bond n A), colimitWitness n A⟩

/-- Every element of the algebraic colimit has a finite-stage representative. -/
theorem exists_stage (A : RingCat.{u}) (x : Limit n A) :
    ∃ (k : ℕ) (a : stage n A k), inclusion n A k a = x := by
  obtain ⟨k, a, h⟩ := DirectLimit.exists_eq_mk
    (fun i j h => bondMap (bond n A) i j h) x
  exact ⟨k, a, h.symm⟩

/-- Two arbitrary limit elements can be represented at one common finite stage. -/
theorem exists_common_stage (A : RingCat.{u}) (x y : Limit n A) :
    ∃ (k : ℕ) (a b : stage n A k), inclusion n A k a = x ∧ inclusion n A k b = y := by
  obtain ⟨k, a, b, hx, hy⟩ := DirectLimit.exists_eq_mk₂
    (fun i j h => bondMap (bond n A) i j h) x y
  exact ⟨k, a, b, hx.symm, hy.symm⟩

section Faithfulness

variable [Nonempty n] (A : RingCat.{u})

/-- Reading one diagonal entry proves that each bond is injective. -/
theorem bond_injective (k : ℕ) : Function.Injective (bond n A k) := by
  exact fun _ _ h => Matrix.scalar_inj.mp h

/-- Faithfulness holds for all intervals of the directed diagram. -/
theorem transition_injective (i j : ℕ) (h : i ≤ j) :
    Function.Injective (bondMap (bond n A) i j h) :=
  bondMap_injective (bond n A) (bond_injective n A) i j h

/-- Canonical inclusion does not identify distinct elements of a stage. -/
theorem inclusion_injective (k : ℕ) : Function.Injective (inclusion n A k) :=
  directLimitOf_injective (bond n A) (bond_injective n A) k

/-- The inclusion preserves and reflects commutation of arbitrary stage elements. -/
theorem inclusion_commute_iff (k : ℕ) (x y : stage n A k) :
    Commute (inclusion n A k x) (inclusion n A k y) ↔ Commute x y :=
  commute_map_iff (inclusion_injective n A k)

/-- A stage commutator vanishes in the colimit exactly when it already vanishes. -/
theorem inclusion_commutator_eq_zero_iff (k : ℕ) (x y : stage n A k) :
    ⁅inclusion n A k x, inclusion n A k y⁆ = 0 ↔ ⁅x, y⁆ = 0 := by
  have hm : ⁅inclusion n A k x, inclusion n A k y⁆ = inclusion n A k ⁅x, y⁆ := by
    simp only [Ring.lie_def, map_sub, map_mul]
  rw [hm, ← map_zero (inclusion n A k)]
  exact (inclusion_injective n A k).eq_iff

/-- Nontriviality propagates through the full matrix stages. -/
instance stageNontrivial [Nontrivial A] (k : ℕ) : Nontrivial (stage n A k) := by
  induction k with
  | zero => exact inferInstanceAs (Nontrivial A)
  | succ k ih =>
    letI := ih
    change Nontrivial (Matrix n n (stage n A k))
    infer_instance

/-- A nontrivial seed remains nontrivial in the algebraic colimit. -/
instance limitNontrivial [Nontrivial A] : Nontrivial (Limit n A) :=
  (inclusion_injective n A 0).nontrivial

/-- Opposite matrix units remain a concrete noncommuting pair in the colimit. -/
theorem inclusion_single_commutator_ne_zero [Nontrivial A]
    (k : ℕ) {i j : n} (hij : i ≠ j) :
    ⁅inclusion n A (k + 1) (Matrix.single i j (1 : stage n A k)),
      inclusion n A (k + 1) (Matrix.single j i (1 : stage n A k))⁆ ≠ 0 := by
  intro h
  exact single_commutator_ne_zero hij
    ((inclusion_commutator_eq_zero_iff n A (k + 1) _ _).mp h)

end Faithfulness

/-- Each stage image is a native subring of the direct limit. -/
def stageRange (A : RingCat.{u}) (k : ℕ) : Subring (Limit n A) :=
  (inclusion n A k).range

/-- The canonical subrings increase along the actual diagram arrows. -/
theorem stageRange_mono (A : RingCat.{u}) : Monotone (stageRange n A) := by
  intro i j hij x hx
  obtain ⟨a, rfl⟩ := hx
  exact ⟨bondMap (bond n A) i j hij a,
    directLimitOf_bondMap (bond n A) i j hij a⟩

section StrictGrowth

variable [Nontrivial n] (A : RingCat.{u}) [Nontrivial A]

/-- A new off-diagonal matrix unit makes every successive stage image proper. -/
theorem stageRange_lt_succ (k : ℕ) : stageRange n A k < stageRange n A (k + 1) := by
  apply lt_of_le_not_ge (stageRange_mono n A (Nat.le_succ k))
  intro h
  obtain ⟨i, j, hij⟩ := exists_pair_ne n
  have hmem : inclusion n A (k + 1) (Matrix.single i j (1 : stage n A k)) ∈
      stageRange n A (k + 1) := ⟨_, rfl⟩
  obtain ⟨a, ha⟩ := h hmem
  apply single_not_mem_range_scalar (A := stage n A k) hij
  refine ⟨a, ?_⟩
  apply inclusion_injective n A (k + 1)
  exact (directLimitOf_bond (bond n A) k a).trans ha

/-- The tower supplies a strictly increasing chain of subrings of its colimit. -/
theorem stageRange_strictMono : StrictMono (stageRange n A) :=
  strictMono_nat_of_lt_succ (stageRange_lt_succ n A)

/-- Genuine algebraic infinitude follows from strict stage growth, including
when the seed ring itself is finite. This is not a dimension or completion claim. -/
theorem limit_infinite : Infinite (Limit n A) := by
  have hinj : Function.Injective (fun k => (stageRange n A k : Set (Limit n A))) := by
    intro i j h
    exact (stageRange_strictMono n A).injective (SetLike.coe_injective h)
  haveI : Infinite (Set (Limit n A)) := Infinite.of_injective _ hinj
  by_contra h
  haveI : Finite (Limit n A) := not_infinite_iff_finite.mp h
  exact not_finite (Set (Limit n A))

end StrictGrowth

end InfoGeometry.Categorical.MatrixAmplificationTower
