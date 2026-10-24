/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.Ring.Associator
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic

/-!
# Albert-Cayley-Dickson doubling

This module formalizes the generalized doubling pattern attributed to Albert
(1942):

* the doubled carrier is the pair type `A × A`;
* the doubled product uses a scalar parameter `γ` and the involution on `A`;
* the doubled involution is `(p, q) ↦ (p*, -q)`;
* the split case `γ = 1` has canonical zero divisors and null vectors.

The file is intentionally conservative:

* it does not claim a ring instance for the doubled carrier;
* it does not claim a full octonion classification theorem;
* the concrete split-complex / split-quaternion / split-octonion layers are
  handled by their own carriers elsewhere in the repository.
-/

noncomputable section

namespace InfoGeometry.Canonical.AlbertCayleyDickson

/--
Albert's doubled carrier `A ⊕ A` with parameter `γ`.

The underlying algebra `A` is assumed to be a ring with a star involution.
The construction itself is purely algebraic; we do not package a ring
structure on the doubled type here.
-/
@[ext]
structure AlbertStep (F A : Type*) [CommRing F] [Ring A] [Algebra F A]
    [StarRing A] (γ : F) where
  p : A
  q : A

namespace AlbertStep

variable {F A : Type*} [CommRing F] [Ring A] [Algebra F A] [StarRing A]

def zeroElem {γ : F} : AlbertStep F A γ :=
  ⟨0, 0⟩

def oneElem {γ : F} : AlbertStep F A γ :=
  ⟨1, 0⟩

instance {γ : F} : Zero (AlbertStep F A γ) where
  zero := zeroElem (F := F) (A := A) (γ := γ)

instance {γ : F} : One (AlbertStep F A γ) where
  one := oneElem (F := F) (A := A) (γ := γ)

@[simp] theorem zero_p {γ : F} :
    (0 : AlbertStep F A γ).p = 0 := rfl

@[simp] theorem zero_q {γ : F} :
    (0 : AlbertStep F A γ).q = 0 := rfl

@[simp] theorem one_p {γ : F} :
    (1 : AlbertStep F A γ).p = 1 := rfl

@[simp] theorem one_q {γ : F} :
    (1 : AlbertStep F A γ).q = 0 := rfl

/-- The Albert involution `(p, q) ↦ (p*, -q)`. -/
def conj {γ : F} (x : AlbertStep F A γ) : AlbertStep F A γ :=
  ⟨star x.p, -x.q⟩

@[simp] theorem conj_conj {γ : F} (x : AlbertStep F A γ) :
    conj (conj x) = x := by
  ext <;> simp [conj]

/-- The Albert product with parameter `γ`. -/
def mul {γ : F} (x y : AlbertStep F A γ) : AlbertStep F A γ :=
  ⟨x.p * y.p + (γ • (star y.q * x.q)),
   y.q * x.p + x.q * star y.p⟩

/-- The Albert norm readout. -/
def norm {γ : F} (x : AlbertStep F A γ) : A :=
  x.p * star x.p - (γ • (x.q * star x.q))

@[simp] theorem mul_conj_p {γ : F} (x : AlbertStep F A γ) :
    (mul x (conj x)).p = x.p * star x.p - (γ • (star x.q * x.q)) := by
  simp [mul, conj, sub_eq_add_neg]

@[simp] theorem mul_conj_q {γ : F} (x : AlbertStep F A γ) :
    (mul x (conj x)).q = 0 := by
  simp [mul, conj]

@[simp] theorem conj_mul_p {γ : F} (x : AlbertStep F A γ) :
    (mul (conj x) x).p = star x.p * x.p - (γ • (star x.q * x.q)) := by
  simp [mul, conj, sub_eq_add_neg]

@[simp] theorem conj_mul_q {γ : F} (x : AlbertStep F A γ) :
    (mul (conj x) x).q = 0 := by
  simp [mul, conj]

theorem mul_conj_sub_conj_mul_p {γ : F} (x : AlbertStep F A γ) :
    (mul x (conj x)).p - (mul (conj x) x).p =
      x.p * star x.p - star x.p * x.p := by
  rw [mul_conj_p, conj_mul_p]
  abel

theorem mul_eq_zero_iff {γ : F} (x y : AlbertStep F A γ) :
    mul x y = 0 ↔
      x.p * y.p + (γ • (star y.q * x.q)) = 0 ∧
      y.q * x.p + x.q * star y.p = 0 := by
  constructor
  · intro h
    exact ⟨congrArg AlbertStep.p h, congrArg AlbertStep.q h⟩
  · rintro ⟨hp, hq⟩
    ext
    · exact hp
    · exact hq

@[simp] theorem mul_left_embed {γ : F} (s : A) (y : AlbertStep F A γ) :
    mul (γ := γ) ⟨s, 0⟩ y = ⟨s * y.p, y.q * s⟩ := by
  ext <;> simp [mul]

@[simp] theorem mul_right_embed {γ : F} (y : AlbertStep F A γ) (t : A) :
    mul (γ := γ) y ⟨t, 0⟩ = ⟨y.p * t, y.q * star t⟩ := by
  ext <;> simp [mul]

theorem mul_left_embed_eq_iff {γ : F} (s a p q : A) :
    mul (γ := γ) ⟨s, 0⟩ ⟨p, q⟩ = ⟨s * p, q * a⟩ ↔ q * s = q * a := by
  rw [mul_left_embed]
  constructor
  · intro h
    exact congrArg AlbertStep.q h
  · intro hq
    ext
    · rfl
    · exact hq

theorem associator_conj_embed_p {γ : F} (p : A) (y : AlbertStep F A γ) :
    (mul (γ := γ) (mul (γ := γ) ⟨star p, 0⟩ ⟨p, 0⟩) y).p =
      (mul (γ := γ) ⟨star p, 0⟩ (mul (γ := γ) ⟨p, 0⟩ y)).p := by
  simp [mul_left_embed, mul_assoc]

theorem associator_conj_embed_q {γ : F} (p : A) (y : AlbertStep F A γ) :
    (mul (γ := γ) (mul (γ := γ) ⟨star p, 0⟩ ⟨p, 0⟩) y).q -
      (mul (γ := γ) ⟨star p, 0⟩ (mul (γ := γ) ⟨p, 0⟩ y)).q =
      y.q * (star p * p - p * star p) := by
  simp only [mul_left_embed, zero_mul]
  rw [mul_sub, mul_assoc]

theorem bimodule_embed_associator_q {γ : F} (s t : A) (y : AlbertStep F A γ) :
    (mul (γ := γ) (mul (γ := γ) ⟨s, 0⟩ y) ⟨t, 0⟩).q -
      (mul (γ := γ) ⟨s, 0⟩ (mul (γ := γ) y ⟨t, 0⟩)).q =
      y.q * (s * star t - star t * s) := by
  simp only [mul_left_embed, mul_right_embed]
  rw [mul_sub, mul_assoc, mul_assoc]

/-- The canonical split-complex-like element `(1, 1)` in the `γ = 1` step. -/
def splitPlus : AlbertStep F A (1 : F) :=
  ⟨1, 1⟩

/-- The canonical split-complex-like element `(1, -1)` in the `γ = 1` step. -/
def splitMinus : AlbertStep F A (1 : F) :=
  ⟨1, -1⟩

@[simp] theorem splitPlus_sq :
    mul (splitPlus (F := F) (A := A)) (splitPlus (F := F) (A := A))
      = ⟨(2 : A), (2 : A)⟩ := by
  ext <;> simp [splitPlus, mul] <;> norm_num

@[simp] theorem splitMinus_sq :
    mul (splitMinus (F := F) (A := A)) (splitMinus (F := F) (A := A))
      = ⟨(2 : A), -(2 : A)⟩ := by
  ext <;> simp [splitMinus, mul] <;> norm_num

@[simp] theorem splitPlus_mul_splitMinus :
    mul (splitPlus (F := F) (A := A)) (splitMinus (F := F) (A := A)) = 0 := by
  ext <;> simp [splitPlus, splitMinus, mul]

@[simp] theorem splitMinus_mul_splitPlus :
    mul (splitMinus (F := F) (A := A)) (splitPlus (F := F) (A := A)) = 0 := by
  ext <;> simp [splitPlus, splitMinus, mul]

@[simp] theorem splitPlus_norm :
    norm (splitPlus (F := F) (A := A)) = 0 := by
  simp [norm, splitPlus]

@[simp] theorem splitMinus_norm :
    norm (splitMinus (F := F) (A := A)) = 0 := by
  simp [norm, splitMinus]

section ZeroDivisors

variable [Nontrivial A]

theorem splitPlus_ne_zero :
    splitPlus (F := F) (A := A) ≠ 0 := by
  intro h
  have hp : (1 : A) = 0 := by
    have h' := congrArg AlbertStep.p h
    simp [splitPlus] at h'
  exact one_ne_zero hp

theorem splitMinus_ne_zero :
    splitMinus (F := F) (A := A) ≠ 0 := by
  intro h
  have hp : (1 : A) = 0 := by
    have h' := congrArg AlbertStep.p h
    simp [splitMinus] at h'
  exact one_ne_zero hp

/--
The split Albert step has canonical zero divisors.

This is the precise theorem-level content that the split/causal layer needs:
the `γ = 1` doubling admits nonzero null factors.
-/
theorem gamma_one_has_canonical_zero_divisors :
    ∃ x y : AlbertStep F A (1 : F), x ≠ 0 ∧ y ≠ 0 ∧ mul x y = 0 := by
  refine ⟨splitPlus (F := F) (A := A), splitMinus (F := F) (A := A),
    splitPlus_ne_zero (F := F) (A := A),
    splitMinus_ne_zero (F := F) (A := A), ?_⟩
  simp

end ZeroDivisors

end AlbertStep

/--
The split-quaternion carrier used as the base algebra for the next Albert step.

This is the canonical `2 × 2` matrix model of split quaternions.
-/
abbrev SplitQuaternion (F : Type*) [CommRing F] [StarRing F] :=
  Matrix (Fin 2) (Fin 2) F

/--
The split-octonion carrier as the `γ = 1` Albert doubling of split quaternions.

This is only the carrier-level alias.  The multiplication is still the Albert
doubling multiplication from `AlbertStep`.
-/
abbrev SplitOctonion (F : Type*) [CommRing F] [StarRing F] :=
  AlbertStep F (SplitQuaternion F) (1 : F)

namespace SplitQuaternion

variable {F : Type*} [CommRing F] [StarRing F]

/-- Positive diagonal Peirce projector `E_{00}` in `SplitQuaternion F`. -/
def peircePlus : SplitQuaternion F :=
  !![1, 0; 0, 0]

/-- Negative diagonal Peirce projector `E_{11}` in `SplitQuaternion F`. -/
def peirceMinus : SplitQuaternion F :=
  !![0, 0; 0, 1]

@[simp] theorem peircePlus_idem :
    (peircePlus : SplitQuaternion F) * peircePlus = peircePlus := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [peircePlus]

@[simp] theorem peirceMinus_idem :
    (peirceMinus : SplitQuaternion F) * peirceMinus = peirceMinus := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [peirceMinus]

@[simp] theorem peircePlus_add_peirceMinus :
    (peircePlus : SplitQuaternion F) + peirceMinus = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [peircePlus, peirceMinus]

@[simp] theorem peircePlus_mul_peirceMinus :
    (peircePlus : SplitQuaternion F) * peirceMinus = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [peircePlus, peirceMinus]

@[simp] theorem peirceMinus_mul_peircePlus :
    (peirceMinus : SplitQuaternion F) * peircePlus = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [peircePlus, peirceMinus]

@[simp] theorem star_peircePlus :
    star (peircePlus : SplitQuaternion F) = peircePlus := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [peircePlus]

@[simp] theorem star_peirceMinus :
    star (peirceMinus : SplitQuaternion F) = peirceMinus := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [peirceMinus]

theorem left_mul_right_peirce_comm (S χ : SplitQuaternion F) :
    (S * χ) * peircePlus = S * (χ * peircePlus) ∧
    (S * χ) * peirceMinus = S * (χ * peirceMinus) :=
  ⟨mul_assoc S χ peircePlus, mul_assoc S χ peirceMinus⟩

theorem mixed_peirce_gram_corner (χ : SplitQuaternion F) :
    star (χ * peircePlus) * (χ * peirceMinus) =
      peircePlus * (star χ * χ) * peirceMinus := by
  rw [star_mul, star_peircePlus]
  simp only [mul_assoc]

theorem trace_mixed_peirce_gram_zero (χ : SplitQuaternion F) :
    Matrix.trace (star (χ * peircePlus) * (χ * peirceMinus)) = 0 := by
  rw [mixed_peirce_gram_corner,
      Matrix.trace_mul_comm (peircePlus * (star χ * χ)) peirceMinus,
      ← mul_assoc, peirceMinus_mul_peircePlus, zero_mul, Matrix.trace_zero]

theorem diagonal_peirce_gram_decomposition (χ : SplitQuaternion F) :
    peircePlus * (star χ * χ) * peircePlus +
      peirceMinus * (star χ * χ) * peirceMinus =
      star (χ * peircePlus) * (χ * peircePlus) +
      star (χ * peirceMinus) * (χ * peirceMinus) := by
  rw [star_mul, star_mul, star_peircePlus, star_peirceMinus]
  simp only [mul_assoc]

theorem trace_peircePlus_sandwich (X : SplitQuaternion F) :
    Matrix.trace (peircePlus * X * peircePlus) =
      Matrix.trace (peircePlus * X) := by
  rw [Matrix.trace_mul_comm (peircePlus * X) peircePlus,
      ← mul_assoc, peircePlus_idem]

theorem trace_peirceMinus_sandwich (X : SplitQuaternion F) :
    Matrix.trace (peirceMinus * X * peirceMinus) =
      Matrix.trace (peirceMinus * X) := by
  rw [Matrix.trace_mul_comm (peirceMinus * X) peirceMinus,
      ← mul_assoc, peirceMinus_idem]

theorem trace_peirce_gram_decomposition (χ : SplitQuaternion F) :
    Matrix.trace (star χ * χ) =
      Matrix.trace (star (χ * peircePlus) * (χ * peircePlus)) +
      Matrix.trace (star (χ * peirceMinus) * (χ * peirceMinus)) := by
  rw [← Matrix.trace_add, ← diagonal_peirce_gram_decomposition, Matrix.trace_add,
      trace_peircePlus_sandwich, trace_peirceMinus_sandwich,
      ← Matrix.trace_add, ← add_mul, peircePlus_add_peirceMinus, one_mul]

end SplitQuaternion

end InfoGeometry.Canonical.AlbertCayleyDickson
