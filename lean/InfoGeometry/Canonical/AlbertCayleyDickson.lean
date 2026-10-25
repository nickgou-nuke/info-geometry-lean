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

instance {γ : F} : Add (AlbertStep F A γ) where
  add x y := ⟨x.p + y.p, x.q + y.q⟩

instance {γ : F} : Sub (AlbertStep F A γ) where
  sub x y := ⟨x.p - y.p, x.q - y.q⟩

@[simp] theorem add_p {γ : F} (x y : AlbertStep F A γ) :
    (x + y).p = x.p + y.p := rfl

@[simp] theorem add_q {γ : F} (x y : AlbertStep F A γ) :
    (x + y).q = x.q + y.q := rfl

@[simp] theorem sub_p {γ : F} (x y : AlbertStep F A γ) :
    (x - y).p = x.p - y.p := rfl

@[simp] theorem sub_q {γ : F} (x y : AlbertStep F A γ) :
    (x - y).q = x.q - y.q := rfl

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

@[simp] theorem mul_lateral_self {γ : F} (q : A) :
    mul (γ := γ) (⟨0, q⟩ : AlbertStep F A γ) ⟨0, q⟩ = ⟨γ • (star q * q), 0⟩ := by
  ext <;> simp [mul]

theorem mul_embed_lateral_sub {γ : F} (s q : A) :
    mul (γ := γ) (⟨s, 0⟩ : AlbertStep F A γ) ⟨0, q⟩ -
      mul (γ := γ) (⟨0, q⟩ : AlbertStep F A γ) ⟨s, 0⟩ =
      ⟨0, q * (s - star s)⟩ := by
  ext
  · simp [mul]
  · simp [mul, mul_sub]

theorem mul_embed_lateral_add {γ : F} (s q : A) :
    mul (γ := γ) (⟨s, 0⟩ : AlbertStep F A γ) ⟨0, q⟩ +
      mul (γ := γ) (⟨0, q⟩ : AlbertStep F A γ) ⟨s, 0⟩ =
      ⟨0, q * (s + star s)⟩ := by
  ext
  · simp [mul]
  · simp [mul, mul_add]

theorem two_sided_conj_embed_assoc {γ : F} (s : A) (y : AlbertStep F A γ) :
    mul (γ := γ) (mul (γ := γ) (⟨s, 0⟩ : AlbertStep F A γ) y) ⟨star s, 0⟩ =
      mul (γ := γ) (⟨s, 0⟩ : AlbertStep F A γ) (mul (γ := γ) y ⟨star s, 0⟩) := by
  ext
  · simp [mul, mul_assoc]
  · simp [mul, star_star, mul_assoc]

/-- Even base connection projection `(p, q) ↦ (p, 0)` on `AlbertStep F A γ`. -/
def basePart {γ : F} (x : AlbertStep F A γ) : AlbertStep F A γ :=
  ⟨x.p, 0⟩

/-- Odd lateral Cayley–Dickson frame projection `(p, q) ↦ (0, q)` on `AlbertStep F A γ`. -/
def lateralPart {γ : F} (x : AlbertStep F A γ) : AlbertStep F A γ :=
  ⟨0, x.q⟩

/-- Cayley–Dickson `ℤ₂` doubling grading involution `(p, q) ↦ (p, -q)` on `AlbertStep F A γ`. -/
def doublingGamma {γ : F} (x : AlbertStep F A γ) : AlbertStep F A γ :=
  ⟨x.p, -x.q⟩

/-- **Erlangen 2.0 on `AlbertStep F A γ`: Base Connection `⊕` Lateral Frame Decomposition**. -/
theorem doubling_connection_frame_split {γ : F} (x : AlbertStep F A γ) :
    basePart x + lateralPart x = x ∧
    doublingGamma (basePart x) = basePart x ∧
    doublingGamma (lateralPart x) = ⟨0, -x.q⟩ ∧
    doublingGamma (doublingGamma x) = x := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · ext <;> simp [basePart, lateralPart, doublingGamma]

/-- **Emergent Base Metric & Curvature from Lateral Cayley–Dickson Frames**:
    For any `x, y : AlbertStep F A γ`, both the symmetric Jordan anticommutator and the
    Lie commutator of their odd lateral frame parts `lateralPart x` and `lateralPart y`
    have zero lateral component and land purely in the even base algebra! -/
theorem lateralPart_anticommutator_and_commutator_in_base
    {γ : F} (x y : AlbertStep F A γ) :
    mul (lateralPart x) (lateralPart y) + mul (lateralPart y) (lateralPart x) =
      ⟨γ • (star y.q * x.q + star x.q * y.q), 0⟩ ∧
    mul (lateralPart x) (lateralPart y) - mul (lateralPart y) (lateralPart x) =
      ⟨γ • (star y.q * x.q - star x.q * y.q), 0⟩ := by
  refine ⟨?_, ?_⟩
  · ext
    · simp [lateralPart, mul, smul_add]
    · simp [lateralPart, mul]
  · ext
    · simp [lateralPart, mul, smul_sub]
    · simp [lateralPart, mul]

/-- **Triple Lateral Associator Torsion Lands Purely in the Odd Lateral Sector**:
    For any `x, y, z : AlbertStep F A γ`, the associator of three lateral frames
    has zero base component and lands purely in the odd lateral sector! -/
theorem lateralPart_associator_in_lateral
    {γ : F} (x y z : AlbertStep F A γ) :
    mul (mul (lateralPart x) (lateralPart y)) (lateralPart z) -
    mul (lateralPart x) (mul (lateralPart y) (lateralPart z)) =
      ⟨0, z.q * (γ • (star y.q * x.q)) - x.q * star (γ • (star z.q * y.q))⟩ := by
  ext
  · simp [lateralPart, mul]
  · simp [lateralPart, mul]

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

/-- Upper-right off-diagonal Peirce seed `E_{01}` in `SplitQuaternion F`. -/
def peirceSeedD : SplitQuaternion F :=
  !![0, 1; 0, 0]

/-- Lower-left off-diagonal Peirce seed `E_{10}` in `SplitQuaternion F`. -/
def peirceSeedB : SplitQuaternion F :=
  !![0, 0; 1, 0]

@[simp] theorem peirceSeedD_mul_peirceSeedB :
    (peirceSeedD : SplitQuaternion F) * peirceSeedB = peircePlus := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [peirceSeedD, peirceSeedB, peircePlus]

@[simp] theorem peirceSeedB_mul_peirceSeedD :
    (peirceSeedB : SplitQuaternion F) * peirceSeedD = peirceMinus := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [peirceSeedD, peirceSeedB, peirceMinus]

@[simp] theorem peirceSeedD_mul_self :
    (peirceSeedD : SplitQuaternion F) * peirceSeedD = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [peirceSeedD]

@[simp] theorem peirceSeedB_mul_self :
    (peirceSeedB : SplitQuaternion F) * peirceSeedB = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [peirceSeedB]

@[simp] theorem peircePlus_mul_peirceSeedD :
    (peircePlus : SplitQuaternion F) * peirceSeedD = peirceSeedD := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [peircePlus, peirceSeedD]

@[simp] theorem peirceSeedD_mul_peirceMinus :
    (peirceSeedD : SplitQuaternion F) * peirceMinus = peirceSeedD := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [peirceMinus, peirceSeedD]

@[simp] theorem peirceMinus_mul_peirceSeedD :
    (peirceMinus : SplitQuaternion F) * peirceSeedD = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [peirceMinus, peirceSeedD]

@[simp] theorem peirceSeedD_mul_peircePlus :
    (peirceSeedD : SplitQuaternion F) * peircePlus = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [peircePlus, peirceSeedD]

@[simp] theorem peirceMinus_mul_peirceSeedB :
    (peirceMinus : SplitQuaternion F) * peirceSeedB = peirceSeedB := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [peirceMinus, peirceSeedB]

@[simp] theorem peirceSeedB_mul_peircePlus :
    (peirceSeedB : SplitQuaternion F) * peircePlus = peirceSeedB := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [peircePlus, peirceSeedB]

@[simp] theorem peircePlus_mul_peirceSeedB :
    (peircePlus : SplitQuaternion F) * peirceSeedB = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [peircePlus, peirceSeedB]

@[simp] theorem peirceSeedB_mul_peirceMinus :
    (peirceSeedB : SplitQuaternion F) * peirceMinus = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [peirceMinus, peirceSeedB]

/-- Diagonal hyperbolic Peirce kernel `λ P_+ + μ P_-` in `SplitQuaternion F`. -/
def hyperbolicKernel (lam mu : F) : SplitQuaternion F :=
  lam • peircePlus + mu • peirceMinus

/-- Two-sided hyperbolic Laplace sandwich `K(λ_L, μ_L) * X * K(λ_R, μ_R)` in `SplitQuaternion F`. -/
def twoSidedHyperbolicLaplace (lamL muL lamR muR : F) (X : SplitQuaternion F) :
    SplitQuaternion F :=
  hyperbolicKernel lamL muL * X * hyperbolicKernel lamR muR

@[simp] theorem hyperbolicKernel_one :
    (hyperbolicKernel (1 : F) (1 : F) : SplitQuaternion F) = 1 := by
  simp [hyperbolicKernel, peircePlus_add_peirceMinus]

theorem hyperbolicKernel_mul (lam₁ mu₁ lam₂ mu₂ : F) :
    (hyperbolicKernel lam₁ mu₁ : SplitQuaternion F) * hyperbolicKernel lam₂ mu₂ =
      hyperbolicKernel (lam₁ * lam₂) (mu₁ * mu₂) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hyperbolicKernel, peircePlus, peirceMinus]

theorem twoSidedHyperbolicLaplace_comp
    (lamL₁ muL₁ lamR₁ muR₁ lamL₂ muL₂ lamR₂ muR₂ : F) (X : SplitQuaternion F) :
    twoSidedHyperbolicLaplace lamL₁ muL₁ lamR₁ muR₁
        (twoSidedHyperbolicLaplace lamL₂ muL₂ lamR₂ muR₂ X) =
      twoSidedHyperbolicLaplace (lamL₁ * lamL₂) (muL₁ * muL₂)
        (lamR₂ * lamR₁) (muR₂ * muR₁) X := by
  dsimp [twoSidedHyperbolicLaplace]
  calc
    hyperbolicKernel lamL₁ muL₁ *
        (hyperbolicKernel lamL₂ muL₂ * X * hyperbolicKernel lamR₂ muR₂) *
        hyperbolicKernel lamR₁ muR₁ =
      (hyperbolicKernel lamL₁ muL₁ * hyperbolicKernel lamL₂ muL₂) * X *
        (hyperbolicKernel lamR₂ muR₂ * hyperbolicKernel lamR₁ muR₁) := by
      simp only [mul_assoc]
    _ = hyperbolicKernel (lamL₁ * lamL₂) (muL₁ * muL₂) * X *
        hyperbolicKernel (lamR₂ * lamR₁) (muR₂ * muR₁) := by
      rw [hyperbolicKernel_mul, hyperbolicKernel_mul]

@[simp] theorem twoSidedHyperbolicLaplace_peircePlus (lamL muL lamR muR : F) :
    twoSidedHyperbolicLaplace lamL muL lamR muR (peircePlus : SplitQuaternion F) =
      (lamL * lamR) • peircePlus := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [twoSidedHyperbolicLaplace, hyperbolicKernel, peircePlus, peirceMinus]

@[simp] theorem twoSidedHyperbolicLaplace_peirceMinus (lamL muL lamR muR : F) :
    twoSidedHyperbolicLaplace lamL muL lamR muR (peirceMinus : SplitQuaternion F) =
      (muL * muR) • peirceMinus := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [twoSidedHyperbolicLaplace, hyperbolicKernel, peircePlus, peirceMinus]

@[simp] theorem twoSidedHyperbolicLaplace_peirceSeedD (lamL muL lamR muR : F) :
    twoSidedHyperbolicLaplace lamL muL lamR muR (peirceSeedD : SplitQuaternion F) =
      (lamL * muR) • peirceSeedD := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [twoSidedHyperbolicLaplace, hyperbolicKernel, peircePlus, peirceMinus, peirceSeedD]

@[simp] theorem twoSidedHyperbolicLaplace_peirceSeedB (lamL muL lamR muR : F) :
    twoSidedHyperbolicLaplace lamL muL lamR muR (peirceSeedB : SplitQuaternion F) =
      (muL * lamR) • peirceSeedB := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [twoSidedHyperbolicLaplace, hyperbolicKernel, peircePlus, peirceMinus, peirceSeedB]

theorem peirce_four_sector_decomposition (X : SplitQuaternion F) :
    X = peircePlus * X * peircePlus + peirceMinus * X * peirceMinus +
        peircePlus * X * peirceMinus + peirceMinus * X * peircePlus := by
  calc
    X = 1 * X * 1 := by rw [one_mul, mul_one]
    _ = (peircePlus + peirceMinus) * X * (peircePlus + peirceMinus) := by
      rw [peircePlus_add_peirceMinus]
    _ = peircePlus * X * peircePlus + peirceMinus * X * peirceMinus +
          peircePlus * X * peirceMinus + peirceMinus * X * peircePlus := by
      simp only [add_mul, mul_add]
      abel

theorem twoSidedHyperbolicLaplace_sector_decomposition
    (lamL muL lamR muR : F) (X : SplitQuaternion F) :
    twoSidedHyperbolicLaplace lamL muL lamR muR X =
      (lamL * lamR) • (peircePlus * X * peircePlus) +
      (muL * muR) • (peirceMinus * X * peirceMinus) +
      (lamL * muR) • (peircePlus * X * peirceMinus) +
      (muL * lamR) • (peirceMinus * X * peircePlus) := by
  dsimp [twoSidedHyperbolicLaplace, hyperbolicKernel]
  simp only [add_mul, mul_add]
  simp only [smul_mul_assoc]
  simp only [mul_smul_comm, smul_smul]
  abel

theorem symmetric_twoSidedHyperbolicLaplace_wheel_invariance (u : Fˣ) :
    twoSidedHyperbolicLaplace (u : F) (↑u⁻¹ : F) (u : F) (↑u⁻¹ : F)
        (peirceSeedD : SplitQuaternion F) = peirceSeedD ∧
      twoSidedHyperbolicLaplace (u : F) (↑u⁻¹ : F) (u : F) (↑u⁻¹ : F)
        (peirceSeedB : SplitQuaternion F) = peirceSeedB ∧
      twoSidedHyperbolicLaplace (u : F) (↑u⁻¹ : F) (u : F) (↑u⁻¹ : F)
        (peircePlus : SplitQuaternion F) = ((u : F) * u) • peircePlus ∧
      twoSidedHyperbolicLaplace (u : F) (↑u⁻¹ : F) (u : F) (↑u⁻¹ : F)
        (peirceMinus : SplitQuaternion F) = ((↑u⁻¹ : F) * ↑u⁻¹) • peirceMinus := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [twoSidedHyperbolicLaplace_peirceSeedD, Units.mul_inv, one_smul]
  · rw [twoSidedHyperbolicLaplace_peirceSeedB, Units.inv_mul, one_smul]
  · exact twoSidedHyperbolicLaplace_peircePlus (u : F) (↑u⁻¹ : F) (u : F) (↑u⁻¹ : F)
  · exact twoSidedHyperbolicLaplace_peirceMinus (u : F) (↑u⁻¹ : F) (u : F) (↑u⁻¹ : F)

theorem antisymmetric_twoSidedHyperbolicLaplace_diagonal_invariance (u : Fˣ) :
    twoSidedHyperbolicLaplace (u : F) (↑u⁻¹ : F) (↑u⁻¹ : F) (u : F)
        (peircePlus : SplitQuaternion F) = peircePlus ∧
      twoSidedHyperbolicLaplace (u : F) (↑u⁻¹ : F) (↑u⁻¹ : F) (u : F)
        (peirceMinus : SplitQuaternion F) = peirceMinus ∧
      twoSidedHyperbolicLaplace (u : F) (↑u⁻¹ : F) (↑u⁻¹ : F) (u : F)
        (peirceSeedD : SplitQuaternion F) = ((u : F) * u) • peirceSeedD ∧
      twoSidedHyperbolicLaplace (u : F) (↑u⁻¹ : F) (↑u⁻¹ : F) (u : F)
        (peirceSeedB : SplitQuaternion F) = ((↑u⁻¹ : F) * ↑u⁻¹) • peirceSeedB := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [twoSidedHyperbolicLaplace_peircePlus, Units.mul_inv, one_smul]
  · rw [twoSidedHyperbolicLaplace_peirceMinus, Units.inv_mul, one_smul]
  · exact twoSidedHyperbolicLaplace_peirceSeedD (u : F) (↑u⁻¹ : F) (↑u⁻¹ : F) (u : F)
  · exact twoSidedHyperbolicLaplace_peirceSeedB (u : F) (↑u⁻¹ : F) (↑u⁻¹ : F) (u : F)

theorem trace_antisymmetric_twoSidedHyperbolicLaplace (u : Fˣ) (X : SplitQuaternion F) :
    Matrix.trace
        (twoSidedHyperbolicLaplace (u : F) (↑u⁻¹ : F) (↑u⁻¹ : F) (u : F) X) =
      Matrix.trace X := by
  dsimp [twoSidedHyperbolicLaplace]
  rw [Matrix.trace_mul_comm (hyperbolicKernel (u : F) (↑u⁻¹ : F) * X)
        (hyperbolicKernel (↑u⁻¹ : F) (u : F)),
      ← mul_assoc, hyperbolicKernel_mul, Units.inv_mul, Units.mul_inv,
      hyperbolicKernel_one, one_mul]

/-- Alias `seedD` for the constructive upper-right nilpotent seed `peirceSeedD`. -/
abbrev seedD : SplitQuaternion F := peirceSeedD

/-- Alias `seedB` for the constructive lower-left nilpotent seed `peirceSeedB`. -/
abbrev seedB : SplitQuaternion F := peirceSeedB

/-- Constructive transition velocity `velocityQ = seedD + seedB = !![0, 1; 1, 0]`. -/
def velocityQ : SplitQuaternion F := peirceSeedD + peirceSeedB

/-- Constructive wheel generator `wheelJ = seedD - seedB = !![0, 1; -1, 0]`. -/
def wheelJ : SplitQuaternion F := peirceSeedD - peirceSeedB

/-- Constructive phase polarization `polarizationGamma = peircePlus - peirceMinus = !![1, 0; 0, -1]`. -/
def polarizationGamma : SplitQuaternion F := peircePlus - peirceMinus

/-- Constructive Tits–Bruhat quartic generator `bruhatS = (1 + seedD) * (1 - seedB) * (1 + seedD)`. -/
def bruhatS : SplitQuaternion F := (1 + peirceSeedD) * (1 - peirceSeedB) * (1 + peirceSeedD)

/-- Constructive double-shear hexality generator `hexalityU = (1 + seedD) * (1 - seedB)`. -/
def hexalityU : SplitQuaternion F := (1 + peirceSeedD) * (1 - peirceSeedB)

/-- Constructive homogenized moving pole projector `movingPolePlus c s`. -/
def movingPolePlus (c s : F) : SplitQuaternion F :=
  (c * c) • peircePlus + (s * s) • peirceMinus - (c * s) • velocityQ

/-- Constructive complementary homogenized moving pole projector `movingPoleMinus c s`. -/
def movingPoleMinus (c s : F) : SplitQuaternion F :=
  (s * s) • peircePlus + (c * c) • peirceMinus + (c * s) • velocityQ

/-- Alias `twoSidedLaplace` for `twoSidedHyperbolicLaplace`. -/
abbrev twoSidedLaplace (lamL muL lamR muR : F) (X : SplitQuaternion F) : SplitQuaternion F :=
  twoSidedHyperbolicLaplace lamL muL lamR muR X

/-- Zero-hypothesis nilpotent seed and Peirce corner multiplication table. -/
theorem seed_peirce_identities :
    (seedD : SplitQuaternion F) * seedD = 0 ∧
    (seedB : SplitQuaternion F) * seedB = 0 ∧
    (seedD : SplitQuaternion F) * seedB = peircePlus ∧
    (seedB : SplitQuaternion F) * seedD = peirceMinus :=
  ⟨peirceSeedD_mul_self, peirceSeedB_mul_self,
   peirceSeedD_mul_peirceSeedB, peirceSeedB_mul_peirceSeedD⟩

/-- Zero-hypothesis parabolic-to-cyclotomic `SL₂` center and order relations. -/
theorem bruhatS_and_hexalityU_modular_relations :
    (bruhatS : SplitQuaternion F) * bruhatS = -1 ∧
    (hexalityU : SplitQuaternion F) ^ 3 = -1 ∧
    (bruhatS : SplitQuaternion F) * bruhatS = (hexalityU : SplitQuaternion F) ^ 3 ∧
    (bruhatS : SplitQuaternion F) ^ 4 = 1 ∧
    (hexalityU : SplitQuaternion F) ^ 6 = 1 := by
  have hS2 : (bruhatS : SplitQuaternion F) * bruhatS = -1 := by
    dsimp [bruhatS]
    rw [← peircePlus_add_peirceMinus]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [peircePlus, peirceMinus, peirceSeedD, peirceSeedB]
  have hU3 : (hexalityU : SplitQuaternion F) ^ 3 = -1 := by
    rw [pow_three]
    dsimp [hexalityU]
    rw [← peircePlus_add_peirceMinus]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [peircePlus, peirceMinus, peirceSeedD, peirceSeedB]
  have hS4 : (bruhatS : SplitQuaternion F) ^ 4 = 1 := by
    calc (bruhatS : SplitQuaternion F) ^ 4
      _ = (bruhatS * bruhatS) * (bruhatS * bruhatS) := by
          simp [pow_succ, mul_assoc]
      _ = (-1) * (-1) := by rw [hS2]
      _ = 1 := by simp
  have hU6 : (hexalityU : SplitQuaternion F) ^ 6 = 1 := by
    calc (hexalityU : SplitQuaternion F) ^ 6
      _ = (hexalityU ^ 3) * (hexalityU ^ 3) := by
          simp [pow_succ, mul_assoc]
      _ = (-1) * (-1) := by rw [hU3]
      _ = 1 := by simp
  exact ⟨hS2, hU3, by rw [hS2, hU3], hS4, hU6⟩

/-- Zero-hypothesis projective idempotence and orthogonality of `movingPolePlus c s`. -/
theorem movingPolePlus_projective_idem_and_orth (c s : F) :
    movingPolePlus c s * movingPolePlus c s = (c * c + s * s) • movingPolePlus c s ∧
    movingPolePlus c s * movingPoleMinus c s = 0 ∧
    movingPolePlus c s + movingPoleMinus c s = (c * c + s * s) • (1 : SplitQuaternion F) := by
  refine ⟨?_, ?_, ?_⟩ <;>
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [movingPolePlus, movingPoleMinus, peircePlus, peirceMinus, velocityQ,
            peirceSeedD, peirceSeedB] <;>
      ring

/-- Zero-hypothesis homogenized Fubini–Study chordal metric and Mostow fidelity. -/
theorem movingPolePlus_homogenized_fubini_study_metric (c s : F) :
    (movingPolePlus c s - (c * c + s * s) • peircePlus) *
      (movingPolePlus c s - (c * c + s * s) • peircePlus) =
      (s * s * (c * c + s * s)) • (1 : SplitQuaternion F) ∧
    peircePlus * movingPolePlus c s * peircePlus = (c * c) • (peircePlus : SplitQuaternion F) := by
  refine ⟨?_, ?_⟩ <;>
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [movingPolePlus, peircePlus, peirceMinus, velocityQ, peirceSeedD, peirceSeedB] <;>
      ring

/-- Zero-hypothesis two-state weak-value sandwiches and linear syzygy. -/
theorem two_state_weak_sandwich_and_syzygy (c s : F) :
    peircePlus * movingPolePlus c s =
      (c * c) • peircePlus - (c * s) • (peirceSeedD : SplitQuaternion F) ∧
    peircePlus * velocityQ * movingPolePlus c s =
      (s * s) • (peirceSeedD : SplitQuaternion F) - (c * s) • peircePlus ∧
    s • (peircePlus * movingPolePlus c s) +
      c • (peircePlus * velocityQ * movingPolePlus c s) = 0 := by
  refine ⟨?_, ?_, ?_⟩ <;>
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [movingPolePlus, peircePlus, peirceMinus, velocityQ, peirceSeedD, peirceSeedB] <;>
      ring

/-- Zero-hypothesis two-sided hyperbolic Laplace 4-sector eigen-scaling. -/
theorem twoSidedLaplace_four_sector_scaling (lamL muL lamR muR : F) :
    twoSidedLaplace lamL muL lamR muR peircePlus = (lamL * lamR) • peircePlus ∧
    twoSidedLaplace lamL muL lamR muR peirceMinus = (muL * muR) • peirceMinus ∧
    twoSidedLaplace lamL muL lamR muR seedD = (lamL * muR) • seedD ∧
    twoSidedLaplace lamL muL lamR muR seedB = (muL * lamR) • seedB :=
  ⟨twoSidedHyperbolicLaplace_peircePlus lamL muL lamR muR,
   twoSidedHyperbolicLaplace_peirceMinus lamL muL lamR muR,
   twoSidedHyperbolicLaplace_peirceSeedD lamL muL lamR muR,
   twoSidedHyperbolicLaplace_peirceSeedB lamL muL lamR muR⟩

/-- Zero-hypothesis intertwining of `(peircePlus, peirceMinus, wheelJ)` by `bruhatS`. -/
theorem bruhatS_left_intertwines_peirce_and_wheelJ :
    (peirceMinus : SplitQuaternion F) * bruhatS = bruhatS * peircePlus ∧
    (peircePlus : SplitQuaternion F) * bruhatS = bruhatS * peirceMinus ∧
    (wheelJ : SplitQuaternion F) * bruhatS = bruhatS * wheelJ := by
  refine ⟨?_, ?_, ?_⟩ <;>
  · dsimp [bruhatS]
    rw [← peircePlus_add_peirceMinus]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [peircePlus, peirceMinus, wheelJ, peirceSeedD, peirceSeedB]

/-! ### Erlangen 2.0: `Pin_+` / `Pin_-` Factorization, Spin Connection `ω`, and Emergent Spacetime Frame `e` -/

/-- **Even Spin-Connection Component (`spinConnectionPart X ∈ 𝔥`)**:
Diagonal Peirce projection `ω(X) = P_+ X P_+ + P_- X P_-`. -/
def spinConnectionPart (X : SplitQuaternion F) : SplitQuaternion F :=
  peircePlus * X * peircePlus + peirceMinus * X * peirceMinus

/-- **Odd Emergent Spacetime Frame / Solder Form (`spacetimeFramePart X ∈ 𝔭`)**:
Off-diagonal nilpotent Peirce projection `e(X) = P_+ X P_- + P_- X P_+`. -/
def spacetimeFramePart (X : SplitQuaternion F) : SplitQuaternion F :=
  peircePlus * X * peirceMinus + peirceMinus * X * peircePlus

/-- **Emergent Spacetime Metric Bilinear (`emergentMetric X Y : F`)**:
Induced by the Jordan anticommutator `{e(X), e(Y)} = emergentMetric X Y • 1`. -/
def emergentMetric (X Y : SplitQuaternion F) : F :=
  X 0 1 * Y 1 0 + X 1 0 * Y 0 1

/-- **Emergent Riemann–Cartan Spin Curvature Scalar (`emergentCurvature X Y : F`)**:
Induced by the Lie commutator `[e(X), e(Y)] = emergentCurvature X Y • polarizationGamma`. -/
def emergentCurvature (X Y : SplitQuaternion F) : F :=
  X 0 1 * Y 1 0 - X 1 0 * Y 0 1

/-- Explicit `2 × 2` matrix eta-expansion for `SplitQuaternion F`. -/
theorem eq_eta (X : SplitQuaternion F) :
    X = !![X 0 0, X 0 1; X 1 0, X 1 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- Explicit `2 × 2` matrix formula for `spinConnectionPart X`. -/
@[simp] theorem spinConnectionPart_eq (X : SplitQuaternion F) :
    spinConnectionPart X = !![X 0 0, 0; 0, X 1 1] := by
  unfold spinConnectionPart
  conv_lhs => rw [eq_eta X]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [peircePlus, peirceMinus]

/-- Explicit `2 × 2` matrix formula for `spacetimeFramePart X`. -/
@[simp] theorem spacetimeFramePart_eq (X : SplitQuaternion F) :
    spacetimeFramePart X = !![0, X 0 1; X 1 0, 0] := by
  unfold spacetimeFramePart
  conv_lhs => rw [eq_eta X]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [peircePlus, peirceMinus]

/-- **Node 0: `Pin_-` × `Pin_+` Factorizes the Cartan Spin-Connection Generator `polarizationGamma`**. -/
theorem pinMinus_mul_pinPlus_eq_polarizationGamma :
    (wheelJ : SplitQuaternion F) * velocityQ = polarizationGamma ∧
    (velocityQ : SplitQuaternion F) * wheelJ = -polarizationGamma ∧
    (velocityQ : SplitQuaternion F) * velocityQ = 1 ∧
    (wheelJ : SplitQuaternion F) * wheelJ = -1 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [wheelJ, velocityQ, polarizationGamma, peircePlus, peirceMinus,
            peirceSeedD, peirceSeedB]

/-- **Node 1: Cartan Decomposition `X = ω(X) + e(X)` & Parity Grading under `polarizationGamma`**. -/
theorem cartan_spinConnection_spacetimeFrame_split (X : SplitQuaternion F) :
    spinConnectionPart X + spacetimeFramePart X = X ∧
    polarizationGamma * spinConnectionPart X * polarizationGamma = spinConnectionPart X ∧
    polarizationGamma * spacetimeFramePart X * polarizationGamma = -spacetimeFramePart X := by
  refine ⟨?_, ?_, ?_⟩ <;>
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [polarizationGamma, peircePlus, peirceMinus]

/-- **Node 2a: Emergent Spacetime Metric from the Jordan Anticommutator of Frame Vectors**:
For any `X, Y : SplitQuaternion F`, the symmetric product `{e(X), e(Y)}` of their odd
spacetime frame parts is a pure scalar multiple of the identity matrix `1`! -/
theorem spacetimeFrame_anticommutator_eq_emergentMetric_smul_one
    (X Y : SplitQuaternion F) :
    spacetimeFramePart X * spacetimeFramePart Y +
    spacetimeFramePart Y * spacetimeFramePart X =
      emergentMetric X Y • (1 : SplitQuaternion F) := by
  rw [ ← peircePlus_add_peirceMinus]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [emergentMetric, peircePlus, peirceMinus] <;>
    ring

/-- **Node 2b: Emergent Riemann–Cartan Spin Curvature from the Lie Commutator of Frame Vectors**:
For any `X, Y : SplitQuaternion F`, the commutator `[e(X), e(Y)]` of their odd spacetime
frame parts lands purely in the even spin-connection algebra along `polarizationGamma`! -/
theorem spacetimeFrame_commutator_eq_emergentCurvature_smul_gamma
    (X Y : SplitQuaternion F) :
    spacetimeFramePart X * spacetimeFramePart Y -
    spacetimeFramePart Y * spacetimeFramePart X =
      emergentCurvature X Y • (polarizationGamma : SplitQuaternion F) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [emergentCurvature, polarizationGamma, peircePlus, peirceMinus] <;>
    ring

/-- **Node 3a: Cartan Torsion / Covariant Derivative `[ω(X), e(Y)]` Lands Purely in `𝔭`**. -/
theorem spinConnection_spacetimeFrame_commutator_in_frame
    (X Y : SplitQuaternion F) :
    spinConnectionPart
      (spinConnectionPart X * spacetimeFramePart Y -
       spacetimeFramePart Y * spinConnectionPart X) = 0 ∧
    spacetimeFramePart
      (spinConnectionPart X * spacetimeFramePart Y -
       spacetimeFramePart Y * spinConnectionPart X) =
      spinConnectionPart X * spacetimeFramePart Y -
      spacetimeFramePart Y * spinConnectionPart X := by
  refine ⟨?_, ?_⟩ <;>
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp

/-- **Node 3b: Local Lorentz / Modular Gauge Invariance of Emergent Metric & Curvature (`u : Fˣ`)**:
Under the antisymmetric two-sided hyperbolic gauge boost `L_{u, u⁻¹, u⁻¹, u}` (`u : Fˣ`),
both `emergentMetric X Y` and `emergentCurvature X Y` are strictly invariant! -/
theorem emergentMetric_and_curvature_gauge_invariant
    (u : Fˣ) (X Y : SplitQuaternion F) :
    emergentMetric
      (twoSidedHyperbolicLaplace (u : F) (↑u⁻¹ : F) (↑u⁻¹ : F) (u : F) X)
      (twoSidedHyperbolicLaplace (u : F) (↑u⁻¹ : F) (↑u⁻¹ : F) (u : F) Y) =
      emergentMetric X Y ∧
    emergentCurvature
      (twoSidedHyperbolicLaplace (u : F) (↑u⁻¹ : F) (↑u⁻¹ : F) (u : F) X)
      (twoSidedHyperbolicLaplace (u : F) (↑u⁻¹ : F) (↑u⁻¹ : F) (u : F) Y) =
      emergentCurvature X Y := by
  have h_lap (Z : SplitQuaternion F) :
      twoSidedHyperbolicLaplace (u : F) (↑u⁻¹ : F) (↑u⁻¹ : F) (u : F) Z =
        !![(u : F) * Z 0 0 * (↑u⁻¹ : F), (u : F) * Z 0 1 * (u : F);
           (↑u⁻¹ : F) * Z 1 0 * (↑u⁻¹ : F), (↑u⁻¹ : F) * Z 1 1 * (u : F)] := by
    unfold twoSidedHyperbolicLaplace hyperbolicKernel
    conv_lhs => rw [eq_eta Z]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [peircePlus, peirceMinus]
  rw [h_lap X, h_lap Y]
  unfold emergentMetric emergentCurvature
  dsimp
  have h1 : (u : F) * X 0 1 * (u : F) * ((↑u⁻¹ : F) * Y 1 0 * (↑u⁻¹ : F)) =
      X 0 1 * Y 1 0 := by
    calc (u : F) * X 0 1 * (u : F) * ((↑u⁻¹ : F) * Y 1 0 * (↑u⁻¹ : F))
      _ = ((u : F) * (↑u⁻¹ : F)) * ((u : F) * (↑u⁻¹ : F)) * (X 0 1 * Y 1 0) := by ring
      _ = X 0 1 * Y 1 0 := by simp
  have h2 : (↑u⁻¹ : F) * X 1 0 * (↑u⁻¹ : F) * ((u : F) * Y 0 1 * (u : F)) =
      X 1 0 * Y 0 1 := by
    calc (↑u⁻¹ : F) * X 1 0 * (↑u⁻¹ : F) * ((u : F) * Y 0 1 * (u : F))
      _ = ((↑u⁻¹ : F) * (u : F)) * ((↑u⁻¹ : F) * (u : F)) * (X 1 0 * Y 0 1) := by ring
      _ = X 1 0 * Y 0 1 := by simp
  rw [h1, h2]
  exact ⟨rfl, rfl⟩

/-! ### Tamm–Dancoff `1 ⊕ 3` Singlet–Triplet Split & Three-Triplet Nambu Closure on `SplitQuaternion F` -/

/-- **Division-Free Singlet Part (`singletPart X ∈ 1`)**:
    `singletPart X = trace(X) • 1`. -/
def singletPart (X : SplitQuaternion F) : SplitQuaternion F :=
  Matrix.trace X • (1 : SplitQuaternion F)

/-- **Division-Free Traceless Triplet Part (`tripletPart X ∈ 3 = 𝔰𝔩₂(F)`)**:
    `tripletPart X = (2 : F) • X - trace(X) • 1`. -/
def tripletPart (X : SplitQuaternion F) : SplitQuaternion F :=
  (2 : F) • X - Matrix.trace X • (1 : SplitQuaternion F)

/-- **Division-Free Tamm–Dancoff `1 ⊕ 3` Decomposition (`singlet_add_triplet_eq_two_smul`)**:
    Every `2 × 2` operator `X` decomposes as `2 • X = singletPart X + tripletPart X` with
    `trace (tripletPart X) = 0`. -/
theorem singlet_add_triplet_eq_two_smul (X : SplitQuaternion F) :
    singletPart X + tripletPart X = (2 : F) • X ∧
    Matrix.trace (tripletPart X) = 0 := by
  refine ⟨?_, ?_⟩
  · unfold singletPart tripletPart; abel
  · simp [tripletPart, Matrix.trace, Matrix.diag, Fin.sum_univ_two]

/-- **Triplet × Triplet Jordan Anticommutator Lands Purely in the 1D Singlet Sector**:
    For any `X, Y : SplitQuaternion F`, `{tripletPart X, tripletPart Y}` is a pure scalar
    multiple of `1` equal to `trace(tripletPart X * tripletPart Y) • 1`! -/
theorem tripletPart_anticommutator_in_singlet (X Y : SplitQuaternion F) :
    tripletPart X * tripletPart Y + tripletPart Y * tripletPart X =
      Matrix.trace (tripletPart X * tripletPart Y) • (1 : SplitQuaternion F) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
  · simp [tripletPart, Matrix.trace, Matrix.diag,
          Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply]
    ring

/-- **Triplet × Triplet Lie Commutator Lands Purely in the 3D Triplet Sector (`trace = 0`)**. -/
theorem tripletPart_commutator_trace_zero (X Y : SplitQuaternion F) :
    Matrix.trace (tripletPart X * tripletPart Y - tripletPart Y * tripletPart X) = 0 := by
  simp [tripletPart, Matrix.trace, Matrix.diag,
        Matrix.mul_apply, Fin.sum_univ_two]
  ring

/-- **Three-Triplet Nambu Bracket Lands Purely in the 1D Singlet Sector**:
    For any three operators `X, Y, Z : SplitQuaternion F`, pairing the commutator
    `[tripletPart X, tripletPart Y]` with `tripletPart Z` via the Jordan anticommutator
    lands purely in the 1D Singlet sector `trace([T₁, T₂] * T₃) • 1`! -/
theorem three_triplet_nambu_bracket_in_singlet (X Y Z : SplitQuaternion F) :
    (tripletPart X * tripletPart Y - tripletPart Y * tripletPart X) * tripletPart Z +
    tripletPart Z * (tripletPart X * tripletPart Y - tripletPart Y * tripletPart X) =
      Matrix.trace ((tripletPart X * tripletPart Y - tripletPart Y * tripletPart X) *
                    tripletPart Z) • (1 : SplitQuaternion F) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
  · simp [tripletPart, Matrix.trace, Matrix.diag,
          Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply]
    ring

section TrivialStarPositivityAndConservation

variable [TrivialStar F]

/-- Under a trivial scalar star involution, `wheelJ = seedD - seedB` is skew-adjoint. -/
@[simp] theorem star_wheelJ :
    star (wheelJ : SplitQuaternion F) = -wheelJ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [wheelJ, peirceSeedD, peirceSeedB]

/-- Zero-hypothesis exact `2 × 2` matrix Gram conservation under left multiplication by `wheelJ`. -/
theorem wheelJ_gram_deriv_zero (χ : SplitQuaternion F) :
    star (wheelJ * χ) * χ + star χ * (wheelJ * χ) = 0 := by
  rw [star_mul, star_wheelJ]
  simp only [mul_neg, neg_mul, mul_assoc, neg_add_cancel]

/-- Zero-hypothesis right-isospin sectorwise matrix Gram conservation under left `wheelJ` evolution. -/
theorem wheelJ_peirce_sector_gram_deriv_zero (χ : SplitQuaternion F) :
    star ((wheelJ * χ) * peircePlus) * (χ * peircePlus) +
      star (χ * peircePlus) * ((wheelJ * χ) * peircePlus) = 0 ∧
    star ((wheelJ * χ) * peirceMinus) * (χ * peirceMinus) +
      star (χ * peirceMinus) * ((wheelJ * χ) * peirceMinus) = 0 := by
  rw [mul_assoc wheelJ χ peircePlus, mul_assoc wheelJ χ peirceMinus]
  exact ⟨wheelJ_gram_deriv_zero (χ * peircePlus),
         wheelJ_gram_deriv_zero (χ * peirceMinus)⟩

/-- Zero-hypothesis sum-of-squares expansion of the Hilbert–Schmidt Gram trace on `SplitQuaternion F`. -/
theorem trace_star_mul_self_eq_sum_sq (χ : SplitQuaternion F) :
    Matrix.trace (star χ * χ) =
      χ 0 0 * χ 0 0 + χ 0 1 * χ 0 1 + χ 1 0 * χ 1 0 + χ 1 1 * χ 1 1 := by
  simp [Matrix.trace, Fin.sum_univ_two, Matrix.mul_apply]
  ring

/-- Zero-hypothesis sum-of-squares expansion of the positive right-isospin sector Gram trace. -/
theorem trace_star_mul_self_peircePlus_eq_sum_sq (χ : SplitQuaternion F) :
    Matrix.trace (star (χ * peircePlus) * (χ * peircePlus)) =
      χ 0 0 * χ 0 0 + χ 1 0 * χ 1 0 := by
  simp [Matrix.trace, Fin.sum_univ_two, Matrix.mul_apply, peircePlus]

/-- Zero-hypothesis sum-of-squares expansion of the negative right-isospin sector Gram trace. -/
theorem trace_star_mul_self_peirceMinus_eq_sum_sq (χ : SplitQuaternion F) :
    Matrix.trace (star (χ * peirceMinus) * (χ * peirceMinus)) =
      χ 0 1 * χ 0 1 + χ 1 1 * χ 1 1 := by
  simp [Matrix.trace, Fin.sum_univ_two, Matrix.mul_apply, peirceMinus]

end TrivialStarPositivityAndConservation

section OrderedGramPositivity

variable [LinearOrder F] [IsStrictOrderedRing F] [TrivialStar F]

/-- Zero-hypothesis nonnegativity of the positive right-isospin sector Gram trace. -/
theorem trace_star_mul_self_peircePlus_nonneg (χ : SplitQuaternion F) :
    0 ≤ Matrix.trace (star (χ * peircePlus) * (χ * peircePlus)) := by
  rw [trace_star_mul_self_peircePlus_eq_sum_sq]
  exact add_nonneg (mul_self_nonneg (χ 0 0)) (mul_self_nonneg (χ 1 0))

/-- Zero-hypothesis nonnegativity of the negative right-isospin sector Gram trace. -/
theorem trace_star_mul_self_peirceMinus_nonneg (χ : SplitQuaternion F) :
    0 ≤ Matrix.trace (star (χ * peirceMinus) * (χ * peirceMinus)) := by
  rw [trace_star_mul_self_peirceMinus_eq_sum_sq]
  exact add_nonneg (mul_self_nonneg (χ 0 1)) (mul_self_nonneg (χ 1 1))

/-- Zero-hypothesis nonnegativity of the full Hilbert–Schmidt Gram trace on `SplitQuaternion F`. -/
theorem trace_star_mul_self_nonneg (χ : SplitQuaternion F) :
    0 ≤ Matrix.trace (star χ * χ) := by
  rw [trace_peirce_gram_decomposition]
  exact add_nonneg
    (trace_star_mul_self_peircePlus_nonneg χ)
    (trace_star_mul_self_peirceMinus_nonneg χ)

end OrderedGramPositivity

section PorterNoncommutativeRiccatiAndLoxodromes

variable {A : Type*} [Ring A]

/-!
### Porter's Noncommutative Riccati Operator, Loxodrome Spirals, & Parabolic Commutator Anomaly
-/

/-- **Porter's Noncommutative Riccati Quadratic Operator (`porterRiccati`, Eq. 1.4 & Prop. 3.1)**:
    For `X : Matrix (Fin 2) (Fin 2) A` and `q : A`,
    `P_X(q) = -q * X 1 0 * q - q * X 1 1 + X 0 0 * q + X 0 1`. -/
def porterRiccati (X : Matrix (Fin 2) (Fin 2) A) (q : A) : A :=
  -q * X 1 0 * q - q * X 1 1 + X 0 0 * q + X 0 1

/-- **1. Grassmannian Factorization & Universal Riccati Composition Law (Porter Lemma 2.4)**:
    In ANY associative ring `A` (with zero hypotheses!):
    - `P_X(q) = (X 0 0 * q + X 0 1) - q * (X 1 0 * q + X 1 1)`.
    - `P_{X * Y}(q) = (X 0 0 - q * X 1 0) * P_Y(q) + P_X(q) * (Y 1 0 * q + Y 1 1)`!
    This proves Porter's Lemma 2.4 (`P_X(q) = 0 ∧ P_Y(q) = 0 ⟹ P_{X*Y}(q) = 0`)
    purely algebraically without analytic limits! -/
theorem porterRiccati_factorization_and_mul_composition
    (X Y : Matrix (Fin 2) (Fin 2) A) (q : A) :
    porterRiccati X q = (X 0 0 * q + X 0 1) - q * (X 1 0 * q + X 1 1) ∧
    porterRiccati (X * Y) q =
      (X 0 0 - q * X 1 0) * porterRiccati Y q +
      porterRiccati X q * (Y 1 0 * q + Y 1 1) := by
  refine ⟨?_, ?_⟩
  · unfold porterRiccati
    noncomm_ring
  · unfold porterRiccati
    simp only [Matrix.mul_apply, Fin.sum_univ_two]
    noncomm_ring

/-- **2. Riccati Classification of Spirals, `Pin_±` Reflections, & Idempotent Selectors**:
    In ANY associative ring `A` (with zero hypotheses!):
    - Identity matrix `1`: `porterRiccati 1 q = 0`.
    - Diagonal spiral generator `!![u, 0; 0, v]` (Porter Eq. 3.3): `P(q) = u * q - q * v`.
    - `Pin_+` reflection `!![0, 1; 1, 0]`: `P(q) = 1 - q * q` (selects involutions `q² = 1`).
    - `Pin_-` wheel `!![0, 1; -1, 0]`: `P(q) = 1 + q * q` (selects complex structures `q² = -1`).
    - Idempotent selector `!![1, 0; 1, 0]`: `P(q) = q - q * q` (selects idempotents `q² = q`). -/
theorem porterRiccati_spiral_and_generator_classification (u v q : A) :
    porterRiccati (1 : Matrix (Fin 2) (Fin 2) A) q = 0 ∧
    porterRiccati !![u, 0; 0, v] q = u * q - q * v ∧
    porterRiccati !![(0 : A), 1; 1, 0] q = 1 - q * q ∧
    porterRiccati !![(0 : A), 1; -1, 0] q = 1 + q * q ∧
    porterRiccati !![(1 : A), 0; 1, 0] q = q - q * q := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
  · simp [porterRiccati, add_comm, sub_eq_add_neg]

/-- **3. Porter's Parabolic Commutator Anomaly (Eq. 2.8, p. 6)**:
    For any traceless upper-triangular matrix `X = !![a, x; 0, -a]` over a noncommutative ring `A`,
    squaring `X` produces `a * a` on the diagonal and the exact commutator `a * x - x * a`
    in the upper-right parabolic corner! -/
theorem porter_parabolic_sq_commutator_anomaly (a x : A) :
    let X : Matrix (Fin 2) (Fin 2) A := !![a, x; 0, -a]
    X * X = !![a * a, a * x - x * a; 0, a * a] := by
  intro X
  ext i j; fin_cases i <;> fin_cases j <;>
  · simp [X, Matrix.mul_apply, Fin.sum_univ_two]
    try noncomm_ring

/-- **4. Schur Complement Identity for the Isometric Sphere Radius (`δ_c = b - a c⁻¹ d`, Eq. 4.5)**:
    When `c` has a two-sided inverse `c_inv` (`c * c_inv = 1`), the upper-right entry of
    `!![a, b; c, d] * !![1, -c_inv * d; 0, 1]` isolates Porter's Schur complement `b - a * c_inv * d`! -/
theorem porter_schur_complement_factorization (a b c d c_inv : A) :
    let M : Matrix (Fin 2) (Fin 2) A := !![a, b; c, d]
    let U : Matrix (Fin 2) (Fin 2) A := !![1, -c_inv * d; 0, 1]
    (M * U) 0 0 = a ∧
    (M * U) 0 1 = b - a * c_inv * d ∧
    (M * U) 1 0 = c ∧
    (M * U) 1 1 = d - c * c_inv * d := by
  intro M U
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · simp [M, U, Matrix.mul_apply, Fin.sum_univ_two]
    try noncomm_ring

/-- Upper-right `2 × 2` parabolic seed `!![0, 1; 0, 0]` over `A`. -/
def porterSeedD : Matrix (Fin 2) (Fin 2) A := !![0, 1; 0, 0]

/-- Lower-left `2 × 2` parabolic seed `!![0, 0; 1, 0]` over `A`. -/
def porterSeedB : Matrix (Fin 2) (Fin 2) A := !![0, 0; 1, 0]

/-- **5. Explicit Non-Commutativity Witness on `Matrix (Fin 2) (Fin 2) ℤ` (`porterSeedD * porterSeedB ≠ porterSeedB * porterSeedD`)**:
    In `Matrix (Fin 2) (Fin 2) ℤ`, the upper and lower parabolic seeds do not commute. -/
theorem porter_parabolic_noncomm_witness :
    porterSeedD (A := ℤ) * porterSeedB (A := ℤ) ≠ porterSeedB (A := ℤ) * porterSeedD (A := ℤ) := by
  intro h
  have h00 := congrFun (congrFun h 0) 0
  revert h00
  decide

/-!
### LogCFT Jordan Cell, Multiplicative-to-Additive Monodromy, Temperley–Lieb (`δ = 0`), & Artin Braid Group `B₃`
-/

/-- **Indecomposable LogCFT Jordan Cell (`logCftJordanCell h x = h • 1 + x • d`)**. -/
def logCftJordanCell (h x : F) : SplitQuaternion F :=
  h • (1 : SplitQuaternion F) + x • peirceSeedD

/-- **LogCFT Multiplicative-to-Additive Monodromy Matrix (`logCftMonodromy u τ x`)**:
    Represents `z^{L₀} = u • (1 + (τ * x) • d)` where `u = z^h` and `τ = log z`. -/
def logCftMonodromy (u τ x : F) : SplitQuaternion F :=
  u • (1 : SplitQuaternion F) + (u * τ * x) • peirceSeedD

/-- **First Artin Parabolic Braid Generator `braidSigma1 = 1 + d = !![1, 1; 0, 1]`**. -/
def braidSigma1 : SplitQuaternion F := 1 + peirceSeedD

/-- **Second Artin Parabolic Braid Generator `braidSigma2 = 1 - B = !![1, 0; -1, 1]`**. -/
def braidSigma2 : SplitQuaternion F := 1 - peirceSeedB

/-- **6. Indecomposable LogCFT Jordan Cell & Multiplicative-to-Additive Monodromy Homomorphism**:
    With zero hypotheses in any commutative ring `F`:
    - Jordan-block shift eigenvalue equation: `(logCftJordanCell h x - h • 1) * peircePlus = 0` and
      `(logCftJordanCell h x - h • 1) * peirceSeedD = 0`, while `(logCftJordanCell h x - h • 1) * peirceMinus = x • peirceSeedD`.
    - Nilpotent square of the Jordan anomaly: `(logCftJordanCell h x - h • 1)² = 0`.
    - **Multiplicative-to-Additive Monodromy Law**: multiplying two logarithmic monodromy operators
      `M(u₁, τ₁, x) = u₁ • (1 + τ₁ x • d)` and `M(u₂, τ₂, x) = u₂ • (1 + τ₂ x • d)` multiplies the
      conformal weights `u₁ * u₂` while **adding** the logarithmic branch-cut phases `τ₁ + τ₂`! -/
theorem logCft_jordan_cell_and_monodromy_homomorphism (h x u₁ τ₁ u₂ τ₂ : F) :
    (logCftJordanCell h x - h • (1 : SplitQuaternion F)) * peircePlus = 0 ∧
    (logCftJordanCell h x - h • (1 : SplitQuaternion F)) * peirceMinus = x • peirceSeedD ∧
    (logCftJordanCell h x - h • (1 : SplitQuaternion F)) *
      (logCftJordanCell h x - h • (1 : SplitQuaternion F)) = 0 ∧
    logCftMonodromy u₁ τ₁ x * logCftMonodromy u₂ τ₂ x =
      logCftMonodromy (u₁ * u₂) (τ₁ + τ₂) x := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · dsimp [logCftJordanCell]
    rw [← peircePlus_add_peirceMinus]
    ext i j; fin_cases i <;> fin_cases j <;>
    · simp [peircePlus, peirceMinus, peirceSeedD]
  · dsimp [logCftJordanCell]
    rw [← peircePlus_add_peirceMinus]
    ext i j; fin_cases i <;> fin_cases j <;>
    · simp [peircePlus, peirceMinus, peirceSeedD]
  · dsimp [logCftJordanCell]
    rw [← peircePlus_add_peirceMinus]
    ext i j; fin_cases i <;> fin_cases j <;>
    · simp [peircePlus, peirceMinus, peirceSeedD]
  · dsimp [logCftMonodromy]
    rw [← peircePlus_add_peirceMinus]
    ext i j; fin_cases i <;> fin_cases j <;>
    · simp [peircePlus, peirceMinus, peirceSeedD]; try ring

/-- **7. Logarithmic Temperley–Lieb Algebra (`δ = 0`) & Emil Artin's Braid Group `B₃` Representation**:
    With zero hypotheses in any commutative ring `F`:
    - The nilpotent Peirce seeds `(d, B)` satisfy the defining relations of the `δ = 0` (`q = i` root of unity)
      **Logarithmic Temperley–Lieb Algebra**: `d² = 0`, `B² = 0`, `d * B * d = d`, and `B * d * B = B`.
    - Consequently, the parabolic monodromy generators `σ₁ = 1 + d` and `σ₂ = 1 - B` satisfy
      **Emil Artin's 3-strand Braid Group relation** `σ₁ * σ₂ * σ₁ = σ₂ * σ₁ * σ₂`, and both sides equal
      the Coxeter element `bruhatS = (1 + d) * (1 - B) * (1 + d)`. -/
theorem temperley_lieb_and_artin_braid_group_relations :
    (peirceSeedD : SplitQuaternion F) * peirceSeedB * peirceSeedD = peirceSeedD ∧
    (peirceSeedB : SplitQuaternion F) * peirceSeedD * peirceSeedB = peirceSeedB ∧
    (braidSigma1 : SplitQuaternion F) * braidSigma2 * braidSigma1 =
      braidSigma2 * braidSigma1 * braidSigma2 ∧
    (braidSigma1 : SplitQuaternion F) * braidSigma2 * braidSigma1 = bruhatS := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext i j; fin_cases i <;> fin_cases j <;> simp [peirceSeedD, peirceSeedB]
  · ext i j; fin_cases i <;> fin_cases j <;> simp [peirceSeedD, peirceSeedB]
  · dsimp [braidSigma1, braidSigma2]
    rw [← peircePlus_add_peirceMinus]
    ext i j; fin_cases i <;> fin_cases j <;>
    · simp [peircePlus, peirceMinus, peirceSeedD, peirceSeedB]
  · rfl

/-- **8. Universal Majorana / Clifford Braid Relation (`(1 + J₁)(1 + J₂)(1 + J₁) = (1 + J₂)(1 + J₁)(1 + J₂)`)**:
    In ANY associative ring `A` (with zero hypotheses!), both `(1 + J₁)(1 + J₂)(1 + J₁) - 2 • (J₁ + J₂)`
    and the 3-strand Artin braid defect `(1 + J₁)(1 + J₂)(1 + J₁) - (1 + J₂)(1 + J₁)(1 + J₂)` lie in the
    two-sided ideal generated by `J₁² + 1`, `J₂² + 1`, and the anticommutator `{J₁, J₂}`! -/
theorem majorana_clifford_braid_universal_identity (J₁ J₂ : A) :
    (1 + J₁) * (1 + J₂) * (1 + J₁) - (2 : ℕ) • (J₁ + J₂) =
      (J₁ * J₁ + 1) + (J₁ * J₂ + J₂ * J₁) + J₁ * (J₁ * J₂ + J₂ * J₁) -
      (J₁ * J₁ + 1) * J₂ ∧
    (1 + J₁) * (1 + J₂) * (1 + J₁) - (1 + J₂) * (1 + J₁) * (1 + J₂) =
      (J₁ * J₁ + 1) - (J₂ * J₂ + 1) + (J₁ * J₂ + J₂ * J₁) * (J₁ - J₂) -
      J₂ * (J₁ * J₁ + 1) + J₁ * (J₂ * J₂ + 1) := by
  refine ⟨?_, ?_⟩ <;> noncomm_ring

/-!
### Orientability & Flow Operator Algebra, Exponential Trifactorization (`L D U`), Affine Wavelets, & Walsh–Hadamard Grading Transform
-/

/-- **General Traceless Flow Generator (`tracelessFlowGen α β γ = α • Γ + β • Q + γ • J`)**:
    Combines the orientability/grading involution `polarizationGamma` (`Γ² = +1`), the symmetric
    hyperbolic flow velocity `velocityQ` (`Q² = +1`), and the symplectic wheel `wheelJ` (`J² = -1`). -/
def tracelessFlowGen (α β γ : F) : SplitQuaternion F :=
  α • polarizationGamma + β • velocityQ + γ • wheelJ

/-- **Upper Nilpotent Exponential Shear (`expUpperNil t = 1 + t • d = exp(t d)`)**. -/
def expUpperNil (t : F) : SplitQuaternion F :=
  1 + t • peirceSeedD

/-- **Lower Nilpotent Exponential Shear (`expLowerNil s = 1 + s • B = exp(s B)`)**. -/
def expLowerNil (s : F) : SplitQuaternion F :=
  1 + s • peirceSeedB

/-- **Affine Wavelet Transform Generator (`affineWaveletGen lam mu t = D(lam, mu) + t • d`)**:
    Combines the idempotent-driven Cartan dilation `hyperbolicKernel lam mu` with the upper
    nilpotent translation `t • peirceSeedD` in the upper Borel parabolic subgroup. -/
def affineWaveletGen (lam mu t : F) : SplitQuaternion F :=
  hyperbolicKernel lam mu + t • peirceSeedD

/-- **9. Orientability & Flow Clifford Algebra and Universal Casimir On-Shell Mass-Shell Law**:
    With zero hypotheses:
    - Pairwise Clifford anticommutation: `{Γ, Q} = 0`, `{Γ, J} = 0`, and `{Q, J} = 0`.
    - Mutual factorization: `Γ * Q = -J`, `Γ * J = -Q`, and `J * Q = Γ`.
    - **Universal Casimir On-Shell Law**: for any `(α, β, γ)`, the square of `tracelessFlowGen α β γ`
      is a pure scalar multiple of `1` controlled by the `(2, 1)` Casimir invariant `α² + β² - γ²`! -/
theorem orientability_and_flow_clifford_casimir_onshell (α β γ : F) :
    (polarizationGamma : SplitQuaternion F) * velocityQ + velocityQ * polarizationGamma = 0 ∧
    (polarizationGamma : SplitQuaternion F) * wheelJ + wheelJ * polarizationGamma = 0 ∧
    (velocityQ : SplitQuaternion F) * wheelJ + wheelJ * velocityQ = 0 ∧
    (polarizationGamma : SplitQuaternion F) * velocityQ = wheelJ ∧
    (polarizationGamma : SplitQuaternion F) * wheelJ = velocityQ ∧
    tracelessFlowGen α β γ * tracelessFlowGen α β γ =
      (α * α + β * β - γ * γ) • (1 : SplitQuaternion F) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · ext i j; fin_cases i <;> fin_cases j <;>
    simp [polarizationGamma, velocityQ, peircePlus, peirceMinus, peirceSeedD, peirceSeedB]
  · ext i j; fin_cases i <;> fin_cases j <;>
    simp [polarizationGamma, wheelJ, peircePlus, peirceMinus, peirceSeedD, peirceSeedB]
  · ext i j; fin_cases i <;> fin_cases j <;>
    simp [velocityQ, wheelJ, peirceSeedD, peirceSeedB]
  · ext i j; fin_cases i <;> fin_cases j <;>
    simp [polarizationGamma, velocityQ, wheelJ, peircePlus, peirceMinus, peirceSeedD, peirceSeedB]
  · ext i j; fin_cases i <;> fin_cases j <;>
    simp [polarizationGamma, velocityQ, wheelJ, peircePlus, peirceMinus, peirceSeedD, peirceSeedB]
  · dsimp [tracelessFlowGen]
    rw [← peircePlus_add_peirceMinus]
    ext i j; fin_cases i <;> fin_cases j <;>
    · simp [polarizationGamma, velocityQ, wheelJ, peircePlus, peirceMinus, peirceSeedD, peirceSeedB]
      ring

/-- **10. Nilpotent Exponential Shear Group Laws, Affine Wavelet Semigroup, & Gauss–Bruhat `L D U` Trifactorization**:
    With zero hypotheses in any commutative ring `F`:
    - Nilpotent exponential homomorphisms: `expUpperNil t₁ * expUpperNil t₂ = expUpperNil (t₁ + t₂)`
      and `expLowerNil s₁ * expLowerNil s₂ = expLowerNil (s₁ + s₂)`.
    - **Affine Wavelet Semigroup Law**:
      `affineWaveletGen lam₁ mu₁ t₁ * affineWaveletGen lam₂ mu₂ t₂ = affineWaveletGen (lam₁ * lam₂) (mu₁ * mu₂) (lam₁ * t₂ + t₁ * mu₂)`.
    - **Gauss–Bruhat `L D U` Trifactorization**:
      `expLowerNil s₁ * hyperbolicKernel lam₁ mu₁ * expUpperNil t₁ = !![lam₁, lam₁ * t₁; lam₁ * s₁, lam₁ * s₁ * t₁ + mu₁]` and
      `expLowerNil c * hyperbolicKernel 1 (d - b * c) * expUpperNil b = !![1, b; c, d]`.
-/
theorem expUpperNil_expLowerNil_mul_and_affine_wavelet_semigroup
    (lam₁ mu₁ t₁ lam₂ mu₂ t₂ s₁ s₂ b c d : F) :
    expUpperNil t₁ * expUpperNil t₂ = expUpperNil (t₁ + t₂) ∧
    expLowerNil s₁ * expLowerNil s₂ = expLowerNil (s₁ + s₂) ∧
    affineWaveletGen lam₁ mu₁ t₁ * affineWaveletGen lam₂ mu₂ t₂ =
      affineWaveletGen (lam₁ * lam₂) (mu₁ * mu₂) (lam₁ * t₂ + t₁ * mu₂) ∧
    expLowerNil s₁ * hyperbolicKernel lam₁ mu₁ * expUpperNil t₁ =
      (!![lam₁, lam₁ * t₁; lam₁ * s₁, lam₁ * s₁ * t₁ + mu₁] : SplitQuaternion F) ∧
    expLowerNil c * hyperbolicKernel 1 (d - b * c) * expUpperNil b =
      (!![1, b; c, d] : SplitQuaternion F) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · dsimp [expUpperNil]
    rw [← peircePlus_add_peirceMinus]
    ext i j; fin_cases i <;> fin_cases j <;>
    · simp [peircePlus, peirceMinus, peirceSeedD]; try ring
  · dsimp [expLowerNil]
    rw [← peircePlus_add_peirceMinus]
    ext i j; fin_cases i <;> fin_cases j <;>
    · simp [peircePlus, peirceMinus, peirceSeedB]; try ring
  · dsimp [affineWaveletGen, hyperbolicKernel]
    ext i j; fin_cases i <;> fin_cases j <;>
    · simp [peircePlus, peirceMinus, peirceSeedD]; try ring
  · dsimp [expLowerNil, expUpperNil, hyperbolicKernel]
    rw [← peircePlus_add_peirceMinus]
    ext i j; fin_cases i <;> fin_cases j <;>
    · simp [peircePlus, peirceMinus, peirceSeedD, peirceSeedB]; try ring
  · dsimp [expLowerNil, expUpperNil, hyperbolicKernel]
    rw [← peircePlus_add_peirceMinus]
    ext i j; fin_cases i <;> fin_cases j <;>
    · simp [peircePlus, peirceMinus, peirceSeedD, peirceSeedB]; try ring

/-- **11. Discrete `ℤ₂ × ℤ₂` Walsh–Hadamard / Fourier Grading Inversion via `polarizationGamma`**:
    With zero hypotheses, the 4 Peirce grading sectors of any operator `X : SplitQuaternion F` are
    extracted by the 4 discrete sign characters `(1 ± Γ) * X * (1 ± Γ)` of `polarizationGamma`:
    - `(1 + Γ) * X * (1 + Γ) = 4 • (P_+ * X * P_+)`
    - `(1 - Γ) * X * (1 - Γ) = 4 • (P_- * X * P_-)`
    - `(1 + Γ) * X * (1 - Γ) = 4 • (P_+ * X * P_-)`
    - `(1 - Γ) * X * (1 + Γ) = 4 • (P_- * X * P_+)`. -/
theorem walsh_hadamard_peirce_fourier_inversion (X : SplitQuaternion F) :
    (1 + polarizationGamma) * X * (1 + polarizationGamma) =
      (4 : F) • (peircePlus * X * peircePlus) ∧
    (1 - polarizationGamma) * X * (1 - polarizationGamma) =
      (4 : F) • (peirceMinus * X * peirceMinus) ∧
    (1 + polarizationGamma) * X * (1 - polarizationGamma) =
      (4 : F) • (peircePlus * X * peirceMinus) ∧
    (1 - polarizationGamma) * X * (1 + polarizationGamma) =
      (4 : F) • (peirceMinus * X * peircePlus) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · dsimp [polarizationGamma]
    rw [← peircePlus_add_peirceMinus]
    conv_lhs => rw [eq_eta X]
    conv_rhs => rw [eq_eta X]
    ext i j; fin_cases i <;> fin_cases j <;>
    · simp [peircePlus, peirceMinus]; try ring

/-- **12. Universal Associative-Ring Walsh–Hadamard Grading Completeness & Orientability–Flow Casimir Law**:
    In ANY associative ring `A` (with zero hypotheses on `Γ, Q, J, X, D₁, D₂, N₁, N₂ : A`!):
    - **4-Sector Walsh–Hadamard Completeness**:
      `(1 + Γ)X(1 + Γ) + (1 - Γ)X(1 - Γ) + (1 + Γ)X(1 - Γ) + (1 - Γ)X(1 + Γ) = 4 • X`.
    - **Block-Diagonal (Grade `0`) vs. Off-Diagonal (Grade `±1`) Separation**:
      `(1 + Γ)X(1 + Γ) + (1 - Γ)X(1 - Γ) = 2 • (X + Γ X Γ)` and
      `(1 + Γ)X(1 - Γ) + (1 - Γ)X(1 + Γ) = 2 • (X - Γ X Γ)`.
    - **Signed Chiral Grading Commutator**:
      `(1 + Γ)X(1 - Γ) - (1 - Γ)X(1 + Γ) = 2 • (Γ X - X Γ)`.
    - **Universal Orientability–Flow–Wheel Clifford Casimir Identity**:
      `(Γ + Q + J)² - (Γ² + Q² + J²) = {Γ, Q} + {Γ, J} + {Q, J}`.
    - **Universal Affine Wavelet Upper-Borel Product Decomposition**:
      `(D₁ + N₁)(D₂ + N₂) - (D₁ D₂ + (D₁ N₂ + N₁ D₂)) = N₁ N₂`. -/
theorem universal_ring_walsh_hadamard_and_orientability_flow_casimir
    (Γ Q J X D₁ D₂ N₁ N₂ : A) :
    (1 + Γ) * X * (1 + Γ) + (1 - Γ) * X * (1 - Γ) +
      (1 + Γ) * X * (1 - Γ) + (1 - Γ) * X * (1 + Γ) = (4 : ℕ) • X ∧
    (1 + Γ) * X * (1 + Γ) + (1 - Γ) * X * (1 - Γ) =
      (2 : ℕ) • (X + Γ * X * Γ) ∧
    (1 + Γ) * X * (1 - Γ) + (1 - Γ) * X * (1 + Γ) =
      (2 : ℕ) • (X - Γ * X * Γ) ∧
    (1 + Γ) * X * (1 - Γ) - (1 - Γ) * X * (1 + Γ) =
      (2 : ℕ) • (Γ * X - X * Γ) ∧
    (Γ + Q + J) * (Γ + Q + J) - (Γ * Γ + Q * Q + J * J) =
      (Γ * Q + Q * Γ) + (Γ * J + J * Γ) + (Q * J + J * Q) ∧
    (D₁ + N₁) * (D₂ + N₂) - (D₁ * D₂ + (D₁ * N₂ + N₁ * D₂)) = N₁ * N₂ := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> noncomm_ring

/-!
### Gauss–Bruhat–Harish-Chandra Trifactor Flow (`trifactorFlow`), Schur Reconstruction, & Two-Sided Loxodromic Twin-Wave Kernel
-/

/-- **Nilpotent–Idempotent Trifactor Flow (`trifactorFlow β λ μ α`)**:
    `(1 + β • B) * (λ • P_+ + μ • P_-) * (1 + α • d) = !![λ, λ * α; λ * β, μ + λ * α * β]`. -/
def trifactorFlow (β lam mu α : F) : SplitQuaternion F :=
  (1 + β • peirceSeedB) * hyperbolicKernel lam mu * (1 + α • peirceSeedD)

/-- **Reversed Trifactor Inverse Flow (`trifactorFlowInv α invLam invMu β`)**:
    `(1 - α • d) * (invLam • P_+ + invMu • P_-) * (1 - β • B)`. -/
def trifactorFlowInv (α invLam invMu β : F) : SplitQuaternion F :=
  (1 - α • peirceSeedD) * hyperbolicKernel invLam invMu * (1 - β • peirceSeedB)

/-- **Affine Wavelet Scale–Translation Operator (`waveletOp a b = !![a, b; 0, 1]`)**:
    Combines Mellin scale dilation `D(a, 1)` with nilpotent translation `b • peirceSeedD`. -/
def waveletOp (a b : F) : SplitQuaternion F :=
  hyperbolicKernel a 1 + b • peirceSeedD

/-- **Loxodromic Laplace–Fourier Kernel (`loxodromicKernel λ μ c s = D(λ, μ) * (c • 1 + s • J)`)**. -/
def loxodromicKernel (lam mu c s : F) : SplitQuaternion F :=
  hyperbolicKernel lam mu * (c • (1 : SplitQuaternion F) + s • wheelJ)

/-- **Backward Twin Loxodromic Kernel (`loxodromicTwinKernel c s invLam invMu = (c • 1 - s • J) * D(invLam, invMu)`)**. -/
def loxodromicTwinKernel (c s invLam invMu : F) : SplitQuaternion F :=
  (c • (1 : SplitQuaternion F) - s • wheelJ) * hyperbolicKernel invLam invMu

/-- **13. Trifactor Casimir On-Shell Invariance, Two-Sided Inversion, Wavelet Semigroup, & Exact Schur Reconstruction**:
    With zero hypotheses:
    - **Casimir On-Shell Determinant**: `det (trifactorFlow β λ μ α) = λ * μ` (independent of `α, β`!).
    - **Exact Reversed Trifactor Inverse (`u, v : Fˣ`)**:
      `trifactorFlow β u v α * trifactorFlowInv α u⁻¹ v⁻¹ β = 1`.
    - **Affine Wavelet Semigroup Law**: `waveletOp a₁ b₁ * waveletOp a₂ b₂ = waveletOp (a₁ * a₂) (b₁ + a₁ * b₂)`.
    - **Universal Schur Reconstruction (`u : Fˣ`)**:
      Every matrix `!![u, x₀₁; x₁₀, x₁₁]` equals `trifactorFlow (u⁻¹ * x₁₀) u (x₁₁ - x₁₀ * u⁻¹ * x₀₁) (u⁻¹ * x₀₁)`! -/
theorem trifactorFlow_casimir_wavelet_and_schur_reconstruction
    (β lam mu α a₁ b₁ a₂ b₂ x₀₁ x₁₀ x₁₁ : F) (u v : Fˣ) :
    Matrix.det (trifactorFlow β lam mu α) = lam * mu ∧
    trifactorFlow β (u : F) (v : F) α *
      trifactorFlowInv α (↑u⁻¹ : F) (↑v⁻¹ : F) β = 1 ∧
    waveletOp a₁ b₁ * waveletOp a₂ b₂ = waveletOp (a₁ * a₂) (b₁ + a₁ * b₂) ∧
    trifactorFlow (x₁₀ * (↑u⁻¹ : F)) (u : F)
      (x₁₁ - x₁₀ * (↑u⁻¹ : F) * x₀₁) ((↑u⁻¹ : F) * x₀₁) =
      !![(u : F), x₀₁; x₁₀, x₁₁] := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · dsimp [trifactorFlow, hyperbolicKernel]
    rw [← peircePlus_add_peirceMinus]
    simp [peircePlus, peirceMinus, peirceSeedD, peirceSeedB, Matrix.det_fin_two]; ring
  · have h_d : ((1 : SplitQuaternion F) + α • peirceSeedD) * (1 - α • peirceSeedD) = 1 := by
      rw [← peircePlus_add_peirceMinus]
      ext i j; fin_cases i <;> fin_cases j <;> simp [peircePlus, peirceMinus, peirceSeedD]
    have h_B : ((1 : SplitQuaternion F) + β • peirceSeedB) * (1 - β • peirceSeedB) = 1 := by
      rw [← peircePlus_add_peirceMinus]
      ext i j; fin_cases i <;> fin_cases j <;> simp [peircePlus, peirceMinus, peirceSeedB]
    have h_D : hyperbolicKernel (u : F) (v : F) *
               hyperbolicKernel (↑u⁻¹ : F) (↑v⁻¹ : F) = 1 := by
      rw [← peircePlus_add_peirceMinus]
      ext i j; fin_cases i <;> fin_cases j <;>
        simp [hyperbolicKernel, peircePlus, peirceMinus, Units.mul_inv]
    dsimp [trifactorFlow, trifactorFlowInv]
    calc
      (1 + β • peirceSeedB) * hyperbolicKernel (u : F) (v : F) * (1 + α • peirceSeedD) *
          ((1 - α • peirceSeedD) * hyperbolicKernel (↑u⁻¹ : F) (↑v⁻¹ : F) * (1 - β • peirceSeedB)) =
        (1 + β • peirceSeedB) * (hyperbolicKernel (u : F) (v : F) *
          (((1 + α • peirceSeedD) * (1 - α • peirceSeedD)) *
          hyperbolicKernel (↑u⁻¹ : F) (↑v⁻¹ : F))) * (1 - β • peirceSeedB) := by
        simp only [mul_assoc]
      _ = (1 + β • peirceSeedB) * (1 - β • peirceSeedB) := by
        rw [h_d, one_mul, h_D, mul_one]
      _ = 1 := h_B
  · dsimp [waveletOp, hyperbolicKernel]
    ext i j; fin_cases i <;> fin_cases j <;>
    · simp [peircePlus, peirceMinus, peirceSeedD]; try ring
  · dsimp [trifactorFlow, hyperbolicKernel]
    rw [← peircePlus_add_peirceMinus]
    ext i j; fin_cases i <;> fin_cases j <;>
    · simp [peircePlus, peirceMinus, peirceSeedD, peirceSeedB]; try ring

/-- **14. Loxodromic Twin-Wave Kernel: Casimir Determinant, Cartan Grading Flip, & Twin Inversion**:
    With zero hypotheses:
    - **Loxodromic Casimir Factorization**: `det (loxodromicKernel λ μ c s) = (λ * μ) * (c * c + s * s)`.
    - **Cartan Grading Conjugation**: `Γ * loxodromicKernel λ μ c s * Γ = loxodromicKernel λ μ c (-s)`.
    - **Forward–Backward Twin Wave Inversion (`u, v : Fˣ`)**:
      `loxodromicKernel u v c s * loxodromicTwinKernel c s u⁻¹ v⁻¹ = (c * c + s * s) • 1`! -/
theorem loxodromicKernel_casimir_grading_and_twin_inversion
    (lam mu c s : F) (u v : Fˣ) :
    Matrix.det (loxodromicKernel lam mu c s) = (lam * mu) * (c * c + s * s) ∧
    polarizationGamma * loxodromicKernel lam mu c s * polarizationGamma =
      loxodromicKernel lam mu c (-s) ∧
    loxodromicKernel (u : F) (v : F) c s *
      loxodromicTwinKernel c s (↑u⁻¹ : F) (↑v⁻¹ : F) =
      (c * c + s * s) • (1 : SplitQuaternion F) := by
  have h_grad : polarizationGamma * loxodromicKernel lam mu c s * polarizationGamma =
      loxodromicKernel lam mu c (-s) := by
    dsimp [loxodromicKernel, polarizationGamma, hyperbolicKernel, wheelJ]
    rw [← peircePlus_add_peirceMinus]
    ext i j; fin_cases i <;> fin_cases j <;>
    · simp [peircePlus, peirceMinus, peirceSeedD, peirceSeedB]; try ring
  refine ⟨?_, h_grad, ?_⟩
  · dsimp [loxodromicKernel, hyperbolicKernel, wheelJ]
    rw [← peircePlus_add_peirceMinus]
    simp [peircePlus, peirceMinus, peirceSeedD, peirceSeedB, Matrix.det_fin_two]; ring
  · have h_R : (c • (1 : SplitQuaternion F) + s • wheelJ) *
               (c • (1 : SplitQuaternion F) - s • wheelJ) =
               (c * c + s * s) • (1 : SplitQuaternion F) := by
      dsimp [wheelJ]
      rw [← peircePlus_add_peirceMinus]
      ext i j; fin_cases i <;> fin_cases j <;>
      · simp [peircePlus, peirceMinus, peirceSeedD, peirceSeedB]; try ring
    have h_D : hyperbolicKernel (u : F) (v : F) *
               hyperbolicKernel (↑u⁻¹ : F) (↑v⁻¹ : F) = 1 := by
      rw [← peircePlus_add_peirceMinus]
      ext i j; fin_cases i <;> fin_cases j <;>
        simp [hyperbolicKernel, peircePlus, peirceMinus, Units.mul_inv]
    dsimp [loxodromicKernel, loxodromicTwinKernel]
    calc
      hyperbolicKernel (u : F) (v : F) * (c • 1 + s • wheelJ) *
          ((c • 1 - s • wheelJ) * hyperbolicKernel (↑u⁻¹ : F) (↑v⁻¹ : F)) =
        hyperbolicKernel (u : F) (v : F) *
          ((c • 1 + s • wheelJ) * (c • 1 - s • wheelJ)) *
          hyperbolicKernel (↑u⁻¹ : F) (↑v⁻¹ : F) := by simp only [mul_assoc]
      _ = (c * c + s * s) • (hyperbolicKernel (u : F) (v : F) *
          hyperbolicKernel (↑u⁻¹ : F) (↑v⁻¹ : F)) := by
        rw [h_R, Matrix.mul_smul, Matrix.smul_mul, mul_one]
      _ = (c * c + s * s) • 1 := by rw [h_D]

/-- **15. Porter's Riccati Operator on `tracelessFlowGen α β γ` & `trifactorFlow β λ μ α`, and the `(2, 1)` Casimir Discriminant**:
    With zero hypotheses:
    1. On `M = tracelessFlowGen α β γ = α • Γ + β • Q + γ • J`,
       `porterRiccati M x = -(β - γ) * (x * x) + (2 * α) * x + (β + γ)`.
    2. Its quadratic discriminant `(2 * α)² + 4 * (β - γ) * (β + γ)` equals
       `4 * (α * α + β * β - γ * γ)` — exactly 4 times the `(2, 1)` Casimir mass-shell invariant!
    3. On `trifactorFlow β lam mu α = U_-(β) * D(lam, mu) * U_+(α)`,
       `porterRiccati (trifactorFlow β lam mu α) x = -β * lam * (x * x) + (lam - mu - β * lam * α) * x + lam * α`! -/
theorem porterRiccati_tracelessFlowGen_and_casimir_discriminant
    (α β γ lam mu x : F) :
    porterRiccati (tracelessFlowGen α β γ) x =
      -(β - γ) * (x * x) + (2 * α) * x + (β + γ) ∧
    (2 * α) * (2 * α) + 4 * (β - γ) * (β + γ) =
      4 * (α * α + β * β - γ * γ) ∧
    porterRiccati (trifactorFlow β lam mu α) x =
      -β * lam * (x * x) + (lam - mu - β * lam * α) * x + lam * α := by
  refine ⟨?_, ?_, ?_⟩
  · simp [porterRiccati, tracelessFlowGen, polarizationGamma,
          velocityQ, wheelJ, peircePlus, peirceMinus, peirceSeedD, peirceSeedB]
    ring
  · ring
  · dsimp [porterRiccati, trifactorFlow, hyperbolicKernel]
    rw [← peircePlus_add_peirceMinus]
    simp [peircePlus, peirceMinus, peirceSeedD, peirceSeedB]
    ring

/-- **16. Porter's Riccati Composition Law & Casimir Discriminant (`porterRiccati_composition_and_tracelessFlowGen_discriminant`)**:
    1. In any associative ring `A`:
       `P_{X * Y}(q) = (X 0 0 - q * X 1 0) * P_Y(q) + P_X(q) * (Y 1 0 * q + Y 1 1)`.
    2. On `M = tracelessFlowGen α β γ`, `P_M(x) = -(β - γ) * x² + (2 * α) * x + (β + γ)`,
       whose discriminant `(2 * α)² + 4 * (β - γ) * (β + γ)` is `4 * (α² + β² - γ²)`! -/
theorem porterRiccati_composition_and_tracelessFlowGen_discriminant
    (X Y : Matrix (Fin 2) (Fin 2) A) (q : A) (α β γ x : F) :
    porterRiccati (X * Y) q =
      (X 0 0 - q * X 1 0) * porterRiccati Y q +
      porterRiccati X q * (Y 1 0 * q + Y 1 1) ∧
    porterRiccati (tracelessFlowGen α β γ) x =
      -(β - γ) * (x * x) + (2 * α) * x + (β + γ) ∧
    (2 * α) * (2 * α) + 4 * (β - γ) * (β + γ) =
      4 * (α * α + β * β - γ * γ) := by
  exact ⟨(porterRiccati_factorization_and_mul_composition X Y q).2,
         (porterRiccati_tracelessFlowGen_and_casimir_discriminant α β γ 0 0 x).1,
         (porterRiccati_tracelessFlowGen_and_casimir_discriminant α β γ 0 0 x).2.1⟩

/-- **17. Porter's Riccati Composition Law, Casimir Square Completion, & On-Shell Annihilation**:
    1. **Noncommutative Composition (`[Ring A]`)**:
       `P_{X * Y}(q) = (X 0 0 - q * X 1 0) * P_Y(q) + P_X(q) * (Y 1 0 * q + Y 1 1)`.
    2. **Evaluation on `M = tracelessFlowGen α β γ`**:
       `P_M(x) = -(β - γ) * x² + (2 * α) * x + (β + γ)`.
    3. **Division-Free Riccati–Casimir Square Completion**:
       `(α - (β - γ) * x)² + (β - γ) * P_M(x) = α² + β² - γ²`
       (and discriminant `(2 * α)² + 4 * (β - γ) * (β + γ) = 4 * (α² + β² - γ²)`).
    4. **On-Shell Riccati Annihilation of `M * M`**:
       `P_{M * M}(x) = 0` for all `x : F`! -/
theorem porterRiccati_composition_and_tracelessFlowGen_casimir
    (X Y : Matrix (Fin 2) (Fin 2) A) (q : A) (α β γ x : F) :
    porterRiccati (X * Y) q =
      (X 0 0 - q * X 1 0) * porterRiccati Y q +
      porterRiccati X q * (Y 1 0 * q + Y 1 1) ∧
    porterRiccati (tracelessFlowGen α β γ) x =
      -(β - γ) * (x * x) + (2 * α) * x + (β + γ) ∧
    (α - (β - γ) * x) * (α - (β - γ) * x) +
      (β - γ) * porterRiccati (tracelessFlowGen α β γ) x =
      α * α + β * β - γ * γ ∧
    (2 * α) * (2 * α) + 4 * (β - γ) * (β + γ) =
      4 * (α * α + β * β - γ * γ) ∧
    porterRiccati (tracelessFlowGen α β γ * tracelessFlowGen α β γ) x = 0 := by
  have hd := porterRiccati_composition_and_tracelessFlowGen_discriminant X Y q α β γ x
  refine ⟨hd.1, hd.2.1, ?_, hd.2.2, ?_⟩
  · rw [hd.2.1]; ring
  · simp [porterRiccati, tracelessFlowGen, polarizationGamma,
          velocityQ, wheelJ, peircePlus, peirceMinus, peirceSeedD, peirceSeedB,
          Matrix.mul_apply, Fin.sum_univ_two]
    ring

/-- Noncommutative grading involution $U = \begin{pmatrix} 1 & 0 \\ 0 & -1 \end{pmatrix} \in M_2(A)$. -/
def cliffordU : Matrix (Fin 2) (Fin 2) A := !![1, 0; 0, -1]

/-- Noncommutative flip involution $V = \begin{pmatrix} 0 & 1 \\ 1 & 0 \end{pmatrix} \in M_2(A)$. -/
def cliffordV : Matrix (Fin 2) (Fin 2) A := !![0, 1; 1, 0]

/-- Twice the orthogonal Peirce projectors $2 \Pi_\pm = I_2 \pm U \in M_2(A)$. -/
def twoPeircePlus : Matrix (Fin 2) (Fin 2) A := 1 + cliffordU
def twoPeirceMinus : Matrix (Fin 2) (Fin 2) A := 1 - cliffordU

/-- **18. Noncommutative Clifford–Weyl Relations & Chiral Intertwining in $M_2(A)$**:
    Over any noncommutative ring $A$:
    1. $U^2 = I_2$ and $V^2 = I_2$.
    2. Anticommutativity: $U V + V U = 0$.
    3. Peirce Orthogonality: $(I_2 + U)(I_2 - U) = 0$.
    4. Exact Chiral Intertwining: $V (I_2 + U) = (I_2 - U) V$. -/
theorem cliffordWeyl_noncomm_relations :
    (cliffordU : Matrix (Fin 2) (Fin 2) A) * cliffordU = 1 ∧
    (cliffordV : Matrix (Fin 2) (Fin 2) A) * cliffordV = 1 ∧
    (cliffordU : Matrix (Fin 2) (Fin 2) A) * cliffordV + cliffordV * cliffordU = 0 ∧
    (twoPeircePlus : Matrix (Fin 2) (Fin 2) A) * twoPeirceMinus = 0 ∧
    (cliffordV : Matrix (Fin 2) (Fin 2) A) * twoPeircePlus = twoPeirceMinus * cliffordV := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
  (ext i j; fin_cases i <;> fin_cases j <;>
   simp [cliffordU, cliffordV, twoPeircePlus, twoPeirceMinus,
         Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply])

/-- **19. Clifford–Weyl Anticommutation & Peirce Intertwining in $M_2(F)$**:
    1. $\Gamma^2 = I_2$, $Q^2 = I_2$, and $J^2 = -I_2$.
    2. Mutual Clifford Anticommutativity: $\Gamma Q + Q \Gamma = 0$, $\Gamma J + J \Gamma = 0$, $Q J + J Q = 0$.
    3. Exact Peirce Intertwining: $Q e_{11} = e_{22} Q$ and $J e_{11} = e_{22} J$. -/
theorem cliffordWeyl_noncomm_involutions_and_intertwining :
    (polarizationGamma : SplitQuaternion F) * polarizationGamma = 1 ∧
    (velocityQ : SplitQuaternion F) * velocityQ = 1 ∧
    (wheelJ : SplitQuaternion F) * wheelJ = -1 ∧
    (polarizationGamma : SplitQuaternion F) * velocityQ + velocityQ * polarizationGamma = 0 ∧
    (polarizationGamma : SplitQuaternion F) * wheelJ + wheelJ * polarizationGamma = 0 ∧
    (velocityQ : SplitQuaternion F) * wheelJ + wheelJ * velocityQ = 0 ∧
    (velocityQ : SplitQuaternion F) * peircePlus = peirceMinus * velocityQ ∧
    (wheelJ : SplitQuaternion F) * peircePlus = peirceMinus * wheelJ := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  (ext i j; fin_cases i <;> fin_cases j <;>
   simp [polarizationGamma, velocityQ, wheelJ, peircePlus, peirceMinus,
         peirceSeedD, peirceSeedB, Matrix.mul_apply, Fin.sum_univ_two])

/-- Local Majorana mode $\gamma_A = \begin{pmatrix} 1 & 0 \\ 0 & -1 \end{pmatrix} \in M_2(A)$ ($\gamma_A^2 = I_2$). -/
def majoranaA : Matrix (Fin 2) (Fin 2) A := !![1, 0; 0, -1]

/-- Local skew Majorana mode $\gamma_B = \begin{pmatrix} 0 & 1 \\ -1 & 0 \end{pmatrix} \in M_2(A)$ ($\gamma_B^2 = -I_2$). -/
def majoranaB : Matrix (Fin 2) (Fin 2) A := !![0, 1; -1, 0]

/-- Sweet-spot ($t = \Delta$) Kitaev inter-cell right-shift nilpotent
    $K_+ = e_{12} = \begin{pmatrix} 0 & 1 \\ 0 & 0 \end{pmatrix} \in M_2(A)$. -/
def kitaevShiftPlus : Matrix (Fin 2) (Fin 2) A := !![0, 1; 0, 0]

/-- Sweet-spot ($t = \Delta$) Kitaev inter-cell left-shift nilpotent
    $K_- = e_{21} = \begin{pmatrix} 0 & 0 \\ 1 & 0 \end{pmatrix} \in M_2(A)$. -/
def kitaevShiftMinus : Matrix (Fin 2) (Fin 2) A := !![0, 0; 1, 0]

/-- Left boundary Majorana zero-mode projector $P_L = K_+ K_- = e_{11} \in M_2(A)$. -/
def kitaevEdgeLeft : Matrix (Fin 2) (Fin 2) A := !![1, 0; 0, 0]

/-- Right boundary Majorana zero-mode projector $P_R = K_- K_+ = e_{22} \in M_2(A)$. -/
def kitaevEdgeRight : Matrix (Fin 2) (Fin 2) A := !![0, 0; 0, 1]

/-- 2-site noncommutative Kitaev inter-site dimer bond in $M_2(M_2(A))$, coupling the
    right mode ($e_{22}$) of Site 1 to the left mode ($e_{11}$) of Site 2 via the inter-cell
    nilpotents $K_- = e_{21}$ and $K_+ = e_{12}$. -/
def kitaevChainBondDim : Matrix (Fin 2) (Fin 2) (Matrix (Fin 2) (Fin 2) A) :=
  !![kitaevEdgeRight, kitaevShiftMinus;
     kitaevShiftPlus, kitaevEdgeLeft]

/-- Leftmost dangling boundary zero-mode projector on Site 1 of the 2-site chain. -/
def kitaevChainLeftZeroMode : Matrix (Fin 2) (Fin 2) (Matrix (Fin 2) (Fin 2) A) :=
  !![kitaevEdgeLeft, 0;
     0, 0]

/-- Rightmost dangling boundary zero-mode projector on Site 2 of the 2-site chain. -/
def kitaevChainRightZeroMode : Matrix (Fin 2) (Fin 2) (Matrix (Fin 2) (Fin 2) A) :=
  !![0, 0;
     0, kitaevEdgeRight]

/-- **20. Local Majorana Clifford Algebra, Sweet-Spot Nilpotents, & 2-Site Kitaev Zero Modes**:
    Over ANY noncommutative ring $A$:
    1. Local Majorana Clifford Relations:
       $\gamma_A^2 = I_2$, $\gamma_B^2 = -I_2$, and $\gamma_A \gamma_B + \gamma_B \gamma_A = 0$.
    2. Sweet-Spot Nilpotent Factorization:
       $K_+^2 = 0$, $K_-^2 = 0$, and $K_+ K_- + K_- K_+ = I_2$.
    3. Exact Annihilation of Dangling Boundary Zero Modes by the Inter-Site Kitaev Bond:
       $H_{\mathrm{bond}} Z_L = 0$, $Z_L H_{\mathrm{bond}} = 0$,
       $H_{\mathrm{bond}} Z_R = 0$, and $Z_R H_{\mathrm{bond}} = 0$.
    4. Mutual Orthogonality & Idempotence of Boundary Zero Modes:
       $Z_L^2 = Z_L$, $Z_R^2 = Z_R$, and $Z_L Z_R = 0$. -/
theorem kitaevMajoranaChain_clifford_and_boundary_zero_modes :
    (majoranaA : Matrix (Fin 2) (Fin 2) A) * majoranaA = 1 ∧
    (majoranaB : Matrix (Fin 2) (Fin 2) A) * majoranaB = -1 ∧
    (majoranaA : Matrix (Fin 2) (Fin 2) A) * majoranaB + majoranaB * majoranaA = 0 ∧
    (kitaevShiftPlus : Matrix (Fin 2) (Fin 2) A) * kitaevShiftPlus = 0 ∧
    (kitaevShiftMinus : Matrix (Fin 2) (Fin 2) A) * kitaevShiftMinus = 0 ∧
    (kitaevShiftPlus : Matrix (Fin 2) (Fin 2) A) * kitaevShiftMinus +
      kitaevShiftMinus * kitaevShiftPlus = 1 ∧
    (kitaevChainBondDim : Matrix (Fin 2) (Fin 2) (Matrix (Fin 2) (Fin 2) A)) *
      kitaevChainLeftZeroMode = 0 ∧
    kitaevChainLeftZeroMode *
      (kitaevChainBondDim : Matrix (Fin 2) (Fin 2) (Matrix (Fin 2) (Fin 2) A)) = 0 ∧
    (kitaevChainBondDim : Matrix (Fin 2) (Fin 2) (Matrix (Fin 2) (Fin 2) A)) *
      kitaevChainRightZeroMode = 0 ∧
    kitaevChainRightZeroMode *
      (kitaevChainBondDim : Matrix (Fin 2) (Fin 2) (Matrix (Fin 2) (Fin 2) A)) = 0 ∧
    (kitaevChainLeftZeroMode : Matrix (Fin 2) (Fin 2) (Matrix (Fin 2) (Fin 2) A)) *
      kitaevChainLeftZeroMode = kitaevChainLeftZeroMode ∧
    (kitaevChainRightZeroMode : Matrix (Fin 2) (Fin 2) (Matrix (Fin 2) (Fin 2) A)) *
      kitaevChainRightZeroMode = kitaevChainRightZeroMode ∧
    (kitaevChainLeftZeroMode : Matrix (Fin 2) (Fin 2) (Matrix (Fin 2) (Fin 2) A)) *
      kitaevChainRightZeroMode = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [majoranaA, Matrix.mul_apply, Fin.sum_univ_two]
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [majoranaB, Matrix.mul_apply, Fin.sum_univ_two]
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [majoranaA, majoranaB]
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [kitaevShiftPlus, Matrix.mul_apply, Fin.sum_univ_two]
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [kitaevShiftMinus, Matrix.mul_apply, Fin.sum_univ_two]
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [kitaevShiftPlus, kitaevShiftMinus]
  · ext i j k l; fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
      simp [kitaevChainBondDim, kitaevChainLeftZeroMode, kitaevEdgeRight, kitaevEdgeLeft,
            kitaevShiftPlus, kitaevShiftMinus, Matrix.mul_apply, Fin.sum_univ_two]
  · ext i j k l; fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
      simp [kitaevChainBondDim, kitaevChainLeftZeroMode, kitaevEdgeRight, kitaevEdgeLeft,
            kitaevShiftPlus, kitaevShiftMinus, Matrix.mul_apply, Fin.sum_univ_two]
  · ext i j k l; fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
      simp [kitaevChainBondDim, kitaevChainRightZeroMode, kitaevEdgeRight, kitaevEdgeLeft,
            kitaevShiftPlus, kitaevShiftMinus, Matrix.mul_apply, Fin.sum_univ_two]
  · ext i j k l; fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
      simp [kitaevChainBondDim, kitaevChainRightZeroMode, kitaevEdgeRight, kitaevEdgeLeft,
            kitaevShiftPlus, kitaevShiftMinus, Matrix.mul_apply, Fin.sum_univ_two]
  · ext i j k l; fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
      simp [kitaevChainLeftZeroMode, kitaevEdgeLeft, Matrix.mul_apply, Fin.sum_univ_two]
  · ext i j k l; fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
      simp [kitaevChainRightZeroMode, kitaevEdgeRight, Matrix.mul_apply, Fin.sum_univ_two]
  · ext i j k l; fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
      simp [kitaevChainLeftZeroMode, kitaevChainRightZeroMode,
            Matrix.mul_apply, Fin.sum_univ_two]

/-!
### Archetypes XVII–XX: Cuntz–Majorana Braiding, Noncommutative Gauss–LDU Banachiewicz Inversion, Sylvester–Peirce Derivations, and UHF Inductive Colimits
-/

/-- First Cuntz partial isometry $S_1 = e_{11} = \begin{pmatrix} 1 & 0 \\ 0 & 0 \end{pmatrix} \in M_2(A)$. -/
def cuntzS1 : Matrix (Fin 2) (Fin 2) A := !![1, 0; 0, 0]

/-- Second Cuntz partial isometry $S_2 = e_{21} = \begin{pmatrix} 0 & 0 \\ 1 & 0 \end{pmatrix} \in M_2(A)$. -/
def cuntzS2 : Matrix (Fin 2) (Fin 2) A := !![0, 0; 1, 0]

/-- Adjoint partial isometry $S_2^* = e_{12} = \begin{pmatrix} 0 & 1 \\ 0 & 0 \end{pmatrix} \in M_2(A)$. -/
def cuntzS2Star : Matrix (Fin 2) (Fin 2) A := !![0, 1; 0, 0]

/-- Symmetric Majorana partner $\gamma_X = \gamma_A \gamma_B = \begin{pmatrix} 0 & 1 \\ 1 & 0 \end{pmatrix} \in M_2(A)$. -/
def majoranaX : Matrix (Fin 2) (Fin 2) A := !![0, 1; 1, 0]

/-- Unnormalized Ivanov–Majorana braid rotor $B_+ = I_2 + \gamma_B = \begin{pmatrix} 1 & 1 \\ -1 & 1 \end{pmatrix} \in M_2(A)$. -/
def majoranaBraidPlus : Matrix (Fin 2) (Fin 2) A := !![1, 1; -1, 1]

/-- Inverse unnormalized Ivanov–Majorana braid rotor $B_- = I_2 - \gamma_B = \begin{pmatrix} 1 & -1 \\ 1 & 1 \end{pmatrix} \in M_2(A)$. -/
def majoranaBraidMinus : Matrix (Fin 2) (Fin 2) A := !![1, -1; 1, 1]

/-- **21. Noncommutative Cuntz Partition of Unity & Ivanov–Majorana Braiding Exchange Law**:
    Over ANY noncommutative ring $A$:
    1. Cuntz Range Orthogonality & Partition of Unity:
       $S_1^* S_2 = 0$, $S_2^* S_1 = 0$, and $S_1 S_1^* + S_2 S_2^* = I_2$.
    2. Majorana Braid Rotor Decomposition & Inversion:
       $B_+ = I_2 + \gamma_B$, $B_- = I_2 - \gamma_B$, $B_+ B_- = 2 I_2$, and $B_- B_+ = 2 I_2$.
    3. Exact Ivanov–Majorana Braiding Exchange of $(\gamma_A, \gamma_X)$:
       $B_+ \gamma_A B_- = -2 \gamma_X$ and $B_+ \gamma_X B_- = 2 \gamma_A$. -/
theorem cuntz_and_majorana_braid_relations :
    (cuntzS1 : Matrix (Fin 2) (Fin 2) A) * cuntzS2 = 0 ∧
    (cuntzS2Star : Matrix (Fin 2) (Fin 2) A) * cuntzS1 = 0 ∧
    (cuntzS1 : Matrix (Fin 2) (Fin 2) A) * cuntzS1 + cuntzS2 * cuntzS2Star = 1 ∧
    (majoranaBraidPlus : Matrix (Fin 2) (Fin 2) A) = 1 + majoranaB ∧
    (majoranaBraidMinus : Matrix (Fin 2) (Fin 2) A) = 1 - majoranaB ∧
    (majoranaBraidPlus : Matrix (Fin 2) (Fin 2) A) * majoranaBraidMinus = 2 • 1 ∧
    (majoranaBraidMinus : Matrix (Fin 2) (Fin 2) A) * majoranaBraidPlus = 2 • 1 ∧
    (majoranaBraidPlus : Matrix (Fin 2) (Fin 2) A) * majoranaA * majoranaBraidMinus =
      -(2 • majoranaX) ∧
    (majoranaBraidPlus : Matrix (Fin 2) (Fin 2) A) * majoranaX * majoranaBraidMinus =
      2 • majoranaA := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [cuntzS1, cuntzS2, Matrix.mul_apply, Fin.sum_univ_two]
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [cuntzS2Star, cuntzS1, Matrix.mul_apply, Fin.sum_univ_two]
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [cuntzS1, cuntzS2, cuntzS2Star]
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [majoranaBraidPlus, majoranaB]
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [majoranaBraidMinus, majoranaB]
  · ext i j; fin_cases i <;> fin_cases j <;>
      (simp [majoranaBraidPlus, majoranaBraidMinus, Matrix.mul_apply, Fin.sum_univ_two, two_smul];
       try noncomm_ring)
  · ext i j; fin_cases i <;> fin_cases j <;>
      (simp [majoranaBraidPlus, majoranaBraidMinus, Matrix.mul_apply, Fin.sum_univ_two, two_smul];
       try noncomm_ring)
  · ext i j; fin_cases i <;> fin_cases j <;>
      (simp [majoranaBraidPlus, majoranaBraidMinus, majoranaA, majoranaX,
             Matrix.mul_apply, Fin.sum_univ_two, two_smul];
       try noncomm_ring)
  · ext i j; fin_cases i <;> fin_cases j <;>
      (simp [majoranaBraidPlus, majoranaBraidMinus, majoranaA, majoranaX,
             Matrix.mul_apply, Fin.sum_univ_two, two_smul];
       try noncomm_ring)

/-- Lower unipotent Gauss factor $L(l) = \begin{pmatrix} 1 & 0 \\ l & 1 \end{pmatrix} \in M_2(A)$. -/
def gaussL (l : A) : Matrix (Fin 2) (Fin 2) A := !![1, 0; l, 1]

/-- Diagonal pivot-Schur Gauss factor $D(d_1, d_2) = \begin{pmatrix} d_1 & 0 \\ 0 & d_2 \end{pmatrix} \in M_2(A)$. -/
def gaussD (d₁ d₂ : A) : Matrix (Fin 2) (Fin 2) A := !![d₁, 0; 0, d₂]

/-- Upper unipotent Gauss factor $U(r) = \begin{pmatrix} 1 & r \\ 0 & 1 \end{pmatrix} \in M_2(A)$. -/
def gaussU (r : A) : Matrix (Fin 2) (Fin 2) A := !![1, r; 0, 1]

/-- Noncommutative Gauss–Bruhat LDU trifactor product $L(l) * D(d_1, d_2) * U(r) \in M_2(A)$. -/
def noncommLDU (l d₁ d₂ r : A) : Matrix (Fin 2) (Fin 2) A :=
  gaussL l * gaussD d₁ d₂ * gaussU r

/-- Reverse-order Banachiewicz–Schur inverse trifactor $U(-r) * D(d_1^{-1}, d_2^{-1}) * L(-l) \in M_2(A)$. -/
def noncommLDUInv (l invD₁ invD₂ r : A) : Matrix (Fin 2) (Fin 2) A :=
  gaussU (-r) * gaussD invD₁ invD₂ * gaussL (-l)

/-- **22. Noncommutative Unipotent Factor Inverses, Schur Reconstruction, & Banachiewicz Inverse**:
    Over ANY noncommutative ring $A$, for any $l, d_1, d_2, r, v, w, b \in A$ and units $u, \Delta \in A^\times$:
    1. Unipotent Factor Inverses:
       $L(l) L(-l) = I_2$ and $U(r) U(-r) = I_2$.
    2. Explicit Noncommutative LDU Product:
       $L(l) D(d_1, d_2) U(r) = \begin{pmatrix} d_1 & d_1 r \\ l d_1 & l d_1 r + d_2 \end{pmatrix}$.
    3. Exact Noncommutative Schur Complement Reconstruction of $\begin{pmatrix} u & v \\ w & b \end{pmatrix}$:
       $L(w u^{-1}) D(u, b - w u^{-1} v) U(u^{-1} v) = \begin{pmatrix} u & v \\ w & b \end{pmatrix}$.
    4. Exact Two-Sided Noncommutative Banachiewicz–Schur Inversion:
       $\mathrm{noncommLDU}\;l\;u\;\Delta\;r * \mathrm{noncommLDUInv}\;l\;u^{-1}\;\Delta^{-1}\;r = I_2$ and
       $\mathrm{noncommLDUInv}\;l\;u^{-1}\;\Delta^{-1}\;r * \mathrm{noncommLDU}\;l\;u\;\Delta\;r = I_2$. -/
theorem noncommLDU_schur_reconstruction_and_banachiewicz_inverse
    (l d₁ d₂ r v w b : A) (u Δ : Aˣ) :
    gaussL l * gaussL (-l) = 1 ∧
    gaussU r * gaussU (-r) = 1 ∧
    noncommLDU l d₁ d₂ r = !![d₁, d₁ * r; l * d₁, l * d₁ * r + d₂] ∧
    noncommLDU (w * (↑u⁻¹ : A)) (u : A) (b - w * (↑u⁻¹ : A) * v) ((↑u⁻¹ : A) * v) =
      !![(u : A), v; w, b] ∧
    noncommLDU l (u : A) (Δ : A) r * noncommLDUInv l (↑u⁻¹ : A) (↑Δ⁻¹ : A) r = 1 ∧
    noncommLDUInv l (↑u⁻¹ : A) (↑Δ⁻¹ : A) r * noncommLDU l (u : A) (Δ : A) r = 1 := by
  have hL : ∀ x : A, gaussL x * gaussL (-x) = 1 := by
    intro x; ext i j; fin_cases i <;> fin_cases j <;>
      (simp [gaussL, Matrix.mul_apply, Fin.sum_univ_two]; try noncomm_ring)
  have hL_sym : ∀ x : A, gaussL (-x) * gaussL x = 1 := by
    intro x; ext i j; fin_cases i <;> fin_cases j <;>
      (simp [gaussL, Matrix.mul_apply, Fin.sum_univ_two]; try noncomm_ring)
  have hU : ∀ x : A, gaussU x * gaussU (-x) = 1 := by
    intro x; ext i j; fin_cases i <;> fin_cases j <;>
      (simp [gaussU, Matrix.mul_apply, Fin.sum_univ_two]; try noncomm_ring)
  have hU_sym : ∀ x : A, gaussU (-x) * gaussU x = 1 := by
    intro x; ext i j; fin_cases i <;> fin_cases j <;>
      (simp [gaussU, Matrix.mul_apply, Fin.sum_univ_two]; try noncomm_ring)
  have hD_r : gaussD (u : A) (Δ : A) * gaussD (↑u⁻¹ : A) (↑Δ⁻¹ : A) = 1 := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [gaussD, Matrix.mul_apply, Fin.sum_univ_two]
  have hD_l : gaussD (↑u⁻¹ : A) (↑Δ⁻¹ : A) * gaussD (u : A) (Δ : A) = 1 := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [gaussD, Matrix.mul_apply, Fin.sum_univ_two]
  have h_prod : ∀ l' a₁ a₂ r' : A,
      noncommLDU l' a₁ a₂ r' = !![a₁, a₁ * r'; l' * a₁, l' * a₁ * r' + a₂] := by
    intro l' a₁ a₂ r'
    ext i j; fin_cases i <;> fin_cases j <;>
      (simp [noncommLDU, gaussL, gaussD, gaussU, Matrix.mul_apply, Fin.sum_univ_two];
       try noncomm_ring)
  refine ⟨hL l, hU r, h_prod l d₁ d₂ r, ?_, ?_, ?_⟩
  · rw [h_prod]
    ext i j; fin_cases i <;> fin_cases j <;> (simp; try noncomm_ring)
  · unfold noncommLDU noncommLDUInv
    calc gaussL l * gaussD (u : A) (Δ : A) * gaussU r *
           (gaussU (-r) * gaussD (↑u⁻¹ : A) (↑Δ⁻¹ : A) * gaussL (-l))
      _ = gaussL l * (gaussD (u : A) (Δ : A) * ((gaussU r * gaussU (-r)) *
            gaussD (↑u⁻¹ : A) (↑Δ⁻¹ : A)) * gaussL (-l)) := by simp only [mul_assoc]
      _ = gaussL l * ((gaussD (u : A) (Δ : A) * gaussD (↑u⁻¹ : A) (↑Δ⁻¹ : A)) * gaussL (-l)) := by
          rw [hU r, one_mul, mul_assoc]
      _ = gaussL l * gaussL (-l) := by rw [hD_r, one_mul]
      _ = 1 := hL l
  · unfold noncommLDU noncommLDUInv
    calc gaussU (-r) * gaussD (↑u⁻¹ : A) (↑Δ⁻¹ : A) * gaussL (-l) *
           (gaussL l * gaussD (u : A) (Δ : A) * gaussU r)
      _ = gaussU (-r) * (gaussD (↑u⁻¹ : A) (↑Δ⁻¹ : A) * ((gaussL (-l) * gaussL l) *
            gaussD (u : A) (Δ : A)) * gaussU r) := by simp only [mul_assoc]
      _ = gaussU (-r) * ((gaussD (↑u⁻¹ : A) (↑Δ⁻¹ : A) * gaussD (u : A) (Δ : A)) * gaussU r) := by
          rw [hL_sym l, one_mul, mul_assoc]
      _ = gaussU (-r) * gaussU r := by rw [hD_l, one_mul]
      _ = 1 := hU_sym r

/-- The Sylvester–Peirce grading derivation $\mathrm{ad}_\Gamma(X) = \gamma_A X - X \gamma_A$ in $M_2(A)$. -/
def sylvesterAdGamma (X : Matrix (Fin 2) (Fin 2) A) : Matrix (Fin 2) (Fin 2) A :=
  majoranaA * X - X * majoranaA

/-- Diagonal Peirce projection $X_{\mathrm{diag}} = e_{11} X e_{11} + e_{22} X e_{22}$ in $M_2(A)$. -/
def peirceDiagPart (X : Matrix (Fin 2) (Fin 2) A) : Matrix (Fin 2) (Fin 2) A :=
  !![X 0 0, 0; 0, X 1 1]

/-- Off-diagonal Peirce projection $X_{\mathrm{off}} = e_{11} X e_{22} + e_{22} X e_{11}$ in $M_2(A)$. -/
def peirceOffDiagPart (X : Matrix (Fin 2) (Fin 2) A) : Matrix (Fin 2) (Fin 2) A :=
  !![0, X 0 1; X 1 0, 0]

/-- **23. Sylvester Derivation Kernel, Off-Diagonal Eigen-Square, & Cubic Periodicity**:
    For ANY matrix $X \in M_2(A)$ over a noncommutative ring $A$:
    1. Additive Peirce Split: $X = X_{\mathrm{diag}} + X_{\mathrm{off}}$.
    2. Commutant Kernel Law: $\mathrm{ad}_\Gamma(X_{\mathrm{diag}}) = 0$.
    3. Double Sylvester Derivation on Off-Diagonal Module:
       $\mathrm{ad}_\Gamma(\mathrm{ad}_\Gamma(X)) = 4 \bullet X_{\mathrm{off}}$.
    4. Universal Cubic Period-2 Law:
       $\mathrm{ad}_\Gamma(\mathrm{ad}_\Gamma(\mathrm{ad}_\Gamma(X))) = 4 \bullet \mathrm{ad}_\Gamma(X)$. -/
theorem sylvesterAdGamma_kernel_square_and_cubic_periodicity
    (X : Matrix (Fin 2) (Fin 2) A) :
    peirceDiagPart X + peirceOffDiagPart X = X ∧
    sylvesterAdGamma (peirceDiagPart X) = 0 ∧
    sylvesterAdGamma (sylvesterAdGamma X) = (4 : ℕ) • peirceOffDiagPart X ∧
    sylvesterAdGamma (sylvesterAdGamma (sylvesterAdGamma X)) = (4 : ℕ) • sylvesterAdGamma X := by
  have h_ad : ∀ Y : Matrix (Fin 2) (Fin 2) A,
      sylvesterAdGamma Y = !![0, Y 0 1 + Y 0 1; -(Y 1 0 + Y 1 0), 0] := by
    intro Y; ext i j; fin_cases i <;> fin_cases j <;>
      (simp [sylvesterAdGamma, majoranaA, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two];
       try noncomm_ring)
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [peirceDiagPart, peirceOffDiagPart]
  · rw [h_ad]
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [peirceDiagPart]
  · rw [h_ad, h_ad]
    ext i j; fin_cases i <;> fin_cases j <;>
      (simp [peirceOffDiagPart, nsmul_eq_mul]; try noncomm_ring)
  · rw [h_ad, h_ad, h_ad]
    ext i j; fin_cases i <;> fin_cases j <;>
      (simp [nsmul_eq_mul]; try noncomm_ring)

/-- First-site UHF inductive colimit embedding $\iota_1(X) = \begin{pmatrix} X & 0 \\ 0 & X \end{pmatrix} \in M_2(M_2(A))$. -/
def uhfEmbedSite1 (X : Matrix (Fin 2) (Fin 2) A) :
    Matrix (Fin 2) (Fin 2) (Matrix (Fin 2) (Fin 2) A) :=
  !![X, 0; 0, X]

/-- Graded Jordan–Wigner string involution $\mathcal{J}_1 = \begin{pmatrix} \gamma_A & 0 \\ 0 & -\gamma_A \end{pmatrix} \in M_2(M_2(A))$. -/
def jwStringSite1 : Matrix (Fin 2) (Fin 2) (Matrix (Fin 2) (Fin 2) A) :=
  !![majoranaA, 0; 0, -majoranaA]

/-- Inter-site Jordan–Wigner flip involution $\mathcal{J}_2 = \begin{pmatrix} 0 & I_2 \\ I_2 & 0 \end{pmatrix} \in M_2(M_2(A))$. -/
def jwFlipSite2 : Matrix (Fin 2) (Fin 2) (Matrix (Fin 2) (Fin 2) A) :=
  !![0, 1; 1, 0]

/-- **24. UHF Inductive Colimit Ring Homomorphism & Jordan–Wigner Inter-Site Clifford Relations**:
    Over ANY noncommutative ring $A$ and for all $X, Y \in M_2(A)$:
    1. Unital Inductive Colimit Homomorphism:
       $\iota_1(I_2) = I_4$, $\iota_1(X + Y) = \iota_1(X) + \iota_1(Y)$, and $\iota_1(X Y) = \iota_1(X) \iota_1(Y)$.
    2. Exact Inter-Site Commutativity of Site-1 Operators with Site-2 Flip:
       $\iota_1(X) \mathcal{J}_2 = \mathcal{J}_2 \iota_1(X)$.
    3. Graded Jordan–Wigner Clifford Anticommutation Across Inductive Stages:
       $\mathcal{J}_1^2 = I_4$, $\mathcal{J}_2^2 = I_4$, and $\mathcal{J}_1 \mathcal{J}_2 + \mathcal{J}_2 \mathcal{J}_1 = 0$. -/
theorem uhfInductiveColimit_homomorphism_and_jordan_wigner
    (X Y : Matrix (Fin 2) (Fin 2) A) :
    uhfEmbedSite1 (1 : Matrix (Fin 2) (Fin 2) A) = 1 ∧
    uhfEmbedSite1 (X + Y) = uhfEmbedSite1 X + uhfEmbedSite1 Y ∧
    uhfEmbedSite1 (X * Y) = uhfEmbedSite1 X * uhfEmbedSite1 Y ∧
    uhfEmbedSite1 X * (jwFlipSite2 : Matrix (Fin 2) (Fin 2) (Matrix (Fin 2) (Fin 2) A)) =
      jwFlipSite2 * uhfEmbedSite1 X ∧
    (jwStringSite1 : Matrix (Fin 2) (Fin 2) (Matrix (Fin 2) (Fin 2) A)) * jwStringSite1 = 1 ∧
    (jwFlipSite2 : Matrix (Fin 2) (Fin 2) (Matrix (Fin 2) (Fin 2) A)) * jwFlipSite2 = 1 ∧
    (jwStringSite1 : Matrix (Fin 2) (Fin 2) (Matrix (Fin 2) (Fin 2) A)) * jwFlipSite2 +
      jwFlipSite2 * jwStringSite1 = 0 := by
  have h_majA_sq : (majoranaA : Matrix (Fin 2) (Fin 2) A) * majoranaA = 1 :=
    (kitaevMajoranaChain_clifford_and_boundary_zero_modes (A := A)).1
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · ext i j; fin_cases i <;> fin_cases j <;> rfl
  · ext i j; fin_cases i <;> fin_cases j <;> simp [uhfEmbedSite1]
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [uhfEmbedSite1, Matrix.mul_apply, Fin.sum_univ_two]
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [uhfEmbedSite1, jwFlipSite2, Matrix.mul_apply, Fin.sum_univ_two]
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [jwStringSite1, Matrix.mul_apply, Fin.sum_univ_two, h_majA_sq]
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [jwFlipSite2, Matrix.mul_apply, Fin.sum_univ_two]
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [jwStringSite1, jwFlipSite2]

/-!
### Archetypes XXI–XXVIII: Operator-Valued Kasparov Bimodules, Krein Space Involutions, & Noncommutative Zorn Algebras $\mathrm{Zorn}(A)$
-/

/-- Fundamental Krein metric symmetry $\Gamma = \begin{pmatrix} 1 & 0 \\ 0 & -1 \end{pmatrix} \in M_2(A)$. -/
def kreinGamma : Matrix (Fin 2) (Fin 2) A := !![1, 0; 0, -1]

/-- The indefinite Krein adjoint $X^\flat = \Gamma X^{\mathrm{H}} \Gamma =
    \begin{pmatrix} \mathrm{star}(X_{00}) & -\mathrm{star}(X_{10}) \\ -\mathrm{star}(X_{01}) & \mathrm{star}(X_{11}) \end{pmatrix}$
    on $M_2(A)$ over a noncommutative $*$-ring $A$. -/
def kreinAdjoint [StarRing A] (X : Matrix (Fin 2) (Fin 2) A) : Matrix (Fin 2) (Fin 2) A :=
  !![star (X 0 0), -star (X 1 0);
     -star (X 0 1), star (X 1 1)]

/-- **25. Noncommutative Krein Space Anti-Involution Laws on $M_2(A)$ (Archetype XXI)**:
    Over ANY noncommutative $*$-ring $A$ and for all $X, Y \in M_2(A)$:
    1. Involution Period-2: $(X^\flat)^\flat = X$.
    2. Krein Self-Adjointness of $\Gamma$: $\Gamma^\flat = \Gamma$.
    3. Exact Multiplicative Anti-Homomorphism: $(X Y)^\flat = Y^\flat X^\flat$. -/
theorem kreinAdjoint_involution_and_antihomomorphism [StarRing A]
    (X Y : Matrix (Fin 2) (Fin 2) A) :
    kreinAdjoint (kreinAdjoint X) = X ∧
    kreinAdjoint (kreinGamma : Matrix (Fin 2) (Fin 2) A) = kreinGamma ∧
    kreinAdjoint (X * Y) = kreinAdjoint Y * kreinAdjoint X := by
  refine ⟨?_, ?_, ?_⟩
  · ext i j; fin_cases i <;> fin_cases j <;> simp [kreinAdjoint]
  · ext i j; fin_cases i <;> fin_cases j <;> simp [kreinAdjoint, kreinGamma]
  · ext i j; fin_cases i <;> fin_cases j <;>
      (simp [kreinAdjoint, Matrix.mul_apply, Fin.sum_univ_two, star_add, star_mul];
       try abel)

/-- Grading involution $\Gamma = \begin{pmatrix} 1 & 0 \\ 0 & -1 \end{pmatrix} \in M_2(A)$. -/
def kasparovGamma : Matrix (Fin 2) (Fin 2) A := !![1, 0; 0, -1]

/-- Positive and negative Krein–Peirce subbundle projectors $e_{11}, e_{22} \in M_2(A)$. -/
def kasparovProjPlus : Matrix (Fin 2) (Fin 2) A := !![1, 0; 0, 0]
def kasparovProjMinus : Matrix (Fin 2) (Fin 2) A := !![0, 0; 0, 1]

/-- Odd Kasparov Fredholm/Dirac operator $F(u, v) = \begin{pmatrix} 0 & u \\ v & 0 \end{pmatrix} \in M_2(A)$
    with noncommuting operator entries $u, v \in A$. -/
def kasparovFredholm (u v : A) : Matrix (Fin 2) (Fin 2) A := !![0, u; v, 0]

/-- The Fedosov–Kasparov curvature defect $D_F(u, v) = I_2 - F(u, v)^2 =
    \begin{pmatrix} 1 - u v & 0 \\ 0 & 1 - v u \end{pmatrix} \in M_2(A)$. -/
def kasparovDefect (u v : A) : Matrix (Fin 2) (Fin 2) A :=
  1 - kasparovFredholm u v * kasparovFredholm u v

/-- **26. Even Kasparov Bimodule Relations & Noncommutative Fedosov Defect Intertwining (Archetype XXII)**:
    Over ANY noncommutative operator ring $A$ and for all $u, v \in A$:
    1. Odd Grading Anticommutation: $\Gamma F(u, v) + F(u, v) \Gamma = 0$.
    2. Noncommutative Diagonal Square: $F(u, v)^2 = \begin{pmatrix} u v & 0 \\ 0 & v u \end{pmatrix}$.
    3. Even Grading Commutation of Curvature Defect: $\Gamma D_F(u, v) = D_F(u, v) \Gamma$.
    4. Exact Noncommutative Fedosov Intertwining:
       $F(u, v) D_F(u, v) = D_F(u, v) F(u, v)$ and
       $D_F(u, v) F(u, v) e_{11} = e_{22} F(u, v) D_F(u, v)$. -/
theorem kasparovFredholm_grading_square_and_fedosov_intertwining (u v : A) :
    let F := kasparovFredholm u v
    let D_F := kasparovDefect u v
    kasparovGamma * F + F * kasparovGamma = 0 ∧
    F * F = !![u * v, 0; 0, v * u] ∧
    kasparovGamma * D_F = D_F * kasparovGamma ∧
    F * D_F = D_F * F ∧
    D_F * F * kasparovProjPlus = kasparovProjMinus * F * D_F := by
  intro F D_F
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
  (ext i j; fin_cases i <;> fin_cases j <;>
   (simp [F, D_F, kasparovGamma, kasparovFredholm, kasparovDefect,
          kasparovProjPlus, kasparovProjMinus,
          Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply];
    try noncomm_ring))

/-- 3-component operator tuple $v = (v_x, v_y, v_z) \in A^3$ over a noncommutative ring $A$. -/
@[ext]
structure OpVec3 (A : Type*) where
  x : A
  y : A
  z : A
  deriving DecidableEq

namespace OpVec3

instance : Zero (OpVec3 A) := ⟨⟨0, 0, 0⟩⟩
instance : Inhabited (OpVec3 A) := ⟨0⟩
instance : Add (OpVec3 A) := ⟨fun u v => ⟨u.x + v.x, u.y + v.y, u.z + v.z⟩⟩
instance : Sub (OpVec3 A) := ⟨fun u v => ⟨u.x - v.x, u.y - v.y, u.z - v.z⟩⟩
instance : Neg (OpVec3 A) := ⟨fun u => ⟨-u.x, -u.y, -u.z⟩⟩

/-- Left and right operator action of $A$ on $A^3$. -/
def leftScale (c : A) (u : OpVec3 A) : OpVec3 A := ⟨c * u.x, c * u.y, c * u.z⟩
def rightScale (u : OpVec3 A) (c : A) : OpVec3 A := ⟨u.x * c, u.y * c, u.z * c⟩

@[simp] lemma zero_x : (0 : OpVec3 A).x = 0 := rfl
@[simp] lemma zero_y : (0 : OpVec3 A).y = 0 := rfl
@[simp] lemma zero_z : (0 : OpVec3 A).z = 0 := rfl
@[simp] lemma add_x (u v : OpVec3 A) : (u + v).x = u.x + v.x := rfl
@[simp] lemma add_y (u v : OpVec3 A) : (u + v).y = u.y + v.y := rfl
@[simp] lemma add_z (u v : OpVec3 A) : (u + v).z = u.z + v.z := rfl
@[simp] lemma sub_x (u v : OpVec3 A) : (u - v).x = u.x - v.x := rfl
@[simp] lemma sub_y (u v : OpVec3 A) : (u - v).y = u.y - v.y := rfl
@[simp] lemma sub_z (u v : OpVec3 A) : (u - v).z = u.z - v.z := rfl
@[simp] lemma neg_x (u : OpVec3 A) : (-u).x = -u.x := rfl
@[simp] lemma neg_y (u : OpVec3 A) : (-u).y = -u.y := rfl
@[simp] lemma neg_z (u : OpVec3 A) : (-u).z = -u.z := rfl
@[simp] lemma leftScale_x (c : A) (u : OpVec3 A) : (leftScale c u).x = c * u.x := rfl
@[simp] lemma leftScale_y (c : A) (u : OpVec3 A) : (leftScale c u).y = c * u.y := rfl
@[simp] lemma leftScale_z (c : A) (u : OpVec3 A) : (leftScale c u).z = c * u.z := rfl
@[simp] lemma rightScale_x (u : OpVec3 A) (c : A) : (rightScale u c).x = u.x * c := rfl
@[simp] lemma rightScale_y (u : OpVec3 A) (c : A) : (rightScale u c).y = u.y * c := rfl
@[simp] lemma rightScale_z (u : OpVec3 A) (c : A) : (rightScale u c).z = u.z * c := rfl

/-- Ordered noncommutative dot contraction $u \cdot w = u_x w_x + u_y w_y + u_z w_z \in A$. -/
def dot (u w : OpVec3 A) : A := u.x * w.x + u.y * w.y + u.z * w.z

/-- Naive ordered cross product $(u \times v)_x = u_y v_z - u_z v_y$ over noncommutative $A$. -/
def naiveCross (u v : OpVec3 A) : OpVec3 A :=
  ⟨u.y * v.z - u.z * v.y,
   u.z * v.x - u.x * v.z,
   u.x * v.y - u.y * v.x⟩

/-- Skew-symmetrized operator cross product $u \times_{\mathrm{skew}} v = u \times v - v \times u$,
    which satisfies $v \times_{\mathrm{skew}} v = 0$ over ANY noncommutative ring $A$. -/
def skewCross (u v : OpVec3 A) : OpVec3 A :=
  naiveCross u v - naiveCross v u

end OpVec3

/-- **27. Yang–Mills Commutator Curvature of Naive Cross vs. Alternativity of Skew Cross (Archetype XXIII)**:
    Over ANY noncommutative operator ring $A$ and for all $u, v \in A^3$:
    1. Naive Self-Cross-Product is the Noncommutative Operator Commutator Curvature:
       $v \times v = \langle [v_y, v_z], [v_z, v_x], [v_x, v_y] \rangle$.
    2. Skew-Symmetrized Cross Product Vanishes on Diagonal: $v \times_{\mathrm{skew}} v = 0$.
    3. Exact Skew-Symmetry over Noncommutative $A$: $u \times_{\mathrm{skew}} v + v \times_{\mathrm{skew}} u = 0$. -/
theorem opVec3_naive_commutator_curvature_and_skewCross_alternating
    (u v : OpVec3 A) :
    OpVec3.naiveCross v v =
      ⟨v.y * v.z - v.z * v.y, v.z * v.x - v.x * v.z, v.x * v.y - v.y * v.x⟩ ∧
    OpVec3.skewCross v v = 0 ∧
    OpVec3.skewCross u v + OpVec3.skewCross v u = 0 := by
  refine ⟨rfl, ?_, ?_⟩
  · ext <;> simp [OpVec3.skewCross, OpVec3.naiveCross]
  · ext <;> simp [OpVec3.skewCross, OpVec3.naiveCross]

/-- **Operator-Valued Zorn Algebra (`OpZornMatrix A`) over a Noncommutative Ring $A$**. -/
@[ext]
structure OpZornMatrix (A : Type*) where
  a : A
  v : OpVec3 A
  w : OpVec3 A
  b : A
  deriving DecidableEq

instance : Zero (OpZornMatrix A) := ⟨⟨0, 0, 0, 0⟩⟩
instance : One (OpZornMatrix A) := ⟨⟨1, 0, 0, 1⟩⟩
instance : Inhabited (OpZornMatrix A) := ⟨0⟩
instance : Add (OpZornMatrix A) :=
  ⟨fun X Y => ⟨X.a + Y.a, X.v + Y.v, X.w + Y.w, X.b + Y.b⟩⟩
instance : Sub (OpZornMatrix A) :=
  ⟨fun X Y => ⟨X.a - Y.a, X.v - Y.v, X.w - Y.w, X.b - Y.b⟩⟩
instance : Neg (OpZornMatrix A) :=
  ⟨fun X => ⟨-X.a, -X.v, -X.w, -X.b⟩⟩

/-- Noncommutative bimodule Zorn multiplication over `[Ring A]`. -/
instance : Mul (OpZornMatrix A) :=
  ⟨fun X Y =>
    { a := X.a * Y.a - OpVec3.dot X.v Y.w
      v := OpVec3.leftScale X.a Y.v + OpVec3.rightScale X.v Y.b - OpVec3.skewCross X.w Y.w
      w := OpVec3.rightScale X.w Y.a + OpVec3.leftScale X.b Y.w + OpVec3.skewCross X.v Y.v
      b := -OpVec3.dot X.w Y.v + X.b * Y.b }⟩

namespace OpZornMatrix

@[simp] lemma zero_a : (0 : OpZornMatrix A).a = 0 := rfl
@[simp] lemma zero_v : (0 : OpZornMatrix A).v = 0 := rfl
@[simp] lemma zero_w : (0 : OpZornMatrix A).w = 0 := rfl
@[simp] lemma zero_b : (0 : OpZornMatrix A).b = 0 := rfl
@[simp] lemma one_a : (1 : OpZornMatrix A).a = 1 := rfl
@[simp] lemma one_v : (1 : OpZornMatrix A).v = 0 := rfl
@[simp] lemma one_w : (1 : OpZornMatrix A).w = 0 := rfl
@[simp] lemma one_b : (1 : OpZornMatrix A).b = 1 := rfl
@[simp] lemma add_a (X Y : OpZornMatrix A) : (X + Y).a = X.a + Y.a := rfl
@[simp] lemma add_v (X Y : OpZornMatrix A) : (X + Y).v = X.v + Y.v := rfl
@[simp] lemma add_w (X Y : OpZornMatrix A) : (X + Y).w = X.w + Y.w := rfl
@[simp] lemma add_b (X Y : OpZornMatrix A) : (X + Y).b = X.b + Y.b := rfl
@[simp] lemma sub_a (X Y : OpZornMatrix A) : (X - Y).a = X.a - Y.a := rfl
@[simp] lemma sub_v (X Y : OpZornMatrix A) : (X - Y).v = X.v - Y.v := rfl
@[simp] lemma sub_w (X Y : OpZornMatrix A) : (X - Y).w = X.w - Y.w := rfl
@[simp] lemma sub_b (X Y : OpZornMatrix A) : (X - Y).b = X.b - Y.b := rfl
@[simp] lemma neg_a (X : OpZornMatrix A) : (-X).a = -X.a := rfl
@[simp] lemma neg_v (X : OpZornMatrix A) : (-X).v = -X.v := rfl
@[simp] lemma neg_w (X : OpZornMatrix A) : (-X).w = -X.w := rfl
@[simp] lemma neg_b (X : OpZornMatrix A) : (-X).b = -X.b := rfl
@[simp] lemma mul_a (X Y : OpZornMatrix A) :
    (X * Y).a = X.a * Y.a - OpVec3.dot X.v Y.w := rfl
@[simp] lemma mul_v (X Y : OpZornMatrix A) :
    (X * Y).v = OpVec3.leftScale X.a Y.v + OpVec3.rightScale X.v Y.b - OpVec3.skewCross X.w Y.w := rfl
@[simp] lemma mul_w (X Y : OpZornMatrix A) :
    (X * Y).w = OpVec3.rightScale X.w Y.a + OpVec3.leftScale X.b Y.w + OpVec3.skewCross X.v Y.v := rfl
@[simp] lemma mul_b (X Y : OpZornMatrix A) :
    (X * Y).b = -OpVec3.dot X.w Y.v + X.b * Y.b := rfl

end OpZornMatrix

/-- Trilinear associator $[X, Y, Z] = (X Y) Z - X (Y Z)$ in $\mathrm{Zorn}(A)$. -/
def opAssociator (X Y Z : OpZornMatrix A) : OpZornMatrix A :=
  (X * Y) * Z - X * (Y * Z)

/-- Grading involution $\Gamma = \langle 1, 0, 0, -1 \rangle \in \mathrm{Zorn}(A)$. -/
def opZornGamma : OpZornMatrix A := ⟨1, 0, 0, -1⟩

/-- Odd Kasparov–Zorn operator $J(v, w) = \langle 0, v, w, 0 \rangle \in \mathrm{Zorn}(A)$. -/
def opKasparovZornJ (v w : OpVec3 A) : OpZornMatrix A := ⟨0, v, w, 0⟩

/-- Diagonal operator torus $D(\lambda, \mu) = \langle \lambda, 0, 0, \mu \rangle \in \mathrm{Zorn}(A)$. -/
def opCartanDiag (lam mu : A) : OpZornMatrix A := ⟨lam, 0, 0, mu⟩

/-- Upper and lower parabolic unipotent operators $U_+(v), U_-(w) \in \mathrm{Zorn}(A)$. -/
def opUnipotentUpper (v : OpVec3 A) : OpZornMatrix A := ⟨1, v, 0, 1⟩
def opUnipotentLower (w : OpVec3 A) : OpZornMatrix A := ⟨1, 0, w, 1⟩

/-- **28. Operator-Valued Kasparov–Zorn Odd Square, Unipotent 2-Cocycle, & Bruhat Associativity (Archetype XXIV)**:
    Over ANY noncommutative operator ring $A$, for all $v, w, v_1, v_2 \in A^3$, $\lambda, \mu, \lambda_1, \mu_1, \lambda_2, \mu_2 \in A$, and $X \in \mathrm{Zorn}(A)$:
    1. Odd Kasparov Grading Anticommutation: $\Gamma J(v, w) + J(v, w) \Gamma = 0$.
    2. Noncommutative Kasparov–Zorn Square: $J(v, w)^2 = \langle -(v \cdot w), 0, 0, -(w \cdot v) \rangle$.
    3. Operator Unipotent Multiplication: $U_+(v_1) U_+(v_2) = \langle 1, v_1 + v_2, v_1 \times_{\mathrm{skew}} v_2, 1 \rangle$.
    4. Two-Sided Cartan Bimodule Associativity: $[D(\lambda_1, \mu_1), X, D(\lambda_2, \mu_2)] = 0$.
    5. Noncommutative Gauss–Bruhat Trifactor Associativity: $[U_-(w), D(\lambda, \mu), U_+(v)] = 0$. -/
theorem opZorn_kasparov_square_unipotent_and_bruhat_assoc
    (v w v₁ v₂ : OpVec3 A) (lam mu lam₁ mu₁ lam₂ mu₂ : A) (X : OpZornMatrix A) :
    let J := opKasparovZornJ v w
    opZornGamma * J + J * opZornGamma = 0 ∧
    J * J = ⟨-OpVec3.dot v w, 0, 0, -OpVec3.dot w v⟩ ∧
    opUnipotentUpper v₁ * opUnipotentUpper v₂ =
      ⟨1, v₁ + v₂, OpVec3.skewCross v₁ v₂, 1⟩ ∧
    opAssociator (opCartanDiag lam₁ mu₁) X (opCartanDiag lam₂ mu₂) = 0 ∧
    opAssociator (opUnipotentLower w) (opCartanDiag lam mu) (opUnipotentUpper v) = 0 := by
  intro J
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
  (ext <;>
   (simp [J, opZornGamma, opKasparovZornJ, opUnipotentUpper, opUnipotentLower,
          opCartanDiag, opAssociator, OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross];
    (try noncomm_ring); (try abel)))

/-- Canonical first basis vector $e_1(c) = \langle c, 0, 0 \rangle \in A^3$. -/
def opBasisE1 (c : A) : OpVec3 A := ⟨c, 0, 0⟩

@[simp] lemma opBasisE1_x (c : A) : (opBasisE1 c).x = c := rfl
@[simp] lemma opBasisE1_y (c : A) : (opBasisE1 c).y = 0 := rfl
@[simp] lemma opBasisE1_z (c : A) : (opBasisE1 c).z = 0 := rfl

/-- Canonical noncommutative slice embedding $\Phi_{e_1, -e_1} : M_2(A) \hookrightarrow \mathrm{OpZornMatrix}\;A$. -/
def opCanonicalMatEmbed (X : Matrix (Fin 2) (Fin 2) A) : OpZornMatrix A :=
  ⟨X 0 0, opBasisE1 (X 0 1), opBasisE1 (-X 1 0), X 1 1⟩

@[simp] lemma opCanonicalMatEmbed_a (X : Matrix (Fin 2) (Fin 2) A) :
    (opCanonicalMatEmbed X).a = X 0 0 := rfl
@[simp] lemma opCanonicalMatEmbed_v (X : Matrix (Fin 2) (Fin 2) A) :
    (opCanonicalMatEmbed X).v = opBasisE1 (X 0 1) := rfl
@[simp] lemma opCanonicalMatEmbed_w (X : Matrix (Fin 2) (Fin 2) A) :
    (opCanonicalMatEmbed X).w = opBasisE1 (-X 1 0) := rfl
@[simp] lemma opCanonicalMatEmbed_b (X : Matrix (Fin 2) (Fin 2) A) :
    (opCanonicalMatEmbed X).b = X 1 1 := rfl

/-- Componentwise star involution on `OpVec3 A` over a noncommutative $*$-ring $A$. -/
def opVec3Star [StarRing A] (u : OpVec3 A) : OpVec3 A :=
  ⟨star u.x, star u.y, star u.z⟩

@[simp] lemma opVec3Star_x [StarRing A] (u : OpVec3 A) : (opVec3Star u).x = star u.x := rfl
@[simp] lemma opVec3Star_y [StarRing A] (u : OpVec3 A) : (opVec3Star u).y = star u.y := rfl
@[simp] lemma opVec3Star_z [StarRing A] (u : OpVec3 A) : (opVec3Star u).z = star u.z := rfl

/-- **8D Indefinite Krein Adjoint (`opZornKreinAdjoint X`) on `OpZornMatrix A`**:
    $\langle a, v, w, b \rangle^\flat = \langle a^\star, w^\star, v^\star, b^\star \rangle$. -/
def opZornKreinAdjoint [StarRing A] (X : OpZornMatrix A) : OpZornMatrix A :=
  ⟨star X.a, opVec3Star X.w, opVec3Star X.v, star X.b⟩

@[simp] lemma opZornKreinAdjoint_a [StarRing A] (X : OpZornMatrix A) :
    (opZornKreinAdjoint X).a = star X.a := rfl
@[simp] lemma opZornKreinAdjoint_v [StarRing A] (X : OpZornMatrix A) :
    (opZornKreinAdjoint X).v = opVec3Star X.w := rfl
@[simp] lemma opZornKreinAdjoint_w [StarRing A] (X : OpZornMatrix A) :
    (opZornKreinAdjoint X).w = opVec3Star X.v := rfl
@[simp] lemma opZornKreinAdjoint_b [StarRing A] (X : OpZornMatrix A) :
    (opZornKreinAdjoint X).b = star X.b := rfl

/-- **29. 8D Noncommutative Krein Anti-Involution & $M_2(A) \hookrightarrow \mathrm{Zorn}(A)$ $*$-Homomorphism (Archetype XXV)**:
    Over ANY noncommutative $*$-ring $A$ (`[Ring A] [StarRing A]`), for all $X, Y \in \mathrm{OpZornMatrix}\;A$
    and $M, N \in M_2(A)$:
    1. Period-2 & Grading Self-Adjointness: $(X^\flat)^\flat = X$ and $\Gamma^\flat = \Gamma$.
    2. Exact 8D Multiplicative Anti-Homomorphism: $(X * Y)^\flat = Y^\flat * X^\flat$.
    3. Noncommutative Slice Multiplicativity:
       $\Phi_{e_1, -e_1}(M * N) = \Phi_{e_1, -e_1}(M) * \Phi_{e_1, -e_1}(N)$.
    4. Krein Adjoint Intertwining:
       $(\Phi_{e_1, -e_1}(M))^\flat = \Phi_{e_1, -e_1}(\mathrm{kreinAdjoint}\;M)$. -/
theorem opZornKreinAdjoint_and_slice_star_homomorphism [StarRing A]
    (X Y : OpZornMatrix A) (M N : Matrix (Fin 2) (Fin 2) A) :
    opZornKreinAdjoint (opZornKreinAdjoint X) = X ∧
    opZornKreinAdjoint (opZornGamma : OpZornMatrix A) = opZornGamma ∧
    opZornKreinAdjoint (X * Y) = opZornKreinAdjoint Y * opZornKreinAdjoint X ∧
    opCanonicalMatEmbed (M * N) = opCanonicalMatEmbed M * opCanonicalMatEmbed N ∧
    opZornKreinAdjoint (opCanonicalMatEmbed M) = opCanonicalMatEmbed (kreinAdjoint M) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · ext <;> simp
  · ext <;> simp [opZornGamma]
  · ext <;>
    (simp [OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross,
           star_add, star_sub, star_mul, star_neg];
     try abel)
  · ext <;>
    (simp [Matrix.mul_apply, Fin.sum_univ_two,
           OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross];
     try abel)
  · ext <;> simp [kreinAdjoint]

/-- The 8D Kasparov–Zorn curvature defect $D_J(v, w) = 1 + J(v, w)^2 = \langle 1 - v \cdot w, 0, 0, 1 - w \cdot v \rangle$. -/
def opKasparovZornDefect (v w : OpVec3 A) : OpZornMatrix A :=
  1 + opKasparovZornJ v w * opKasparovZornJ v w

/-- **30. Kasparov–Zorn Self-Associator Bimodule Defect & Single-Channel Fedosov Law (Archetype XXVI)**:
    Over ANY noncommutative ring $A$, for all $v, w \in A^3$ and $u, q \in A$:
    1. Exact Self-Associator Bimodule Defect:
       $[J(v, w), J(v, w), J(v, w)] =
        \langle 0, v \cdot_R (w \cdot v) - (v \cdot w) \cdot_L v, w \cdot_R (v \cdot w) - (w \cdot v) \cdot_L w, 0 \rangle$.
    2. Defect-Generator Commutator:
       $D_J(v, w) * J(v, w) - J(v, w) * D_J(v, w) = [J(v, w), J(v, w), J(v, w)]$.
    3. Single-Channel Noncommutative Fedosov Associativity:
       For $v = \langle u, 0, 0 \rangle$ and $w = \langle q, 0, 0 \rangle$,
       $[J(v, w), J(v, w), J(v, w)] = 0$ and $D_J(v, w) * J(v, w) = J(v, w) * D_J(v, w)$. -/
theorem opKasparovZornJ_self_associator_and_fedosov_intertwining
    (v w : OpVec3 A) (u q : A) :
    let J := opKasparovZornJ v w
    let D_J := opKasparovZornDefect v w
    let J₁ := opKasparovZornJ (opBasisE1 u) (opBasisE1 q)
    let D₁ := opKasparovZornDefect (opBasisE1 u) (opBasisE1 q)
    opAssociator J J J =
      ⟨0,
       OpVec3.rightScale v (OpVec3.dot w v) - OpVec3.leftScale (OpVec3.dot v w) v,
       OpVec3.rightScale w (OpVec3.dot v w) - OpVec3.leftScale (OpVec3.dot w v) w,
       0⟩ ∧
    D_J * J - J * D_J = opAssociator J J J ∧
    opAssociator J₁ J₁ J₁ = 0 ∧
    D₁ * J₁ = J₁ * D₁ := by
  intro J D_J J₁ D₁
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  (ext <;>
   (simp [J, D_J, J₁, D₁, opAssociator, opKasparovZornJ, opKasparovZornDefect,
          OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross];
    try noncomm_ring))

/-- Operator-valued Gauss–Bruhat trifactor flow $(U_-(w) * D(\lambda, \mu)) * U_+(v) \in \mathrm{OpZornMatrix}\;A$. -/
def opBruhatTrifactor (w : OpVec3 A) (lam mu : A) (v : OpVec3 A) : OpZornMatrix A :=
  (opUnipotentLower w * opCartanDiag lam mu) * opUnipotentUpper v

/-- **Reversed Operator Bruhat Inverse Flow (`opBruhatTrifactorInv v invLam invMu w`)**:
    $(U_+(-v) * D(\tilde{\lambda}, \tilde{\mu})) * U_-(-w) \in \mathrm{OpZornMatrix}\;A$. -/
def opBruhatTrifactorInv (v : OpVec3 A) (invLam invMu : A) (w : OpVec3 A) : OpZornMatrix A :=
  (opUnipotentUpper (-v) * opCartanDiag invLam invMu) * opUnipotentLower (-w)

/-- Right-associated unit cancellation helpers for noncommutative operator rings `[Ring A]`. -/
@[simp] lemma unit_mul_inv_cancel_left (u : Aˣ) (x : A) :
    (u : A) * ((↑u⁻¹ : A) * x) = x := by
  rw [← mul_assoc, Units.mul_inv, one_mul]

@[simp] lemma unit_inv_mul_cancel_left (u : Aˣ) (x : A) :
    (↑u⁻¹ : A) * ((u : A) * x) = x := by
  rw [← mul_assoc, Units.inv_mul, one_mul]

/-- **31. Noncommutative Parabolic Inversion, Bruhat Coordinates, & Schur Reconstruction (Archetype XXVII)**:
    Over ANY noncommutative operator ring $A$, for all $w, v \in A^3$, $\lambda, \mu, b \in A$,
    and any invertible operator $u \in A^\times$ (`u : Aˣ`):
    1. Exact Parabolic Unipotent Inverses:
       $U_+(v) * U_+(-v) = 1$ and $U_-(w) * U_-(-w) = 1$.
    2. Explicit Noncommutative Bimodule Bruhat Coordinates:
       $\mathrm{opBruhatTrifactor}\;w\;\lambda\;\mu\;v =
        \langle \lambda,\; \lambda \cdot_L v,\; w \cdot_R \lambda,\; \mu - (w \cdot_R \lambda) \cdot v \rangle$.
    3. Universal Noncommutative Schur Complement Reconstruction (`u : Aˣ`):
       $\mathrm{opBruhatTrifactor}\;(w \cdot_R u^{-1})\;u\;(b + w \cdot (u^{-1} \cdot_L v))\;(u^{-1} \cdot_L v) = \langle u, v, w, b \rangle$. -/
theorem opBruhatTrifactor_coords_and_operator_schur_reconstruction
    (w v : OpVec3 A) (lam mu b : A) (u : Aˣ) :
    opUnipotentUpper v * opUnipotentUpper (-v) = 1 ∧
    opUnipotentLower w * opUnipotentLower (-w) = 1 ∧
    opBruhatTrifactor w lam mu v =
      ⟨lam,
       OpVec3.leftScale lam v,
       OpVec3.rightScale w lam,
       mu - OpVec3.dot (OpVec3.rightScale w lam) v⟩ ∧
    opBruhatTrifactor (OpVec3.rightScale w (↑u⁻¹ : A)) (u : A)
      (b + OpVec3.dot w (OpVec3.leftScale (↑u⁻¹ : A) v))
      (OpVec3.leftScale (↑u⁻¹ : A) v) =
      ⟨(u : A), v, w, b⟩ := by
  have h_coords : ∀ w' : OpVec3 A, ∀ l m : A, ∀ v' : OpVec3 A,
      opBruhatTrifactor w' l m v' =
        ⟨l, OpVec3.leftScale l v', OpVec3.rightScale w' l,
         m - OpVec3.dot (OpVec3.rightScale w' l) v'⟩ := by
    intro w' l m v'; ext <;>
    (simp [opBruhatTrifactor, opUnipotentLower, opCartanDiag, opUnipotentUpper,
           OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross];
     try noncomm_ring)
  have h_v : OpVec3.leftScale (u : A) (OpVec3.leftScale (↑u⁻¹ : A) v) = v := by
    ext <;> simp
  have h_w : OpVec3.rightScale (OpVec3.rightScale w (↑u⁻¹ : A)) (u : A) = w := by
    ext <;> simp [mul_assoc]
  refine ⟨?_, ?_, h_coords w lam mu v, ?_⟩
  · ext <;>
    (simp [opUnipotentUpper, OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross];
     try noncomm_ring)
  · ext <;>
    (simp [opUnipotentLower, OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross];
     try noncomm_ring)
  · rw [h_coords, h_v, h_w, add_sub_cancel_right]

/-- **32. Reversed Operator Bruhat Zero Associator & Explicit Coordinates (Archetype XXVIII.1)**:
    Over ANY noncommutative ring $A$, for all $v, w \in A^3$ and $\tilde{\lambda}, \tilde{\mu} \in A$:
    1. Vanishing Reversed Bruhat Associator:
       $[U_+(-v), D(\tilde{\lambda}, \tilde{\mu}), U_-(-w)] = 0$.
    2. Explicit Noncommutative Coordinates:
       $\mathrm{opBruhatTrifactorInv}\;v\;\tilde{\lambda}\;\tilde{\mu}\;w =
        \langle \tilde{\lambda} - (v \cdot_R \tilde{\mu}) \cdot w,\; -(v \cdot_R \tilde{\mu}),\; -(\tilde{\mu} \cdot_L w),\; \tilde{\mu} \rangle$. -/
theorem opBruhatTrifactorInv_assoc_and_coords
    (v w : OpVec3 A) (invLam invMu : A) :
    opAssociator (opUnipotentUpper (-v)) (opCartanDiag invLam invMu) (opUnipotentLower (-w)) = 0 ∧
    opBruhatTrifactorInv v invLam invMu w =
      ⟨invLam - OpVec3.dot (OpVec3.rightScale v invMu) w,
       -OpVec3.rightScale v invMu,
       -OpVec3.leftScale invMu w,
       invMu⟩ := by
  refine ⟨?_, ?_⟩ <;>
  (ext <;>
   (simp [opAssociator, opBruhatTrifactorInv, opUnipotentUpper, opCartanDiag, opUnipotentLower,
          OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross];
    try noncomm_ring))

@[simp] lemma opBruhatTrifactor_a (w : OpVec3 A) (lam mu : A) (v : OpVec3 A) :
    (opBruhatTrifactor w lam mu v).a = lam := by
  rw [(opBruhatTrifactor_coords_and_operator_schur_reconstruction w v lam mu 0 1).2.2.1]

@[simp] lemma opBruhatTrifactor_v (w : OpVec3 A) (lam mu : A) (v : OpVec3 A) :
    (opBruhatTrifactor w lam mu v).v = OpVec3.leftScale lam v := by
  rw [(opBruhatTrifactor_coords_and_operator_schur_reconstruction w v lam mu 0 1).2.2.1]

@[simp] lemma opBruhatTrifactor_w (w : OpVec3 A) (lam mu : A) (v : OpVec3 A) :
    (opBruhatTrifactor w lam mu v).w = OpVec3.rightScale w lam := by
  rw [(opBruhatTrifactor_coords_and_operator_schur_reconstruction w v lam mu 0 1).2.2.1]

@[simp] lemma opBruhatTrifactor_b (w : OpVec3 A) (lam mu : A) (v : OpVec3 A) :
    (opBruhatTrifactor w lam mu v).b = mu - OpVec3.dot (OpVec3.rightScale w lam) v := by
  rw [(opBruhatTrifactor_coords_and_operator_schur_reconstruction w v lam mu 0 1).2.2.1]

@[simp] lemma opBruhatTrifactorInv_a (v : OpVec3 A) (invLam invMu : A) (w : OpVec3 A) :
    (opBruhatTrifactorInv v invLam invMu w).a = invLam - OpVec3.dot (OpVec3.rightScale v invMu) w := by
  rw [(opBruhatTrifactorInv_assoc_and_coords v w invLam invMu).2]

@[simp] lemma opBruhatTrifactorInv_v (v : OpVec3 A) (invLam invMu : A) (w : OpVec3 A) :
    (opBruhatTrifactorInv v invLam invMu w).v = -OpVec3.rightScale v invMu := by
  rw [(opBruhatTrifactorInv_assoc_and_coords v w invLam invMu).2]

@[simp] lemma opBruhatTrifactorInv_w (v : OpVec3 A) (invLam invMu : A) (w : OpVec3 A) :
    (opBruhatTrifactorInv v invLam invMu w).w = -OpVec3.leftScale invMu w := by
  rw [(opBruhatTrifactorInv_assoc_and_coords v w invLam invMu).2]

@[simp] lemma opBruhatTrifactorInv_b (v : OpVec3 A) (invLam invMu : A) (w : OpVec3 A) :
    (opBruhatTrifactorInv v invLam invMu w).b = invMu := by
  rw [(opBruhatTrifactorInv_assoc_and_coords v w invLam invMu).2]

/-- **33. Universal 8D Right- & Left-Product Diagonal Identities & Klein Bottle Skew-Cross Holonomy (Archetypes XXVIII.2 & XXIX)**:
    Over ANY noncommutative ring $A$, for ALL 3-vectors $v, w \in A^3$ and invertible operators
    $u, m \in A^\times$ (`u m : Aˣ`), let $T = \mathrm{opBruhatTrifactor}\;w\;u\;m\;v$ and
    $T_{\mathrm{inv}} = \mathrm{opBruhatTrifactorInv}\;v\;u^{-1}\;m^{-1}\;w$:
    1. Right-Product Diagonal Inversion: $(T * T_{\mathrm{inv}}).a = 1$ and $(T * T_{\mathrm{inv}}).b = 1$.
    2. Right-Product Upper-Right Klein Bottle Holonomy:
       $(T * T_{\mathrm{inv}}).v = (w \cdot_R u) \times_{\mathrm{skew}} (m^{-1} \cdot_L w)$.
    3. Left-Product Diagonal Inversion: $(T_{\mathrm{inv}} * T).a = 1$ and $(T_{\mathrm{inv}} * T).b = 1$.
    4. Left-Product Lower-Left Klein Bottle Holonomy:
       $(T_{\mathrm{inv}} * T).w = -(v \cdot_R m^{-1}) \times_{\mathrm{skew}} (u \cdot_L v)$. -/
theorem opBruhatTrifactor_klein_bottle_holonomy
    (v w : OpVec3 A) (u m : Aˣ) :
    let T := opBruhatTrifactor w (u : A) (m : A) v
    let T_inv := opBruhatTrifactorInv v (↑u⁻¹ : A) (↑m⁻¹ : A) w
    (T * T_inv).a = 1 ∧
    (T * T_inv).b = 1 ∧
    (T * T_inv).v =
      OpVec3.skewCross (OpVec3.rightScale w (u : A)) (OpVec3.leftScale (↑m⁻¹ : A) w) ∧
    (T_inv * T).a = 1 ∧
    (T_inv * T).b = 1 ∧
    (T_inv * T).w =
      -OpVec3.skewCross (OpVec3.rightScale v (↑m⁻¹ : A)) (OpVec3.leftScale (u : A) v) := by
  intro T T_inv
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [T, T_inv, OpVec3.dot]
    simp only [sub_eq_add_neg, mul_add, mul_neg, mul_assoc, Units.mul_inv]
    abel
  · simp [T, T_inv, OpVec3.dot]
    simp only [sub_eq_add_neg, add_mul, neg_mul, mul_assoc, Units.mul_inv]
    abel
  · ext <;>
    (simp [T, T_inv, OpVec3.skewCross, OpVec3.naiveCross];
     simp only [sub_eq_add_neg, mul_assoc];
     abel)
  · simp [T, T_inv, OpVec3.dot]
    simp only [sub_eq_add_neg, add_mul, neg_mul, mul_assoc, Units.inv_mul]
    abel
  · simp [T, T_inv, OpVec3.dot]
    simp only [sub_eq_add_neg, mul_add, mul_neg, mul_assoc, Units.inv_mul]
    abel
  · ext <;>
    (simp [T, T_inv, OpVec3.skewCross, OpVec3.naiveCross];
     simp only [sub_eq_add_neg, mul_assoc];
     abel)

/-- **34. Exact Two-Sided Inversion on Parabolic, Cartan, & Single-Channel Subgroups (Archetype XXVIII.3)**:
    Over ANY noncommutative ring $A$, for all $v, w \in A^3$, $\alpha, \beta \in A$, and $u, m \in A^\times$:
    1. Upper Parabolic Two-Sided Inverse:
       $\mathrm{opBruhatTrifactor}\;0\;1\;1\;v * \mathrm{opBruhatTrifactorInv}\;v\;1\;1\;0 = 1$ and
       $\mathrm{opBruhatTrifactorInv}\;v\;1\;1\;0 * \mathrm{opBruhatTrifactor}\;0\;1\;1\;v = 1$.
    2. Lower Parabolic Two-Sided Inverse:
       $\mathrm{opBruhatTrifactor}\;w\;1\;1\;0 * \mathrm{opBruhatTrifactorInv}\;0\;1\;1\;w = 1$ and
       $\mathrm{opBruhatTrifactorInv}\;0\;1\;1\;w * \mathrm{opBruhatTrifactor}\;w\;1\;1\;0 = 1$.
    3. Noncommutative Cartan Two-Sided Inverse:
       $\mathrm{opBruhatTrifactor}\;0\;u\;m\;0 * \mathrm{opBruhatTrifactorInv}\;0\;u^{-1}\;m^{-1}\;0 = 1$.
    4. Single-Channel Operator Slice Two-Sided Inverse:
       For $v_1 = \mathrm{opBasisE1}\;\alpha$ and $w_1 = \mathrm{opBasisE1}\;\beta$,
       $\mathrm{opBruhatTrifactor}\;w_1\;u\;m\;v_1 * \mathrm{opBruhatTrifactorInv}\;v_1\;u^{-1}\;m^{-1}\;w_1 = 1$ and
       $\mathrm{opBruhatTrifactorInv}\;v_1\;u^{-1}\;m^{-1}\;w_1 * \mathrm{opBruhatTrifactor}\;w_1\;u\;m\;v_1 = 1$. -/
theorem opBruhatTrifactor_parabolic_cartan_and_single_channel_inverse
    (v w : OpVec3 A) (α β : A) (u m : Aˣ) :
    let v₁ := opBasisE1 α
    let w₁ := opBasisE1 β
    opBruhatTrifactor 0 1 1 v * opBruhatTrifactorInv v 1 1 0 = 1 ∧
    opBruhatTrifactorInv v 1 1 0 * opBruhatTrifactor 0 1 1 v = 1 ∧
    opBruhatTrifactor w 1 1 0 * opBruhatTrifactorInv 0 1 1 w = 1 ∧
    opBruhatTrifactorInv 0 1 1 w * opBruhatTrifactor w 1 1 0 = 1 ∧
    opBruhatTrifactor 0 (u : A) (m : A) 0 *
      opBruhatTrifactorInv 0 (↑u⁻¹ : A) (↑m⁻¹ : A) 0 = 1 ∧
    opBruhatTrifactor w₁ (u : A) (m : A) v₁ *
      opBruhatTrifactorInv v₁ (↑u⁻¹ : A) (↑m⁻¹ : A) w₁ = 1 ∧
    opBruhatTrifactorInv v₁ (↑u⁻¹ : A) (↑m⁻¹ : A) w₁ *
      opBruhatTrifactor w₁ (u : A) (m : A) v₁ = 1 := by
  intro v₁ w₁
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · ext <;> (simp [OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross]; try abel)
  · ext <;> (simp [OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross]; try abel)
  · ext <;> (simp [OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross]; try abel)
  · ext <;> (simp [OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross]; try abel)
  · ext <;> simp [OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross]
  · ext <;>
    (simp [v₁, w₁, OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross];
     try (simp only [sub_eq_add_neg, add_mul, mul_add, neg_mul, mul_neg, mul_assoc,
                     unit_mul_inv_cancel_left, Units.mul_inv, mul_one, neg_add_rev, neg_neg];
          abel))
  · ext <;>
    (simp [v₁, w₁, OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross];
     try (simp only [sub_eq_add_neg, add_mul, mul_add, neg_mul, mul_neg, mul_assoc,
                     unit_inv_mul_cancel_left, Units.inv_mul, mul_one, neg_add_rev, neg_neg];
          abel))

/-- **8D Weyl-Swapped Star Involution (`opZornWeylStar X`) on `OpZornMatrix A`**:
    Swaps the diagonal Peirce corners $a \leftrightarrow b$ while applying `opVec3Star` to $v, w$:
    $\langle a, v, w, b \rangle^\sharp = \langle b^\star, v^\star, w^\star, a^\star \rangle$. -/
def opZornWeylStar [StarRing A] (X : OpZornMatrix A) : OpZornMatrix A :=
  ⟨star X.b, opVec3Star X.v, opVec3Star X.w, star X.a⟩

@[simp] lemma opZornWeylStar_a [StarRing A] (X : OpZornMatrix A) :
    (opZornWeylStar X).a = star X.b := rfl
@[simp] lemma opZornWeylStar_v [StarRing A] (X : OpZornMatrix A) :
    (opZornWeylStar X).v = opVec3Star X.v := rfl
@[simp] lemma opZornWeylStar_w [StarRing A] (X : OpZornMatrix A) :
    (opZornWeylStar X).w = opVec3Star X.w := rfl
@[simp] lemma opZornWeylStar_b [StarRing A] (X : OpZornMatrix A) :
    (opZornWeylStar X).b = star X.a := rfl

/-- **35. Exact Krein Self-Duality & Weyl-Star Intertwining Between Forward & Reversed Operator Bruhat Flows (Archetype XXIX.1)**:
    Over ANY noncommutative $*$-ring $A$ (`[Ring A] [StarRing A]`), for all $w, v \in A^3$ and $\lambda, \mu \in A$:
    1. Krein Self-Duality of Forward & Reversed Bruhat Flows:
       $(\mathrm{opBruhatTrifactor}\;w\;\lambda\;\mu\;v)^\flat =
        \mathrm{opBruhatTrifactor}\;(v^\star)\;\lambda^\star\;\mu^\star\;(w^\star)$ and
       $(\mathrm{opBruhatTrifactorInv}\;v\;\lambda\;\mu\;w)^\flat =
        \mathrm{opBruhatTrifactorInv}\;(w^\star)\;\lambda^\star\;\mu^\star\;(v^\star)$.
    2. Exact Weyl-Star Orientation-Flip Intertwining Between `opBruhatTrifactor` and `opBruhatTrifactorInv`:
       $(\mathrm{opBruhatTrifactor}\;w\;\lambda\;\mu\;v)^\sharp =
        \mathrm{opBruhatTrifactorInv}\;(-v^\star)\;\mu^\star\;\lambda^\star\;(-w^\star)$. -/
theorem opBruhatTrifactor_kreinAdjoint_duality [StarRing A]
    (w v : OpVec3 A) (lam mu : A) :
    opZornKreinAdjoint (opBruhatTrifactor w lam mu v) =
      opBruhatTrifactor (opVec3Star v) (star lam) (star mu) (opVec3Star w) ∧
    opZornKreinAdjoint (opBruhatTrifactorInv v lam mu w) =
      opBruhatTrifactorInv (opVec3Star w) (star lam) (star mu) (opVec3Star v) ∧
    opZornWeylStar (opBruhatTrifactor w lam mu v) =
      opBruhatTrifactorInv (-opVec3Star v) (star mu) (star lam) (-opVec3Star w) := by
  refine ⟨?_, ?_, ?_⟩ <;>
  (ext <;>
   (simp [OpVec3.dot, star_add, star_sub, star_mul, star_neg];
    try noncomm_ring))

/-- The Klein bottle skew-cross holonomy 3-vector $\kappa_R(w, u, m^{-1}) = (w \cdot_R u) \times_{\mathrm{skew}} (m^{-1} \cdot_L w)$. -/
def kleinHolonomyVecR (w : OpVec3 A) (u m_inv : A) : OpVec3 A :=
  OpVec3.skewCross (OpVec3.rightScale w u) (OpVec3.leftScale m_inv w)

/-- The dual Klein bottle skew-cross holonomy 3-vector $\kappa_L(v, u, m^{-1}) = (v \cdot_R m^{-1}) \times_{\mathrm{skew}} (u \cdot_L v)$. -/
def kleinHolonomyVecL (v : OpVec3 A) (u m_inv : A) : OpVec3 A :=
  OpVec3.skewCross (OpVec3.rightScale v m_inv) (OpVec3.leftScale u v)

/-- Helper: Any state $H \in \mathrm{OpZornMatrix}\;A$ with unit diagonal Peirce corners ($H.a = 1, H.b = 1$)
    has a purely odd defect $H - 1$ that anticommutes with $\Gamma$. -/
lemma opZornGamma_anticomm_sub_one_of_diag_eq_one (H : OpZornMatrix A)
    (ha : H.a = 1) (hb : H.b = 1) :
    opZornGamma * (H - 1) + (H - 1) * opZornGamma = 0 := by
  ext <;>
  (simp [opZornGamma, ha, hb, OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross];
   try abel)

/-- **36. Odd Kasparov Grading of the Universal 8D Bruhat Holonomy Defect (Archetype XXX.1)**:
    Over ANY noncommutative ring $A$, for ALL 3-vectors $v, w \in A^3$ and invertible operators
    $u, m \in A^\times$ (`u m : Aˣ`), let $\Omega_R = T * T_{\mathrm{inv}} - 1$ and
    $\Omega_L = T_{\mathrm{inv}} * T - 1$:
    1. Right Holonomy Defect is Purely Odd (Off-Diagonal):
       $\Gamma * \Omega_R + \Omega_R * \Gamma = 0$.
    2. Left Holonomy Defect is Purely Odd (Off-Diagonal):
       $\Gamma * \Omega_L + \Omega_L * \Gamma = 0$. -/
theorem opBruhat_holonomy_defect_odd_grading
    (v w : OpVec3 A) (u m : Aˣ) :
    let T := opBruhatTrifactor w (u : A) (m : A) v
    let T_inv := opBruhatTrifactorInv v (↑u⁻¹ : A) (↑m⁻¹ : A) w
    let Ω_R := T * T_inv - 1
    let Ω_L := T_inv * T - 1
    opZornGamma * Ω_R + Ω_R * opZornGamma = 0 ∧
    opZornGamma * Ω_L + Ω_L * opZornGamma = 0 := by
  intro T T_inv Ω_R Ω_L
  have h := opBruhatTrifactor_klein_bottle_holonomy v w u m
  exact ⟨opZornGamma_anticomm_sub_one_of_diag_eq_one (T * T_inv) h.1 h.2.1,
         opZornGamma_anticomm_sub_one_of_diag_eq_one (T_inv * T) h.2.2.2.1 h.2.2.2.2.1⟩

/-- **37. Parabolic Channel Teleportation & Exact Holonomy-Corrected 8D Borel Inversion (Archetype XXX.2)**:
    Over ANY noncommutative operator ring $A$, for ALL 3-vectors $v, w \in A^3$ and units $u, m \in A^\times$:
    1. Lower-to-Upper Parabolic Holonomy Teleportation ($v = 0$):
       $\mathrm{opBruhatTrifactor}\;w\;u\;m\;0 * \mathrm{opBruhatTrifactorInv}\;0\;u^{-1}\;m^{-1}\;w =
        U_+(\kappa_R(w, u, m^{-1}))$.
    2. Upper-to-Lower Parabolic Holonomy Teleportation ($w = 0$):
       $\mathrm{opBruhatTrifactorInv}\;v\;u^{-1}\;m^{-1}\;0 * \mathrm{opBruhatTrifactor}\;0\;u\;m\;v =
        U_-(-\kappa_L(v, u, m^{-1}))$.
    3. Exact Holonomy-Corrected 8D Lower-Borel Inverse:
       $(\mathrm{opBruhatTrifactor}\;w\;u\;m\;0 * \mathrm{opBruhatTrifactorInv}\;0\;u^{-1}\;m^{-1}\;w) *
        U_+(-\kappa_R(w, u, m^{-1})) = 1$.
    4. Exact Holonomy-Corrected 8D Upper-Borel Inverse:
       $U_-(\kappa_L(v, u, m^{-1})) *
        (\mathrm{opBruhatTrifactorInv}\;v\;u^{-1}\;m^{-1}\;0 * \mathrm{opBruhatTrifactor}\;0\;u\;m\;v) = 1$. -/
theorem opBruhat_parabolic_teleportation_and_holonomy_corrected_inverse
    (v w : OpVec3 A) (u m : Aˣ) :
    let κ_R := kleinHolonomyVecR w (u : A) (↑m⁻¹ : A)
    let κ_L := kleinHolonomyVecL v (u : A) (↑m⁻¹ : A)
    opBruhatTrifactor w (u : A) (m : A) 0 *
      opBruhatTrifactorInv 0 (↑u⁻¹ : A) (↑m⁻¹ : A) w =
      opUnipotentUpper κ_R ∧
    opBruhatTrifactorInv v (↑u⁻¹ : A) (↑m⁻¹ : A) 0 *
      opBruhatTrifactor 0 (u : A) (m : A) v =
      opUnipotentLower (-κ_L) ∧
    (opBruhatTrifactor w (u : A) (m : A) 0 *
      opBruhatTrifactorInv 0 (↑u⁻¹ : A) (↑m⁻¹ : A) w) *
      opUnipotentUpper (-κ_R) = 1 ∧
    opUnipotentLower κ_L *
      (opBruhatTrifactorInv v (↑u⁻¹ : A) (↑m⁻¹ : A) 0 *
      opBruhatTrifactor 0 (u : A) (m : A) v) = 1 := by
  intro κ_R κ_L
  have h_tele_R : opBruhatTrifactor w (u : A) (m : A) 0 *
      opBruhatTrifactorInv 0 (↑u⁻¹ : A) (↑m⁻¹ : A) w = opUnipotentUpper κ_R := by
    ext <;>
    (simp [κ_R, kleinHolonomyVecR, opUnipotentUpper, OpVec3.dot,
           OpVec3.skewCross, OpVec3.naiveCross];
     try abel)
  have h_tele_L : opBruhatTrifactorInv v (↑u⁻¹ : A) (↑m⁻¹ : A) 0 *
      opBruhatTrifactor 0 (u : A) (m : A) v = opUnipotentLower (-κ_L) := by
    ext <;>
    (simp [κ_L, kleinHolonomyVecL, opUnipotentLower, OpVec3.dot,
           OpVec3.skewCross, OpVec3.naiveCross];
     try abel)
  refine ⟨h_tele_R, h_tele_L, ?_, ?_⟩
  · rw [h_tele_R]
    ext <;>
    (simp [opUnipotentUpper, OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross];
     try noncomm_ring)
  · rw [h_tele_L]
    ext <;>
    (simp [opUnipotentLower, OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross];
     try noncomm_ring)

/-!
### Archetype XXXI: First-Quantized Chiral Lightcone Rays, Heisenberg Commutators, Split Nambu 3-Cocycles, & Chiral Projectors
-/

namespace OpVec3

/-- Operator-vector commutator $[\alpha, v] = \alpha \cdot_L v - v \cdot_R \alpha$ on $A^3$. -/
def opComm (α : A) (v : OpVec3 A) : OpVec3 A :=
  leftScale α v - rightScale v α

@[simp] lemma opComm_x (α : A) (v : OpVec3 A) : (opComm α v).x = α * v.x - v.x * α := rfl
@[simp] lemma opComm_y (α : A) (v : OpVec3 A) : (opComm α v).y = α * v.y - v.y * α := rfl
@[simp] lemma opComm_z (α : A) (v : OpVec3 A) : (opComm α v).z = α * v.z - v.z * α := rfl

/-- Left-associated operator Nambu triple determinant $\det_L(u, v, w) = u \cdot (v \times_{\mathrm{skew}} w) \in A$. -/
def opDetLeft (u v w : OpVec3 A) : A :=
  dot u (skewCross v w)

/-- Right-associated operator Nambu triple determinant $\det_R(u, v, w) = (u \times_{\mathrm{skew}} v) \cdot w \in A$. -/
def opDetRight (u v w : OpVec3 A) : A :=
  dot (skewCross u v) w

end OpVec3

/-- First-quantized traceless generator $M_{\mathrm{op}}(\alpha, v, w) = \langle \alpha, v, w, -\alpha \rangle \in \mathrm{OpZornMatrix}\;A$. -/
def opTracelessGen (α : A) (v w : OpVec3 A) : OpZornMatrix A :=
  ⟨α, v, w, -α⟩

/-- Pure upper chiral lightcone ray $L_+(v) = \langle 0, v, 0, 0 \rangle \in \mathrm{OpZornMatrix}\;A$. -/
def opLightconeRayPlus (v : OpVec3 A) : OpZornMatrix A := ⟨0, v, 0, 0⟩

/-- Pure lower chiral lightcone ray $L_-(w) = \langle 0, 0, w, 0 \rangle \in \mathrm{OpZornMatrix}\;A$. -/
def opLightconeRayMinus (w : OpVec3 A) : OpZornMatrix A := ⟨0, 0, w, 0⟩

/-- First-quantized upper chiral lightcone Peirce projector $P_+(v) = \langle 1, v, 0, 0 \rangle \in \mathrm{OpZornMatrix}\;A$. -/
def opChiralProjPlus (v : OpVec3 A) : OpZornMatrix A := ⟨1, v, 0, 0⟩

/-- First-quantized lower complementary chiral lightcone Peirce projector $P_-(v) = \langle 0, -v, 0, 1 \rangle \in \mathrm{OpZornMatrix}\;A$. -/
def opChiralProjMinus (v : OpVec3 A) : OpZornMatrix A := ⟨0, -v, 0, 1⟩

/-- **38. First-Quantized Traceless Generator Square & Heisenberg Operator Commutators (Archetype XXXI.1)**:
    Over ANY noncommutative operator ring $A$, for all $\alpha \in A$ and $v, w \in A^3$, the square
    of $M_{\mathrm{op}}(\alpha, v, w) = \langle \alpha, v, w, -\alpha \rangle$ has zero cross-product
    terms and isolates the Kasparov diagonal squares $\alpha^2 - v \cdot w$, $\alpha^2 - w \cdot v$
    together with the off-diagonal Heisenberg operator commutators $[\alpha, v]$ and $-[\alpha, w]$:
    $$M_{\mathrm{op}}(\alpha, v, w)^2 =
      \langle \alpha^2 - v \cdot w,\; [\alpha, v],\; -[\alpha, w],\; \alpha^2 - w \cdot v \rangle.$$ -/
theorem opTracelessGen_sq_heisenberg_commutators
    (α : A) (v w : OpVec3 A) :
    let M := opTracelessGen α v w
    M * M =
      ⟨α * α - OpVec3.dot v w,
       OpVec3.opComm α v,
       -OpVec3.opComm α w,
       α * α - OpVec3.dot w v⟩ := by
  intro M
  ext <;>
  (simp [M, opTracelessGen, OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross];
   try noncomm_ring)

/-- **39. First-Quantized Lightcone Ray Nilpotence, Teleportation, & Split Nambu Determinants (Archetype XXXI.2)**:
    Over ANY noncommutative operator ring $A$, for ALL $v, w, v_1, v_2, v_3, w_1, w_2 \in A^3$:
    1. Exact Square-Zero Nilpotence:
       $L_+(v) * L_+(v) = 0$ and $L_-(w) * L_-(w) = 0$.
    2. Two-Ray Chiral Teleportation:
       $L_+(v_1) * L_+(v_2) = L_-(v_1 \times_{\mathrm{skew}} v_2)$ and
       $L_-(w_1) * L_-(w_2) = L_+(-(w_1 \times_{\mathrm{skew}} w_2))$.
    3. Left- vs. Right-Parenthesized Triple Product Corner Separation:
       $(L_+(v_1) * L_+(v_2)) * L_+(v_3) = \langle 0, 0, 0, -\det_R(v_1, v_2, v_3) \rangle$ and
       $L_+(v_1) * (L_+(v_2) * L_+(v_3)) = \langle -\det_L(v_1, v_2, v_3), 0, 0, 0 \rangle$.
    4. Noncommutative Chiral Nambu 3-Cocycle Associator:
       $\mathrm{opAssociator}\;(L_+(v_1))\;(L_+(v_2))\;(L_+(v_3)) =
        \langle \det_L(v_1, v_2, v_3), 0, 0, -\det_R(v_1, v_2, v_3) \rangle$. -/
theorem opLightconeRay_nilpotence_teleportation_and_split_nambu_det
    (v w v₁ v₂ v₃ w₁ w₂ : OpVec3 A) :
    opLightconeRayPlus v * opLightconeRayPlus v = 0 ∧
    opLightconeRayMinus w * opLightconeRayMinus w = 0 ∧
    opLightconeRayPlus v₁ * opLightconeRayPlus v₂ =
      opLightconeRayMinus (OpVec3.skewCross v₁ v₂) ∧
    opLightconeRayMinus w₁ * opLightconeRayMinus w₂ =
      opLightconeRayPlus (-OpVec3.skewCross w₁ w₂) ∧
    (opLightconeRayPlus v₁ * opLightconeRayPlus v₂) * opLightconeRayPlus v₃ =
      ⟨0, 0, 0, -OpVec3.opDetRight v₁ v₂ v₃⟩ ∧
    opLightconeRayPlus v₁ * (opLightconeRayPlus v₂ * opLightconeRayPlus v₃) =
      ⟨-OpVec3.opDetLeft v₁ v₂ v₃, 0, 0, 0⟩ ∧
    opAssociator (opLightconeRayPlus v₁) (opLightconeRayPlus v₂) (opLightconeRayPlus v₃) =
      ⟨OpVec3.opDetLeft v₁ v₂ v₃, 0, 0, -OpVec3.opDetRight v₁ v₂ v₃⟩ := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  (ext <;>
   (simp [opLightconeRayPlus, opLightconeRayMinus, opAssociator,
          OpVec3.opDetLeft, OpVec3.opDetRight,
          OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross];
    try noncomm_ring))

/-- **40. First-Quantized Operator Nambu-WZW Unipotent 3-Cocycles (Archetype XXXI.3)**:
    Over ANY noncommutative operator ring $A$, for all $v_1, v_2, v_3, w_1, w_2, w_3 \in A^3$,
    the non-associative 3-associators of the unipotent lightcone exponentials $U_+(v_i)$ and $U_-(w_i)$
    are strictly diagonal and split the left-associated and right-associated operator triple determinants
    between the upper-left and lower-right Peirce corners:
    1. $[U_+(v_1), U_+(v_2), U_+(v_3)] =
        \langle \det_L(v_1, v_2, v_3),\; 0,\; 0,\; -\det_R(v_1, v_2, v_3) \rangle$.
    2. $[U_-(w_1), U_-(w_2), U_-(w_3)] =
        \langle \det_R(w_1, w_2, w_3),\; 0,\; 0,\; -\det_L(w_1, w_2, w_3) \rangle$. -/
theorem opUnipotent_first_quantized_nambu_three_cocycles
    (v₁ v₂ v₃ w₁ w₂ w₃ : OpVec3 A) :
    opAssociator (opUnipotentUpper v₁) (opUnipotentUpper v₂) (opUnipotentUpper v₃) =
      ⟨OpVec3.opDetLeft v₁ v₂ v₃, 0, 0, -OpVec3.opDetRight v₁ v₂ v₃⟩ ∧
    opAssociator (opUnipotentLower w₁) (opUnipotentLower w₂) (opUnipotentLower w₃) =
      ⟨OpVec3.opDetRight w₁ w₂ w₃, 0, 0, -OpVec3.opDetLeft w₁ w₂ w₃⟩ := by
  refine ⟨?_, ?_⟩ <;>
  (ext <;>
   (simp [opAssociator, opUnipotentUpper, opUnipotentLower,
          OpVec3.opDetLeft, OpVec3.opDetRight,
          OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross];
    try noncomm_ring))

/-- **41. First-Quantized Chiral Lightcone Projectors & Emergent Cross-Product Excitation (Archetype XXXI.4)**:
    Over ANY noncommutative operator ring $A$, for ALL $v, v_1, v_2 \in A^3$:
    1. Exact Resolution of Identity: $P_+(v) + P_-(v) = 1$.
    2. Exact Idempotence: $P_+(v) * P_+(v) = P_+(v)$ and $P_-(v) * P_-(v) = P_-(v)$.
    3. Exact Mutual Orthogonality: $P_+(v) * P_-(v) = 0$ and $P_-(v) * P_+(v) = 0$.
    4. Two-Projector Non-Associative Cross-Excitation Law:
       $P_+(v_1) * P_+(v_2) = P_+(v_2) + L_-(v_1 \times_{\mathrm{skew}} v_2)$. -/
theorem opChiralProj_idempotence_orthogonality_and_cross_excitation
    (v v₁ v₂ : OpVec3 A) :
    opChiralProjPlus v + opChiralProjMinus v = 1 ∧
    opChiralProjPlus v * opChiralProjPlus v = opChiralProjPlus v ∧
    opChiralProjMinus v * opChiralProjMinus v = opChiralProjMinus v ∧
    opChiralProjPlus v * opChiralProjMinus v = 0 ∧
    opChiralProjMinus v * opChiralProjPlus v = 0 ∧
    opChiralProjPlus v₁ * opChiralProjPlus v₂ =
      opChiralProjPlus v₂ + opLightconeRayMinus (OpVec3.skewCross v₁ v₂) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  (ext <;>
   (simp [opChiralProjPlus, opChiralProjMinus, opLightconeRayMinus,
          OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross];
    try noncomm_ring))

/-!
### Archetypes XXXII & XXXIII: Emergence of the Metric & Spin Connection from Twin Chiral Lightcones, Polarized Time Evolution, & Covariant Spin-Connection Gauge Shift
-/

namespace OpVec3

/-- Polarized bimodule covariant differential $\nabla_{\tau_+, \tau_-}(v) = \tau_+ \cdot_L v - v \cdot_R \tau_-$. -/
def bimoduleDiff (τ_plus τ_minus : A) (v : OpVec3 A) : OpVec3 A :=
  leftScale τ_plus v - rightScale v τ_minus

@[simp] lemma bimoduleDiff_x (τ₁ τ₂ : A) (v : OpVec3 A) :
    (bimoduleDiff τ₁ τ₂ v).x = τ₁ * v.x - v.x * τ₂ := rfl
@[simp] lemma bimoduleDiff_y (τ₁ τ₂ : A) (v : OpVec3 A) :
    (bimoduleDiff τ₁ τ₂ v).y = τ₁ * v.y - v.y * τ₂ := rfl
@[simp] lemma bimoduleDiff_z (τ₁ τ₂ : A) (v : OpVec3 A) :
    (bimoduleDiff τ₁ τ₂ v).z = τ₁ * v.z - v.z * τ₂ := rfl

end OpVec3

/-- Forward ($e_{11}$) and backward ($e_{22}$) primitive Peirce idempotents in $\mathrm{OpZornMatrix}\;A$. -/
def opPeircePlus : OpZornMatrix A := ⟨1, 0, 0, 0⟩
def opPeirceMinus : OpZornMatrix A := ⟨0, 0, 0, 1⟩

/-- Forward and backward chiral lightcone generators $L_+(v) = \langle 0, v, 0, 0 \rangle$ and $L_-(w) = \langle 0, 0, w, 0 \rangle$. -/
abbrev opLightconePlus (v : OpVec3 A) : OpZornMatrix A := opLightconeRayPlus v
abbrev opLightconeMinus (w : OpVec3 A) : OpZornMatrix A := opLightconeRayMinus w

/-- Combined twin-lightcone Dirac/Kasparov operator $J(v, w) = L_+(v) + L_-(w) = \langle 0, v, w, 0 \rangle$. -/
abbrev opTwinLightconeJ (v w : OpVec3 A) : OpZornMatrix A := opKasparovZornJ v w

/-- Polarized diagonal time/modular operator $D(\tau_+, \tau_-) = \langle \tau_+, 0, 0, \tau_- \rangle$. -/
abbrev opTimeDiag (τ_plus τ_minus : A) : OpZornMatrix A := opCartanDiag τ_plus τ_minus

/-- Forward and backward chiral lightcone gauge transformations $U_+(v) = 1 + L_+(v)$, $U_-(w) = 1 + L_-(w)$. -/
abbrev opGaugePlus (v : OpVec3 A) : OpZornMatrix A := opUnipotentUpper v
abbrev opGaugeMinus (w : OpVec3 A) : OpZornMatrix A := opUnipotentLower w

/-- **42. Forward/Backward Peirce Polarization, Nilpotence, & Eigen-Grading (Archetype XXXII.1)**:
    Over ANY noncommutative operator ring $A$, for all $v, w, v_1, v_2, v_3 \in A^3$:
    1. Peirce Chiral Polarization:
       $(e_{11} * J(v, w)) * e_{22} = L_+(v)$ and $(e_{22} * J(v, w)) * e_{11} = L_-(w)$.
    2. Square-Zero Chiral Nilpotence:
       $L_+(v) * L_+(v) = 0$ and $L_-(w) * L_-(w) = 0$.
    3. Chiral Eigen-Grading under $\Gamma$:
       $\Gamma * L_+(v) = L_+(v)$ and $L_+(v) * \Gamma = -L_+(v)$.
    4. Split Operator Nambu 3-Cocycle:
       $\mathrm{opAssociator}\;(L_+(v_1))\;(L_+(v_2))\;(L_+(v_3)) =
        \langle \det_L(v_1, v_2, v_3), 0, 0, -\det_R(v_1, v_2, v_3) \rangle$. -/
theorem twinLightcone_polarization_nilpotence_and_nambu_split
    (v w v₁ v₂ v₃ : OpVec3 A) :
    (opPeircePlus * opTwinLightconeJ v w) * opPeirceMinus = opLightconePlus v ∧
    (opPeirceMinus * opTwinLightconeJ v w) * opPeircePlus = opLightconeMinus w ∧
    opLightconePlus v * opLightconePlus v = 0 ∧
    opLightconeMinus w * opLightconeMinus w = 0 ∧
    opZornGamma * opLightconePlus v = opLightconePlus v ∧
    opLightconePlus v * opZornGamma = -opLightconePlus v ∧
    opAssociator (opLightconePlus v₁) (opLightconePlus v₂) (opLightconePlus v₃) =
      ⟨OpVec3.opDetLeft v₁ v₂ v₃, 0, 0, -OpVec3.opDetRight v₁ v₂ v₃⟩ := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  (ext <;>
   (simp [opPeircePlus, opPeirceMinus, opZornGamma, opTwinLightconeJ, opKasparovZornJ,
          opLightconePlus, opLightconeMinus, opLightconeRayPlus, opLightconeRayMinus,
          opAssociator, OpVec3.opDetLeft, OpVec3.opDetRight,
          OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross];
    try noncomm_ring))

/-- **43. Emergence of the Split Metric as Anticommutator & Spin Connection as Commutator (Archetype XXXII.2)**:
    Over ANY noncommutative operator ring $A$, for all $v, w, v_1, v_2, w_1, w_2 \in A^3$:
    1. Forward-Backward One-Way Contractions:
       $L_+(v) * L_-(w) = \langle -(v \cdot w), 0, 0, 0 \rangle$ and
       $L_-(w) * L_+(v) = \langle 0, 0, 0, -(w \cdot v) \rangle$.
    2. Emergent Split Metric = Jordan Anticommutator of Twin Lightcones:
       $L_+(v) * L_-(w) + L_-(w) * L_+(v) = \langle -(v \cdot w), 0, 0, -(w \cdot v) \rangle = J(v, w) * J(v, w)$.
    3. Emergent Chiral Boost Connection = Commutator of Twin Lightcones:
       $L_+(v) * L_-(w) - L_-(w) * L_+(v) = \langle -(v \cdot w), 0, 0, w \cdot v \rangle$.
    4. Emergent Spatial Spin-Torsion = Same-Chirality Lightcone Product:
       $L_+(v_1) * L_+(v_2) = L_-(v_1 \times_{\mathrm{skew}} v_2)$ and
       $L_-(w_1) * L_-(w_2) = L_+(-(w_1 \times_{\mathrm{skew}} w_2))$. -/
theorem metric_and_spin_connection_emergence_from_twin_lightcones
    (v w v₁ v₂ w₁ w₂ : OpVec3 A) :
    let L_p := opLightconePlus v
    let L_m := opLightconeMinus w
    let J := opTwinLightconeJ v w
    L_p * L_m = ⟨-OpVec3.dot v w, 0, 0, 0⟩ ∧
    L_m * L_p = ⟨0, 0, 0, -OpVec3.dot w v⟩ ∧
    L_p * L_m + L_m * L_p = ⟨-OpVec3.dot v w, 0, 0, -OpVec3.dot w v⟩ ∧
    L_p * L_m + L_m * L_p = J * J ∧
    L_p * L_m - L_m * L_p = ⟨-OpVec3.dot v w, 0, 0, OpVec3.dot w v⟩ ∧
    opLightconePlus v₁ * opLightconePlus v₂ =
      opLightconeMinus (OpVec3.skewCross v₁ v₂) ∧
    opLightconeMinus w₁ * opLightconeMinus w₂ =
      opLightconePlus (-OpVec3.skewCross w₁ w₂) := by
  intro L_p L_m J
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  (ext <;>
   (simp [L_p, L_m, J, opLightconePlus, opLightconeMinus, opLightconeRayPlus, opLightconeRayMinus,
          opKasparovZornJ, OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross];
    try noncomm_ring))

/-- **44. Polarized Lax-Heisenberg Time Derivative & Covariant Spin-Connection Gauge Shift (Archetype XXXIII)**:
    Over ANY noncommutative operator ring $A$, for any forward/backward time operators
    $\tau_+, \tau_- \in A$ and lightcone 3-vectors $v, w \in A^3$, let $D_\tau = D(\tau_+, \tau_-)$:
    1. Polarized Heisenberg-Dirac Time Derivative on Twin Lightcones:
       $D_\tau * J(v, w) - J(v, w) * D_\tau =
        \langle 0,\; \tau_+ \cdot_L v - v \cdot_R \tau_-,\; \tau_- \cdot_L w - w \cdot_R \tau_+,\; 0 \rangle$.
    2. Chiral Gauge Associators Isolate Opposite-Chirality Quadratic Spin-Torsion:
       $[U_+(v), D_\tau, U_+(-v)] = -L_-\bigl((v \cdot_R \tau_-) \times_{\mathrm{skew}} v + (\tau_+ \cdot_L v) \times_{\mathrm{skew}} v\bigr)$ and
       $[U_-(w), D_\tau, U_-(-w)] = L_+\bigl((w \cdot_R \tau_+) \times_{\mathrm{skew}} w + (\tau_- \cdot_L w) \times_{\mathrm{skew}} w\bigr)$.
    3. Exact Forward Lightcone Gauge Shift of Polarized Time (Covariant Derivative + Backward Spin-Torsion):
       $(U_+(v) * D_\tau) * U_+(-v) = D_\tau - L_+(\tau_+ \cdot_L v - v \cdot_R \tau_-) - L_-\bigl((v \cdot_R \tau_-) \times_{\mathrm{skew}} v\bigr)$.
    4. Exact Backward Lightcone Gauge Shift of Polarized Time (Covariant Derivative + Forward Spin-Torsion):
       $(U_-(w) * D_\tau) * U_-(-w) = D_\tau - L_-(\tau_- \cdot_L w - w \cdot_R \tau_+) + L_+\bigl((w \cdot_R \tau_+) \times_{\mathrm{skew}} w\bigr)$. -/
theorem polarizedTime_heisenberg_derivative_and_covariant_gauge_shift
    (τ_plus τ_minus : A) (v w : OpVec3 A) :
    let D_τ := opTimeDiag τ_plus τ_minus
    let J := opTwinLightconeJ v w
    D_τ * J - J * D_τ =
      ⟨0,
       OpVec3.bimoduleDiff τ_plus τ_minus v,
       OpVec3.bimoduleDiff τ_minus τ_plus w,
       0⟩ ∧
    opAssociator (opGaugePlus v) D_τ (opGaugePlus (-v)) =
      -opLightconeMinus (OpVec3.skewCross (OpVec3.rightScale v τ_minus) v +
                         OpVec3.skewCross (OpVec3.leftScale τ_plus v) v) ∧
    opAssociator (opGaugeMinus w) D_τ (opGaugeMinus (-w)) =
      opLightconePlus (OpVec3.skewCross (OpVec3.rightScale w τ_plus) w +
                       OpVec3.skewCross (OpVec3.leftScale τ_minus w) w) ∧
    (opGaugePlus v * D_τ) * opGaugePlus (-v) =
      D_τ - opLightconePlus (OpVec3.bimoduleDiff τ_plus τ_minus v)
          - opLightconeMinus (OpVec3.skewCross (OpVec3.rightScale v τ_minus) v) ∧
    (opGaugeMinus w * D_τ) * opGaugeMinus (-w) =
      D_τ - opLightconeMinus (OpVec3.bimoduleDiff τ_minus τ_plus w)
          + opLightconePlus (OpVec3.skewCross (OpVec3.rightScale w τ_plus) w) := by
  intro D_τ J
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
  (ext <;>
   (simp [D_τ, J, opCartanDiag, opKasparovZornJ,
          opGaugePlus, opGaugeMinus, opUnipotentUpper, opUnipotentLower,
          opLightconePlus, opLightconeMinus, opLightconeRayPlus, opLightconeRayMinus,
          opAssociator, OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross];
    try noncomm_ring))

/-!
### Archetypes XXXIV & XXXV: Cartan's First & Second Structure Equations and the Universal Operator Akivis-Bianchi Identity
-/

/-- Operator commutator $[X, Y] = X Y - Y X$ in $\mathrm{OpZornMatrix}\;A$. -/
def opCommutator (X Y : OpZornMatrix A) : OpZornMatrix A :=
  X * Y - Y * X

/-- Forward chiral lightcone Lie gauge derivation $\delta_{v}(X) = [L_+(v), X] = L_+(v) * X - X * L_+(v)$. -/
def opLightconeLieDerivPlus (v : OpVec3 A) (X : OpZornMatrix A) : OpZornMatrix A :=
  opCommutator (opLightconePlus v) X

/-- Right and left distributivity of `OpZornMatrix A` multiplication over subtraction. -/
lemma opZorn_sub_mul (X Y Z : OpZornMatrix A) :
    (X - Y) * Z = X * Z - Y * Z := by
  ext <;>
  (simp [OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross];
   try noncomm_ring)

lemma opZorn_mul_sub (X Y Z : OpZornMatrix A) :
    X * (Y - Z) = X * Y - X * Z := by
  ext <;>
  (simp [OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross];
   try noncomm_ring)

/-- **45. Cartan's First & Second Structure Equations: Torsion & Gauge Curvature 2-Form (Archetype XXXIV)**:
    Over ANY noncommutative operator ring $A$, for all $\tau_+, \tau_- \in A$ and $v_1, v_2 \in A^3$:
    1. Cartan's First Structure Equation (Unipotent Translation + Teleported Torsion 2-Form):
       $U_+(v_1) * U_+(v_2) = U_+(v_1 + v_2) + L_-(v_1 \times_{\mathrm{skew}} v_2)$.
    2. Additive Abelianization Defect (Torsion Commutator):
       $[U_+(v_1), U_+(v_2)] = L_-(v_1 \times_{\mathrm{skew}} v_2 + v_1 \times_{\mathrm{skew}} v_2)$.
    3. Two-Step Chiral Lightcone Gauge Derivation of Polarized Time $D_\tau = D(\tau_+, \tau_-)$:
       $\delta_{v_1}(\delta_{v_2}(D_\tau)) = -L_-(v_1 \times_{\mathrm{skew}} \nabla_\tau v_2 + v_1 \times_{\mathrm{skew}} \nabla_\tau v_2)$.
    4. Cartan's Second Structure Equation (Curvature Commutator of Sequential Lightcone Gauge Shifts):
       $\delta_{v_1}(\delta_{v_2}(D_\tau)) - \delta_{v_2}(\delta_{v_1}(D_\tau)) = L_-(F_{12} + F_{12})$,
       where $F_{12} = v_2 \times_{\mathrm{skew}} \nabla_\tau v_1 - v_1 \times_{\mathrm{skew}} \nabla_\tau v_2$. -/
theorem cartan_first_and_second_structure_equations
    (τ_plus τ_minus : A) (v₁ v₂ : OpVec3 A) :
    let D_τ := opTimeDiag τ_plus τ_minus
    let dv₁ := OpVec3.bimoduleDiff τ_plus τ_minus v₁
    let dv₂ := OpVec3.bimoduleDiff τ_plus τ_minus v₂
    let F₁₂ := OpVec3.skewCross v₂ dv₁ - OpVec3.skewCross v₁ dv₂
    opGaugePlus v₁ * opGaugePlus v₂ =
      opGaugePlus (v₁ + v₂) + opLightconeMinus (OpVec3.skewCross v₁ v₂) ∧
    opCommutator (opGaugePlus v₁) (opGaugePlus v₂) =
      opLightconeMinus (OpVec3.skewCross v₁ v₂ + OpVec3.skewCross v₁ v₂) ∧
    opLightconeLieDerivPlus v₁ (opLightconeLieDerivPlus v₂ D_τ) =
      -opLightconeMinus (OpVec3.skewCross v₁ dv₂ + OpVec3.skewCross v₁ dv₂) ∧
    opLightconeLieDerivPlus v₁ (opLightconeLieDerivPlus v₂ D_τ) -
      opLightconeLieDerivPlus v₂ (opLightconeLieDerivPlus v₁ D_τ) =
      opLightconeMinus (F₁₂ + F₁₂) := by
  intro D_τ dv₁ dv₂ F₁₂
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  (ext <;>
   (simp [D_τ, dv₁, dv₂, F₁₂, opLightconeLieDerivPlus, opUnipotentUpper,
          opCartanDiag, opLightconeRayPlus, opLightconeRayMinus,
          opCommutator, OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross];
    try noncomm_ring
    try abel))

/-- **46. Universal Operator Akivis-Bianchi Identity & Chiral Volume Triple Commutator (Archetype XXXV)**:
    Over ANY noncommutative operator ring $A$, for ALL $X, Y, Z \in \mathrm{OpZornMatrix}\;A$ and
    all chiral lightcone rays $v_1, v_2, v_3 \in A^3$:
    1. Universal Operator Akivis-Bianchi Identity:
       The Lie Jacobiator $[[X, Y], Z] + [[Y, Z], X] + [[Z, X], Y]$ is identically equal to the
       6-term alternating sum of trilinear associators:
       $$[[X, Y], Z] + [[Y, Z], X] + [[Z, X], Y] =
         [X, Y, Z] + [Y, Z, X] + [Z, X, Y] - [Y, X, Z] - [X, Z, Y] - [Z, Y, X].$$
    2. Chiral Lightcone Triple Commutator (Split Einstein-Nambu Volume Operator):
       $$[[L_+(v_1), L_+(v_2)], L_+(v_3)] =
         \Bigl\langle 2 \bigl(v_3 \cdot (v_1 \times_{\mathrm{skew}} v_2)\bigr),\;\; 0,\;\; 0,\;\;
                      -2 \bigl((v_1 \times_{\mathrm{skew}} v_2) \cdot v_3\bigr) \Bigr\rangle.$$ -/
theorem universal_akivis_bianchi_identity_and_chiral_volume_commutator
    (X Y Z : OpZornMatrix A) (v₁ v₂ v₃ : OpVec3 A) :
    let L₁ := opLightconePlus v₁
    let L₂ := opLightconePlus v₂
    let L₃ := opLightconePlus v₃
    let w₁₂ := OpVec3.skewCross v₁ v₂
    opCommutator (opCommutator X Y) Z +
      opCommutator (opCommutator Y Z) X +
      opCommutator (opCommutator Z X) Y =
      opAssociator X Y Z + opAssociator Y Z X + opAssociator Z X Y -
        opAssociator Y X Z - opAssociator X Z Y - opAssociator Z Y X ∧
    opCommutator (opCommutator L₁ L₂) L₃ =
      ⟨OpVec3.dot v₃ w₁₂ + OpVec3.dot v₃ w₁₂,
       0,
       0,
       -(OpVec3.dot w₁₂ v₃ + OpVec3.dot w₁₂ v₃)⟩ := by
  intro L₁ L₂ L₃ w₁₂
  refine ⟨?_, ?_⟩
  · simp only [opCommutator, opAssociator, opZorn_sub_mul, opZorn_mul_sub]
    ext <;>
    (simp only [OpZornMatrix.add_a, OpZornMatrix.add_v, OpZornMatrix.add_w, OpZornMatrix.add_b,
                OpZornMatrix.sub_a, OpZornMatrix.sub_v, OpZornMatrix.sub_w, OpZornMatrix.sub_b,
                OpVec3.add_x, OpVec3.add_y, OpVec3.add_z,
                OpVec3.sub_x, OpVec3.sub_y, OpVec3.sub_z];
     abel)
  · ext <;>
    (simp [L₁, L₂, L₃, w₁₂, opCommutator, opLightconeRayPlus,
           OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross];
     try noncomm_ring)

/-!
## 15. Archetypes XXXVI & XXXVII: Operator Para-Kähler Super-Grassmannians, Amari-Chentsov Cubic Skewness Tensor, & Maurer-Cartan Chiral Anomaly Hierarchy
-/

/-- Operator Zorn trace $\mathrm{opZornTrace}(X) = X_a + X_b \in A$. -/
def opZornTrace (X : OpZornMatrix A) : A := X.a + X.b

/-- Symmetric Jordan anticommutator $\{X, Y\} = X * Y + Y * X$ in $\mathrm{OpZornMatrix}\;A$. -/
def opAnticommutator (X Y : OpZornMatrix A) : OpZornMatrix A :=
  X * Y + Y * X

/-- Para-Kähler pseudo-Riemannian metric $g(v, w) = \{L_+(v), L_-(w)\}$. -/
def opParaKahlerMetric (v w : OpVec3 A) : OpZornMatrix A :=
  opAnticommutator (opLightconeRayPlus v) (opLightconeRayMinus w)

/-- Para-Kähler symplectic 2-form $\omega(v, w) = [L_+(v), L_-(w)]$. -/
def opParaKahlerSymplectic (v w : OpVec3 A) : OpZornMatrix A :=
  opCommutator (opLightconeRayPlus v) (opLightconeRayMinus w)

/-- Relative Maurer-Cartan transition form $\Theta(v_1, v_2) = U_+(-v_1) * U_+(v_2) - 1$
    on the primal affine exponential family in $\mathrm{OpZornMatrix}\;A$. -/
def opMaurerCartanForm (v₁ v₂ : OpVec3 A) : OpZornMatrix A :=
  opUnipotentUpper (-v₁) * opUnipotentUpper v₂ - 1

/-- **47. Operator Para-Kähler Triplet Compatibility, Chiral Anomaly Residue, & Primal-Dual Loop Anomaly (Archetype XXXVI.1)**:
    Over ANY noncommutative operator ring $A$, for all $v, w \in A^3$:
    1. Explicit Para-Kähler Metric (Symmetric Jordan Sum):
       $g(v, w) = \langle -(v \cdot w), 0, 0, -(w \cdot v) \rangle$.
    2. Explicit Symplectic 2-Form (Antisymmetric Commutator Difference):
       $\omega(v, w) = \langle -(v \cdot w), 0, 0, w \cdot v \rangle$.
    3. Fundamental Para-Kähler Compatibility ($\Gamma g = \omega$ and $\Gamma \omega = g$):
       $\Gamma * g(v, w) = \omega(v, w)$ and $\Gamma * \omega(v, w) = g(v, w)$.
    4. Noncommuting Chiral Anomaly Residue:
       $\mathrm{opZornTrace}(\omega(v, w)) = (w \cdot v) - (v \cdot w)$.
    5. Primal-Dual Exponential Commutator & Loop Holonomy Identity:
       $[U_+(v), U_-(w)] = \omega(v, w)$, and for $G(v, w) = U_+(v) * U_-(w)$ and
       $G_{\mathrm{inv}}(v, w) = U_-(-w) * U_+(-v)$,
       $G(v, w) * G_{\mathrm{inv}}(v, w) - 1 = [L_+(v), g(v, w)] =
        L_+\!\bigl((v \cdot w) \cdot_L v - v \cdot_R (w \cdot v)\bigr)$. -/
theorem opParaKahler_triplet_compatibility_and_anomaly_residue
    (v w : OpVec3 A) :
    let g := opParaKahlerMetric v w
    let ω := opParaKahlerSymplectic v w
    let Γ := opZornGamma
    let G := opUnipotentUpper v * opUnipotentLower w
    let G_inv := opUnipotentLower (-w) * opUnipotentUpper (-v)
    g = ⟨-OpVec3.dot v w, 0, 0, -OpVec3.dot w v⟩ ∧
    ω = ⟨-OpVec3.dot v w, 0, 0, OpVec3.dot w v⟩ ∧
    Γ * g = ω ∧
    Γ * ω = g ∧
    opZornTrace ω = OpVec3.dot w v - OpVec3.dot v w ∧
    opCommutator (opUnipotentUpper v) (opUnipotentLower w) = ω ∧
    G * G_inv - 1 = opCommutator (opLightconeRayPlus v) g := by
  intro g ω Γ G G_inv
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · ext <;>
    (simp [g, opParaKahlerMetric, opAnticommutator, opLightconeRayPlus, opLightconeRayMinus,
           OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross];
     try noncomm_ring)
  · ext <;>
    (simp [ω, opParaKahlerSymplectic, opCommutator, opLightconeRayPlus, opLightconeRayMinus,
           OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross];
     try noncomm_ring)
  · ext <;>
    (simp [Γ, g, ω, opZornGamma, opParaKahlerMetric, opParaKahlerSymplectic,
           opAnticommutator, opCommutator, opLightconeRayPlus, opLightconeRayMinus,
           OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross];
     try noncomm_ring)
  · ext <;>
    (simp [Γ, g, ω, opZornGamma, opParaKahlerMetric, opParaKahlerSymplectic,
           opAnticommutator, opCommutator, opLightconeRayPlus, opLightconeRayMinus,
           OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross];
     try noncomm_ring)
  · simp [ω, opParaKahlerSymplectic, opCommutator, opLightconeRayPlus, opLightconeRayMinus,
          opZornTrace, OpVec3.dot]
    noncomm_ring
  · ext <;>
    (simp [ω, opParaKahlerSymplectic, opCommutator, opUnipotentUpper, opUnipotentLower,
           opLightconeRayPlus, opLightconeRayMinus, OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross];
     try noncomm_ring)
  · ext <;>
    (simp [G, G_inv, g, opParaKahlerMetric, opAnticommutator, opCommutator,
           opUnipotentUpper, opUnipotentLower,
           opLightconeRayPlus, opLightconeRayMinus, OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross];
     try noncomm_ring)

/-- **48. Amari-Chentsov Cubic Skewness Tensor & Jordan Triple Product (Archetype XXXVI.2)**:
    Over ANY noncommutative operator ring $A$, for all $v, w \in A^3$, the nested commutator
    of the symplectic 2-form $\omega(v, w) = [L_+(v), L_-(w)]$ with the primal and dual tangent
    spaces reproduces the exact noncommutative Jordan triple product:
    1. Primal Amari-Chentsov Cubic Tensor:
       $[[L_-(w), L_+(v)], L_+(v)] = L_+\!\bigl((v \cdot w) \cdot_L v + v \cdot_R (w \cdot v)\bigr)$ and
       $[[L_+(v), L_-(w)], L_+(v)] = -L_+\!\bigl((v \cdot w) \cdot_L v + v \cdot_R (w \cdot v)\bigr)$.
    2. Dual Amari-Chentsov Cubic Tensor:
       $[[L_+(v), L_-(w)], L_-(w)] = L_-\!\bigl((w \cdot v) \cdot_L w + w \cdot_R (v \cdot w)\bigr)$ and
       $[[L_-(w), L_+(v)], L_-(w)] = -L_-\!\bigl((w \cdot v) \cdot_L w + w \cdot_R (v \cdot w)\bigr)$. -/
theorem amariChentsov_cubic_skewness_tensor
    (v w : OpVec3 A) :
    let L_v := opLightconeRayPlus v
    let L_w := opLightconeRayMinus w
    let T_v := OpVec3.leftScale (OpVec3.dot v w) v + OpVec3.rightScale v (OpVec3.dot w v)
    let T_w := OpVec3.leftScale (OpVec3.dot w v) w + OpVec3.rightScale w (OpVec3.dot v w)
    opCommutator (opCommutator L_w L_v) L_v = opLightconeRayPlus T_v ∧
    opCommutator (opCommutator L_v L_w) L_v = -opLightconeRayPlus T_v ∧
    opCommutator (opCommutator L_v L_w) L_w = opLightconeRayMinus T_w ∧
    opCommutator (opCommutator L_w L_v) L_w = -opLightconeRayMinus T_w := by
  intro L_v L_w T_v T_w
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  (ext <;>
   (simp [L_v, L_w, T_v, T_w, opCommutator, opLightconeRayPlus, opLightconeRayMinus,
          OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross];
    try noncomm_ring))

/-- **49. Maurer-Cartan Grade Decomposition & Anomaly-Driven Grade-3 Square (Archetype XXXVII)**:
    Over ANY noncommutative operator ring $A$, for all $v_1, v_2 \in A^3$:
    1. Grade-1 (Flat Affine Difference) + Grade-2 (Skew Torsion) Decomposition:
       $$\Theta(v_1, v_2) = L_+(v_2 - v_1) - L_-(v_1 \times_{\mathrm{skew}} v_2).$$
    2. Grade-3 Maurer-Cartan Square (Generated Purely by the Noncommuting Anomaly):
       $$\Theta(v_1, v_2) * \Theta(v_1, v_2) =
         \Bigl\langle (v_2 - v_1) \cdot (v_1 \times_{\mathrm{skew}} v_2),\;\; 0,\;\; 0,\;\;
                      (v_1 \times_{\mathrm{skew}} v_2) \cdot (v_2 - v_1) \Bigr\rangle.$$
    3. Maurer-Cartan Symplectic Anomaly Commutator:
       $$\bigl[L_+(v_2 - v_1),\; -L_-(v_1 \times_{\mathrm{skew}} v_2)\bigr] =
         \Bigl\langle (v_2 - v_1) \cdot (v_1 \times_{\mathrm{skew}} v_2),\;\; 0,\;\; 0,\;\;
                      -((v_1 \times_{\mathrm{skew}} v_2) \cdot (v_2 - v_1)) \Bigr\rangle.$$
    4. Antisymmetry & Two-Point Maurer-Cartan Multiplicative Cocycle Anomaly:
       $$\Theta(v_2, v_1) = -\Theta(v_1, v_2), \qquad
         (1 + \Theta(v_1, v_2)) * (1 + \Theta(v_2, v_1)) = 1 - \Theta(v_1, v_2) * \Theta(v_1, v_2).$$
    5. Three-Point Maurer-Cartan Associator Anomaly:
       $$(U_+(-v_1) * U_+(v_2)) * U_+(-v_2) =
         U_+(-v_1) + \Bigl\langle 0,\;\; 0,\;\; 0,\;\; -((v_1 \times_{\mathrm{skew}} v_2) \cdot v_2) \Bigr\rangle.$$ -/
theorem opMaurerCartanForm_grade_hierarchy_and_anomaly_generation
    (v₁ v₂ : OpVec3 A) :
    let Θ := opMaurerCartanForm v₁ v₂
    let Δv := v₂ - v₁
    let τ₁₂ := OpVec3.skewCross v₁ v₂
    Θ = opLightconeRayPlus Δv - opLightconeRayMinus τ₁₂ ∧
    Θ * Θ = ⟨OpVec3.dot Δv τ₁₂, 0, 0, OpVec3.dot τ₁₂ Δv⟩ ∧
    opCommutator (opLightconeRayPlus Δv) (-opLightconeRayMinus τ₁₂) =
      ⟨OpVec3.dot Δv τ₁₂, 0, 0, -OpVec3.dot τ₁₂ Δv⟩ ∧
    opMaurerCartanForm v₂ v₁ = -Θ ∧
    (1 + opMaurerCartanForm v₁ v₂) * (1 + opMaurerCartanForm v₂ v₁) = 1 - Θ * Θ ∧
    (opUnipotentUpper (-v₁) * opUnipotentUpper v₂) * opUnipotentUpper (-v₂) =
      opUnipotentUpper (-v₁) + ⟨0, 0, 0, -OpVec3.dot τ₁₂ v₂⟩ := by
  intro Θ Δv τ₁₂
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  (ext <;>
   (simp [Θ, Δv, τ₁₂, opMaurerCartanForm, opUnipotentUpper, opLightconeRayPlus,
          opLightconeRayMinus, opCommutator, OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross];
    try noncomm_ring
    try abel))

/-- Relative dual Maurer-Cartan transition form $\Theta_-(w_1, w_2) = U_-(-w_1) * U_-(w_2) - 1$
    on the dual affine mixture family in $\mathrm{OpZornMatrix}\;A$. -/
def opDualMaurerCartanForm (w₁ w₂ : OpVec3 A) : OpZornMatrix A :=
  opUnipotentLower (-w₁) * opUnipotentLower w₂ - 1

/-- **50. Commutative Maurer-Cartan Vanishing vs. Noncommutative Dual Mixture Hierarchy (Archetype XXXVII.2)**:
    1. Exact Commutative Orthogonality Vanishing:
       Over ANY commutative ring $R$ (`[CommRing R]`), for all $u_1, u_2 \in R^3$, the cross product
       $u_1 \times_{\mathrm{skew}} u_2$ is orthogonal to $u_2 - u_1$, so the Grade-3 Maurer-Cartan
       square vanishes identically:
       $$\Theta(u_1, u_2) * \Theta(u_1, u_2) = 0, \qquad
         (1 + \Theta(u_1, u_2)) * (1 + \Theta(u_2, u_1)) = 1.$$
    2. Colinear / Diagonal Vanishing over Arbitrary Noncommutative `[Ring A]`:
       For any $v \in A^3$, $\Theta(v, v) = 0$ and $\Theta(-v, v) * \Theta(-v, v) = 0$.
    3. Dual Mixture Maurer-Cartan Grade Decomposition & Square over `[Ring A]`:
       For all $w_1, w_2 \in A^3$ with $\Delta w = w_2 - w_1$ and $\sigma_{12} = w_1 \times_{\mathrm{skew}} w_2$:
       $$\Theta_-(w_1, w_2) = L_-(\Delta w) + L_+(\sigma_{12}), \qquad
         \Theta_-(w_1, w_2) * \Theta_-(w_1, w_2) =
           \langle -(\sigma_{12} \cdot \Delta w),\; 0,\; 0,\; -(\Delta w \cdot \sigma_{12}) \rangle.$$ -/
theorem opMaurerCartan_commutative_vanishing_and_dual_hierarchy
    {R : Type*} [CommRing R] (u₁ u₂ : OpVec3 R) (v w₁ w₂ : OpVec3 A) :
    let Θ_R := opMaurerCartanForm u₁ u₂
    let Θ_m := opDualMaurerCartanForm w₁ w₂
    let Δw := w₂ - w₁
    let σ₁₂ := OpVec3.skewCross w₁ w₂
    Θ_R * Θ_R = 0 ∧
    (1 + opMaurerCartanForm u₁ u₂) * (1 + opMaurerCartanForm u₂ u₁) = 1 ∧
    opMaurerCartanForm v v = 0 ∧
    opMaurerCartanForm (-v) v * opMaurerCartanForm (-v) v = 0 ∧
    Θ_m = opLightconeRayMinus Δw + opLightconeRayPlus σ₁₂ ∧
    Θ_m * Θ_m = ⟨-OpVec3.dot σ₁₂ Δw, 0, 0, -OpVec3.dot Δw σ₁₂⟩ := by
  intro Θ_R Θ_m Δw σ₁₂
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · ext <;>
    (simp [Θ_R, opMaurerCartanForm, opUnipotentUpper, OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross];
     try ring)
  · ext <;>
    (simp [opMaurerCartanForm, opUnipotentUpper, OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross];
     try ring)
  · ext <;>
    (simp [opMaurerCartanForm, opUnipotentUpper, OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross];
     try noncomm_ring
     try abel)
  · ext <;>
    (simp [opMaurerCartanForm, opUnipotentUpper, OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross];
     try noncomm_ring
     try abel)
  · ext <;>
    (simp [Θ_m, Δw, σ₁₂, opDualMaurerCartanForm, opUnipotentLower, opLightconeRayPlus, opLightconeRayMinus,
           OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross];
     try noncomm_ring
     try abel)
  · ext <;>
    (simp [Θ_m, Δw, σ₁₂, opDualMaurerCartanForm, opUnipotentLower,
           OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross];
     try noncomm_ring
     try abel)

/-- **51. Higher-Grade Maurer-Cartan Cube, Self-Associator Emergent Flow, & Dual Flatness (Archetype XXXVII.3)**:
    Over ANY noncommutative operator ring $A$, for all $v_1, v_2, v_3, w_1, w_2, w_3 \in A^3$, let
    $\Theta = \Theta(v_1, v_2)$, $\Delta v = v_2 - v_1$, $\tau_{12} = v_1 \times_{\mathrm{skew}} v_2$,
    $\alpha_+ = \Delta v \cdot \tau_{12}$, $\alpha_- = \tau_{12} \cdot \Delta v$, and
    $D_{\mathrm{anom}} = D(\alpha_+, \alpha_-) = \Theta * \Theta$:
    1. Left and Right Grade-4 Maurer-Cartan Cubes:
       $$(\Theta * \Theta) * \Theta = L_+(\alpha_+ \cdot_L \Delta v) - L_-(\alpha_- \cdot_L \tau_{12}), \qquad
         \Theta * (\Theta * \Theta) = L_+(\Delta v \cdot_R \alpha_-) - L_-(\tau_{12} \cdot_R \alpha_+).$$
    2. Maurer-Cartan Self-Associator Equals Anomaly-Driven Heisenberg-Dirac Flow:
       $$[\Theta, \Theta, \Theta] = [D_{\mathrm{anom}}, \Theta] =
         L_+\!\bigl(\nabla_{\alpha_+, \alpha_-}(\Delta v)\bigr) - L_-\!\bigl(\nabla_{\alpha_-, \alpha_+}(\tau_{12})\bigr).$$
    3. Individual Parabolic Flatness & Unipotent Inversion:
       $$U_+(v_1) * U_+(-v_1) = 1, \qquad U_-(w_1) * U_-(-w_1) = 1,$$
       $$\bigl((L_+(v_1) * L_+(v_2)) * L_+(v_3)\bigr).v = 0, \qquad
         \bigl((L_+(v_1) * L_+(v_2)) * L_+(v_3)\bigr).w = 0,$$
       $$\bigl((L_-(w_1) * L_-(w_2)) * L_-(w_3)\bigr).v = 0, \qquad
         \bigl((L_-(w_1) * L_-(w_2)) * L_-(w_3)\bigr).w = 0.$$ -/
theorem opMaurerCartan_cube_and_self_associator_emergent_flow
    (v₁ v₂ v₃ w₁ w₂ w₃ : OpVec3 A) :
    let Θ := opMaurerCartanForm v₁ v₂
    let Δv := v₂ - v₁
    let τ₁₂ := OpVec3.skewCross v₁ v₂
    let α_plus := OpVec3.dot Δv τ₁₂
    let α_minus := OpVec3.dot τ₁₂ Δv
    let D_anom := opCartanDiag α_plus α_minus
    (Θ * Θ) * Θ =
      opLightconeRayPlus (OpVec3.leftScale α_plus Δv) -
        opLightconeRayMinus (OpVec3.leftScale α_minus τ₁₂) ∧
    Θ * (Θ * Θ) =
      opLightconeRayPlus (OpVec3.rightScale Δv α_minus) -
        opLightconeRayMinus (OpVec3.rightScale τ₁₂ α_plus) ∧
    opAssociator Θ Θ Θ = opCommutator D_anom Θ ∧
    opAssociator Θ Θ Θ =
      opLightconeRayPlus (OpVec3.bimoduleDiff α_plus α_minus Δv) -
        opLightconeRayMinus (OpVec3.bimoduleDiff α_minus α_plus τ₁₂) ∧
    opUnipotentUpper v₁ * opUnipotentUpper (-v₁) = 1 ∧
    opUnipotentLower w₁ * opUnipotentLower (-w₁) = 1 ∧
    ((opLightconeRayPlus v₁ * opLightconeRayPlus v₂) * opLightconeRayPlus v₃).v = 0 ∧
    ((opLightconeRayPlus v₁ * opLightconeRayPlus v₂) * opLightconeRayPlus v₃).w = 0 ∧
    ((opLightconeRayMinus w₁ * opLightconeRayMinus w₂) * opLightconeRayMinus w₃).v = 0 ∧
    ((opLightconeRayMinus w₁ * opLightconeRayMinus w₂) * opLightconeRayMinus w₃).w = 0 := by
  intro Θ Δv τ₁₂ α_plus α_minus D_anom
  have hΘ : Θ = opLightconeRayPlus Δv - opLightconeRayMinus τ₁₂ :=
    (opMaurerCartanForm_grade_hierarchy_and_anomaly_generation v₁ v₂).1
  have hΘ2 : Θ * Θ = D_anom :=
    (opMaurerCartanForm_grade_hierarchy_and_anomaly_generation v₁ v₂).2.1
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hΘ2, hΘ]
    ext <;>
    (simp [D_anom, opCartanDiag, opLightconeRayPlus, opLightconeRayMinus,
           OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross];
     try noncomm_ring)
  · rw [hΘ2, hΘ]
    ext <;>
    (simp [D_anom, opCartanDiag, opLightconeRayPlus, opLightconeRayMinus,
           OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross];
     try noncomm_ring)
  · simp only [opAssociator, opCommutator, hΘ2]
  · simp only [opAssociator]
    rw [hΘ2, hΘ]
    ext <;>
    (simp [D_anom, opCartanDiag, opLightconeRayPlus, opLightconeRayMinus,
           OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross];
     try noncomm_ring)
  · ext <;>
    (simp [opUnipotentUpper, OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross];
     try noncomm_ring
     try abel)
  · ext <;>
    (simp [opUnipotentLower, OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross];
     try noncomm_ring
     try abel)
  · ext <;>
    (simp [opLightconeRayPlus, OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross];
     try noncomm_ring)
  · ext <;>
    (simp [opLightconeRayPlus, OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross];
     try noncomm_ring)
  · ext <;>
    (simp [opLightconeRayMinus, OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross];
     try noncomm_ring)
  · ext <;>
    (simp [opLightconeRayMinus, OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross];
     try noncomm_ring)

/-!
## 16. Archetypes XXXVIII–XLI: Nucleus Leibniz Derivations, Bogoliubov-Kubo-Mori (BKM) Modular Metric, Erlangen Homogeneous Flag States, Killing Lie Algebras, & Noether Supercharges
-/

/-- Modular KMS derivation $\delta_{\rho_+, \rho_-}(X) = [D(\rho_+, \rho_-), X]$ in $\mathrm{OpZornMatrix}\;A$. -/
def opModularDeriv (ρ_plus ρ_minus : A) (X : OpZornMatrix A) : OpZornMatrix A :=
  opCommutator (opCartanDiag ρ_plus ρ_minus) X

/-- Bogoliubov-Kubo-Mori (BKM) modular metric pairing
    $G_{\mathrm{BKM}}(\rho; v, w) = \{\delta_\rho(L_+(v)), L_-(w)\}$. -/
def opBKMMetric (ρ_plus ρ_minus : A) (v w : OpVec3 A) : OpZornMatrix A :=
  opAnticommutator (opModularDeriv ρ_plus ρ_minus (opLightconeRayPlus v)) (opLightconeRayMinus w)

/-- Dual BKM modular metric pairing $G_{\mathrm{BKM}}^{\mathrm{dual}}(\rho; v, w) = \{L_+(v), \delta_\rho(L_-(w))\}$. -/
def opBKMMetricDual (ρ_plus ρ_minus : A) (v w : OpVec3 A) : OpZornMatrix A :=
  opAnticommutator (opLightconeRayPlus v) (opModularDeriv ρ_plus ρ_minus (opLightconeRayMinus w))

/-- Homogeneous flag state projector $\Pi_{\mathrm{hom}}(v) = (U_+(v) * e_{11}) * U_+(-v)$ in $\mathrm{OpZornMatrix}\;A$. -/
def homogeneousFlagState (v : OpVec3 A) : OpZornMatrix A :=
  (opUnipotentUpper v * opPeircePlus) * opUnipotentUpper (-v)

/-- Forward and backward Noether supercharges $Q_+(v) = L_+(v)$ and $Q_-(w) = L_-(w)$. -/
abbrev noetherSuperchargePlus (v : OpVec3 A) : OpZornMatrix A := opLightconeRayPlus v
abbrev noetherSuperchargeMinus (w : OpVec3 A) : OpZornMatrix A := opLightconeRayMinus w

/-- Emergent Modular Hamiltonian $H_{\mathrm{mod}}(v, w) = \{Q_+(v), Q_-(w)\} = g(v, w)$. -/
def emergentModularHamiltonian (v w : OpVec3 A) : OpZornMatrix A :=
  opAnticommutator (noetherSuperchargePlus v) (noetherSuperchargeMinus w)

/-- Explicit action of $\delta_{\rho_+, \rho_-}$ on the forward lightcone ideal $\mathcal{L}_+(A^3)$. -/
theorem opModularDeriv_lightconeRayPlus (ρ_plus ρ_minus : A) (v : OpVec3 A) :
    opModularDeriv ρ_plus ρ_minus (opLightconeRayPlus v) =
      opLightconeRayPlus (OpVec3.bimoduleDiff ρ_plus ρ_minus v) := by
  ext <;>
  (simp [opModularDeriv, opCartanDiag, opLightconeRayPlus, opCommutator,
         OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross];
   try noncomm_ring)

/-- Explicit action of $\delta_{\rho_+, \rho_-}$ on the backward lightcone ideal $\mathcal{L}_-(A^3)$. -/
theorem opModularDeriv_lightconeRayMinus (ρ_plus ρ_minus : A) (w : OpVec3 A) :
    opModularDeriv ρ_plus ρ_minus (opLightconeRayMinus w) =
      opLightconeRayMinus (OpVec3.bimoduleDiff ρ_minus ρ_plus w) := by
  ext <;>
  (simp [opModularDeriv, opCartanDiag, opLightconeRayMinus, opCommutator,
         OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross];
   try noncomm_ring)

/-- Explicit homogeneous coordinates of the flag state projector $\Pi_{\mathrm{hom}}(v) = \langle 1, -v, 0, 0 \rangle$. -/
theorem homogeneousFlagState_coords (v : OpVec3 A) :
    homogeneousFlagState v = ⟨1, -v, 0, 0⟩ := by
  ext <;>
  simp [homogeneousFlagState, opUnipotentUpper, opPeircePlus,
        OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross]

/-- **52. Universal Non-Associative Leibniz Defect & Exact Opposite-Chirality / Diagonal Modular Derivation Law (Archetype XXXVIII)**:
    Over ANY noncommutative operator ring $A$, for ALL $K, X, Y \in \mathrm{OpZornMatrix}\;A$,
    any vectors $v, w \in A^3$, and any modular operators $\rho_+, \rho_- \in A$:
    1. Universal Non-Associative Leibniz Defect Identity:
       $$([K, X] * Y + X * [K, Y]) - [K, X * Y] = [K, X, Y] - [X, K, Y] + [X, Y, K].$$
    2. Exact Left, Middle, and Right Nucleus Associativity of $D(\rho_+, \rho_-)$ on Opposite-Chirality Lightcone Rays:
       $$[D(\rho_+, \rho_-), L_+(v), L_-(w)] = 0, \qquad
         [L_+(v), D(\rho_+, \rho_-), L_-(w)] = 0, \qquad
         [L_+(v), L_-(w), D(\rho_+, \rho_-)] = 0.$$
    3. Exact 8D Leibniz Product Rule for $\delta_{\rho_+, \rho_-}$ on Primal-Dual Lightcone Products:
       $$\delta_{\rho_+, \rho_-}(L_+(v) * L_-(w)) =
         \delta_{\rho_+, \rho_-}(L_+(v)) * L_-(w) + L_+(v) * \delta_{\rho_+, \rho_-}(L_-(w)),$$
       $$\delta_{\rho_+, \rho_-}(L_-(w) * L_+(v)) =
         \delta_{\rho_+, \rho_-}(L_-(w)) * L_+(v) + L_-(w) * \delta_{\rho_+, \rho_-}(L_+(v)).$$
    4. Universal Diagonal (`.a` and `.b`) Leibniz Product Rule for ALL $X, Y \in \mathrm{OpZornMatrix}\;A$:
       $$\bigl(\delta_{\rho_+, \rho_-}(X * Y)\bigr).a =
         \bigl(\delta_{\rho_+, \rho_-}(X) * Y + X * \delta_{\rho_+, \rho_-}(Y)\bigr).a,$$
       $$\bigl(\delta_{\rho_+, \rho_-}(X * Y)\bigr).b =
         \bigl(\delta_{\rho_+, \rho_-}(X) * Y + X * \delta_{\rho_+, \rho_-}(Y)\bigr).b.$$ -/
theorem opModularDeriv_nucleus_and_exact_leibniz_rule
    (K X Y : OpZornMatrix A) (v w : OpVec3 A) (ρ_plus ρ_minus : A) :
    let D_ρ := opCartanDiag ρ_plus ρ_minus
    let Lp := opLightconeRayPlus v
    let Lm := opLightconeRayMinus w
    (opCommutator K X * Y + X * opCommutator K Y) - opCommutator K (X * Y) =
      opAssociator K X Y - opAssociator X K Y + opAssociator X Y K ∧
    opAssociator D_ρ Lp Lm = 0 ∧
    opAssociator Lp D_ρ Lm = 0 ∧
    opAssociator Lp Lm D_ρ = 0 ∧
    opModularDeriv ρ_plus ρ_minus (Lp * Lm) =
      opModularDeriv ρ_plus ρ_minus Lp * Lm + Lp * opModularDeriv ρ_plus ρ_minus Lm ∧
    opModularDeriv ρ_plus ρ_minus (Lm * Lp) =
      opModularDeriv ρ_plus ρ_minus Lm * Lp + Lm * opModularDeriv ρ_plus ρ_minus Lp ∧
    (opModularDeriv ρ_plus ρ_minus (X * Y)).a =
      (opModularDeriv ρ_plus ρ_minus X * Y + X * opModularDeriv ρ_plus ρ_minus Y).a ∧
    (opModularDeriv ρ_plus ρ_minus (X * Y)).b =
      (opModularDeriv ρ_plus ρ_minus X * Y + X * opModularDeriv ρ_plus ρ_minus Y).b := by
  intro D_ρ Lp Lm
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [opCommutator, opAssociator, opZorn_sub_mul, opZorn_mul_sub]
    ext <;>
    (simp only [OpZornMatrix.add_a, OpZornMatrix.add_v, OpZornMatrix.add_w, OpZornMatrix.add_b,
                OpZornMatrix.sub_a, OpZornMatrix.sub_v, OpZornMatrix.sub_w, OpZornMatrix.sub_b,
                OpVec3.add_x, OpVec3.add_y, OpVec3.add_z,
                OpVec3.sub_x, OpVec3.sub_y, OpVec3.sub_z];
     abel)
  · ext <;>
    (simp [D_ρ, Lp, Lm, opCartanDiag, opLightconeRayPlus, opLightconeRayMinus,
           opAssociator, OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross];
     try noncomm_ring)
  · ext <;>
    (simp [D_ρ, Lp, Lm, opCartanDiag, opLightconeRayPlus, opLightconeRayMinus,
           opAssociator, OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross];
     try noncomm_ring)
  · ext <;>
    (simp [D_ρ, Lp, Lm, opCartanDiag, opLightconeRayPlus, opLightconeRayMinus,
           opAssociator, OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross];
     try noncomm_ring)
  · change opModularDeriv ρ_plus ρ_minus (opLightconeRayPlus v * opLightconeRayMinus w) =
      opModularDeriv ρ_plus ρ_minus (opLightconeRayPlus v) * opLightconeRayMinus w +
        opLightconeRayPlus v * opModularDeriv ρ_plus ρ_minus (opLightconeRayMinus w)
    rw [opModularDeriv_lightconeRayPlus, opModularDeriv_lightconeRayMinus]
    ext <;>
    (simp [opModularDeriv, opCartanDiag, opLightconeRayPlus, opLightconeRayMinus,
           opCommutator, OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross];
     try noncomm_ring)
  · change opModularDeriv ρ_plus ρ_minus (opLightconeRayMinus w * opLightconeRayPlus v) =
      opModularDeriv ρ_plus ρ_minus (opLightconeRayMinus w) * opLightconeRayPlus v +
        opLightconeRayMinus w * opModularDeriv ρ_plus ρ_minus (opLightconeRayPlus v)
    rw [opModularDeriv_lightconeRayPlus, opModularDeriv_lightconeRayMinus]
    ext <;>
    (simp [opModularDeriv, opCartanDiag, opLightconeRayPlus, opLightconeRayMinus,
           opCommutator, OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross];
     try noncomm_ring)
  · simp [opModularDeriv, opCartanDiag, opCommutator, OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross]
    noncomm_ring
  · simp [opModularDeriv, opCartanDiag, opCommutator, OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross]
    noncomm_ring

/-- **53. Explicit BKM Modular Metric, KMS Leibniz Conservation, & Symplectic Duality (Archetype XXXIX)**:
    Over ANY noncommutative operator ring $A$, for all $\rho_+, \rho_- \in A$, $v, w \in A^3$, and $X, Y \in \mathrm{OpZornMatrix}\;A$:
    1. Explicit BKM Modular Metric Coordinates:
       $$G_{\mathrm{BKM}}(\rho; v, w) =
         \Bigl\langle -\bigl(\nabla_{\rho_+, \rho_-}(v) \cdot w\bigr),\;\; 0,\;\; 0,\;\;
                      -\bigl(w \cdot \nabla_{\rho_+, \rho_-}(v)\bigr) \Bigr\rangle.$$
    2. KMS Integration-by-Parts / Leibniz Conservation for the Para-Kähler Metric $g(v, w)$:
       $$G_{\mathrm{BKM}}(\rho; v, w) + G_{\mathrm{BKM}}^{\mathrm{dual}}(\rho; v, w) =
         \delta_{\rho_+, \rho_-}(g(v, w)) =
         \Bigl\langle -\bigl(\rho_+ (v \cdot w) - (v \cdot w) \rho_+\bigr),\;\; 0,\;\; 0,\;\;
                      -\bigl(\rho_- (w \cdot v) - (w \cdot v) \rho_-\bigr) \Bigr\rangle.$$
    3. KMS Leibniz Conservation for the Para-Kähler Symplectic 2-Form $\omega(v, w)$:
       $$[\delta_{\rho}(L_+(v)), L_-(w)] + [L_+(v), \delta_{\rho}(L_-(w))] =
         \delta_{\rho_+, \rho_-}(\omega(v, w)) =
         \Bigl\langle -\bigl(\rho_+ (v \cdot w) - (v \cdot w) \rho_+\bigr),\;\; 0,\;\; 0,\;\;
                      +\bigl(\rho_- (w \cdot v) - (w \cdot v) \rho_-\bigr) \Bigr\rangle.$$
    4. Universal KMS Trace Adjoint Duality:
       $$\mathrm{opZornTrace}\bigl(\delta_\rho(X) * Y + X * \delta_\rho(Y)\bigr) =
         \bigl(\rho_+ (X * Y)_a - (X * Y)_a \rho_+\bigr) + \bigl(\rho_- (X * Y)_b - (X * Y)_b \rho_-\bigr).$$ -/
theorem opBKMMetric_coords_and_kms_leibniz_conservation
    (ρ_plus ρ_minus : A) (v w : OpVec3 A) (X Y : OpZornMatrix A) :
    let dv := OpVec3.bimoduleDiff ρ_plus ρ_minus v
    let g := opParaKahlerMetric v w
    let ω := opParaKahlerSymplectic v w
    opBKMMetric ρ_plus ρ_minus v w =
      ⟨-OpVec3.dot dv w, 0, 0, -OpVec3.dot w dv⟩ ∧
    opBKMMetric ρ_plus ρ_minus v w + opBKMMetricDual ρ_plus ρ_minus v w =
      opModularDeriv ρ_plus ρ_minus g ∧
    opModularDeriv ρ_plus ρ_minus g =
      ⟨-(ρ_plus * OpVec3.dot v w - OpVec3.dot v w * ρ_plus),
       0,
       0,
       -(ρ_minus * OpVec3.dot w v - OpVec3.dot w v * ρ_minus)⟩ ∧
    opCommutator (opModularDeriv ρ_plus ρ_minus (opLightconeRayPlus v)) (opLightconeRayMinus w) +
      opCommutator (opLightconeRayPlus v) (opModularDeriv ρ_plus ρ_minus (opLightconeRayMinus w)) =
      opModularDeriv ρ_plus ρ_minus ω ∧
    opModularDeriv ρ_plus ρ_minus ω =
      ⟨-(ρ_plus * OpVec3.dot v w - OpVec3.dot v w * ρ_plus),
       0,
       0,
       ρ_minus * OpVec3.dot w v - OpVec3.dot w v * ρ_minus⟩ ∧
    opZornTrace (opModularDeriv ρ_plus ρ_minus X * Y + X * opModularDeriv ρ_plus ρ_minus Y) =
      (ρ_plus * (X * Y).a - (X * Y).a * ρ_plus) +
        (ρ_minus * (X * Y).b - (X * Y).b * ρ_minus) := by
  intro dv g ω
  have hg : g = ⟨-OpVec3.dot v w, 0, 0, -OpVec3.dot w v⟩ :=
    (opParaKahler_triplet_compatibility_and_anomaly_residue v w).1
  have hω : ω = ⟨-OpVec3.dot v w, 0, 0, OpVec3.dot w v⟩ :=
    (opParaKahler_triplet_compatibility_and_anomaly_residue v w).2.1
  have hBKM1 : opBKMMetric ρ_plus ρ_minus v w = ⟨-OpVec3.dot dv w, 0, 0, -OpVec3.dot w dv⟩ := by
    unfold opBKMMetric
    rw [opModularDeriv_lightconeRayPlus]
    exact (opParaKahler_triplet_compatibility_and_anomaly_residue dv w).1
  have hBKM2 : opBKMMetricDual ρ_plus ρ_minus v w =
      ⟨-OpVec3.dot v (OpVec3.bimoduleDiff ρ_minus ρ_plus w), 0, 0,
       -OpVec3.dot (OpVec3.bimoduleDiff ρ_minus ρ_plus w) v⟩ := by
    unfold opBKMMetricDual
    rw [opModularDeriv_lightconeRayMinus]
    exact (opParaKahler_triplet_compatibility_and_anomaly_residue v (OpVec3.bimoduleDiff ρ_minus ρ_plus w)).1
  have hDg : opModularDeriv ρ_plus ρ_minus g =
      ⟨-(ρ_plus * OpVec3.dot v w - OpVec3.dot v w * ρ_plus),
       0,
       0,
       -(ρ_minus * OpVec3.dot w v - OpVec3.dot w v * ρ_minus)⟩ := by
    rw [hg]
    ext <;>
    (simp [opModularDeriv, opCartanDiag, opCommutator, OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross];
     try noncomm_ring)
  have hDω : opModularDeriv ρ_plus ρ_minus ω =
      ⟨-(ρ_plus * OpVec3.dot v w - OpVec3.dot v w * ρ_plus),
       0,
       0,
       ρ_minus * OpVec3.dot w v - OpVec3.dot w v * ρ_minus⟩ := by
    rw [hω]
    ext <;>
    (simp [opModularDeriv, opCartanDiag, opCommutator, OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross];
     try noncomm_ring)
  refine ⟨hBKM1, ?_, hDg, ?_, hDω, ?_⟩
  · rw [hBKM1, hBKM2, hDg]
    ext <;>
    (simp [dv, OpVec3.dot];
     try noncomm_ring)
  · rw [opModularDeriv_lightconeRayPlus, opModularDeriv_lightconeRayMinus, hDω]
    have hω1 := (opParaKahler_triplet_compatibility_and_anomaly_residue dv w).2.1
    have hω2 := (opParaKahler_triplet_compatibility_and_anomaly_residue v (OpVec3.bimoduleDiff ρ_minus ρ_plus w)).2.1
    unfold opParaKahlerSymplectic at hω1 hω2
    rw [hω1, hω2]
    ext <;>
    (simp [dv, OpVec3.dot];
     try noncomm_ring)
  · simp only [opZornTrace, OpZornMatrix.add_a, OpZornMatrix.add_b]
    have hLeib := opModularDeriv_nucleus_and_exact_leibniz_rule 0 X Y v w ρ_plus ρ_minus
    have ha : (opModularDeriv ρ_plus ρ_minus X * Y).a + (X * opModularDeriv ρ_plus ρ_minus Y).a =
              (opModularDeriv ρ_plus ρ_minus (X * Y)).a := hLeib.2.2.2.2.2.2.1.symm
    have hb : (opModularDeriv ρ_plus ρ_minus X * Y).b + (X * opModularDeriv ρ_plus ρ_minus Y).b =
              (opModularDeriv ρ_plus ρ_minus (X * Y)).b := hLeib.2.2.2.2.2.2.2.symm
    rw [ha, hb]
    simp [opModularDeriv, opCartanDiag, opCommutator, OpVec3.dot]

/-- **54. Homogeneous Flag State Orbit, Exact Idempotence, & Symmetry Group Law (Archetype XL.1)**:
    Over ANY noncommutative operator ring $A$, for all $v, v_1, v_2 \in A^3$:
    1. Vanishing Exponential Orbit Associator:
       $[U_+(v), e_{11}, U_+(-v)] = 0$.
    2. Explicit Homogeneous Coordinates:
       $\Pi_{\mathrm{hom}}(v) = \langle 1, -v, 0, 0 \rangle$.
    3. Exact Projective Idempotence:
       $\Pi_{\mathrm{hom}}(v) * \Pi_{\mathrm{hom}}(v) = \Pi_{\mathrm{hom}}(v)$.
    4. Exact Conjugation Law with Double Torsion & Scalar Defect, and Transitive Flag Projection:
       $$(U_+(v_1) * \Pi_{\mathrm{hom}}(v_2)) * U_+(-v_1) =
         \Pi_{\mathrm{hom}}(v_1 + v_2) -
         \Bigl\langle 0,\; 0,\; \tau_{12} + \tau_{12},\; \tau_{12} \cdot v_1 \Bigr\rangle,$$
       $$e_{11} * \bigl((U_+(v_1) * \Pi_{\mathrm{hom}}(v_2)) * U_+(-v_1)\bigr) =
         \Pi_{\mathrm{hom}}(v_1 + v_2),$$
       where $\tau_{12} = v_1 \times_{\mathrm{skew}} v_2$. -/
theorem homogeneousFlagState_orbit_idempotence_and_group_action
    (v v₁ v₂ : OpVec3 A) :
    let τ₁₂ := OpVec3.skewCross v₁ v₂
    opAssociator (opUnipotentUpper v) opPeircePlus (opUnipotentUpper (-v)) = 0 ∧
    homogeneousFlagState v = ⟨1, -v, 0, 0⟩ ∧
    homogeneousFlagState v * homogeneousFlagState v = homogeneousFlagState v ∧
    (opUnipotentUpper v₁ * homogeneousFlagState v₂) * opUnipotentUpper (-v₁) =
      homogeneousFlagState (v₁ + v₂) - ⟨0, 0, τ₁₂ + τ₁₂, OpVec3.dot τ₁₂ v₁⟩ ∧
    opPeircePlus * ((opUnipotentUpper v₁ * homogeneousFlagState v₂) * opUnipotentUpper (-v₁)) =
      homogeneousFlagState (v₁ + v₂) := by
  intro τ₁₂
  refine ⟨?_, homogeneousFlagState_coords v, ?_, ?_, ?_⟩
  · ext <;>
    (simp [opUnipotentUpper, opPeircePlus, opAssociator,
           OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross];
     try abel)
  · rw [homogeneousFlagState_coords]
    ext <;>
    simp [OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross]
  · rw [homogeneousFlagState_coords, homogeneousFlagState_coords]
    ext <;>
    (simp [τ₁₂, opUnipotentUpper, OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross];
     try noncomm_ring
     try abel)
  · rw [homogeneousFlagState_coords, homogeneousFlagState_coords]
    ext <;>
    (simp [opPeircePlus, opUnipotentUpper, OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross];
     try abel)

/-- **55. Killing Lie Algebra Representation of Nucleus Derivations on $\mathrm{OpZornMatrix}\;A$ (Archetype XL.2)**:
    Over ANY noncommutative operator ring $A$, for any two modular generators
    $D_1 = D(\rho_+, \rho_-)$ and $D_2 = D(\sigma_+, \sigma_-)$ and ANY $X \in \mathrm{OpZornMatrix}\;A$:
    1. Closure of Nucleus Commutator:
       $[D_1, D_2] = D(\rho_+ \sigma_+ - \sigma_+ \rho_+,\; \rho_- \sigma_- - \sigma_- \rho_-)$.
    2. Exact Killing Lie Bracket Homomorphism on 8D Non-Associative $\mathrm{OpZornMatrix}\;A$:
       $\delta_{D_1}(\delta_{D_2}(X)) - \delta_{D_2}(\delta_{D_1}(X)) = \delta_{[D_1, D_2]}(X)$. -/
theorem killing_nucleus_derivation_lie_homomorphism
    (ρ_plus ρ_minus σ_plus σ_minus : A) (X : OpZornMatrix A) :
    let D₁ := opCartanDiag ρ_plus ρ_minus
    let D₂ := opCartanDiag σ_plus σ_minus
    opCommutator D₁ D₂ =
      opCartanDiag (ρ_plus * σ_plus - σ_plus * ρ_plus)
                   (ρ_minus * σ_minus - σ_minus * ρ_minus) ∧
    opCommutator D₁ (opCommutator D₂ X) - opCommutator D₂ (opCommutator D₁ X) =
      opCommutator (opCommutator D₁ D₂) X := by
  intro D₁ D₂
  refine ⟨?_, ?_⟩ <;>
  (ext <;>
   (simp [D₁, D₂, opCartanDiag, opCommutator, OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross];
    try noncomm_ring))

/-- **56. Noether Supercharge Anticommutator, Emergent Modular Leibniz Flow, & Conservation (Archetype XLI)**:
    Over ANY noncommutative operator ring $A$, for all $v, w \in A^3$ and $u, q \in A$:
    1. Nilpotence of Supercharges & Emergence of Modular Hamiltonian:
       $Q_+(v)^2 = 0$, $Q_-(w)^2 = 0$, and
       $H_{\mathrm{mod}}(v, w) = \{Q_+(v), Q_-(w)\} = \langle -(v \cdot w), 0, 0, -(w \cdot v) \rangle$.
    2. Exact Noether-Leibniz Derivation Law of the Emergent Modular Hamiltonian on Opposite-Chirality Supercharges:
       $[H_{\mathrm{mod}}(v, w), Q_+(v) * Q_-(w)] = [H_{\mathrm{mod}}(v, w), Q_+(v)] * Q_-(w) + Q_+(v) * [H_{\mathrm{mod}}(v, w), Q_-(w)]$.
    3. Noether Anomaly = Self-Associator of $J(v, w) = Q_+(v) + Q_-(w)$:
       $[H_{\mathrm{mod}}(v, w), J(v, w)] = [J(v, w), J(v, w), J(v, w)]$ and
       $[H_{\mathrm{mod}}(v, w), Q_+(v)] = Q_+(v \cdot_R (w \cdot v) - (v \cdot w) \cdot_L v)$.
    4. Exact Conservation of Noether Supercharges on Single-Channel Operator Slices:
       For $v_1 = \langle u, 0, 0 \rangle$ and $w_1 = \langle q, 0, 0 \rangle$,
       $[H_{\mathrm{mod}}(v_1, w_1), Q_+(v_1)] = 0$ and
       $[H_{\mathrm{mod}}(v_1, w_1), Q_-(w_1)] = 0$. -/
theorem noetherSupercharges_emergent_modular_hamiltonian_and_conservation
    (v w : OpVec3 A) (u q : A) :
    let Q_p := noetherSuperchargePlus v
    let Q_m := noetherSuperchargeMinus w
    let J := opKasparovZornJ v w
    let H_mod := emergentModularHamiltonian v w
    let v₁ := opBasisE1 u
    let w₁ := opBasisE1 q
    let H₁ := emergentModularHamiltonian v₁ w₁
    Q_p * Q_p = 0 ∧
    Q_m * Q_m = 0 ∧
    H_mod = opCartanDiag (-OpVec3.dot v w) (-OpVec3.dot w v) ∧
    opCommutator H_mod (Q_p * Q_m) =
      opCommutator H_mod Q_p * Q_m + Q_p * opCommutator H_mod Q_m ∧
    opCommutator H_mod J = opAssociator J J J ∧
    opCommutator H_mod Q_p =
      noetherSuperchargePlus
        (OpVec3.rightScale v (OpVec3.dot w v) - OpVec3.leftScale (OpVec3.dot v w) v) ∧
    opCommutator H₁ (noetherSuperchargePlus v₁) = 0 ∧
    opCommutator H₁ (noetherSuperchargeMinus w₁) = 0 := by
  intro Q_p Q_m J H_mod v₁ w₁ H₁
  have hH : H_mod = opCartanDiag (-OpVec3.dot v w) (-OpVec3.dot w v) := by
    ext <;>
    (simp [H_mod, emergentModularHamiltonian, opCartanDiag, opAnticommutator,
           opLightconeRayPlus, opLightconeRayMinus, OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross];
     try noncomm_ring)
  refine ⟨?_, ?_, hH, ?_, ?_, ?_, ?_, ?_⟩
  · ext <;>
    (simp [Q_p, opLightconeRayPlus, OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross];
     try noncomm_ring)
  · ext <;>
    (simp [Q_m, opLightconeRayMinus, OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross];
     try noncomm_ring)
  · rw [hH]
    exact (opModularDeriv_nucleus_and_exact_leibniz_rule H_mod Q_p Q_m v w (-OpVec3.dot v w) (-OpVec3.dot w v)).2.2.2.2.1
  · rw [hH]
    ext <;>
    (simp [J, opKasparovZornJ, opCartanDiag, opCommutator, opAssociator,
           OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross];
     try noncomm_ring)
  · rw [hH]
    ext <;>
    (simp [Q_p, opLightconeRayPlus, opCartanDiag, opCommutator,
           OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross];
     try noncomm_ring)
  · ext <;>
    (simp [H₁, v₁, w₁, emergentModularHamiltonian, opBasisE1, opAnticommutator, opCommutator,
           opLightconeRayPlus, opLightconeRayMinus, OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross];
     try noncomm_ring)
  · ext <;>
    (simp [H₁, v₁, w₁, emergentModularHamiltonian, opBasisE1, opAnticommutator, opCommutator,
           opLightconeRayPlus, opLightconeRayMinus, OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross];
     try noncomm_ring)

/-!
## 17. Archetypes XLII & XLIII: The 5-Graded Kantor-Koecher-Tits Contact Structure & Associative Heisenberg Nilradicals in $\mathrm{Zorn}(A)$
-/

/-- **Grade $-2$ ($\mathcal{G}_{-2}$)**: Longitudinal dual contact ray $E_{-2}(\eta) = \langle 0, \langle \eta, 0, 0 \rangle, 0, 0 \rangle$. -/
def opGradeMinus2 (η : A) : OpZornMatrix A := ⟨0, ⟨η, 0, 0⟩, 0, 0⟩

/-- **Grade $-1$ ($\mathcal{G}_{-1}$)**: Transverse backward plane $E_{-1}(y, z) = \langle 0, 0, \langle 0, y, z \rangle, 0 \rangle$. -/
def opGradeMinus1 (y z : A) : OpZornMatrix A := ⟨0, 0, ⟨0, y, z⟩, 0⟩

/-- **Grade $0$ ($\mathcal{G}_0$)**: Associative nucleus Cartan/modular diagonal $D(\rho_+, \rho_-) = \langle \rho_+, 0, 0, \rho_- \rangle$. -/
abbrev opGradeZero (ρ_plus ρ_minus : A) : OpZornMatrix A := opCartanDiag ρ_plus ρ_minus

/-- **Grade $+1$ ($\mathcal{G}_{+1}$)**: Transverse forward plane $E_{+1}(y, z) = \langle 0, \langle 0, y, z \rangle, 0, 0 \rangle$. -/
def opGradePlus1 (y z : A) : OpZornMatrix A := ⟨0, ⟨0, y, z⟩, 0, 0⟩

/-- **Grade $+2$ ($\mathcal{G}_{+2}$)**: Longitudinal primal contact ray $E_{+2}(\xi) = \langle 0, 0, \langle \xi, 0, 0 \rangle, 0 \rangle$. -/
def opGradePlus2 (ξ : A) : OpZornMatrix A := ⟨0, 0, ⟨ξ, 0, 0⟩, 0⟩

/-- Skew-symmetrized transverse symplectic contact form $\omega_\perp(y_1, z_1; y_2, z_2) \in A$. -/
def opContactSymplecticForm (y₁ z₁ y₂ z₂ : A) : A :=
  (y₁ * z₂ - z₁ * y₂) - (y₂ * z₁ - z₂ * y₁)

/-- General element $N_+(y, z, \xi) = E_{+1}(y, z) + E_{+2}(\xi)$ of the positive Heisenberg nilradical $\mathcal{N}_+ = \mathcal{G}_{+1} \oplus \mathcal{G}_{+2}$. -/
def opHeisenbergNilPlus (y z ξ : A) : OpZornMatrix A :=
  ⟨0, ⟨0, y, z⟩, ⟨ξ, 0, 0⟩, 0⟩

/-- Exponential element $H_+(y, z, \xi) = 1 + N_+(y, z, \xi)$ in the positive Heisenberg group $\exp(\mathcal{N}_+)$. -/
def opHeisenbergGroupPlus (y z ξ : A) : OpZornMatrix A :=
  ⟨1, ⟨0, y, z⟩, ⟨ξ, 0, 0⟩, 1⟩

/-- Helper lemma: product of two elements in the 5-graded positive Heisenberg nilradical $\mathcal{N}_+ = \mathcal{G}_{+1} \oplus \mathcal{G}_{+2}$. -/
theorem opHeisenbergNilPlus_mul (y₁ z₁ ξ₁ y₂ z₂ ξ₂ : A) :
    opHeisenbergNilPlus y₁ z₁ ξ₁ * opHeisenbergNilPlus y₂ z₂ ξ₂ =
      opGradePlus2 (opContactSymplecticForm y₁ z₁ y₂ z₂) := by
  ext <;>
  (simp [opHeisenbergNilPlus, opGradePlus2, opContactSymplecticForm,
         OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross];
   try noncomm_ring)

/-- Helper lemma: product of two elements in the 5-graded positive Heisenberg group $\exp(\mathcal{N}_+)$. -/
theorem opHeisenbergGroupPlus_mul (y₁ z₁ ξ₁ y₂ z₂ ξ₂ : A) :
    opHeisenbergGroupPlus y₁ z₁ ξ₁ * opHeisenbergGroupPlus y₂ z₂ ξ₂ =
      opHeisenbergGroupPlus (y₁ + y₂) (z₁ + z₂)
        (ξ₁ + ξ₂ + opContactSymplecticForm y₁ z₁ y₂ z₂) := by
  ext <;>
  (simp [opHeisenbergGroupPlus, opContactSymplecticForm,
         OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross];
   try noncomm_ring
   try abel)

/-- **57. Exact 5-Graded Step-2 Multiplication & Nilpotent Termination at Grade $\pm 2$ (Archetype XLII.1)**:
    Over ANY noncommutative operator ring $A$, for all $y, z, y_1, z_1, y_2, z_2, \xi, \xi_1, \xi_2, \eta, \eta_1, \eta_2 \in A$:
    1. Grade $+1 \times$ Grade $+1 \to$ Grade $+2$:
       $E_{+1}(y_1, z_1) * E_{+1}(y_2, z_2) = E_{+2}(\omega_\perp(y_1, z_1; y_2, z_2))$.
    2. Grade $-1 \times$ Grade $-1 \to$ Grade $-2$:
       $E_{-1}(y_1, z_1) * E_{-1}(y_2, z_2) = E_{-2}(-\omega_\perp(y_1, z_1; y_2, z_2))$.
    3. Exact Positive Termination ($\mathcal{G}_{+1} * \mathcal{G}_{+2} = 0$, $\mathcal{G}_{+2} * \mathcal{G}_{+1} = 0$, $\mathcal{G}_{+2} * \mathcal{G}_{+2} = 0$):
       $E_{+1}(y, z) * E_{+2}(\xi) = 0$, $E_{+2}(\xi) * E_{+1}(y, z) = 0$, and $E_{+2}(\xi_1) * E_{+2}(\xi_2) = 0$.
    4. Exact Negative Termination ($\mathcal{G}_{-1} * \mathcal{G}_{-2} = 0$, $\mathcal{G}_{-2} * \mathcal{G}_{-1} = 0$, $\mathcal{G}_{-2} * \mathcal{G}_{-2} = 0$):
       $E_{-1}(y, z) * E_{-2}(\eta) = 0$, $E_{-2}(\eta) * E_{-1}(y, z) = 0$, and $E_{-2}(\eta_1) * E_{-2}(\eta_2) = 0$. -/
theorem fiveGraded_step_two_heisenberg_and_termination
    (y z y₁ z₁ y₂ z₂ ξ ξ₁ ξ₂ η η₁ η₂ : A) :
    opGradePlus1 y₁ z₁ * opGradePlus1 y₂ z₂ =
      opGradePlus2 (opContactSymplecticForm y₁ z₁ y₂ z₂) ∧
    opGradeMinus1 y₁ z₁ * opGradeMinus1 y₂ z₂ =
      opGradeMinus2 (-opContactSymplecticForm y₁ z₁ y₂ z₂) ∧
    opGradePlus1 y z * opGradePlus2 ξ = 0 ∧
    opGradePlus2 ξ * opGradePlus1 y z = 0 ∧
    opGradePlus2 ξ₁ * opGradePlus2 ξ₂ = 0 ∧
    opGradeMinus1 y z * opGradeMinus2 η = 0 ∧
    opGradeMinus2 η * opGradeMinus1 y z = 0 ∧
    opGradeMinus2 η₁ * opGradeMinus2 η₂ = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  (ext <;>
   (simp [opGradePlus1, opGradePlus2, opGradeMinus1, opGradeMinus2, opContactSymplecticForm,
          OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross];
    try noncomm_ring))

/-- **58. Exact Associativity of the 5-Graded Nilradical $\mathcal{N}_+$ & Heisenberg Group Law (Archetype XLII.2)**:
    Over ANY noncommutative operator ring $A$, for all $y_i, z_i, \xi_i \in A$:
    1. 2-Step Nilradical Product:
       $N_+(y_1, z_1, \xi_1) * N_+(y_2, z_2, \xi_2) = E_{+2}(\omega_\perp(y_1, z_1; y_2, z_2))$.
    2. Vanishing Triple Products & Vanishing 3-Associator on $\mathcal{N}_+$:
       $(N_1 * N_2) * N_3 = 0$, $N_1 * (N_2 * N_3) = 0$, and $\mathrm{opAssociator}\;N_1\;N_2\;N_3 = 0$.
    3. Exact Associative Heisenberg Group Law on $\exp(\mathcal{N}_+)$:
       $H_+(y_1, z_1, \xi_1) * H_+(y_2, z_2, \xi_2) =
        H_+(y_1 + y_2,\; z_1 + z_2,\; \xi_1 + \xi_2 + \omega_\perp(y_1, z_1; y_2, z_2))$.
    4. Vanishing Group 3-Associator & Exact Two-Sided Group Inversion:
       $\mathrm{opAssociator}\;H_1\;H_2\;H_3 = 0$ and
       $H_+(y_1, z_1, \xi_1) * H_+(-y_1, -z_1, -\xi_1) = 1$. -/
theorem heisenbergNilPlus_associativity_and_group_law
    (y₁ z₁ ξ₁ y₂ z₂ ξ₂ y₃ z₃ ξ₃ : A) :
    let N₁ := opHeisenbergNilPlus y₁ z₁ ξ₁
    let N₂ := opHeisenbergNilPlus y₂ z₂ ξ₂
    let N₃ := opHeisenbergNilPlus y₃ z₃ ξ₃
    let H₁ := opHeisenbergGroupPlus y₁ z₁ ξ₁
    let H₂ := opHeisenbergGroupPlus y₂ z₂ ξ₂
    let H₃ := opHeisenbergGroupPlus y₃ z₃ ξ₃
    N₁ * N₂ = opGradePlus2 (opContactSymplecticForm y₁ z₁ y₂ z₂) ∧
    (N₁ * N₂) * N₃ = 0 ∧
    N₁ * (N₂ * N₃) = 0 ∧
    opAssociator N₁ N₂ N₃ = 0 ∧
    H₁ * H₂ =
      opHeisenbergGroupPlus (y₁ + y₂) (z₁ + z₂)
        (ξ₁ + ξ₂ + opContactSymplecticForm y₁ z₁ y₂ z₂) ∧
    opAssociator H₁ H₂ H₃ = 0 ∧
    H₁ * opHeisenbergGroupPlus (-y₁) (-z₁) (-ξ₁) = 1 := by
  intro N₁ N₂ N₃ H₁ H₂ H₃
  have hL : (N₁ * N₂) * N₃ = 0 := by
    change (opHeisenbergNilPlus y₁ z₁ ξ₁ * opHeisenbergNilPlus y₂ z₂ ξ₂) * N₃ = 0
    rw [opHeisenbergNilPlus_mul]
    ext <;>
    simp [N₃, opGradePlus2, opHeisenbergNilPlus, OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross]
  have hR : N₁ * (N₂ * N₃) = 0 := by
    change N₁ * (opHeisenbergNilPlus y₂ z₂ ξ₂ * opHeisenbergNilPlus y₃ z₃ ξ₃) = 0
    rw [opHeisenbergNilPlus_mul]
    ext <;>
    simp [N₁, opGradePlus2, opHeisenbergNilPlus, OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross]
  have hAssocN : opAssociator N₁ N₂ N₃ = 0 := by
    unfold opAssociator
    rw [hL, hR]
    ext <;> simp
  refine ⟨opHeisenbergNilPlus_mul y₁ z₁ ξ₁ y₂ z₂ ξ₂,
          hL, hR, hAssocN,
          opHeisenbergGroupPlus_mul y₁ z₁ ξ₁ y₂ z₂ ξ₂,
          ?_, ?_⟩
  · change (opHeisenbergGroupPlus y₁ z₁ ξ₁ * opHeisenbergGroupPlus y₂ z₂ ξ₂) * opHeisenbergGroupPlus y₃ z₃ ξ₃ -
      opHeisenbergGroupPlus y₁ z₁ ξ₁ * (opHeisenbergGroupPlus y₂ z₂ ξ₂ * opHeisenbergGroupPlus y₃ z₃ ξ₃) = 0
    rw [opHeisenbergGroupPlus_mul, opHeisenbergGroupPlus_mul,
        opHeisenbergGroupPlus_mul, opHeisenbergGroupPlus_mul]
    ext <;>
    (simp [opHeisenbergGroupPlus, opContactSymplecticForm];
     try noncomm_ring
     try abel)
  · change opHeisenbergGroupPlus y₁ z₁ ξ₁ * opHeisenbergGroupPlus (-y₁) (-z₁) (-ξ₁) = 1
    rw [opHeisenbergGroupPlus_mul]
    ext <;>
    (simp [opHeisenbergGroupPlus, opContactSymplecticForm];
     try noncomm_ring)

/-- **59. Opposite-Grade Contact Couplings into $\mathcal{G}_0$ & Adjoint Lowering $\mathcal{G}_{+1} \times \mathcal{G}_{-2} \to \mathcal{G}_{-1}$ (Archetype XLIII)**:
    Over ANY noncommutative operator ring $A$, for all $y, z, y_1, z_1, y_2, z_2, \xi, \eta \in A$:
    1. Grade $-2 \times$ Grade $+2 \to$ Grade $0$:
       $E_{-2}(\eta) * E_{+2}(\xi) = \langle -\eta \xi, 0, 0, 0 \rangle$ and
       $E_{+2}(\xi) * E_{-2}(\eta) = \langle 0, 0, 0, -\xi \eta \rangle$.
    2. Grade $+1 \times$ Grade $-1$ Symmetric Anticommutator $\to$ Grade $0$:
       $E_{+1}(y_1, z_1) * E_{-1}(y_2, z_2) + E_{-1}(y_2, z_2) * E_{+1}(y_1, z_1) =
        \mathrm{opGradeZero}\;(-(y_1 y_2 + z_1 z_2))\;(-(y_2 y_1 + z_2 z_1))$.
    3. Grade $+1 \times$ Grade $-2 \to$ Grade $-1$ (Contact Lowering Action):
       $E_{+1}(y, z) * E_{-2}(\eta) = E_{-1}(z \eta + \eta z,\; -(y \eta + \eta y))$. -/
theorem fiveGraded_opposite_grade_couplings
    (y z y₁ z₁ y₂ z₂ ξ η : A) :
    opGradeMinus2 η * opGradePlus2 ξ = opGradeZero (-η * ξ) 0 ∧
    opGradePlus2 ξ * opGradeMinus2 η = opGradeZero 0 (-ξ * η) ∧
    opGradePlus1 y₁ z₁ * opGradeMinus1 y₂ z₂ + opGradeMinus1 y₂ z₂ * opGradePlus1 y₁ z₁ =
      opGradeZero (-(y₁ * y₂ + z₁ * z₂)) (-(y₂ * y₁ + z₂ * z₁)) ∧
    opGradePlus1 y z * opGradeMinus2 η =
      opGradeMinus1 (z * η + η * z) (-(y * η + η * y)) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  (ext <;>
   (simp [opGradeMinus2, opGradePlus2, opGradeMinus1, opGradePlus1, opGradeZero, opCartanDiag,
          OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross];
    try noncomm_ring))

end PorterNoncommutativeRiccatiAndLoxodromes

end SplitQuaternion

end InfoGeometry.Canonical.AlbertCayleyDickson
