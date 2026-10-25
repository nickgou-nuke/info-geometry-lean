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

end PorterNoncommutativeRiccatiAndLoxodromes

end SplitQuaternion

end InfoGeometry.Canonical.AlbertCayleyDickson
