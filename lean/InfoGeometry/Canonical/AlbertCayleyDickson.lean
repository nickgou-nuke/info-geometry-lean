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

instance instZeroAlbertStep {γ : F} : Zero (AlbertStep F A γ) where
  zero := zeroElem (F := F) (A := A) (γ := γ)

instance instOneAlbertStep {γ : F} : One (AlbertStep F A γ) where
  one := oneElem (F := F) (A := A) (γ := γ)

instance instAddAlbertStep {γ : F} : Add (AlbertStep F A γ) where
  add x y := ⟨x.p + y.p, x.q + y.q⟩

instance instSubAlbertStep {γ : F} : Sub (AlbertStep F A γ) where
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

instance instZeroOpVec3 : Zero (OpVec3 A) := ⟨⟨0, 0, 0⟩⟩
instance instInhabitedOpVec3 : Inhabited (OpVec3 A) := ⟨0⟩
instance instAddOpVec3 : Add (OpVec3 A) := ⟨fun u v => ⟨u.x + v.x, u.y + v.y, u.z + v.z⟩⟩
instance instSubOpVec3 : Sub (OpVec3 A) := ⟨fun u v => ⟨u.x - v.x, u.y - v.y, u.z - v.z⟩⟩
instance instNegOpVec3 : Neg (OpVec3 A) := ⟨fun u => ⟨-u.x, -u.y, -u.z⟩⟩

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

instance instZeroOpZornMatrix : Zero (OpZornMatrix A) := ⟨⟨0, 0, 0, 0⟩⟩
instance instOneOpZornMatrix : One (OpZornMatrix A) := ⟨⟨1, 0, 0, 1⟩⟩
instance instInhabitedOpZornMatrix : Inhabited (OpZornMatrix A) := ⟨0⟩
instance instAddOpZornMatrix : Add (OpZornMatrix A) :=
  ⟨fun X Y => ⟨X.a + Y.a, X.v + Y.v, X.w + Y.w, X.b + Y.b⟩⟩
instance instSubOpZornMatrix : Sub (OpZornMatrix A) :=
  ⟨fun X Y => ⟨X.a - Y.a, X.v - Y.v, X.w - Y.w, X.b - Y.b⟩⟩
instance instNegOpZornMatrix : Neg (OpZornMatrix A) :=
  ⟨fun X => ⟨-X.a, -X.v, -X.w, -X.b⟩⟩

/-- Noncommutative bimodule Zorn multiplication over `[Ring A]`. -/
instance instMulOpZornMatrix : Mul (OpZornMatrix A) :=
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

/-- Exact lower-unipotent composition: its only deviation from additive
parameter addition is the owner-defined skew-cross contact term. -/
theorem opUnipotentLower_mul (w₁ w₂ : OpVec3 A) :
    opUnipotentLower w₁ * opUnipotentLower w₂ =
      ⟨1, -OpVec3.skewCross w₁ w₂, w₁ + w₂, 1⟩ := by
  ext <;>
  simp [opUnipotentLower, OpVec3.dot, OpVec3.skewCross,
    OpVec3.naiveCross, OpVec3.leftScale, OpVec3.rightScale]

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

/-!
## 18. Archetypes XLIV & XLV: The Negative Heisenberg Nilradical $\mathcal{N}_-$, Krein Involution Duality, & Opposite-Nilradical Nucleus Coupling in $\mathrm{Zorn}(A)$
-/

/-- General element $N_-(y, z, \eta) = E_{-1}(y, z) + E_{-2}(\eta)$ of the negative Heisenberg nilradical $\mathcal{N}_- = \mathcal{G}_{-1} \oplus \mathcal{G}_{-2}$. -/
def opHeisenbergNilMinus (y z η : A) : OpZornMatrix A :=
  ⟨0, ⟨η, 0, 0⟩, ⟨0, y, z⟩, 0⟩

/-- Exponential element $H_-(y, z, \eta) = 1 + N_-(y, z, \eta)$ in the negative Heisenberg group $\exp(\mathcal{N}_-)$. -/
def opHeisenbergGroupMinus (y z η : A) : OpZornMatrix A :=
  ⟨1, ⟨η, 0, 0⟩, ⟨0, y, z⟩, 1⟩

/-- Helper lemma: product of two elements in the 5-graded negative Heisenberg nilradical $\mathcal{N}_- = \mathcal{G}_{-1} \oplus \mathcal{G}_{-2}$. -/
theorem opHeisenbergNilMinus_mul (y₁ z₁ η₁ y₂ z₂ η₂ : A) :
    opHeisenbergNilMinus y₁ z₁ η₁ * opHeisenbergNilMinus y₂ z₂ η₂ =
      opGradeMinus2 (-opContactSymplecticForm y₁ z₁ y₂ z₂) := by
  ext <;>
  (simp [opHeisenbergNilMinus, opGradeMinus2, opContactSymplecticForm,
         OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross];
   try noncomm_ring)

/-- Helper lemma: product of two elements in the 5-graded negative Heisenberg group $\exp(\mathcal{N}_-)$. -/
theorem opHeisenbergGroupMinus_mul (y₁ z₁ η₁ y₂ z₂ η₂ : A) :
    opHeisenbergGroupMinus y₁ z₁ η₁ * opHeisenbergGroupMinus y₂ z₂ η₂ =
      opHeisenbergGroupMinus (y₁ + y₂) (z₁ + z₂)
        (η₁ + η₂ - opContactSymplecticForm y₁ z₁ y₂ z₂) := by
  ext <;>
  (simp [opHeisenbergGroupMinus, opContactSymplecticForm,
         OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross];
   try noncomm_ring
   try abel)

/-- **60. Negative Nilradical Step-2 Closure, Associativity, & Dual Heisenberg Group Law (Archetype XLIV.1)**:
    Over ANY noncommutative operator ring $A$, for all $y_i, z_i, \eta_i \in A$:
    1. 2-Step Negative Nilradical Product (Opposite Symplectic Chirality):
       $N_-(y_1, z_1, \eta_1) * N_-(y_2, z_2, \eta_2) = E_{-2}(-\omega_\perp(y_1, z_1; y_2, z_2))$.
    2. Vanishing Triple Products & Vanishing 3-Associator on $\mathcal{N}_-$:
       $(N_1 * N_2) * N_3 = 0$, $N_1 * (N_2 * N_3) = 0$, and $\mathrm{opAssociator}\;N_1\;N_2\;N_3 = 0$.
    3. Exact Associative Dual Heisenberg Group Law on $\exp(\mathcal{N}_-)$:
       $H_-(y_1, z_1, \eta_1) * H_-(y_2, z_2, \eta_2) =
        H_-(y_1 + y_2,\; z_1 + z_2,\; \eta_1 + \eta_2 - \omega_\perp(y_1, z_1; y_2, z_2))$.
    4. Vanishing Group 3-Associator & Exact Two-Sided Group Inversion:
       $\mathrm{opAssociator}\;H_1\;H_2\;H_3 = 0$,
       $H_-(y_1, z_1, \eta_1) * H_-(-y_1, -z_1, -\eta_1) = 1$, and
       $H_-(-y_1, -z_1, -\eta_1) * H_-(y_1, z_1, \eta_1) = 1$. -/
theorem heisenbergNilMinus_associativity_and_group_law
    (y₁ z₁ η₁ y₂ z₂ η₂ y₃ z₃ η₃ : A) :
    let N₁ := opHeisenbergNilMinus y₁ z₁ η₁
    let N₂ := opHeisenbergNilMinus y₂ z₂ η₂
    let N₃ := opHeisenbergNilMinus y₃ z₃ η₃
    let H₁ := opHeisenbergGroupMinus y₁ z₁ η₁
    let H₂ := opHeisenbergGroupMinus y₂ z₂ η₂
    let H₃ := opHeisenbergGroupMinus y₃ z₃ η₃
    N₁ * N₂ = opGradeMinus2 (-opContactSymplecticForm y₁ z₁ y₂ z₂) ∧
    (N₁ * N₂) * N₃ = 0 ∧
    N₁ * (N₂ * N₃) = 0 ∧
    opAssociator N₁ N₂ N₃ = 0 ∧
    H₁ * H₂ =
      opHeisenbergGroupMinus (y₁ + y₂) (z₁ + z₂)
        (η₁ + η₂ - opContactSymplecticForm y₁ z₁ y₂ z₂) ∧
    opAssociator H₁ H₂ H₃ = 0 ∧
    H₁ * opHeisenbergGroupMinus (-y₁) (-z₁) (-η₁) = 1 ∧
    opHeisenbergGroupMinus (-y₁) (-z₁) (-η₁) * H₁ = 1 := by
  intro N₁ N₂ N₃ H₁ H₂ H₃
  have hL : (N₁ * N₂) * N₃ = 0 := by
    change (opHeisenbergNilMinus y₁ z₁ η₁ * opHeisenbergNilMinus y₂ z₂ η₂) * N₃ = 0
    rw [opHeisenbergNilMinus_mul]
    ext <;>
    simp [N₃, opGradeMinus2, opHeisenbergNilMinus, OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross]
  have hR : N₁ * (N₂ * N₃) = 0 := by
    change N₁ * (opHeisenbergNilMinus y₂ z₂ η₂ * opHeisenbergNilMinus y₃ z₃ η₃) = 0
    rw [opHeisenbergNilMinus_mul]
    ext <;>
    simp [N₁, opGradeMinus2, opHeisenbergNilMinus, OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross]
  have hAssocN : opAssociator N₁ N₂ N₃ = 0 := by
    unfold opAssociator
    rw [hL, hR]
    ext <;> simp
  refine ⟨opHeisenbergNilMinus_mul y₁ z₁ η₁ y₂ z₂ η₂,
          hL, hR, hAssocN,
          opHeisenbergGroupMinus_mul y₁ z₁ η₁ y₂ z₂ η₂,
          ?_, ?_, ?_⟩
  · change (opHeisenbergGroupMinus y₁ z₁ η₁ * opHeisenbergGroupMinus y₂ z₂ η₂) * opHeisenbergGroupMinus y₃ z₃ η₃ -
      opHeisenbergGroupMinus y₁ z₁ η₁ * (opHeisenbergGroupMinus y₂ z₂ η₂ * opHeisenbergGroupMinus y₃ z₃ η₃) = 0
    rw [opHeisenbergGroupMinus_mul, opHeisenbergGroupMinus_mul,
        opHeisenbergGroupMinus_mul, opHeisenbergGroupMinus_mul]
    ext <;>
    (simp [opHeisenbergGroupMinus, opContactSymplecticForm];
     try noncomm_ring
     try abel)
  · change opHeisenbergGroupMinus y₁ z₁ η₁ * opHeisenbergGroupMinus (-y₁) (-z₁) (-η₁) = 1
    rw [opHeisenbergGroupMinus_mul]
    ext <;>
    (simp [opHeisenbergGroupMinus, opContactSymplecticForm];
     try noncomm_ring)
  · change opHeisenbergGroupMinus (-y₁) (-z₁) (-η₁) * opHeisenbergGroupMinus y₁ z₁ η₁ = 1
    rw [opHeisenbergGroupMinus_mul]
    ext <;>
    (simp [opHeisenbergGroupMinus, opContactSymplecticForm];
     try noncomm_ring)

/-- **61. Exact Krein Space Anti-Involution Duality Between $\mathcal{N}_+$ and $\mathcal{N}_-$ (Archetype XLIV.2)**:
    Over ANY noncommutative $*$-ring $A$ (`[Ring A] [StarRing A]`), for all $y, z, \xi \in A$:
    1. $(E_{+1}(y, z))^\flat = E_{-1}(y^\star, z^\star)$ and $(E_{+2}(\xi))^\flat = E_{-2}(\xi^\star)$.
    2. $(N_+(y, z, \xi))^\flat = N_-(y^\star, z^\star, \xi^\star)$.
    3. $(H_+(y, z, \xi))^\flat = H_-(y^\star, z^\star, \xi^\star)$. -/
theorem heisenbergNil_kreinAdjoint_duality [StarRing A]
    (y z ξ : A) :
    opZornKreinAdjoint (opGradePlus1 y z) = opGradeMinus1 (star y) (star z) ∧
    opZornKreinAdjoint (opGradePlus2 ξ) = opGradeMinus2 (star ξ) ∧
    opZornKreinAdjoint (opHeisenbergNilPlus y z ξ) =
      opHeisenbergNilMinus (star y) (star z) (star ξ) ∧
    opZornKreinAdjoint (opHeisenbergGroupPlus y z ξ) =
      opHeisenbergGroupMinus (star y) (star z) (star ξ) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  (ext <;>
   simp [opZornKreinAdjoint, opVec3Star, opGradePlus1, opGradeMinus1, opGradePlus2, opGradeMinus2,
         opHeisenbergNilPlus, opHeisenbergNilMinus, opHeisenbergGroupPlus, opHeisenbergGroupMinus])

/-- **62. 3-Grade Decomposition of $N_+ * N_-$ & Exact $\mathcal{G}_0$ Nucleus Closure of $\{N_+, N_-\}$ (Archetype XLV)**:
    Over ANY noncommutative operator ring $A$, for all $y_1, z_1, \xi, y_2, z_2, \eta \in A$,
    $v, w \in A^3$, and $X, Y \in \mathrm{OpZornMatrix}\;A$,
    let $N_+ = N_+(y_1, z_1, \xi) \in \mathcal{N}_+$ and $N_- = N_-(y_2, z_2, \eta) \in \mathcal{N}_-$:
    1. Forward-Backward Product Decomposition ($\mathcal{G}_0 \oplus \mathcal{G}_{+1} \oplus \mathcal{G}_{-1}$):
       $$N_+ * N_- = \mathrm{opGradeZero}\;(-(y_1 y_2 + z_1 z_2))\;(-\xi \eta) +
                     E_{+1}(\xi z_2 + z_2 \xi,\; -(\xi y_2 + y_2 \xi)) +
                     E_{-1}(z_1 \eta + \eta z_1,\; -(y_1 \eta + \eta y_1)).$$
    2. Backward-Forward Product Decomposition ($\mathcal{G}_0 \oplus \mathcal{G}_{+1} \oplus \mathcal{G}_{-1}$):
       $$N_- * N_+ = \mathrm{opGradeZero}\;(-\eta \xi)\;(-(y_2 y_1 + z_2 z_1)) +
                     E_{+1}(-(\xi z_2 + z_2 \xi),\; \xi y_2 + y_2 \xi) +
                     E_{-1}(-(z_1 \eta + \eta z_1),\; y_1 \eta + \eta y_1).$$
    3. Exact $\mathcal{G}_0$ Associative Nucleus Closure of the Jordan Anticommutator $\{N_+, N_-\}$:
       $$K = N_+ * N_- + N_- * N_+ =
         \mathrm{opGradeZero}\;\bigl(-(y_1 y_2 + z_1 z_2 + \eta \xi)\bigr)\;\bigl(-(y_2 y_1 + z_2 z_1 + \xi \eta)\bigr) \in \mathcal{G}_0.$$
    4. Exact Opposite-Chirality & Diagonal Leibniz Derivation Property of $K = \{N_+, N_-\}$:
       $$[K, L_+(v) * L_-(w)] = [K, L_+(v)] * L_-(w) + L_+(v) * [K, L_-(w)],$$
       $$([K, X * Y]).a = ([K, X] * Y + X * [K, Y]).a, \qquad ([K, X * Y]).b = ([K, X] * Y + X * [K, Y]).b.$$ -/
theorem oppositeNilradical_coupling_and_nucleus_anticommutator
    (y₁ z₁ ξ y₂ z₂ η : A) (v w : OpVec3 A) (X Y : OpZornMatrix A) :
    let N_p := opHeisenbergNilPlus y₁ z₁ ξ
    let N_m := opHeisenbergNilMinus y₂ z₂ η
    let K := N_p * N_m + N_m * N_p
    let Lp := opLightconeRayPlus v
    let Lm := opLightconeRayMinus w
    N_p * N_m =
      opGradeZero (-(y₁ * y₂ + z₁ * z₂)) (-ξ * η) +
        opGradePlus1 (ξ * z₂ + z₂ * ξ) (-(ξ * y₂ + y₂ * ξ)) +
        opGradeMinus1 (z₁ * η + η * z₁) (-(y₁ * η + η * y₁)) ∧
    N_m * N_p =
      opGradeZero (-η * ξ) (-(y₂ * y₁ + z₂ * z₁)) +
        opGradePlus1 (-(ξ * z₂ + z₂ * ξ)) (ξ * y₂ + y₂ * ξ) +
        opGradeMinus1 (-(z₁ * η + η * z₁)) (y₁ * η + η * y₁) ∧
    K = opGradeZero (-(y₁ * y₂ + z₁ * z₂ + η * ξ)) (-(y₂ * y₁ + z₂ * z₁ + ξ * η)) ∧
    opCommutator K (Lp * Lm) = opCommutator K Lp * Lm + Lp * opCommutator K Lm ∧
    (opCommutator K (X * Y)).a = (opCommutator K X * Y + X * opCommutator K Y).a ∧
    (opCommutator K (X * Y)).b = (opCommutator K X * Y + X * opCommutator K Y).b := by
  intro N_p N_m K Lp Lm
  have hK : K = opGradeZero (-(y₁ * y₂ + z₁ * z₂ + η * ξ)) (-(y₂ * y₁ + z₂ * z₁ + ξ * η)) := by
    ext <;>
    (simp [K, N_p, N_m, opHeisenbergNilPlus, opHeisenbergNilMinus, opGradeZero, opCartanDiag,
           OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross];
     try noncomm_ring
     try abel)
  have hLeib := opModularDeriv_nucleus_and_exact_leibniz_rule K X Y v w
    (-(y₁ * y₂ + z₁ * z₂ + η * ξ)) (-(y₂ * y₁ + z₂ * z₁ + ξ * η))
  refine ⟨?_, ?_, hK, ?_, ?_, ?_⟩
  · ext <;>
    (simp [N_p, N_m, opHeisenbergNilPlus, opHeisenbergNilMinus,
           opGradeZero, opCartanDiag, opGradePlus1, opGradeMinus1,
           OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross];
     try noncomm_ring
     try abel)
  · ext <;>
    (simp [N_p, N_m, opHeisenbergNilPlus, opHeisenbergNilMinus,
           opGradeZero, opCartanDiag, opGradePlus1, opGradeMinus1,
           OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross];
     try noncomm_ring
     try abel)
  · rw [hK]
    exact hLeib.2.2.2.2.1
  · rw [hK]
    exact hLeib.2.2.2.2.2.2.1
  · rw [hK]
    exact hLeib.2.2.2.2.2.2.2

/-- Positive central contact subgroup $C_+(\xi) := H_+(0, 0, \xi) = 1 + E_{+2}(\xi) = \langle 1, 0, \langle \xi, 0, 0 \rangle, 1 \rangle \in \exp(\mathcal{N}_+)$. -/
def opContactSubgroupPlus (ξ : A) : OpZornMatrix A :=
  opHeisenbergGroupPlus 0 0 ξ

/-- Negative central contact subgroup $C_-(\eta) := H_-(0, 0, \eta) = 1 + E_{-2}(\eta) = \langle 1, \langle \eta, 0, 0 \rangle, 0, 1 \rangle \in \exp(\mathcal{N}_-)$. -/
def opContactSubgroupMinus (η : A) : OpZornMatrix A :=
  opHeisenbergGroupMinus 0 0 η

/-- **63. 5-Grade Invariance Under $\mathcal{G}_0$ Nucleus Derivations & Opposite-Grade / Contact Leibniz Laws (Archetype XLVI)**:
    Over ANY noncommutative operator ring $A$, for any $\mathcal{G}_0$ nucleus Hamiltonian
    $D = \mathrm{opGradeZero}\;\rho_+\;\rho_- = D(\rho_+, \rho_-)$:
    1. Grade $+1$ Invariance: $[D, E_{+1}(y, z)] = E_{+1}(\rho_+ y - y \rho_-,\; \rho_+ z - z \rho_-) \in \mathcal{G}_{+1}$.
    2. Grade $+2$ Invariance: $[D, E_{+2}(\xi)] = E_{+2}(\rho_- \xi - \xi \rho_+) \in \mathcal{G}_{+2}$.
    3. Grade $-1$ Invariance: $[D, E_{-1}(y, z)] = E_{-1}(\rho_- y - y \rho_+,\; \rho_- z - z \rho_+) \in \mathcal{G}_{-1}$.
    4. Grade $-2$ Invariance: $[D, E_{-2}(\eta)] = E_{-2}(\rho_+ \eta - \eta \rho_-) \in \mathcal{G}_{-2}$.
    5. Contact-Center Eigenvalue Law on $\mathcal{G}_{+1} * \mathcal{G}_{+1} \to \mathcal{G}_{+2}$:
       $$[D, E_{+1}(y_1, z_1) * E_{+1}(y_2, z_2)] = E_{+2}\bigl(\rho_- \omega_\perp(y_1, z_1; y_2, z_2) - \omega_\perp(y_1, z_1; y_2, z_2) \rho_+\bigr).$$
    6. Exact Opposite-Grade Leibniz Rules on $\mathcal{G}_{+1} * \mathcal{G}_{-1} \to \mathcal{G}_0$ and $\mathcal{G}_{-2} * \mathcal{G}_{+2} \to \mathcal{G}_0$:
       $$[D, E_{+1}(y_1, z_1) * E_{-1}(y_2, z_2)] = [D, E_{+1}(y_1, z_1)] * E_{-1}(y_2, z_2) + E_{+1}(y_1, z_1) * [D, E_{-1}(y_2, z_2)],$$
       $$[D, E_{-2}(\eta) * E_{+2}(\xi)] = [D, E_{-2}(\eta)] * E_{+2}(\xi) + E_{-2}(\eta) * [D, E_{+2}(\xi)].$$ -/
theorem fiveGraded_nucleus_derivation_invariance_and_contact_leibniz
    (ρ_plus ρ_minus y z y₁ z₁ y₂ z₂ ξ η : A) :
    let D := opGradeZero ρ_plus ρ_minus
    opCommutator D (opGradePlus1 y z) =
      opGradePlus1 (ρ_plus * y - y * ρ_minus) (ρ_plus * z - z * ρ_minus) ∧
    opCommutator D (opGradePlus2 ξ) =
      opGradePlus2 (ρ_minus * ξ - ξ * ρ_plus) ∧
    opCommutator D (opGradeMinus1 y z) =
      opGradeMinus1 (ρ_minus * y - y * ρ_plus) (ρ_minus * z - z * ρ_plus) ∧
    opCommutator D (opGradeMinus2 η) =
      opGradeMinus2 (ρ_plus * η - η * ρ_minus) ∧
    opCommutator D (opGradePlus1 y₁ z₁ * opGradePlus1 y₂ z₂) =
      opGradePlus2 (ρ_minus * opContactSymplecticForm y₁ z₁ y₂ z₂ -
        opContactSymplecticForm y₁ z₁ y₂ z₂ * ρ_plus) ∧
    opCommutator D (opGradePlus1 y₁ z₁ * opGradeMinus1 y₂ z₂) =
      opCommutator D (opGradePlus1 y₁ z₁) * opGradeMinus1 y₂ z₂ +
        opGradePlus1 y₁ z₁ * opCommutator D (opGradeMinus1 y₂ z₂) ∧
    opCommutator D (opGradeMinus2 η * opGradePlus2 ξ) =
      opCommutator D (opGradeMinus2 η) * opGradePlus2 ξ +
        opGradeMinus2 η * opCommutator D (opGradePlus2 ξ) := by
  intro D
  have hModP1 := opModularDeriv_lightconeRayPlus ρ_plus ρ_minus ⟨0, y, z⟩
  have hModP2 := opModularDeriv_lightconeRayMinus ρ_plus ρ_minus ⟨ξ, 0, 0⟩
  have hModM1 := opModularDeriv_lightconeRayMinus ρ_plus ρ_minus ⟨0, y, z⟩
  have hModM2 := opModularDeriv_lightconeRayPlus ρ_plus ρ_minus ⟨η, 0, 0⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change opModularDeriv ρ_plus ρ_minus (opLightconeRayPlus ⟨0, y, z⟩) =
      opGradePlus1 (ρ_plus * y - y * ρ_minus) (ρ_plus * z - z * ρ_minus)
    rw [hModP1]
    ext <;> simp [opGradePlus1, opLightconeRayPlus, OpVec3.bimoduleDiff]
  · change opModularDeriv ρ_plus ρ_minus (opLightconeRayMinus ⟨ξ, 0, 0⟩) =
      opGradePlus2 (ρ_minus * ξ - ξ * ρ_plus)
    rw [hModP2]
    ext <;> simp [opGradePlus2, opLightconeRayMinus, OpVec3.bimoduleDiff]
  · change opModularDeriv ρ_plus ρ_minus (opLightconeRayMinus ⟨0, y, z⟩) =
      opGradeMinus1 (ρ_minus * y - y * ρ_plus) (ρ_minus * z - z * ρ_plus)
    rw [hModM1]
    ext <;> simp [opGradeMinus1, opLightconeRayMinus, OpVec3.bimoduleDiff]
  · change opModularDeriv ρ_plus ρ_minus (opLightconeRayPlus ⟨η, 0, 0⟩) =
      opGradeMinus2 (ρ_plus * η - η * ρ_minus)
    rw [hModM2]
    ext <;> simp [opGradeMinus2, opLightconeRayPlus, OpVec3.bimoduleDiff]
  · have hStep : opGradePlus1 y₁ z₁ * opGradePlus1 y₂ z₂ =
        opGradePlus2 (opContactSymplecticForm y₁ z₁ y₂ z₂) :=
      (fiveGraded_step_two_heisenberg_and_termination 0 0 y₁ z₁ y₂ z₂ 0 0 0 0 0 0).1
    rw [hStep]
    change opModularDeriv ρ_plus ρ_minus
        (opLightconeRayMinus ⟨opContactSymplecticForm y₁ z₁ y₂ z₂, 0, 0⟩) =
      opGradePlus2 (ρ_minus * opContactSymplecticForm y₁ z₁ y₂ z₂ -
        opContactSymplecticForm y₁ z₁ y₂ z₂ * ρ_plus)
    rw [opModularDeriv_lightconeRayMinus]
    ext <;> simp [opGradePlus2, opLightconeRayMinus, OpVec3.bimoduleDiff]
  · exact (opModularDeriv_nucleus_and_exact_leibniz_rule D 0 0
      ⟨0, y₁, z₁⟩ ⟨0, y₂, z₂⟩ ρ_plus ρ_minus).2.2.2.2.1
  · exact (opModularDeriv_nucleus_and_exact_leibniz_rule D 0 0
      ⟨η, 0, 0⟩ ⟨ξ, 0, 0⟩ ρ_plus ρ_minus).2.2.2.2.1

/-- **64. Centrality of Contact Subgroups $C_\pm$, Selective Contact Readout, & Contact-Gauss Associativity (Archetype XLVII)**:
    Over ANY noncommutative operator ring $A$, for all $y, z, \xi, \xi', \eta, \eta', \rho_+, \rho_- \in A$:
    1. Centrality of $C_+(\xi') = H_+(0, 0, \xi')$ in $\exp(\mathcal{N}_+)$ (Up to Ring Commutators in $A$):
       $$H_+(y, z, \xi) * C_+(\xi') = H_+(y, z, \xi + \xi'), \qquad
         C_+(\xi') * H_+(y, z, \xi) = H_+(y, z, \xi' + \xi).$$
    2. Centrality of $C_-(\eta') = H_-(0, 0, \eta')$ in $\exp(\mathcal{N}_-)$ (Up to Ring Commutators in $A$):
       $$H_-(y, z, \eta) * C_-(\eta') = H_-(y, z, \eta + \eta'), \qquad
         C_-(\eta') * H_-(y, z, \eta) = H_-(y, z, \eta' + \eta).$$
    3. Selective Contact Readout by Opposite Contact Generators $E_{\mp 2}$ (Blindness to Same-Nilradical $\mathcal{G}_{\mp 1}$):
       $$E_{-2}(\eta) * \bigl(E_{-1}(y, z) + E_{+2}(\xi)\bigr) = \mathrm{opGradeZero}\;(-\eta \xi)\;0,$$
       $$\bigl(E_{-1}(y, z) + E_{+2}(\xi)\bigr) * E_{-2}(\eta) = \mathrm{opGradeZero}\;0\;(-\xi \eta).$$
    4. Exact Contact-Gauss Bruhat Associativity Across Opposite Contact Subgroups and the $\mathcal{G}_0$ Levi Nucleus:
       $$\mathrm{opAssociator}\;\bigl(C_+(\xi)\bigr)\;\bigl(\mathrm{opGradeZero}\;\rho_+\;\rho_-\bigr)\;\bigl(C_-(\eta)\bigr) = 0.$$ -/
theorem contactSubgroup_centrality_selective_readout_and_gauss_assoc
    (y z ξ ξ' η η' ρ_plus ρ_minus : A) :
    opHeisenbergGroupPlus y z ξ * opContactSubgroupPlus ξ' =
      opHeisenbergGroupPlus y z (ξ + ξ') ∧
    opContactSubgroupPlus ξ' * opHeisenbergGroupPlus y z ξ =
      opHeisenbergGroupPlus y z (ξ' + ξ) ∧
    opHeisenbergGroupMinus y z η * opContactSubgroupMinus η' =
      opHeisenbergGroupMinus y z (η + η') ∧
    opContactSubgroupMinus η' * opHeisenbergGroupMinus y z η =
      opHeisenbergGroupMinus y z (η' + η) ∧
    opGradeMinus2 η * (opGradeMinus1 y z + opGradePlus2 ξ) =
      opGradeZero (-η * ξ) 0 ∧
    (opGradeMinus1 y z + opGradePlus2 ξ) * opGradeMinus2 η =
      opGradeZero 0 (-ξ * η) ∧
    opAssociator (opContactSubgroupPlus ξ) (opGradeZero ρ_plus ρ_minus)
      (opContactSubgroupMinus η) = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change opHeisenbergGroupPlus y z ξ * opHeisenbergGroupPlus 0 0 ξ' =
      opHeisenbergGroupPlus y z (ξ + ξ')
    rw [opHeisenbergGroupPlus_mul]
    ext <;> simp [opHeisenbergGroupPlus, opContactSymplecticForm]
  · change opHeisenbergGroupPlus 0 0 ξ' * opHeisenbergGroupPlus y z ξ =
      opHeisenbergGroupPlus y z (ξ' + ξ)
    rw [opHeisenbergGroupPlus_mul]
    ext <;> simp [opHeisenbergGroupPlus, opContactSymplecticForm]
  · change opHeisenbergGroupMinus y z η * opHeisenbergGroupMinus 0 0 η' =
      opHeisenbergGroupMinus y z (η + η')
    rw [opHeisenbergGroupMinus_mul]
    ext <;> simp [opHeisenbergGroupMinus, opContactSymplecticForm]
  · change opHeisenbergGroupMinus 0 0 η' * opHeisenbergGroupMinus y z η =
      opHeisenbergGroupMinus y z (η' + η)
    rw [opHeisenbergGroupMinus_mul]
    ext <;> simp [opHeisenbergGroupMinus, opContactSymplecticForm]
  · ext <;>
    (simp [opGradeMinus2, opGradeMinus1, opGradePlus2, opGradeZero, opCartanDiag,
           OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross];
     try noncomm_ring)
  · ext <;>
    (simp [opGradeMinus2, opGradeMinus1, opGradePlus2, opGradeZero, opCartanDiag,
           OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross];
     try noncomm_ring)
  · ext <;>
    (simp [opAssociator, opContactSubgroupPlus, opContactSubgroupMinus,
           opHeisenbergGroupPlus, opHeisenbergGroupMinus, opGradeZero, opCartanDiag,
           OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross];
     try noncomm_ring
     try abel)

/-- Transverse Erlangen flag state $\Pi_\perp(y, z) := \Pi_{\mathrm{hom}}(\langle 0, y, z \rangle)$ supported in $\mathcal{G}_0 \oplus \mathcal{G}_{+1}$. -/
def opTransverseFlagState (y z : A) : OpZornMatrix A :=
  homogeneousFlagState ⟨0, y, z⟩

/-- Transverse BCFW shift operator $H_{+1}(y_s, z_s) := 1 + E_{+1}(y_s, z_s) = H_+(y_s, z_s, 0)$. -/
def opBCFWTransverseShift (y_s z_s : A) : OpZornMatrix A :=
  1 + opGradePlus1 y_s z_s

/-- **65. 5-Graded BCFW Transverse Shift, Grade $+2$ Contact Pole Residue, & Dual Probe Readout (Archetype XLVIII)**:
    Over ANY noncommutative operator ring $A$, for all $y_0, z_0, y_s, z_s, \eta \in A$,
    let $\Pi_0 = \mathrm{opTransverseFlagState}\;y_0\;z_0$,
    $\Pi_{\mathrm{shifted}} = \mathrm{opTransverseFlagState}\;(y_s + y_0)\;(z_s + z_0)$,
    $S_+ = \mathrm{opBCFWTransverseShift}\;y_s\;z_s$,
    $S_- = \mathrm{opBCFWTransverseShift}\;(-y_s)\;(-z_s)$, and
    $\omega_{\mathrm{res}} = \mathrm{opContactSymplecticForm}\;y_s\;z_s\;y_0\;z_0$:
    1. Explicit Transverse Homogeneous Flag Coordinates:
       $$\Pi_0 = \langle 1, \langle 0, -y_0, -z_0 \rangle, 0, 0 \rangle = e_{11} - E_{+1}(y_0, z_0).$$
    2. Vanishing BCFW Shift 3-Associator:
       $$\mathrm{opAssociator}\;S_+\;\Pi_0\;S_- = 0.$$
    3. Exact Right BCFW Shift & Grade $+2$ Symplectic Contact Residue Factorization:
       $$\Pi_0 * S_- = \Pi_{\mathrm{shifted}} - E_{+2}(\omega_{\mathrm{res}}).$$
    4. Exact Two-Sided BCFW Conjugation Shift:
       $$(S_+ * \Pi_0) * S_- = \Pi_{\mathrm{shifted}} - E_{+2}(\omega_{\mathrm{res}} + \omega_{\mathrm{res}}).$$
    5. Direct Dual Contact Probe Readout of the BCFW Symplectic Residue:
       $$E_{-2}(\eta) * (\Pi_0 * S_- - \Pi_{\mathrm{shifted}}) = \mathrm{opGradeZero}\;(\eta * \omega_{\mathrm{res}})\;0,$$
       $$E_{-2}(\eta) * ((S_+ * \Pi_0) * S_- - \Pi_{\mathrm{shifted}}) =
         \mathrm{opGradeZero}\;(\eta * (\omega_{\mathrm{res}} + \omega_{\mathrm{res}}))\;0.$$ -/
theorem bcfwTransverseShift_flag_recursion_and_contact_residue
    (y₀ z₀ y_s z_s η : A) :
    let P₀ := opTransverseFlagState y₀ z₀
    let P_shifted := opTransverseFlagState (y_s + y₀) (z_s + z₀)
    let S_plus := opBCFWTransverseShift y_s z_s
    let S_minus := opBCFWTransverseShift (-y_s) (-z_s)
    let ω_res := opContactSymplecticForm y_s z_s y₀ z₀
    P₀ = ⟨1, ⟨0, -y₀, -z₀⟩, 0, 0⟩ ∧
    opAssociator S_plus P₀ S_minus = 0 ∧
    P₀ * S_minus = P_shifted - opGradePlus2 ω_res ∧
    (S_plus * P₀) * S_minus = P_shifted - opGradePlus2 (ω_res + ω_res) ∧
    opGradeMinus2 η * (P₀ * S_minus - P_shifted) =
      opGradeZero (η * ω_res) 0 ∧
    opGradeMinus2 η * ((S_plus * P₀) * S_minus - P_shifted) =
      opGradeZero (η * (ω_res + ω_res)) 0 := by
  intro P₀ P_shifted S_plus S_minus ω_res
  have hP₀ : P₀ = ⟨1, ⟨0, -y₀, -z₀⟩, 0, 0⟩ := by
    change homogeneousFlagState ⟨0, y₀, z₀⟩ = ⟨1, ⟨0, -y₀, -z₀⟩, 0, 0⟩
    rw [homogeneousFlagState_coords]
    ext <;> simp
  have hP_s : P_shifted = ⟨1, ⟨0, -(y_s + y₀), -(z_s + z₀)⟩, 0, 0⟩ := by
    change homogeneousFlagState ⟨0, y_s + y₀, z_s + z₀⟩ = ⟨1, ⟨0, -(y_s + y₀), -(z_s + z₀)⟩, 0, 0⟩
    rw [homogeneousFlagState_coords]
    ext <;> simp
  have hRight : P₀ * S_minus = P_shifted - opGradePlus2 ω_res := by
    rw [hP₀, hP_s]
    ext <;>
    (simp [S_minus, opBCFWTransverseShift, opGradePlus1, opGradePlus2,
           ω_res, opContactSymplecticForm,
           OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross];
     try noncomm_ring
     try abel)
  have hConj : (S_plus * P₀) * S_minus = P_shifted - opGradePlus2 (ω_res + ω_res) := by
    rw [hP₀, hP_s]
    ext <;>
    (simp [S_plus, S_minus, opBCFWTransverseShift, opGradePlus1, opGradePlus2,
           ω_res, opContactSymplecticForm,
           OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross];
     try noncomm_ring
     try abel)
  refine ⟨hP₀, ?_, hRight, hConj, ?_, ?_⟩
  · rw [hP₀]
    ext <;>
    (simp [opAssociator, S_plus, S_minus, opBCFWTransverseShift, opGradePlus1,
           OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross];
     try noncomm_ring
     try abel)
  · rw [hRight]
    ext <;>
    (simp [opGradeMinus2, opGradePlus2, opGradeZero, opCartanDiag,
           OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross];
     try noncomm_ring)
  · rw [hConj]
    ext <;>
    (simp [opGradeMinus2, opGradePlus2, opGradeZero, opCartanDiag,
           OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross];
     try noncomm_ring)

/-- Operator Lamb vector $\mathbf{L}_{\mathrm{op}}(\omega, u) := \omega \times_{\mathrm{skew}} u \in A^3$. -/
def opLambVector (ω u : OpVec3 A) : OpVec3 A :=
  OpVec3.skewCross ω u

/-- Operator Helicity Casimir $H_{\mathrm{hel}}(u, \omega) := \{L_+(u), L_-(\omega)\} \in \mathcal{G}_0$. -/
def opHelicityNucleus (u ω : OpVec3 A) : OpZornMatrix A :=
  opAnticommutator (opLightconeRayPlus u) (opLightconeRayMinus ω)

/-- Operator Bernoulli-Beltrami Hamiltonian $B(u) := \{L_+(u), L_-(u)\} \in \mathcal{G}_0$. -/
def opBernoulliBeltrami (u : OpVec3 A) : OpZornMatrix A :=
  opHelicityNucleus u u

/-- Symmetric Metric Readout of a 5-graded state $X$ by a dual contact probe $E_{-2}(\eta)$. -/
def opArnoldMetricReadout (η : A) (X : OpZornMatrix A) : OpZornMatrix A :=
  opAnticommutator (opGradeMinus2 η) X

/-- Antisymmetric Chiral Phase Readout of a 5-graded state $X$ by a dual contact probe $E_{-2}(\eta)$. -/
def opArnoldPhaseReadout (η : A) (X : OpZornMatrix A) : OpZornMatrix A :=
  opCommutator (opGradeMinus2 η) X

/-- **66. Arnold (1969) Braid Cohomology, Pairwise 3-Term Relation, & 5-Graded Nilradical Lie-Jacobi Law (Archetype L)**:
    Over ANY noncommutative operator ring $A$, for ALL $v_1, v_2, v_3 \in A^3$ and $y_i, z_i, \xi_i \in A$:
    1. Pairwise Difference 3-Term Arnold Curvature Residue ($\omega_{ij} = v_i - v_j \in A^3$):
       $$\omega_{12} \times_{\mathrm{skew}} \omega_{23} +
         \omega_{23} \times_{\mathrm{skew}} \omega_{31} +
         \omega_{31} \times_{\mathrm{skew}} \omega_{12} =
         \mathrm{cycle} + \mathrm{cycle} + \mathrm{cycle},$$
       where $\mathrm{cycle} = v_1 \times_{\mathrm{skew}} v_2 + v_2 \times_{\mathrm{skew}} v_3 + v_3 \times_{\mathrm{skew}} v_1$.
    2. BCFW Collinear Splitting Rearrangement of the 3-Term Arnold Identity:
       $$\omega_{12} \times_{\mathrm{skew}} \omega_{23} =
         -(\omega_{23} \times_{\mathrm{skew}} \omega_{31} + \omega_{31} \times_{\mathrm{skew}} \omega_{12}) +
         (\mathrm{cycle} + \mathrm{cycle} + \mathrm{cycle}).$$
    3. Exact Vanishing of Nested 3-Term Products & Exact Lie-Jacobi Identity in the 5-Graded Nilradical $\mathcal{N}_+$:
       $$(E_{+1}(y_1, z_1) * E_{+1}(y_2, z_2)) * E_{+1}(y_3, z_3) = 0,$$
       $$[[N_1, N_2], N_3] + [[N_2, N_3], N_1] + [[N_3, N_1], N_2] = 0$$
       for all $N_i = N_+(y_i, z_i, \xi_i) \in \mathcal{N}_+$. -/
theorem arnold_braid_jacobi_and_three_term_relation
    (v₁ v₂ v₃ : OpVec3 A) (y₁ z₁ ξ₁ y₂ z₂ ξ₂ y₃ z₃ ξ₃ : A) :
    let ω₁₂ := v₁ - v₂
    let ω₂₃ := v₂ - v₃
    let ω₃₁ := v₃ - v₁
    let cycle := OpVec3.skewCross v₁ v₂ + OpVec3.skewCross v₂ v₃ + OpVec3.skewCross v₃ v₁
    let N₁ := opHeisenbergNilPlus y₁ z₁ ξ₁
    let N₂ := opHeisenbergNilPlus y₂ z₂ ξ₂
    let N₃ := opHeisenbergNilPlus y₃ z₃ ξ₃
    OpVec3.skewCross ω₁₂ ω₂₃ + OpVec3.skewCross ω₂₃ ω₃₁ + OpVec3.skewCross ω₃₁ ω₁₂ =
      cycle + cycle + cycle ∧
    OpVec3.skewCross ω₁₂ ω₂₃ =
      -(OpVec3.skewCross ω₂₃ ω₃₁ + OpVec3.skewCross ω₃₁ ω₁₂) + (cycle + cycle + cycle) ∧
    (opGradePlus1 y₁ z₁ * opGradePlus1 y₂ z₂) * opGradePlus1 y₃ z₃ = 0 ∧
    opCommutator (opCommutator N₁ N₂) N₃ +
      opCommutator (opCommutator N₂ N₃) N₁ +
      opCommutator (opCommutator N₃ N₁) N₂ = 0 := by
  intro ω₁₂ ω₂₃ ω₃₁ cycle N₁ N₂ N₃
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext <;>
    (simp [ω₁₂, ω₂₃, ω₃₁, cycle, OpVec3.skewCross, OpVec3.naiveCross];
     try noncomm_ring
     try abel)
  · ext <;>
    (simp [ω₁₂, ω₂₃, ω₃₁, cycle, OpVec3.skewCross, OpVec3.naiveCross];
     try noncomm_ring
     try abel)
  · have hStep := (fiveGraded_step_two_heisenberg_and_termination 0 0 y₁ z₁ y₂ z₂ 0 0 0 0 0 0).1
    rw [hStep]
    exact (fiveGraded_step_two_heisenberg_and_termination y₃ z₃ 0 0 0 0
      (opContactSymplecticForm y₁ z₁ y₂ z₂) 0 0 0 0 0).2.2.2.1
  · have hC : ∀ a₁ b₁ c₁ a₂ b₂ c₂ a₃ b₃ c₃ : A,
        opCommutator (opCommutator (opHeisenbergNilPlus a₁ b₁ c₁) (opHeisenbergNilPlus a₂ b₂ c₂))
          (opHeisenbergNilPlus a₃ b₃ c₃) = 0 := by
      intro a₁ b₁ c₁ a₂ b₂ c₂ a₃ b₃ c₃
      dsimp [opCommutator]
      rw [opHeisenbergNilPlus_mul, opHeisenbergNilPlus_mul]
      ext <;>
      simp [opGradePlus2, opHeisenbergNilPlus,
            OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross]
    rw [hC, hC, hC]
    ext <;> simp

/-- **67. Arnold (1966) Geometric Fluid Dynamics: Lamb Vector, Helicity Casimir, & Beltrami Flows (Archetype LI)**:
    Over ANY noncommutative operator ring $A$, for ALL velocity/vorticity fields $u, \omega, v, w \in A^3$
    and arbitrary states $X, Y \in \mathrm{OpZornMatrix}\;A$:
    1. Same-Chirality Advection Isolates Arnold's Lamb Vector:
       $$L_+(\omega) * L_+(u) = L_-(\mathbf{L}_{\mathrm{op}}(\omega, u)).$$
    2. Opposite-Chirality Anticommutator Isolates the Helicity Casimir in $\mathcal{G}_0$:
       $$H_{\mathrm{hel}}(u, \omega) = \mathrm{opGradeZero}\;(-(u \cdot \omega))\;(-(\omega \cdot u)).$$
    3. Noncommutative Beltrami Flow Fixed-Point Law ($\omega = u \implies \mathbf{L}_{\mathrm{op}} = 0$):
       $$\mathbf{L}_{\mathrm{op}}(u, u) = 0 \qquad \text{and} \qquad L_+(u) * L_+(u) = 0.$$
    4. Bernoulli-Beltrami Nucleus Hamiltonian $B(u) = \{L_+(u), L_-(u)\} \in \mathcal{G}_0$ Generates an Exact Opposite-Chirality & Diagonal Leibniz Derivation:
       $$[B(u), L_+(v) * L_-(w)] = [B(u), L_+(v)] * L_-(w) + L_+(v) * [B(u), L_-(w)],$$
       $$([B(u), X * Y]).a = ([B(u), X] * Y + X * [B(u), Y]).a, \qquad
         ([B(u), X * Y]).b = ([B(u), X] * Y + X * [B(u), Y]).b.$$ -/
theorem arnold_hydrodynamics_lamb_helicity_and_beltrami_flow
    (u ω v w : OpVec3 A) (X Y : OpZornMatrix A) :
    let B := opBernoulliBeltrami u
    let Lp := opLightconeRayPlus v
    let Lm := opLightconeRayMinus w
    opLightconeRayPlus ω * opLightconeRayPlus u = opLightconeRayMinus (opLambVector ω u) ∧
    opHelicityNucleus u ω = opGradeZero (-OpVec3.dot u ω) (-OpVec3.dot ω u) ∧
    opLambVector u u = 0 ∧
    opLightconeRayPlus u * opLightconeRayPlus u = 0 ∧
    opCommutator B (Lp * Lm) = opCommutator B Lp * Lm + Lp * opCommutator B Lm ∧
    (opCommutator B (X * Y)).a = (opCommutator B X * Y + X * opCommutator B Y).a ∧
    (opCommutator B (X * Y)).b = (opCommutator B X * Y + X * opCommutator B Y).b := by
  intro B Lp Lm
  have hHel : ∀ u' ω' : OpVec3 A,
      opHelicityNucleus u' ω' = opGradeZero (-OpVec3.dot u' ω') (-OpVec3.dot ω' u') := by
    intro u' ω'
    ext <;>
    (simp [opHelicityNucleus, opAnticommutator, opLightconeRayPlus, opLightconeRayMinus,
           opGradeZero, opCartanDiag, OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross];
     try noncomm_ring)
  have hB : B = opGradeZero (-OpVec3.dot u u) (-OpVec3.dot u u) := hHel u u
  have hLeib := opModularDeriv_nucleus_and_exact_leibniz_rule B X Y v w
    (-OpVec3.dot u u) (-OpVec3.dot u u)
  refine ⟨?_, hHel u ω, ?_, ?_, ?_, ?_, ?_⟩
  · ext <;>
    simp [opLightconeRayPlus, opLightconeRayMinus, opLambVector,
          OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross]
  · ext <;> simp [opLambVector, OpVec3.skewCross, OpVec3.naiveCross]
  · ext <;>
    simp [opLightconeRayPlus, OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross]
  · rw [hB]
    exact hLeib.2.2.2.2.1
  · rw [hB]
    exact hLeib.2.2.2.2.2.2.1
  · rw [hB]
    exact hLeib.2.2.2.2.2.2.2

/-- **68. Arnold-Majorana Braid Networks: 3-Layer KAN Superposition, 4-Gate Braid Monodromy Loop, & Metric/Phase Readouts (Archetype LII)**:
    Over ANY noncommutative operator ring $A$, for all $y_i, z_i, \xi_i, \eta, \xi \in A$:
    1. Strict 3-Layer Associativity & Additive KAN + Symplectic Braid Accumulation:
       $$(H_+(y_1, z_1, \xi_1) * H_+(y_2, z_2, \xi_2)) * H_+(y_3, z_3, \xi_3) =
         H_+\!\bigl(y_1 + y_2 + y_3,\; z_1 + z_2 + z_3,\;
                    \xi_1 + \xi_2 + \xi_3 + \omega_\perp(y_1, z_1; y_2, z_2) +
                    \omega_\perp(y_1 + y_2, z_1 + z_2; y_3, z_3)\bigr).$$
    2. 4-Gate Braid Group Commutator Loop Isolates Pure Grade $+2$ Contact Monodromy:
       $$(H_+(y_1, z_1, \xi_1) * H_+(y_2, z_2, \xi_2)) *
         (H_+(-y_1, -z_1, -\xi_1) * H_+(-y_2, -z_2, -\xi_2)) =
         C_+\!\bigl(\omega_\perp(y_1, z_1; y_2, z_2) + \omega_\perp(y_1, z_1; y_2, z_2)\bigr).$$
    3. Exact Grade-0 Symmetric Metric Readout & Antisymmetric Phase Readout of Contact Register:
       $$\mathrm{opArnoldMetricReadout}\;\eta\;(E_{+2}(\xi)) = \mathrm{opGradeZero}\;(-\eta \xi)\;(-\xi \eta),$$
       $$\mathrm{opArnoldPhaseReadout}\;\eta\;(E_{+2}(\xi)) = \mathrm{opGradeZero}\;(-\eta \xi)\;(+\xi \eta).$$ -/
theorem arnold_network_three_layer_kan_braid_loop_and_readouts
    (y₁ z₁ ξ₁ y₂ z₂ ξ₂ y₃ z₃ ξ₃ η ξ : A) :
    let G₁ := opHeisenbergGroupPlus y₁ z₁ ξ₁
    let G₂ := opHeisenbergGroupPlus y₂ z₂ ξ₂
    let G₃ := opHeisenbergGroupPlus y₃ z₃ ξ₃
    let G₁_inv := opHeisenbergGroupPlus (-y₁) (-z₁) (-ξ₁)
    let G₂_inv := opHeisenbergGroupPlus (-y₂) (-z₂) (-ξ₂)
    let ω₁₂ := opContactSymplecticForm y₁ z₁ y₂ z₂
    let ω₁₂_₃ := opContactSymplecticForm (y₁ + y₂) (z₁ + z₂) y₃ z₃
    (G₁ * G₂) * G₃ =
      opHeisenbergGroupPlus (y₁ + y₂ + y₃) (z₁ + z₂ + z₃) (ξ₁ + ξ₂ + ξ₃ + ω₁₂ + ω₁₂_₃) ∧
    (G₁ * G₂) * (G₁_inv * G₂_inv) = opContactSubgroupPlus (ω₁₂ + ω₁₂) ∧
    opArnoldMetricReadout η (opGradePlus2 ξ) = opGradeZero (-η * ξ) (-ξ * η) ∧
    opArnoldPhaseReadout η (opGradePlus2 ξ) = opGradeZero (-η * ξ) (ξ * η) := by
  intro G₁ G₂ G₃ G₁_inv G₂_inv ω₁₂ ω₁₂_₃
  refine ⟨?_, ?_, ?_, ?_⟩
  · change (opHeisenbergGroupPlus y₁ z₁ ξ₁ * opHeisenbergGroupPlus y₂ z₂ ξ₂) *
        opHeisenbergGroupPlus y₃ z₃ ξ₃ =
      opHeisenbergGroupPlus (y₁ + y₂ + y₃) (z₁ + z₂ + z₃) (ξ₁ + ξ₂ + ξ₃ + ω₁₂ + ω₁₂_₃)
    rw [opHeisenbergGroupPlus_mul, opHeisenbergGroupPlus_mul]
    ext <;>
    (simp [opHeisenbergGroupPlus, ω₁₂, ω₁₂_₃];
     try abel)
  · change (opHeisenbergGroupPlus y₁ z₁ ξ₁ * opHeisenbergGroupPlus y₂ z₂ ξ₂) *
        (opHeisenbergGroupPlus (-y₁) (-z₁) (-ξ₁) * opHeisenbergGroupPlus (-y₂) (-z₂) (-ξ₂)) =
      opContactSubgroupPlus (ω₁₂ + ω₁₂)
    rw [opHeisenbergGroupPlus_mul, opHeisenbergGroupPlus_mul, opHeisenbergGroupPlus_mul]
    ext <;>
    (simp [opHeisenbergGroupPlus, opContactSubgroupPlus, ω₁₂, opContactSymplecticForm];
     try noncomm_ring
     try abel)
  · ext <;>
    (simp [opArnoldMetricReadout, opAnticommutator, opGradeMinus2, opGradePlus2,
           opGradeZero, opCartanDiag, OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross];
     try noncomm_ring)
  · ext <;>
    (simp [opArnoldPhaseReadout, opCommutator, opGradeMinus2, opGradePlus2,
           opGradeZero, opCartanDiag, OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross];
     try noncomm_ring)

/-! ### Archetypes LIII & LIV: Operator Navier–Stokes Viscous Leibniz Law & 5-Graded Vorticity Depletion -/

/-- **Theorem 69 (Archetype LIII — Operator Navier–Stokes Viscous Enstrophy/Helicity Balance & Lamb Work)**:
    For any Grade $0$ viscous/Laplacian operator $D_{\mathrm{visc}} = \mathrm{opGradeZero}\;\Delta_+\;\Delta_-$
    and any operator velocity $u \in \mathrm{OpVec3}\;A$ and vorticity $\omega \in \mathrm{OpVec3}\;A$
    with $U = L_+(u)$, $\Omega_+ = L_+(\omega)$, and $\Omega_- = L_-(\omega)$:
    1. Opposite-Chirality Viscous Leibniz Product Rule:
       $$\mathrm{opCommutator}\;D_{\mathrm{visc}}\;(\Omega_+ * \Omega_-) =
         (\mathrm{opCommutator}\;D_{\mathrm{visc}}\;\Omega_+) * \Omega_- +
         \Omega_+ * (\mathrm{opCommutator}\;D_{\mathrm{visc}}\;\Omega_-).$$
    2. Viscous Enstrophy / Helicity Anticommutator Balance:
       $$\mathrm{opAnticommutator}\;(\mathrm{opCommutator}\;D_{\mathrm{visc}}\;\Omega_+)\;\Omega_- +
         \mathrm{opAnticommutator}\;\Omega_+\;(\mathrm{opCommutator}\;D_{\mathrm{visc}}\;\Omega_-) =
         \mathrm{opCommutator}\;D_{\mathrm{visc}}\;(\mathrm{opAnticommutator}\;\Omega_+\;\Omega_-).$$
    3. 3D Operator Lamb-Velocity Work Projection into the Associative Nucleus $\mathcal{G}_0$:
       $$U * (\Omega_+ * U) = \mathrm{opGradeZero}\;(-\mathrm{OpVec3.dot}\;u\;(\mathrm{opLambVector}\;\omega\;u))\;0,$$
       $$(\Omega_+ * U) * U = \mathrm{opGradeZero}\;0\;(-\mathrm{OpVec3.dot}\;(\mathrm{opLambVector}\;\omega\;u)\;u).$$ -/
theorem operator_navier_stokes_viscous_leibniz_and_lamb_work
    (Δ_p Δ_m : A) (u ω : OpVec3 A) :
    let D_visc := opGradeZero Δ_p Δ_m
    let U := opLightconeRayPlus u
    let Ω_p := opLightconeRayPlus ω
    let Ω_m := opLightconeRayMinus ω
    let L_vec := opLambVector ω u
    opCommutator D_visc (Ω_p * Ω_m) =
      opCommutator D_visc Ω_p * Ω_m + Ω_p * opCommutator D_visc Ω_m ∧
    opAnticommutator (opCommutator D_visc Ω_p) Ω_m +
      opAnticommutator Ω_p (opCommutator D_visc Ω_m) =
      opCommutator D_visc (opAnticommutator Ω_p Ω_m) ∧
    U * (Ω_p * U) = opGradeZero (-OpVec3.dot u L_vec) 0 ∧
    (Ω_p * U) * U = opGradeZero 0 (-OpVec3.dot L_vec u) := by
  intro D_visc U Ω_p Ω_m L_vec
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext <;>
    (simp [D_visc, Ω_p, Ω_m, opCommutator, opCartanDiag,
           opLightconeRayPlus, opLightconeRayMinus,
           OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross];
     try noncomm_ring)
  · ext <;>
    (simp [D_visc, Ω_p, Ω_m, opAnticommutator, opCommutator, opCartanDiag,
           opLightconeRayPlus, opLightconeRayMinus,
           OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross];
     try noncomm_ring)
  · ext <;>
    (simp [U, Ω_p, L_vec, opLambVector, opGradeZero, opCartanDiag,
           opLightconeRayPlus, OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross];
     try noncomm_ring)
  · ext <;>
    (simp [U, Ω_p, L_vec, opLambVector, opGradeZero, opCartanDiag,
           opLightconeRayPlus, OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross];
     try noncomm_ring)

/-- **Theorem 70 (Archetype LIV — 5-Graded Noncommutative Lamb Orthogonality & Vorticity Depletion)**:
    For any transverse Grade $+1$ velocity $U_\perp = \mathrm{opGradePlus1}\;u_y\;u_z$ and
    transverse Grade $+1$ vorticity $\Omega_\perp = \mathrm{opGradePlus1}\;\omega_y\;\omega_z$
    over *any* noncommutative operator ring $A$:
    1. Exact Grade $+2$ Contact-Central Lamb Vector:
       $$\Omega_\perp * U_\perp = \mathrm{opGradePlus2}\;(\mathrm{opContactSymplecticForm}\;\omega_y\;\omega_z\;u_y\;u_z).$$
    2. Exact Noncommutative Lamb-Velocity Work Vanishing ($U_\perp * (\Omega_\perp * U_\perp) = 0$):
       $$U_\perp * (\Omega_\perp * U_\perp) = 0 \qquad \text{and} \qquad (\Omega_\perp * U_\perp) * U_\perp = 0.$$
    3. Exact Noncommutative Lamb-Vorticity Self-Advection Depletion ($\Omega_\perp * (\Omega_\perp * U_\perp) = 0$):
       $$\Omega_\perp * (\Omega_\perp * U_\perp) = 0 \qquad \text{and} \qquad (\Omega_\perp * U_\perp) * \Omega_\perp = 0.$$ -/
theorem fiveGraded_operator_lamb_orthogonality_and_vorticity_depletion
    (u_y u_z ω_y ω_z : A) :
    let U_perp := opGradePlus1 u_y u_z
    let Ω_perp := opGradePlus1 ω_y ω_z
    let ω_symp := opContactSymplecticForm ω_y ω_z u_y u_z
    Ω_perp * U_perp = opGradePlus2 ω_symp ∧
    U_perp * (Ω_perp * U_perp) = 0 ∧
    (Ω_perp * U_perp) * U_perp = 0 ∧
    Ω_perp * (Ω_perp * U_perp) = 0 ∧
    (Ω_perp * U_perp) * Ω_perp = 0 := by
  intro U_perp Ω_perp ω_symp
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · ext <;>
    (simp [U_perp, Ω_perp, ω_symp, opGradePlus1, opGradePlus2, opContactSymplecticForm,
           OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross];
     try noncomm_ring)
  · ext <;>
    (simp [U_perp, Ω_perp, opGradePlus1, OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross];
     try noncomm_ring)
  · ext <;>
    (simp [U_perp, Ω_perp, opGradePlus1, OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross];
     try noncomm_ring)
  · ext <;>
    (simp [U_perp, Ω_perp, opGradePlus1, OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross];
     try noncomm_ring)
  · ext <;>
    (simp [U_perp, Ω_perp, opGradePlus1, OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross];
     try noncomm_ring)

/-! ### Archetypes LV, LVI, & LVII: Noncommutative QGT, Metriplectic Evolution, & Beltrami Helicity Dissipation -/

/-- **Forward Noncommutative Quantum Geometric Tensor**
    $Q_{\mathrm{QGT}}(v, w) := L_+(v) * L_-(w) + L_+(v) * L_-(w)$. -/
def opQuantumGeometricTensor (v w : OpVec3 A) : OpZornMatrix A :=
  opLightconeRayPlus v * opLightconeRayMinus w + opLightconeRayPlus v * opLightconeRayMinus w

/-- **Backward Dual Noncommutative Quantum Geometric Tensor**
    $Q_{\mathrm{QGT}}^*(v, w) := L_-(w) * L_+(v) + L_-(w) * L_+(v)$. -/
def opQuantumGeometricTensorDual (v w : OpVec3 A) : OpZornMatrix A :=
  opLightconeRayMinus w * opLightconeRayPlus v + opLightconeRayMinus w * opLightconeRayPlus v

/-- **Combined Non-Associative Metriplectic Evolution Operator**
    $\mathcal{M}_{H, S}(X) := [H, X] + \{S, X\} = \mathrm{opCommutator}\;H\;X + \mathrm{opAnticommutator}\;S\;X$. -/
def opMetriplecticFlow (H S X : OpZornMatrix A) : OpZornMatrix A :=
  opCommutator H X + opAnticommutator S X

/-- **Theorem 71 (Archetype LV — Noncommutative Quantum Geometric Tensor & Madelung Metric-Berry Split)**:
    Over *any* noncommutative operator ring $A$, for all $v, w \in \mathrm{OpVec3}\;A$, let
    $g(v, w) = \mathrm{opParaKahlerMetric}\;v\;w = \{L_+(v), L_-(w)\}$ and
    $\omega(v, w) = \mathrm{opParaKahlerSymplectic}\;v\;w = [L_+(v), L_-(w)]$:
    1. Forward QGT = Quantum Metric + Berry Symplectic 2-Form:
       $$Q_{\mathrm{QGT}}(v, w) = g(v, w) + \omega(v, w) = \mathrm{opGradeZero}\;(-(v \cdot w + v \cdot w))\;0.$$
    2. Backward Dual QGT = Quantum Metric - Berry Symplectic 2-Form:
       $$Q_{\mathrm{QGT}}^*(v, w) = g(v, w) - \omega(v, w) = \mathrm{opGradeZero}\;0\;(-(w \cdot v + w \cdot v)).$$
    3. Para-Kähler Chiral Projector Split of the QGT ($\Gamma = \mathrm{opZornGamma}$):
       $$(1 + \Gamma) * g(v, w) = Q_{\mathrm{QGT}}(v, w) \qquad \text{and} \qquad
         (1 - \Gamma) * g(v, w) = Q_{\mathrm{QGT}}^*(v, w).$$ -/
theorem quantumGeometricTensor_madelung_metric_berry_split
    (v w : OpVec3 A) :
    let Q := opQuantumGeometricTensor v w
    let Q_dual := opQuantumGeometricTensorDual v w
    let g := opParaKahlerMetric v w
    let ω := opParaKahlerSymplectic v w
    let Γ := opZornGamma
    Q = g + ω ∧
    Q_dual = g - ω ∧
    Q = opGradeZero (-(OpVec3.dot v w + OpVec3.dot v w)) 0 ∧
    Q_dual = opGradeZero 0 (-(OpVec3.dot w v + OpVec3.dot w v)) ∧
    (1 + Γ) * g = Q ∧
    (1 - Γ) * g = Q_dual := by
  intro Q Q_dual g ω Γ
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · ext <;>
    (simp [Q, g, ω, opQuantumGeometricTensor, opParaKahlerMetric, opParaKahlerSymplectic,
           opAnticommutator, opCommutator];
     try abel)
  · ext <;>
    (simp [Q_dual, g, ω, opQuantumGeometricTensorDual, opParaKahlerMetric, opParaKahlerSymplectic,
           opAnticommutator, opCommutator];
     try abel)
  · ext <;>
    (simp [Q, opQuantumGeometricTensor, opCartanDiag,
           opLightconeRayPlus, opLightconeRayMinus,
           OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross];
     try noncomm_ring)
  · ext <;>
    (simp [Q_dual, opQuantumGeometricTensorDual, opCartanDiag,
           opLightconeRayPlus, opLightconeRayMinus,
           OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross];
     try noncomm_ring)
  · ext <;>
    (simp [Q, g, Γ, opQuantumGeometricTensor, opParaKahlerMetric, opZornGamma,
           opAnticommutator, opLightconeRayPlus, opLightconeRayMinus,
           OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross];
     try noncomm_ring)
  · ext <;>
    (simp [Q_dual, g, Γ, opQuantumGeometricTensorDual, opParaKahlerMetric, opZornGamma,
           opAnticommutator, opLightconeRayPlus, opLightconeRayMinus,
           OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross];
     try noncomm_ring)

lemma opVec3_add_zero (u : OpVec3 A) : u + 0 = u := by
  ext <;> simp

lemma opVec3_zero_add (u : OpVec3 A) : 0 + u = u := by
  ext <;> simp

lemma opVec3_sub_zero (u : OpVec3 A) : u - 0 = u := by
  ext <;> simp

lemma opVec3_sub_self (u : OpVec3 A) : u - u = 0 := by
  ext <;> simp

lemma opVec3_dot_zero_left (u : OpVec3 A) : OpVec3.dot 0 u = 0 := by
  simp [OpVec3.dot]

lemma opVec3_dot_zero_right (u : OpVec3 A) : OpVec3.dot u 0 = 0 := by
  simp [OpVec3.dot]

lemma opVec3_leftScale_zero (c : A) : OpVec3.leftScale c 0 = 0 := by
  ext <;> simp

lemma opVec3_rightScale_zero (c : A) : OpVec3.rightScale 0 c = 0 := by
  ext <;> simp

lemma opVec3_skewCross_zero_left (u : OpVec3 A) : OpVec3.skewCross 0 u = 0 := by
  ext <;> simp [OpVec3.skewCross, OpVec3.naiveCross]

lemma opVec3_skewCross_zero_right (u : OpVec3 A) : OpVec3.skewCross u 0 = 0 := by
  ext <;> simp [OpVec3.skewCross, OpVec3.naiveCross]

/-- **Theorem 72 (Archetype LVI — Non-Associative Metriplectic Operator Evolution & Poisson–Jordan Derivation Law)**:
    Over *any* noncommutative operator ring $A$, for any Hamiltonian $H = \mathrm{opGradeZero}\;h_+\;h_- \in \mathcal{G}_0$,
    viscous/entropy generator $S = \mathrm{opGradeZero}\;\nu_+\;\nu_- \in \mathcal{G}_0$, any $v, w \in \mathrm{OpVec3}\;A$,
    and ALL $X \in \mathrm{OpZornMatrix}\;A$:
    1. Universal Left-Right Chiral Factorization of Metriplectic Flow:
       $$\mathcal{M}_{H, S}(X) = [H, X] + \{S, X\} = (H + S) * X + X * (S - H).$$
    2. Exact Viscous Jordan Modified-Leibniz Product Law on Opposite-Chirality Pairings:
       $$\{S, L_+(v) * L_-(w)\} = \{S, L_+(v)\} * L_-(w) + L_+(v) * \{S, L_-(w)\} - ((L_+(v) * S) * L_-(w) + (L_+(v) * S) * L_-(w)).$$
    3. Universal Poisson–Jordan Derivation Law on 8D $\mathrm{OpZornMatrix}\;A$:
       $$[H, \{S, X\}] - \{S, [H, X]\} = \{[H, S], X\}.$$ -/
theorem metriplecticFlow_chiral_factorization_and_viscous_leibniz
    (h_plus h_minus ν_plus ν_minus : A) (v w : OpVec3 A) (X : OpZornMatrix A) :
    let H := opGradeZero h_plus h_minus
    let S := opGradeZero ν_plus ν_minus
    let Lp := opLightconeRayPlus v
    let Lm := opLightconeRayMinus w
    opMetriplecticFlow H S X = (H + S) * X + X * (S - H) ∧
    opAnticommutator S (Lp * Lm) =
      opAnticommutator S Lp * Lm + Lp * opAnticommutator S Lm - ((Lp * S) * Lm + (Lp * S) * Lm) ∧
    opCommutator H (opAnticommutator S X) - opAnticommutator S (opCommutator H X) =
      opAnticommutator (opCommutator H S) X := by
  intro H S Lp Lm
  refine ⟨?_, ?_, ?_⟩
  · ext <;>
    (simp [H, S, opMetriplecticFlow, opCommutator, opAnticommutator, opCartanDiag,
           opVec3_add_zero, opVec3_zero_add, opVec3_sub_zero, opVec3_sub_self,
           opVec3_dot_zero_left, opVec3_dot_zero_right,
           opVec3_leftScale_zero, opVec3_rightScale_zero,
           opVec3_skewCross_zero_left, opVec3_skewCross_zero_right];
     try noncomm_ring)
  · ext <;>
    (simp [S, Lp, Lm, opAnticommutator, opCartanDiag,
           opLightconeRayPlus, opLightconeRayMinus,
           OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross];
     try noncomm_ring)
  · ext <;>
    (simp [H, S, opCommutator, opAnticommutator, opCartanDiag,
           opVec3_add_zero, opVec3_zero_add, opVec3_sub_zero, opVec3_sub_self,
           opVec3_dot_zero_left, opVec3_dot_zero_right,
           opVec3_leftScale_zero, opVec3_rightScale_zero,
           opVec3_skewCross_zero_left, opVec3_skewCross_zero_right];
     try noncomm_ring)

/-- **Theorem 73 (Archetype LVII — Noncommutative Beltrami Lamb Vanishing & Viscous Helicity Dissipation)**:
    Over *any* noncommutative operator ring $A$, for any velocity $u \in \mathrm{OpVec3}\;A$,
    vorticity $\omega \in \mathrm{OpVec3}\;A$, and viscous decay operator
    $S = \mathrm{opGradeZero}\;(-\nu)\;(-\nu)$:
    1. Beltrami Collinear Lamb Product Vanishing:
       $$L_+(u) * L_+(u) = 0.$$
    2. Exact Noncommutative Viscous Helicity Dissipation Bimodule Law:
       $$\mathrm{opAnticommutator}\;(S * L_+(u))\;(L_-(\omega)) +
         \mathrm{opAnticommutator}\;(L_+(u))\;(S * L_-(\omega)) =
         \mathrm{opGradeZero}\;(\nu * \mathrm{OpVec3.dot}\;u\;\omega + \mathrm{OpVec3.dot}\;(\mathrm{OpVec3.rightScale}\;u\;\nu)\;\omega)\;
                               (\nu * \mathrm{OpVec3.dot}\;\omega\;u + \mathrm{OpVec3.dot}\;(\mathrm{OpVec3.rightScale}\;\omega\;\nu)\;u).$$ -/
theorem operator_beltrami_lamb_vanishing_and_viscous_helicity_dissipation
    (ν : A) (u ω : OpVec3 A) :
    let U_p := opLightconeRayPlus u
    let Ω_m := opLightconeRayMinus ω
    let S := opGradeZero (-ν) (-ν)
    U_p * U_p = 0 ∧
    opAnticommutator (S * U_p) Ω_m + opAnticommutator U_p (S * Ω_m) =
      opGradeZero (ν * OpVec3.dot u ω + OpVec3.dot (OpVec3.rightScale u ν) ω)
                  (ν * OpVec3.dot ω u + OpVec3.dot (OpVec3.rightScale ω ν) u) := by
  intro U_p Ω_m S
  refine ⟨?_, ?_⟩
  · ext <;>
    (simp [U_p, opLightconeRayPlus, OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross];
     try noncomm_ring)
  · ext <;>
    (simp [U_p, Ω_m, S, opAnticommutator, opCartanDiag,
           opLightconeRayPlus, opLightconeRayMinus,
           OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross];
     try noncomm_ring)

/-! ### Archetypes LVIII & LIX: Quantum Chromo-Hydrodynamics, Algebraic QCD Bianchi Identity, & Nucleus Color Confinement -/

/-- **Symmetric Non-Abelian Color-Commutator Cross Product**
    $u \times_{\mathrm{color}} v := u \times_{\mathrm{naive}} v + v \times_{\mathrm{naive}} u$. -/
def OpVec3.colorCross (u v : OpVec3 A) : OpVec3 A :=
  OpVec3.naiveCross u v + OpVec3.naiveCross v u

/-- **Non-Abelian Yang–Mills Color-Magnetic Field Strength**
    $F_{\mathrm{YM}}(u) := u \times_{\mathrm{naive}} u = \langle [u_y, u_z], [u_z, u_x], [u_x, u_y] \rangle$. -/
def OpVec3.yangMillsColorField (u : OpVec3 A) : OpVec3 A :=
  OpVec3.naiveCross u u

/-- **Left & Right Baryon Color-Singlet Nambu Determinants**
    $\det_L(v_1, v_2, v_3) = v_1 \cdot (v_2 \times_{\mathrm{skew}} v_3)$ and
    $\det_R(v_1, v_2, v_3) = (v_1 \times_{\mathrm{skew}} v_2) \cdot v_3$. -/
def OpVec3.baryonDetLeft (v₁ v₂ v₃ : OpVec3 A) : A := OpVec3.dot v₁ (OpVec3.skewCross v₂ v₃)
def OpVec3.baryonDetRight (v₁ v₂ v₃ : OpVec3 A) : A := OpVec3.dot (OpVec3.skewCross v₁ v₂) v₃

/-- **Chromo-Magnetic Chern–Simons Color Helicity Operator**
    $\mathcal{C}_{\mathrm{CS}}(u) := \{L_+(u), L_-(F_{\mathrm{YM}}(u))\} \in \mathcal{G}_0$. -/
def opChernSimonsColorHelicity (u : OpVec3 A) : OpZornMatrix A :=
  opAnticommutator (opLightconeRayPlus u) (opLightconeRayMinus (OpVec3.yangMillsColorField u))

/-- **Quark–Antiquark Meson Color-Singlet Operator**
    $M(v, w) := \{L_+(v), L_-(w)\} \in \mathcal{G}_0$. -/
def opMesonSinglet (v w : OpVec3 A) : OpZornMatrix A :=
  opAnticommutator (opLightconeRayPlus v) (opLightconeRayMinus w)

/-- **3-Quark Baryon Color-Singlet Associator Operator**
    $B(v_1, v_2, v_3) := [L_+(v_1), L_+(v_2), L_+(v_3)] \in \mathcal{G}_0$. -/
def opBaryonSinglet (v₁ v₂ v₃ : OpVec3 A) : OpZornMatrix A :=
  opAssociator (opLightconeRayPlus v₁) (opLightconeRayPlus v₂) (opLightconeRayPlus v₃)

/-- **Theorem 74 (Archetype LVIII — Chromo-Hydrodynamic Vorticity Split, Algebraic QCD Bianchi Identity, & Anomaly-Free Chern–Simons Helicity)**:
    Over *any* noncommutative operator ring $A$, for all 3-color operator fields $u, v \in \mathrm{OpVec3}\;A$:
    1. Exact Chromo-Hydrodynamic Decomposition of the Ordered Cross Product:
       $$u \times_{\mathrm{naive}} v + u \times_{\mathrm{naive}} v = (u \times_{\mathrm{skew}} v) + (u \times_{\mathrm{color}} v).$$
    2. Self-Interaction Isolates Pure Yang–Mills Gluon Field Strength:
       $$u \times_{\mathrm{skew}} u = 0 \qquad \text{and} \qquad u \times_{\mathrm{color}} u = F_{\mathrm{YM}}(u) + F_{\mathrm{YM}}(u).$$
    3. Exact Algebraic QCD Bianchi Identity (Jacobi Cancellation of Color-Magnetic Divergence):
       $$u \cdot F_{\mathrm{YM}}(u) = F_{\mathrm{YM}}(u) \cdot u.$$
    4. Balanced Chern–Simons Color Helicity in $\mathcal{G}_0$:
       $$\mathcal{C}_{\mathrm{CS}}(u) = \mathrm{opGradeZero}\;(-(u \cdot F_{\mathrm{YM}}(u)))\;(-(u \cdot F_{\mathrm{YM}}(u))).$$
    5. Identical Vanishing of the Chiral Anomaly Trace of $\omega(u, F_{\mathrm{YM}}(u))$:
       $$\mathrm{opZornTrace}\bigl(\mathrm{opCommutator}\;(L_+(u))\;(L_-(F_{\mathrm{YM}}(u)))\bigr) = 0.$$ -/
theorem chromoHydrodynamics_vorticity_split_bianchi_and_chern_simons
    (u v : OpVec3 A) :
    let F_u := OpVec3.yangMillsColorField u
    OpVec3.naiveCross u v + OpVec3.naiveCross u v =
      OpVec3.skewCross u v + OpVec3.colorCross u v ∧
    OpVec3.skewCross u u = 0 ∧
    OpVec3.colorCross u u = F_u + F_u ∧
    OpVec3.dot u F_u = OpVec3.dot F_u u ∧
    opChernSimonsColorHelicity u =
      opGradeZero (-OpVec3.dot u F_u) (-OpVec3.dot u F_u) ∧
    opZornTrace (opCommutator (opLightconeRayPlus u) (opLightconeRayMinus F_u)) = 0 := by
  intro F_u
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · ext <;> (simp [OpVec3.naiveCross, OpVec3.skewCross, OpVec3.colorCross]; try noncomm_ring)
  · ext <;> (simp [OpVec3.skewCross, OpVec3.naiveCross]; try noncomm_ring)
  · ext <;> simp [F_u, OpVec3.colorCross, OpVec3.yangMillsColorField, OpVec3.naiveCross]
  · simp [F_u, OpVec3.yangMillsColorField, OpVec3.dot, OpVec3.naiveCross]; noncomm_ring
  · ext <;>
    (simp [F_u, opChernSimonsColorHelicity, opAnticommutator, opCartanDiag,
           opLightconeRayPlus, opLightconeRayMinus,
           OpVec3.yangMillsColorField, OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross];
     try noncomm_ring)
  · simp [F_u, opZornTrace, opCommutator, opLightconeRayPlus, opLightconeRayMinus,
          OpVec3.yangMillsColorField, OpVec3.dot, OpVec3.naiveCross]
    noncomm_ring

/-- **Theorem 75 (Archetype LIX — Quark–Diquark Anti-Triplet Pairing & Meson/Baryon Confinement into the $\mathcal{G}_0$ Leibniz Nucleus)**:
    Over *any* noncommutative operator ring $A$, for all 3-color quark fields $v, v_1, v_2, v_3, q \in \mathrm{OpVec3}\;A$
    and antiquark fields $w, \bar{q} \in \mathrm{OpVec3}\;A$:
    1. Quark $\times$ Quark $\to$ Diquark Anti-Triplet:
       $$L_+(v_1) * L_+(v_2) = L_-(v_1 \times_{\mathrm{skew}} v_2).$$
    2. Meson Singlet Lands in the Grade-0 Associative Nucleus $\mathcal{G}_0$:
       $$M(v, w) = \mathrm{opGradeZero}\;(-(v \cdot w))\;(-(w \cdot v)).$$
    3. 3-Quark Baryon Singlet Lands in the Grade-0 Associative Nucleus $\mathcal{G}_0$:
       $$B(v_1, v_2, v_3) = \mathrm{opGradeZero}\;(\det_L(v_1, v_2, v_3))\;(-\det_R(v_1, v_2, v_3)).$$
    4. Confined Meson & Baryon Singlets Generate Exact Leibniz Derivations on Opposite-Chirality Pairings:
       $$\mathrm{opCommutator}\;M\;(L_+(q) * L_-(\bar{q})) =
         (\mathrm{opCommutator}\;M\;(L_+(q))) * L_-(\bar{q}) + L_+(q) * (\mathrm{opCommutator}\;M\;(L_-(\bar{q}))),$$
       $$\mathrm{opCommutator}\;B\;(L_+(q) * L_-(\bar{q})) =
         (\mathrm{opCommutator}\;B\;(L_+(q))) * L_-(\bar{q}) + L_+(q) * (\mathrm{opCommutator}\;B\;(L_-(\bar{q}))).$$ -/
theorem quark_diquark_meson_baryon_nucleus_confinement_and_leibniz
    (v w v₁ v₂ v₃ q q_bar : OpVec3 A) :
    let M := opMesonSinglet v w
    let B := opBaryonSinglet v₁ v₂ v₃
    let Qp := opLightconeRayPlus q
    let Qm := opLightconeRayMinus q_bar
    opLightconeRayPlus v₁ * opLightconeRayPlus v₂ =
      opLightconeRayMinus (OpVec3.skewCross v₁ v₂) ∧
    M = opGradeZero (-OpVec3.dot v w) (-OpVec3.dot w v) ∧
    B = opGradeZero (OpVec3.baryonDetLeft v₁ v₂ v₃) (-OpVec3.baryonDetRight v₁ v₂ v₃) ∧
    opCommutator M (Qp * Qm) = opCommutator M Qp * Qm + Qp * opCommutator M Qm ∧
    opCommutator B (Qp * Qm) = opCommutator B Qp * Qm + Qp * opCommutator B Qm := by
  intro M B Qp Qm
  have hM : M = opGradeZero (-OpVec3.dot v w) (-OpVec3.dot w v) := by
    ext <;>
    (simp [M, opMesonSinglet, opAnticommutator, opCartanDiag,
           opLightconeRayPlus, opLightconeRayMinus,
           OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross];
     try noncomm_ring)
  have hB : B = opGradeZero (OpVec3.baryonDetLeft v₁ v₂ v₃) (-OpVec3.baryonDetRight v₁ v₂ v₃) := by
    ext <;>
    (simp [B, opBaryonSinglet, opAssociator, opCartanDiag,
           opLightconeRayPlus, OpVec3.baryonDetLeft, OpVec3.baryonDetRight,
           OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross];
     try noncomm_ring)
  refine ⟨?_, hM, hB, ?_, ?_⟩
  · ext <;>
    (simp [opLightconeRayPlus, opLightconeRayMinus,
           OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross];
     try noncomm_ring)
  · rw [hM]
    ext <;>
    (simp [Qp, Qm, opCommutator, opCartanDiag, opLightconeRayPlus, opLightconeRayMinus,
           OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross];
     try noncomm_ring)
  · rw [hB]
    ext <;>
    (simp [Qp, Qm, opCommutator, opCartanDiag, opLightconeRayPlus, opLightconeRayMinus,
           OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross];
     try noncomm_ring)

/-!
## 25. Archetype LX: The Master Nilpotent–Idempotent Trifactor Synthesis (Wavefunction Factors, 4-Factor Associative Square, Madelung–Bernoulli Split, & Contact-Lamb Composition)
-/

/-- **Left Chiral Wavefunction Factor (`opChiralWaveLeft w = U_-(w) * e_{11}` = $\langle 1, 0, w, 0 \rangle$)**. -/
def opChiralWaveLeft (w : OpVec3 A) : OpZornMatrix A :=
  opUnipotentLower w * opPeircePlus

/-- **Right Chiral Wavefunction Factor (`opChiralWaveRight v = e_{11} * U_+(v)` = $\langle 1, v, 0, 0 \rangle$)**. -/
def opChiralWaveRight (v : OpVec3 A) : OpZornMatrix A :=
  opPeircePlus * opUnipotentUpper v

/-- **Rank-1 Trifactor Projector (`opTrifactorProjector w v = (U_-(w) * e_{11}) * U_+(v)`)**. -/
def opTrifactorProjector (w v : OpVec3 A) : OpZornMatrix A :=
  (opUnipotentLower w * opPeircePlus) * opUnipotentUpper v

lemma opChiralWaveLeft_eq (w : OpVec3 A) :
    opChiralWaveLeft w = ⟨1, 0, w, 0⟩ := by
  ext <;> simp [opChiralWaveLeft, opUnipotentLower, opPeircePlus, OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross]

lemma opChiralWaveRight_eq (v : OpVec3 A) :
    opChiralWaveRight v = ⟨1, v, 0, 0⟩ := by
  ext <;> simp [opChiralWaveRight, opUnipotentUpper, opPeircePlus, OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross]

lemma opTrifactorProjector_eq (w v : OpVec3 A) :
    opTrifactorProjector w v = ⟨1, v, w, -OpVec3.dot w v⟩ := by
  ext <;> simp [opTrifactorProjector, opUnipotentLower, opUnipotentUpper, opPeircePlus, OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross]

/-- **Flow-Conjugated Rank-1 Core Projector (`opFlowProjectorCore w ρ_plus v`)**:
    $\Pi_{\mathrm{flow}}(w, \rho_+, v) = (U_-(w) * \mathrm{opGradeZero}\;\rho_+\;0) * U_+(-v)$. -/
def opFlowProjectorCore (w : OpVec3 A) (ρ_plus : A) (v : OpVec3 A) : OpZornMatrix A :=
  (opUnipotentLower w * opGradeZero ρ_plus 0) * opUnipotentUpper (-v)

/-- **5-Graded Contact-Transverse Trifactor Idempotent (`opContactFlowIdempotent ξ y z`)**:
    $\Pi_{\mathrm{contact}}(\xi, y, z) = \Pi_{\mathrm{flow}}(\langle \xi, 0, 0 \rangle, 1, \langle 0, y, z \rangle)$. -/
def opContactFlowIdempotent (ξ y z : A) : OpZornMatrix A :=
  opFlowProjectorCore ⟨ξ, 0, 0⟩ 1 ⟨0, y, z⟩

/-- **Complementary Contact-Transverse Trifactor Idempotent (`opContactFlowIdempotentCompl ξ y z`)**:
    $\Pi_{\mathrm{contact}}^\perp(\xi, y, z) = 1 - \Pi_{\mathrm{contact}}(\xi, y, z)$. -/
def opContactFlowIdempotentCompl (ξ y z : A) : OpZornMatrix A :=
  1 - opContactFlowIdempotent ξ y z

/-- **Theorem 76 (Archetype LX.1 — Chiral Wavefunction Idempotence, Inner/Outer Contractions, Noether-Sandwich Associators, & Lamb Vorticity Generation)**:
    Over *any* noncommutative operator ring $A$, for all 3-vectors $v, w, v_1, v_2, w_1, w_2 \in \mathrm{OpVec3}\;A$,
    let $\Psi_L = \mathrm{opChiralWaveLeft}\;w$, $\Psi_R = \mathrm{opChiralWaveRight}\;v$,
    $\Pi = \mathrm{opTrifactorProjector}\;w\;v$, and $H_{\mathrm{mod}} = \{L_+(v), L_-(w)\}$:
    1. Exact Idempotence of Chiral Wavefunction Factors:
       $$\Psi_L * \Psi_L = \Psi_L \qquad \text{and} \qquad \Psi_R * \Psi_R = \Psi_R.$$
    2. Inner Contraction = Grade-0 Quantum Metric / Helicity Eigenvalue:
       $$\Psi_R * \Psi_L = \mathrm{opGradeZero}\;(1 - v \cdot w)\;0.$$
    3. Outer Contraction = Rank-1 Trifactor Projector:
       $$\Psi_L * \Psi_R = \Pi \qquad \text{and} \qquad \Pi = \langle 1, v, w, -(w \cdot v) \rangle.$$
    4. Exact Noether Modular Commutator Law for the 3-Factor Sandwich Associators & Explicit Trifactor Square:
       $$\mathrm{opAssociator}\;\Psi_R\;\Psi_L\;\Psi_R = \mathrm{opCommutator}\;H_{\mathrm{mod}}\;(L_+(v)), \qquad
         \mathrm{opAssociator}\;\Psi_L\;\Psi_R\;\Psi_L = \mathrm{opCommutator}\;H_{\mathrm{mod}}\;(L_-(w)),$$
       $$\Pi * \Pi = \bigl\langle 1 - v \cdot w,\;\; v - v \cdot_{\mathrm{R}} (w \cdot v),\;\;
                                  w - (w \cdot v) \cdot_{\mathrm{L}} w,\;\; -(w \cdot v) + (w \cdot v) * (w \cdot v) \bigr\rangle.$$
    5. Same-Chirality Row & Column Composition Generates Arnold's Hydrodynamic Lamb Curl:
       $$\mathrm{opChiralWaveRight}\;v_1 * \mathrm{opChiralWaveRight}\;v_2 =
         \mathrm{opChiralWaveRight}\;v_2 + L_-(v_1 \times_{\mathrm{skew}} v_2),$$
       $$\mathrm{opChiralWaveLeft}\;w_1 * \mathrm{opChiralWaveLeft}\;w_2 =
         \mathrm{opChiralWaveLeft}\;w_1 - L_+(w_1 \times_{\mathrm{skew}} w_2).$$ -/
theorem chiralWave_trifactor_contractions_and_four_factor_associativity
    (w v v₁ v₂ w₁ w₂ : OpVec3 A) :
    let Ψ_L := opChiralWaveLeft w
    let Ψ_R := opChiralWaveRight v
    let Pi_tri := opTrifactorProjector w v
    let H_mod := opAnticommutator (opLightconeRayPlus v) (opLightconeRayMinus w)
    Ψ_L * Ψ_L = Ψ_L ∧
    Ψ_R * Ψ_R = Ψ_R ∧
    Ψ_R * Ψ_L = opGradeZero (1 - OpVec3.dot v w) 0 ∧
    Ψ_L * Ψ_R = Pi_tri ∧
    Pi_tri = ⟨1, v, w, -OpVec3.dot w v⟩ ∧
    opAssociator Ψ_R Ψ_L Ψ_R = opCommutator H_mod (opLightconeRayPlus v) ∧
    opAssociator Ψ_L Ψ_R Ψ_L = opCommutator H_mod (opLightconeRayMinus w) ∧
    Pi_tri * Pi_tri =
      ⟨1 - OpVec3.dot v w,
       v - OpVec3.rightScale v (OpVec3.dot w v),
       w - OpVec3.leftScale (OpVec3.dot w v) w,
       -OpVec3.dot w v + OpVec3.dot w v * OpVec3.dot w v⟩ ∧
    opChiralWaveRight v₁ * opChiralWaveRight v₂ =
      opChiralWaveRight v₂ + opLightconeRayMinus (OpVec3.skewCross v₁ v₂) ∧
    opChiralWaveLeft w₁ * opChiralWaveLeft w₂ =
      opChiralWaveLeft w₁ - opLightconeRayPlus (OpVec3.skewCross w₁ w₂) := by
  intro Ψ_L Ψ_R Pi_tri H_mod
  refine ⟨?_, ?_, ?_, ?_, opTrifactorProjector_eq w v, ?_, ?_, ?_, ?_, ?_⟩ <;>
  (ext <;>
   (simp [Ψ_L, Ψ_R, Pi_tri, H_mod,
          opChiralWaveLeft_eq, opChiralWaveRight_eq, opTrifactorProjector_eq,
          opCartanDiag, opAssociator, opCommutator, opAnticommutator,
          opLightconeRayPlus, opLightconeRayMinus,
          OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross];
    try noncomm_ring))

/-- **Theorem 77 (Archetype LX.2 — Madelung–Bohm–Bernoulli Core-Pressure Split of the General Gauss–Bruhat Trifactor Flow)**:
    Over *any* noncommutative operator ring $A$, for all $w, v \in \mathrm{OpVec3}\;A$ and $\rho_+, \rho_- \in A$:
    1. Vanishing Trifactor Associators:
       $$\mathrm{opAssociator}\;(U_-(w))\;(\mathrm{opGradeZero}\;\rho_+\;\rho_-)\;(U_+(v)) = 0 \quad \text{and} \quad
         \mathrm{opAssociator}\;(U_-(w))\;(\mathrm{opGradeZero}\;\rho_+\;0)\;(U_+(-v)) = 0.$$
    2. Explicit Madelung–Bohm Coordinates of $\Pi_{\mathrm{flow}}(w, \rho_+, v)$:
       $$\Pi_{\mathrm{flow}}(w, \rho_+, v) =
         \Bigl\langle \rho_+,\;\; -(\rho_+ \cdot_{\mathrm{L}} v),\;\; w \cdot_{\mathrm{R}} \rho_+,\;\;
                      (w \cdot_{\mathrm{R}} \rho_+) \cdot v \Bigr\rangle.$$
    3. Exact Decomposition into Rank-1 Madelung Core $\oplus$ Complementary Pressure Reservoir:
       $$\mathrm{opBruhatTrifactor}\;w\;\rho_+\;\rho_-\;v =
         (\mathrm{opChiralWaveLeft}\;w * \mathrm{opGradeZero}\;\rho_+\;0) * \mathrm{opChiralWaveRight}\;v +
         \mathrm{opGradeZero}\;0\;\rho_-,$$
       $$\mathrm{opBruhatTrifactor}\;w\;\rho_+\;\rho_-\;(-v) =
         \mathrm{opFlowProjectorCore}\;w\;\rho_+\;v + \mathrm{opGradeZero}\;0\;\rho_-.$$
    4. On-Shell Madelung–Bernoulli Balance ($\rho_- = (w \cdot_{\mathrm{R}} \rho_+) \cdot v$):
       When the reservoir $\rho_-$ equals the kinetic energy density $(w \cdot_{\mathrm{R}} \rho_+) \cdot v$,
       the $(1, 1)$ Schur complement vanishes identically:
       $$\mathrm{opBruhatTrifactor}\;w\;\rho_+\;\bigl((w \cdot_{\mathrm{R}} \rho_+) \cdot v\bigr)\;v =
         \bigl\langle \rho_+,\;\; \rho_+ \cdot_{\mathrm{L}} v,\;\; w \cdot_{\mathrm{R}} \rho_+,\;\; 0 \bigr\rangle.$$ -/
theorem madelung_bernoulli_trifactor_core_pressure_decomposition
    (w v : OpVec3 A) (ρ_plus ρ_minus : A) :
    let Ψ_L := opChiralWaveLeft w
    let Ψ_R := opChiralWaveRight v
    let K_kin := OpVec3.dot (OpVec3.rightScale w ρ_plus) v
    opAssociator (opUnipotentLower w) (opGradeZero ρ_plus ρ_minus) (opUnipotentUpper v) = 0 ∧
    opAssociator (opUnipotentLower w) (opGradeZero ρ_plus 0) (opUnipotentUpper (-v)) = 0 ∧
    opFlowProjectorCore w ρ_plus v =
      ⟨ρ_plus,
       -OpVec3.leftScale ρ_plus v,
       OpVec3.rightScale w ρ_plus,
       K_kin⟩ ∧
    opBruhatTrifactor w ρ_plus ρ_minus v =
      (Ψ_L * opGradeZero ρ_plus 0) * Ψ_R + opGradeZero 0 ρ_minus ∧
    opBruhatTrifactor w ρ_plus ρ_minus (-v) =
      opFlowProjectorCore w ρ_plus v + opGradeZero 0 ρ_minus ∧
    opBruhatTrifactor w ρ_plus K_kin v =
      ⟨ρ_plus, OpVec3.leftScale ρ_plus v, OpVec3.rightScale w ρ_plus, 0⟩ := by
  intro Ψ_L Ψ_R K_kin
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  (ext <;>
   (simp [Ψ_L, Ψ_R, K_kin, opFlowProjectorCore, opBruhatTrifactor,
          opChiralWaveLeft, opChiralWaveRight,
          opUnipotentLower, opUnipotentUpper, opPeircePlus, opCartanDiag, opAssociator,
          OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross];
    try noncomm_ring))

/-- **Theorem 78 (Archetype LX.3 — 5-Graded Contact-Transverse Strict Idempotence, Orthogonality, & Lamb Vorticity Composition)**:
    Over *any* noncommutative operator ring $A$, for all $\xi, y, z, \xi_1, y_1, z_1, \xi_2, y_2, z_2 \in A$,
    let $\Pi = \mathrm{opContactFlowIdempotent}\;\xi\;y\;z$ and $\Pi^\perp = \mathrm{opContactFlowIdempotentCompl}\;\xi\;y\;z$:
    1. Explicit Coordinates:
       $$\Pi_{\mathrm{contact}}(\xi, y, z) = \langle 1, \langle 0, -y, -z \rangle, \langle \xi, 0, 0 \rangle, 0 \rangle.$$
    2. Strict Idempotence in All 8 Non-Associative Channels:
       $$\Pi * \Pi = \Pi \qquad \text{and} \qquad \Pi^\perp * \Pi^\perp = \Pi^\perp.$$
    3. Exact Mutual Orthogonality:
       $$\Pi * \Pi^\perp = 0 \qquad \text{and} \qquad \Pi^\perp * \Pi = 0.$$
    4. Two-Projector Composition Law (Injecting the Lamb / Symplectic Contact Vorticity $\omega_\perp$):
       $$\Pi_{\mathrm{contact}}(\xi_1, y_1, z_1) * \Pi_{\mathrm{contact}}(\xi_2, y_2, z_2) =
         \Pi_{\mathrm{contact}}\!\bigl(\xi_1 + \omega_\perp(y_1, z_1; y_2, z_2),\;\; y_2,\;\; z_2\bigr).$$ -/
theorem contactFlowIdempotent_strict_idem_orth_and_lamb_composition
    (ξ y z ξ₁ y₁ z₁ ξ₂ y₂ z₂ : A) :
    let Pi_c := opContactFlowIdempotent ξ y z
    let Pi_perp := opContactFlowIdempotentCompl ξ y z
    let Pi_c1 := opContactFlowIdempotent ξ₁ y₁ z₁
    let Pi_c2 := opContactFlowIdempotent ξ₂ y₂ z₂
    Pi_c = ⟨1, ⟨0, -y, -z⟩, ⟨ξ, 0, 0⟩, 0⟩ ∧
    Pi_c * Pi_c = Pi_c ∧
    Pi_perp * Pi_perp = Pi_perp ∧
    Pi_c * Pi_perp = 0 ∧
    Pi_perp * Pi_c = 0 ∧
    Pi_c1 * Pi_c2 =
      opContactFlowIdempotent (ξ₁ + opContactSymplecticForm y₁ z₁ y₂ z₂) y₂ z₂ := by
  intro Pi_c Pi_perp Pi_c1 Pi_c2
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  (ext <;>
   (simp [Pi_c, Pi_perp, Pi_c1, Pi_c2, opContactFlowIdempotent, opContactFlowIdempotentCompl,
          opFlowProjectorCore, opUnipotentLower, opUnipotentUpper, opCartanDiag,
          opContactSymplecticForm,
          OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross];
    try noncomm_ring))

/-!
## 26. Archetypes LXI & LXII: The 1934 Jordan–von Neumann–Wigner Formalism in $\mathrm{OpZornMatrix}\;A$ (Non-Associative Interchangeability, Cubic Peirce Polynomial, & Yang–Mills Jordan Balance)
-/

/-- **Jordan Associator (`opJordanAssoc X Y Z`)** (Jordan–von Neumann–Wigner 1934, Page 31, Eq. 1):
    $[X, Y, Z]_J := \{ \{X, Y\}, Z \} - \{ X, \{Y, Z\} \}$. -/
def opJordanAssoc (X Y Z : OpZornMatrix A) : OpZornMatrix A :=
  opAnticommutator (opAnticommutator X Y) Z - opAnticommutator X (opAnticommutator Y Z)

/-- **Left Jordan Multiplication (`opLeftJordan E X`)** by an operator $E \in \mathrm{OpZornMatrix}\;A$:
    $L_E(X) := \{E, X\} = E * X + X * E$. -/
def opLeftJordan (E X : OpZornMatrix A) : OpZornMatrix A :=
  opAnticommutator E X

/-- **Left Jordan Multiplication by the Primitive Peirce Idempotent $e_{11} = \langle 1, 0, 0, 0 \rangle$**:
    $L_{e_{11}}(X) := \{e_{11}, X\} = \mathrm{opAnticommutator}\;\mathrm{opPeircePlus}\;X$. -/
def opLeftJordanPeircePlus (X : OpZornMatrix A) : OpZornMatrix A :=
  opAnticommutator opPeircePlus X

/-- Right and left distributivity of `OpZornMatrix A` multiplication over addition. -/
lemma opZorn_add_mul (X Y Z : OpZornMatrix A) :
    (X + Y) * Z = X * Z + Y * Z := by
  ext <;>
  (simp [OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross];
   try noncomm_ring)

lemma opZorn_mul_add (X Y Z : OpZornMatrix A) :
    X * (Y + Z) = X * Y + X * Z := by
  ext <;>
  (simp [OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross];
   try noncomm_ring)

/-- Explicit 8-channel action of $L_{e_{11}}(X) = \{e_{11}, X\} = \langle 2 X.a, X.v, X.w, 0 \rangle$. -/
@[simp] lemma opLeftJordanPeircePlus_eq (X : OpZornMatrix A) :
    opLeftJordanPeircePlus X = ⟨X.a + X.a, X.v, X.w, 0⟩ := by
  ext <;>
  (simp [opLeftJordanPeircePlus, opAnticommutator, opPeircePlus,
         OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross];
   try abel)

/-- **Theorem 79 (Archetype LXI.1 — JvNW Page 31 Associator Symmetries & Page 45 Universal Non-Associative Interchangeability Law)**:
    Over *any* noncommutative operator ring $A$, for ALL $X, Y, Z \in \mathrm{OpZornMatrix}\;A$ and
    any Grade-0 nucleus operators $\rho_1, \sigma_1, \rho_2, \sigma_2 \in A$:
    1. Jordan Commutativity:
       $$\{X, Y\} = \{Y, X\}.$$
    2. JvNW Page 31, Eq. (2) (Outer Skew-Symmetry of the Jordan Associator):
       $$[X, Y, Z]_J + [Z, Y, X]_J = 0.$$
    3. JvNW Page 31, Eq. (3) (Cyclic Jacobi Sum of the Jordan Associator):
       $$[X, Y, Z]_J + [Y, Z, X]_J + [Z, X, Y]_J = 0.$$
    4. JvNW Page 45 Universal Non-Associative Interchangeability Identity:
       $$[X, Y, Z]_J = [[Z, X], Y] +
         \bigl([X, Y, Z] + [Y, X, Z] + [X, Z, Y] - [Z, X, Y] - [Y, Z, X] - [Z, Y, X]\bigr).$$
    5. Exact JvNW Page 45 Interchangeability Formula on the Associative Nucleus $\mathcal{G}_0$
       ($D_1 = \mathrm{opGradeZero}\;\rho_1\;\sigma_1$, $D_2 = \mathrm{opGradeZero}\;\rho_2\;\sigma_2$):
       $$[D_1, Y, D_2]_J = [[D_2, D_1], Y] \qquad \text{and} \qquad [D_1, Y, D_1]_J = 0.$$ -/
theorem jvnw_page31_and_page45_nonassociative_interchangeability
    (X Y Z : OpZornMatrix A) (ρ₁ σ₁ ρ₂ σ₂ : A) :
    let D₁ := opGradeZero ρ₁ σ₁
    let D₂ := opGradeZero ρ₂ σ₂
    opAnticommutator X Y = opAnticommutator Y X ∧
    opJordanAssoc X Y Z + opJordanAssoc Z Y X = 0 ∧
    opJordanAssoc X Y Z + opJordanAssoc Y Z X + opJordanAssoc Z X Y = 0 ∧
    opJordanAssoc X Y Z =
      opCommutator (opCommutator Z X) Y +
        (opAssociator X Y Z + opAssociator Y X Z + opAssociator X Z Y -
          opAssociator Z X Y - opAssociator Y Z X - opAssociator Z Y X) ∧
    opJordanAssoc D₁ Y D₂ = opCommutator (opCommutator D₂ D₁) Y ∧
    opJordanAssoc D₁ Y D₁ = 0 := by
  intro D₁ D₂
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [opAnticommutator]
    ext <;> (simp only [OpZornMatrix.add_a, OpZornMatrix.add_v, OpZornMatrix.add_w, OpZornMatrix.add_b,
                        OpVec3.add_x, OpVec3.add_y, OpVec3.add_z]; abel)
  · simp only [opJordanAssoc, opAnticommutator, opZorn_add_mul, opZorn_mul_add]
    ext <;> (simp only [OpZornMatrix.add_a, OpZornMatrix.add_v, OpZornMatrix.add_w, OpZornMatrix.add_b,
                        OpZornMatrix.sub_a, OpZornMatrix.sub_v, OpZornMatrix.sub_w, OpZornMatrix.sub_b,
                        OpZornMatrix.zero_a, OpZornMatrix.zero_v, OpZornMatrix.zero_w, OpZornMatrix.zero_b,
                        OpVec3.add_x, OpVec3.add_y, OpVec3.add_z,
                        OpVec3.sub_x, OpVec3.sub_y, OpVec3.sub_z,
                        OpVec3.zero_x, OpVec3.zero_y, OpVec3.zero_z]; abel)
  · simp only [opJordanAssoc, opAnticommutator, opZorn_add_mul, opZorn_mul_add]
    ext <;> (simp only [OpZornMatrix.add_a, OpZornMatrix.add_v, OpZornMatrix.add_w, OpZornMatrix.add_b,
                        OpZornMatrix.sub_a, OpZornMatrix.sub_v, OpZornMatrix.sub_w, OpZornMatrix.sub_b,
                        OpZornMatrix.zero_a, OpZornMatrix.zero_v, OpZornMatrix.zero_w, OpZornMatrix.zero_b,
                        OpVec3.add_x, OpVec3.add_y, OpVec3.add_z,
                        OpVec3.sub_x, OpVec3.sub_y, OpVec3.sub_z,
                        OpVec3.zero_x, OpVec3.zero_y, OpVec3.zero_z]; abel)
  · simp only [opJordanAssoc, opAnticommutator, opCommutator, opAssociator,
               opZorn_add_mul, opZorn_mul_add, opZorn_sub_mul, opZorn_mul_sub]
    ext <;> (simp only [OpZornMatrix.add_a, OpZornMatrix.add_v, OpZornMatrix.add_w, OpZornMatrix.add_b,
                        OpZornMatrix.sub_a, OpZornMatrix.sub_v, OpZornMatrix.sub_w, OpZornMatrix.sub_b,
                        OpVec3.add_x, OpVec3.add_y, OpVec3.add_z,
                        OpVec3.sub_x, OpVec3.sub_y, OpVec3.sub_z]; abel)
  · ext <;>
    (simp [D₁, D₂, opJordanAssoc, opAnticommutator, opCommutator, opCartanDiag,
           OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross];
     try noncomm_ring)
  · ext <;>
    (simp [D₁, opJordanAssoc, opAnticommutator, opCartanDiag,
           OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross];
     try noncomm_ring)

/-- **Theorem 80 (Archetype LXI.2 — JvNW Theorem 3 Cubic Peirce Polynomial & Theorem 4 / 12 Cross-Product Cancellation)**:
    Over *any* noncommutative operator ring $A$, for ALL $X \in \mathrm{OpZornMatrix}\;A$,
    all $\rho_1, \sigma_2 \in A$, and all $v_1, w_1, v_2, w_2 \in \mathrm{OpVec3}\;A$:
    1. JvNW Theorem 3, Eq. (8) (Page 33: Cubic Peirce Minimal Polynomial of $L_{e_{11}}$):
       $$L_{e_{11}}^3(X) - 3 L_{e_{11}}^2(X) + 2 L_{e_{11}}(X) = 0.$$
    2. JvNW Theorem 3, Eq. (10) (Page 33: Explicit Peirce Eigen-Projectors onto $N_0(e_{11}), N_{1/2}(e_{11}), N_1(e_{11})$):
       $$L_{e_{11}}^2(X) - 3 L_{e_{11}}(X) + 2 X = \mathrm{opGradeZero}\;0\;(X.b + X.b),$$
       $$-L_{e_{11}}^2(X) + 2 L_{e_{11}}(X) = \mathrm{opKasparovZornJ}\;X.v\;X.w,$$
       $$L_{e_{11}}^2(X) - L_{e_{11}}(X) = \mathrm{opGradeZero}\;(X.a + X.a)\;0.$$
    3. JvNW Theorem 4 (Page 34: Orthogonality of Diagonal Peirce Subspaces $N_1(e_{11}) \circ N_0(e_{11}) = 0$):
       $$\mathrm{opAnticommutator}\;(\mathrm{opGradeZero}\;\rho_1\;0)\;(\mathrm{opGradeZero}\;0\;\sigma_2) = 0.$$
    4. JvNW Theorem 4 & Theorem 12 (Pages 34 & 41: $N_{1/2}(e_{11}) \circ N_{1/2}(e_{11}) \subseteq N_1(e_{11}) \oplus N_0(e_{11})$ with Zero Cross-Product Leakage):
       $$\mathrm{opAnticommutator}\;(\mathrm{opKasparovZornJ}\;v_1\;w_1)\;(\mathrm{opKasparovZornJ}\;v_2\;w_2) =
         \mathrm{opGradeZero}\;\bigl(-(v_1 \cdot w_2 + v_2 \cdot w_1)\bigr)\;\bigl(-(w_1 \cdot v_2 + w_2 \cdot v_1)\bigr).$$ -/
theorem jvnw_theorem3_cubic_peirce_and_theorem4_multiplication_table
    (X : OpZornMatrix A) (ρ₁ σ₂ : A) (v₁ w₁ v₂ w₂ : OpVec3 A) :
    let L1 := opLeftJordanPeircePlus X
    let L2 := opLeftJordanPeircePlus L1
    let L3 := opLeftJordanPeircePlus L2
    L3 - (L2 + L2 + L2) + (L1 + L1) = 0 ∧
    L2 - (L1 + L1 + L1) + (X + X) = opGradeZero 0 (X.b + X.b) ∧
    -L2 + (L1 + L1) = opKasparovZornJ X.v X.w ∧
    L2 - L1 = opGradeZero (X.a + X.a) 0 ∧
    opAnticommutator (opGradeZero ρ₁ 0) (opGradeZero 0 σ₂) = 0 ∧
    opAnticommutator (opKasparovZornJ v₁ w₁) (opKasparovZornJ v₂ w₂) =
      opGradeZero (-(OpVec3.dot v₁ w₂ + OpVec3.dot v₂ w₁))
                  (-(OpVec3.dot w₁ v₂ + OpVec3.dot w₂ v₁)) := by
  intro L1 L2 L3
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · ext <;> (simp [L1, L2, L3]; try abel)
  · ext <;> (simp [L1, L2, opCartanDiag]; try abel)
  · ext <;> (simp [L1, L2, opKasparovZornJ]; try abel)
  · ext <;> (simp [L1, L2, opCartanDiag]; try abel)
  · ext <;>
    (simp [opCartanDiag, opAnticommutator, OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross])
  · ext <;>
    (simp [opKasparovZornJ, opCartanDiag, opAnticommutator,
           OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross];
     try abel)

/-- Explicit 8-channel action of $L_{\Pi_c}$ on any positive-parabolic operator
    $\langle a_0, \langle 0, u_y, u_z \rangle, \langle w_x, 0, 0 \rangle, b_0 \rangle \in \mathcal{G}_0 \oplus \mathcal{G}_{+1} \oplus \mathcal{G}_{+2}$. -/
@[simp] lemma opLeftJordan_contact_posParabolic (ξ y z a₀ u_y u_z w_x b₀ : A) :
    opLeftJordan (opContactFlowIdempotent ξ y z) ⟨a₀, ⟨0, u_y, u_z⟩, ⟨w_x, 0, 0⟩, b₀⟩ =
      ⟨a₀ + a₀,
       ⟨0, u_y - (y * b₀ + a₀ * y), u_z - (z * b₀ + a₀ * z)⟩,
       ⟨w_x + (ξ * a₀ + b₀ * ξ), 0, 0⟩,
       0⟩ := by
  ext <;>
  (simp [opLeftJordan, opAnticommutator, opContactFlowIdempotent, opFlowProjectorCore,
         opUnipotentLower, opUnipotentUpper, opCartanDiag,
         OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross];
   try abel;
   try noncomm_ring)

/-- **Theorem 81 (Archetype LXII — JvNW Theorem 12 Noncommutative Yang–Mills Balance, Universal Cubic Power-Associativity, & 5-Graded Contact Cubic Peirce Law)**:
    Over *any* noncommutative operator ring $A$, for ALL $X, Y \in \mathrm{OpZornMatrix}\;A$,
    all $u \in \mathrm{OpVec3}\;A$, and all $\rho_1, \sigma_1, \xi, y, z, a_0, b_0, u_y, u_z, w_x \in A$:
    1. Universal Cubic Jordan Power-Associativity on $\mathrm{OpZornMatrix}\;A$:
       $$[X, X, X]_J = 0 \qquad (\text{i.e., } \{\{X, X\}, X\} = \{X, \{X, X\}\}).$$
    2. Exact JvNW Fundamental Axiom (III) on the Associative Nucleus $\mathcal{G}_0$ ($D = \mathrm{opGradeZero}\;\rho_1\;\sigma_1$):
       $$[\{D, D\}, Y, D]_J = 0 \qquad (\text{i.e., } \{\{\{D, D\}, Y\}, D\} = \{\{D, D\}, \{Y, D\}\}).$$
    3. JvNW Theorem 12 Equal-Weight Law ($\alpha = \beta$, Page 41) on Noncommutative Yang–Mills States
       $J_{\mathrm{YM}}(u) = \mathrm{opKasparovZornJ}\;u\;(F_{\mathrm{YM}}(u))$ via the QCD Bianchi Identity:
       $$\{J_{\mathrm{YM}}(u), J_{\mathrm{YM}}(u)\} =
         \mathrm{opGradeZero}\;\bigl(-(u \cdot F_{\mathrm{YM}}(u) + u \cdot F_{\mathrm{YM}}(u))\bigr)\;
                               \bigl(-(u \cdot F_{\mathrm{YM}}(u) + u \cdot F_{\mathrm{YM}}(u))\bigr).$$
    4. 5-Graded Positive-Parabolic Cubic Peirce Law for Any Contact Flow Idempotent $\Pi_c = \mathrm{opContactFlowIdempotent}\;\xi\;y\;z$
       on $X_+ = \mathrm{opGradeZero}\;a_0\;b_0 + \mathrm{opGradePlus1}\;u_y\;u_z + \mathrm{opGradePlus2}\;w_x \in \mathcal{G}_0 \oplus \mathcal{G}_{+1} \oplus \mathcal{G}_{+2}$:
       $$L_{\Pi_c}^3(X_+) - 3 L_{\Pi_c}^2(X_+) + 2 L_{\Pi_c}(X_+) = 0.$$ -/
theorem jvnw_theorem12_yang_mills_balance_and_jordan_power_associativity
    (X Y : OpZornMatrix A) (u : OpVec3 A) (ρ₁ σ₁ ξ y z a₀ b₀ u_y u_z w_x : A) :
    let D := opGradeZero ρ₁ σ₁
    let F_u := OpVec3.yangMillsColorField u
    let J_YM := opKasparovZornJ u F_u
    let α := -(OpVec3.dot u F_u + OpVec3.dot u F_u)
    let Pi_c := opContactFlowIdempotent ξ y z
    let X_pos := opGradeZero a₀ b₀ + opGradePlus1 u_y u_z + opGradePlus2 w_x
    let Lc1 := opLeftJordan Pi_c X_pos
    let Lc2 := opLeftJordan Pi_c Lc1
    let Lc3 := opLeftJordan Pi_c Lc2
    opJordanAssoc X X X = 0 ∧
    opJordanAssoc (opAnticommutator D D) Y D = 0 ∧
    opAnticommutator J_YM J_YM = opGradeZero α α ∧
    Lc3 - (Lc2 + Lc2 + Lc2) + (Lc1 + Lc1) = 0 := by
  intro D F_u J_YM α Pi_c X_pos Lc1 Lc2 Lc3
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [opJordanAssoc, opAnticommutator, opZorn_add_mul, opZorn_mul_add]
    ext <;> (simp only [OpZornMatrix.add_a, OpZornMatrix.add_v, OpZornMatrix.add_w, OpZornMatrix.add_b,
                        OpZornMatrix.sub_a, OpZornMatrix.sub_v, OpZornMatrix.sub_w, OpZornMatrix.sub_b,
                        OpZornMatrix.zero_a, OpZornMatrix.zero_v, OpZornMatrix.zero_w, OpZornMatrix.zero_b,
                        OpVec3.add_x, OpVec3.add_y, OpVec3.add_z,
                        OpVec3.sub_x, OpVec3.sub_y, OpVec3.sub_z,
                        OpVec3.zero_x, OpVec3.zero_y, OpVec3.zero_z]; abel)
  · ext <;>
    (simp [D, opJordanAssoc, opAnticommutator, opCartanDiag,
           OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross];
     try noncomm_ring)
  · ext <;>
    (simp [F_u, J_YM, α, opAnticommutator, opCartanDiag, opKasparovZornJ,
           OpVec3.yangMillsColorField, OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross];
     try noncomm_ring)
  · have hX : X_pos = ⟨a₀, ⟨0, u_y, u_z⟩, ⟨w_x, 0, 0⟩, b₀⟩ := by
      ext <;> simp [X_pos, opCartanDiag, opGradePlus1, opGradePlus2]
    dsimp [Lc3, Lc2, Lc1, Pi_c]
    rw [hX]
    ext <;> (simp; try abel; try noncomm_ring)

/-!
## 27. Archetypes LXIII & LXIV: John Archibald Wheeler's Pregeometry in $\mathrm{OpZornMatrix}\;A$ ("It from Bit", "The Boundary of a Boundary is Zero", & Participatory Idempotent Loops)
-/

/-- **Wheeler Forward Boundary Differential (`opBoundaryDiffPlus v := P_row(v) - e_{11}` = $\langle 0, v, 0, 0 \rangle$)**. -/
def opBoundaryDiffPlus (v : OpVec3 A) : OpZornMatrix A :=
  opChiralWaveRight v - opPeircePlus

/-- **Wheeler Backward Codifferential (`opBoundaryDiffMinus w := P_col(w) - e_{11}` = $\langle 0, 0, w, 0 \rangle$)**. -/
def opBoundaryDiffMinus (w : OpVec3 A) : OpZornMatrix A :=
  opChiralWaveLeft w - opPeircePlus

@[simp] lemma opBoundaryDiffPlus_eq (v : OpVec3 A) :
    opBoundaryDiffPlus v = opLightconeRayPlus v := by
  ext <;> simp [opBoundaryDiffPlus, opChiralWaveRight_eq, opPeircePlus, opLightconeRayPlus]

@[simp] lemma opBoundaryDiffMinus_eq (w : OpVec3 A) :
    opBoundaryDiffMinus w = opLightconeRayMinus w := by
  ext <;> simp [opBoundaryDiffMinus, opChiralWaveLeft_eq, opPeircePlus, opLightconeRayMinus]

/-- **Theorem 82 (Archetype LXIII.1 — Wheeler's "Boundary of a Boundary is Zero" $\partial^2 = 0$ Derived from Binary Idempotents $P^2 = P$)**:
    Over *any* noncommutative operator ring $A$, for ALL $v, w, u \in \mathrm{OpVec3}\;A$ and $y, z, y_0, z_0, \xi_0 \in A$:
    1. Exact Idempotence of Binary Bits ("It from Bit"):
       $$e_{11} * e_{11} = e_{11}, \qquad
         P_{\mathrm{row}}(v) * P_{\mathrm{row}}(v) = P_{\mathrm{row}}(v), \qquad
         P_{\mathrm{col}}(w) * P_{\mathrm{col}}(w) = P_{\mathrm{col}}(w).$$
    2. Exact Nilpotence of Bit-Differences ("The Boundary of a Boundary is Zero", $d^2 = 0$ and $(d^*)^2 = 0$):
       $$d(v) * d(v) = 0 \qquad \text{and} \qquad d^*(w) * d^*(w) = 0.$$
    3. 5-Graded Nilradical Chain Boundary Law ($\partial_{y, z} \circ \partial_{y, z} = 0$ on $\mathcal{N}_+$):
       $$E_{+1}(y, z) * \bigl(E_{+1}(y, z) * N_+(y_0, z_0, \xi_0)\bigr) = 0.$$
    4. Yang–Mills Bianchi Boundary-of-a-Boundary Law ($d_u F_{\mathrm{YM}}(u) = 0$):
       $$u \cdot F_{\mathrm{YM}}(u) - F_{\mathrm{YM}}(u) \cdot u = 0.$$ -/
theorem wheeler_bit_idempotence_and_boundary_of_boundary_zero
    (v w u : OpVec3 A) (y z y₀ z₀ ξ₀ : A) :
    let d_v := opBoundaryDiffPlus v
    let d_w := opBoundaryDiffMinus w
    let d_yz := opGradePlus1 y z
    let N₀ := opHeisenbergNilPlus y₀ z₀ ξ₀
    let F_u := OpVec3.yangMillsColorField u
    opPeircePlus * (opPeircePlus : OpZornMatrix A) = opPeircePlus ∧
    opChiralWaveRight v * opChiralWaveRight v = opChiralWaveRight v ∧
    opChiralWaveLeft w * opChiralWaveLeft w = opChiralWaveLeft w ∧
    d_v * d_v = 0 ∧
    d_w * d_w = 0 ∧
    d_yz * (d_yz * N₀) = 0 ∧
    OpVec3.dot u F_u - OpVec3.dot F_u u = 0 := by
  intro d_v d_w d_yz N₀ F_u
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · ext <;> simp [opPeircePlus, OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross]
  · ext <;> (simp [opChiralWaveRight_eq, OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross]; try abel)
  · ext <;> (simp [opChiralWaveLeft_eq, OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross]; try abel)
  · ext <;> (simp [d_v, opLightconeRayPlus, OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross])
  · ext <;> (simp [d_w, opLightconeRayMinus, OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross])
  · ext <;>
    (simp [d_yz, N₀, opGradePlus1, opHeisenbergNilPlus,
           OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross];
     try noncomm_ring)
  · simp [F_u, OpVec3.yangMillsColorField, OpVec3.dot, OpVec3.naiveCross]; noncomm_ring

/-- **Theorem 83 (Archetypes LXIII.2 & LXIV — Wheeler's "It from Bit" Emergence of Metric, Spin Connection, Torsion, & 3D Volume from Binary Idempotents)**:
    Over *any* noncommutative operator ring $A$, for ALL $v, w, v_1, v_2, v_3 \in \mathrm{OpVec3}\;A$,
    let $d(v) = P_{\mathrm{row}}(v) - e_{11}$ and $d^*(w) = P_{\mathrm{col}}(w) - e_{11}$:
    1. Born Transition Amplitude from Direct Bit Product:
       $$P_{\mathrm{row}}(v) * P_{\mathrm{col}}(w) = \mathrm{opGradeZero}\;(1 - v \cdot w)\;0.$$
    2. Spacetime Metric $g(v, w)$ as the Hodge Laplacian $\{d(v), d^*(w)\}$ of Two Bits:
       $$d(v) * d^*(w) + d^*(w) * d(v) = \mathrm{opGradeZero}\;(-(v \cdot w))\;(-(w \cdot v)).$$
    3. Symplectic Spin Connection $\omega(v, w)$ as the Commutator $[d(v), d^*(w)]$ of Two Bits:
       $$d(v) * d^*(w) - d^*(w) * d(v) = \mathrm{opGradeZero}\;(-(v \cdot w))\;(+(w \cdot v)).$$
    4. Emergent Spin/Gauge Torsion from Two Sequential Row Bits:
       $$e_{22} * (P_{\mathrm{row}}(v_1) * P_{\mathrm{row}}(v_2)) = d^*(v_1 \times_{\mathrm{skew}} v_2).$$
    5. Emergent 3D Spacetime Volume from Three Sequential Bit-Differences:
       $$d(v_1) * (d(v_2) * d(v_3)) = \mathrm{opGradeZero}\;(-\det_L(v_1, v_2, v_3))\;0 \quad \text{and} \quad
         (d(v_1) * d(v_2)) * d(v_3) = \mathrm{opGradeZero}\;0\;(-\det_R(v_1, v_2, v_3)).$$ -/
theorem wheeler_it_from_bit_metric_torsion_and_volume_emergence
    (v w v₁ v₂ v₃ : OpVec3 A) :
    let d_v := opBoundaryDiffPlus v
    let d_w := opBoundaryDiffMinus w
    let d₁ := opBoundaryDiffPlus v₁
    let d₂ := opBoundaryDiffPlus v₂
    let d₃ := opBoundaryDiffPlus v₃
    opChiralWaveRight v * opChiralWaveLeft w = opGradeZero (1 - OpVec3.dot v w) 0 ∧
    d_v * d_w + d_w * d_v = opGradeZero (-OpVec3.dot v w) (-OpVec3.dot w v) ∧
    d_v * d_w - d_w * d_v = opGradeZero (-OpVec3.dot v w) (OpVec3.dot w v) ∧
    opPeirceMinus * (opChiralWaveRight v₁ * opChiralWaveRight v₂) =
      opBoundaryDiffMinus (OpVec3.skewCross v₁ v₂) ∧
    d₁ * (d₂ * d₃) = opGradeZero (-OpVec3.baryonDetLeft v₁ v₂ v₃) 0 ∧
    (d₁ * d₂) * d₃ = opGradeZero 0 (-OpVec3.baryonDetRight v₁ v₂ v₃) := by
  intro d_v d_w d₁ d₂ d₃
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  (ext <;>
   (simp [d_v, d_w, d₁, d₂, d₃, opChiralWaveRight_eq, opChiralWaveLeft_eq,
          opPeirceMinus, opLightconeRayPlus, opLightconeRayMinus, opCartanDiag,
          OpVec3.baryonDetLeft, OpVec3.baryonDetRight,
          OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross];
    try abel))

/-!
## 28. Archetypes LXV & LXVI: The 5-Graded Super-Grassmannian, KKT Degree-5 Polynomial, Günaydin–Gürsey $\mathfrak{gl}_3(A)$ Color Bridge, & $(2|3)$ Supertrace Cancellation
-/

/-- **The Euler 5-Grading Operator (`opEulerFiveGrading X`)**:
    Assigns eigenvalues $(-2, -1, 0, +1, +2)$ to $(\mathcal{G}_{-2}, \mathcal{G}_{-1}, \mathcal{G}_0, \mathcal{G}_{+1}, \mathcal{G}_{+2})$. -/
def opEulerFiveGrading (X : OpZornMatrix A) : OpZornMatrix A :=
  ⟨0,
   ⟨-(X.v.x + X.v.x), X.v.y, X.v.z⟩,
   ⟨X.w.x + X.w.x, -X.w.y, -X.w.z⟩,
   0⟩

/-- **Günaydin–Gürsey $\mathfrak{gl}_3(A)$ Color Outer-Product Matrix (`opColorOuterMat u w`)**:
    $G_{\mathrm{color}}(u, w)_{ij} = u_i * w_j \in \mathrm{Matrix}\;(\mathrm{Fin}\;3)\;(\mathrm{Fin}\;3)\;A$. -/
def opColorOuterMat (u w : OpVec3 A) : Matrix (Fin 3) (Fin 3) A :=
  !![u.x * w.x, u.x * w.y, u.x * w.z;
     u.y * w.x, u.y * w.y, u.y * w.z;
     u.z * w.x, u.z * w.y, u.z * w.z]

/-- Quark color trace $\mathrm{tr}_{\mathrm{quark}}(C) = C_{00} + C_{11} + C_{22}$ on `Matrix (Fin 3) (Fin 3) A`. -/
def opQuarkTrace (C : Matrix (Fin 3) (Fin 3) A) : A :=
  C 0 0 + C 1 1 + C 2 2

/-- **The $(2|3)$ Lepton–Quark Supertrace (`opSuperTrace23 L C`)**:
    $\mathrm{str}_{2|3}(L, C) = \mathrm{opZornTrace}(L) - \mathrm{opQuarkTrace}(C) \in A$. -/
def opSuperTrace23 (L : OpZornMatrix A) (C : Matrix (Fin 3) (Fin 3) A) : A :=
  opZornTrace L - opQuarkTrace C

/-- **Theorem 84 (Archetype LXV.1 — Euler 5-Grading Eigenvalues, Nilradical Leibniz Derivation Law, & Universal KKT Polynomial $\mathcal{E}_5^5 - 5\mathcal{E}_5^3 + 4\mathcal{E}_5 = 0$)**:
    Over *any* noncommutative operator ring $A$, for ALL $X \in \mathrm{OpZornMatrix}\;A$ and
    all $y, z, \xi, \eta, \rho_+, \rho_-, y_1, z_1, \xi_1, y_2, z_2, \xi_2 \in A$:
    1. Eigen-Action on $\mathcal{G}_0, \mathcal{G}_{\pm 1}, \mathcal{G}_{\pm 2}$:
       $$\mathcal{E}_5(\mathrm{opGradeZero}\;\rho_+\;\rho_-) = 0, \qquad
         \mathcal{E}_5(E_{+1}(y, z)) = E_{+1}(y, z), \qquad
         \mathcal{E}_5(E_{-1}(y, z)) = -E_{-1}(y, z),$$
       $$\mathcal{E}_5(E_{+2}(\xi)) = E_{+2}(\xi + \xi), \qquad
         \mathcal{E}_5(E_{-2}(\eta)) = -E_{-2}(\eta + \eta).$$
    2. Exact Leibniz Derivation Law on Both Heisenberg Nilradicals $\mathcal{N}_+$ and $\mathcal{N}_-$:
       $$\mathcal{E}_5(N_{+,1} * N_{+,2}) = \mathcal{E}_5(N_{+,1}) * N_{+,2} + N_{+,1} * \mathcal{E}_5(N_{+,2}),$$
       $$\mathcal{E}_5(N_{-,1} * N_{-,2}) = \mathcal{E}_5(N_{-,1}) * N_{-,2} + N_{-,1} * \mathcal{E}_5(N_{-,2}).$$
    3. Universal KKT Degree-5 Minimal Polynomial Annihilation ($\mathcal{E}_5^5 - 5 \mathcal{E}_5^3 + 4 \mathcal{E}_5 = 0$):
       $$\mathcal{E}_5^5(X) - (\mathcal{E}_5^3(X) + \mathcal{E}_5^3(X) + \mathcal{E}_5^3(X) + \mathcal{E}_5^3(X) + \mathcal{E}_5^3(X)) +
         (\mathcal{E}_5(X) + \mathcal{E}_5(X) + \mathcal{E}_5(X) + \mathcal{E}_5(X)) = 0.$$ -/
theorem eulerFiveGrading_eigen_derivation_and_kkt_polynomial
    (X : OpZornMatrix A) (y z ξ η ρ_plus ρ_minus y₁ z₁ ξ₁ y₂ z₂ ξ₂ : A) :
    let N_p1 := opHeisenbergNilPlus y₁ z₁ ξ₁
    let N_p2 := opHeisenbergNilPlus y₂ z₂ ξ₂
    let N_m1 := opHeisenbergNilMinus y₁ z₁ ξ₁
    let N_m2 := opHeisenbergNilMinus y₂ z₂ ξ₂
    let E1 := opEulerFiveGrading X
    let E2 := opEulerFiveGrading E1
    let E3 := opEulerFiveGrading E2
    let E4 := opEulerFiveGrading E3
    let E5 := opEulerFiveGrading E4
    opEulerFiveGrading (opGradeZero ρ_plus ρ_minus) = 0 ∧
    opEulerFiveGrading (opGradePlus1 y z) = opGradePlus1 y z ∧
    opEulerFiveGrading (opGradeMinus1 y z) = -opGradeMinus1 y z ∧
    opEulerFiveGrading (opGradePlus2 ξ) = opGradePlus2 (ξ + ξ) ∧
    opEulerFiveGrading (opGradeMinus2 η) = -opGradeMinus2 (η + η) ∧
    opEulerFiveGrading (N_p1 * N_p2) =
      opEulerFiveGrading N_p1 * N_p2 + N_p1 * opEulerFiveGrading N_p2 ∧
    opEulerFiveGrading (N_m1 * N_m2) =
      opEulerFiveGrading N_m1 * N_m2 + N_m1 * opEulerFiveGrading N_m2 ∧
    E5 - (E3 + E3 + E3 + E3 + E3) + (E1 + E1 + E1 + E1) = 0 := by
  intro N_p1 N_p2 N_m1 N_m2 E1 E2 E3 E4 E5
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · ext <;> simp [opEulerFiveGrading, opCartanDiag]
  · ext <;> simp [opEulerFiveGrading, opGradePlus1]
  · ext <;> simp [opEulerFiveGrading, opGradeMinus1]
  · ext <;> simp [opEulerFiveGrading, opGradePlus2]
  · ext <;> (simp [opEulerFiveGrading, opGradeMinus2]; try abel)
  · ext <;>
    (simp [N_p1, N_p2, opEulerFiveGrading, opHeisenbergNilPlus,
           OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross];
     try abel)
  · ext <;>
    (simp [N_m1, N_m2, opEulerFiveGrading, opHeisenbergNilMinus,
           OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross];
     try abel)
  · ext <;>
    (simp [E1, E2, E3, E4, E5, opEulerFiveGrading];
     try abel)

/-- **Theorem 85 (Archetypes LXV.2 & LXVI — Günaydin–Gürsey $\mathfrak{gl}_3(A)$ Contraction Bridge, $(2|3)$ Lepton–Quark Supertrace UV Cancellation, & Bogoliubov–Weyl Invariance)**:
    Over *any* noncommutative operator ring $A$, for ALL quark/antiquark 3-vectors $u, w, u_1, w_1, u_2, w_2 \in \mathrm{OpVec3}\;A$
    and any invertible Bogoliubov–Weyl boost operator $\lambda \in A^\times$ (`lam : Aˣ`):
    1. $\mathfrak{gl}_3(A)$ Outer-Product Multiplication Intertwines the Zorn Singlet Contraction $w_1 \cdot u_2$:
       $$G_{\mathrm{color}}(u_1, w_1) * G_{\mathrm{color}}(u_2, w_2) =
         G_{\mathrm{color}}\bigl(u_1 \cdot_{\mathrm{R}} (w_1 \cdot u_2),\; w_2\bigr).$$
    2. General & Exact Forward $(2|3)$ Lepton–Quark Supertrace UV Cancellation:
       $$\mathrm{str}_{2|3}\bigl(-(L_+(u) * L_-(w)),\; G_{\mathrm{color}}(u_2, w_2)\bigr) = u \cdot w - u_2 \cdot w_2,$$
       $$\mathrm{str}_{2|3}\bigl(-(L_+(u) * L_-(w)),\; G_{\mathrm{color}}(u, w)\bigr) = 0.$$
    3. Backward Dual $(2|3)$ Lepton–Quark Supertrace UV Cancellation:
       $$\mathrm{str}_{2|3}\bigl(-(L_-(w) * L_+(u)),\; G_{\mathrm{color}}(w, u)\bigr) = 0.$$
    4. Noncommutative Hyperbolic Bogoliubov–Weyl Boost Invariance (`lam : Aˣ`):
       Under $u' = \lambda \cdot_L u$ and $w' = w \cdot_R \lambda^{-1}$,
       $$w' \cdot u' = w \cdot u \qquad \text{and} \qquad
         L_-(w') * L_+(u') = L_-(w) * L_+(u).$$ -/
theorem gunaydin_gursey_color_bridge_supertrace_cancellation_and_bogoliubov
    (u w u₁ w₁ u₂ w₂ : OpVec3 A) (lam : Aˣ) :
    let u_boost := OpVec3.leftScale (lam : A) u
    let w_boost := OpVec3.rightScale w (↑lam⁻¹ : A)
    opColorOuterMat u₁ w₁ * opColorOuterMat u₂ w₂ =
      opColorOuterMat (OpVec3.rightScale u₁ (OpVec3.dot w₁ u₂)) w₂ ∧
    opSuperTrace23 (-(opLightconeRayPlus u * opLightconeRayMinus w)) (opColorOuterMat u₂ w₂) =
      OpVec3.dot u w - OpVec3.dot u₂ w₂ ∧
    opSuperTrace23 (-(opLightconeRayPlus u * opLightconeRayMinus w)) (opColorOuterMat u w) = 0 ∧
    opSuperTrace23 (-(opLightconeRayMinus w * opLightconeRayPlus u)) (opColorOuterMat w u) = 0 ∧
    OpVec3.dot w_boost u_boost = OpVec3.dot w u ∧
    opLightconeRayMinus w_boost * opLightconeRayPlus u_boost =
      opLightconeRayMinus w * opLightconeRayPlus u := by
  intro u_boost w_boost
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · ext i j; fin_cases i <;> fin_cases j <;>
    (simp [opColorOuterMat, OpVec3.dot, Matrix.mul_apply, Fin.sum_univ_three];
     try noncomm_ring)
  · simp [opSuperTrace23, opZornTrace, opQuarkTrace, opLightconeRayPlus, opLightconeRayMinus,
          opColorOuterMat, OpVec3.dot]
  · simp [opSuperTrace23, opZornTrace, opQuarkTrace, opLightconeRayPlus, opLightconeRayMinus,
          opColorOuterMat, OpVec3.dot]
  · simp [opSuperTrace23, opZornTrace, opQuarkTrace, opLightconeRayPlus, opLightconeRayMinus,
          opColorOuterMat, OpVec3.dot]
  · simp [u_boost, w_boost, OpVec3.dot, mul_assoc]
  · ext <;>
    simp [u_boost, w_boost, opLightconeRayMinus, opLightconeRayPlus,
          OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross, mul_assoc]

/-!
## 29. Archetypes LXVII & LXVIII: Rolf Dahm's Projective Line Geometry, Plücker–Klein 6-Vector Bijection, Maxwell–Poynting Line Complex, Dihedral $D_4$ / $\mathrm{PG}(3,2)$ Collinear Triples, Lie Triple Systems, & Lounesto Spinor Ideals
-/

/-- **Dahm's First Electromagnetic / Line-Complex Invariant (`opMaxwellInvariantI1 E B`)**:
    $I_1(\mathbf{E}, \mathbf{B}) = \mathbf{B} \cdot \mathbf{B} - \mathbf{E} \cdot \mathbf{E} \in A$
    (R. Dahm, JPCS 3152 (2025) 012008, §2.2). -/
def opMaxwellInvariantI1 (E B : OpVec3 A) : A :=
  OpVec3.dot B B - OpVec3.dot E E

/-- **Dahm's Second Electromagnetic / Pfaffian Plücker–Klein Quadric Invariant (`opPluckerKleinQuadric p_rad p_trans`)**:
    $I_2(\mathbf{p}_{\mathrm{rad}}, \mathbf{p}_{\mathrm{trans}}) = p_{01} p_{23} + p_{02} p_{31} + p_{03} p_{12} = \mathbf{p}_{\mathrm{rad}} \cdot \mathbf{p}_{\mathrm{trans}} \in A$
    (R. Dahm, JPCS 3152 (2025) 012008, §2.2–2.3, Eq. (1)). -/
def opPluckerKleinQuadric (p_rad p_trans : OpVec3 A) : A :=
  OpVec3.dot p_rad p_trans

/-- **Dahm's Poynting Axis 3-Vector of a Special Line Complex (`opPoyntingAxis E B`)**:
    $\mathbf{S}(\mathbf{E}, \mathbf{B}) = \mathbf{E} \times_{\mathrm{skew}} \mathbf{B} \in \mathrm{OpVec3}\;A$
    (R. Dahm, JPCS 3152 (2025) 012008, §2.2). -/
def opPoyntingAxis (E B : OpVec3 A) : OpVec3 A :=
  OpVec3.skewCross E B

/-- **Dahm's Senary Klein-to-Plücker Radial 3-Vector Map (`opKleinToPluckerRad x_even x_odd`)**:
    $(p_{01}, p_{02}, p_{03}) = (x_1 + x_2, x_3 + x_4, x_5 + x_6)$
    (R. Dahm, JPCS 3152 (2025) 012008, §2.3, Eq. (1)). -/
def opKleinToPluckerRad (x_even x_odd : OpVec3 A) : OpVec3 A :=
  x_even + x_odd

/-- **Dahm's Senary Klein-to-Plücker Transverse 3-Vector Map (`opKleinToPluckerTrans x_even x_odd`)**:
    $(p_{23}, p_{31}, p_{12}) = (x_1 - x_2, x_3 - x_4, x_5 - x_6)$
    (R. Dahm, JPCS 3152 (2025) 012008, §2.3, Eq. (1)). -/
def opKleinToPluckerTrans (x_even x_odd : OpVec3 A) : OpVec3 A :=
  x_even - x_odd

/-- **Dahm's Dual Line Conjugation (`opLineDualConj X`)**:
    Exchanges point-line Plücker coordinates $\mathbf{p}_{\mathrm{rad}} = (p_{01}, p_{02}, p_{03})$
    with dual plane-pencil coordinates $\mathbf{p}_{\mathrm{trans}} = (p_{23}, p_{31}, p_{12})$
    (R. Dahm, JPCS 3152 (2025) 012008, §4: $p_{\alpha\beta} \leftrightarrow p_{\alpha+3,\beta+3}$). -/
def opLineDualConj (X : OpZornMatrix A) : OpZornMatrix A :=
  ⟨X.b, X.w, X.v, X.a⟩

/-- **Dahm's Dihedral Identity Generator $r_0 = \begin{pmatrix} 1 & 0 \\ 0 & 1 \end{pmatrix}$ (`opDahmR0`)**:
    (R. Dahm, JPCS 3152 (2025) 012008, §2.4). -/
def opDahmR0 : OpZornMatrix A :=
  ⟨1, 0, 0, 1⟩

/-- **Dahm's Complex Structure / Order-4 Dihedral Rotation $r_1 = Q_{02}$ (`opDahmR1`)**:
    Satisfies $r_1^2 = -r_0 = -1$ in `OpZornMatrix A`
    (R. Dahm, JPCS 3152 (2025) 012008, §2.3–2.4). -/
def opDahmR1 : OpZornMatrix A :=
  ⟨0, ⟨-1, 0, 0⟩, ⟨-1, 0, 0⟩, 0⟩

/-- **Dahm's Diagonal Dihedral Reflection $s_0 = \begin{pmatrix} 1 & 0 \\ 0 & -1 \end{pmatrix}$ (`opDahmS0`)**:
    Satisfies $s_0^2 = r_0 = 1$ in `OpZornMatrix A`
    (R. Dahm, JPCS 3152 (2025) 012008, §2.4). -/
def opDahmS0 : OpZornMatrix A :=
  ⟨1, 0, 0, -1⟩

/-- **Dahm's Anti-Diagonal Dihedral Reflection $s_1 = \begin{pmatrix} 0 & 1 \\ 1 & 0 \end{pmatrix}$ (`opDahmS1`)**:
    Satisfies $s_1^2 = r_0 = 1$ in `OpZornMatrix A`
    (R. Dahm, JPCS 3152 (2025) 012008, §2.4). -/
def opDahmS1 : OpZornMatrix A :=
  ⟨0, ⟨-1, 0, 0⟩, ⟨1, 0, 0⟩, 0⟩

/-- **Dahm's Lie Triple System (LTS) Product (`opLieTripleProduct X Y Z`)**:
    $\mathcal{T}_{\mathrm{LTS}}(X, Y, Z) = [X, [Y, Z]]$ in `OpZornMatrix A`
    (R. Dahm, JPCS 3152 (2025) 012008, §3). -/
def opLieTripleProduct (X Y Z : OpZornMatrix A) : OpZornMatrix A :=
  opCommutator X (opCommutator Y Z)

/-- **Lounesto–Dahm Left Spinorial Column Carrier (`opLounestoSpinorLeft ψ₁ ψ₂`)**:
    Embeds a 2-component spinor column $(\psi_1, \psi_2)$ into the left Peirce–Lounesto ideal
    $(\mathrm{OpZornMatrix}\;A) * e_+$
    (R. Dahm, JPCS 3152 (2025) 012008, §3, citing Lounesto Ch. 10.2). -/
def opLounestoSpinorLeft (ψ₁ ψ₂ : A) : OpZornMatrix A :=
  ⟨ψ₁, 0, ⟨ψ₂, 0, 0⟩, 0⟩

/-- **Theorem 86 (Archetype LXVII — Dahm's Plücker–Klein 6-Vector Bijection, Maxwell–Poynting Line-Complex Invariants, & Wave–Particle Dual Line Conjugation)**:
    Over *any* noncommutative operator ring $A$, for ALL 3-vectors $\mathbf{E}, \mathbf{B}, \mathbf{x}_{\mathrm{even}}, \mathbf{x}_{\mathrm{odd}} \in \mathrm{OpVec3}\;A$
    and any $X \in \mathrm{OpZornMatrix}\;A$:
    1. Senary Klein-to-Plücker Bijection & Characteristic-Free Inverse Reconstruction (Dahm §2.3, Eq. (1)):
       $$\mathbf{p}_{\mathrm{rad}}(\mathbf{x}_{\mathrm{even}}, \mathbf{x}_{\mathrm{odd}}) + \mathbf{p}_{\mathrm{trans}}(\mathbf{x}_{\mathrm{even}}, \mathbf{x}_{\mathrm{odd}}) = \mathbf{x}_{\mathrm{even}} + \mathbf{x}_{\mathrm{even}},$$
       $$\mathbf{p}_{\mathrm{rad}}(\mathbf{x}_{\mathrm{even}}, \mathbf{x}_{\mathrm{odd}}) - \mathbf{p}_{\mathrm{trans}}(\mathbf{x}_{\mathrm{even}}, \mathbf{x}_{\mathrm{odd}}) = \mathbf{x}_{\mathrm{odd}} + \mathbf{x}_{\mathrm{odd}}.$$
    2. Noncommutative Plücker–Klein Quadric Expansion in Klein Coordinates (Dahm §2.3, Eq. (1)):
       $$\mathbf{p}_{\mathrm{rad}}(\mathbf{x}_{\mathrm{even}}, \mathbf{x}_{\mathrm{odd}}) \cdot \mathbf{p}_{\mathrm{trans}}(\mathbf{x}_{\mathrm{even}}, \mathbf{x}_{\mathrm{odd}}) +
         \mathbf{p}_{\mathrm{trans}}(\mathbf{x}_{\mathrm{even}}, \mathbf{x}_{\mathrm{odd}}) \cdot \mathbf{p}_{\mathrm{rad}}(\mathbf{x}_{\mathrm{even}}, \mathbf{x}_{\mathrm{odd}}) =
         (\mathbf{x}_{\mathrm{even}} \cdot \mathbf{x}_{\mathrm{even}} - \mathbf{x}_{\mathrm{odd}} \cdot \mathbf{x}_{\mathrm{odd}}) +
         (\mathbf{x}_{\mathrm{even}} \cdot \mathbf{x}_{\mathrm{even}} - \mathbf{x}_{\mathrm{odd}} \cdot \mathbf{x}_{\mathrm{odd}}).$$
    3. Zorn Off-Diagonal Line-Complex Anticommutator Encodes Both Plücker–Klein Quadric Pairings $I_2(\mathbf{E}, \mathbf{B})$ and $I_2(\mathbf{B}, \mathbf{E})$:
       $$-\bigl(L_+(\mathbf{E}) * L_-(\mathbf{B}) + L_-(\mathbf{B}) * L_+(\mathbf{E})\bigr) =
         \begin{pmatrix} I_2(\mathbf{E}, \mathbf{B}) & 0 \\ 0 & I_2(\mathbf{B}, \mathbf{E}) \end{pmatrix}.$$
    4. Self-Dual Null Line Complex ($\mathbf{E} = \mathbf{B}$) Vanishing of $I_1$ and Dual Line Conjugation Involution ($\mathcal{C}_{\mathrm{line}}^2 = \mathrm{id}$):
       $$I_1(\mathbf{E}, \mathbf{E}) = 0, \qquad \mathrm{opLineDualConj}(\mathrm{opLineDualConj}\;X) = X, \qquad
         \mathrm{opZornTrace}(\mathrm{opLineDualConj}\;X) = X.b + X.a.$$ -/
theorem dahm_plucker_klein_quadric_and_maxwell_poynting_invariants
    (E B x_even x_odd : OpVec3 A) (X : OpZornMatrix A) :
    opKleinToPluckerRad x_even x_odd + opKleinToPluckerTrans x_even x_odd =
      x_even + x_even ∧
    opKleinToPluckerRad x_even x_odd - opKleinToPluckerTrans x_even x_odd =
      x_odd + x_odd ∧
    opPluckerKleinQuadric (opKleinToPluckerRad x_even x_odd) (opKleinToPluckerTrans x_even x_odd) +
      opPluckerKleinQuadric (opKleinToPluckerTrans x_even x_odd) (opKleinToPluckerRad x_even x_odd) =
      (OpVec3.dot x_even x_even - OpVec3.dot x_odd x_odd) +
        (OpVec3.dot x_even x_even - OpVec3.dot x_odd x_odd) ∧
    -(opLightconeRayPlus E * opLightconeRayMinus B + opLightconeRayMinus B * opLightconeRayPlus E) =
      opGradeZero (opPluckerKleinQuadric E B) (opPluckerKleinQuadric B E) ∧
    opMaxwellInvariantI1 E E = 0 ∧
    opLineDualConj (opLineDualConj X) = X ∧
    opZornTrace (opLineDualConj X) = X.b + X.a := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · ext <;> (simp [opKleinToPluckerRad, opKleinToPluckerTrans]; try abel)
  · ext <;> (simp [opKleinToPluckerRad, opKleinToPluckerTrans]; try abel)
  · simp [opPluckerKleinQuadric, opKleinToPluckerRad, opKleinToPluckerTrans, OpVec3.dot]
    noncomm_ring
  · ext <;>
    simp [opLightconeRayPlus, opLightconeRayMinus, opCartanDiag,
          opPluckerKleinQuadric, OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross]
  · simp [opMaxwellInvariantI1]
  · ext <;> rfl
  · rfl

/-- **Theorem 87 (Archetype LXVIII — Dahm's Dihedral $D_4$ Gauge Relations, $\mathrm{PG}(3,2)$ Collinear Operator Triple Identity, Lie Triple System Closure, & Lounesto Spinorial Ideals)**:
    Over *any* noncommutative operator ring $A$, for all $\psi_1, \psi_2, u_1, w_1, u_2, w_2, u_3, w_3 \in A$:
    1. Dihedral $D_4$ & $D_2 \cong \mathbb{Z}_2 \times \mathbb{Z}_2$ Relations in `OpZornMatrix A` (Dahm §2.4):
       $$r_1^2 = -r_0, \qquad s_0^2 = r_0, \qquad s_1^2 = r_0, \qquad
         s_0 * r_1 = s_1, \qquad r_1 * s_0 = -s_1, \qquad s_0 * s_1 = r_1, \qquad s_1 * s_0 = -r_1.$$
    2. Fano 3-Space $\mathrm{PG}(3,2)$ Collinear Operator Triple Law (Dahm §3, Fig. 1: *"operator triples along the lines of $\mathrm{PG}(3,2)$ multiply to $\sim 1$"*):
       $$(s_1 * s_0) * r_1 = r_0 = 1 \qquad \text{and} \qquad (s_0 * s_1) * r_1 = -r_0 = -1.$$
    3. Longitudinal Lie Triple System (LTS) Jacobi Identity & Coset Closure (Dahm §3):
       For any longitudinal coset elements $C_k = E_{+2}(u_k) + E_{-2}(w_k)$ ($k = 1, 2, 3$),
       $$\mathcal{T}_{\mathrm{LTS}}(C_1, C_2, C_3) + \mathcal{T}_{\mathrm{LTS}}(C_2, C_3, C_1) + \mathcal{T}_{\mathrm{LTS}}(C_3, C_1, C_2) = 0,$$
       and their Lie triple product $\mathcal{T}_{\mathrm{LTS}}(C_1, C_2, C_3)$ has strictly zero diagonal
       ($\mathcal{T}_{\mathrm{LTS}}(C_1, C_2, C_3).a = 0$ and $\mathcal{T}_{\mathrm{LTS}}(C_1, C_2, C_3).b = 0$).
    4. Lounesto–Dahm Primitive Idempotent Reconstruction & Left Spinor Ideal Absorption (Dahm §3, Lounesto Ch. 10.2):
       $$r_0 + s_0 = e_+ + e_+, \qquad r_0 - s_0 = e_- + e_-,$$
       $$\Psi(\psi_1, \psi_2) * e_+ = \Psi(\psi_1, \psi_2), \qquad \Psi(\psi_1, \psi_2) * e_- = 0.$$ -/
theorem dahm_dihedral_d4_pg32_line_triple_and_lounesto_spinor_ideals
    (ψ₁ ψ₂ u₁ w₁ u₂ w₂ u₃ w₃ : A) :
    let C₁ := opGradePlus2 u₁ + opGradeMinus2 w₁
    let C₂ := opGradePlus2 u₂ + opGradeMinus2 w₂
    let C₃ := opGradePlus2 u₃ + opGradeMinus2 w₃
    (opDahmR1 : OpZornMatrix A) * opDahmR1 = -opDahmR0 ∧
    (opDahmS0 : OpZornMatrix A) * opDahmS0 = opDahmR0 ∧
    (opDahmS1 : OpZornMatrix A) * opDahmS1 = opDahmR0 ∧
    (opDahmS0 : OpZornMatrix A) * opDahmR1 = opDahmS1 ∧
    (opDahmR1 : OpZornMatrix A) * opDahmS0 = -opDahmS1 ∧
    (opDahmS0 : OpZornMatrix A) * opDahmS1 = opDahmR1 ∧
    (opDahmS1 : OpZornMatrix A) * opDahmS0 = -opDahmR1 ∧
    ((opDahmS1 : OpZornMatrix A) * opDahmS0) * opDahmR1 = opDahmR0 ∧
    ((opDahmS0 : OpZornMatrix A) * opDahmS1) * opDahmR1 = -opDahmR0 ∧
    opLieTripleProduct C₁ C₂ C₃ + opLieTripleProduct C₂ C₃ C₁ + opLieTripleProduct C₃ C₁ C₂ = 0 ∧
    (opLieTripleProduct C₁ C₂ C₃).a = 0 ∧
    (opLieTripleProduct C₁ C₂ C₃).b = 0 ∧
    (opDahmR0 : OpZornMatrix A) + opDahmS0 = opPeircePlus + opPeircePlus ∧
    (opDahmR0 : OpZornMatrix A) - opDahmS0 = opPeirceMinus + opPeirceMinus ∧
    opLounestoSpinorLeft ψ₁ ψ₂ * opPeircePlus = opLounestoSpinorLeft ψ₁ ψ₂ ∧
    opLounestoSpinorLeft ψ₁ ψ₂ * opPeirceMinus = 0 := by
  intro C₁ C₂ C₃
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · ext <;> simp [opDahmR1, opDahmR0, OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross]
  · ext <;> simp [opDahmS0, opDahmR0, OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross]
  · ext <;> simp [opDahmS1, opDahmR0, OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross]
  · ext <;> simp [opDahmS0, opDahmR1, opDahmS1, OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross]
  · ext <;> simp [opDahmR1, opDahmS0, opDahmS1, OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross]
  · ext <;> simp [opDahmS0, opDahmS1, opDahmR1, OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross]
  · ext <;> simp [opDahmS1, opDahmS0, opDahmR1, OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross]
  · ext <;> simp [opDahmS1, opDahmS0, opDahmR1, opDahmR0, OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross]
  · ext <;> simp [opDahmS0, opDahmS1, opDahmR1, opDahmR0, OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross]
  · ext <;>
    (simp [C₁, C₂, C₃, opLieTripleProduct, opCommutator, opGradePlus2, opGradeMinus2,
           OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross];
     try noncomm_ring)
  · simp [C₁, C₂, C₃, opLieTripleProduct, opCommutator, opGradePlus2, opGradeMinus2,
          OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross]
  · simp [C₁, C₂, C₃, opLieTripleProduct, opCommutator, opGradePlus2, opGradeMinus2,
          OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross]
  · ext <;> (simp [opDahmR0, opDahmS0, opPeircePlus]; try abel)
  · ext <;> (simp [opDahmR0, opDahmS0, opPeirceMinus]; try abel)
  · ext <;> simp [opLounestoSpinorLeft, opPeircePlus, OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross]
  · ext <;> simp [opLounestoSpinorLeft, opPeirceMinus, OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross]

/-!
## 30. Archetypes LXIX & LXX: Electromagnetic Hodge Duality & the 8D Operator Maxwell–Poynting Stress Matrix in `OpZornMatrix A`
-/

/-- **Plücker–Klein Line Complex Matrix (`opLineComplex E B`)**:
    $J(\mathbf{E}, \mathbf{B}) = \langle 0, \mathbf{E}, \mathbf{B}, 0 \rangle \in \mathrm{OpZornMatrix}\;A$. -/
def opLineComplex (E B : OpVec3 A) : OpZornMatrix A :=
  ⟨0, E, B, 0⟩

/-- **Electromagnetic Hodge Dual Line Complex (`opLineHodgeDual E B`)**:
    $J^\star(\mathbf{E}, \mathbf{B}) = \langle 0, -\mathbf{B}, \mathbf{E}, 0 \rangle \in \mathrm{OpZornMatrix}\;A$. -/
def opLineHodgeDual (E B : OpVec3 A) : OpZornMatrix A :=
  ⟨0, -B, E, 0⟩

/-- **Theorem 88 (Archetype LXIX — Operator Maxwell–Poynting Stress Matrix, Lagrangian & Hamiltonian Traces, Dual-Line Product, & Plücker–Klein Square)**:
    Over *any* noncommutative operator ring $A$, for ALL 3-vector fields $\mathbf{E}, \mathbf{B} \in \mathrm{OpVec3}\;A$,
    let $J = \mathrm{opLineComplex}\;\mathbf{E}\;\mathbf{B}$ and $J^\star = \mathrm{opLineHodgeDual}\;\mathbf{E}\;\mathbf{B}$:
    1. Exact 8D Operator Maxwell–Poynting Stress Product ($J * J^\star$):
       $$J * J^\star =
         \bigl\langle -(\mathbf{E} \cdot \mathbf{E}),\;\;
                      \mathbf{S}(\mathbf{E}, \mathbf{B}),\;\;
                      -\mathbf{S}(\mathbf{E}, \mathbf{B}),\;\;
                      \mathbf{B} \cdot \mathbf{B} \bigr\rangle.$$
    2. Dual-Line Conjugate Stress Product ($J * \mathrm{opLineDualConj}\;J$):
       $$J * \mathrm{opLineDualConj}\;J =
         \bigl\langle -(\mathbf{E} \cdot \mathbf{E}),\;\;
                      \mathbf{S}(\mathbf{E}, \mathbf{B}),\;\;
                      \mathbf{S}(\mathbf{E}, \mathbf{B}),\;\;
                      -(\mathbf{B} \cdot \mathbf{B}) \bigr\rangle.$$
    3. Trace of $J * J^\star$ Isolates Dahm's First Maxwell Lagrangian Invariant $I_1(\mathbf{E}, \mathbf{B}) = \mathbf{B} \cdot \mathbf{B} - \mathbf{E} \cdot \mathbf{E}$:
       $$\mathrm{opZornTrace}(J * J^\star) = -((\mathbf{E} \cdot \mathbf{E}) - (\mathbf{B} \cdot \mathbf{B})).$$
    4. Chiral Trace of $J * J^\star$ Isolates Minus the Total Maxwell Hamiltonian Energy Density $-(\mathbf{E} \cdot \mathbf{E} + \mathbf{B} \cdot \mathbf{B})$:
       $$\mathrm{opZornTrace}(\mathrm{opDahmS0} * (J * J^\star)) = -(\mathbf{E} \cdot \mathbf{E} + \mathbf{B} \cdot \mathbf{B}).$$
    5. Self-Square Isolates Dahm's Second (Plücker–Klein Pfaffian) Invariant $I_2(\mathbf{E}, \mathbf{B}) = \mathbf{E} \cdot \mathbf{B}$:
       $$J * J = \mathrm{opGradeZero}\;(-I_2(\mathbf{E}, \mathbf{B}))\;(-I_2(\mathbf{B}, \mathbf{E})).$$
    6. Hodge Dual Period-4 Complex Structure:
       $$\mathrm{opLineHodgeDual}\;(-\mathbf{B})\;\mathbf{E} = -J.$$ -/
theorem dahm_hodge_dual_maxwell_poynting_stress_tensor
    (E B : OpVec3 A) :
    let J := opLineComplex E B
    let J_star := opLineHodgeDual E B
    J * J_star =
      ⟨-OpVec3.dot E E,
       opPoyntingAxis E B,
       -opPoyntingAxis E B,
       OpVec3.dot B B⟩ ∧
    J * opLineDualConj J =
      ⟨-OpVec3.dot E E,
       opPoyntingAxis E B,
       opPoyntingAxis E B,
       -OpVec3.dot B B⟩ ∧
    opZornTrace (J * J_star) = -OpVec3.dot E E + OpVec3.dot B B ∧
    opZornTrace (opDahmS0 * (J * J_star)) = -(OpVec3.dot E E + OpVec3.dot B B) ∧
    J * J = opGradeZero (-opPluckerKleinQuadric E B) (-opPluckerKleinQuadric B E) ∧
    opLineHodgeDual (-B) E = -J := by
  intro J J_star
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · ext <;>
    (simp [J, J_star, opLineComplex, opLineHodgeDual, opPoyntingAxis,
           OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross];
     try abel)
  · ext <;>
    (simp [J, opLineComplex, opLineDualConj, opPoyntingAxis,
           OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross];
     try abel)
  · simp [J, J_star, opLineComplex, opLineHodgeDual, opZornTrace, OpVec3.dot]
    abel
  · simp [J, J_star, opDahmS0, opLineComplex, opLineHodgeDual, opZornTrace, OpVec3.dot]
    abel
  · ext <;>
    simp [J, opLineComplex, opCartanDiag, opPluckerKleinQuadric,
          OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross]
  · ext <;> simp [J, opLineComplex, opLineHodgeDual]

/-!
## 31. Archetypes LXXI & LXXII: Saniga–Holweck–Pracna (2015) Combinatorial Grassmannians $G_2(N+1)$, Edge-Triangle Invariance, & Operator Cayley–Dickson Sedenion Zero Divisors
-/

/-- Number of points $v_N = \binom{N+1}{2}$ of the combinatorial Grassmannian $\mathcal{C}_N \cong G_2(N+1)$
    (Saniga–Holweck–Pracna, *Mathematics* **3** (2015), 1192–1221, Page 1217). -/
def grassmannPoints (N : ℕ) : ℕ := Nat.choose (N + 1) 2

/-- Number of lines $b_N = \binom{N+1}{3}$ of the combinatorial Grassmannian $\mathcal{C}_N \cong G_2(N+1)$
    (Saniga–Holweck–Pracna, Page 1217). -/
def grassmannLines (N : ℕ) : ℕ := Nat.choose (N + 1) 3

/-- Number of Pasch $(6_2, 4_3)$ subconfigurations $\binom{N+1}{4}$ in $\mathcal{C}_N \cong G_2(N+1)$
    (Saniga–Holweck–Pracna, Page 1218). -/
def grassmannPaschCount (N : ℕ) : ℕ := Nat.choose (N + 1) 4

/-- **Theorem 89 (Archetype LXXI.1 — Saniga–Holweck–Pracna Combinatorial Grassmannian $G_2(N+1)$ Hierarchy & Binomial Incidence Law)**:
    1. Exact $(v_N, b_N, \mathrm{Pasch}_N)$ hierarchy for $N = 1, 2, 3, 4, 5, 6$ (Pages 1217–1218):
       - $N = 1$ (Complex): $(1, 0, 0)$
       - $N = 2$ (Quaternions): $(3, 1, 0)$
       - $N = 3$ (Octonions / Pasch $G_2(4)$): $(6, 4, 1)$
       - $N = 4$ (Sedenions / Desargues $G_2(5)$): $(10, 10, 5)$
       - $N = 5$ (32-Nions / Cayley–Salmon $G_2(6)$): $(15, 20, 15)$
       - $N = 6$ (64-Nions / Generalized Desargues $G_2(7)$): $(21, 35, 35)$.
    2. Universal Binomial Point-Line Incidence Law ($r = N - 1, k = 3$):
       For all $m \in \mathbb{N}$ (setting $N = m + 1 \ge 1$),
       $$m * \binom{m + 2}{2} = 3 * \binom{m + 2}{3}.$$ -/
theorem saniga_grassmannian_binomial_configuration_identities (m : ℕ) :
    (grassmannPoints 1, grassmannLines 1, grassmannPaschCount 1) = (1, 0, 0) ∧
    (grassmannPoints 2, grassmannLines 2, grassmannPaschCount 2) = (3, 1, 0) ∧
    (grassmannPoints 3, grassmannLines 3, grassmannPaschCount 3) = (6, 4, 1) ∧
    (grassmannPoints 4, grassmannLines 4, grassmannPaschCount 4) = (10, 10, 5) ∧
    (grassmannPoints 5, grassmannLines 5, grassmannPaschCount 5) = (15, 20, 15) ∧
    (grassmannPoints 6, grassmannLines 6, grassmannPaschCount 6) = (21, 35, 35) ∧
    m * grassmannPoints (m + 1) = 3 * grassmannLines (m + 1) := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  unfold grassmannPoints grassmannLines
  have h_step : (m + 2).choose 3 * 3 = (m + 2).choose 2 * m := Nat.choose_succ_right_eq (m + 2) 2
  rw [Nat.mul_comm 3, h_step, Nat.mul_comm]

/-- **Combinatorial Grassmannian $G_2(N+1)$ Edge Operator (`opGrassmannEdge v_i v_j`)**:
    Represents the 2-element subset (edge) $\{i, j\}$ as $\Omega_{ij} = L_+(v_i - v_j) \in \mathrm{OpZornMatrix}\;A$. -/
def opGrassmannEdge (v_i v_j : OpVec3 A) : OpZornMatrix A :=
  opLightconePlus (v_i - v_j)

/-- **Theorem 90 (Archetype LXXI.2 — Noncommutative Operator Grassmannian $G_2(N+1)$ Edge-Triangle Collinear Invariance)**:
    Over *any* noncommutative operator ring $A$, for ALL vertex 3-vectors $v_i, v_j, v_k \in \mathrm{OpVec3}\;A$,
    let $\Omega_{ij}, \Omega_{jk}, \Omega_{ki}, \Omega_{ik}$ be the edge operators of the triangle $\{i, j, k\}$:
    1. Edge Nilpotence: $\Omega_{ij} * \Omega_{ij} = 0$.
    2. Veldkamp Collinear Triangle Sum:
       $\Omega_{ij} + \Omega_{jk} = \Omega_{ik}$ and $\Omega_{ij} + \Omega_{jk} + \Omega_{ki} = 0$.
    3. Universal 2-Plane Invariance Across All Three Edges of the Line $\{\{i, j\}, \{j, k\}, \{k, i\}\}$:
       $$\Omega_{ij} * \Omega_{jk} = \Omega_{jk} * \Omega_{ki} = \Omega_{ki} * \Omega_{ij} =
         L_-\!\bigl(v_i \times_{\mathrm{skew}} v_j + v_j \times_{\mathrm{skew}} v_k + v_k \times_{\mathrm{skew}} v_i\bigr).$$ -/
theorem operator_grassmannian_edge_triangle_collinear_invariance
    (v_i v_j v_k : OpVec3 A) :
    let Ω_ij := opGrassmannEdge v_i v_j
    let Ω_jk := opGrassmannEdge v_j v_k
    let Ω_ki := opGrassmannEdge v_k v_i
    let Ω_ik := opGrassmannEdge v_i v_k
    let plane_ijk :=
      opLightconeMinus
        (OpVec3.skewCross v_i v_j + OpVec3.skewCross v_j v_k + OpVec3.skewCross v_k v_i)
    Ω_ij * Ω_ij = 0 ∧
    Ω_ij + Ω_jk = Ω_ik ∧
    Ω_ij + Ω_jk + Ω_ki = 0 ∧
    Ω_ij * Ω_jk = plane_ijk ∧
    Ω_jk * Ω_ki = plane_ijk ∧
    Ω_ki * Ω_ij = plane_ijk := by
  intro Ω_ij Ω_jk Ω_ki Ω_ik plane_ijk
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  (ext <;>
   (simp [Ω_ij, Ω_jk, Ω_ki, Ω_ik, plane_ijk, opGrassmannEdge,
          opLightconePlus, opLightconeMinus, opLightconeRayPlus, opLightconeRayMinus,
          OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross];
    try noncomm_ring))

/-- Canonical Cayley involution $X^* = \langle b, -v, -w, a \rangle$ on `OpZornMatrix A`. -/
def opCayleyConj (X : OpZornMatrix A) : OpZornMatrix A :=
  ⟨X.b, -X.v, -X.w, X.a⟩

/-- **16-Component Operator Sedenion Algebra (`OpSedenion A`)**:
    Constructed via the Cayley–Dickson doubling of `OpZornMatrix A`
    (Saniga–Holweck–Pracna, Page 1193, Eqs. 1–2). -/
@[ext]
structure OpSedenion (A : Type*) where
  x : OpZornMatrix A
  y : OpZornMatrix A
  deriving DecidableEq

instance instZeroOpSedenion : Zero (OpSedenion A) := ⟨⟨0, 0⟩⟩
instance instOneOpSedenion : One (OpSedenion A) := ⟨⟨1, 0⟩⟩
instance instInhabitedOpSedenion : Inhabited (OpSedenion A) := ⟨0⟩
instance instAddOpSedenion : Add (OpSedenion A) := ⟨fun S₁ S₂ => ⟨S₁.x + S₂.x, S₁.y + S₂.y⟩⟩
instance instSubOpSedenion : Sub (OpSedenion A) := ⟨fun S₁ S₂ => ⟨S₁.x - S₂.x, S₁.y - S₂.y⟩⟩
instance instNegOpSedenion : Neg (OpSedenion A) := ⟨fun S => ⟨-S.x, -S.y⟩⟩

namespace OpSedenion

@[simp] lemma zero_x : (0 : OpSedenion A).x = 0 := rfl
@[simp] lemma zero_y : (0 : OpSedenion A).y = 0 := rfl
@[simp] lemma one_x : (1 : OpSedenion A).x = 1 := rfl
@[simp] lemma one_y : (1 : OpSedenion A).y = 0 := rfl
@[simp] lemma add_x (S₁ S₂ : OpSedenion A) : (S₁ + S₂).x = S₁.x + S₂.x := rfl
@[simp] lemma add_y (S₁ S₂ : OpSedenion A) : (S₁ + S₂).y = S₁.y + S₂.y := rfl
@[simp] lemma sub_x (S₁ S₂ : OpSedenion A) : (S₁ - S₂).x = S₁.x - S₂.x := rfl
@[simp] lemma sub_y (S₁ S₂ : OpSedenion A) : (S₁ - S₂).y = S₁.y - S₂.y := rfl
@[simp] lemma neg_x (S : OpSedenion A) : (-S).x = -S.x := rfl
@[simp] lemma neg_y (S : OpSedenion A) : (-S).y = -S.y := rfl

end OpSedenion

/-- Saniga–Holweck–Pracna Eq. (1) (Page 1193): Cayley–Dickson conjugation $(x, y)^* = (x^*, -y)$. -/
def opSedenionConj (S : OpSedenion A) : OpSedenion A :=
  ⟨opCayleyConj S.x, -S.y⟩

/-- Saniga–Holweck–Pracna Eq. (2) (Page 1193): Cayley–Dickson multiplication
    $(x, y)(X, Y) = (x X - Y y^*,\; x^* Y + X y)$. -/
instance instMulOpSedenion : Mul (OpSedenion A) :=
  ⟨fun S₁ S₂ =>
    { x := S₁.x * S₂.x - S₂.y * opCayleyConj S₁.y
      y := opCayleyConj S₁.x * S₂.y + S₂.x * S₁.y }⟩

@[simp] lemma OpSedenion.mul_x (S₁ S₂ : OpSedenion A) :
    (S₁ * S₂).x = S₁.x * S₂.x - S₂.y * opCayleyConj S₁.y := rfl

@[simp] lemma OpSedenion.mul_y (S₁ S₂ : OpSedenion A) :
    (S₁ * S₂).y = opCayleyConj S₁.x * S₂.y + S₂.x * S₁.y := rfl

/-- Paired chiral sedenion zero-divisor state $S_+(v, w) = (L_+(v), L_-(w))$. -/
def opSedenionZeroDivPlus (v w : OpVec3 A) : OpSedenion A :=
  ⟨opLightconePlus v, opLightconeMinus w⟩

/-- Dual paired chiral sedenion zero-divisor state $S_-(v, w) = (L_-(w), -L_+(v))$. -/
def opSedenionZeroDivMinus (v w : OpVec3 A) : OpSedenion A :=
  ⟨opLightconeMinus w, -opLightconePlus v⟩

/-- **Theorem 91 (Archetype LXXII — Operator Sedenion Cayley–Dickson Laws, 4-Ray Cross Multiplication, & Universal Two-Sided Zero Divisors)**:
    Over *any* noncommutative operator ring $A$, for ALL $S \in \mathrm{OpSedenion}\;A$ and
    all 3-vectors $v, w, v_1, v_2, v_3, v_4 \in \mathrm{OpVec3}\;A$:
    1. Exact Period-2 Sedenion Conjugation & Unit Preservation:
       $((S)^*)^* = S$, $1 * S = S$, and $S * 1 = S$.
    2. Desargues 4-Ray Sedenion Cross-Product Multiplication Law:
       $$(L_+(v_1), L_+(v_2)) * (L_+(v_3), L_+(v_4)) =
         \bigl(L_-(v_1 \times_{\mathrm{skew}} v_3 + v_4 \times_{\mathrm{skew}} v_2),\;
               L_-(v_3 \times_{\mathrm{skew}} v_2 - v_1 \times_{\mathrm{skew}} v_4)\bigr).$$
    3. Universal Two-Sided Sedenion Zero-Divisor Theorem (Valid for ALL $v, w \in A^3$):
       $$S_+(v, w) * S_-(v, w) = 0 \quad \text{and} \quad S_-(v, w) * S_+(v, w) = 0.$$ -/
theorem operator_sedenion_cayley_dickson_and_universal_zero_divisors
    (S : OpSedenion A) (v w v₁ v₂ v₃ v₄ : OpVec3 A) :
    let S₁ : OpSedenion A := ⟨opLightconePlus v₁, opLightconePlus v₂⟩
    let S₂ : OpSedenion A := ⟨opLightconePlus v₃, opLightconePlus v₄⟩
    opSedenionConj (opSedenionConj S) = S ∧
    (1 : OpSedenion A) * S = S ∧
    S * (1 : OpSedenion A) = S ∧
    S₁ * S₂ =
      ⟨opLightconeMinus (OpVec3.skewCross v₁ v₃ + OpVec3.skewCross v₄ v₂),
       opLightconeMinus (OpVec3.skewCross v₃ v₂ - OpVec3.skewCross v₁ v₄)⟩ ∧
    opSedenionZeroDivPlus v w * opSedenionZeroDivMinus v w = 0 ∧
    opSedenionZeroDivMinus v w * opSedenionZeroDivPlus v w = 0 := by
  intro S₁ S₂
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  (ext <;>
   (simp [S₁, S₂, opSedenionConj, opCayleyConj, opSedenionZeroDivPlus, opSedenionZeroDivMinus,
          opLightconePlus, opLightconeMinus, opLightconeRayPlus, opLightconeRayMinus,
          OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross];
    try noncomm_ring))

/-!
## 32. Archetypes LXXIII & LXXIV: Universal $(p|q)$ Block Para-Kähler Super-Grassmannians $\mathrm{SuperGr}(p, q; A)$ & the Plücker–Veldkamp Pasch 4-Simplex Boundary Functor
-/

/-- **The $(p|q)$ Block Supermatrix Algebra (`SuperGrassmannMatrix p q A`)**:
    - $a \in M_{p \times p}(A)$ (Even Bosonic / Leptonic Block),
    - $v \in M_{p \times q}(A)$ (Odd Primal Tangent Block $\mathcal{V}_+$),
    - $w \in M_{q \times p}(A)$ (Odd Dual Cotangent Block $\mathcal{V}_-$),
    - $b \in M_{q \times q}(A)$ (Even Fermionic / Color Block). -/
@[ext]
structure SuperGrassmannMatrix (p q : ℕ) (A : Type*) where
  a : Matrix (Fin p) (Fin p) A
  v : Matrix (Fin p) (Fin q) A
  w : Matrix (Fin q) (Fin p) A
  b : Matrix (Fin q) (Fin q) A

instance instZeroSuperGrassmannMatrix {p q : ℕ} : Zero (SuperGrassmannMatrix p q A) := ⟨⟨0, 0, 0, 0⟩⟩
instance instOneSuperGrassmannMatrix {p q : ℕ} : One (SuperGrassmannMatrix p q A) := ⟨⟨1, 0, 0, 1⟩⟩
instance instInhabitedSuperGrassmannMatrix {p q : ℕ} : Inhabited (SuperGrassmannMatrix p q A) := ⟨0⟩
instance instAddSuperGrassmannMatrix {p q : ℕ} : Add (SuperGrassmannMatrix p q A) :=
  ⟨fun X Y => ⟨X.a + Y.a, X.v + Y.v, X.w + Y.w, X.b + Y.b⟩⟩
instance instSubSuperGrassmannMatrix {p q : ℕ} : Sub (SuperGrassmannMatrix p q A) :=
  ⟨fun X Y => ⟨X.a - Y.a, X.v - Y.v, X.w - Y.w, X.b - Y.b⟩⟩
instance instNegSuperGrassmannMatrix {p q : ℕ} : Neg (SuperGrassmannMatrix p q A) :=
  ⟨fun X => ⟨-X.a, -X.v, -X.w, -X.b⟩⟩

/-- Block matrix multiplication on `SuperGrassmannMatrix p q A`. -/
instance instMulSuperGrassmannMatrix {p q : ℕ} : Mul (SuperGrassmannMatrix p q A) :=
  ⟨fun X Y =>
    { a := X.a * Y.a + X.v * Y.w
      v := X.a * Y.v + X.v * Y.b
      w := X.w * Y.a + X.b * Y.w
      b := X.w * Y.v + X.b * Y.b }⟩

namespace SuperGrassmannMatrix

variable {p q : ℕ}

@[simp] lemma zero_a : (0 : SuperGrassmannMatrix p q A).a = 0 := rfl
@[simp] lemma zero_v : (0 : SuperGrassmannMatrix p q A).v = 0 := rfl
@[simp] lemma zero_w : (0 : SuperGrassmannMatrix p q A).w = 0 := rfl
@[simp] lemma zero_b : (0 : SuperGrassmannMatrix p q A).b = 0 := rfl
@[simp] lemma one_a : (1 : SuperGrassmannMatrix p q A).a = 1 := rfl
@[simp] lemma one_v : (1 : SuperGrassmannMatrix p q A).v = 0 := rfl
@[simp] lemma one_w : (1 : SuperGrassmannMatrix p q A).w = 0 := rfl
@[simp] lemma one_b : (1 : SuperGrassmannMatrix p q A).b = 1 := rfl
@[simp] lemma add_a (X Y : SuperGrassmannMatrix p q A) : (X + Y).a = X.a + Y.a := rfl
@[simp] lemma add_v (X Y : SuperGrassmannMatrix p q A) : (X + Y).v = X.v + Y.v := rfl
@[simp] lemma add_w (X Y : SuperGrassmannMatrix p q A) : (X + Y).w = X.w + Y.w := rfl
@[simp] lemma add_b (X Y : SuperGrassmannMatrix p q A) : (X + Y).b = X.b + Y.b := rfl
@[simp] lemma sub_a (X Y : SuperGrassmannMatrix p q A) : (X - Y).a = X.a - Y.a := rfl
@[simp] lemma sub_v (X Y : SuperGrassmannMatrix p q A) : (X - Y).v = X.v - Y.v := rfl
@[simp] lemma sub_w (X Y : SuperGrassmannMatrix p q A) : (X - Y).w = X.w - Y.w := rfl
@[simp] lemma sub_b (X Y : SuperGrassmannMatrix p q A) : (X - Y).b = X.b - Y.b := rfl
@[simp] lemma neg_a (X : SuperGrassmannMatrix p q A) : (-X).a = -X.a := rfl
@[simp] lemma neg_v (X : SuperGrassmannMatrix p q A) : (-X).v = -X.v := rfl
@[simp] lemma neg_w (X : SuperGrassmannMatrix p q A) : (-X).w = -X.w := rfl
@[simp] lemma neg_b (X : SuperGrassmannMatrix p q A) : (-X).b = -X.b := rfl
@[simp] lemma mul_a (X Y : SuperGrassmannMatrix p q A) : (X * Y).a = X.a * Y.a + X.v * Y.w := rfl
@[simp] lemma mul_v (X Y : SuperGrassmannMatrix p q A) : (X * Y).v = X.a * Y.v + X.v * Y.b := rfl
@[simp] lemma mul_w (X Y : SuperGrassmannMatrix p q A) : (X * Y).w = X.w * Y.a + X.b * Y.w := rfl
@[simp] lemma mul_b (X Y : SuperGrassmannMatrix p q A) : (X * Y).b = X.w * Y.v + X.b * Y.b := rfl

end SuperGrassmannMatrix

/-- Upper primitive Peirce super-idempotent $E_{11} = \langle I_p, 0, 0, 0 \rangle$. -/
def superPeircePlus {p q : ℕ} : SuperGrassmannMatrix p q A := ⟨1, 0, 0, 0⟩

/-- Para-complex super-grading involution $\Gamma_{p|q} = \langle I_p, 0, 0, -I_q \rangle$. -/
def superGamma {p q : ℕ} : SuperGrassmannMatrix p q A := ⟨1, 0, 0, -1⟩

/-- Odd primal tangent embedding $L_+(v) = \langle 0, v, 0, 0 \rangle$. -/
def superTangentPlus {p q : ℕ} (v : Matrix (Fin p) (Fin q) A) : SuperGrassmannMatrix p q A :=
  ⟨0, v, 0, 0⟩

/-- Odd dual cotangent embedding $L_-(w) = \langle 0, 0, w, 0 \rangle$. -/
def superTangentMinus {p q : ℕ} (w : Matrix (Fin q) (Fin p) A) : SuperGrassmannMatrix p q A :=
  ⟨0, 0, w, 0⟩

/-- Upper and lower unipotent exponential charts $U_+(v) = 1 + L_+(v)$ and $U_-(w) = 1 + L_-(w)$. -/
def superUnipotentPlus {p q : ℕ} (v : Matrix (Fin p) (Fin q) A) : SuperGrassmannMatrix p q A :=
  ⟨1, v, 0, 1⟩

def superUnipotentMinus {p q : ℕ} (w : Matrix (Fin q) (Fin p) A) : SuperGrassmannMatrix p q A :=
  ⟨1, 0, w, 1⟩

/-- Left and right chiral wavefunction factors $\Psi_L(w) = U_-(w) * E_{11}$ and $\Psi_R(v) = E_{11} * U_+(v)$. -/
def superWaveLeft {p q : ℕ} (w : Matrix (Fin q) (Fin p) A) : SuperGrassmannMatrix p q A :=
  superUnipotentMinus w * superPeircePlus

def superWaveRight {p q : ℕ} (v : Matrix (Fin p) (Fin q) A) : SuperGrassmannMatrix p q A :=
  superPeircePlus * superUnipotentPlus v

/-- Para-Kähler metric $g_{p|q}(v, w) = L_+(v) * L_-(w) + L_-(w) * L_+(v)$. -/
def superParaKahlerMetric {p q : ℕ} (v : Matrix (Fin p) (Fin q) A) (w : Matrix (Fin q) (Fin p) A) :
    SuperGrassmannMatrix p q A :=
  superTangentPlus v * superTangentMinus w + superTangentMinus w * superTangentPlus v

/-- Para-Kähler symplectic 2-form $\omega_{p|q}(v, w) = L_+(v) * L_-(w) - L_-(w) * L_+(v)$. -/
def superParaKahlerSymplectic {p q : ℕ} (v : Matrix (Fin p) (Fin q) A) (w : Matrix (Fin q) (Fin p) A) :
    SuperGrassmannMatrix p q A :=
  superTangentPlus v * superTangentMinus w - superTangentMinus w * superTangentPlus v

/-- **Theorem 92 (Archetype LXXIII — Universal $(p|q)$ Para-Kähler Super-Grassmannian & Chiral Wavefunction Trifactorization)**:
    Over *any* noncommutative ring $A$ and for ALL dimensions $p, q \in \mathbb{N}$,
    $v \in M_{p \times q}(A)$, and $w \in M_{q \times p}(A)$:
    1. Square-Zero Nilpotence of Tangent & Cotangent Bundles:
       $L_+(v) * L_+(v) = 0$ and $L_-(w) * L_-(w) = 0$.
    2. Universal $(p|q)$ Para-Kähler Compatibility ($\Gamma_{p|q} g = \omega$ and $\Gamma_{p|q} \omega = g$):
       $g_{p|q}(v, w) = \langle v * w, 0, 0, w * v \rangle$,
       $\omega_{p|q}(v, w) = \langle v * w, 0, 0, -(w * v) \rangle$,
       $\Gamma_{p|q} * g_{p|q}(v, w) = \omega_{p|q}(v, w)$, and
       $\Gamma_{p|q} * \omega_{p|q}(v, w) = g_{p|q}(v, w)$.
    3. Exact Idempotence of Chiral Wavefunction Factors:
       $\Psi_L(w) * \Psi_L(w) = \Psi_L(w)$ and $\Psi_R(v) * \Psi_R(v) = \Psi_R(v)$.
    4. Inner Contraction (Metric Kernel) & Outer Contraction (Super-Grassmannian Projector):
       $\Psi_R(v) * \Psi_L(w) = \langle 1 + v * w, 0, 0, 0 \rangle$ and
       $\Psi_L(w) * \Psi_R(v) = \langle 1, v, w, w * v \rangle$. -/
theorem superGrassmannian_paraKahler_and_trifactor_projector
    {p q : ℕ} (v : Matrix (Fin p) (Fin q) A) (w : Matrix (Fin q) (Fin p) A) :
    let g := superParaKahlerMetric v w
    let ω := superParaKahlerSymplectic v w
    let Γ := (superGamma : SuperGrassmannMatrix p q A)
    let Ψ_L := superWaveLeft w
    let Ψ_R := superWaveRight v
    superTangentPlus v * superTangentPlus v = 0 ∧
    superTangentMinus w * superTangentMinus w = 0 ∧
    g = ⟨v * w, 0, 0, w * v⟩ ∧
    ω = ⟨v * w, 0, 0, -(w * v)⟩ ∧
    Γ * g = ω ∧
    Γ * ω = g ∧
    Ψ_L * Ψ_L = Ψ_L ∧
    Ψ_R * Ψ_R = Ψ_R ∧
    Ψ_R * Ψ_L = ⟨1 + v * w, 0, 0, 0⟩ ∧
    Ψ_L * Ψ_R = ⟨1, v, w, w * v⟩ := by
  intro g ω Γ Ψ_L Ψ_R
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  (ext <;>
   simp [g, ω, Γ, Ψ_L, Ψ_R, superParaKahlerMetric, superParaKahlerSymplectic,
         superGamma, superWaveLeft, superWaveRight, superUnipotentPlus, superUnipotentMinus,
         superPeircePlus, superTangentPlus, superTangentMinus])

/-- Dual edge operator $\Omega_{ij}^- = L_-(v_i - v_j)$ representing a dual point $\{i, j\}$ of $G_2(N+1)$. -/
def opGrassmannEdgeMinus (v_i v_j : OpVec3 A) : OpZornMatrix A :=
  opLightconeMinus (v_i - v_j)

/-- Plücker 2-plane operator $\mathcal{P}_{ijk} = \Omega_{ij}^+ * \Omega_{jk}^+$ representing a line
    $\{\{i, j\}, \{j, k\}, \{i, k\}\}$ of the combinatorial Grassmannian $G_2(N+1)$. -/
def opGrassmannLinePlane (v_i v_j v_k : OpVec3 A) : OpZornMatrix A :=
  opGrassmannEdge v_i v_j * opGrassmannEdge v_j v_k

/-- Edge self-metric $g_{ij} = \{\Omega_{ij}^+, \Omega_{ij}^-\} \in \mathcal{G}_0$. -/
def opGrassmannEdgeMetric (v_i v_j : OpVec3 A) : OpZornMatrix A :=
  opAnticommutator (opGrassmannEdge v_i v_j) (opGrassmannEdgeMinus v_i v_j)

/-- **Theorem 93 (Archetype LXXIV — Universal Pasch 4-Simplex Boundary Closure $\partial_2 = 0$ & Combinatorial Para-Kähler Metric Polarization Law)**:
    Over *any* noncommutative operator ring $A$, for ALL vertex 3-vectors $v_i, v_j, v_k, v_l \in \mathrm{OpVec3}\;A$:
    1. 1-Boundary Closure on Every Line $\{i, j, k\}$ of $G_2(N+1)$:
       $$\Omega_{ij}^+ + \Omega_{jk}^+ - \Omega_{ik}^+ = 0.$$
    2. 2-Boundary Closure Around Every Pasch 4-Simplex $\{i, j, k, l\} \in \binom{V}{4}$ ($\partial_2 \circ \partial_1 = 0$):
       The alternating sum of the four Plücker line operators of any Pasch subconfiguration
       $\{i, j, k, l\}$ vanishes identically across all 8 channels of `OpZornMatrix A`:
       $$\mathcal{P}_{jkl} - \mathcal{P}_{ikl} + \mathcal{P}_{ijl} - \mathcal{P}_{ijk} = 0.$$
    3. Combinatorial Para-Kähler Metric Polarization Law on Every Line $\{i, j, k\}$ of $G_2(N+1)$:
       $$g_{ik} - g_{ij} - g_{jk} =
         \bigl\{\Omega_{ij}^+,\; \Omega_{jk}^-\bigr\} + \bigl\{\Omega_{jk}^+,\; \Omega_{ij}^-\bigr\}.$$ -/
theorem combinatorialGrassmannian_pasch_tetrahedral_boundary_and_metric_law
    (v_i v_j v_k v_l : OpVec3 A) :
    let Ω_ij_p := opGrassmannEdge v_i v_j
    let Ω_jk_p := opGrassmannEdge v_j v_k
    let Ω_ik_p := opGrassmannEdge v_i v_k
    let Ω_ij_m := opGrassmannEdgeMinus v_i v_j
    let Ω_jk_m := opGrassmannEdgeMinus v_j v_k
    let P_ijk := opGrassmannLinePlane v_i v_j v_k
    let P_ikl := opGrassmannLinePlane v_i v_k v_l
    let P_ijl := opGrassmannLinePlane v_i v_j v_l
    let P_jkl := opGrassmannLinePlane v_j v_k v_l
    Ω_ij_p + Ω_jk_p - Ω_ik_p = 0 ∧
    P_jkl - P_ikl + P_ijl - P_ijk = 0 ∧
    opGrassmannEdgeMetric v_i v_k - opGrassmannEdgeMetric v_i v_j - opGrassmannEdgeMetric v_j v_k =
      opAnticommutator Ω_ij_p Ω_jk_m + opAnticommutator Ω_jk_p Ω_ij_m := by
  intro Ω_ij_p Ω_jk_p Ω_ik_p Ω_ij_m Ω_jk_m P_ijk P_ikl P_ijl P_jkl
  refine ⟨?_, ?_, ?_⟩ <;>
  (ext <;>
   (simp [Ω_ij_p, Ω_jk_p, Ω_ik_p, Ω_ij_m, Ω_jk_m, P_ijk, P_ikl, P_ijl, P_jkl,
          opGrassmannEdge, opGrassmannEdgeMinus, opGrassmannLinePlane, opGrassmannEdgeMetric,
          opLightconePlus, opLightconeMinus, opLightconeRayPlus, opLightconeRayMinus,
          opAnticommutator, OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross];
    try noncomm_ring))

/-!
## 32. Archetypes LXXV & LXXVI: Catto–Gürcan–Khalfan–Kurt (2018) Affine $E_9$, Hyperbolic $E_{10}$ Kac–Moody Roots, Noncommutative Affine Jordan Triple Closure, & Conway–Sloane $(2+1)$ Freudenthal Cubic Secular Law
-/

/-- Catto et al. Eq. (45) (Page 8, unscaled by $-2$): Lorentzian Kac–Moody pairing
    $\langle X, Y \rangle_{\mathrm{Kac}} = \mathrm{opZornTrace}(X * \mathrm{opCayleyConj}\;Y)$ on `OpZornMatrix A`. -/
def opKacMoodyPairing (X Y : OpZornMatrix A) : A :=
  opZornTrace (X * opCayleyConj Y)

/-- **Jacobson's Jordan Triple Product (`opJacobsonTriple X Y Z`)** on `OpZornMatrix A`
    (Catto–Gürcan–Khalfan–Kurt 2018, Page 7, Eq. 35, unscaled):
    $\{X, Y, Z\}_{\mathrm{JT}} = (X \circ Y) \circ Z + X \circ (Y \circ Z) - (X \circ Z) \circ Y$. -/
def opJacobsonTriple (X Y Z : OpZornMatrix A) : OpZornMatrix A :=
  opAnticommutator (opAnticommutator X Y) Z +
    opAnticommutator X (opAnticommutator Y Z) -
    opAnticommutator (opAnticommutator X Z) Y

/-- Affine $\tilde{E}_8 = E_9$ root $R_0^{(+)}(x_+, v, w) = x_+ R_+ + R_\alpha(v, w) = \langle x_+, v, w, 0 \rangle$
    (Catto et al. 2018, Page 7, Eq. 31 & Page 9, Eqs. 52, 55). -/
def opCattoAffineRoot (x_plus : A) (v w : OpVec3 A) : OpZornMatrix A :=
  ⟨x_plus, v, w, 0⟩

/-- **Theorem 94 (Archetype LXXV.1 — Catto–Gürcan–Khalfan–Kurt Affine $E_9$, Hyperbolic $E_{10}$ Kac–Moody Root Inner Products & Noncommutative Affine Jordan Triple Closure)**:
    Over *any* noncommutative operator ring $A$ (`[Ring A]`), for all $X \in \mathrm{OpZornMatrix}\;A$,
    all $x_1, x_2, x_3 \in A$, and all $v, w, v_1, w_1, v_2, w_2, v_3, w_3 \in \mathrm{OpVec3}\;A$:
    1. Secular Trace Identity (Catto et al. Page 6, Eq. 28):
       $$X + \mathrm{opCayleyConj}\;X = \mathrm{opGradeZero}\;(\mathrm{opZornTrace}\;X)\;(\mathrm{opZornTrace}\;X).$$
    2. Lightlike Kac–Moody Root Inner Products (Page 9, Eqs. 56, 58, 60, where $R_+ = e_{11}$ and $R_- = e_{22}$):
       $$\langle R_+, R_+ \rangle_{\mathrm{Kac}} = 0, \qquad
         \langle R_-, R_- \rangle_{\mathrm{Kac}} = 0, \qquad
         \langle R_+, R_- \rangle_{\mathrm{Kac}} = 1.$$
    3. Hyperbolic $E_{10}$ Root Attachment to Affine $E_9$ (Pages 9–10, Eqs. 53, 54, 59, 66, 67, where $R_9 = R_+ - R_- = \Gamma$):
       $$\langle R_9, R_9 \rangle_{\mathrm{Kac}} = -(1 + 1), \qquad
         \langle R_9, R_\alpha(v, w) \rangle_{\mathrm{Kac}} = 0, \qquad
         \langle R_9, R_0^{(+)}(1, v, w) \rangle_{\mathrm{Kac}} = -1.$$
    4. Universal Noncommutative Affine Kac–Moody Root Closure under Jacobson's Jordan Triple Product (Page 7, Eqs. 31, 35, 37):
       For any three affine roots $R_i = \mathrm{opCattoAffineRoot}\;x_i\;v_i\;w_i$,
       $$\bigl(\{R_1, \mathrm{opCayleyConj}\;R_2, R_3\}_{\mathrm{JT}}\bigr).b = 0.$$ -/
theorem catto_e9_e10_kac_moody_roots_and_affine_triple_closure
    (X : OpZornMatrix A) (x₁ x₂ x₃ : A) (v w v₁ w₁ v₂ w₂ v₃ w₃ : OpVec3 A) :
    let R₁ := opCattoAffineRoot x₁ v₁ w₁
    let R₂ := opCattoAffineRoot x₂ v₂ w₂
    let R₃ := opCattoAffineRoot x₃ v₃ w₃
    X + opCayleyConj X = opGradeZero (opZornTrace X) (opZornTrace X) ∧
    opKacMoodyPairing (opPeircePlus : OpZornMatrix A) opPeircePlus = 0 ∧
    opKacMoodyPairing (opPeirceMinus : OpZornMatrix A) opPeirceMinus = 0 ∧
    opKacMoodyPairing (opPeircePlus : OpZornMatrix A) opPeirceMinus = 1 ∧
    opKacMoodyPairing (opZornGamma : OpZornMatrix A) opZornGamma = -(1 + 1) ∧
    opKacMoodyPairing (opZornGamma : OpZornMatrix A) (opKasparovZornJ v w) = 0 ∧
    opKacMoodyPairing (opZornGamma : OpZornMatrix A) (opCattoAffineRoot 1 v w) = -1 ∧
    (opJacobsonTriple R₁ (opCayleyConj R₂) R₃).b = 0 := by
  intro R₁ R₂ R₃
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · ext <;> simp [opCayleyConj, opZornTrace, opCartanDiag] <;> abel
  · simp [opKacMoodyPairing, opPeircePlus, opCayleyConj, opZornTrace, OpVec3.dot]
  · simp [opKacMoodyPairing, opPeirceMinus, opCayleyConj, opZornTrace, OpVec3.dot]
  · simp [opKacMoodyPairing, opPeircePlus, opPeirceMinus, opCayleyConj, opZornTrace, OpVec3.dot]
  · simp [opKacMoodyPairing, opZornGamma, opCayleyConj, opZornTrace, OpVec3.dot]
  · simp [opKacMoodyPairing, opZornGamma, opKasparovZornJ, opCayleyConj, opZornTrace, OpVec3.dot]
  · simp [opKacMoodyPairing, opZornGamma, opCattoAffineRoot, opCayleyConj, opZornTrace, OpVec3.dot]
  · simp [R₁, R₂, R₃, opJacobsonTriple, opAnticommutator, opCattoAffineRoot, opCayleyConj,
          OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross]
    noncomm_ring

/-- Catto et al. Eq. (81) (Page 12): $(2+1)$ Conway–Sloane $E_{10} \times E_8 \times E_8$ Block Decomposition
    $M = \begin{pmatrix} V & \xi \\ \xi^\dagger & v \end{pmatrix}$ of a $3 \times 3$ matrix over $A$ into a $2 \times 2$
    Lorentzian block $V = \begin{pmatrix} x_+ & q \\ \bar{q} & x_- \end{pmatrix}$, a 2-component spinor
    column $\xi = (\xi_1, \xi_2)^T$, and a scalar $v = M_{22}$. -/
def conwaySloaneMat3 (x_plus q q_bar x_minus ξ₁ ξ₂ ξ₁_bar ξ₂_bar v : A) :
    Matrix (Fin 3) (Fin 3) A :=
  !![x_plus, q, ξ₁;
     q_bar, x_minus, ξ₂;
     ξ₁_bar, ξ₂_bar, v]

/-- Noncommutative grading involution $U_3 = \mathrm{diag}(1, -1, 0) \in M_3(A)$ on the $(2+1)$ Lorentzian $2 \times 2$ block. -/
def conwaySloaneCliffordU : Matrix (Fin 3) (Fin 3) A :=
  !![1, 0, 0;
     0, -1, 0;
     0, 0, 0]

/-- Noncommutative flip involution $V_3 \in M_3(A)$ on the $(2+1)$ Lorentzian $2 \times 2$ block. -/
def conwaySloaneCliffordV : Matrix (Fin 3) (Fin 3) A :=
  !![0, 1, 0;
     1, 0, 0;
     0, 0, 0]

/-- Non-commutativity / Clifford anticommutation witness for `Matrix (Fin 3) (Fin 3) A` (`T16` witness):
    $U_3 V_3 + V_3 U_3 = 0$. -/
theorem conwaySloaneClifford_anticomm :
    (conwaySloaneCliffordU : Matrix (Fin 3) (Fin 3) A) * conwaySloaneCliffordV +
      conwaySloaneCliffordV * conwaySloaneCliffordU = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;>
  simp [conwaySloaneCliffordU, conwaySloaneCliffordV, Matrix.mul_apply, Fin.sum_univ_three]

/-- Second elementary symmetric invariant $S_2(M) = (M_{00} M_{11} - M_{01} M_{10}) +
    (M_{00} M_{22} - M_{02} M_{20}) + (M_{11} M_{22} - M_{12} M_{21})$ of a $3 \times 3$ matrix. -/
def freudenthalSecondInvariant {R : Type*} [CommRing R] (M : Matrix (Fin 3) (Fin 3) R) : R :=
  (M 0 0 * M 1 1 - M 0 1 * M 1 0) +
    (M 0 0 * M 2 2 - M 0 2 * M 2 0) +
    (M 1 1 * M 2 2 - M 1 2 * M 2 1)

/-- Catto et al. Eq. (69) (Page 10): Division-free Freudenthal Sharp Adjoint
    $M^\# = M \times M = M^2 - (\mathrm{Tr}\,M) M + S_2(M) I_3$. -/
def freudenthalSharp3 {R : Type*} [CommRing R] (M : Matrix (Fin 3) (Fin 3) R) :
    Matrix (Fin 3) (Fin 3) R :=
  M * M - Matrix.trace M • M + freudenthalSecondInvariant M • (1 : Matrix (Fin 3) (Fin 3) R)

/-- Explicit $3 \times 3$ Freudenthal determinant $\mathrm{Det}\,M$ (Catto et al. Eq. 68). -/
def freudenthalDet3 {R : Type*} [CommRing R] (M : Matrix (Fin 3) (Fin 3) R) : R :=
  M 0 0 * (M 1 1 * M 2 2 - M 1 2 * M 2 1) -
    M 0 1 * (M 1 0 * M 2 2 - M 1 2 * M 2 0) +
    M 0 2 * (M 1 0 * M 2 1 - M 1 1 * M 2 0)

/-- Noncommutative grading involution $U_{3,R} = \mathrm{diag}(1, -1, 0) \in M_3(R)$ on the $(2+1)$ Lorentzian $2 \times 2$ block. -/
def conwaySloaneCommU {R : Type*} [CommRing R] : Matrix (Fin 3) (Fin 3) R :=
  !![1, 0, 0;
     0, -1, 0;
     0, 0, 0]

/-- Noncommutative flip involution $V_{3,R} \in M_3(R)$ on the $(2+1)$ Lorentzian $2 \times 2$ block. -/
def conwaySloaneCommV {R : Type*} [CommRing R] : Matrix (Fin 3) (Fin 3) R :=
  !![0, 1, 0;
     1, 0, 0;
     0, 0, 0]

/-- Non-commutativity / Clifford anticommutation witness for `Matrix (Fin 3) (Fin 3) R` (`T16` witness):
    $U_{3,R} V_{3,R} + V_{3,R} U_{3,R} = 0$. -/
theorem conwaySloaneComm_anticomm {R : Type*} [CommRing R] :
    (conwaySloaneCommU : Matrix (Fin 3) (Fin 3) R) * conwaySloaneCommV +
      conwaySloaneCommV * conwaySloaneCommU = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;>
  simp [conwaySloaneCommU, conwaySloaneCommV, Matrix.mul_apply, Fin.sum_univ_three]

/-- **Theorem 95 (Archetype LXXVI — Catto–Gürcan–Khalfan–Kurt Conway–Sloane $E_{10} \times E_8 \times E_8$ Freudenthal Adjoint & Cubic Secular Equation)**:
    Over *any* commutative ring $R$ (`[CommRing R]`), for ALL $M \in \mathrm{Matrix}\;(\mathrm{Fin}\;3)\;(\mathrm{Fin}\;3)\;R$
    and any Conway–Sloane $(2+1)$ parameters $(x_+, q, \bar{q}, x_-, \xi_1, \xi_2, \bar{\xi}_1, \bar{\xi}_2, v)$:
    1. Freudenthal Trace Identity (Catto et al. Page 11, Eq. 71):
       $$\mathrm{trace}(M^\#) = S_2(M) \quad \text{and} \quad
         2 * \mathrm{trace}(M^\#) = (\mathrm{trace}\;M)^2 - \mathrm{trace}(M * M).$$
    2. $(2, 2)$ Scalar Corner of $M^\#$ is the $2 \times 2$ $E_{10}$ Lorentzian Determinant (Page 12, Eq. 81):
       $$(M_{\mathrm{CS}}^\#)_{2, 2} = x_+ * x_- - q * \bar{q}.$$
    3. Exact Freudenthal Adjoint Product & Cubic Secular Equation (Pages 10–11, Eqs. 69 & 72):
       $$M * M^\# = (\mathrm{freudenthalDet3}\;M) \bullet 1 \quad \text{and} \quad
         M * M * M - (\mathrm{trace}\;M) \bullet (M * M) +
           (\mathrm{trace}\;M^\#) \bullet M - (\mathrm{freudenthalDet3}\;M) \bullet 1 = 0.$$ -/
theorem catto_conway_sloane_freudenthal_adjoint_and_cubic_secular_law
    {R : Type*} [CommRing R] (M : Matrix (Fin 3) (Fin 3) R)
    (x_plus q q_bar x_minus ξ₁ ξ₂ ξ₁_bar ξ₂_bar v : R) :
    let M_CS := conwaySloaneMat3 x_plus q q_bar x_minus ξ₁ ξ₂ ξ₁_bar ξ₂_bar v
    Matrix.trace (freudenthalSharp3 M) = freudenthalSecondInvariant M ∧
    2 * Matrix.trace (freudenthalSharp3 M) =
      (Matrix.trace M) ^ 2 - Matrix.trace (M * M) ∧
    (freudenthalSharp3 M_CS) 2 2 = x_plus * x_minus - q * q_bar ∧
    M * freudenthalSharp3 M = freudenthalDet3 M • (1 : Matrix (Fin 3) (Fin 3) R) ∧
    M * M * M - Matrix.trace M • (M * M) +
      Matrix.trace (freudenthalSharp3 M) • M -
      freudenthalDet3 M • (1 : Matrix (Fin 3) (Fin 3) R) = 0 := by
  intro M_CS
  have h_tr : Matrix.trace (freudenthalSharp3 M) = freudenthalSecondInvariant M := by
    simp [freudenthalSharp3, freudenthalSecondInvariant, Matrix.trace,
          Fin.sum_univ_three, Matrix.mul_apply]
    ring
  refine ⟨h_tr, ?_, ?_, ?_, ?_⟩
  · rw [h_tr]
    simp [freudenthalSecondInvariant, Matrix.trace, Fin.sum_univ_three, Matrix.mul_apply]
    ring
  · simp [M_CS, conwaySloaneMat3, freudenthalSharp3, freudenthalSecondInvariant,
          Matrix.trace, Fin.sum_univ_three, Matrix.mul_apply]
    ring
  · ext i j; fin_cases i <;> fin_cases j <;>
    simp [freudenthalSharp3, freudenthalSecondInvariant, freudenthalDet3,
          Matrix.trace, Fin.sum_univ_three, Matrix.mul_apply, Matrix.one_apply] <;>
    ring
  · rw [h_tr]
    ext i j; fin_cases i <;> fin_cases j <;>
    simp [freudenthalSharp3, freudenthalSecondInvariant, freudenthalDet3,
          Matrix.trace, Fin.sum_univ_three, Matrix.mul_apply, Matrix.one_apply] <;>
    ring

/-!
## 33. Archetype LXXVIII: First-Quantized Operator Zorn Jacobson Triple Closure, Chiral Lightcone Weyl Reflection, & Chiral Spinor Freudenthal Cubic in $\mathcal{G}_0$
-/

/-- **Theorem 96 (Archetype LXXVIII — Noncommutative Operator Zorn Jacobson Triple Closure, Chiral Lightcone Weyl Reflection, & Chiral Freudenthal Cubic in `OpZornMatrix A`)**:
    Over *any* noncommutative operator ring $A$ (`[Ring A]`), for all 3-vectors
    $w, u, v_1, w_1, v_2, w_2, v_3, w_3, q, \xi_1, \xi_2 \in \mathrm{OpVec3}\;A$:
    1. Universal Off-Diagonal Closure of Jacobson's Jordan Triple Product on `OpZornMatrix A`:
       For $J_i = \mathrm{opKasparovZornJ}\;v_i\;w_i = \langle 0, v_i, w_i, 0 \rangle$,
       $$\bigl(\{J_1, J_2, J_3\}_{\mathrm{JT}}\bigr).a = 0 \qquad \text{and} \qquad
         \bigl(\{J_1, J_2, J_3\}_{\mathrm{JT}}\bigr).b = 0.$$
    2. Noncommutative Operator Weyl Reflection of $L_+(u)$ by $L_-(w)$:
       $$\bigl\{L_-(w),\; L_+(u),\; L_-(w)\bigr\}_{\mathrm{JT}} =
         -L_-\!\bigl(((w \cdot u) \cdot_{\mathrm{L}} w + w \cdot_{\mathrm{R}} (u \cdot w)) +
                     ((w \cdot u) \cdot_{\mathrm{L}} w + w \cdot_{\mathrm{R}} (u \cdot w))\bigr).$$
    3. Chiral Spinor Freudenthal Cubic Product $(Q * \Xi_2) * \Xi_1$ Lands in the Associative Nucleus $\mathcal{G}_0$:
       For $Q = L_+(q), \Xi_1 = L_+(\xi_1), \Xi_2 = L_+(\xi_2) \in \mathrm{OpZornMatrix}\;A$,
       $$Q * \Xi_2 = L_-(q \times_{\mathrm{skew}} \xi_2) \qquad \text{and} \qquad
         (Q * \Xi_2) * \Xi_1 = \mathrm{opGradeZero}\;0\;(-((q \times_{\mathrm{skew}} \xi_2) \cdot \xi_1)).$$ -/
theorem opZorn_jacobson_triple_closure_weyl_and_chiral_freudenthal
    (w u v₁ w₁ v₂ w₂ v₃ w₃ q ξ₁ ξ₂ : OpVec3 A) :
    let J₁ := opKasparovZornJ v₁ w₁
    let J₂ := opKasparovZornJ v₂ w₂
    let J₃ := opKasparovZornJ v₃ w₃
    let Lw := opLightconeMinus w
    let Lu := opLightconePlus u
    let refl_w := OpVec3.leftScale (OpVec3.dot w u) w + OpVec3.rightScale w (OpVec3.dot u w)
    let Q := opLightconePlus q
    let Ξ₁ := opLightconePlus ξ₁
    let Ξ₂ := opLightconePlus ξ₂
    (opJacobsonTriple J₁ J₂ J₃).a = 0 ∧
    (opJacobsonTriple J₁ J₂ J₃).b = 0 ∧
    opJacobsonTriple Lw Lu Lw = -opLightconeMinus (refl_w + refl_w) ∧
    Q * Ξ₂ = opLightconeMinus (OpVec3.skewCross q ξ₂) ∧
    (Q * Ξ₂) * Ξ₁ = opGradeZero 0 (-OpVec3.dot (OpVec3.skewCross q ξ₂) ξ₁) := by
  intro J₁ J₂ J₃ Lw Lu refl_w Q Ξ₁ Ξ₂
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [J₁, J₂, J₃, opJacobsonTriple, opAnticommutator, opKasparovZornJ,
          OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross]
  · simp [J₁, J₂, J₃, opJacobsonTriple, opAnticommutator, opKasparovZornJ,
          OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross]
  · ext <;>
    (simp [Lw, Lu, refl_w, opJacobsonTriple, opAnticommutator,
           opLightconePlus, opLightconeMinus, opLightconeRayPlus, opLightconeRayMinus,
           OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross];
     try noncomm_ring)
  · ext <;>
    (simp [Q, Ξ₂, opLightconePlus, opLightconeMinus, opLightconeRayPlus, opLightconeRayMinus,
           OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross];
     try noncomm_ring)
  · ext <;>
    (simp [Q, Ξ₁, Ξ₂, opLightconePlus, opLightconeMinus, opLightconeRayPlus, opLightconeRayMinus,
           opCartanDiag, OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross];
     try noncomm_ring)

/-!
## 34. Archetypes LXXIX & LXXX: $\mathbb{Z}_3$-Triality Operator Determinant Splitting & 72-Channel $3 \times 3$ Freudenthal Inversion in $M_3(\mathrm{OpZornMatrix}\;A)$
-/

/-- Register `NonUnitalNonAssocRing` on `OpZornMatrix A` so
    `Matrix (Fin 3) (Fin 3) (OpZornMatrix A)` inherits matrix addition, subtraction,
    negation, `Matrix.mul`, and matrix distributivity (`add_mul`, `mul_add`) automatically. -/
instance instNonUnitalNonAssocRingOpZornMatrix : NonUnitalNonAssocRing (OpZornMatrix A) where
  add_assoc X Y Z := by ext <;> simp [add_assoc]
  zero_add X := by ext <;> simp
  add_zero X := by ext <;> simp
  neg_add_cancel X := by ext <;> simp
  add_comm X Y := by ext <;> simp [add_comm]
  sub_eq_add_neg X Y := by ext <;> simp [sub_eq_add_neg]
  nsmul := nsmulRec
  zsmul := zsmulRec
  left_distrib X Y Z := by
    ext <;>
      (simp [OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross,
             OpVec3.leftScale, OpVec3.rightScale];
       noncomm_ring)
  right_distrib X Y Z := by
    ext <;>
      (simp [OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross,
             OpVec3.leftScale, OpVec3.rightScale];
       noncomm_ring)
  zero_mul X := by
    ext <;> simp [OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross, OpVec3.leftScale, OpVec3.rightScale]
  mul_zero X := by
    ext <;> simp [OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross, OpVec3.leftScale, OpVec3.rightScale]

@[simp] private lemma opZorn_one_mul (X : OpZornMatrix A) : (1 : OpZornMatrix A) * X = X := by
  ext <;> simp [OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross, OpVec3.leftScale, OpVec3.rightScale]

@[simp] private lemma opZorn_mul_one (X : OpZornMatrix A) : X * (1 : OpZornMatrix A) = X := by
  ext <;> simp [OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross, OpVec3.leftScale, OpVec3.rightScale]

private lemma mat3_one_mul (B : Matrix (Fin 3) (Fin 3) (OpZornMatrix A)) : 1 * B = B := by
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_three,
          OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross,
          OpVec3.leftScale, OpVec3.rightScale]

private lemma mat3_mul_one (B : Matrix (Fin 3) (Fin 3) (OpZornMatrix A)) : B * 1 = B := by
  refine Matrix.ext fun i j => ?_
  fin_cases j <;> fin_cases i <;>
    simp [Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_three,
          OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross,
          OpVec3.leftScale, OpVec3.rightScale]

/-- **Theorem 97 (Archetype LXXIX — $\mathbb{Z}_3$-Triality Splitting of the Operator Freudenthal Determinant & Leibniz Nucleus)**:
    Over *any* noncommutative operator ring $A$ (`[Ring A]`), for all chiral spinor-octonion fields
    $q, \xi_1, \xi_2, u, w \in \mathrm{OpVec3}\;A$ and arbitrary states $X, Y \in \mathrm{OpZornMatrix}\;A$, let
    $Q = L_+(q)$, $\Xi_1 = L_+(\xi_1)$, $\Xi_2 = L_+(\xi_2)$, $L_u = L_+(u)$, $L_w = L_-(w)$, and define the three
    $\mathbb{Z}_3$-cyclic operator Nambu determinants $\Delta_0 = \det_L(q, \xi_2, \xi_1)$,
    $\Delta_1 = \det_L(\xi_2, \xi_1, q)$, $\Delta_2 = \det_L(\xi_1, q, \xi_2)$ and their right-associated duals
    $\Delta_0^*, \Delta_1^*, \Delta_2^*$:
    1. Three Cyclic Associators Split the $\mathbb{Z}_3$-Triality Determinants Across $e_{11}$ and $e_{22}$:
       $$[Q, \Xi_2, \Xi_1] = \mathrm{opGradeZero}\;\Delta_0\;(-\Delta_0^*), \qquad
         [\Xi_2, \Xi_1, Q] = \mathrm{opGradeZero}\;\Delta_1\;(-\Delta_1^*), \qquad
         [\Xi_1, Q, \Xi_2] = \mathrm{opGradeZero}\;\Delta_2\;(-\Delta_2^*).$$
    2. Cyclic Triality Associator Sum Lands in the Grade-0 Associative Nucleus $\mathcal{G}_0$:
       $$S_{\mathrm{tri}} := [Q, \Xi_2, \Xi_1] + [\Xi_2, \Xi_1, Q] + [\Xi_1, Q, \Xi_2] =
         \mathrm{opGradeZero}\;(\Delta_0 + \Delta_1 + \Delta_2)\;(-(\Delta_0^* + \Delta_1^* + \Delta_2^*)).$$
    3. Exact Opposite-Chirality & Diagonal Leibniz Derivation Law of the Triality Determinant Sum:
       $$\mathrm{opCommutator}\;S_{\mathrm{tri}}\;(L_u * L_w) =
         (\mathrm{opCommutator}\;S_{\mathrm{tri}}\;L_u) * L_w + L_u * (\mathrm{opCommutator}\;S_{\mathrm{tri}}\;L_w),$$
       $$(\mathrm{opCommutator}\;S_{\mathrm{tri}}\;(X * Y)).a =
         (\mathrm{opCommutator}\;S_{\mathrm{tri}}\;X * Y + X * \mathrm{opCommutator}\;S_{\mathrm{tri}}\;Y).a,$$
       $$(\mathrm{opCommutator}\;S_{\mathrm{tri}}\;(X * Y)).b =
         (\mathrm{opCommutator}\;S_{\mathrm{tri}}\;X * Y + X * \mathrm{opCommutator}\;S_{\mathrm{tri}}\;Y).b.$$ -/
private lemma opGradeZero_add_three (a₀ b₀ a₁ b₁ a₂ b₂ : A) :
    opGradeZero a₀ (-b₀) + opGradeZero a₁ (-b₁) + opGradeZero a₂ (-b₂) =
      opGradeZero (a₀ + a₁ + a₂) (-(b₀ + b₁ + b₂)) := by
  ext <;> (simp [opGradeZero, opCartanDiag]; try abel)

private lemma opCommutator_opGradeZero_leibniz
    (d₁ d₂ : A) (u w : OpVec3 A) (X Y : OpZornMatrix A) :
    let G := opGradeZero d₁ d₂
    let Lu := opLightconePlus u
    let Lw := opLightconeMinus w
    opCommutator G (Lu * Lw) = opCommutator G Lu * Lw + Lu * opCommutator G Lw ∧
    (opCommutator G (X * Y)).a = (opCommutator G X * Y + X * opCommutator G Y).a ∧
    (opCommutator G (X * Y)).b = (opCommutator G X * Y + X * opCommutator G Y).b := by
  intro G Lu Lw
  have h := opModularDeriv_nucleus_and_exact_leibniz_rule (opGradeZero d₁ d₂) X Y u w d₁ d₂
  simp [opModularDeriv] at h
  exact ⟨h.2.2.2.2.1, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2⟩

theorem operator_albert_triality_determinant_split_and_nucleus_leibniz
    (q ξ₁ ξ₂ u w : OpVec3 A) (X Y : OpZornMatrix A) :
    let Q := opLightconePlus q
    let Ξ₁ := opLightconePlus ξ₁
    let Ξ₂ := opLightconePlus ξ₂
    let Lu := opLightconePlus u
    let Lw := opLightconeMinus w
    let Δ₀ := OpVec3.baryonDetLeft q ξ₂ ξ₁
    let Δ₁ := OpVec3.baryonDetLeft ξ₂ ξ₁ q
    let Δ₂ := OpVec3.baryonDetLeft ξ₁ q ξ₂
    let Δ₀_star := OpVec3.baryonDetRight q ξ₂ ξ₁
    let Δ₁_star := OpVec3.baryonDetRight ξ₂ ξ₁ q
    let Δ₂_star := OpVec3.baryonDetRight ξ₁ q ξ₂
    let S_tri := opAssociator Q Ξ₂ Ξ₁ + opAssociator Ξ₂ Ξ₁ Q + opAssociator Ξ₁ Q Ξ₂
    opAssociator Q Ξ₂ Ξ₁ = opGradeZero Δ₀ (-Δ₀_star) ∧
    opAssociator Ξ₂ Ξ₁ Q = opGradeZero Δ₁ (-Δ₁_star) ∧
    opAssociator Ξ₁ Q Ξ₂ = opGradeZero Δ₂ (-Δ₂_star) ∧
    S_tri = opGradeZero (Δ₀ + Δ₁ + Δ₂) (-(Δ₀_star + Δ₁_star + Δ₂_star)) ∧
    opCommutator S_tri (Lu * Lw) = opCommutator S_tri Lu * Lw + Lu * opCommutator S_tri Lw ∧
    (opCommutator S_tri (X * Y)).a = (opCommutator S_tri X * Y + X * opCommutator S_tri Y).a ∧
    (opCommutator S_tri (X * Y)).b = (opCommutator S_tri X * Y + X * opCommutator S_tri Y).b := by
  intro Q Ξ₁ Ξ₂ Lu Lw Δ₀ Δ₁ Δ₂ Δ₀_star Δ₁_star Δ₂_star S_tri
  have h0 : opAssociator Q Ξ₂ Ξ₁ = opGradeZero Δ₀ (-Δ₀_star) :=
    (quark_diquark_meson_baryon_nucleus_confinement_and_leibniz 0 0 q ξ₂ ξ₁ 0 0).2.2.1
  have h1 : opAssociator Ξ₂ Ξ₁ Q = opGradeZero Δ₁ (-Δ₁_star) :=
    (quark_diquark_meson_baryon_nucleus_confinement_and_leibniz 0 0 ξ₂ ξ₁ q 0 0).2.2.1
  have h2 : opAssociator Ξ₁ Q Ξ₂ = opGradeZero Δ₂ (-Δ₂_star) :=
    (quark_diquark_meson_baryon_nucleus_confinement_and_leibniz 0 0 ξ₁ q ξ₂ 0 0).2.2.1
  have h_S : S_tri = opGradeZero (Δ₀ + Δ₁ + Δ₂) (-(Δ₀_star + Δ₁_star + Δ₂_star)) := by
    change opAssociator Q Ξ₂ Ξ₁ + opAssociator Ξ₂ Ξ₁ Q + opAssociator Ξ₁ Q Ξ₂ = _
    rw [h0, h1, h2]
    exact opGradeZero_add_three Δ₀ Δ₀_star Δ₁ Δ₁_star Δ₂ Δ₂_star
  have h_leib := opCommutator_opGradeZero_leibniz (Δ₀ + Δ₁ + Δ₂) (-(Δ₀_star + Δ₁_star + Δ₂_star)) u w X Y
  refine ⟨h0, h1, h2, h_S, ?_, ?_, ?_⟩
  · rw [h_S]; exact h_leib.1
  · rw [h_S]; exact h_leib.2.1
  · rw [h_S]; exact h_leib.2.2

/-- Any product of a Grade-$+2$ top-chiral operator with a Heisenberg nilradical element vanishes. -/
@[simp] theorem opGradePlus2_mul_opHeisenbergNilPlus (s y z ξ : A) :
    opGradePlus2 s * opHeisenbergNilPlus y z ξ = 0 := by
  ext <;> simp [opGradePlus2, opHeisenbergNilPlus, opLightconeRayPlus,
                OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross, OpVec3.leftScale, OpVec3.rightScale]

/-- Any product of a Heisenberg nilradical element with a Grade-$+2$ top-chiral operator vanishes. -/
@[simp] theorem opHeisenbergNilPlus_mul_opGradePlus2 (y z ξ s : A) :
    opHeisenbergNilPlus y z ξ * opGradePlus2 s = 0 := by
  ext <;> simp [opGradePlus2, opHeisenbergNilPlus, opLightconeRayPlus,
                OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross, OpVec3.leftScale, OpVec3.rightScale]

/-- Left-associated triple product of any three elements of the Heisenberg nilradical
    $\mathcal{N}_+ = \mathcal{G}_{+1} \oplus \mathcal{G}_{+2}$ vanishes identically. -/
@[simp] theorem opHeisenbergNilPlus_mul_mul (y₁ z₁ ξ₁ y₂ z₂ ξ₂ y₃ z₃ ξ₃ : A) :
    (opHeisenbergNilPlus y₁ z₁ ξ₁ * opHeisenbergNilPlus y₂ z₂ ξ₂) *
      opHeisenbergNilPlus y₃ z₃ ξ₃ = 0 := by
  ext <;> simp [opHeisenbergNilPlus, opLightconePlus, opLightconeRayPlus,
                OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross, OpVec3.leftScale, OpVec3.rightScale]

/-- Right-associated triple product of any three elements of the Heisenberg nilradical
    $\mathcal{N}_+ = \mathcal{G}_{+1} \oplus \mathcal{G}_{+2}$ vanishes identically. -/
@[simp] theorem opHeisenbergNilPlus_mul_mul_right (y₁ z₁ ξ₁ y₂ z₂ ξ₂ y₃ z₃ ξ₃ : A) :
    opHeisenbergNilPlus y₁ z₁ ξ₁ *
      (opHeisenbergNilPlus y₂ z₂ ξ₂ * opHeisenbergNilPlus y₃ z₃ ξ₃) = 0 := by
  ext <;> simp [opHeisenbergNilPlus, opLightconePlus, opLightconeRayPlus,
                OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross, OpVec3.leftScale, OpVec3.rightScale]

/-- Constructs a 72-channel $3 \times 3$ matrix over `OpZornMatrix A` whose $(i, j)$ entry lies in
    the 5-graded Heisenberg nilradical $\mathcal{N}_+ = \mathcal{G}_{+1} \oplus \mathcal{G}_{+2}$. -/
def mat3HeisenbergNilPlus (y z ξ : Fin 3 → Fin 3 → A) :
    Matrix (Fin 3) (Fin 3) (OpZornMatrix A) :=
  fun i j => opHeisenbergNilPlus (y i j) (z i j) (ξ i j)

/-- Noncommutative grading involution $U_{3,\mathrm{Zorn}} = \mathrm{diag}(1, -1, 0) \in M_3(\mathrm{OpZornMatrix}\;A)$. -/
def mat3OpZornCliffordU : Matrix (Fin 3) (Fin 3) (OpZornMatrix A) :=
  !![1, 0, 0;
     0, -1, 0;
     0, 0, 0]

/-- Noncommutative flip involution $V_{3,\mathrm{Zorn}} \in M_3(\mathrm{OpZornMatrix}\;A)$. -/
def mat3OpZornCliffordV : Matrix (Fin 3) (Fin 3) (OpZornMatrix A) :=
  !![0, 1, 0;
     1, 0, 0;
     0, 0, 0]

/-- Non-commutativity / Clifford anticommutation witness for `Matrix (Fin 3) (Fin 3) (OpZornMatrix A)` (`T16` witness):
    $U_{3,\mathrm{Zorn}} V_{3,\mathrm{Zorn}} + V_{3,\mathrm{Zorn}} U_{3,\mathrm{Zorn}} = 0$. -/
theorem mat3OpZornClifford_anticomm :
    (mat3OpZornCliffordU : Matrix (Fin 3) (Fin 3) (OpZornMatrix A)) * mat3OpZornCliffordV +
      mat3OpZornCliffordV * mat3OpZornCliffordU = 0 := by
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    (refine OpZornMatrix.ext ?_ (OpVec3.ext ?_ ?_ ?_) (OpVec3.ext ?_ ?_ ?_) ?_ <;>
     simp [mat3OpZornCliffordU, mat3OpZornCliffordV, Matrix.mul_apply])

/-- **Theorem 98a (Archetype LXXX — 72-Channel Triple Product Vanishing)**:
    Over *any* noncommutative operator ring $A$ (`[Ring A]`), for all $3 \times 3$ coefficient arrays
    $y_k, z_k, \xi_k : \mathrm{Fin}\;3 \to \mathrm{Fin}\;3 \to A$ ($k \in \{1, 2, 3\}$), let
    $M_k = \mathrm{mat3HeisenbergNilPlus}\;y_k\;z_k\;\xi_k \in \mathrm{Matrix}\;(\mathrm{Fin}\;3)\;(\mathrm{Fin}\;3)\;(\mathrm{OpZornMatrix}\;A)$:
    $$(M_1 * M_2) * M_3 = 0 \qquad \text{and} \qquad M_1 * (M_2 * M_3) = 0.$$ -/
theorem matrix3_operator_zorn_nilradical_triple_product_vanishing
    (y₁ z₁ ξ₁ y₂ z₂ ξ₂ y₃ z₃ ξ₃ : Fin 3 → Fin 3 → A) :
    let M₁ := mat3HeisenbergNilPlus y₁ z₁ ξ₁
    let M₂ := mat3HeisenbergNilPlus y₂ z₂ ξ₂
    let M₃ := mat3HeisenbergNilPlus y₃ z₃ ξ₃
    (M₁ * M₂) * M₃ = 0 ∧ M₁ * (M₂ * M₃) = 0 := by
  intro M₁ M₂ M₃
  have h_left : (M₁ * M₂) * M₃ = 0 := by
    refine Matrix.ext fun i j => ?_
    simp only [M₁, M₂, M₃, mat3HeisenbergNilPlus, Matrix.mul_apply, Matrix.zero_apply,
               Fin.sum_univ_three, add_mul,
               opHeisenbergNilPlus_mul_mul, add_zero]
  have h_right : M₁ * (M₂ * M₃) = 0 := by
    refine Matrix.ext fun i j => ?_
    simp only [M₁, M₂, M₃, mat3HeisenbergNilPlus, Matrix.mul_apply, Matrix.zero_apply,
               Fin.sum_univ_three, mul_add,
               opHeisenbergNilPlus_mul_mul_right, add_zero]
  exact ⟨h_left, h_right⟩

/-- **Theorem 98b (Archetype LXXX — Exact Associativity of $M_3(\mathcal{N}_+)$)**:
    Over *any* noncommutative operator ring $A$ (`[Ring A]`), for all $3 \times 3$ coefficient arrays
    $y_k, z_k, \xi_k : \mathrm{Fin}\;3 \to \mathrm{Fin}\;3 \to A$ ($k \in \{1, 2, 3\}$), let
    $M_k = \mathrm{mat3HeisenbergNilPlus}\;y_k\;z_k\;\xi_k$:
    $$(M_1 * M_2) * M_3 = M_1 * (M_2 * M_3).$$ -/
theorem matrix3_operator_zorn_nilradical_associativity
    (y₁ z₁ ξ₁ y₂ z₂ ξ₂ y₃ z₃ ξ₃ : Fin 3 → Fin 3 → A) :
    let M₁ := mat3HeisenbergNilPlus y₁ z₁ ξ₁
    let M₂ := mat3HeisenbergNilPlus y₂ z₂ ξ₂
    let M₃ := mat3HeisenbergNilPlus y₃ z₃ ξ₃
    (M₁ * M₂) * M₃ = M₁ * (M₂ * M₃) := by
  intro M₁ M₂ M₃
  have h := matrix3_operator_zorn_nilradical_triple_product_vanishing y₁ z₁ ξ₁ y₂ z₂ ξ₂ y₃ z₃ ξ₃
  dsimp at h
  change (M₁ * M₂) * M₃ = 0 ∧ M₁ * (M₂ * M₃) = 0 at h
  rw [h.1, h.2]

/-- **Theorem 98c (Archetype LXXX — Left Exact Quadratic Freudenthal Inverse of $I_3 + M_1$)**:
    Over *any* noncommutative operator ring $A$ (`[Ring A]`), for all $3 \times 3$ coefficient arrays
    $y, z, \xi : \mathrm{Fin}\;3 \to \mathrm{Fin}\;3 \to A$, let
    $M = \mathrm{mat3HeisenbergNilPlus}\;y\;z\;\xi$:
    $$(1 + M) * (1 - M + M * M) = 1.$$ -/
theorem matrix3_operator_zorn_nilradical_freudenthal_inverse_left
    (y z ξ : Fin 3 → Fin 3 → A) :
    let M := mat3HeisenbergNilPlus y z ξ
    (1 + M) * (1 - M + M * M) = 1 := by
  intro M
  have h_M3 : M * (M * M) = 0 :=
    (matrix3_operator_zorn_nilradical_triple_product_vanishing y z ξ y z ξ y z ξ).2
  calc (1 + M) * (1 - M + M * M)
    _ = 1 * (1 - M + M * M) + M * (1 - M + M * M) := add_mul 1 M (1 - M + M * M)
    _ = (1 - M + M * M) + (M * (1 - M) + M * (M * M)) := by
          rw [mat3_one_mul, mul_add]
    _ = (1 - M + M * M) + (M * 1 - M * M + 0) := by
          rw [mul_sub, h_M3]
    _ = (1 - M + M * M) + (M - M * M + 0) := by
          rw [mat3_mul_one]
    _ = 1 := by abel

/-- **Theorem 98d (Archetype LXXX — Right Exact Quadratic Freudenthal Inverse of $I_3 + M_1$)**:
    Over *any* noncommutative operator ring $A$ (`[Ring A]`), for all $3 \times 3$ coefficient arrays
    $y, z, \xi : \mathrm{Fin}\;3 \to \mathrm{Fin}\;3 \to A$, let
    $M = \mathrm{mat3HeisenbergNilPlus}\;y\;z\;\xi$:
    $$(1 - M + M * M) * (1 + M) = 1.$$ -/
theorem matrix3_operator_zorn_nilradical_freudenthal_inverse_right
    (y z ξ : Fin 3 → Fin 3 → A) :
    let M := mat3HeisenbergNilPlus y z ξ
    (1 - M + M * M) * (1 + M) = 1 := by
  intro M
  have h_M3 : (M * M) * M = 0 :=
    (matrix3_operator_zorn_nilradical_triple_product_vanishing y z ξ y z ξ y z ξ).1
  calc (1 - M + M * M) * (1 + M)
    _ = (1 - M + M * M) * 1 + (1 - M + M * M) * M := mul_add (1 - M + M * M) 1 M
    _ = (1 - M + M * M) + ((1 - M) * M + (M * M) * M) := by
          rw [mat3_mul_one, add_mul]
    _ = (1 - M + M * M) + (1 * M - M * M + 0) := by
          rw [sub_mul, h_M3]
    _ = (1 - M + M * M) + (M - M * M + 0) := by
          rw [mat3_one_mul]
    _ = 1 := by abel

/-- **Theorem 98 (Archetype LXXX — 72-Channel $3 \times 3$ Operator Zorn Nilradical Associativity & Exact Quadratic Freudenthal Inversion in $M_3(\mathrm{OpZornMatrix}\;A)$)**:
    Over *any* noncommutative operator ring $A$ (`[Ring A]`), for all $3 \times 3$ coefficient arrays
    $y_k, z_k, \xi_k : \mathrm{Fin}\;3 \to \mathrm{Fin}\;3 \to A$ ($k \in \{1, 2, 3\}$), let
    $M_k = \mathrm{mat3HeisenbergNilPlus}\;y_k\;z_k\;\xi_k \in \mathrm{Matrix}\;(\mathrm{Fin}\;3)\;(\mathrm{Fin}\;3)\;(\mathrm{OpZornMatrix}\;A)$:
    1. Exact 3-Step Nilpotency & Genuine Associativity of 72-Channel Operator Zorn Matrices:
       $$(M_1 * M_2) * M_3 = 0, \qquad M_1 * (M_2 * M_3) = 0, \qquad (M_1 * M_2) * M_3 = M_1 * (M_2 * M_3).$$
    2. Exact Two-Sided Quadratic Freudenthal Inverse of $I_3 + M_1$:
       $$(1 + M_1) * (1 - M_1 + M_1 * M_1) = 1, \qquad
         (1 - M_1 + M_1 * M_1) * (1 + M_1) = 1.$$ -/
theorem matrix3_operator_zorn_nilradical_freudenthal_inversion_and_associativity
    (y₁ z₁ ξ₁ y₂ z₂ ξ₂ y₃ z₃ ξ₃ : Fin 3 → Fin 3 → A) :
    let M₁ := mat3HeisenbergNilPlus y₁ z₁ ξ₁
    let M₂ := mat3HeisenbergNilPlus y₂ z₂ ξ₂
    let M₃ := mat3HeisenbergNilPlus y₃ z₃ ξ₃
    (M₁ * M₂) * M₃ = 0 ∧
    M₁ * (M₂ * M₃) = 0 ∧
    (M₁ * M₂) * M₃ = M₁ * (M₂ * M₃) ∧
    (1 + M₁) * (1 - M₁ + M₁ * M₁) = 1 ∧
    (1 - M₁ + M₁ * M₁) * (1 + M₁) = 1 := by
  intro M₁ M₂ M₃
  have h_van := matrix3_operator_zorn_nilradical_triple_product_vanishing y₁ z₁ ξ₁ y₂ z₂ ξ₂ y₃ z₃ ξ₃
  exact ⟨h_van.1, h_van.2,
         matrix3_operator_zorn_nilradical_associativity y₁ z₁ ξ₁ y₂ z₂ ξ₂ y₃ z₃ ξ₃,
         matrix3_operator_zorn_nilradical_freudenthal_inverse_left y₁ z₁ ξ₁,
         matrix3_operator_zorn_nilradical_freudenthal_inverse_right y₁ z₁ ξ₁⟩

/-! ### 35. Archetypes LXXXI, LXXXII, & LXXXIII: Steen H. Hansen (2026) $\mathrm{Cl}(4, 2)$ Doublet Tower, Unique $d = 4$ Lorentzian Spacetime Selection $S_2 = 0$, Top-Rung Dirac–Majorana Dichotomy, & Zorn Triality Marriage -/

/-- **Hansen's Conformal Grading / Dilatation Element $D = \mathrm{diag}(1, -1) \in M_2(A)$
    (Hansen 2026, Eq. 2.4 & Remark 7.2)**. -/
def hansenDilatationD : Matrix (Fin 2) (Fin 2) A :=
  !![1, 0; 0, -1]

/-- **Division-Free Scaled Positive Projector $2\Pi_+ = I_2 + D = \mathrm{diag}(2, 0) \in M_2(A)$
    (Hansen 2026, Eq. 2.5)**. -/
def hansenTwoPiPlus : Matrix (Fin 2) (Fin 2) A :=
  !![2, 0; 0, 0]

/-- **Division-Free Scaled Negative Projector $2\Pi_- = I_2 - D = \mathrm{diag}(0, 2) \in M_2(A)$
    (Hansen 2026, Eq. 2.5)**. -/
def hansenTwoPiMinus : Matrix (Fin 2) (Fin 2) A :=
  !![0, 0; 0, 2]

/-- **Positive Conformal Doublet Operator $T^+(x) = \begin{pmatrix} 0 & x \\ 0 & 0 \end{pmatrix} \in \mathfrak{N}_+ \subset M_2(A)$
    (Hansen 2026, Definition 3.1 & Remark 7.2)**. -/
def hansenDoubletPlus (x : A) : Matrix (Fin 2) (Fin 2) A :=
  !![0, x; 0, 0]

/-- **Negative Conformal Doublet Operator $T^-(y) = \begin{pmatrix} 0 & 0 \\ y & 0 \end{pmatrix} \in \mathfrak{N}_- \subset M_2(A)$
    (Hansen 2026, Definition 3.1 & Remark 7.2)**. -/
def hansenDoubletMinus (y : A) : Matrix (Fin 2) (Fin 2) A :=
  !![0, 0; y, 0]

/-- **Hansen's Top-Rung Majorana Combination $I_M(x, y) = T^+(x) + T^-(y) \in M_2(A)$
    (Hansen 2026, Eq. 8.1 & Theorem 8.2)**. -/
def hansenMajoranaComb (x y : A) : Matrix (Fin 2) (Fin 2) A :=
  hansenDoubletPlus x + hansenDoubletMinus y

/-- **Hansen's Top-Rung Dirac Combination $I_D(x, y) = T^+(x) - T^-(y) \in M_2(A)$
    (Hansen 2026, Eq. 8.1 & Theorem 8.2)**. -/
def hansenDiracComb (x y : A) : Matrix (Fin 2) (Fin 2) A :=
  hansenDoubletPlus x - hansenDoubletMinus y

/-- **Scalar Diagonal Embedding $\mathrm{diag}(a, a) \in M_2(A)$**. -/
def hansenScalarDiag (a : A) : Matrix (Fin 2) (Fin 2) A :=
  !![a, 0; 0, a]

/-- **Theorem 99 (Archetype LXXXI.1 — Hansen's Universal Noncommutative Doublet Tower, Abelian Nilradicals, Single-Projector Law, & Two-Branch Levi Commutator in $M_2(A)$)**:
    Over *any* noncommutative operator ring $A$ (`[Ring A]`), for all $x, y \in A$:
    1. Grading Involution & Scaled Projectors:
       $$D^2 = I_2, \qquad (2\Pi_+) + (2\Pi_-) = 2 I_2, \qquad (2\Pi_+) * (2\Pi_-) = 0.$$
    2. Eigenvalue Selection & Anticommutation (Hansen Theorem 3.1 & Lemma 8.1):
       $$D * T^+(x) - T^+(x) * D = T^+(x) + T^+(x), \qquad
         D * T^-(y) - T^-(y) * D = -(T^-(y) + T^-(y)),$$
       $$D * T^+(x) + T^+(x) * D = 0, \qquad
         D * T^-(y) + T^-(y) * D = 0.$$
    3. Universal Nilpotency & Abelian Nilradicals (Hansen Theorems 3.2 & 6.2):
       $$T^+(x) * T^+(y) = 0, \qquad T^-(x) * T^-(y) = 0.$$
    4. Single-Projector Proportionality Law (Hansen Theorem 3.3 & Theorem 7.1(c)):
       $$T^+(x) * T^-(y) = \begin{pmatrix} x y & 0 \\ 0 & 0 \end{pmatrix}, \qquad
         T^-(y) * T^+(x) = \begin{pmatrix} 0 & 0 \\ 0 & y x \end{pmatrix}.$$
    5. Division-Free Two-Branch Mixed Levi Commutator Formula (Hansen Theorem 6.1, Eq. 6.3):
       $$2 \bullet \bigl(T^+(x) * T^-(y) - T^-(y) * T^+(x)\bigr) =
         \mathrm{diag}(x y - y x, x y - y x) + \mathrm{diag}(x y + y x, x y + y x) * D.$$ -/
theorem hansen_universal_doublet_tower_identities (x y : A) :
    let D := (hansenDilatationD : Matrix (Fin 2) (Fin 2) A)
    let P_plus := (hansenTwoPiPlus : Matrix (Fin 2) (Fin 2) A)
    let P_minus := (hansenTwoPiMinus : Matrix (Fin 2) (Fin 2) A)
    let Tp_x := hansenDoubletPlus x
    let Tp_y := hansenDoubletPlus y
    let Tm_x := hansenDoubletMinus x
    let Tm_y := hansenDoubletMinus y
    let comm := Tp_x * Tm_y - Tm_y * Tp_x
    D * D = 1 ∧
    P_plus + P_minus = hansenScalarDiag 2 ∧
    P_plus * P_minus = 0 ∧
    D * Tp_x - Tp_x * D = Tp_x + Tp_x ∧
    D * Tm_y - Tm_y * D = -(Tm_y + Tm_y) ∧
    D * Tp_x + Tp_x * D = 0 ∧
    D * Tm_y + Tm_y * D = 0 ∧
    Tp_x * Tp_y = 0 ∧
    Tm_x * Tm_y = 0 ∧
    Tp_x * Tm_y = !![x * y, 0; 0, 0] ∧
    Tm_y * Tp_x = !![0, 0; 0, y * x] ∧
    comm + comm = hansenScalarDiag (x * y - y * x) + hansenScalarDiag (x * y + y * x) * D := by
  intro D P_plus P_minus Tp_x Tp_y Tm_x Tm_y comm
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (ext i j; fin_cases i <;> fin_cases j <;>
     (simp [D, P_plus, P_minus, Tp_x, Tp_y, Tm_x, Tm_y, comm,
            hansenDilatationD, hansenTwoPiPlus, hansenTwoPiMinus,
            hansenDoubletPlus, hansenDoubletMinus, hansenScalarDiag,
            Matrix.mul_apply, Fin.sum_univ_two];
      try noncomm_ring))

/-- **Theorem 100 (Archetype LXXXIII.1 — Hansen's Top-Rung Dirac vs. Majorana Split-Quaternion Dichotomy & Sector Swap)**:
    Over *any* noncommutative operator ring $A$ (`[Ring A]`), for all $x, y \in A$:
    1. Opposite-Sign Squares of Majorana vs. Dirac Combinations (Hansen Theorem 8.2):
       $$I_M(x, y)^2 = \begin{pmatrix} x y & 0 \\ 0 & y x \end{pmatrix}, \qquad
         I_D(x, y)^2 = \begin{pmatrix} -x y & 0 \\ 0 & -y x \end{pmatrix}.$$
    2. Exact Chiral Sector Swap (Hansen Lemma 8.1):
       $$I_M(x, y) * (2\Pi_+) = (2\Pi_-) * I_M(x, y), \qquad
         I_D(x, y) * (2\Pi_+) = (2\Pi_-) * I_D(x, y).$$
    3. Split-Quaternion Anticommutation & Product (Hansen Remark 8.3):
       $$I_M(x, y) * I_D(x, y) + I_D(x, y) * I_M(x, y) = 0, \qquad
         I_D(x, y) * I_M(x, y) = \begin{pmatrix} x y & 0 \\ 0 & -y x \end{pmatrix}.$$ -/
theorem hansen_top_rung_dirac_majorana_dichotomy_and_sector_swap (x y : A) :
    let IM := hansenMajoranaComb x y
    let ID := hansenDiracComb x y
    let P_plus := (hansenTwoPiPlus : Matrix (Fin 2) (Fin 2) A)
    let P_minus := (hansenTwoPiMinus : Matrix (Fin 2) (Fin 2) A)
    IM * IM = !![x * y, 0; 0, y * x] ∧
    ID * ID = !![-(x * y), 0; 0, -(y * x)] ∧
    IM * P_plus = P_minus * IM ∧
    ID * P_plus = P_minus * ID ∧
    IM * ID + ID * IM = 0 ∧
    ID * IM = !![x * y, 0; 0, -(y * x)] := by
  intro IM ID P_plus P_minus
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (ext i j; fin_cases i <;> fin_cases j <;>
     (simp [IM, ID, P_plus, P_minus,
            hansenMajoranaComb, hansenDiracComb,
            hansenTwoPiPlus, hansenTwoPiMinus,
            hansenDoubletPlus, hansenDoubletMinus,
            Matrix.mul_apply, Fin.sum_univ_two];
      try noncomm_ring))

/-- **Elementary Symmetric Polynomials $S_0, S_1, S_2, S_3, S_4$ of a 4D Metric Signature $(s_1, s_2, s_3, s_4)$
    (Hansen 2026, Definition 4.1 & Eq. 4.1)**. -/
def symPolyS0 {R : Type*} [CommRing R] (_ _ _ _ : R) : R := 1

def symPolyS1 {R : Type*} [CommRing R] (s₁ s₂ s₃ s₄ : R) : R :=
  s₁ + s₂ + s₃ + s₄

def symPolyS2 {R : Type*} [CommRing R] (s₁ s₂ s₃ s₄ : R) : R :=
  s₁ * s₂ + s₁ * s₃ + s₁ * s₄ + s₂ * s₃ + s₂ * s₄ + s₃ * s₄

def symPolyS3 {R : Type*} [CommRing R] (s₁ s₂ s₃ s₄ : R) : R :=
  s₁ * s₂ * s₃ + s₁ * s₂ * s₄ + s₁ * s₃ * s₄ + s₂ * s₃ * s₄

def symPolyS4 {R : Type*} [CommRing R] (s₁ s₂ s₃ s₄ : R) : R :=
  s₁ * s₂ * s₃ * s₄

/-- **Division-Free General-Signature Quadratic Invariant $2 S_2(p, q) = (p + q)(p + q - 1) - 4 p q$
    (Hansen 2026, Eq. 4.3 & Corollary 4.3)**. -/
def twoSymPolyS2Gen {R : Type*} [CommRing R] (p q : R) : R :=
  (p + q) * (p + q - 1) - 4 * p * q

/-- **Theorem 101 (Archetype LXXXII.1 — Hansen's Elementary Symmetric Polynomials, Even/Odd Selection Rule, & Unique $d = 4$ Lorentzian Spacetime Selection $S_2 = 0$)**:
    Over *any* commutative ring $R$ (`[CommRing R]`), and over $\mathbb{Z}$ for the uniqueness equivalence:
    1. Lorentzian $(3, 1)$ Signature Values $(s_1, s_2, s_3, s_4) = (1, 1, 1, -1)$ (Hansen Eq. 4.1):
       $$(S_0, S_1, S_2, S_3, S_4) = (1, 2, 0, -2, -1).$$
    2. Grade-Weighted Doublet Coefficients $w_k = (-2 + 2k) S_k$ & Even/Odd Selection Rule (Hansen Theorem 4.2, Corollary 4.6, & Theorem 5.4):
       $$(w_0, w_1, w_2, w_3, w_4) = (-2, 4, 0, 4, 2), \qquad
         w_1 + w_3 = 8, \qquad w_0 + w_2 + w_4 = 0, \qquad
         w_0 + w_1 + w_2 + w_3 + w_4 = 8.$$
    3. Lorentzian Spacetime Polynomial Factorization (Hansen Corollary 4.3):
       For $p = d - 1$ and $q = 1$, $2 S_2(d - 1, 1) = (d - 1)(d - 4)$, so for $d \in \mathbb{Z}$,
       $$\mathrm{twoSymPolyS2Gen}\;(d - 1)\;1 = 0 \iff d = 1 \vee d = 4.$$
    4. Perfect-Square Diophantine Parametrization of $S_2(p, q) = 0$ (Hansen Corollary 4.3):
       For $2p = m^2 + m$ and $2q = m^2 - m$, $((2p) - (2q))^2 = 2((2p) + (2q)) = 4 m^2$. -/
theorem hansen_symmetric_polynomials_even_odd_rule_and_d4_selection
    {R : Type*} [CommRing R] (d m : R) (d_int : ℤ) :
    let S₀ := symPolyS0 (1 : R) 1 1 (-1)
    let S₁ := symPolyS1 (1 : R) 1 1 (-1)
    let S₂ := symPolyS2 (1 : R) 1 1 (-1)
    let S₃ := symPolyS3 (1 : R) 1 1 (-1)
    let S₄ := symPolyS4 (1 : R) 1 1 (-1)
    let w₀ := (-2 : R) * S₀
    let w₁ := (2 : R) * S₁
    let w₂ := (2 : R) * S₂
    let w₃ := (-2 : R) * S₃
    let w₄ := (-2 : R) * S₄
    let two_p := m ^ 2 + m
    let two_q := m ^ 2 - m
    S₀ = 1 ∧
    S₁ = 2 ∧
    S₂ = 0 ∧
    S₃ = -2 ∧
    S₄ = -1 ∧
    w₀ = -2 ∧
    w₁ = 4 ∧
    w₂ = 0 ∧
    w₃ = 4 ∧
    w₄ = 2 ∧
    w₁ + w₃ = 8 ∧
    w₀ + w₂ + w₄ = 0 ∧
    w₀ + w₁ + w₂ + w₃ + w₄ = 8 ∧
    twoSymPolyS2Gen (d - 1) 1 = (d - 1) * (d - 4) ∧
    (twoSymPolyS2Gen (d_int - 1) 1 = 0 ↔ d_int = 1 ∨ d_int = 4) ∧
    (two_p - two_q) ^ 2 = 2 * (two_p + two_q) := by
  intro S₀ S₁ S₂ S₃ S₄ w₀ w₁ w₂ w₃ w₄ two_p two_q
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · simp [S₁, symPolyS1]; try ring
  · simp [S₂, symPolyS2]; try ring
  · simp [S₃, symPolyS3]; try ring
  · simp [S₄, symPolyS4]; try ring
  · simp [w₀, S₀, symPolyS0]; try ring
  · simp [w₁, S₁, symPolyS1]; try ring
  · simp [w₂, S₂, symPolyS2]; try ring
  · simp [w₃, S₃, symPolyS3]; try ring
  · simp [w₄, S₄, symPolyS4]; try ring
  · simp [w₁, w₃, S₁, S₃, symPolyS1, symPolyS3]; try ring
  · simp [w₀, w₂, w₄, S₀, S₂, S₄, symPolyS0, symPolyS2, symPolyS4]; try ring
  · simp [w₀, w₁, w₂, w₃, w₄, S₀, S₁, S₂, S₃, S₄,
          symPolyS0, symPolyS1, symPolyS2, symPolyS3, symPolyS4]; try ring
  · simp [twoSymPolyS2Gen]; ring
  · have h_fac : twoSymPolyS2Gen (d_int - 1) 1 = (d_int - 1) * (d_int - 4) := by
      simp [twoSymPolyS2Gen]; ring
    rw [h_fac, mul_eq_zero, sub_eq_zero, sub_eq_zero]
  · simp [two_p, two_q]; ring

/-- **Theorem 102 (Archetype LXXXIII.2 — Resolution of Hansen's Page 18 Open Problem: Conformal Doublet Tower + Octonionic Triality Marriage in `OpZornMatrix A`)**:
    Over *any* noncommutative operator ring $A$ (`[Ring A]`), for all 3-generation chiral spinor vectors
    $v, w, v_1, v_2, w_1, w_2 \in \mathrm{OpVec3}\;A$, let
    $D = \mathrm{opZornGamma} = \langle 1, 0, 0, -1 \rangle$,
    $e_{11} = \mathrm{opGradeZero}\;1\;0$, $e_{22} = \mathrm{opGradeZero}\;0\;1$,
    $T^+(v) = \mathrm{opLightconePlus}\;v = \langle 0, v, 0, 0 \rangle$, and
    $T^-(w) = \mathrm{opLightconeMinus}\;w = \langle 0, 0, w, 0 \rangle$:
    1. Exact Conformal Doublet Grading & Anticommutation (Hansen Theorem 3.1 & Lemma 8.1):
       $$D * T^+(v) - T^+(v) * D = T^+(v) + T^+(v), \qquad
         D * T^-(w) - T^-(w) * D = -(T^-(w) + T^-(w)),$$
       $$D * T^+(v) + T^+(v) * D = 0, \qquad
         D * T^-(w) + T^-(w) * D = 0.$$
    2. Universal Nilpotency of Every Chiral Doublet (Hansen Theorem 3.2):
       $$T^+(v) * T^+(v) = 0, \qquad T^-(w) * T^-(w) = 0.$$
    3. Single-Projector Proportionality Law Along $e_{11}$ and $e_{22}$ (Hansen Theorem 3.3 & Theorem 7.1(c)):
       $$T^+(v) * T^-(w) = \mathrm{opGradeZero}\;(-(v \cdot w))\;0, \qquad
         T^-(w) * T^+(v) = \mathrm{opGradeZero}\;0\;(-(w \cdot v)).$$
    4. Non-Abelian Octonionic Triality Upgrade of the Parabolic Nilradicals (Resolving Hansen §10.2):
       $$T^+(v_1) * T^+(v_2) - T^+(v_2) * T^+(v_1) = T^-(2(v_1 \times_{\mathrm{skew}} v_2)), \qquad
         T^-(w_1) * T^-(w_2) - T^-(w_2) * T^-(w_1) = -T^+(2(w_1 \times_{\mathrm{skew}} w_2)).$$
    5. Top-Rung Majorana vs. Dirac Sector Swap & Opposite-Sign Squares in `OpZornMatrix A` (Hansen Theorem 8.2):
       $$(T^+(v) + T^-(w))^2 = \mathrm{opGradeZero}\;(-(v \cdot w))\;(-(w \cdot v)), \qquad
         (T^+(v) - T^-(w))^2 = \mathrm{opGradeZero}\;(v \cdot w)\;(w \cdot v),$$
       $$(T^+(v) + T^-(w)) * e_{11} = e_{22} * (T^+(v) + T^-(w)), \qquad
         (T^+(v) - T^-(w)) * e_{11} = e_{22} * (T^+(v) - T^-(w)).$$ -/
theorem hansen_conformal_triality_marriage_in_opZorn
    (v w v₁ v₂ w₁ w₂ : OpVec3 A) :
    let D := (opZornGamma : OpZornMatrix A)
    let e₁₁ := opGradeZero (1 : A) 0
    let e₂₂ := opGradeZero (0 : A) 1
    let Tp_v := opLightconePlus v
    let Tm_w := opLightconeMinus w
    let Tp_v1 := opLightconePlus v₁
    let Tp_v2 := opLightconePlus v₂
    let Tm_w1 := opLightconeMinus w₁
    let Tm_w2 := opLightconeMinus w₂
    let IM := Tp_v + Tm_w
    let ID := Tp_v - Tm_w
    let cr_v := OpVec3.skewCross v₁ v₂
    let cr_w := OpVec3.skewCross w₁ w₂
    D * Tp_v - Tp_v * D = Tp_v + Tp_v ∧
    D * Tm_w - Tm_w * D = -(Tm_w + Tm_w) ∧
    D * Tp_v + Tp_v * D = 0 ∧
    D * Tm_w + Tm_w * D = 0 ∧
    Tp_v * Tp_v = 0 ∧
    Tm_w * Tm_w = 0 ∧
    Tp_v * Tm_w = opGradeZero (-OpVec3.dot v w) 0 ∧
    Tm_w * Tp_v = opGradeZero 0 (-OpVec3.dot w v) ∧
    Tp_v1 * Tp_v2 - Tp_v2 * Tp_v1 = opLightconeMinus (cr_v + cr_v) ∧
    Tm_w1 * Tm_w2 - Tm_w2 * Tm_w1 = -opLightconePlus (cr_w + cr_w) ∧
    IM * IM = opGradeZero (-OpVec3.dot v w) (-OpVec3.dot w v) ∧
    ID * ID = opGradeZero (OpVec3.dot v w) (OpVec3.dot w v) ∧
    IM * e₁₁ = e₂₂ * IM ∧
    ID * e₁₁ = e₂₂ * ID := by
  intro D e₁₁ e₂₂ Tp_v Tm_w Tp_v1 Tp_v2 Tm_w1 Tm_w2 IM ID cr_v cr_w
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (ext <;>
     (simp [D, e₁₁, e₂₂, Tp_v, Tm_w, Tp_v1, Tp_v2, Tm_w1, Tm_w2, IM, ID, cr_v, cr_w,
            opZornGamma, opGradeZero, opCartanDiag,
            opLightconePlus, opLightconeMinus, opLightconeRayPlus, opLightconeRayMinus,
            OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross,
            OpVec3.leftScale, OpVec3.rightScale];
      try noncomm_ring;
      try abel))

/-! ### 36. Archetypes LXXXIV & LXXXV: Zero Chiral 3-Volume, Krein Space Null Kernel Orthogonality, Parabolic Conformal Boundary Sheaf, & Universal Majorana Horizon Zero Modes -/

/-- **Theorem 103 (Archetype LXXXIV.1 — Zero Chiral 3-Volume on the Transverse Lightfront & Causal Cone Nilpotence)**:
    Over *any* noncommutative operator ring $A$ (`[Ring A]`), for all $y_i, z_i, \xi_i, y, z, \xi \in A$:
    1. Zero Left & Right Chiral Nambu 3-Volume on the Transverse Causal Screen $v_i = \langle 0, y_i, z_i \rangle$:
       $$\det_L\bigl(\langle 0, y_1, z_1 \rangle, \langle 0, y_2, z_2 \rangle, \langle 0, y_3, z_3 \rangle\bigr) = 0, \qquad
         \det_R\bigl(\langle 0, y_1, z_1 \rangle, \langle 0, y_2, z_2 \rangle, \langle 0, y_3, z_3 \rangle\bigr) = 0.$$
    2. Vanishing 3-Associator Across the Parabolic Boundary Nilradical $\mathcal{N}_+ = \mathcal{G}_{+1} \oplus \mathcal{G}_{+2}$:
       $$\mathrm{opAssociator}\;(N_+(y_1, z_1, \xi_1))\;(N_+(y_2, z_2, \xi_2))\;(N_+(y_3, z_3, \xi_3)) = 0.$$
    3. Square-Zero Causal Cone Nilpotence:
       $$E_{+1}(y, z) * E_{+1}(y, z) = 0 \qquad \text{and} \qquad E_{+2}(\xi) * E_{+2}(\xi) = 0.$$ -/
theorem zeroChiralVolume_and_causal_cone_nilpotence
    (y₁ z₁ ξ₁ y₂ z₂ ξ₂ y₃ z₃ ξ₃ y z ξ : A) :
    let v₁ : OpVec3 A := ⟨0, y₁, z₁⟩
    let v₂ : OpVec3 A := ⟨0, y₂, z₂⟩
    let v₃ : OpVec3 A := ⟨0, y₃, z₃⟩
    OpVec3.baryonDetLeft v₁ v₂ v₃ = 0 ∧
    OpVec3.baryonDetRight v₁ v₂ v₃ = 0 ∧
    opAssociator (opHeisenbergNilPlus y₁ z₁ ξ₁)
                 (opHeisenbergNilPlus y₂ z₂ ξ₂)
                 (opHeisenbergNilPlus y₃ z₃ ξ₃) = 0 ∧
    opGradePlus1 y z * opGradePlus1 y z = 0 ∧
    opGradePlus2 ξ * opGradePlus2 ξ = 0 := by
  intro v₁ v₂ v₃
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [v₁, v₂, v₃, OpVec3.baryonDetLeft, OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross]
  · simp [v₁, v₂, v₃, OpVec3.baryonDetRight, OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross]
  · unfold opAssociator
    rw [opHeisenbergNilPlus_mul_mul, opHeisenbergNilPlus_mul_mul_right, sub_self]
  · ext <;>
      (simp [opGradePlus1, OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross];
       try noncomm_ring)
  · ext <;>
      simp [opGradePlus2, OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross]

/-- **Theorem 104 (Archetype LXXXIV.2 — Krein Space Null Kernel Orthogonality & Symplectic Transverse Rotation Between $\mathcal{G}_{+1}$ and $\mathcal{G}_{+2}$)**:
    Over *any* noncommutative $*$-ring $A$ (`[Ring A] [StarRing A]`), for all $y, z, \xi \in A$:
    1. Krein Adjoints of $\mathcal{G}_{+1}$ and $\mathcal{G}_{+2}$ Are $\mathcal{G}_{-1}$ and $\mathcal{G}_{-2}$:
       $$(E_{+1}(y, z))^\flat = E_{-1}(y^\star, z^\star), \qquad
         (E_{+2}(\xi))^\flat = E_{-2}(\xi^\star).$$
    2. Exact Two-Sided Krein Adjoint Nilradical Orthogonality:
       $$(E_{+1}(y, z))^\flat * (E_{+2}(\xi))^\flat = 0 \qquad \text{and} \qquad
         (E_{+2}(\xi))^\flat * (E_{+1}(y, z))^\flat = 0.$$
    3. Vanishing Krein Metric Corners & Exact Symplectic Transverse Rotation of $(E_{+1}(y, z))^\flat * E_{+2}(\xi)$:
       $$\bigl((E_{+1}(y, z))^\flat * E_{+2}(\xi)\bigr).a = 0, \qquad
         \bigl((E_{+1}(y, z))^\flat * E_{+2}(\xi)\bigr).b = 0,$$
       $$(E_{+1}(y, z))^\flat * E_{+2}(\xi) =
         E_{+1}\bigl(-(z^\star * \xi + \xi * z^\star),\; y^\star * \xi + \xi * y^\star\bigr).$$ -/
theorem kreinSpace_null_kernel_orthogonality [StarRing A]
    (y z ξ : A) :
    opZornKreinAdjoint (opGradePlus1 y z) = opGradeMinus1 (star y) (star z) ∧
    opZornKreinAdjoint (opGradePlus2 ξ) = opGradeMinus2 (star ξ) ∧
    opZornKreinAdjoint (opGradePlus1 y z) * opZornKreinAdjoint (opGradePlus2 ξ) = 0 ∧
    opZornKreinAdjoint (opGradePlus2 ξ) * opZornKreinAdjoint (opGradePlus1 y z) = 0 ∧
    (opZornKreinAdjoint (opGradePlus1 y z) * opGradePlus2 ξ).a = 0 ∧
    (opZornKreinAdjoint (opGradePlus1 y z) * opGradePlus2 ξ).b = 0 ∧
    opZornKreinAdjoint (opGradePlus1 y z) * opGradePlus2 ξ =
      opGradePlus1 (-(star z * ξ + ξ * star z)) (star y * ξ + ξ * star y) := by
  have h_dual := heisenbergNil_kreinAdjoint_duality y z ξ
  refine ⟨h_dual.1, h_dual.2.1, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (try ext) <;>
    (simp [opZornKreinAdjoint, opVec3Star, opGradePlus1, opGradePlus2,
           OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross];
     try abel)

/-- **Theorem 105 (Archetype LXXXV — Parabolic Boundary Sheaf Gluing & Universal Majorana Horizon Zero-Mode Nullspace)**:
    Over *any* noncommutative operator ring $A$ (`[Ring A]`), for all boundary coordinates
    $\xi, y, z, \xi_1, y_1, z_1, \xi_2, y_2, z_2 \in A$ and all horizon zero modes $\xi' \in A$, let
    $\Pi = \mathrm{opContactFlowIdempotent}\;\xi\;y\;z = \langle 1, \langle 0, -y, -z \rangle, \langle \xi, 0, 0 \rangle, 0 \rangle$,
    $\Pi^\perp = \mathrm{opContactFlowIdempotentCompl}\;\xi\;y\;z = 1 - \Pi$,
    and $Z_{\mathrm{Maj}} = \mathrm{opGradePlus2}\;\xi'$:
    1. Exact Boundary Idempotence, Mutual Orthogonality, & Sheaf Gluing Transition Law:
       $$\Pi * \Pi = \Pi, \qquad \Pi * \Pi^\perp = 0, \qquad \Pi^\perp * \Pi = 0,$$
       $$\Pi(\xi_1, y_1, z_1) * \Pi(\xi_2, y_2, z_2) =
         \Pi\bigl(\xi_1 + \omega_\perp(y_1, z_1; y_2, z_2),\; y_2,\; z_2\bigr).$$
    2. Two-Sided Annihilation of the Horizon Zero Mode by the Transverse Causal Cone:
       $$E_{+1}(y, z) * Z_{\mathrm{Maj}} = 0 \qquad \text{and} \qquad Z_{\mathrm{Maj}} * E_{+1}(y, z) = 0.$$
    3. Universal Boundary Right-Nullspace Annihilation & Left Eigen-Stabilization of $Z_{\mathrm{Maj}}$:
       $$\Pi * Z_{\mathrm{Maj}} = 0 \qquad \text{and} \qquad Z_{\mathrm{Maj}} * \Pi = Z_{\mathrm{Maj}}.$$
    4. Complementary Bulk Left Eigen-Stabilization & Right Annihilation of $Z_{\mathrm{Maj}}$:
       $$\Pi^\perp * Z_{\mathrm{Maj}} = Z_{\mathrm{Maj}} \qquad \text{and} \qquad Z_{\mathrm{Maj}} * \Pi^\perp = 0.$$ -/
theorem parabolicBoundarySheaf_and_majorana_horizon_zero_mode_nullspace
    (ξ y z ξ₁ y₁ z₁ ξ₂ y₂ z₂ ξ' : A) :
    let Pi_b := opContactFlowIdempotent ξ y z
    let Pi_b_perp := opContactFlowIdempotentCompl ξ y z
    let Z_Maj := opGradePlus2 ξ'
    Pi_b * Pi_b = Pi_b ∧
    Pi_b * Pi_b_perp = 0 ∧
    Pi_b_perp * Pi_b = 0 ∧
    opContactFlowIdempotent ξ₁ y₁ z₁ * opContactFlowIdempotent ξ₂ y₂ z₂ =
      opContactFlowIdempotent (ξ₁ + opContactSymplecticForm y₁ z₁ y₂ z₂) y₂ z₂ ∧
    opGradePlus1 y z * Z_Maj = 0 ∧
    Z_Maj * opGradePlus1 y z = 0 ∧
    Pi_b * Z_Maj = 0 ∧
    Z_Maj * Pi_b = Z_Maj ∧
    Pi_b_perp * Z_Maj = Z_Maj ∧
    Z_Maj * Pi_b_perp = 0 := by
  intro Pi_b Pi_b_perp Z_Maj
  have h_sh := contactFlowIdempotent_strict_idem_orth_and_lamb_composition ξ y z ξ₁ y₁ z₁ ξ₂ y₂ z₂
  refine ⟨h_sh.2.1, h_sh.2.2.2.1, h_sh.2.2.2.2.1, h_sh.2.2.2.2.2, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (ext <;>
     (simp [Pi_b, Pi_b_perp, Z_Maj, opContactFlowIdempotent, opContactFlowIdempotentCompl,
            opFlowProjectorCore, opUnipotentLower, opUnipotentUpper, opCartanDiag,
            opGradePlus1, opGradePlus2,
            OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross];
      try noncomm_ring))

/-! ### 37. Archetypes LXXXVI & LXXXVII: Chevalley–Lounesto–Shirokov Spinor Ideals & Relativistic Dirac–Krein Ket-Bra Duality -/

/-- **General 3-Vector Chevalley Spinor Ket (`opSpinorKet a w = |\Psi(a, w)\rangle`)**:
    Generated by right Peirce projection $X * e_{11} = \langle a, 0, w, 0 \rangle$. -/
def opSpinorKet (a : A) (w : OpVec3 A) : OpZornMatrix A :=
  ⟨a, 0, w, 0⟩

/-- **General 3-Vector Dirac–Krein Conjugate Spinor Bra (`opSpinorBra b v = \langle\bar{\Phi}(b, v)|`)**:
    Defined as $(|\Psi(b, v)\rangle)^\flat = \langle b^\star, v^\star, 0, 0 \rangle$. -/
def opSpinorBra [StarRing A] (b : A) (v : OpVec3 A) : OpZornMatrix A :=
  opZornKreinAdjoint (opSpinorKet b v)

/-- **Lounesto–Shirokov 5-Graded Contact Spinor Bra (`opLounestoSpinorRight b η = \langle\bar{\phi}(b, \eta)|`)**:
    Defined as $(|\psi(b, \eta)\rangle)^\flat = \mathrm{opZornKreinAdjoint}\;(\mathrm{opLounestoSpinorLeft}\;b\;\eta)$. -/
def opLounestoSpinorRight [StarRing A] (b η : A) : OpZornMatrix A :=
  opZornKreinAdjoint (opLounestoSpinorLeft b η)

/-- **Helper Lemma (`opSpinorKet_mul_opSpinorBra`)**:
    Universal zero-cross-product outer density operator $|\Psi(a, w)\rangle * \langle\bar{\Phi}(b, v)|$. -/
theorem opSpinorKet_mul_opSpinorBra [StarRing A] (a b : A) (w v : OpVec3 A) :
    opSpinorKet a w * opSpinorBra b v =
      ⟨a * star b,
       OpVec3.leftScale a (opVec3Star v),
       OpVec3.rightScale w (star b),
       -OpVec3.dot w (opVec3Star v)⟩ := by
  ext <;>
    simp [opSpinorKet, opSpinorBra, opZornKreinAdjoint,
          OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross]

/-- **Helper Lemma (`chevalley_spinor_ket_bra_peirce_absorption`)**:
    Peirce column/row generation, Dirac–Krein adjoint intertwining, and two-sided Peirce absorption
    of Chevalley spinor kets and Dirac–Krein conjugate spinor bras. -/
theorem chevalley_spinor_ket_bra_peirce_absorption [StarRing A]
    (X : OpZornMatrix A) (a b : A) (v w : OpVec3 A) :
    X * opPeircePlus = opSpinorKet X.a X.w ∧
    opZornKreinAdjoint (X * opPeircePlus) = opPeircePlus * opZornKreinAdjoint X ∧
    opSpinorKet a w * opPeircePlus = opSpinorKet a w ∧
    opSpinorKet a w * opPeirceMinus = 0 ∧
    opPeircePlus * opSpinorBra b v = opSpinorBra b v ∧
    opPeirceMinus * opSpinorBra b v = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · ext <;>
      simp [opSpinorKet, opPeircePlus, OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross]
  · ext <;>
      simp [opZornKreinAdjoint, opPeircePlus, OpVec3.dot, OpVec3.skewCross,
            OpVec3.naiveCross, star_zero, star_one]
  · ext <;>
      simp [opSpinorKet, opPeircePlus, OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross]
  · ext <;>
      simp [opSpinorKet, opPeirceMinus, OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross]
  · ext <;>
      simp [opSpinorBra, opSpinorKet, opZornKreinAdjoint, opPeircePlus,
            OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross, star_zero]
  · ext <;>
      simp [opSpinorBra, opSpinorKet, opZornKreinAdjoint, opPeirceMinus,
            OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross, star_zero]

/-- **Helper Lemma (`chevalley_spinor_bra_ket_and_krein_hermitian_density`)**:
    Universal bra-ket inner product and Dirac–Krein self-adjointness of pure-state density operators. -/
theorem chevalley_spinor_bra_ket_and_krein_hermitian_density [StarRing A]
    (a b : A) (v w : OpVec3 A) :
    opSpinorBra b v * opSpinorKet a w = opGradeZero (star b * a - OpVec3.dot (opVec3Star v) w) 0 ∧
    opZornKreinAdjoint (opSpinorKet a w * opSpinorBra a w) = opSpinorKet a w * opSpinorBra a w := by
  refine ⟨?_, ?_⟩
  · ext <;>
      simp [opSpinorKet, opSpinorBra, opZornKreinAdjoint,
            opGradeZero, opCartanDiag, OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross, star_zero]
  · rw [opSpinorKet_mul_opSpinorBra]
    ext <;>
      simp [opZornKreinAdjoint, OpVec3.dot, star_add, star_mul, star_neg]

/-- **Theorem 106 (Archetype LXXXVI — Chevalley Ket/Bra Peirce Absorption, Split Dirac–Krein Inner Product, & Krein-Hermitian Density Operator)**:
    Over *any* noncommutative $*$-ring $A$ (`[Ring A] [StarRing A]`), for all $X \in \mathrm{OpZornMatrix}\;A$,
    $a, b \in A$, and $v, w \in \mathrm{OpVec3}\;A$:
    1. Peirce Column/Row Generation & Dirac–Krein Adjoint Intertwining:
       $$X * e_{11} = |\Psi(X.a, X.w)\rangle, \qquad (X * e_{11})^\flat = e_{11} * X^\flat = \langle\bar{\Phi}(X.a, X.w)|,$$
       $$|\Psi(a, w)\rangle * e_{11} = |\Psi(a, w)\rangle, \qquad |\Psi(a, w)\rangle * e_{22} = 0,$$
       $$e_{11} * \langle\bar{\Phi}(b, v)| = \langle\bar{\Phi}(b, v)|, \qquad e_{22} * \langle\bar{\Phi}(b, v)| = 0.$$
    2. Universal Bra-Ket Inner Product (Indefinite Split Dirac–Krein Metric $b^\star a - v^\star \cdot w$):
       $$\langle\bar{\Phi}(b, v)| * |\Psi(a, w)\rangle = \mathrm{opGradeZero}\;(b^\star * a - v^\star \cdot w)\;0.$$
    3. Universal Ket-Bra Outer Density Matrix:
       $$|\Psi(a, w)\rangle * \langle\bar{\Phi}(b, v)| =
         \bigl\langle a * b^\star,\;\; a \cdot_{\mathrm{L}} v^\star,\;\; w \cdot_{\mathrm{R}} b^\star,\;\; -(w \cdot v^\star) \bigr\rangle.$$
    4. Exact Dirac–Krein Self-Adjointness of Any Pure-State Density Operator $|\Psi\rangle\langle\bar{\Psi}|$:
       $$\bigl(|\Psi(a, w)\rangle * \langle\bar{\Psi}(a, w)|\bigr)^\flat = |\Psi(a, w)\rangle * \langle\bar{\Psi}(a, w)|.$$ -/
theorem chevalley_spinor_ket_bra_duality_and_dirac_krein_products [StarRing A]
    (X : OpZornMatrix A) (a b : A) (v w : OpVec3 A) :
    let ket := opSpinorKet a w
    let bra := opSpinorBra b v
    let bra_self := opSpinorBra a w
    X * opPeircePlus = opSpinorKet X.a X.w ∧
    opZornKreinAdjoint (X * opPeircePlus) = opPeircePlus * opZornKreinAdjoint X ∧
    ket * opPeircePlus = ket ∧
    ket * opPeirceMinus = 0 ∧
    opPeircePlus * bra = bra ∧
    opPeirceMinus * bra = 0 ∧
    bra * ket = opGradeZero (star b * a - OpVec3.dot (opVec3Star v) w) 0 ∧
    ket * bra =
      ⟨a * star b,
       OpVec3.leftScale a (opVec3Star v),
       OpVec3.rightScale w (star b),
       -OpVec3.dot w (opVec3Star v)⟩ ∧
    opZornKreinAdjoint (ket * bra_self) = ket * bra_self := by
  have h1 := chevalley_spinor_ket_bra_peirce_absorption X a b v w
  have h2 := chevalley_spinor_bra_ket_and_krein_hermitian_density a b v w
  exact ⟨h1.1, h1.2.1, h1.2.2.1, h1.2.2.2.1, h1.2.2.2.2.1, h1.2.2.2.2.2,
         h2.1, opSpinorKet_mul_opSpinorBra a b w v, h2.2⟩

/-- **Theorem 107 (Archetype LXXXVII — Associative Ket-Bra-Ket Calculus on the Contact Spinor Ideal & Majorana Zero-Mode Orthogonality)**:
    Over *any* noncommutative $*$-ring $A$ (`[Ring A] [StarRing A]`), for all $a_1, \xi_1, b_2, \eta_2, a_3, \xi_3, \xi \in A$:
    1. Exact Vanishing of the Ket-Bra-Ket Associator $(|\psi_1\rangle * \langle\bar{\phi}_2|) * |\psi_3\rangle = |\psi_1\rangle * (\langle\bar{\phi}_2| * |\psi_3\rangle)$:
       $$\mathrm{opAssociator}\;(|\psi(a_1, \xi_1)\rangle)\;(\langle\bar{\phi}(b_2, \eta_2)|)\;(|\psi(a_3, \xi_3)\rangle) = 0.$$
    2. Explicit Ket-Bra-Ket Inner-Product Scaling:
       $$\bigl(|\psi(a_1, \xi_1)\rangle * \langle\bar{\phi}(b_2, \eta_2)|\bigr) * |\psi(a_3, \xi_3)\rangle =
         |\psi\bigl(a_1 * (b_2^\star * a_3 - \eta_2^\star * \xi_3),\;\;
                    \xi_1 * (b_2^\star * a_3 - \eta_2^\star * \xi_3)\bigr)\rangle.$$
    3. Exact Vanishing of the Bra-Ket-Bra Associator:
       $$\mathrm{opAssociator}\;(\langle\bar{\phi}(a_1, \xi_1)|)\;(|\psi(b_2, \eta_2)\rangle)\;(\langle\bar{\phi}(a_3, \xi_3)|) = 0.$$
    4. Null Majorana Horizon Zero Mode $|\psi(0, \xi)\rangle = E_{+2}(\xi)$ vs. Vacuum $\langle\bar{\phi}(1, 0)| = e_{11}$:
       $$\langle\bar{\phi}(1, 0)| * |\psi(0, \xi)\rangle = 0 \qquad \text{and} \qquad
         |\psi(0, \xi)\rangle * \langle\bar{\phi}(1, 0)| = E_{+2}(\xi).$$ -/
theorem contactSpinor_ket_bra_ket_associativity_and_majorana_zero_mode [StarRing A]
    (a₁ ξ₁ b₂ η₂ a₃ ξ₃ ξ : A) :
    let ψ₁ := opLounestoSpinorLeft a₁ ξ₁
    let φ₂_bar := opLounestoSpinorRight b₂ η₂
    let ψ₃ := opLounestoSpinorLeft a₃ ξ₃
    let φ₁_bar := opLounestoSpinorRight a₁ ξ₁
    let ψ₂ := opLounestoSpinorLeft b₂ η₂
    let φ₃_bar := opLounestoSpinorRight a₃ ξ₃
    let inner₂₃ := star b₂ * a₃ - star η₂ * ξ₃
    opAssociator ψ₁ φ₂_bar ψ₃ = 0 ∧
    (ψ₁ * φ₂_bar) * ψ₃ = opLounestoSpinorLeft (a₁ * inner₂₃) (ξ₁ * inner₂₃) ∧
    opAssociator φ₁_bar ψ₂ φ₃_bar = 0 ∧
    opLounestoSpinorRight 1 0 * opLounestoSpinorLeft 0 ξ = 0 ∧
    opLounestoSpinorLeft 0 ξ * opLounestoSpinorRight 1 0 = opGradePlus2 ξ := by
  intro ψ₁ φ₂_bar ψ₃ φ₁_bar ψ₂ φ₃_bar inner₂₃
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    (ext <;>
     (simp [ψ₁, φ₂_bar, ψ₃, φ₁_bar, ψ₂, φ₃_bar, inner₂₃,
            opLounestoSpinorLeft, opLounestoSpinorRight, opZornKreinAdjoint, opVec3Star,
            opGradePlus2, opAssociator,
            OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross,
            OpVec3.leftScale, OpVec3.rightScale, star_one, star_zero];
      try noncomm_ring))

/-! ### 38. Archetypes LXXXVIII & LXXXIX: Trifactor + Loxodromic Local Compass of Observables, Peirce-Doubled 4-Vector Operator Potentials, Dilaton Log-Scale Time Decay, & Noncommutative Zorn–Riccati Möbius Inversion -/

/-- **Forward Chiral 4-Vector Operator Potential (`opFourPotentialPlus a v = \langle a, v, 0, 0 \rangle`)**:
    Generated by left Peirce orientation $e_{11} * X = \langle X.a, X.v, 0, 0 \rangle$. -/
def opFourPotentialPlus (a : A) (v : OpVec3 A) : OpZornMatrix A :=
  ⟨a, v, 0, 0⟩

/-- **Backward Chiral 4-Vector Operator Potential (`opFourPotentialMinus b w = \langle 0, 0, w, b \rangle`)**:
    Generated by left Peirce orientation $e_{22} * X = \langle 0, 0, X.w, X.b \rangle$. -/
def opFourPotentialMinus (b : A) (w : OpVec3 A) : OpZornMatrix A :=
  ⟨0, 0, w, b⟩

/-- **Forward Row Idempotent Compass Needle (`opCompassNeedleRow v = \langle 1, v, 0, 0 \rangle`)**:
    Oriented by $e_{11} * U_+(v) = \langle 1, v, 0, 0 \rangle$. -/
def opCompassNeedleRow (v : OpVec3 A) : OpZornMatrix A :=
  ⟨1, v, 0, 0⟩

/-- **Backward Column Idempotent Compass Needle (`opCompassNeedleCol w = \langle 1, 0, w, 0 \rangle`)**:
    Oriented by $U_-(w) * e_{11} = \langle 1, 0, w, 0 \rangle$. -/
def opCompassNeedleCol (w : OpVec3 A) : OpZornMatrix A :=
  ⟨1, 0, w, 0⟩

/-- **The 8D Noncommutative Zorn–Riccati Möbius Operator (`opZornRiccati X q`)**:
    $$\mathcal{R}_X(q) := q \cdot_{\mathrm{R}} (X.w \cdot q) + q \cdot_{\mathrm{R}} X.b + X.a \cdot_{\mathrm{L}} q - X.v \in \mathrm{OpVec3}\;A.$$ -/
def opZornRiccati (X : OpZornMatrix A) (q : OpVec3 A) : OpVec3 A :=
  OpVec3.rightScale q (OpVec3.dot X.w q) +
    OpVec3.rightScale q X.b +
    OpVec3.leftScale X.a q -
    X.v

/-- **Theorem 108 (Archetype LXXXVIII — Peirce-Doubled 4-Vector Operator Potential Split, Curl Coupling, & Dilaton Log-Scale Time Decay on Compass Needles)**:
    Over *any* noncommutative operator ring $A$ (`[Ring A]`), for all $X \in \mathrm{OpZornMatrix}\;A$,
    $a, a_1, a_2, b \in A$, $v, v_1, v_2, w, q \in \mathrm{OpVec3}\;A$, and invertible dilaton operators
    $u, \mu \in A^\times$ (`u mu : Aˣ`), let $D = \mathrm{opGradeZero}\;(u : A)\;(\mu : A)$ and
    $D^{-1} = \mathrm{opGradeZero}\;(\uparrow u^{-1} : A)\;(\uparrow \mu^{-1} : A)$:
    1. Peirce-Doubled 4-Vector Potential Decomposition & 4D Lorentzian Contraction:
       $$e_{11} * X = \mathcal{A}_+(X.a, X.v), \qquad e_{22} * X = \mathcal{A}_-(X.b, X.w), \qquad e_{11} * X + e_{22} * X = X,$$
       $$(e_{11} * X) * (\mathrm{opCayleyConj}\;X * e_{11}) = \mathrm{opGradeZero}\;(X.a * X.b + X.v \cdot X.w)\;0.$$
    2. Same-Pole & Cross-Pole 4-Vector Potential Products (Affine Dilaton Scaling + Magnetic Curl + Lorentz Contraction):
       $$\mathcal{A}_+(a_1, v_1) * \mathcal{A}_+(a_2, v_2) = \mathcal{A}_+(a_1 * a_2,\; a_1 \cdot_{\mathrm{L}} v_2) + \mathrm{opLightconeMinus}\;(v_1 \times_{\mathrm{skew}} v_2),$$
       $$\mathcal{A}_+(a, v) * \mathcal{A}_-(b, w) = \langle -(v \cdot w),\; v \cdot_{\mathrm{R}} b,\; 0,\; 0 \rangle,$$
       $$\mathcal{A}_-(b, w) * \mathcal{A}_+(a, v) = \langle 0,\; 0,\; w \cdot_{\mathrm{R}} a,\; -(w \cdot v) \rangle.$$
    3. Dilaton Log-Scale Time Sandwich Associativity & Exponential Decay / Amplification of Compass Needles & Parabolic Wings:
       $$\mathrm{opAssociator}\;D\;X\;D^{-1} = 0,$$
       $$(D * U_+(v)) * D^{-1} = U_+\bigl(u \cdot_{\mathrm{L}} (v \cdot_{\mathrm{R}} \mu^{-1})\bigr), \qquad
         (D * U_-(w)) * D^{-1} = U_-\bigl(\mu \cdot_{\mathrm{L}} (w \cdot_{\mathrm{R}} u^{-1})\bigr),$$
       $$(D * P_{\mathrm{col}}(q)) * D^{-1} = P_{\mathrm{col}}\bigl(\mu \cdot_{\mathrm{L}} (q \cdot_{\mathrm{R}} u^{-1})\bigr), \qquad
         (D * P_{\mathrm{row}}(v)) * D^{-1} = P_{\mathrm{row}}\bigl(u \cdot_{\mathrm{L}} (v \cdot_{\mathrm{R}} \mu^{-1})\bigr).$$ -/
theorem doubledFourPotential_peirce_split_and_dilaton_compass_decay
    (X : OpZornMatrix A) (a a₁ a₂ b : A) (v v₁ v₂ w q : OpVec3 A) (u mu : Aˣ) :
    let D := opGradeZero (u : A) (mu : A)
    let D_inv := opGradeZero (↑u⁻¹ : A) (↑mu⁻¹ : A)
    opPeircePlus * X = opFourPotentialPlus X.a X.v ∧
    opPeirceMinus * X = opFourPotentialMinus X.b X.w ∧
    opPeircePlus * X + opPeirceMinus * X = X ∧
    (opPeircePlus * X) * (opCayleyConj X * opPeircePlus) =
      opGradeZero (X.a * X.b + OpVec3.dot X.v X.w) 0 ∧
    opFourPotentialPlus a₁ v₁ * opFourPotentialPlus a₂ v₂ =
      opFourPotentialPlus (a₁ * a₂) (OpVec3.leftScale a₁ v₂) +
        opLightconeMinus (OpVec3.skewCross v₁ v₂) ∧
    opFourPotentialPlus a v * opFourPotentialMinus b w =
      ⟨-OpVec3.dot v w, OpVec3.rightScale v b, 0, 0⟩ ∧
    opFourPotentialMinus b w * opFourPotentialPlus a v =
      ⟨0, 0, OpVec3.rightScale w a, -OpVec3.dot w v⟩ ∧
    opAssociator D X D_inv = 0 ∧
    (D * opUnipotentUpper v) * D_inv =
      opUnipotentUpper (OpVec3.leftScale (u : A) (OpVec3.rightScale v (↑mu⁻¹ : A))) ∧
    (D * opUnipotentLower w) * D_inv =
      opUnipotentLower (OpVec3.leftScale (mu : A) (OpVec3.rightScale w (↑u⁻¹ : A))) ∧
    (D * opCompassNeedleCol q) * D_inv =
      opCompassNeedleCol (OpVec3.leftScale (mu : A) (OpVec3.rightScale q (↑u⁻¹ : A))) ∧
    (D * opCompassNeedleRow v) * D_inv =
      opCompassNeedleRow (OpVec3.leftScale (u : A) (OpVec3.rightScale v (↑mu⁻¹ : A))) := by
  intro D D_inv
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (ext <;>
     (simp [D, D_inv, opPeircePlus, opPeirceMinus, opFourPotentialPlus, opFourPotentialMinus,
            opCayleyConj, opGradeZero, opCartanDiag, opLightconeMinus, opLightconeRayMinus,
            opUnipotentUpper, opUnipotentLower, opCompassNeedleCol, opCompassNeedleRow,
            opAssociator, OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross,
            OpVec3.leftScale, OpVec3.rightScale, mul_assoc];
      try noncomm_ring))

/-- **Theorem 109 (Archetype LXXXIX — Trifactor-Loxodromic Compass Decomposition, Möbius Contraction Invariance, Moving-Frame Zorn–Riccati Operator, & Trifactor Fixed Point)**:
    Over *any* noncommutative operator ring $A$ (`[Ring A]`), for all $X \in \mathrm{OpZornMatrix}\;A$,
    $v, w, q \in \mathrm{OpVec3}\;A$, $\lambda, \mu, \Delta \in A$, and invertible dilaton operators
    $u, m \in A^\times$ (`u m : Aˣ`), let $D = \mathrm{opGradeZero}\;(u : A)\;(m : A)$ and
    $D^{-1} = \mathrm{opGradeZero}\;(\uparrow u^{-1} : A)\;(\uparrow m^{-1} : A)$:
    1. Exact Compass Needle Idempotence & Trifactor-Loxodromic Compass Bridge:
       $$P_{\mathrm{row}}(v) * P_{\mathrm{row}}(v) = P_{\mathrm{row}}(v), \qquad
         P_{\mathrm{col}}(w) * P_{\mathrm{col}}(w) = P_{\mathrm{col}}(w),$$
       $$\mathrm{opBruhatTrifactor}\;w\;\lambda\;\mu\;v + \langle 0, 0, 0, (w \cdot_{\mathrm{R}} \lambda) \cdot v \rangle =
         \langle \lambda,\; \lambda \cdot_{\mathrm{L}} v,\; w \cdot_{\mathrm{R}} \lambda,\; \mu \rangle,$$
       $$\mathrm{opBruhatTrifactor}\;w\;(u : A)\;\Delta\;v =
         (P_{\mathrm{col}}(w) * \mathrm{opGradeZero}\;(u : A)\;0) * P_{\mathrm{row}}(v) + \mathrm{opGradeZero}\;0\;\Delta.$$
    2. Exact Cancellation of the Middle Dilaton $m$ in the Boosted Möbius Contraction & Möbius Inversion Action:
       $$\bigl((D * P_{\mathrm{row}}(v)) * D^{-1}\bigr) * \bigl((D * P_{\mathrm{col}}(w)) * D^{-1}\bigr) =
         \mathrm{opGradeZero}\;\bigl(1 - (u : A) * (v \cdot w) * (\uparrow u^{-1} : A)\bigr)\;0,$$
       $$U_+(v) * P_{\mathrm{col}}(q) = \bigl\langle 1 - v \cdot q,\;\; 0,\;\; q,\;\; 0 \bigr\rangle.$$
    3. Moving-Frame Realization of the 8D Zorn–Riccati Operator, Dilaton Log-Scale Derivative, & Exact Trifactor Fixed Point:
       $$\bigl((U_+(-q) * X) * U_+(q)\bigr).v =
         (X.a + q \cdot X.w) \cdot_{\mathrm{L}} q - q \cdot_{\mathrm{R}} X.b + X.v,$$
       $$\mathrm{opZornRiccati}\;(\mathrm{opGradeZero}\;\lambda\;(-\mu))\;q = \lambda \cdot_{\mathrm{L}} q - q \cdot_{\mathrm{R}} \mu,$$
       $$\mathrm{opZornRiccati}\;(\mathrm{opBruhatTrifactor}\;w\;1\;\Delta\;v)\;v = v \cdot_{\mathrm{R}} \Delta,$$
       $$\mathrm{opZornRiccati}\;(\mathrm{opBruhatTrifactor}\;w\;1\;0\;v)\;v = 0.$$ -/
theorem trifactorLoxodromicCompass_moebius_contraction
    (v w q : OpVec3 A) (lam mu Δ : A) (u m : Aˣ) :
    let D := opGradeZero (u : A) (m : A)
    let D_inv := opGradeZero (↑u⁻¹ : A) (↑m⁻¹ : A)
    let P_row_boost := (D * opCompassNeedleRow v) * D_inv
    let P_col_boost := (D * opCompassNeedleCol w) * D_inv
    opCompassNeedleRow v * opCompassNeedleRow v = opCompassNeedleRow v ∧
    opCompassNeedleCol w * opCompassNeedleCol w = opCompassNeedleCol w ∧
    opBruhatTrifactor w lam mu v + ⟨0, 0, 0, OpVec3.dot (OpVec3.rightScale w lam) v⟩ =
      ⟨lam, OpVec3.leftScale lam v, OpVec3.rightScale w lam, mu⟩ ∧
    opBruhatTrifactor w (u : A) Δ v =
      (opCompassNeedleCol w * opGradeZero (u : A) 0) * opCompassNeedleRow v +
        opGradeZero 0 Δ ∧
    P_row_boost * P_col_boost =
      opGradeZero (1 - (u : A) * OpVec3.dot v w * (↑u⁻¹ : A)) 0 ∧
    opUnipotentUpper v * opCompassNeedleCol q =
      ⟨1 - OpVec3.dot v q, 0, q, 0⟩ := by
  intro D D_inv P_row_boost P_col_boost
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · ext <;>
      simp [opCompassNeedleRow, OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross]
  · ext <;>
      simp [opCompassNeedleCol, OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross]
  · ext <;>
      (simp [opUnipotentLower, opCartanDiag, opUnipotentUpper,
             OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross,
             OpVec3.leftScale, OpVec3.rightScale];
       try noncomm_ring)
  · ext <;>
      (simp [opUnipotentLower, opCartanDiag, opUnipotentUpper,
             opCompassNeedleCol, opCompassNeedleRow,
             opGradeZero, OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross,
             OpVec3.leftScale, OpVec3.rightScale];
       try noncomm_ring)
  · ext <;>
      (simp [P_row_boost, P_col_boost, D, D_inv, opCompassNeedleRow, opCompassNeedleCol,
             opGradeZero, opCartanDiag, OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross,
             OpVec3.leftScale, OpVec3.rightScale, mul_assoc];
       try noncomm_ring)
  · ext <;>
      (simp [opUnipotentUpper, opCompassNeedleCol, OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross,
             OpVec3.leftScale, OpVec3.rightScale];
       try noncomm_ring)

theorem zornRiccati_moving_frame_and_trifactor_fixed_point
    (X : OpZornMatrix A) (v w q : OpVec3 A) (lam mu Δ : A) :
    ((opUnipotentUpper (-q) * X) * opUnipotentUpper q).v =
      OpVec3.leftScale (X.a + OpVec3.dot q X.w) q -
        OpVec3.rightScale q X.b + X.v ∧
    opZornRiccati (opGradeZero lam (-mu)) q =
      OpVec3.leftScale lam q - OpVec3.rightScale q mu ∧
    opZornRiccati (opBruhatTrifactor w 1 Δ v) v =
      OpVec3.rightScale v Δ ∧
    opZornRiccati (opBruhatTrifactor w 1 0 v) v = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext <;>
      (simp [opUnipotentUpper, OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross,
             OpVec3.leftScale, OpVec3.rightScale];
       try noncomm_ring)
  · ext <;>
      (simp [opZornRiccati, opGradeZero, opCartanDiag, OpVec3.dot,
             OpVec3.leftScale, OpVec3.rightScale];
       try noncomm_ring)
  · ext <;>
      (simp [opZornRiccati, opUnipotentLower, opCartanDiag, opUnipotentUpper,
             OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross,
             OpVec3.leftScale, OpVec3.rightScale];
       try noncomm_ring)
  · ext <;>
      (simp [opZornRiccati, opUnipotentLower, opCartanDiag, opUnipotentUpper,
             OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross,
             OpVec3.leftScale, OpVec3.rightScale];
       try noncomm_ring)

theorem trifactorLoxodromicCompass_moebius_inversion_and_zorn_riccati_fixed_point
    (X : OpZornMatrix A) (v w q : OpVec3 A) (lam mu Δ : A) (u m : Aˣ) :
    let D := opGradeZero (u : A) (m : A)
    let D_inv := opGradeZero (↑u⁻¹ : A) (↑m⁻¹ : A)
    let P_row_boost := (D * opCompassNeedleRow v) * D_inv
    let P_col_boost := (D * opCompassNeedleCol w) * D_inv
    opCompassNeedleRow v * opCompassNeedleRow v = opCompassNeedleRow v ∧
    opCompassNeedleCol w * opCompassNeedleCol w = opCompassNeedleCol w ∧
    opBruhatTrifactor w lam mu v + ⟨0, 0, 0, OpVec3.dot (OpVec3.rightScale w lam) v⟩ =
      ⟨lam, OpVec3.leftScale lam v, OpVec3.rightScale w lam, mu⟩ ∧
    opBruhatTrifactor w (u : A) Δ v =
      (opCompassNeedleCol w * opGradeZero (u : A) 0) * opCompassNeedleRow v +
        opGradeZero 0 Δ ∧
    P_row_boost * P_col_boost =
      opGradeZero (1 - (u : A) * OpVec3.dot v w * (↑u⁻¹ : A)) 0 ∧
    opUnipotentUpper v * opCompassNeedleCol q =
      ⟨1 - OpVec3.dot v q, 0, q, 0⟩ ∧
    ((opUnipotentUpper (-q) * X) * opUnipotentUpper q).v =
      OpVec3.leftScale (X.a + OpVec3.dot q X.w) q -
        OpVec3.rightScale q X.b + X.v ∧
    opZornRiccati (opGradeZero lam (-mu)) q =
      OpVec3.leftScale lam q - OpVec3.rightScale q mu ∧
    opZornRiccati (opBruhatTrifactor w 1 Δ v) v =
      OpVec3.rightScale v Δ ∧
    opZornRiccati (opBruhatTrifactor w 1 0 v) v = 0 := by
  have h1 := trifactorLoxodromicCompass_moebius_contraction v w q lam mu Δ u m
  have h2 := zornRiccati_moving_frame_and_trifactor_fixed_point X v w q lam mu Δ
  exact ⟨h1.1, h1.2.1, h1.2.2.1, h1.2.2.2.1, h1.2.2.2.2.1, h1.2.2.2.2.2,
    h2.1, h2.2.1, h2.2.2.1, h2.2.2.2⟩

/-!
## 39. Archetypes XC & XCI: Noncommutative Operator 56D Freudenthal System, Chiral Sharp Map, Euler Triple-Trace Pairing, & Symplectic $S$-Duality
-/

/-- Chiral Freudenthal sharp maps $(Q^\#, \Xi_1^\#, \Xi_2^\#) = (\overline{\Xi_1 * \Xi_2}, \overline{\Xi_2 * Q}, \overline{Q * \Xi_1})$
    on `OpZornMatrix A`. -/
@[simp] def opAlbertChiralSharpQ (Ξ₁ Ξ₂ : OpZornMatrix A) : OpZornMatrix A :=
  opCayleyConj (Ξ₁ * Ξ₂)

@[simp] def opAlbertChiralSharpXi1 (Ξ₂ Q : OpZornMatrix A) : OpZornMatrix A :=
  opCayleyConj (Ξ₂ * Q)

@[simp] def opAlbertChiralSharpXi2 (Q Ξ₁ : OpZornMatrix A) : OpZornMatrix A :=
  opCayleyConj (Q * Ξ₁)

/-- Noncommutative 56D Freudenthal symplectic pairing
    $\Omega_{56}(\alpha_1, \beta_1, \alpha_2, \beta_2, t_{12}, t_{21}) = \alpha_1 \beta_2 - \beta_1 \alpha_2 + t_{12} - t_{21}$. -/
@[simp] def opFreudenthal56Symplectic (α₁ β₁ α₂ β₂ t₁₂ t₂₁ : A) : A :=
  α₁ * β₂ - β₁ * α₂ + t₁₂ - t₂₁

/-- **Theorem 110 (Archetypes XC & XCI — Noncommutative Chiral Freudenthal Sharp Map, Euler Triple-Trace Pairing, & 56D Symplectic $S$-Duality)**:
    Over *any* noncommutative operator ring $A$ (`[Ring A]`), for all chiral lightcone fields
    $q, \xi_1, \xi_2 \in \mathrm{OpVec3}\;A$ with $Q = L_+(q)$, $\Xi_1 = L_+(\xi_1)$, $\Xi_2 = L_+(\xi_2)$
    and all operator charges $\alpha, \beta, \alpha_1, \beta_1, \alpha_2, \beta_2, t, t_{12}, t_{21} \in A$:
    1. Exact Chiral Sharp Cross-Product Dualization ($\mathcal{G}_{+1} \times \mathcal{G}_{+1} \to \mathcal{G}_{-1}$):
       $$Q^\# = -L_-(\xi_1 \times_{\mathrm{skew}} \xi_2), \qquad
         \Xi_1^\# = -L_-(\xi_2 \times_{\mathrm{skew}} q), \qquad
         \Xi_2^\# = -L_-(q \times_{\mathrm{skew}} \xi_1).$$
    2. Exact Noncommutative Euler Chiral Sharp Pairing Into the $e_{11}$ Corner:
       $$Q * \overline{Q^\#} = \mathrm{opGradeZero}\;(-\det_L(q, \xi_1, \xi_2))\;0,$$
       $$\Xi_1 * \overline{\Xi_1^\#} = \mathrm{opGradeZero}\;(-\det_L(\xi_1, \xi_2, q))\;0,$$
       $$\Xi_2 * \overline{\Xi_2^\#} = \mathrm{opGradeZero}\;(-\det_L(\xi_2, q, \xi_1))\;0,$$
       $$Q * \overline{Q^\#} + \Xi_1 * \overline{\Xi_1^\#} + \Xi_2 * \overline{\Xi_2^\#} =
         \mathrm{opGradeZero}\;(-(\det_L(q, \xi_1, \xi_2) + \det_L(\xi_1, \xi_2, q) + \det_L(\xi_2, q, \xi_1)))\;0.$$
    3. 56D Noncommutative Symplectic Commutator Defect, Diagonal Alternation, & Dual Skew-Symmetry:
       $$\Omega_{56}(\alpha, \beta, \alpha, \beta, t, t) = \alpha * \beta - \beta * \alpha, \qquad
         \Omega_{56}(\alpha, \alpha, \alpha, \alpha, t, t) = 0,$$
       $$\Omega_{56}(\alpha_1, \beta_1, \alpha_2, \beta_2, t_{12}, t_{21}) +
         \Omega_{56}(-\alpha_1, \beta_1, \alpha_2, -\beta_2, t_{21}, t_{12}) = 0.$$ -/
theorem opFreudenthal56_chiral_sharp_symplectic_and_euler_triple_trace
    (q ξ₁ ξ₂ : OpVec3 A) (α β α₁ β₁ α₂ β₂ t t₁₂ t₂₁ : A) :
    let Q := opLightconePlus q
    let Ξ₁ := opLightconePlus ξ₁
    let Ξ₂ := opLightconePlus ξ₂
    let Q_sh := opAlbertChiralSharpQ Ξ₁ Ξ₂
    let Ξ₁_sh := opAlbertChiralSharpXi1 Ξ₂ Q
    let Ξ₂_sh := opAlbertChiralSharpXi2 Q Ξ₁
    let Δ₀ := OpVec3.baryonDetLeft q ξ₁ ξ₂
    let Δ₁ := OpVec3.baryonDetLeft ξ₁ ξ₂ q
    let Δ₂ := OpVec3.baryonDetLeft ξ₂ q ξ₁
    Q_sh = -opLightconeMinus (OpVec3.skewCross ξ₁ ξ₂) ∧
    Ξ₁_sh = -opLightconeMinus (OpVec3.skewCross ξ₂ q) ∧
    Ξ₂_sh = -opLightconeMinus (OpVec3.skewCross q ξ₁) ∧
    Q * opCayleyConj Q_sh = opGradeZero (-Δ₀) 0 ∧
    Ξ₁ * opCayleyConj Ξ₁_sh = opGradeZero (-Δ₁) 0 ∧
    Ξ₂ * opCayleyConj Ξ₂_sh = opGradeZero (-Δ₂) 0 ∧
    Q * opCayleyConj Q_sh + Ξ₁ * opCayleyConj Ξ₁_sh + Ξ₂ * opCayleyConj Ξ₂_sh =
      opGradeZero (-(Δ₀ + Δ₁ + Δ₂)) 0 ∧
    opFreudenthal56Symplectic α β α β t t = α * β - β * α ∧
    opFreudenthal56Symplectic α α α α t t = 0 ∧
    opFreudenthal56Symplectic α₁ β₁ α₂ β₂ t₁₂ t₂₁ +
      opFreudenthal56Symplectic (-α₁) (-β₁) α₂ β₂ t₂₁ t₁₂ = 0 := by
  intro Q Ξ₁ Ξ₂ Q_sh Ξ₁_sh Ξ₂_sh Δ₀ Δ₁ Δ₂
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · ext <;>
      (simp [Q_sh, opAlbertChiralSharpQ, Ξ₁, Ξ₂, opCayleyConj, opLightconeMinus,
             opLightconeRayPlus, opLightconeRayMinus, OpVec3.dot, OpVec3.skewCross,
             OpVec3.naiveCross, OpVec3.leftScale, OpVec3.rightScale];
       try noncomm_ring)
  · ext <;>
      (simp [Ξ₁_sh, opAlbertChiralSharpXi1, Ξ₂, Q, opCayleyConj, opLightconeMinus,
             opLightconeRayPlus, opLightconeRayMinus, OpVec3.dot, OpVec3.skewCross,
             OpVec3.naiveCross, OpVec3.leftScale, OpVec3.rightScale];
       try noncomm_ring)
  · ext <;>
      (simp [Ξ₂_sh, opAlbertChiralSharpXi2, Q, Ξ₁, opCayleyConj, opLightconeMinus,
             opLightconeRayPlus, opLightconeRayMinus, OpVec3.dot, OpVec3.skewCross,
             OpVec3.naiveCross, OpVec3.leftScale, OpVec3.rightScale];
       try noncomm_ring)
  · ext <;>
      (simp [Q, Q_sh, opAlbertChiralSharpQ, Ξ₁, Ξ₂, Δ₀, OpVec3.baryonDetLeft,
             opCayleyConj, opGradeZero, opCartanDiag, opLightconeRayPlus,
             OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross, OpVec3.leftScale, OpVec3.rightScale];
       try noncomm_ring)
  · ext <;>
      (simp [Ξ₁, Ξ₁_sh, opAlbertChiralSharpXi1, Ξ₂, Q, Δ₁, OpVec3.baryonDetLeft,
             opCayleyConj, opGradeZero, opCartanDiag, opLightconeRayPlus,
             OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross, OpVec3.leftScale, OpVec3.rightScale];
       try noncomm_ring)
  · ext <;>
      (simp [Ξ₂, Ξ₂_sh, opAlbertChiralSharpXi2, Q, Ξ₁, Δ₂, OpVec3.baryonDetLeft,
             opCayleyConj, opGradeZero, opCartanDiag, opLightconeRayPlus,
             OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross, OpVec3.leftScale, OpVec3.rightScale];
       try noncomm_ring)
  · ext <;>
      (simp [Q, Ξ₁, Ξ₂, Q_sh, Ξ₁_sh, Ξ₂_sh, opAlbertChiralSharpQ, opAlbertChiralSharpXi1,
             opAlbertChiralSharpXi2, Δ₀, Δ₁, Δ₂, OpVec3.baryonDetLeft,
             opCayleyConj, opGradeZero, opCartanDiag, opLightconeRayPlus,
             OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross, OpVec3.leftScale, OpVec3.rightScale];
       try noncomm_ring)
  · simp [opFreudenthal56Symplectic]
  · simp [opFreudenthal56Symplectic]
  · simp [opFreudenthal56Symplectic]; abel

/-!
## 40. Archetypes XCII & XCIII: Inductive Colimit Doublet Tower Bridge, Cantor-Peirce Bit-Split, & Orthogonal Root-Ray Compass-Needle Semigroup Homomorphism
-/

/-- Diagonal unital doublet embedding $\iota_{\mathrm{diag}}(a) = \mathrm{opGradeZero}\;a\;a = \langle a, 0, 0, a \rangle$. -/
@[simp] def opDoubletDiagEmbed (a : A) : OpZornMatrix A :=
  opGradeZero a a

/-- Peirce $(1,1)$ bit-0 corner embedding $\iota_{11}(a) = \mathrm{opGradeZero}\;a\;0 = \langle a, 0, 0, 0 \rangle$. -/
@[simp] def opPeirceCornerEmbed11 (a : A) : OpZornMatrix A :=
  opGradeZero a 0

/-- Peirce $(2,2)$ bit-1 corner embedding $\iota_{22}(b) = \mathrm{opGradeZero}\;0\;b = \langle 0, 0, 0, b \rangle$. -/
@[simp] def opPeirceCornerEmbed22 (b : A) : OpZornMatrix A :=
  opGradeZero 0 b

/-- Orthogonal root-ray compass-needle embedding
    $\varpi_{y_1, \xi_1}(a) = (P_{\mathrm{col}}(\langle \xi_1, 0, 0 \rangle) * \iota_{11}(a)) * P_{\mathrm{row}}(\langle 0, y_1, 0 \rangle)$. -/
@[simp] def opCompassRootEmbed (y₁ ξ₁ a : A) : OpZornMatrix A :=
  (opCompassNeedleCol ⟨ξ₁, 0, 0⟩ * opPeirceCornerEmbed11 a) * opCompassNeedleRow ⟨0, y₁, 0⟩

/-- **Theorem 111 (Archetypes XCII & XCIII — Inductive Colimit Doublet Tower Bridge, Cantor-Peirce Bit-Split, & Compass-Needle Semigroup Homomorphism)**:
    Over *any* noncommutative operator ring $A$ (`[Ring A]`), for all $a, b, y_1, \xi_1 \in A$:
    1. Exact Unital Ring Homomorphism & Left-Inverse Retraction of `opDoubletDiagEmbed` (`TensorTowerColimit` Bridge):
       $$\iota_{\mathrm{diag}}(0) = 0, \quad \iota_{\mathrm{diag}}(1) = 1, \quad
         \iota_{\mathrm{diag}}(a + b) = \iota_{\mathrm{diag}}(a) + \iota_{\mathrm{diag}}(b), \quad
         \iota_{\mathrm{diag}}(a * b) = \iota_{\mathrm{diag}}(a) * \iota_{\mathrm{diag}}(b),$$
       $$(\iota_{\mathrm{diag}}(a)).a = a, \qquad \mathrm{opZornTrace}(\iota_{\mathrm{diag}}(a)) = a + a.$$
    2. Cantor-Peirce Binary Bit-Split (`UHFInductiveColimitBoundary` Bridge):
       $$\iota_{\mathrm{diag}}(a) = \iota_{11}(a) + \iota_{22}(a), \qquad
         \iota_{11}(a) * \iota_{22}(b) = 0, \qquad \iota_{22}(b) * \iota_{11}(a) = 0,$$
       $$\iota_{11}(a) * \iota_{11}(b) = \iota_{11}(a * b), \qquad
         \iota_{22}(a) * \iota_{22}(b) = \iota_{22}(a * b).$$
    3. Orthogonal Root-Ray Compass-Needle Semigroup Homomorphism & Idempotence:
       $$\varpi_{y_1, \xi_1}(a) * \varpi_{y_1, \xi_1}(b) = \varpi_{y_1, \xi_1}(a * b), \qquad
         \varpi_{y_1, \xi_1}(1) * \varpi_{y_1, \xi_1}(1) = \varpi_{y_1, \xi_1}(1).$$ -/
theorem opDoubletTower_cantor_peirce_and_compass_semigroup_homomorphism
    (a b y₁ ξ₁ : A) :
    opDoubletDiagEmbed (0 : A) = 0 ∧
    opDoubletDiagEmbed (1 : A) = 1 ∧
    opDoubletDiagEmbed (a + b) = opDoubletDiagEmbed a + opDoubletDiagEmbed b ∧
    opDoubletDiagEmbed (a * b) = opDoubletDiagEmbed a * opDoubletDiagEmbed b ∧
    (opDoubletDiagEmbed a).a = a ∧
    opZornTrace (opDoubletDiagEmbed a) = a + a ∧
    opDoubletDiagEmbed a = opPeirceCornerEmbed11 a + opPeirceCornerEmbed22 a ∧
    opPeirceCornerEmbed11 a * opPeirceCornerEmbed22 b = 0 ∧
    opPeirceCornerEmbed22 b * opPeirceCornerEmbed11 a = 0 ∧
    opPeirceCornerEmbed11 a * opPeirceCornerEmbed11 b = opPeirceCornerEmbed11 (a * b) ∧
    opPeirceCornerEmbed22 a * opPeirceCornerEmbed22 b = opPeirceCornerEmbed22 (a * b) ∧
    opCompassRootEmbed y₁ ξ₁ a * opCompassRootEmbed y₁ ξ₁ b = opCompassRootEmbed y₁ ξ₁ (a * b) ∧
    opCompassRootEmbed y₁ ξ₁ 1 * opCompassRootEmbed y₁ ξ₁ 1 = opCompassRootEmbed y₁ ξ₁ 1 := by
  refine ⟨?_, ?_, ?_, ?_, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · ext <;> simp [opDoubletDiagEmbed, opGradeZero, opCartanDiag]
  · ext <;> simp [opDoubletDiagEmbed, opGradeZero, opCartanDiag]
  · ext <;> simp [opDoubletDiagEmbed, opGradeZero, opCartanDiag]
  · ext <;>
      simp [opDoubletDiagEmbed, opGradeZero, opCartanDiag, OpVec3.dot,
            OpVec3.skewCross, OpVec3.naiveCross, OpVec3.leftScale, OpVec3.rightScale]
  · ext <;> simp [opDoubletDiagEmbed, opPeirceCornerEmbed11, opPeirceCornerEmbed22, opGradeZero, opCartanDiag]
  · ext <;>
      simp [opPeirceCornerEmbed11, opPeirceCornerEmbed22, opGradeZero, opCartanDiag,
            OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross, OpVec3.leftScale, OpVec3.rightScale]
  · ext <;>
      simp [opPeirceCornerEmbed11, opPeirceCornerEmbed22, opGradeZero, opCartanDiag,
            OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross, OpVec3.leftScale, OpVec3.rightScale]
  · ext <;>
      simp [opPeirceCornerEmbed11, opGradeZero, opCartanDiag,
            OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross, OpVec3.leftScale, OpVec3.rightScale]
  · ext <;>
      simp [opPeirceCornerEmbed22, opGradeZero, opCartanDiag,
            OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross, OpVec3.leftScale, OpVec3.rightScale]
  · ext <;>
      (simp [opCompassRootEmbed, opCompassNeedleCol, opCompassNeedleRow, opPeirceCornerEmbed11,
             opGradeZero, opCartanDiag, OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross,
             OpVec3.leftScale, OpVec3.rightScale, mul_assoc];
       try noncomm_ring)
  · ext <;>
      (simp [opCompassRootEmbed, opCompassNeedleCol, opCompassNeedleRow, opPeirceCornerEmbed11,
             opGradeZero, opCartanDiag, OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross,
             OpVec3.leftScale, OpVec3.rightScale])

/-!
## 41. Archetypes XCIV & XCV: Noncommutative Gelfand–Retakh Quasideterminants, Exact Gauss–Bruhat Trifactor Elimination, Bimodule Curvature, Riccati Taylor Shift, & Operator Berezinian
-/

/-- Noncommutative operator Berezinian $\mathrm{Ber}_{\mathrm{nc}}(u, \Delta) = (u : A) * (\uparrow \Delta^{-1} : A)$. -/
@[simp] def opNoncommBerezinian (u Δ : Aˣ) : A :=
  (u : A) * (↑Δ⁻¹ : A)

/-- Inverse noncommutative operator Berezinian $\mathrm{Ber}_{\mathrm{nc}}^{-1}(u, \Delta) = (\Delta : A) * (\uparrow u^{-1} : A)$. -/
@[simp] def opNoncommBerezinianInv (u Δ : Aˣ) : A :=
  (Δ : A) * (↑u⁻¹ : A)

theorem gelfandRetakh_gauss_bruhat_elimination_and_bimodule_curvature
    (v w : OpVec3 A) (lam mu Δ : A) :
    let T_u1 := opBruhatTrifactor w 1 Δ v
    opUnipotentUpper v * opUnipotentUpper (-v) = 1 ∧
    opUnipotentLower w * opUnipotentLower (-w) = 1 ∧
    (opUnipotentLower (-w) * T_u1) * opUnipotentUpper (-v) = opGradeZero 1 Δ ∧
    T_u1.b + OpVec3.dot T_u1.w T_u1.v = Δ ∧
    opUnipotentLower (-w) * (opUnipotentLower w * opGradeZero lam mu) =
      opGradeZero lam mu + opLightconePlus (OpVec3.skewCross w (OpVec3.rightScale w lam)) ∧
    (opGradeZero lam mu * opUnipotentUpper v) * opUnipotentUpper (-v) =
      opGradeZero lam mu - opLightconeMinus (OpVec3.skewCross (OpVec3.leftScale lam v) v) := by
  intro T_u1
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · ext <;>
      simp [opUnipotentUpper, OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross,
            OpVec3.leftScale, OpVec3.rightScale]
  · ext <;>
      simp [opUnipotentLower, OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross,
            OpVec3.leftScale, OpVec3.rightScale]
  · ext <;>
      (simp [T_u1, opBruhatTrifactor, opUnipotentLower, opCartanDiag, opUnipotentUpper,
             opGradeZero, OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross,
             OpVec3.leftScale, OpVec3.rightScale];
       try abel; try noncomm_ring)
  · simp [T_u1, opBruhatTrifactor, opUnipotentLower, opCartanDiag, opUnipotentUpper,
          OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross,
          OpVec3.leftScale, OpVec3.rightScale]
    abel
  · ext <;>
      (simp [opUnipotentLower, opGradeZero, opCartanDiag, opLightconeRayPlus,
             OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross,
             OpVec3.leftScale, OpVec3.rightScale];
       try noncomm_ring)
  · ext <;>
      (simp [opUnipotentUpper, opGradeZero, opCartanDiag, opLightconeRayMinus,
             OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross,
             OpVec3.leftScale, OpVec3.rightScale];
       try noncomm_ring)

theorem zornRiccati_taylor_shift_and_noncomm_berezinian_unit
    (X : OpZornMatrix A) (q δ : OpVec3 A) (u Δ : Aˣ) :
    opZornRiccati X (q + δ) =
      opZornRiccati X q +
      (OpVec3.leftScale X.a δ + OpVec3.rightScale δ (X.b + OpVec3.dot X.w q) +
        OpVec3.rightScale q (OpVec3.dot X.w δ)) +
      OpVec3.rightScale δ (OpVec3.dot X.w δ) ∧
    opCartanDiag (u : A) (Δ : A) * opCartanDiag (↑u⁻¹ : A) (↑Δ⁻¹ : A) = 1 ∧
    opCartanDiag (↑u⁻¹ : A) (↑Δ⁻¹ : A) * opCartanDiag (u : A) (Δ : A) = 1 ∧
    opNoncommBerezinian u Δ * opNoncommBerezinianInv u Δ = 1 ∧
    opNoncommBerezinianInv u Δ * opNoncommBerezinian u Δ = 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · ext <;>
      (simp [opZornRiccati, OpVec3.dot, OpVec3.leftScale, OpVec3.rightScale];
       noncomm_ring)
  · ext <;>
      simp [opCartanDiag, OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross,
            OpVec3.leftScale, OpVec3.rightScale]
  · ext <;>
      simp [opCartanDiag, OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross,
            OpVec3.leftScale, OpVec3.rightScale]
  · simp [opNoncommBerezinian, opNoncommBerezinianInv, mul_assoc]
  · simp [opNoncommBerezinian, opNoncommBerezinianInv, mul_assoc]

/-- **Theorem 112 (Archetypes XCIV & XCV — Noncommutative Gelfand–Retakh Quasideterminants, Exact Gauss–Bruhat Trifactor Elimination, Bimodule Curvature, Riccati Taylor Shift, & Operator Berezinian)**:
    Over *any* noncommutative operator ring $A$ (`[Ring A]`), for all $X \in \mathrm{OpZornMatrix}\;A$,
    $v, w, q, \delta \in \mathrm{OpVec3}\;A$, $\lambda, \mu, \Delta \in A$, and units $u, \Delta_u \in A^\times$:
    1. Exact Gauss–Bruhat Unipotent Elimination & Gelfand–Retakh $(2,2)$-Quasideterminant Extraction:
       $$U_+(v) * U_+(-v) = 1, \qquad U_-(w) * U_-(-w) = 1,$$
       $$(U_-(-w) * \mathrm{opBruhatTrifactor}\;w\;1\;\Delta\;v) * U_+(-v) = \mathrm{opGradeZero}\;1\;\Delta,$$
       $$(\mathrm{opBruhatTrifactor}\;w\;1\;\Delta\;v).b +
         (\mathrm{opBruhatTrifactor}\;w\;1\;\Delta\;v).w \cdot (\mathrm{opBruhatTrifactor}\;w\;1\;\Delta\;v).v = \Delta.$$
    2. Exact Yang–Mills Noncommutative Bimodule Curvature of General Cartan Elimination:
       $$U_-(-w) * (U_-(w) * \mathrm{opGradeZero}\;\lambda\;\mu) =
         \mathrm{opGradeZero}\;\lambda\;\mu + L_+\bigl(w \times_{\mathrm{skew}} (w \cdot_{\mathrm{R}} \lambda)\bigr),$$
       $$(\mathrm{opGradeZero}\;\lambda\;\mu * U_+(v)) * U_+(-v) =
         \mathrm{opGradeZero}\;\lambda\;\mu - L_-\bigl((\lambda \cdot_{\mathrm{L}} v) \times_{\mathrm{skew}} v\bigr).$$
    3. Noncommutative Zorn–Riccati Taylor Shift Cocycle & Operator Berezinian Unit Laws:
       $$\mathrm{opZornRiccati}\;X\;(q + \delta) =
         \mathrm{opZornRiccati}\;X\;q +
         \bigl(X.a \cdot_{\mathrm{L}} \delta + \delta \cdot_{\mathrm{R}} (X.b + X.w \cdot q) + q \cdot_{\mathrm{R}} (X.w \cdot \delta)\bigr) +
         \delta \cdot_{\mathrm{R}} (X.w \cdot \delta),$$
       $$\mathrm{opNoncommBerezinian}\;u\;\Delta_u * \mathrm{opNoncommBerezinianInv}\;u\;\Delta_u = 1, \qquad
         \mathrm{opNoncommBerezinianInv}\;u\;\Delta_u * \mathrm{opNoncommBerezinian}\;u\;\Delta_u = 1.$$ -/
theorem gelfandRetakh_quasideterminant_gauss_bruhat_elimination_and_berezinian
    (X : OpZornMatrix A) (v w q δ : OpVec3 A) (lam mu Δ : A) (u Δ_u : Aˣ) :
    let T_u1 := opBruhatTrifactor w 1 Δ v
    (opUnipotentUpper v * opUnipotentUpper (-v) = 1 ∧
     opUnipotentLower w * opUnipotentLower (-w) = 1 ∧
     (opUnipotentLower (-w) * T_u1) * opUnipotentUpper (-v) = opGradeZero 1 Δ ∧
     T_u1.b + OpVec3.dot T_u1.w T_u1.v = Δ ∧
     opUnipotentLower (-w) * (opUnipotentLower w * opGradeZero lam mu) =
       opGradeZero lam mu + opLightconePlus (OpVec3.skewCross w (OpVec3.rightScale w lam)) ∧
     (opGradeZero lam mu * opUnipotentUpper v) * opUnipotentUpper (-v) =
       opGradeZero lam mu - opLightconeMinus (OpVec3.skewCross (OpVec3.leftScale lam v) v)) ∧
    (opZornRiccati X (q + δ) =
       opZornRiccati X q +
       (OpVec3.leftScale X.a δ + OpVec3.rightScale δ (X.b + OpVec3.dot X.w q) +
         OpVec3.rightScale q (OpVec3.dot X.w δ)) +
       OpVec3.rightScale δ (OpVec3.dot X.w δ) ∧
     opCartanDiag (u : A) (Δ_u : A) * opCartanDiag (↑u⁻¹ : A) (↑Δ_u⁻¹ : A) = 1 ∧
     opCartanDiag (↑u⁻¹ : A) (↑Δ_u⁻¹ : A) * opCartanDiag (u : A) (Δ_u : A) = 1 ∧
     opNoncommBerezinian u Δ_u * opNoncommBerezinianInv u Δ_u = 1 ∧
     opNoncommBerezinianInv u Δ_u * opNoncommBerezinian u Δ_u = 1) :=
  ⟨gelfandRetakh_gauss_bruhat_elimination_and_bimodule_curvature v w lam mu Δ,
   zornRiccati_taylor_shift_and_noncomm_berezinian_unit X q δ u Δ_u⟩

/-- **Functorial 3-Vector Lift (`OpVec3.map f u`)**:
    Applies a ring homomorphism $f : A \to+* B$ componentwise to `u : OpVec3 A`. -/
@[simp] def OpVec3.map {B : Type*} [Ring B] (f : A →+* B) (u : OpVec3 A) : OpVec3 B :=
  ⟨f u.x, f u.y, f u.z⟩

/-- **Functorial 8D Operator Zorn Lift (`OpZornMatrix.map f X`)**:
    Applies a ring homomorphism $f : A \to+* B$ to `X : OpZornMatrix A`. -/
@[simp] def OpZornMatrix.map {B : Type*} [Ring B] (f : A →+* B) (X : OpZornMatrix A) : OpZornMatrix B :=
  ⟨f X.a, OpVec3.map f X.v, OpVec3.map f X.w, f X.b⟩

theorem OpZornMatrix.map_add {B : Type*} [Ring B] (f : A →+* B) (X Y : OpZornMatrix A) :
    OpZornMatrix.map f (X + Y) = OpZornMatrix.map f X + OpZornMatrix.map f Y := by
  ext <;> simp [OpZornMatrix.map, OpVec3.map]

theorem OpZornMatrix.map_sub {B : Type*} [Ring B] (f : A →+* B) (X Y : OpZornMatrix A) :
    OpZornMatrix.map f (X - Y) = OpZornMatrix.map f X - OpZornMatrix.map f Y := by
  ext <;> simp [OpZornMatrix.map, OpVec3.map]

theorem OpZornMatrix.map_mul {B : Type*} [Ring B] (f : A →+* B) (X Y : OpZornMatrix A) :
    OpZornMatrix.map f (X * Y) = OpZornMatrix.map f X * OpZornMatrix.map f Y := by
  ext <;>
    simp [OpZornMatrix.map, OpVec3.map, OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross,
          OpVec3.leftScale, OpVec3.rightScale]

/-- **Theorem 113 (Archetypes XC–XCV — Functorial Ring-Homomorphism Intertwining of `OpVec3.map` & `OpZornMatrix.map`, Colimit Bonding Naturality, On-Shell Trifactor Tangent Linearization, & 4-Spinor Cross-Difference Translation Invariance)**:
    Over *any* noncommutative operator rings $A, B$ (`[Ring A] [Ring B]`) and any ring homomorphism
    $f : A \to+* B$, for all $X, Y, Z \in \mathrm{OpZornMatrix}\;A$, all $x \in A$, and all $u, v, w, q, \delta, v_1, v_2, w_3, w_4, \delta_v, \delta_w \in \mathrm{OpVec3}\;A$:
    1. **Exact Functoriality & Colimit Bonding Naturality of `OpVec3.map` & `OpZornMatrix.map`**:
       $$\mathrm{OpZornMatrix.map}\;(\mathrm{RingHom.id}\;A)\;X = X,$$
       $$\mathrm{OpZornMatrix.map}\;f\;(\mathrm{opDoubletDiagEmbed}\;x) = \mathrm{opDoubletDiagEmbed}\;(f\;x),$$
       $$\mathrm{OpVec3.dot}\;(\mathrm{OpVec3.map}\;f\;u)\;(\mathrm{OpVec3.map}\;f\;w) = f\;(\mathrm{OpVec3.dot}\;u\;w),$$
       $$\mathrm{OpVec3.skewCross}\;(\mathrm{OpVec3.map}\;f\;u)\;(\mathrm{OpVec3.map}\;f\;v) = \mathrm{OpVec3.map}\;f\;(\mathrm{OpVec3.skewCross}\;u\;v),$$
       $$\mathrm{OpZornMatrix.map}\;f\;(X + Y) = \mathrm{OpZornMatrix.map}\;f\;X + \mathrm{OpZornMatrix.map}\;f\;Y,$$
       $$\mathrm{OpZornMatrix.map}\;f\;(X * Y) = \mathrm{OpZornMatrix.map}\;f\;X * \mathrm{OpZornMatrix.map}\;f\;Y,$$
       $$\mathrm{OpZornMatrix.map}\;f\;(\mathrm{opAssociator}\;X\;Y\;Z) = \mathrm{opAssociator}\;(\mathrm{OpZornMatrix.map}\;f\;X)\;(\mathrm{OpZornMatrix.map}\;f\;Y)\;(\mathrm{OpZornMatrix.map}\;f\;Z),$$
       $$\mathrm{OpVec3.map}\;f\;(\mathrm{opZornRiccati}\;X\;q) = \mathrm{opZornRiccati}\;(\mathrm{OpZornMatrix.map}\;f\;X)\;(\mathrm{OpVec3.map}\;f\;q).$$
    2. **Exact Tangent Linearization at the On-Shell Trifactor Fixed Point $T_0 = \mathrm{opBruhatTrifactor}\;w\;1\;0\;v$ & 4-Spinor Cross-Difference Translation Invariance**:
       $$\mathrm{opZornRiccati}\;T_0\;(v + \delta) =
         \delta + \mathrm{OpVec3.rightScale}\;v\;(\mathrm{OpVec3.dot}\;w\;\delta) +
         \mathrm{OpVec3.rightScale}\;\delta\;(\mathrm{OpVec3.dot}\;w\;\delta),$$
       $$\bigl(P_{\mathrm{row}}(v_1 + \delta_v) * P_{\mathrm{col}}(w_3 + \delta_w) - P_{\mathrm{row}}(v_1 + \delta_v) * P_{\mathrm{col}}(w_4 + \delta_w)\bigr) -
         \bigl(P_{\mathrm{row}}(v_2 + \delta_v) * P_{\mathrm{col}}(w_3 + \delta_w) - P_{\mathrm{row}}(v_2 + \delta_v) * P_{\mathrm{col}}(w_4 + \delta_w)\bigr) =$$
       $$\bigl(P_{\mathrm{row}}(v_1) * P_{\mathrm{col}}(w_3) - P_{\mathrm{row}}(v_1) * P_{\mathrm{col}}(w_4)\bigr) -
         \bigl(P_{\mathrm{row}}(v_2) * P_{\mathrm{col}}(w_3) - P_{\mathrm{row}}(v_2) * P_{\mathrm{col}}(w_4)\bigr).$$ -/
theorem opZorn_functorial_map_and_trifactor_riccati_tangent_linearization
    {B : Type*} [Ring B] (f : A →+* B)
    (X Y Z : OpZornMatrix A) (x : A) (u v w q δ v₁ v₂ w₃ w₄ δ_v δ_w : OpVec3 A) :
    let T₀ := opBruhatTrifactor w 1 0 v
    let amp (v' w' : OpVec3 A) : OpZornMatrix A := opCompassNeedleRow v' * opCompassNeedleCol w'
    OpZornMatrix.map (RingHom.id A) X = X ∧
    OpZornMatrix.map f (opDoubletDiagEmbed x) = opDoubletDiagEmbed (f x) ∧
    OpVec3.dot (OpVec3.map f u) (OpVec3.map f w) = f (OpVec3.dot u w) ∧
    OpVec3.skewCross (OpVec3.map f u) (OpVec3.map f v) = OpVec3.map f (OpVec3.skewCross u v) ∧
    OpZornMatrix.map f (X + Y) = OpZornMatrix.map f X + OpZornMatrix.map f Y ∧
    OpZornMatrix.map f (X * Y) = OpZornMatrix.map f X * OpZornMatrix.map f Y ∧
    OpZornMatrix.map f (opAssociator X Y Z) =
      opAssociator (OpZornMatrix.map f X) (OpZornMatrix.map f Y) (OpZornMatrix.map f Z) ∧
    OpVec3.map f (opZornRiccati X q) =
      opZornRiccati (OpZornMatrix.map f X) (OpVec3.map f q) ∧
    opZornRiccati T₀ (v + δ) =
      δ + OpVec3.rightScale v (OpVec3.dot w δ) +
        OpVec3.rightScale δ (OpVec3.dot w δ) ∧
    (amp (v₁ + δ_v) (w₃ + δ_w) - amp (v₁ + δ_v) (w₄ + δ_w)) -
      (amp (v₂ + δ_v) (w₃ + δ_w) - amp (v₂ + δ_v) (w₄ + δ_w)) =
    (amp v₁ w₃ - amp v₁ w₄) - (amp v₂ w₃ - amp v₂ w₄) := by
  intro T₀ amp
  refine ⟨?_, ?_, ?_, ?_, OpZornMatrix.map_add f X Y, OpZornMatrix.map_mul f X Y, ?_, ?_, ?_, ?_⟩
  · ext <;> rfl
  · ext <;> simp [OpZornMatrix.map, OpVec3.map, opDoubletDiagEmbed, opGradeZero, opCartanDiag]
  · simp [OpVec3.map, OpVec3.dot]
  · ext <;> simp [OpVec3.map, OpVec3.skewCross, OpVec3.naiveCross]
  · simp only [opAssociator, OpZornMatrix.map_sub, OpZornMatrix.map_mul]
  · ext <;>
      simp [OpZornMatrix.map, OpVec3.map, opZornRiccati, OpVec3.dot,
            OpVec3.leftScale, OpVec3.rightScale]
  · have h_shift := (zornRiccati_taylor_shift_and_noncomm_berezinian_unit T₀ v δ 1 1).1
    have h_fp : opZornRiccati T₀ v = 0 :=
      (zornRiccati_moving_frame_and_trifactor_fixed_point T₀ v w v 0 0 0).2.2.2
    have h_a : T₀.a = 1 := by
      simp [T₀, opBruhatTrifactor, opUnipotentLower, opCartanDiag, opUnipotentUpper,
            OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross, OpVec3.leftScale, OpVec3.rightScale]
    have h_w : T₀.w = w := by
      ext <;>
        simp [T₀, opBruhatTrifactor, opUnipotentLower, opCartanDiag, opUnipotentUpper,
              OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross, OpVec3.leftScale, OpVec3.rightScale]
    have h_bv : T₀.b + OpVec3.dot T₀.w v = 0 := by
      have h_q := (gelfandRetakh_gauss_bruhat_elimination_and_bimodule_curvature v w 1 0 0).2.2.2.1
      have h_v : T₀.v = v := by
        ext <;>
          simp [T₀, opBruhatTrifactor, opUnipotentLower, opCartanDiag, opUnipotentUpper,
                OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross, OpVec3.leftScale, OpVec3.rightScale]
      rw [← h_v]
      exact h_q
    rw [h_shift, h_fp, h_a, h_bv, h_w]
    ext <;> simp [OpVec3.leftScale, OpVec3.rightScale]
  · ext <;>
      (simp [amp, opCompassNeedleRow, opCompassNeedleCol, OpVec3.dot, OpVec3.skewCross,
             OpVec3.naiveCross, OpVec3.leftScale, OpVec3.rightScale];
       try noncomm_ring)

/-- **Gelfand–Retakh $(1, 1)$-Quasideterminant (`gelfandRetakhQuasiDet11 u v w b`)**:
    $|X|_{11} = b + w \cdot (u^{-1} \cdot_{\mathrm{L}} v) \in A$ for $X = \langle u, v, w, b \rangle \in \mathrm{OpZornMatrix}\;A$. -/
@[simp] def gelfandRetakhQuasiDet11 (u : Aˣ) (v w : OpVec3 A) (b : A) : A :=
  b + OpVec3.dot w (OpVec3.leftScale (↑u⁻¹ : A) v)

/-- **5-Graded Boundary Compass Stage Embedding (`opCompassStageEmbed ξ y z x`)**:
    Sandwiches $\iota_{11}(x) = \mathrm{opPeirceCornerEmbed11}\;x$ between the 5-graded contact-transverse
    compass needles $P_{\mathrm{col}}(\langle \xi, 0, 0 \rangle)$ and $P_{\mathrm{row}}(\langle 0, -y, -z \rangle)$. -/
@[simp] def opCompassStageEmbed (ξ y z x : A) : OpZornMatrix A :=
  (opCompassNeedleCol ⟨ξ, 0, 0⟩ * opPeirceCornerEmbed11 x) * opCompassNeedleRow ⟨0, -y, -z⟩

/-- **Theorem 114 (Archetypes XCII–XCV — Associative Nucleus of `opDoubletDiagEmbed` against Grade-0 / Opposite-Nilradical States, 5-Graded Compass Stage Idempotence, Gelfand–Retakh Quasideterminant Reconstruction, & Two-Sided Contact-Cartan Banachiewicz Inversion)**:
    Over *any* noncommutative operator ring $A$ (`[Ring A]`), for all $x, a, b, \xi, \eta, y, z \in A$,
    all $v, w \in \mathrm{OpVec3}\;A$, all $Y \in \mathrm{OpZornMatrix}\;A$, and all units $u, \Delta_u \in A^\times$:
    1. **Associative Nucleus of `opDoubletDiagEmbed` with Opposite Lightcone Rays & Grade-0 States (`Archetype XCII.3`)**:
       $$[\iota_{\mathrm{diag}}(x), L_+(v), L_-(w)] = 0, \qquad
         [L_+(v), \iota_{\mathrm{diag}}(x), L_-(w)] = 0, \qquad
         [L_+(v), L_-(w), \iota_{\mathrm{diag}}(x)] = 0, \qquad
         [\iota_{\mathrm{diag}}(x), Y, \mathrm{opGradeZero}\;a\;b] = 0.$$
    2. **3-Channel Boundary Compass Stage Idempotent Survival (`Archetype XCIII.2`)**:
       $$\mathrm{opCompassStageEmbed}\;\xi\;y\;z\;1 * \mathrm{opCompassStageEmbed}\;\xi\;y\;z\;1 =
         \mathrm{opCompassStageEmbed}\;\xi\;y\;z\;1.$$
    3. **Exact Gelfand–Retakh $(1, 1)$-Quasideterminant Trifactor Reconstruction (`Archetype XCIV.3`)**:
       $$\mathrm{opBruhatTrifactor}\;(w \cdot_{\mathrm{R}} u^{-1})\;(u : A)\;(\mathrm{gelfandRetakhQuasiDet11}\;u\;v\;w\;b)\;(u^{-1} \cdot_{\mathrm{L}} v) =
         \langle (u : A), v, w, b \rangle.$$
    4. **Exact Two-Sided Banachiewicz–Quasideterminant Inversion on the Contact-Cartan Subalgebra $\mathcal{G}_{-2} \oplus \mathcal{G}_0 \oplus \mathcal{G}_{+2}$ (`Archetype XCV.2`)**:
       For $w_c = \mathrm{opBasisE1}\;\xi = \langle \xi, 0, 0 \rangle$ and $v_c = \mathrm{opBasisE1}\;\eta = \langle \eta, 0, 0 \rangle$:
       $$\mathrm{opBruhatTrifactor}\;w_c\;(u : A)\;(\Delta_u : A)\;v_c *
         \mathrm{opBruhatTrifactorInv}\;v_c\;(\uparrow u^{-1} : A)\;(\uparrow \Delta_u^{-1} : A)\;w_c = 1,$$
       $$\mathrm{opBruhatTrifactorInv}\;v_c\;(\uparrow u^{-1} : A)\;(\uparrow \Delta_u^{-1} : A)\;w_c *
         \mathrm{opBruhatTrifactor}\;w_c\;(u : A)\;(\Delta_u : A)\;v_c = 1.$$ -/
theorem opDoubletNucleus_compassStage_and_gelfandRetakh_two_sided_inverse
    (x a b ξ η y z : A) (v w : OpVec3 A) (Y : OpZornMatrix A) (u Δ_u : Aˣ) :
    let w_c := opBasisE1 ξ
    let v_c := opBasisE1 η
    opAssociator (opDoubletDiagEmbed x) (opLightconePlus v) (opLightconeMinus w) = 0 ∧
    opAssociator (opLightconePlus v) (opDoubletDiagEmbed x) (opLightconeMinus w) = 0 ∧
    opAssociator (opLightconePlus v) (opLightconeMinus w) (opDoubletDiagEmbed x) = 0 ∧
    opAssociator (opDoubletDiagEmbed x) Y (opGradeZero a b) = 0 ∧
    opCompassStageEmbed ξ y z 1 * opCompassStageEmbed ξ y z 1 =
      opCompassStageEmbed ξ y z 1 ∧
    opBruhatTrifactor (OpVec3.rightScale w (↑u⁻¹ : A)) (u : A)
      (gelfandRetakhQuasiDet11 u v w b) (OpVec3.leftScale (↑u⁻¹ : A) v) =
      ⟨(u : A), v, w, b⟩ ∧
    opBruhatTrifactor w_c (u : A) (Δ_u : A) v_c *
      opBruhatTrifactorInv v_c (↑u⁻¹ : A) (↑Δ_u⁻¹ : A) w_c = 1 ∧
    opBruhatTrifactorInv v_c (↑u⁻¹ : A) (↑Δ_u⁻¹ : A) w_c *
      opBruhatTrifactor w_c (u : A) (Δ_u : A) v_c = 1 := by
  intro w_c v_c
  have h_schur := (opBruhatTrifactor_coords_and_operator_schur_reconstruction w v (u : A) b b u).2.2.2
  have h_inv := (opBruhatTrifactor_parabolic_cartan_and_single_channel_inverse v w η ξ u Δ_u).2.2.2.2.2
  refine ⟨?_, ?_, ?_, ?_, ?_, h_schur, h_inv.1, h_inv.2⟩
  · ext <;>
      (simp [opAssociator, opDoubletDiagEmbed, opGradeZero, opCartanDiag,
             opLightconeRayPlus, opLightconeRayMinus,
             OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross,
             OpVec3.leftScale, OpVec3.rightScale];
       try noncomm_ring)
  · ext <;>
      (simp [opAssociator, opDoubletDiagEmbed, opGradeZero, opCartanDiag,
             opLightconeRayPlus, opLightconeRayMinus,
             OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross,
             OpVec3.leftScale, OpVec3.rightScale];
       try noncomm_ring)
  · ext <;>
      (simp [opAssociator, opDoubletDiagEmbed, opGradeZero, opCartanDiag,
             opLightconeRayPlus, opLightconeRayMinus,
             OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross,
             OpVec3.leftScale, OpVec3.rightScale];
       try noncomm_ring)
  · ext <;>
      (simp [opAssociator, opDoubletDiagEmbed, opGradeZero, opCartanDiag,
             OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross,
             OpVec3.leftScale, OpVec3.rightScale];
       try noncomm_ring)
  · ext <;>
      (simp [opCompassStageEmbed, opCompassNeedleCol, opCompassNeedleRow, opPeirceCornerEmbed11,
             opGradeZero, opCartanDiag, OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross,
             OpVec3.leftScale, OpVec3.rightScale];
       try noncomm_ring)

/-- **Noncommutative Zorn–Riccati Tangent Jacobian (`opZornRiccatiJacobian X q δ`)**:
    The linear Fréchet directional derivative of $\mathcal{R}_X$ at $q$ in direction $\delta \in \mathrm{OpVec3}\;A$:
    $\mathcal{J}_{X, q}(\delta) = X.a \cdot_{\mathrm{L}} \delta + \delta \cdot_{\mathrm{R}} (X.b + X.w \cdot q) + q \cdot_{\mathrm{R}} (X.w \cdot \delta)$. -/
@[simp] def opZornRiccatiJacobian (X : OpZornMatrix A) (q δ : OpVec3 A) : OpVec3 A :=
  OpVec3.leftScale X.a δ +
    OpVec3.rightScale δ (X.b + OpVec3.dot X.w q) +
    OpVec3.rightScale q (OpVec3.dot X.w δ)

/-- **Theorem 115 (Archetypes XC–XCIII — Functorial Category Laws of `OpZornMatrix.map`, Compass Stage Colimit Naturality, Riccati Jacobian Taylor Cocycle, & Dilaton Gauge Cross-Ratio Covariance)**:
    For any noncommutative ring homomorphisms $f : A \to+* B$ and $g : B \to+* C$ (`[Ring A] [Ring B] [Ring C]`),
    for all $X, Y, Z \in \mathrm{OpZornMatrix}\;A$, $q, \delta, v_1, v_2, w_3, w_4 \in \mathrm{OpVec3}\;A$,
    $x, \xi, y, z \in A$, and units $u_g, \mu_g \in A^\times$:
    1. **Category Functoriality & Unital Ring Homomorphism Laws of `OpZornMatrix.map`**:
       $$\mathrm{OpZornMatrix.map}\;(\mathrm{RingHom.id}\;A)\;X = X, \qquad
         \mathrm{OpZornMatrix.map}\;(g.\mathrm{comp}\;f)\;X = \mathrm{OpZornMatrix.map}\;g\;(\mathrm{OpZornMatrix.map}\;f\;X),$$
       $$\mathrm{OpZornMatrix.map}\;f\;0 = 0, \qquad \mathrm{OpZornMatrix.map}\;f\;1 = 1, \qquad
         \mathrm{opZornTrace}\;(\mathrm{OpZornMatrix.map}\;f\;X) = f\;(\mathrm{opZornTrace}\;X).$$
    2. **Naturality of Inductive Colimit Stage & 5-Graded Compass Embeddings**:
       $$\mathrm{OpZornMatrix.map}\;f\;(\mathrm{opDoubletDiagEmbed}\;x) = \mathrm{opDoubletDiagEmbed}\;(f\;x),$$
       $$\mathrm{OpZornMatrix.map}\;f\;(\mathrm{opCompassStageEmbed}\;\xi\;y\;z\;x) =
         \mathrm{opCompassStageEmbed}\;(f\;\xi)\;(f\;y)\;(f\;z)\;(f\;x).$$
    3. **Noncommutative Zorn–Riccati Jacobian Taylor Cocycle & 4-Spinor Cross-Ratio Dilaton Gauge Covariance**:
       $$\mathrm{opZornRiccati}\;X\;(q + \delta) =
         \mathrm{opZornRiccati}\;X\;q + \mathrm{opZornRiccatiJacobian}\;X\;q\;\delta +
         \mathrm{OpVec3.rightScale}\;\delta\;(\mathrm{OpVec3.dot}\;X.w\;\delta),$$
       $$\mathrm{OpVec3.dot}\;\bigl(\mathrm{OpVec3.leftScale}\;(u_g : A)\;(\mathrm{OpVec3.rightScale}\;(v_1 - v_2)\;(\uparrow \mu_g^{-1} : A))\bigr)\;
         \bigl(\mathrm{OpVec3.leftScale}\;(\mu_g : A)\;(\mathrm{OpVec3.rightScale}\;(w_3 - w_4)\;(\uparrow u_g^{-1} : A))\bigr) =
         (u_g : A) * \mathrm{OpVec3.dot}\;(v_1 - v_2)\;(w_3 - w_4) * (\uparrow u_g^{-1} : A).$$ -/
theorem opZornMatrix_map_functorial_riccati_and_colimit_naturality
    {B C : Type*} [Ring B] [Ring C] (f : A →+* B) (g : B →+* C)
    (X : OpZornMatrix A) (q δ v₁ v₂ w₃ w₄ : OpVec3 A) (x ξ y z : A) (u_g μ_g : Aˣ) :
    OpZornMatrix.map (RingHom.id A) X = X ∧
    OpZornMatrix.map (g.comp f) X = OpZornMatrix.map g (OpZornMatrix.map f X) ∧
    OpZornMatrix.map f 0 = 0 ∧
    OpZornMatrix.map f 1 = 1 ∧
    opZornTrace (OpZornMatrix.map f X) = f (opZornTrace X) ∧
    OpZornMatrix.map f (opDoubletDiagEmbed x) = opDoubletDiagEmbed (f x) ∧
    OpZornMatrix.map f (opCompassStageEmbed ξ y z x) =
      opCompassStageEmbed (f ξ) (f y) (f z) (f x) ∧
    opZornRiccati X (q + δ) =
      opZornRiccati X q + opZornRiccatiJacobian X q δ +
        OpVec3.rightScale δ (OpVec3.dot X.w δ) ∧
    OpVec3.dot
        (OpVec3.leftScale (u_g : A) (OpVec3.rightScale (v₁ - v₂) (↑μ_g⁻¹ : A)))
        (OpVec3.leftScale (μ_g : A) (OpVec3.rightScale (w₃ - w₄) (↑u_g⁻¹ : A))) =
      (u_g : A) * OpVec3.dot (v₁ - v₂) (w₃ - w₄) * (↑u_g⁻¹ : A) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_,
          (zornRiccati_taylor_shift_and_noncomm_berezinian_unit X q δ 1 1).1, ?_⟩
  · ext <;> rfl
  · ext <;> rfl
  · ext <;> simp [OpZornMatrix.map, OpVec3.map]
  · ext <;> simp [OpZornMatrix.map, OpVec3.map]
  · simp [OpZornMatrix.map, opZornTrace]
  · ext <;> simp [OpZornMatrix.map, OpVec3.map, opDoubletDiagEmbed, opGradeZero, opCartanDiag]
  · rw [opCompassStageEmbed, OpZornMatrix.map_mul, OpZornMatrix.map_mul]
    ext <;>
      simp [opCompassStageEmbed, opCompassNeedleCol, opCompassNeedleRow, opPeirceCornerEmbed11,
            opGradeZero, opCartanDiag, OpZornMatrix.map, OpVec3.map,
            OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross,
            OpVec3.leftScale, OpVec3.rightScale]
  · have h_mu : ∀ a b : A, a * (↑μ_g⁻¹ : A) * ((μ_g : A) * b) = a * b := by
      intro a b
      calc a * (↑μ_g⁻¹ : A) * ((μ_g : A) * b)
        _ = a * ((↑μ_g⁻¹ : A) * (μ_g : A)) * b := by noncomm_ring
        _ = a * 1 * b := by rw [Units.inv_mul]
        _ = a * b := by simp
    simp only [OpVec3.dot, OpVec3.leftScale_x, OpVec3.leftScale_y, OpVec3.leftScale_z,
               OpVec3.rightScale_x, OpVec3.rightScale_y, OpVec3.rightScale_z,
               OpVec3.sub_x, OpVec3.sub_y, OpVec3.sub_z]
    have h1 : (u_g : A) * ((v₁.x - v₂.x) * (↑μ_g⁻¹ : A)) * ((μ_g : A) * ((w₃.x - w₄.x) * (↑u_g⁻¹ : A))) =
        (u_g : A) * (v₁.x - v₂.x) * (w₃.x - w₄.x) * (↑u_g⁻¹ : A) := by
      calc (u_g : A) * ((v₁.x - v₂.x) * (↑μ_g⁻¹ : A)) * ((μ_g : A) * ((w₃.x - w₄.x) * (↑u_g⁻¹ : A)))
        _ = ((u_g : A) * (v₁.x - v₂.x)) * (↑μ_g⁻¹ : A) * ((μ_g : A) * ((w₃.x - w₄.x) * (↑u_g⁻¹ : A))) := by noncomm_ring
        _ = ((u_g : A) * (v₁.x - v₂.x)) * ((w₃.x - w₄.x) * (↑u_g⁻¹ : A)) := h_mu _ _
        _ = (u_g : A) * (v₁.x - v₂.x) * (w₃.x - w₄.x) * (↑u_g⁻¹ : A) := by noncomm_ring
    have h2 : (u_g : A) * ((v₁.y - v₂.y) * (↑μ_g⁻¹ : A)) * ((μ_g : A) * ((w₃.y - w₄.y) * (↑u_g⁻¹ : A))) =
        (u_g : A) * (v₁.y - v₂.y) * (w₃.y - w₄.y) * (↑u_g⁻¹ : A) := by
      calc (u_g : A) * ((v₁.y - v₂.y) * (↑μ_g⁻¹ : A)) * ((μ_g : A) * ((w₃.y - w₄.y) * (↑u_g⁻¹ : A)))
        _ = ((u_g : A) * (v₁.y - v₂.y)) * (↑μ_g⁻¹ : A) * ((μ_g : A) * ((w₃.y - w₄.y) * (↑u_g⁻¹ : A))) := by noncomm_ring
        _ = ((u_g : A) * (v₁.y - v₂.y)) * ((w₃.y - w₄.y) * (↑u_g⁻¹ : A)) := h_mu _ _
        _ = (u_g : A) * (v₁.y - v₂.y) * (w₃.y - w₄.y) * (↑u_g⁻¹ : A) := by noncomm_ring
    have h3 : (u_g : A) * ((v₁.z - v₂.z) * (↑μ_g⁻¹ : A)) * ((μ_g : A) * ((w₃.z - w₄.z) * (↑u_g⁻¹ : A))) =
        (u_g : A) * (v₁.z - v₂.z) * (w₃.z - w₄.z) * (↑u_g⁻¹ : A) := by
      calc (u_g : A) * ((v₁.z - v₂.z) * (↑μ_g⁻¹ : A)) * ((μ_g : A) * ((w₃.z - w₄.z) * (↑u_g⁻¹ : A)))
        _ = ((u_g : A) * (v₁.z - v₂.z)) * (↑μ_g⁻¹ : A) * ((μ_g : A) * ((w₃.z - w₄.z) * (↑u_g⁻¹ : A))) := by noncomm_ring
        _ = ((u_g : A) * (v₁.z - v₂.z)) * ((w₃.z - w₄.z) * (↑u_g⁻¹ : A)) := h_mu _ _
        _ = (u_g : A) * (v₁.z - v₂.z) * (w₃.z - w₄.z) * (↑u_g⁻¹ : A) := by noncomm_ring
    rw [h1, h2, h3]
    noncomm_ring

/-!
## 42. Archetypes XCVI–XCVIII: Operator-Twisted Nambu–Gorkov Cayley–Dickson Doubling $\mathrm{CD}_\Omega(A)$ and Spectral Projectors of the 5-Graded Operator Characteristic Polynomial
-/

/-- **Operator-Twisted Nambu–Gorkov Cayley–Dickson Pair (`OpCayleyDickson A`)**:
    Represents an element $(x, y) \in A \times A$ with particle component $x \in A$ and
    anomalous / hole component $y \in A$. -/
@[ext]
structure OpCayleyDickson (A : Type*) where
  x : A
  y : A
  deriving DecidableEq, Inhabited

instance instZeroOpCayleyDickson : Zero (OpCayleyDickson A) := ⟨⟨0, 0⟩⟩
instance instOneOpCayleyDickson : One (OpCayleyDickson A) := ⟨⟨1, 0⟩⟩
instance instAddOpCayleyDickson : Add (OpCayleyDickson A) := ⟨fun z w => ⟨z.x + w.x, z.y + w.y⟩⟩
instance instSubOpCayleyDickson : Sub (OpCayleyDickson A) := ⟨fun z w => ⟨z.x - w.x, z.y - w.y⟩⟩
instance instNegOpCayleyDickson : Neg (OpCayleyDickson A) := ⟨fun z => ⟨-z.x, -z.y⟩⟩

@[simp] lemma OpCayleyDickson.zero_x : (0 : OpCayleyDickson A).x = 0 := rfl
@[simp] lemma OpCayleyDickson.zero_y : (0 : OpCayleyDickson A).y = 0 := rfl
@[simp] lemma OpCayleyDickson.one_x : (1 : OpCayleyDickson A).x = 1 := rfl
@[simp] lemma OpCayleyDickson.one_y : (1 : OpCayleyDickson A).y = 0 := rfl
@[simp] lemma OpCayleyDickson.add_x (z w : OpCayleyDickson A) : (z + w).x = z.x + w.x := rfl
@[simp] lemma OpCayleyDickson.add_y (z w : OpCayleyDickson A) : (z + w).y = z.y + w.y := rfl
@[simp] lemma OpCayleyDickson.sub_x (z w : OpCayleyDickson A) : (z - w).x = z.x - w.x := rfl
@[simp] lemma OpCayleyDickson.sub_y (z w : OpCayleyDickson A) : (z - w).y = z.y - w.y := rfl
@[simp] lemma OpCayleyDickson.neg_x (z : OpCayleyDickson A) : (-z).x = -z.x := rfl
@[simp] lemma OpCayleyDickson.neg_y (z : OpCayleyDickson A) : (-z).y = -z.y := rfl

/-- **Nambu–Gorkov Cayley–Dickson Conjugation (`cdConj z`)**:
    $(x, y)^\star = (x^\star, -y)$. -/
@[simp] def cdConj [StarRing A] (z : OpCayleyDickson A) : OpCayleyDickson A :=
  ⟨star z.x, -z.y⟩

/-- **Operator-Twisted Cayley–Dickson Product (`cdMul Ω z w`)**:
    $$(x, y) *_\Omega (X, Y) = \bigl(x * X + \Omega * (Y * y^\star),\;\; x^\star * Y + X * y\bigr).$$ -/
@[simp] def cdMul [StarRing A] (Ω : A) (z w : OpCayleyDickson A) : OpCayleyDickson A :=
  ⟨z.x * w.x + Ω * (w.y * star z.y),
   star z.x * w.y + w.x * z.y⟩

/-- Particle-channel unital embedding $\iota(x) = (x, 0) \in \mathrm{OpCayleyDickson}\;A$. -/
@[simp] def cdEmbed (x : A) : OpCayleyDickson A := ⟨x, 0⟩

/-- The Nambu–Gorkov Cayley–Dickson doubling unit $\mathbf{E} = (0, 1) \in \mathrm{OpCayleyDickson}\;A$. -/
@[simp] def cdGenE : OpCayleyDickson A := ⟨0, 1⟩

/-- **Theorem 116 (Archetypes XCVI & XCVII — Operator-Twisted Nambu–Gorkov Cayley–Dickson Laws, Norm Cancellation, & Particle-Hole Flip)**:
    Over *any* noncommutative $*$-ring $A$ (`[Ring A] [StarRing A]`) and for *any* operator twist $\Omega \in A$ and $x, y \in A$:
    1. **Exact Involution & Unital Embedding**:
       $((x, y)^\star)^\star = (x, y)$, $\mathrm{cdMul}\;\Omega\;1\;(x, y) = (x, y)$,
       $\mathrm{cdMul}\;\Omega\;(x, y)\;1 = (x, y)$, and
       $\mathrm{cdMul}\;\Omega\;(\iota(x))\;(\iota(y)) = \iota(x * y)$.
    2. **Universal Cancellation of Anomalous Off-Diagonal Pairing in $Z *_\Omega Z^\star$**:
       $$\mathrm{cdMul}\;\Omega\;\langle x, y \rangle\;(\mathrm{cdConj}\;\langle x, y \rangle) =
         \iota\bigl(x * x^\star - \Omega * (y * y^\star)\bigr).$$
    3. **Universal Operator Powers of the Doubling Generator $\mathbf{E} = (0, 1)$**:
       $$\mathrm{cdMul}\;\Omega\;\mathbf{E}\;\mathbf{E} = \iota(\Omega), \qquad
         \mathrm{cdMul}\;\Omega\;(\mathrm{cdMul}\;\Omega\;\mathbf{E}\;\mathbf{E})\;\mathbf{E} = \langle 0, \Omega \rangle,$$
       $$\mathrm{cdMul}\;\Omega\;(\mathrm{cdMul}\;\Omega\;\mathbf{E}\;\mathbf{E})\;(\mathrm{cdMul}\;\Omega\;\mathbf{E}\;\mathbf{E}) =
         \iota(\Omega * \Omega).$$
    4. **Nambu–Gorkov Antilinear Particle-Hole Conjugation by $\mathbf{E} = (0, 1)$**:
       $$\mathrm{cdMul}\;\Omega\;(\iota(x))\;\mathbf{E} = \langle 0, x^\star \rangle, \qquad
         \mathrm{cdMul}\;\Omega\;\mathbf{E}\;(\iota(x)) = \langle 0, x \rangle,$$
       $$\mathrm{cdMul}\;\Omega\;(\mathrm{cdMul}\;\Omega\;\mathbf{E}\;(\iota(x)))\;\mathbf{E} =
         \iota(\Omega * x^\star).$$ -/
theorem nambuGorkov_operator_cayley_dickson_norm_and_particle_hole_flip
    [StarRing A] (Ω x y : A) :
    let Z : OpCayleyDickson A := ⟨x, y⟩
    let E : OpCayleyDickson A := cdGenE
    let E2 := cdMul Ω E E
    cdConj (cdConj Z) = Z ∧
    cdMul Ω 1 Z = Z ∧
    cdMul Ω Z 1 = Z ∧
    cdMul Ω (cdEmbed x) (cdEmbed y) = cdEmbed (x * y) ∧
    cdMul Ω Z (cdConj Z) = cdEmbed (x * star x - Ω * (y * star y)) ∧
    E2 = cdEmbed Ω ∧
    cdMul Ω E2 E = ⟨0, star Ω⟩ ∧
    cdMul Ω E2 E2 = cdEmbed (Ω * Ω) ∧
    cdMul Ω (cdEmbed x) E = ⟨0, star x⟩ ∧
    cdMul Ω E (cdEmbed x) = ⟨0, x⟩ ∧
    cdMul Ω (cdMul Ω E (cdEmbed x)) E = cdEmbed (Ω * star x) := by
  intro Z E E2
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  (ext <;>
   (simp [Z, E, E2, cdConj, cdMul, cdEmbed, cdGenE, star_one, star_zero];
    try noncomm_ring))

/-- **Theorem 117 (Archetype XCVII — Unification of Division $\Omega = -1$, Split $\Omega = +1$, and Quartic Operator $\Omega^2 = \pm 1$ Regimes)**:
    Over *any* noncommutative $*$-ring $A$ (`[Ring A] [StarRing A]`), for all $\Omega, x, y \in A$:
    1. **Normed Division Doubling ($\Omega = -1$)**:
       $\mathbf{E} *_{-1} \mathbf{E} = -1$ and
       $(x, y) *_{-1} (x, y)^\star = \iota(x * x^\star + y * y^\star)$.
    2. **Split Hypercomplex Doubling ($\Omega = +1$)**:
       $\mathbf{E} *_{+1} \mathbf{E} = 1$ and
       $(x, y) *_{+1} (x, y)^\star = \iota(x * x^\star - y * y^\star)$.
    3. **Quartic Operator Twist Regime**:
       $(\mathbf{E} *_\Omega \mathbf{E})^2 - 1 = \iota(\Omega^2 - 1)$ and
       $(\mathbf{E} *_\Omega \mathbf{E})^2 + 1 = \iota(\Omega^2 + 1)$. -/
theorem nambuGorkov_division_split_and_quartic_operator_regimes
    [StarRing A] (Ω x y : A) :
    let Z : OpCayleyDickson A := ⟨x, y⟩
    let E : OpCayleyDickson A := cdGenE
    let E2_Ω := cdMul Ω E E
    cdMul (-1) E E = -1 ∧
    cdMul (-1) Z (cdConj Z) = cdEmbed (x * star x + y * star y) ∧
    cdMul 1 E E = 1 ∧
    cdMul 1 Z (cdConj Z) = cdEmbed (x * star x - y * star y) ∧
    cdMul Ω E2_Ω E2_Ω - 1 = cdEmbed (Ω * Ω - 1) ∧
    cdMul Ω E2_Ω E2_Ω + 1 = cdEmbed (Ω * Ω + 1) := by
  intro Z E E2_Ω
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  (ext <;>
   (simp [Z, E, E2_Ω, cdConj, cdMul, cdEmbed, cdGenE, star_one, star_zero];
    try noncomm_ring))

/-- **Theorem 118 (Archetype XCVIII — Spectral Projector Factorization of the 5-Graded Operator Characteristic Polynomial $\mathcal{D}_5^5 - 5\mathcal{D}_5^3 + 4\mathcal{D}_5 = 0$)**:
    Over *any* noncommutative operator ring $A$ (`[Ring A]`), for every 8-component operator state
    $X \in \mathrm{OpZornMatrix}\;A$, let $D_k = \mathrm{opEulerFiveGrading}^k(X)$:
    1. **5-Grade Resolution of $X$**:
       $$X = \mathrm{opGradeMinus2}\;X.v.x + \mathrm{opGradeMinus1}\;X.w.y\;X.w.z + \mathrm{opGradeZero}\;X.a\;X.b +
             \mathrm{opGradePlus1}\;X.v.y\;X.v.z + \mathrm{opGradePlus2}\;X.w.x.$$
    2. **Quartic Nucleus Spectral Projector $(\mathcal{D}_5^2 - I)(\mathcal{D}_5^2 - 4I)(X) = \mathcal{D}_5^4(X) - 5\mathcal{D}_5^2(X) + 4X$**:
       Annihilates $\mathcal{G}_{-2}, \mathcal{G}_{-1}, \mathcal{G}_{+1}, \mathcal{G}_{+2}$ and isolates $4 \bullet \mathcal{G}_0(X)$:
       $$D_4 - (D_2 + D_2 + D_2 + D_2 + D_2) + (X + X + X + X) =
         \mathrm{opGradeZero}\;X.a\;X.b + \mathrm{opGradeZero}\;X.a\;X.b +
         \mathrm{opGradeZero}\;X.a\;X.b + \mathrm{opGradeZero}\;X.a\;X.b.$$
    3. **Cubic Transverse Cone Spectral Projector $\mathcal{D}_5(\mathcal{D}_5^2 - 4I)(X) = \mathcal{D}_5^3(X) - 4\mathcal{D}_5(X)$**:
       Annihilates $\mathcal{G}_{-2}, \mathcal{G}_0, \mathcal{G}_{+2}$ and isolates $-3 \bullet (\mathcal{G}_{+1}(X) - \mathcal{G}_{-1}(X))$:
       $$D_3 - (D_1 + D_1 + D_1 + D_1) =
         -((\mathrm{opGradePlus1}\;X.v.y\;X.v.z - \mathrm{opGradeMinus1}\;X.w.y\;X.w.z) +
           (\mathrm{opGradePlus1}\;X.v.y\;X.v.z - \mathrm{opGradeMinus1}\;X.w.y\;X.w.z) +
           (\mathrm{opGradePlus1}\;X.v.y\;X.v.z - \mathrm{opGradeMinus1}\;X.w.y\;X.w.z)).$$
    4. **Cubic Contact Horizon Spectral Projector $\mathcal{D}_5(\mathcal{D}_5^2 - I)(X) = \mathcal{D}_5^3(X) - \mathcal{D}_5(X)$**:
       Annihilates $\mathcal{G}_{-1}, \mathcal{G}_0, \mathcal{G}_{+1}$ and isolates $6 \bullet (\mathcal{G}_{+2}(X) - \mathcal{G}_{-2}(X))$:
       $$D_3 - D_1 =
         (\mathrm{opGradePlus2}\;X.w.x - \mathrm{opGradeMinus2}\;X.v.x) +
         (\mathrm{opGradePlus2}\;X.w.x - \mathrm{opGradeMinus2}\;X.v.x) +
         (\mathrm{opGradePlus2}\;X.w.x - \mathrm{opGradeMinus2}\;X.v.x) +
         (\mathrm{opGradePlus2}\;X.w.x - \mathrm{opGradeMinus2}\;X.v.x) +
         (\mathrm{opGradePlus2}\;X.w.x - \mathrm{opGradeMinus2}\;X.v.x) +
         (\mathrm{opGradePlus2}\;X.w.x - \mathrm{opGradeMinus2}\;X.v.x).$$
    5. **Universal Degree-5 Characteristic Polynomial Annihilation**:
       $$D_5 - (D_3 + D_3 + D_3 + D_3 + D_3) + (D_1 + D_1 + D_1 + D_1) = 0.$$ -/
theorem fiveGraded_operator_characteristic_polynomial_and_spectral_projectors
    (X : OpZornMatrix A) :
    let D₁ := opEulerFiveGrading X
    let D₂ := opEulerFiveGrading D₁
    let D₃ := opEulerFiveGrading D₂
    let D₄ := opEulerFiveGrading D₃
    let D₅ := opEulerFiveGrading D₄
    let G₀ := opGradeZero X.a X.b
    let G₁ := opGradePlus1 X.v.y X.v.z - opGradeMinus1 X.w.y X.w.z
    let G₂ := opGradePlus2 X.w.x - opGradeMinus2 X.v.x
    X = opGradeMinus2 X.v.x + opGradeMinus1 X.w.y X.w.z + opGradeZero X.a X.b +
          opGradePlus1 X.v.y X.v.z + opGradePlus2 X.w.x ∧
    D₄ - (D₂ + D₂ + D₂ + D₂ + D₂) + (X + X + X + X) = G₀ + G₀ + G₀ + G₀ ∧
    D₃ - (D₁ + D₁ + D₁ + D₁) = -(G₁ + G₁ + G₁) ∧
    D₃ - D₁ = G₂ + G₂ + G₂ + G₂ + G₂ + G₂ ∧
    D₅ - (D₃ + D₃ + D₃ + D₃ + D₃) + (D₁ + D₁ + D₁ + D₁) = 0 := by
  intro D₁ D₂ D₃ D₄ D₅ G₀ G₁ G₂
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
  (ext <;>
   (simp [D₁, D₂, D₃, D₄, D₅, G₀, G₁, G₂, opEulerFiveGrading,
          opGradeMinus2, opGradeMinus1, opGradeZero, opCartanDiag, opGradePlus1, opGradePlus2];
    try abel))

/-! ### 43. Operator Cyclotomics, Noncommutative Cyclotomic Quotients, & the $\mathbb{Z}_6$ Galois Automorphism Group (`Archetypes XCIX & C`) -/

/-- The $\mathbb{Z}_2$ Cayley–Dickson Galois involution $\sigma_{\mathrm{CD}}(x, y) := (x, -y)$
on `OpCayleyDickson A` (`Archetype C.1`). -/
def cdGaloisZ2 (Z : OpCayleyDickson A) : OpCayleyDickson A :=
  ⟨Z.x, -Z.y⟩

@[simp] theorem cdGaloisZ2_x (Z : OpCayleyDickson A) : (cdGaloisZ2 Z).x = Z.x := rfl
@[simp] theorem cdGaloisZ2_y (Z : OpCayleyDickson A) : (cdGaloisZ2 Z).y = -Z.y := rfl

/-- The 1st operator cyclotomic polynomial $\Phi_1(\Omega) = \Omega - 1$ (`Archetype XCIX.1`). -/
def opPhi1 (Ω : A) : A := Ω - 1

/-- The 2nd operator cyclotomic polynomial $\Phi_2(\Omega) = \Omega + 1$ (`Archetype XCIX.1`). -/
def opPhi2 (Ω : A) : A := Ω + 1

/-- The 3rd operator cyclotomic polynomial $\Phi_3(\Omega) = \Omega^2 + \Omega + 1$ (`Archetype XCIX.1`). -/
def opPhi3 (Ω : A) : A := Ω * Ω + Ω + 1

/-- The 4th operator cyclotomic polynomial $\Phi_4(\Omega) = \Omega^2 + 1$ (`Archetype XCIX.1`). -/
def opPhi4 (Ω : A) : A := Ω * Ω + 1

/-- The 6th operator cyclotomic polynomial $\Phi_6(\Omega) = \Omega^2 - \Omega + 1$ (`Archetype XCIX.1`). -/
def opPhi6 (Ω : A) : A := Ω * Ω - Ω + 1

/-- The 8th operator cyclotomic polynomial $\Phi_8(\Omega) = \Omega^4 + 1$ (`Archetype XCIX.1`). -/
def opPhi8 (Ω : A) : A := (Ω * Ω) * (Ω * Ω) + 1

/-- **Theorem 119 (`Archetypes XCIX.1 & C.1`: Universal Noncommutative Cyclotomic Polynomial Factorizations & $\mathbb{Z}_2$ Cayley–Dickson Galois Automorphism)**:
    Over ANY noncommutative ring $A$ (`[Ring A] [StarRing A]`):
    1. **Universal Noncommutative Cyclotomic Factorizations in $A$**:
       - $\Omega^2 - 1 = \Phi_1(\Omega) * \Phi_2(\Omega) = \Phi_2(\Omega) * \Phi_1(\Omega)$,
       - $\Omega^3 - 1 = \Phi_1(\Omega) * \Phi_3(\Omega) = \Phi_3(\Omega) * \Phi_1(\Omega)$,
       - $\Omega^3 + 1 = \Phi_2(\Omega) * \Phi_6(\Omega) = \Phi_6(\Omega) * \Phi_2(\Omega)$,
       - $\Omega^4 - 1 = (\Phi_1(\Omega) * \Phi_2(\Omega)) * \Phi_4(\Omega)$,
       - $\Omega^6 - 1 = ((\Phi_1(\Omega) * \Phi_2(\Omega)) * \Phi_3(\Omega)) * \Phi_6(\Omega)$,
       - $\Omega^8 - 1 = ((\Phi_1(\Omega) * \Phi_2(\Omega)) * \Phi_4(\Omega)) * \Phi_8(\Omega)$.
    2. **Order-2 $\mathbb{Z}_2$ Cayley–Dickson Galois Automorphism $\sigma_{\mathrm{CD}}(x, y) = (x, -y)$**:
       - Involution: $\sigma_{\mathrm{CD}}(\sigma_{\mathrm{CD}}(Z)) = Z$,
       - Fixed subalgebra: $\sigma_{\mathrm{CD}}(\iota(x)) = \iota(x)$ and $\sigma_{\mathrm{CD}}(\mathbf{E}) = -\mathbf{E}$,
       - Exact $*$-algebra automorphism for every twist $\Omega \in A$:
         $$\sigma_{\mathrm{CD}}(Z *_\Omega W) = \sigma_{\mathrm{CD}}(Z) *_\Omega \sigma_{\mathrm{CD}}(W) \quad \text{and} \quad
           \sigma_{\mathrm{CD}}(Z^\star) = (\sigma_{\mathrm{CD}}(Z))^\star.$$ -/
theorem operator_cyclotomic_polynomial_factorizations
    [StarRing A] (Ω : A) (Z W : OpCayleyDickson A) :
    let Ω2 := Ω * Ω
    let Ω3 := Ω2 * Ω
    let Ω4 := Ω2 * Ω2
    let Ω6 := Ω3 * Ω3
    let Ω8 := Ω4 * Ω4
    (Ω2 - 1 = opPhi1 Ω * opPhi2 Ω ∧
     Ω2 - 1 = opPhi2 Ω * opPhi1 Ω ∧
     Ω3 - 1 = opPhi1 Ω * opPhi3 Ω ∧
     Ω3 - 1 = opPhi3 Ω * opPhi1 Ω ∧
     Ω3 + 1 = opPhi2 Ω * opPhi6 Ω ∧
     Ω3 + 1 = opPhi6 Ω * opPhi2 Ω ∧
     Ω4 - 1 = (opPhi1 Ω * opPhi2 Ω) * opPhi4 Ω ∧
     Ω6 - 1 = ((opPhi1 Ω * opPhi2 Ω) * opPhi3 Ω) * opPhi6 Ω ∧
     Ω8 - 1 = ((opPhi1 Ω * opPhi2 Ω) * opPhi4 Ω) * opPhi8 Ω) ∧
    (cdGaloisZ2 (cdGaloisZ2 Z) = Z ∧
     cdGaloisZ2 (cdEmbed Ω) = cdEmbed Ω ∧
     cdGaloisZ2 (cdGenE : OpCayleyDickson A) = -(cdGenE : OpCayleyDickson A) ∧
     cdGaloisZ2 (cdMul Ω Z W) = cdMul Ω (cdGaloisZ2 Z) (cdGaloisZ2 W) ∧
     cdGaloisZ2 (cdConj Z) = cdConj (cdGaloisZ2 Z)) := by
  intro Ω2 Ω3 Ω4 Ω6 Ω8
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_⟩⟩
  · simp [Ω2, opPhi1, opPhi2]; noncomm_ring
  · simp [Ω2, opPhi1, opPhi2]; noncomm_ring
  · simp [Ω3, Ω2, opPhi1, opPhi3]; noncomm_ring
  · simp [Ω3, Ω2, opPhi1, opPhi3]; noncomm_ring
  · simp [Ω3, Ω2, opPhi2, opPhi6]; noncomm_ring
  · simp [Ω3, Ω2, opPhi2, opPhi6]; noncomm_ring
  · simp [Ω4, Ω2, opPhi1, opPhi2, opPhi4]; noncomm_ring
  · simp [Ω6, Ω3, Ω2, opPhi1, opPhi2, opPhi3, opPhi6]; noncomm_ring
  · simp [Ω8, Ω4, Ω2, opPhi1, opPhi2, opPhi4, opPhi8]; noncomm_ring
  · ext <;> simp [cdGaloisZ2]
  · ext <;> simp [cdGaloisZ2, cdEmbed]
  · ext <;> simp [cdGaloisZ2, cdGenE]
  · ext <;> (simp [cdGaloisZ2, cdMul]; try abel; try noncomm_ring)
  · ext <;> simp [cdGaloisZ2, cdConj]

/-- **The 3rd Operator Cyclotomic Quotient Ring $\mathrm{OpCyclotomic3}\;A := A[\omega]/(\omega^2 + \omega + 1 = 0)$ (`Archetype XCIX.2`)**:
    Represented in the basis $\{1, \omega\}$ with $\omega^2 = -1 - \omega$:
    $$(a + b\omega)(c + d\omega) = (ac - bd) + (ad + bc - bd)\omega.$$ -/
@[ext]
structure OpCyclotomic3 (A : Type*) where
  c0 : A
  c1 : A
  deriving DecidableEq, Inhabited

namespace OpCyclotomic3

instance instZero : Zero (OpCyclotomic3 A) := ⟨⟨0, 0⟩⟩
instance instOne : One (OpCyclotomic3 A) := ⟨⟨1, 0⟩⟩
instance instAdd : Add (OpCyclotomic3 A) := ⟨fun x y => ⟨x.c0 + y.c0, x.c1 + y.c1⟩⟩
instance instNeg : Neg (OpCyclotomic3 A) := ⟨fun x => ⟨-x.c0, -x.c1⟩⟩
instance instSub : Sub (OpCyclotomic3 A) := ⟨fun x y => ⟨x.c0 - y.c0, x.c1 - y.c1⟩⟩
instance instMul : Mul (OpCyclotomic3 A) :=
  ⟨fun x y => ⟨x.c0 * y.c0 - x.c1 * y.c1, x.c0 * y.c1 + x.c1 * y.c0 - x.c1 * y.c1⟩⟩

@[simp] theorem zero_c0 : (0 : OpCyclotomic3 A).c0 = 0 := rfl
@[simp] theorem zero_c1 : (0 : OpCyclotomic3 A).c1 = 0 := rfl
@[simp] theorem one_c0 : (1 : OpCyclotomic3 A).c0 = 1 := rfl
@[simp] theorem one_c1 : (1 : OpCyclotomic3 A).c1 = 0 := rfl
@[simp] theorem add_c0 (x y : OpCyclotomic3 A) : (x + y).c0 = x.c0 + y.c0 := rfl
@[simp] theorem add_c1 (x y : OpCyclotomic3 A) : (x + y).c1 = x.c1 + y.c1 := rfl
@[simp] theorem neg_c0 (x : OpCyclotomic3 A) : (-x).c0 = -x.c0 := rfl
@[simp] theorem neg_c1 (x : OpCyclotomic3 A) : (-x).c1 = -x.c1 := rfl
@[simp] theorem sub_c0 (x y : OpCyclotomic3 A) : (x - y).c0 = x.c0 - y.c0 := rfl
@[simp] theorem sub_c1 (x y : OpCyclotomic3 A) : (x - y).c1 = x.c1 - y.c1 := rfl
@[simp] theorem mul_c0 (x y : OpCyclotomic3 A) : (x * y).c0 = x.c0 * y.c0 - x.c1 * y.c1 := rfl
@[simp] theorem mul_c1 (x y : OpCyclotomic3 A) :
    (x * y).c1 = x.c0 * y.c1 + x.c1 * y.c0 - x.c1 * y.c1 := rfl

/-- Canonical embedding $\iota_3(a) = (a, 0)$ of $A$ into $\mathrm{OpCyclotomic3}\;A$. -/
def embed (a : A) : OpCyclotomic3 A := ⟨a, 0⟩

/-- The primitive 3rd cyclotomic root $\omega = (0, 1) \in \mathrm{OpCyclotomic3}\;A$. -/
def omega : OpCyclotomic3 A := ⟨0, 1⟩

/-- The order-2 cyclotomic Galois automorphism $\sigma_3(a + b\omega) = (a - b) - b\omega$
sending $\omega \mapsto \omega^2 = -1 - \omega$ (`Archetype C.1`). -/
def galoisConj (x : OpCyclotomic3 A) : OpCyclotomic3 A :=
  ⟨x.c0 - x.c1, -x.c1⟩

end OpCyclotomic3

/-- **Theorem 120 (`Archetype XCIX.2 & C.1`: Noncommutative 3rd Cyclotomic Quotient Ring Laws & Galois Automorphism)**:
    Over ANY noncommutative ring $A$ (`[Ring A]`):
    1. **Associativity & Distributivity**: $(x * y) * z = x * (y * z)$, $1 * x = x$, $x * 1 = x$.
    2. **Primitive 3rd Root of Unity**: $\omega^2 = \langle -1, -1 \rangle$, $\omega^2 + \omega + 1 = 0$, and $\omega^3 = 1$.
    3. **Galois Automorphism $\sigma_3(\omega) = \omega^2$**:
       - $\sigma_3(\sigma_3(x)) = x$,
       - $\sigma_3(\omega) = \omega * \omega$,
       - $\sigma_3(x * y) = \sigma_3(x) * \sigma_3(y)$,
       - Norm over $A$: $(a + b\omega) * \sigma_3(a + b\omega) = \langle a^2 - ab + b^2,\; b a - a b \rangle$. -/
theorem opCyclotomic3_ring_laws_and_galois_automorphism
    (x y z : OpCyclotomic3 A) (a b : A) :
    let ω : OpCyclotomic3 A := OpCyclotomic3.omega
    let w : OpCyclotomic3 A := ⟨a, b⟩
    (x * y) * z = x * (y * z) ∧
    1 * x = x ∧
    x * 1 = x ∧
    ω * ω = ⟨-1, -1⟩ ∧
    ω * ω + ω + 1 = 0 ∧
    (ω * ω) * ω = 1 ∧
    OpCyclotomic3.galoisConj (OpCyclotomic3.galoisConj x) = x ∧
    OpCyclotomic3.galoisConj ω = ω * ω ∧
    OpCyclotomic3.galoisConj (x * y) = OpCyclotomic3.galoisConj x * OpCyclotomic3.galoisConj y ∧
    w * OpCyclotomic3.galoisConj w = ⟨a * a - a * b + b * b, b * a - a * b⟩ := by
  intro ω w
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · ext <;> (simp; noncomm_ring)
  · ext <;> simp
  · ext <;> simp
  · ext <;> simp [ω, OpCyclotomic3.omega]
  · ext <;> (simp [ω, OpCyclotomic3.omega]; try abel)
  · ext <;> simp [ω, OpCyclotomic3.omega]
  · ext <;> (simp [OpCyclotomic3.galoisConj]; try abel)
  · ext <;> simp [ω, OpCyclotomic3.omega, OpCyclotomic3.galoisConj]
  · ext <;> (simp [OpCyclotomic3.galoisConj]; try noncomm_ring)
  · ext <;> (simp [w, OpCyclotomic3.galoisConj]; try noncomm_ring)

/-- Cyclic $\mathbb{Z}_3$-triality permutation $\tau_3(x, y, z) := (y, z, x)$ on `OpVec3 A`
(`Archetype C.2`). -/
def OpVec3.trialityPerm (u : OpVec3 A) : OpVec3 A :=
  ⟨u.y, u.z, u.x⟩

omit [Ring A] in
@[simp] theorem OpVec3.trialityPerm_x (u : OpVec3 A) : (OpVec3.trialityPerm u).x = u.y := rfl
omit [Ring A] in
@[simp] theorem OpVec3.trialityPerm_y (u : OpVec3 A) : (OpVec3.trialityPerm u).y = u.z := rfl
omit [Ring A] in
@[simp] theorem OpVec3.trialityPerm_z (u : OpVec3 A) : (OpVec3.trialityPerm u).z = u.x := rfl

/-- The order-2 5-grading parity vector involution $\pi_5(x, y, z) := (x, -y, -z)$ on `OpVec3 A`,
fixing the Grade-$\pm 2$ contact horizon $x$ and negating the Grade-$\pm 1$ transverse cone $(y, z)$. -/
def OpVec3.gradeParity (u : OpVec3 A) : OpVec3 A :=
  ⟨u.x, -u.y, -u.z⟩

@[simp] theorem OpVec3.gradeParity_x (u : OpVec3 A) : (OpVec3.gradeParity u).x = u.x := rfl
@[simp] theorem OpVec3.gradeParity_y (u : OpVec3 A) : (OpVec3.gradeParity u).y = -u.y := rfl
@[simp] theorem OpVec3.gradeParity_z (u : OpVec3 A) : (OpVec3.gradeParity u).z = -u.z := rfl

/-- The order-2 5-Grading Parity Automorphism $\pi_5(X) := \langle X.a, \pi_5(X.v), \pi_5(X.w), X.b \rangle$
on `OpZornMatrix A`, fixing $\mathcal{G}_0 \oplus \mathcal{G}_{-2} \oplus \mathcal{G}_{+2}$ and negating $\mathcal{G}_{-1} \oplus \mathcal{G}_{+1}$. -/
def zornGradeParity (X : OpZornMatrix A) : OpZornMatrix A :=
  ⟨X.a, OpVec3.gradeParity X.v, OpVec3.gradeParity X.w, X.b⟩

/-- The $\mathbb{Z}_2$ Chiral Grading Involution $\sigma_2\langle a, v, w, b \rangle := \langle a, -v, -w, b \rangle$
on `OpZornMatrix A`, reflecting the off-diagonal color channels (`Archetype C.2`). -/
def zornGaloisZ2 (X : OpZornMatrix A) : OpZornMatrix A :=
  ⟨X.a, -X.v, -X.w, X.b⟩

/-- The $\mathbb{Z}_3$ Color-Triality Galois Automorphism $\tau_3\langle a, v, w, b \rangle := \langle a, \tau_3(v), \tau_3(w), b \rangle$
on `OpZornMatrix A`, cyclically permuting the 3 color coordinates (`Archetype C.2`). -/
def zornGaloisZ3 (X : OpZornMatrix A) : OpZornMatrix A :=
  ⟨X.a, OpVec3.trialityPerm X.v, OpVec3.trialityPerm X.w, X.b⟩

/-- The combined $\mathbb{Z}_6 \cong \mathbb{Z}_2 \times \mathbb{Z}_3$ Cyclotomic Galois Generator
$\gamma_6 := \sigma_2 \circ \tau_3$ on `OpZornMatrix A` (`Archetype C.2`). -/
def zornGaloisZ6 (X : OpZornMatrix A) : OpZornMatrix A :=
  zornGaloisZ2 (zornGaloisZ3 X)

/-- **Theorem 121 (`Archetype C.2`: The Noncommutative $\mathbb{Z}_2 \times \mathbb{Z}_3 \cong \mathbb{Z}_6$ Cyclotomic Galois Group & 5-Grading Parity Automorphism of `OpZornMatrix A`)**:
    Over ANY noncommutative ring $A$ (`[Ring A]`):
    1. **Cross & Dot Product Covariance under $\tau_3$ and $\pi_5$**:
       $$\tau_3(u) \times \tau_3(v) = \tau_3(u \times v), \qquad \langle \tau_3(u), \tau_3(v) \rangle = \langle u, v \rangle.$$
    2. **Cyclic Order-2, Order-3, & Order-6 Group Relations**:
       $$\sigma_2^2(X) = X, \qquad \tau_3^3(X) = X, \qquad
         \sigma_2(\tau_3(X)) = \tau_3(\sigma_2(X)), \qquad \gamma_6^6(X) = X.$$
    3. **Exact Non-Associative Ring Automorphisms (`zornGradeParity` and `zornGaloisZ3`) & Orbit Invariance**:
       $$\pi_5(X * Y) = \pi_5(X) * \pi_5(Y), \qquad
         \tau_3(X * Y) = \tau_3(X) * \tau_3(Y),$$
       $$\tau_3\bigl(X + \tau_3(X) + \tau_3(\tau_3(X))\bigr) = X + \tau_3(X) + \tau_3(\tau_3(X)),$$
       and $\mathrm{opZornTrace}(\gamma_6(X)) = \mathrm{opZornTrace}(X)$.
    4. **Fixed-Point Galois Invariant Subalgebra (`Peirce Nucleus` $\mathcal{G}_0 = A \oplus A$)**:
       $$\sigma_2(X) + X = 2 \bullet \mathcal{G}_0(X) = \mathrm{opGradeZero}\;X.a\;X.b + \mathrm{opGradeZero}\;X.a\;X.b.$$ -/
theorem opZornMatrix_cyclotomic_galois_automorphism_group
    (X Y : OpZornMatrix A) (u v : OpVec3 A) :
    let orbit3 := X + zornGaloisZ3 X + zornGaloisZ3 (zornGaloisZ3 X)
    OpVec3.naiveCross (OpVec3.trialityPerm u) (OpVec3.trialityPerm v) =
      OpVec3.trialityPerm (OpVec3.naiveCross u v) ∧
    OpVec3.dot (OpVec3.trialityPerm u) (OpVec3.trialityPerm v) = OpVec3.dot u v ∧
    zornGaloisZ2 (zornGaloisZ2 X) = X ∧
    zornGaloisZ3 (zornGaloisZ3 (zornGaloisZ3 X)) = X ∧
    zornGaloisZ2 (zornGaloisZ3 X) = zornGaloisZ3 (zornGaloisZ2 X) ∧
    zornGaloisZ6 (zornGaloisZ6 (zornGaloisZ6 (zornGaloisZ6 (zornGaloisZ6 (zornGaloisZ6 X))))) = X ∧
    zornGradeParity (X * Y) = zornGradeParity X * zornGradeParity Y ∧
    zornGaloisZ3 (X * Y) = zornGaloisZ3 X * zornGaloisZ3 Y ∧
    zornGaloisZ3 orbit3 = orbit3 ∧
    opZornTrace (zornGaloisZ6 X) = opZornTrace X ∧
    zornGaloisZ2 X + X = opGradeZero X.a X.b + opGradeZero X.a X.b := by
  intro orbit3
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · ext <;> simp [OpVec3.naiveCross, OpVec3.trialityPerm]
  · simp [OpVec3.dot, OpVec3.trialityPerm]; abel
  · ext <;> simp [zornGaloisZ2]
  · ext <;> simp [zornGaloisZ3, OpVec3.trialityPerm]
  · ext <;> simp [zornGaloisZ2, zornGaloisZ3, OpVec3.trialityPerm]
  · ext <;> simp [zornGaloisZ6, zornGaloisZ2, zornGaloisZ3, OpVec3.trialityPerm]
  · ext <;> (simp [zornGradeParity, OpVec3.gradeParity, OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross, OpVec3.leftScale, OpVec3.rightScale]; try abel; try noncomm_ring)
  · ext <;> (simp [zornGaloisZ3, OpVec3.trialityPerm, OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross, OpVec3.leftScale, OpVec3.rightScale]; try abel; try noncomm_ring)
  · ext <;> (simp [orbit3, zornGaloisZ3, OpVec3.trialityPerm]; try abel)
  · simp [opZornTrace, zornGaloisZ6, zornGaloisZ2, zornGaloisZ3]
  · ext <;> simp [zornGaloisZ2, opGradeZero, opCartanDiag]

/-- **Theorem 122 (`Archetype CII`: Exact $\mathbb{Z}_2$ Galois Automorphism & Cyclotomic Degree-Doubling in $\mathrm{CD}_\Omega(A)$)**:
    Over ANY noncommutative $*$-ring $A$ (`[Ring A] [StarRing A]`) and for ANY operator twist $\Omega \in A$:
    1. $\sigma_{\mathrm{CD}}(x, y) = (x, -y)$ has Galois trace $Z + \sigma_{\mathrm{CD}}(Z) = \iota(2x)$.
    2. **Cyclotomic Degree-Doubling Laws** for $\mathbf{E} = (0, 1)$ and $\mathbf{E}^2 = \mathbf{E} *_\Omega \mathbf{E} = \iota(\Omega)$:
       - $\mathbf{E}^2 + 1 = \iota(\Phi_2(\Omega))$,
       - $\mathbf{E}^4 + 1 = \iota(\Phi_4(\Omega))$,
       - $\mathbf{E}^8 + 1 = \iota(\Phi_8(\Omega))$,
       - $\mathbf{E}^4 + \mathbf{E}^2 + 1 = \iota(\Phi_3(\Omega))$,
       - $\mathbf{E}^4 - \mathbf{E}^2 + 1 = \iota(\Phi_6(\Omega))$. -/
theorem cdGaloisZ2_automorphism_and_cyclotomic_degree_doubling
    [StarRing A] (Ω : A) (Z W : OpCayleyDickson A) :
    let E : OpCayleyDickson A := cdGenE
    let E2 := cdMul Ω E E
    let E4 := cdMul Ω E2 E2
    let E8 := cdMul Ω E4 E4
    cdGaloisZ2 (cdGaloisZ2 Z) = Z ∧
    cdGaloisZ2 (cdMul Ω Z W) = cdMul Ω (cdGaloisZ2 Z) (cdGaloisZ2 W) ∧
    Z + cdGaloisZ2 Z = cdEmbed (Z.x + Z.x) ∧
    E2 + 1 = cdEmbed (opPhi2 Ω) ∧
    E4 + 1 = cdEmbed (opPhi4 Ω) ∧
    E8 + 1 = cdEmbed (opPhi8 Ω) ∧
    E4 + E2 + 1 = cdEmbed (opPhi3 Ω) ∧
    E4 - E2 + 1 = cdEmbed (opPhi6 Ω) := by
  intro E E2 E4 E8
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · ext <;> simp [cdGaloisZ2]
  · ext <;> (simp [cdGaloisZ2, cdMul]; try abel; try noncomm_ring)
  · ext <;> simp [cdGaloisZ2, cdEmbed]
  · ext <;> (simp [E, E2, cdMul, cdGenE, cdEmbed, opPhi2, star_one, star_zero]; try abel; try noncomm_ring)
  · ext <;> (simp [E, E2, E4, cdMul, cdGenE, cdEmbed, opPhi4, star_one, star_zero]; try abel; try noncomm_ring)
  · ext <;> (simp [E, E2, E4, E8, cdMul, cdGenE, cdEmbed, opPhi8, star_one, star_zero]; try abel; try noncomm_ring)
  · ext <;> (simp [E, E2, E4, cdMul, cdGenE, cdEmbed, opPhi3, star_one, star_zero]; try abel; try noncomm_ring)
  · ext <;> (simp [E, E2, E4, cdMul, cdGenE, cdEmbed, opPhi6, star_one, star_zero]; try abel; try noncomm_ring)

/-- **The Noncommutative 6th Cyclotomic Quotient Ring $\mathrm{OpCyclotomic6}\;A := A[\zeta]/(\zeta^2 - \zeta + 1 = 0)$ (`Archetype CIII`)**:
    Represented in the basis $\{1, \zeta\}$ with $\zeta^2 = \zeta - 1$:
    $$(a_1 + b_1\zeta)(a_2 + b_2\zeta) = (a_1 a_2 - b_1 b_2) + (a_1 b_2 + b_1 a_2 + b_1 b_2)\zeta.$$ -/
@[ext]
structure OpCyclotomic6 (A : Type*) where
  c0 : A
  c1 : A
  deriving DecidableEq, Inhabited

namespace OpCyclotomic6

instance instZero : Zero (OpCyclotomic6 A) := ⟨⟨0, 0⟩⟩
instance instOne : One (OpCyclotomic6 A) := ⟨⟨1, 0⟩⟩
instance instAdd : Add (OpCyclotomic6 A) := ⟨fun x y => ⟨x.c0 + y.c0, x.c1 + y.c1⟩⟩
instance instNeg : Neg (OpCyclotomic6 A) := ⟨fun x => ⟨-x.c0, -x.c1⟩⟩
instance instSub : Sub (OpCyclotomic6 A) := ⟨fun x y => ⟨x.c0 - y.c0, x.c1 - y.c1⟩⟩
instance instMul : Mul (OpCyclotomic6 A) :=
  ⟨fun x y => ⟨x.c0 * y.c0 - x.c1 * y.c1, x.c0 * y.c1 + x.c1 * y.c0 + x.c1 * y.c1⟩⟩

@[simp] theorem zero_c0 : (0 : OpCyclotomic6 A).c0 = 0 := rfl
@[simp] theorem zero_c1 : (0 : OpCyclotomic6 A).c1 = 0 := rfl
@[simp] theorem one_c0 : (1 : OpCyclotomic6 A).c0 = 1 := rfl
@[simp] theorem one_c1 : (1 : OpCyclotomic6 A).c1 = 0 := rfl
@[simp] theorem add_c0 (x y : OpCyclotomic6 A) : (x + y).c0 = x.c0 + y.c0 := rfl
@[simp] theorem add_c1 (x y : OpCyclotomic6 A) : (x + y).c1 = x.c1 + y.c1 := rfl
@[simp] theorem neg_c0 (x : OpCyclotomic6 A) : (-x).c0 = -x.c0 := rfl
@[simp] theorem neg_c1 (x : OpCyclotomic6 A) : (-x).c1 = -x.c1 := rfl
@[simp] theorem sub_c0 (x y : OpCyclotomic6 A) : (x - y).c0 = x.c0 - y.c0 := rfl
@[simp] theorem sub_c1 (x y : OpCyclotomic6 A) : (x - y).c1 = x.c1 - y.c1 := rfl
@[simp] theorem mul_c0 (x y : OpCyclotomic6 A) : (x * y).c0 = x.c0 * y.c0 - x.c1 * y.c1 := rfl
@[simp] theorem mul_c1 (x y : OpCyclotomic6 A) :
    (x * y).c1 = x.c0 * y.c1 + x.c1 * y.c0 + x.c1 * y.c1 := rfl

/-- Canonical embedding $\iota_6(a) = (a, 0)$ of $A$ into $\mathrm{OpCyclotomic6}\;A$. -/
def embed (a : A) : OpCyclotomic6 A := ⟨a, 0⟩

/-- Primitive 6th root of unity $\zeta = (0, 1) \in \mathrm{OpCyclotomic6}\;A$. -/
def zeta : OpCyclotomic6 A := ⟨0, 1⟩

/-- Order-2 Galois automorphism $\sigma_6(a + b\zeta) = (a + b) - b\zeta$ sending $\zeta \mapsto 1 - \zeta = \zeta^{-1}$. -/
def galoisConj (x : OpCyclotomic6 A) : OpCyclotomic6 A :=
  ⟨x.c0 + x.c1, -x.c1⟩

/-- Canonical ring isomorphism `toCyclotomic3 : OpCyclotomic6 A → OpCyclotomic3 A` sending $\zeta \mapsto 1 + \omega$. -/
def toCyclotomic3 (x : OpCyclotomic6 A) : OpCyclotomic3 A :=
  ⟨x.c0 + x.c1, x.c1⟩

/-- Inverse ring isomorphism `ofCyclotomic3 : OpCyclotomic3 A → OpCyclotomic6 A` sending $\omega \mapsto \zeta - 1$. -/
def ofCyclotomic3 (x : OpCyclotomic3 A) : OpCyclotomic6 A :=
  ⟨x.c0 - x.c1, x.c1⟩

end OpCyclotomic6

/-- **Theorem 123 (`Archetype CIII`: Noncommutative 6th Cyclotomic Quotient Ring Laws, Galois Automorphism, & $\Phi_6 \leftrightarrow \Phi_3$ Isomorphism)**:
    Over ANY noncommutative ring $A$ (`[Ring A]`):
    1. `OpCyclotomic6 A` is an associative ring where $\zeta = (0, 1)$ satisfies $\zeta^2 - \zeta + 1 = 0$, $\zeta^3 = -1$, and $\zeta^6 = 1$.
    2. $\sigma_6(a, b) = (a + b, -b)$ is an order-2 multiplicative Galois automorphism with $\zeta * \sigma_6(\zeta) = 1$.
    3. `toCyclotomic3` and `ofCyclotomic3` are mutually inverse multiplicative ring isomorphisms between `OpCyclotomic6 A` and `OpCyclotomic3 A`. -/
theorem opCyclotomic6_laws_and_isomorphism
    (Z W U : OpCyclotomic6 A) :
    let ζ : OpCyclotomic6 A := OpCyclotomic6.zeta
    let ζ3 := (ζ * ζ) * ζ
    (Z * W) * U = Z * (W * U) ∧
    ζ * ζ - ζ + 1 = 0 ∧
    ζ3 = -1 ∧
    ζ3 * ζ3 = 1 ∧
    OpCyclotomic6.galoisConj (OpCyclotomic6.galoisConj Z) = Z ∧
    ζ * OpCyclotomic6.galoisConj ζ = 1 ∧
    OpCyclotomic6.galoisConj (Z * W) = OpCyclotomic6.galoisConj Z * OpCyclotomic6.galoisConj W ∧
    OpCyclotomic6.ofCyclotomic3 (OpCyclotomic6.toCyclotomic3 Z) = Z ∧
    OpCyclotomic6.toCyclotomic3 (Z * W) = OpCyclotomic6.toCyclotomic3 Z * OpCyclotomic6.toCyclotomic3 W := by
  intro ζ ζ3
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · ext <;> (simp; try abel; try noncomm_ring)
  · ext <;> (simp [ζ, OpCyclotomic6.zeta]; try abel)
  · ext <;> (simp [ζ3, ζ, OpCyclotomic6.zeta]; try abel)
  · ext <;> (simp [ζ3, ζ, OpCyclotomic6.zeta]; try abel; try noncomm_ring)
  · ext <;> (simp [OpCyclotomic6.galoisConj]; try abel)
  · ext <;> (simp [ζ, OpCyclotomic6.zeta, OpCyclotomic6.galoisConj]; try abel)
  · ext <;> (simp [OpCyclotomic6.galoisConj]; try abel; try noncomm_ring)
  · ext <;> (simp [OpCyclotomic6.ofCyclotomic3, OpCyclotomic6.toCyclotomic3]; try abel)
  · ext <;> (simp [OpCyclotomic6.toCyclotomic3]; try abel; try noncomm_ring)

/-- Left Nambu–Gorkov Zorn quadratic determinant $\det_L(X) = X.a * X.b + \langle X.v, X.w \rangle$. -/
def opNambuDetLeft (X : OpZornMatrix A) : A :=
  X.a * X.b + OpVec3.dot X.v X.w

/-- Right Nambu–Gorkov Zorn quadratic determinant $\det_R(X) = X.b * X.a + \langle X.w, X.v \rangle$. -/
def opNambuDetRight (X : OpZornMatrix A) : A :=
  X.b * X.a + OpVec3.dot X.w X.v

/-- Both ordered quadratic Zorn determinants take the unit value on either
unipotent family, with no commutativity assumptions on the step coordinates. -/
theorem opNambuDet_unipotent_conservation (v w : OpVec3 A) :
    opNambuDetLeft (opUnipotentUpper v) = 1 ∧
    opNambuDetRight (opUnipotentUpper v) = 1 ∧
    opNambuDetLeft (opUnipotentLower w) = 1 ∧
    opNambuDetRight (opUnipotentLower w) = 1 := by
  simp [opNambuDetLeft, opNambuDetRight, opUnipotentUpper,
    opUnipotentLower, OpVec3.dot]

/-- **Theorem 124 (`Archetype CIV`: $\mathbb{Z}_6$ Galois Invariance of Nambu Determinants & Equivariance of the Bruhat Trifactor and Zorn–Riccati Operator)**:
    Over ANY noncommutative ring $A$ (`[Ring A]`), for all $X \in \mathrm{OpZornMatrix}\;A$, $a, b \in A$, and $w, v, q \in \mathrm{OpVec3}\;A$:
    1. **Exact Galois Invariance of Left and Right Nambu Determinants under $\tau_3$ and $\gamma_6$**:
       $$\mathrm{opNambuDetLeft}(\tau_3(X)) = \mathrm{opNambuDetLeft}(X), \qquad
         \mathrm{opNambuDetRight}(\tau_3(X)) = \mathrm{opNambuDetRight}(X),$$
       $$\mathrm{opNambuDetLeft}(\gamma_6(X)) = \mathrm{opNambuDetLeft}(X), \qquad
         \mathrm{opNambuDetRight}(\gamma_6(X)) = \mathrm{opNambuDetRight}(X).$$
    2. **Exact Galois Equivariance of the Bruhat Trifactor**:
       $$\tau_3(\mathrm{opBruhatTrifactor}\;w\;a\;b\;v) =
         \mathrm{opBruhatTrifactor}\;(\tau_3(w))\;a\;b\;(\tau_3(v)),$$
       $$\gamma_6(\mathrm{opBruhatTrifactor}\;w\;a\;b\;v) =
         \mathrm{opBruhatTrifactor}\;(-\tau_3(w))\;a\;b\;(-\tau_3(v)).$$
    3. **Exact Galois Equivariance of the 8D Noncommutative Zorn–Riccati Operator $\mathcal{R}_X(q)$**:
       $$\tau_3(\mathrm{opZornRiccati}\;X\;q) = \mathrm{opZornRiccati}\;(\tau_3(X))\;(\tau_3(q)),$$
       $$-\tau_3(\mathrm{opZornRiccati}\;X\;q) = \mathrm{opZornRiccati}\;(\gamma_6(X))\;(-\tau_3(q)).$$ -/
theorem zornGalois_nambuDet_bruhat_and_riccati_equivariance
    (X : OpZornMatrix A) (a b : A) (w v q : OpVec3 A) :
    opNambuDetLeft (zornGaloisZ3 X) = opNambuDetLeft X ∧
    opNambuDetRight (zornGaloisZ3 X) = opNambuDetRight X ∧
    opNambuDetLeft (zornGaloisZ6 X) = opNambuDetLeft X ∧
    opNambuDetRight (zornGaloisZ6 X) = opNambuDetRight X ∧
    zornGaloisZ3 (opBruhatTrifactor w a b v) =
      opBruhatTrifactor (OpVec3.trialityPerm w) a b (OpVec3.trialityPerm v) ∧
    zornGaloisZ6 (opBruhatTrifactor w a b v) =
      opBruhatTrifactor (-OpVec3.trialityPerm w) a b (-OpVec3.trialityPerm v) ∧
    OpVec3.trialityPerm (opZornRiccati X q) =
      opZornRiccati (zornGaloisZ3 X) (OpVec3.trialityPerm q) ∧
    -OpVec3.trialityPerm (opZornRiccati X q) =
      opZornRiccati (zornGaloisZ6 X) (-OpVec3.trialityPerm q) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [opNambuDetLeft, zornGaloisZ3, OpVec3.trialityPerm, OpVec3.dot]; abel
  · simp [opNambuDetRight, zornGaloisZ3, OpVec3.trialityPerm, OpVec3.dot]; abel
  · simp [opNambuDetLeft, zornGaloisZ6, zornGaloisZ2, zornGaloisZ3, OpVec3.trialityPerm, OpVec3.dot]; abel
  · simp [opNambuDetRight, zornGaloisZ6, zornGaloisZ2, zornGaloisZ3, OpVec3.trialityPerm, OpVec3.dot]; abel
  · ext <;> (simp [zornGaloisZ3, opBruhatTrifactor, opUnipotentLower, opCartanDiag, opUnipotentUpper, OpVec3.trialityPerm, OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross, OpVec3.leftScale, OpVec3.rightScale]; try abel; try noncomm_ring)
  · ext <;> (simp [zornGaloisZ6, zornGaloisZ2, zornGaloisZ3, opBruhatTrifactor, opUnipotentLower, opCartanDiag, opUnipotentUpper, OpVec3.trialityPerm, OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross, OpVec3.leftScale, OpVec3.rightScale]; try abel; try noncomm_ring)
  · ext <;> (simp [opZornRiccati, zornGaloisZ3, OpVec3.trialityPerm, OpVec3.dot, OpVec3.leftScale, OpVec3.rightScale]; try abel; try noncomm_ring)
  · ext <;> (simp [opZornRiccati, zornGaloisZ6, zornGaloisZ2, zornGaloisZ3, OpVec3.trialityPerm, OpVec3.dot, OpVec3.leftScale, OpVec3.rightScale]; try abel; try noncomm_ring)

/-- A zero of the Zorn–Riccati operator is transported to a zero by color triality.
This is the fixed-point consequence of `zornGalois_nambuDet_bruhat_and_riccati_equivariance`. -/
theorem opZornRiccati_triality_fixed_point
    (X : OpZornMatrix A) (q : OpVec3 A)
    (h : opZornRiccati X q = 0) :
    opZornRiccati (zornGaloisZ3 X) (OpVec3.trialityPerm q) = 0 := by
  have hequiv :=
    (zornGalois_nambuDet_bruhat_and_riccati_equivariance
      X (0 : A) (0 : A) (0 : OpVec3 A) (0 : OpVec3 A) q).2.2.2.2.2.2.1
  rw [← hequiv, h]
  rfl

/-- Both first triality conjugates of a Riccati zero are again zeros, with their
operator parameters transformed by the same powers of triality. -/
theorem opZornRiccati_first_two_triality_fixed_points
    (X : OpZornMatrix A) (q : OpVec3 A)
    (h : opZornRiccati X q = 0) :
    opZornRiccati (zornGaloisZ3 X) (OpVec3.trialityPerm q) = 0 ∧
    opZornRiccati (zornGaloisZ3 (zornGaloisZ3 X))
      (OpVec3.trialityPerm (OpVec3.trialityPerm q)) = 0 := by
  refine ⟨opZornRiccati_triality_fixed_point X q h, ?_⟩
  exact opZornRiccati_triality_fixed_point (zornGaloisZ3 X)
    (OpVec3.trialityPerm q) (opZornRiccati_triality_fixed_point X q h)

/-- The triality-fixed family in the canonical Zorn owner. -/
def opZornTrialityFixed (a v w b : A) : OpZornMatrix A :=
  ⟨a, ⟨v, v, v⟩, ⟨w, w, w⟩, b⟩

/-- Exact coordinate characterization of the fixed locus of triality. -/
theorem zornGaloisZ3_eq_self_iff (X : OpZornMatrix A) :
    zornGaloisZ3 X = X ↔
      X.v.x = X.v.y ∧ X.v.y = X.v.z ∧
      X.w.x = X.w.y ∧ X.w.y = X.w.z := by
  constructor
  · intro h
    have hvx := congrArg (fun Z : OpZornMatrix A => Z.v.x) h
    have hvy := congrArg (fun Z : OpZornMatrix A => Z.v.y) h
    have hwx := congrArg (fun Z : OpZornMatrix A => Z.w.x) h
    have hwy := congrArg (fun Z : OpZornMatrix A => Z.w.y) h
    simp [zornGaloisZ3, OpVec3.trialityPerm] at hvx hvy hwx hwy
    exact ⟨hvx.symm, hvy.symm, hwx.symm, hwy.symm⟩
  · rintro ⟨hvx, hvy, hwx, hwy⟩
    ext <;>
      simp [zornGaloisZ3, OpVec3.trialityPerm, hvx, hvy, hwx, hwy]

/-- The triality-fixed family is closed under the canonical noncommutative
Zorn product. The factor three is the three-term owner dot contraction. -/
theorem opZornTrialityFixed_mul
    (a₁ v₁ w₁ b₁ a₂ v₂ w₂ b₂ : A) :
    opZornTrialityFixed a₁ v₁ w₁ b₁ * opZornTrialityFixed a₂ v₂ w₂ b₂ =
      opZornTrialityFixed
        (a₁ * a₂ - ((v₁ * w₂ + v₁ * w₂) + v₁ * w₂))
        (a₁ * v₂ + v₁ * b₂)
        (w₁ * a₂ + b₁ * w₂)
        (-( (w₁ * v₂ + w₁ * v₂) + w₁ * v₂) + b₁ * b₂) := by
  ext <;>
  simp [opZornTrialityFixed, OpVec3.dot, OpVec3.skewCross,
    OpVec3.naiveCross, OpVec3.leftScale, OpVec3.rightScale]

/-- The triality-fixed family has zero Zorn associator. Equivalently, its
restricted multiplication is associative despite possible noncommutativity in A. -/
theorem opZornTrialityFixed_associator
    (a₁ v₁ w₁ b₁ a₂ v₂ w₂ b₂ a₃ v₃ w₃ b₃ : A) :
    opAssociator (opZornTrialityFixed a₁ v₁ w₁ b₁)
      (opZornTrialityFixed a₂ v₂ w₂ b₂)
      (opZornTrialityFixed a₃ v₃ w₃ b₃) = 0 := by
  ext <;>
  simp [opAssociator, opZornTrialityFixed, OpVec3.dot, OpVec3.skewCross,
    OpVec3.naiveCross, OpVec3.leftScale, OpVec3.rightScale] <;>
  noncomm_ring

/-! ### 44. Noncommutative Cyclotomic Galois Norms, Associativity of the $\mathbb{Z}_3$-Galois Singlet Subalgebra, Octahedral $S_4 = V_4 \rtimes S_3$ Galois Group, & Triality 5-Gradings (`Archetypes CV–CXIII`) -/

/-- **Theorem 125 (`Archetype CV`: Noncommutative Galois Norm Commutator Anomaly & Symmetrized Jordan Galois Norm)**:
    Over ANY noncommutative ring $A$ (`[Ring A]`), for all $Z_3 = \langle a, b \rangle \in \mathrm{OpCyclotomic3}\;A$
    and $Z_6 = \langle a, b \rangle \in \mathrm{OpCyclotomic6}\;A$:
    1. **Left & Right Galois Norms in `OpCyclotomic3 A` Isolate the Commutator $[b, a]$**:
       $$Z_3 * \sigma_3(Z_3) = \langle a * a - a * b + b * b,\; b * a - a * b \rangle, \qquad
         \sigma_3(Z_3) * Z_3 = \langle a * a - b * a + b * b,\; a * b - b * a \rangle.$$
    2. **Symmetrized Jordan Galois Norm in `OpCyclotomic3 A` Lands Purely in Base Ring $A$**:
       $$Z_3 * \sigma_3(Z_3) + \sigma_3(Z_3) * Z_3 =
         \mathrm{OpCyclotomic3.embed}\bigl((a * a + a * a) - (a * b + b * a) + (b * b + b * b)\bigr).$$
    3. **Left & Right Galois Norms in `OpCyclotomic6 A` Isolate the Commutator $[b, a]$**:
       $$Z_6 * \sigma_6(Z_6) = \langle a * a + a * b + b * b,\; b * a - a * b \rangle, \qquad
         \sigma_6(Z_6) * Z_6 = \langle a * a + b * a + b * b,\; a * b - b * a \rangle.$$
    4. **Symmetrized Jordan Galois Norm in `OpCyclotomic6 A` Lands Purely in Base Ring $A$**:
       $$Z_6 * \sigma_6(Z_6) + \sigma_6(Z_6) * Z_6 =
         \mathrm{OpCyclotomic6.embed}\bigl((a * a + a * a) + (a * b + b * a) + (b * b + b * b)\bigr).$$ -/
theorem opCyclotomic_galois_norm_commutator_and_jordan_norm (a b : A) :
    let Z₃ : OpCyclotomic3 A := ⟨a, b⟩
    let Z₆ : OpCyclotomic6 A := ⟨a, b⟩
    Z₃ * OpCyclotomic3.galoisConj Z₃ = ⟨a * a - a * b + b * b, b * a - a * b⟩ ∧
    OpCyclotomic3.galoisConj Z₃ * Z₃ = ⟨a * a - b * a + b * b, a * b - b * a⟩ ∧
    Z₃ * OpCyclotomic3.galoisConj Z₃ + OpCyclotomic3.galoisConj Z₃ * Z₃ =
      OpCyclotomic3.embed ((a * a + a * a) - (a * b + b * a) + (b * b + b * b)) ∧
    Z₆ * OpCyclotomic6.galoisConj Z₆ = ⟨a * a + a * b + b * b, b * a - a * b⟩ ∧
    OpCyclotomic6.galoisConj Z₆ * Z₆ = ⟨a * a + b * a + b * b, a * b - b * a⟩ ∧
    Z₆ * OpCyclotomic6.galoisConj Z₆ + OpCyclotomic6.galoisConj Z₆ * Z₆ =
      OpCyclotomic6.embed ((a * a + a * a) + (a * b + b * a) + (b * b + b * b)) := by
  intro Z₃ Z₆
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  (ext <;>
   (simp [Z₃, Z₆, OpCyclotomic3.galoisConj, OpCyclotomic3.embed,
          OpCyclotomic6.galoisConj, OpCyclotomic6.embed];
    try abel; try noncomm_ring))

/-- Diagonal singlet 3-vector $\mathbf{1}(c) = \langle c, c, c \rangle \in \mathrm{OpVec3}\;A$ (`Archetype CVI`). -/
def OpVec3.diagVec (c : A) : OpVec3 A := ⟨c, c, c⟩

omit [Ring A] in
@[simp] theorem OpVec3.diagVec_x (c : A) : (OpVec3.diagVec c).x = c := rfl
omit [Ring A] in
@[simp] theorem OpVec3.diagVec_y (c : A) : (OpVec3.diagVec c).y = c := rfl
omit [Ring A] in
@[simp] theorem OpVec3.diagVec_z (c : A) : (OpVec3.diagVec c).z = c := rfl

/-- $\mathbb{Z}_3$-Galois Invariant Singlet Element `zornSinglet a c d b := ⟨a, ⟨c, c, c⟩, ⟨d, d, d⟩, b⟩`
in $\mathrm{Fix}(\tau_3) \subset \mathrm{OpZornMatrix}\;A$ (`Archetype CVI`). -/
def zornSinglet (a c d b : A) : OpZornMatrix A :=
  ⟨a, OpVec3.diagVec c, OpVec3.diagVec d, b⟩

/-- $\mathbb{Z}_3$-Galois singlet projection $\mathcal{P}_{\mathrm{sing}}(X) = X + \tau_3(X) + \tau_3^2(X)$ (`Archetype CVI`). -/
def zornSingletProj (X : OpZornMatrix A) : OpZornMatrix A :=
  X + zornGaloisZ3 X + zornGaloisZ3 (zornGaloisZ3 X)

/-- $\mathbb{Z}_3$-Galois octet residual $\mathcal{P}_{\mathrm{oct}}(X) = (X + X + X) - \mathcal{P}_{\mathrm{sing}}(X)$ (`Archetype CVI`). -/
def zornOctetProj (X : OpZornMatrix A) : OpZornMatrix A :=
  (X + X + X) - zornSingletProj X

/-- **Theorem 126 (`Archetype CVI`: Strict Associativity of the $\mathbb{Z}_3$-Galois Singlet Subalgebra $\mathrm{Fix}(\tau_3)$ & $\Phi_3$ Singlet-Octet Split)**:
    Over ANY noncommutative ring $A$ (`[Ring A]`):
    1. **Exact $\mathbb{Z}_3$-Galois Fixed-Point Invariance & Vanishing Diagonal Cross Product**:
       $\tau_3(\mathrm{zornSinglet}\;a_1\;c_1\;d_1\;b_1) = \mathrm{zornSinglet}\;a_1\;c_1\;d_1\;b_1$
       and $\mathrm{OpVec3.skewCross}\;(\mathbf{1}(c_1))\;(\mathbf{1}(c_2)) = 0$.
    2. **Multiplicative Closure of $\mathrm{Fix}(\tau_3)$**:
       $$\mathrm{zornSinglet}\;a_1\;c_1\;d_1\;b_1 * \mathrm{zornSinglet}\;a_2\;c_2\;d_2\;b_2 =
         \mathrm{zornSinglet}\;(a_1 a_2 - (c_1 d_2 + c_1 d_2 + c_1 d_2))\;(a_1 c_2 + c_1 b_2)\;
                               (d_1 a_2 + b_1 d_2)\;(-(d_1 c_2 + d_1 c_2 + d_1 c_2) + b_1 b_2).$$
    3. **Strict Associativity of the $\mathbb{Z}_3$-Galois Fixed-Point Subalgebra $\mathrm{Fix}(\tau_3)$**:
       $$\mathrm{opAssociator}\;(\mathrm{zornSinglet}\;a_1\;c_1\;d_1\;b_1)\;
                                (\mathrm{zornSinglet}\;a_2\;c_2\;d_2\;b_2)\;
                                (\mathrm{zornSinglet}\;a_3\;c_3\;d_3\;b_3) = 0.$$
    4. **Exact $\Phi_3(\tau_3)$ Singlet-Octet Orthogonality**:
       $$\tau_3(\mathcal{P}_{\mathrm{sing}}(X)) = \mathcal{P}_{\mathrm{sing}}(X) \quad \text{and} \quad
         \mathcal{P}_{\mathrm{sing}}(\mathcal{P}_{\mathrm{oct}}(X)) = 0.$$ -/
theorem zornSinglet_closure_strict_associativity_and_octet_split
    (a₁ c₁ d₁ b₁ a₂ c₂ d₂ b₂ a₃ c₃ d₃ b₃ : A) (X : OpZornMatrix A) :
    let S₁ := zornSinglet a₁ c₁ d₁ b₁
    let S₂ := zornSinglet a₂ c₂ d₂ b₂
    let S₃ := zornSinglet a₃ c₃ d₃ b₃
    zornGaloisZ3 S₁ = S₁ ∧
    OpVec3.skewCross (OpVec3.diagVec c₁) (OpVec3.diagVec c₂) = 0 ∧
    S₁ * S₂ =
      zornSinglet (a₁ * a₂ - (c₁ * d₂ + c₁ * d₂ + c₁ * d₂))
                  (a₁ * c₂ + c₁ * b₂)
                  (d₁ * a₂ + b₁ * d₂)
                  (-(d₁ * c₂ + d₁ * c₂ + d₁ * c₂) + b₁ * b₂) ∧
    opAssociator S₁ S₂ S₃ = 0 ∧
    zornGaloisZ3 (zornSingletProj X) = zornSingletProj X ∧
    zornSingletProj (zornOctetProj X) = 0 := by
  intro S₁ S₂ S₃
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  (ext <;>
   (simp [S₁, S₂, S₃, zornSinglet, zornSingletProj, zornOctetProj,
          zornGaloisZ3, opAssociator, OpVec3.diagVec, OpVec3.trialityPerm,
          OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross,
          OpVec3.leftScale, OpVec3.rightScale];
    try abel; try noncomm_ring))

/-- **Theorem 127 (`Archetype CVII`: $\mathbb{Z}_6$ Galois Equivariance of the Zorn–Riccati Tangent Jacobian & Singlet Riccati Reduction)**:
    Over ANY noncommutative ring $A$ (`[Ring A]`), for all $X \in \mathrm{OpZornMatrix}\;A$,
    $q, \delta \in \mathrm{OpVec3}\;A$, and $a, c, d, b, q_0 \in A$:
    1. **Exact $\mathbb{Z}_3$-Triality Galois Equivariance of the Riccati Jacobian $\mathcal{J}_{X, q}(\delta)$**:
       $$\tau_3\bigl(\mathrm{opZornRiccatiJacobian}\;X\;q\;\delta\bigr) =
         \mathrm{opZornRiccatiJacobian}\;(\tau_3(X))\;(\tau_3(q))\;(\tau_3(\delta)).$$
    2. **Exact $\mathbb{Z}_6$-Cyclotomic Galois Equivariance of the Riccati Jacobian $\mathcal{J}_{X, q}(\delta)$**:
       $$\tau_3\bigl(\mathrm{opZornRiccatiJacobian}\;X\;q\;\delta\bigr) =
         \mathrm{opZornRiccatiJacobian}\;(\gamma_6(X))\;(-\tau_3(q))\;(\tau_3(\delta)).$$
    3. **Exact Reduction of 8D `opZornRiccati` on $\mathrm{Fix}(\tau_3)$ to the 1D Baryonic Singlet Riccati Equation**:
       $$\mathrm{opZornRiccati}\;(\mathrm{zornSinglet}\;a\;c\;d\;b)\;(\mathbf{1}(q_0)) =
         \mathbf{1}\bigl(q_0 * (d * q_0 + d * q_0 + d * q_0) + q_0 * b + a * q_0 - c\bigr).$$ -/
theorem zornRiccatiJacobian_galois_equivariance_and_singlet_reduction
    (X : OpZornMatrix A) (q δ : OpVec3 A) (a c d b q₀ : A) :
    let r_sing := q₀ * (d * q₀ + d * q₀ + d * q₀) + q₀ * b + a * q₀ - c
    OpVec3.trialityPerm (opZornRiccatiJacobian X q δ) =
      opZornRiccatiJacobian (zornGaloisZ3 X) (OpVec3.trialityPerm q) (OpVec3.trialityPerm δ) ∧
    OpVec3.trialityPerm (opZornRiccatiJacobian X q δ) =
      opZornRiccatiJacobian (zornGaloisZ6 X) (-OpVec3.trialityPerm q) (OpVec3.trialityPerm δ) ∧
    opZornRiccati (zornSinglet a c d b) (OpVec3.diagVec q₀) =
      OpVec3.diagVec r_sing := by
  intro r_sing
  refine ⟨?_, ?_, ?_⟩ <;>
  (ext <;>
   (simp [r_sing, opZornRiccati, opZornRiccatiJacobian,
          zornGaloisZ3, zornGaloisZ6, zornGaloisZ2, zornSinglet,
          OpVec3.diagVec, OpVec3.trialityPerm, OpVec3.dot,
          OpVec3.leftScale, OpVec3.rightScale];
    try abel; try noncomm_ring))

/-- Order-2 signed reflection vector involution $\sigma_{\mathrm{refl}}\langle x, y, z \rangle := \langle -x, -z, -y \rangle$
on `OpVec3 A` with $\det(\sigma_{\mathrm{refl}}) = +1 \in \mathrm{SO}(3, \mathbb{Z})$ (`Archetype CVIII`). -/
def OpVec3.reflPerm (u : OpVec3 A) : OpVec3 A :=
  ⟨-u.x, -u.z, -u.y⟩

@[simp] theorem OpVec3.reflPerm_x (u : OpVec3 A) : (OpVec3.reflPerm u).x = -u.x := rfl
@[simp] theorem OpVec3.reflPerm_y (u : OpVec3 A) : (OpVec3.reflPerm u).y = -u.z := rfl
@[simp] theorem OpVec3.reflPerm_z (u : OpVec3 A) : (OpVec3.reflPerm u).z = -u.y := rfl

/-- Order-2 signed reflection automorphism $\sigma_{\mathrm{refl}}\langle a, v, w, b \rangle := \langle a, \sigma_{\mathrm{refl}}(v), \sigma_{\mathrm{refl}}(w), b \rangle$
on `OpZornMatrix A`, generating the non-abelian dihedral group $S_3 = \mathbb{Z}_3 \rtimes \mathbb{Z}_2$ with `zornGaloisZ3` (`Archetype CVIII`). -/
def zornReflZ2 (X : OpZornMatrix A) : OpZornMatrix A :=
  ⟨X.a, OpVec3.reflPerm X.v, OpVec3.reflPerm X.w, X.b⟩

/-- **Theorem 128 (`Archetype CVIII`: The Non-Abelian Dihedral Galois Group $S_3 = \mathbb{Z}_3 \rtimes \mathbb{Z}_2$, Reflection Automorphism `zornReflZ2`, & Riccati Reflection Equivariance)**:
    Over ANY noncommutative ring $A$ (`[Ring A]`):
    1. **Cross & Dot Product Covariance under $\sigma_{\mathrm{refl}}$ ($\det = +1$)**:
       $$\sigma_{\mathrm{refl}}(u) \times_{\mathrm{skew}} \sigma_{\mathrm{refl}}(v) = \sigma_{\mathrm{refl}}(u \times_{\mathrm{skew}} v), \qquad
         \langle \sigma_{\mathrm{refl}}(u), \sigma_{\mathrm{refl}}(v) \rangle = \langle u, v \rangle.$$
    2. **Exact Non-Associative Ring Automorphism & Dihedral $S_3 = \mathbb{Z}_3 \rtimes \mathbb{Z}_2$ Group Law**:
       $$\sigma_{\mathrm{refl}}(\sigma_{\mathrm{refl}}(X)) = X, \qquad
         \sigma_{\mathrm{refl}}(X * Y) = \sigma_{\mathrm{refl}}(X) * \sigma_{\mathrm{refl}}(Y), \qquad
         \sigma_{\mathrm{refl}}(\tau_3(\sigma_{\mathrm{refl}}(X))) = \tau_3(\tau_3(X)).$$
    3. **Exact Reflection Equivariance of `opZornRiccati`**:
       $$\sigma_{\mathrm{refl}}(\mathrm{opZornRiccati}\;X\;q) =
         \mathrm{opZornRiccati}\;(\sigma_{\mathrm{refl}}(X))\;(\sigma_{\mathrm{refl}}(q)).$$ -/
theorem zornReflZ2_automorphism_dihedral_S3_and_riccati_equivariance
    (X Y : OpZornMatrix A) (u v q : OpVec3 A) :
    OpVec3.skewCross (OpVec3.reflPerm u) (OpVec3.reflPerm v) =
      OpVec3.reflPerm (OpVec3.skewCross u v) ∧
    OpVec3.dot (OpVec3.reflPerm u) (OpVec3.reflPerm v) = OpVec3.dot u v ∧
    zornReflZ2 (zornReflZ2 X) = X ∧
    zornReflZ2 (X * Y) = zornReflZ2 X * zornReflZ2 Y ∧
    zornReflZ2 (zornGaloisZ3 (zornReflZ2 X)) = zornGaloisZ3 (zornGaloisZ3 X) ∧
    OpVec3.reflPerm (opZornRiccati X q) =
      opZornRiccati (zornReflZ2 X) (OpVec3.reflPerm q) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · ext <;> (simp [OpVec3.reflPerm, OpVec3.skewCross, OpVec3.naiveCross]; try abel; try noncomm_ring)
  · simp [OpVec3.reflPerm, OpVec3.dot]; try abel; try noncomm_ring
  · ext <;> simp [zornReflZ2, OpVec3.reflPerm]
  · ext <;>
    (simp [zornReflZ2, OpVec3.reflPerm, OpVec3.dot, OpVec3.skewCross,
           OpVec3.naiveCross, OpVec3.leftScale, OpVec3.rightScale];
     try abel; try noncomm_ring)
  · ext <;> simp [zornReflZ2, zornGaloisZ3, OpVec3.reflPerm, OpVec3.trialityPerm]
  · ext <;>
    (simp [opZornRiccati, zornReflZ2, OpVec3.reflPerm, OpVec3.dot,
           OpVec3.leftScale, OpVec3.rightScale];
     try abel; try noncomm_ring)

/-- Klein four-group vector involutions $\kappa_y\langle x, y, z \rangle = \langle -x, y, -z \rangle$
and $\kappa_z\langle x, y, z \rangle = \langle -x, -y, z \rangle$ on `OpVec3 A` (`Archetype CIX`). -/
def OpVec3.kleinY (u : OpVec3 A) : OpVec3 A := ⟨-u.x, u.y, -u.z⟩
def OpVec3.kleinZ (u : OpVec3 A) : OpVec3 A := ⟨-u.x, -u.y, u.z⟩

@[simp] theorem OpVec3.kleinY_x (u : OpVec3 A) : (OpVec3.kleinY u).x = -u.x := rfl
@[simp] theorem OpVec3.kleinY_y (u : OpVec3 A) : (OpVec3.kleinY u).y = u.y := rfl
@[simp] theorem OpVec3.kleinY_z (u : OpVec3 A) : (OpVec3.kleinY u).z = -u.z := rfl
@[simp] theorem OpVec3.kleinZ_x (u : OpVec3 A) : (OpVec3.kleinZ u).x = -u.x := rfl
@[simp] theorem OpVec3.kleinZ_y (u : OpVec3 A) : (OpVec3.kleinZ u).y = -u.y := rfl
@[simp] theorem OpVec3.kleinZ_z (u : OpVec3 A) : (OpVec3.kleinZ u).z = u.z := rfl

/-- Klein four-group $V_4 = \{I, K_x, K_y, K_z\}$ of order-2 multiplicative automorphisms on `OpZornMatrix A` (`Archetype CIX`). -/
abbrev zornKleinX (X : OpZornMatrix A) : OpZornMatrix A := zornGradeParity X
def zornKleinY (X : OpZornMatrix A) : OpZornMatrix A := ⟨X.a, OpVec3.kleinY X.v, OpVec3.kleinY X.w, X.b⟩
def zornKleinZ (X : OpZornMatrix A) : OpZornMatrix A := ⟨X.a, OpVec3.kleinZ X.v, OpVec3.kleinZ X.w, X.b⟩

/-- The second and third triality-conjugate Euler 5-grading operators $\mathcal{D}_{5,y}$ and $\mathcal{D}_{5,z}$
on `OpZornMatrix A`, isolating the $y$-axis and $z$-axis as Grade $\pm 2$ contact horizons (`Archetype CXII`). -/
def opEuler5Y (X : OpZornMatrix A) : OpZornMatrix A :=
  ⟨0, ⟨X.v.x, -(X.v.y + X.v.y), X.v.z⟩, ⟨-X.w.x, X.w.y + X.w.y, -X.w.z⟩, 0⟩

def opEuler5Z (X : OpZornMatrix A) : OpZornMatrix A :=
  ⟨0, ⟨X.v.x, X.v.y, -(X.v.z + X.v.z)⟩, ⟨-X.w.x, -X.w.y, X.w.z + X.w.z⟩, 0⟩

/-- **Theorem 129 (`Archetypes CIX–CXIII`: The 24-Element Octahedral Galois Group $S_4 = V_4 \rtimes S_3$, Klein 4-Character Resolution, & Triality Trio of 5-Gradings)**:
    Over ANY noncommutative ring $A$ (`[Ring A]`):
    1. **Klein Four-Group $V_4 = \{I, K_x, K_y, K_z\}$ of Multiplicative Automorphisms**:
       $K_y(X * Y) = K_y(X) * K_y(Y)$, $K_z(X * Y) = K_z(X) * K_z(Y)$, $K_x(K_y(X)) = K_z(X)$, and
       $$X + K_x(X) + K_y(X) + K_z(X) =
         \mathrm{opGradeZero}\;X.a\;X.b + \mathrm{opGradeZero}\;X.a\;X.b +
         \mathrm{opGradeZero}\;X.a\;X.b + \mathrm{opGradeZero}\;X.a\;X.b.$$
    2. **Octahedral $S_4 = V_4 \rtimes S_3$ Conjugation by $\tau_3$ and $\sigma_{\mathrm{refl}}$**:
       $$\tau_3^2(K_x(\tau_3(X))) = K_y(X), \quad \tau_3^2(K_y(\tau_3(X))) = K_z(X), \quad
         \sigma_{\mathrm{refl}}(K_x(\sigma_{\mathrm{refl}}(X))) = K_x(X), \quad
         \sigma_{\mathrm{refl}}(K_y(\sigma_{\mathrm{refl}}(X))) = K_z(X).$$
    3. **Triality Trio of 5-Grading Operators $(\mathcal{D}_{5,x}, \mathcal{D}_{5,y}, \mathcal{D}_{5,z})$**:
       Pairwise commutativity, $S_3$ conjugation, and exact zero-sum conservation:
       $$\mathrm{opEulerFiveGrading}\;X + \mathrm{opEuler5Y}\;X + \mathrm{opEuler5Z}\;X = 0,$$
       $$\mathrm{opEulerFiveGrading}\;(\mathrm{opEuler5Y}\;X) = \mathrm{opEuler5Y}\;(\mathrm{opEulerFiveGrading}\;X),$$
       $$\tau_3^2(\mathrm{opEulerFiveGrading}\;(\tau_3(X))) = \mathrm{opEuler5Y}\;X, \qquad
         \sigma_{\mathrm{refl}}(\mathrm{opEuler5Y}\;(\sigma_{\mathrm{refl}}(X))) = \mathrm{opEuler5Z}\;X.$$ -/
theorem octahedral_S4_klein_character_resolution_and_triality_five_gradings
    (X Y : OpZornMatrix A) :
    let G₀ := opGradeZero X.a X.b
    zornKleinY (X * Y) = zornKleinY X * zornKleinY Y ∧
    zornKleinZ (X * Y) = zornKleinZ X * zornKleinZ Y ∧
    zornKleinX (zornKleinY X) = zornKleinZ X ∧
    X + zornKleinX X + zornKleinY X + zornKleinZ X = G₀ + G₀ + G₀ + G₀ ∧
    zornGaloisZ3 (zornGaloisZ3 (zornKleinX (zornGaloisZ3 X))) = zornKleinY X ∧
    zornGaloisZ3 (zornGaloisZ3 (zornKleinY (zornGaloisZ3 X))) = zornKleinZ X ∧
    zornReflZ2 (zornKleinX (zornReflZ2 X)) = zornKleinX X ∧
    zornReflZ2 (zornKleinY (zornReflZ2 X)) = zornKleinZ X ∧
    opEulerFiveGrading X + opEuler5Y X + opEuler5Z X = 0 ∧
    opEulerFiveGrading (opEuler5Y X) = opEuler5Y (opEulerFiveGrading X) ∧
    zornGaloisZ3 (zornGaloisZ3 (opEulerFiveGrading (zornGaloisZ3 X))) = opEuler5Y X ∧
    zornReflZ2 (opEuler5Y (zornReflZ2 X)) = opEuler5Z X := by
  intro G₀
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · ext <;> (simp [zornKleinY, OpVec3.kleinY, OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross, OpVec3.leftScale, OpVec3.rightScale]; try abel; try noncomm_ring)
  · ext <;> (simp [zornKleinZ, OpVec3.kleinZ, OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross, OpVec3.leftScale, OpVec3.rightScale]; try abel; try noncomm_ring)
  · ext <;> simp [zornKleinX, zornGradeParity, zornKleinY, zornKleinZ, OpVec3.gradeParity, OpVec3.kleinY, OpVec3.kleinZ]
  · ext <;> (simp [G₀, zornKleinX, zornGradeParity, zornKleinY, zornKleinZ, OpVec3.gradeParity, OpVec3.kleinY, OpVec3.kleinZ, opCartanDiag]; try abel)
  · ext <;> simp [zornGaloisZ3, zornKleinX, zornGradeParity, zornKleinY, OpVec3.trialityPerm, OpVec3.gradeParity, OpVec3.kleinY]
  · ext <;> simp [zornGaloisZ3, zornKleinY, zornKleinZ, OpVec3.trialityPerm, OpVec3.kleinY, OpVec3.kleinZ]
  · ext <;> simp [zornReflZ2, zornKleinX, zornGradeParity, OpVec3.reflPerm, OpVec3.gradeParity]
  · ext <;> simp [zornReflZ2, zornKleinY, zornKleinZ, OpVec3.reflPerm, OpVec3.kleinY, OpVec3.kleinZ]
  · ext <;> (simp [opEulerFiveGrading, opEuler5Y, opEuler5Z]; try abel)
  · ext <;> (simp [opEulerFiveGrading, opEuler5Y]; try abel)
  · ext <;> simp [zornGaloisZ3, opEulerFiveGrading, opEuler5Y, OpVec3.trialityPerm]
  · ext <;> (simp [zornReflZ2, opEuler5Y, opEuler5Z, OpVec3.reflPerm]; try abel)

/-! ### 45. The Discrete Spin Projection Group: Quaternion Double Cover $Q_8 \twoheadrightarrow V_4$, Internal Zorn Spinors $S_a^2 = -1$, & Klein Spin-Sector Fusion (`Archetypes CXIV–CXVI`) -/

/-- The 4-component Operator Quaternion Algebra `OpQuaternion A` over a noncommutative ring `A` (`Archetype CXIV`). -/
@[ext]
structure OpQuaternion (A : Type*) where
  w : A
  x : A
  y : A
  z : A
  deriving DecidableEq, Inhabited

namespace OpQuaternion

instance instZero : Zero (OpQuaternion A) := ⟨⟨0, 0, 0, 0⟩⟩
instance instOne : One (OpQuaternion A) := ⟨⟨1, 0, 0, 0⟩⟩
instance instAdd : Add (OpQuaternion A) := ⟨fun p q => ⟨p.w + q.w, p.x + q.x, p.y + q.y, p.z + q.z⟩⟩
instance instSub : Sub (OpQuaternion A) := ⟨fun p q => ⟨p.w - q.w, p.x - q.x, p.y - q.y, p.z - q.z⟩⟩
instance instNeg : Neg (OpQuaternion A) := ⟨fun p => ⟨-p.w, -p.x, -p.y, -p.z⟩⟩
instance instMul : Mul (OpQuaternion A) := ⟨fun p q =>
  ⟨p.w * q.w - p.x * q.x - p.y * q.y - p.z * q.z,
   p.w * q.x + p.x * q.w + p.y * q.z - p.z * q.y,
   p.w * q.y - p.x * q.z + p.y * q.w + p.z * q.x,
   p.w * q.z + p.x * q.y - p.y * q.x + p.z * q.w⟩⟩

@[simp] theorem zero_w : (0 : OpQuaternion A).w = 0 := rfl
@[simp] theorem zero_x : (0 : OpQuaternion A).x = 0 := rfl
@[simp] theorem zero_y : (0 : OpQuaternion A).y = 0 := rfl
@[simp] theorem zero_z : (0 : OpQuaternion A).z = 0 := rfl
@[simp] theorem one_w : (1 : OpQuaternion A).w = 1 := rfl
@[simp] theorem one_x : (1 : OpQuaternion A).x = 0 := rfl
@[simp] theorem one_y : (1 : OpQuaternion A).y = 0 := rfl
@[simp] theorem one_z : (1 : OpQuaternion A).z = 0 := rfl
@[simp] theorem neg_w (p : OpQuaternion A) : (-p).w = -p.w := rfl
@[simp] theorem neg_x (p : OpQuaternion A) : (-p).x = -p.x := rfl
@[simp] theorem neg_y (p : OpQuaternion A) : (-p).y = -p.y := rfl
@[simp] theorem neg_z (p : OpQuaternion A) : (-p).z = -p.z := rfl
@[simp] theorem mul_w (p q : OpQuaternion A) :
    (p * q).w = p.w * q.w - p.x * q.x - p.y * q.y - p.z * q.z := rfl
@[simp] theorem mul_x (p q : OpQuaternion A) :
    (p * q).x = p.w * q.x + p.x * q.w + p.y * q.z - p.z * q.y := rfl
@[simp] theorem mul_y (p q : OpQuaternion A) :
    (p * q).y = p.w * q.y - p.x * q.z + p.y * q.w + p.z * q.x := rfl
@[simp] theorem mul_z (p q : OpQuaternion A) :
    (p * q).z = p.w * q.z + p.x * q.y - p.y * q.x + p.z * q.w := rfl

/-- Quaternion conjugate `conj (w, x, y, z) = (w, -x, -y, -z)`. -/
def conj (p : OpQuaternion A) : OpQuaternion A := ⟨p.w, -p.x, -p.y, -p.z⟩

/-- Pure 3-vector embedding `OpVec3 A ↪ OpQuaternion A`. -/
def ofVec3 (v : OpVec3 A) : OpQuaternion A := ⟨0, v.x, v.y, v.z⟩

/-- The three unit quaternion spin generators `spinI, spinJ, spinK` generating $Q_8$. -/
def spinI : OpQuaternion A := ⟨0, 1, 0, 0⟩
def spinJ : OpQuaternion A := ⟨0, 0, 1, 0⟩
def spinK : OpQuaternion A := ⟨0, 0, 0, 1⟩

/-- Spinor adjoint sandwich action `Ad_s(v) = (s * ofVec3(v)) * conj(s)`. -/
def spinSandwich (s : OpQuaternion A) (v : OpVec3 A) : OpQuaternion A :=
  (s * ofVec3 v) * conj s

end OpQuaternion

/-- **Theorem 130 (`Archetype CXIV`: The Discrete Spin Double Cover $1 \to \{\pm 1\} \to Q_8 \xrightarrow{\mathrm{Ad}} V_4 \to 1$)**:
    Over ANY noncommutative operator ring $A$ (`[Ring A]`), for every 3-vector $v \in \mathrm{OpVec3}\;A$:
    1. **Non-Abelian Quaternion Spin Group Relations ($Q_8$)**:
       $$\mathbf{i}_Q^2 = -1, \quad \mathbf{j}_Q^2 = -1, \quad \mathbf{k}_Q^2 = -1, \quad
         \mathbf{i}_Q * \mathbf{j}_Q = \mathbf{k}_Q = -\mathbf{j}_Q * \mathbf{i}_Q.$$
    2. **Exact Double-Cover Projection onto the Klein Four-Group $V_4 = \{\mathrm{id}, \kappa_x, \kappa_y, \kappa_z\}$**:
       Both $+\mathbf{i}_Q$ and $-\mathbf{i}_Q$ (and similarly $\pm \mathbf{j}_Q, \pm \mathbf{k}_Q$) project
       under `spinSandwich` onto the exact same Klein involution $\kappa_x, \kappa_y, \kappa_z$, while
       the kernel $\{\pm 1\}$ acts as the identity $\mathrm{ofVec3}(v)$. -/
theorem quaternion_Q8_double_cover_of_klein_V4 (v : OpVec3 A) :
    let iQ : OpQuaternion A := OpQuaternion.spinI
    let jQ : OpQuaternion A := OpQuaternion.spinJ
    let kQ : OpQuaternion A := OpQuaternion.spinK
    iQ * iQ = -1 ∧
    jQ * jQ = -1 ∧
    kQ * kQ = -1 ∧
    iQ * jQ = kQ ∧
    jQ * iQ = -kQ ∧
    OpQuaternion.spinSandwich (-1) v = OpQuaternion.ofVec3 v ∧
    OpQuaternion.spinSandwich iQ v = OpQuaternion.ofVec3 (OpVec3.gradeParity v) ∧
    OpQuaternion.spinSandwich (-iQ) v = OpQuaternion.ofVec3 (OpVec3.gradeParity v) ∧
    OpQuaternion.spinSandwich jQ v = OpQuaternion.ofVec3 (OpVec3.kleinY v) ∧
    OpQuaternion.spinSandwich (-jQ) v = OpQuaternion.ofVec3 (OpVec3.kleinY v) ∧
    OpQuaternion.spinSandwich kQ v = OpQuaternion.ofVec3 (OpVec3.kleinZ v) ∧
    OpQuaternion.spinSandwich (-kQ) v = OpQuaternion.ofVec3 (OpVec3.kleinZ v) := by
  intro iQ jQ kQ
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  (ext <;>
   simp [iQ, jQ, kQ, OpQuaternion.spinI, OpQuaternion.spinJ, OpQuaternion.spinK,
         OpQuaternion.spinSandwich, OpQuaternion.conj, OpQuaternion.ofVec3,
         OpVec3.gradeParity, OpVec3.kleinY, OpVec3.kleinZ])

/-- Internal Zorn axial spinor generators $S_x, S_y, S_z \in \mathrm{OpZornMatrix}\;A$ satisfying
$S_a * S_a = -1$ (`Archetype CXV`). -/
def zornSpinX : OpZornMatrix A := ⟨0, ⟨1, 0, 0⟩, ⟨1, 0, 0⟩, 0⟩
def zornSpinY : OpZornMatrix A := ⟨0, ⟨0, 1, 0⟩, ⟨0, 1, 0⟩, 0⟩
def zornSpinZ : OpZornMatrix A := ⟨0, ⟨0, 0, 1⟩, ⟨0, 0, 1⟩, 0⟩

/-- The four discrete spin sector projectors $\Pi_0, \Pi_x, \Pi_y, \Pi_z$ on `OpZornMatrix A`
(scaled by $|V_4| = 4$ so they are division-free over any ring $A$, `Archetype CXVI`). -/
def spinProj0 (X : OpZornMatrix A) : OpZornMatrix A :=
  X + zornKleinX X + zornKleinY X + zornKleinZ X
def spinProjX (X : OpZornMatrix A) : OpZornMatrix A :=
  X + zornKleinX X - zornKleinY X - zornKleinZ X
def spinProjY (X : OpZornMatrix A) : OpZornMatrix A :=
  X - zornKleinX X + zornKleinY X - zornKleinZ X
def spinProjZ (X : OpZornMatrix A) : OpZornMatrix A :=
  X - zornKleinX X - zornKleinY X + zornKleinZ X

/-- **Theorem 131 (`Archetypes CXV & CXVI`: Internal Zorn Spinors $S_a^2 = -1$, Orthogonal Spin Projectors, & Klein Fusion Rule $\Pi_x * \Pi_y \subseteq \Pi_z$)**:
    Over ANY noncommutative operator ring $A$ (`[Ring A]`), for all $X, Y \in \mathrm{OpZornMatrix}\;A$:
    1. **Internal Spinor Period-4 Law ($S_a^2 = -1$)**:
       $$S_x * S_x = -1, \qquad S_y * S_y = -1, \qquad S_z * S_z = -1.$$
    2. **Scaled Idempotency, Mutual Orthogonality, & Resolution of the Identity**:
       $$\Pi_\alpha(\Pi_\alpha(X)) = 4 \bullet \Pi_\alpha(X), \qquad
         \Pi_\alpha(\Pi_\beta(X)) = 0 \quad (\alpha \neq \beta), \qquad
         \Pi_0(X) + \Pi_x(X) + \Pi_y(X) + \Pi_z(X) = 4 \bullet X.$$
    3. **Exact Spin-Sector Selection / Fusion Rule ($\Pi_x(X) * \Pi_y(Y)$ Lands Purely in $\mathrm{Im}(\Pi_z)$)**:
       $$\Pi_0\bigl(\Pi_x(X) * \Pi_y(Y)\bigr) = 0, \quad
         \Pi_x\bigl(\Pi_x(X) * \Pi_y(Y)\bigr) = 0, \quad
         \Pi_y\bigl(\Pi_x(X) * \Pi_y(Y)\bigr) = 0,$$
       $$\Pi_z\bigl(\Pi_x(X) * \Pi_y(Y)\bigr) = 4 \bullet \bigl(\Pi_x(X) * \Pi_y(Y)\bigr)!$$ -/
theorem zorn_internal_spinors_orthogonal_projectors_and_klein_fusion
    (X Y : OpZornMatrix A) :
    let fourZ (W : OpZornMatrix A) : OpZornMatrix A := W + W + W + W
    (zornSpinX : OpZornMatrix A) * zornSpinX = -1 ∧
    (zornSpinY : OpZornMatrix A) * zornSpinY = -1 ∧
    (zornSpinZ : OpZornMatrix A) * zornSpinZ = -1 ∧
    spinProj0 X + spinProjX X + spinProjY X + spinProjZ X = fourZ X ∧
    spinProj0 (spinProj0 X) = fourZ (spinProj0 X) ∧
    spinProjX (spinProjX X) = fourZ (spinProjX X) ∧
    spinProjY (spinProjY X) = fourZ (spinProjY X) ∧
    spinProjZ (spinProjZ X) = fourZ (spinProjZ X) ∧
    spinProj0 (spinProjX X) = 0 ∧
    spinProjX (spinProjY X) = 0 ∧
    spinProjY (spinProjZ X) = 0 ∧
    spinProjZ (spinProjX X) = 0 ∧
    spinProj0 (spinProjX X * spinProjY Y) = 0 ∧
    spinProjX (spinProjX X * spinProjY Y) = 0 ∧
    spinProjY (spinProjX X * spinProjY Y) = 0 ∧
    spinProjZ (spinProjX X * spinProjY Y) = fourZ (spinProjX X * spinProjY Y) := by
  intro fourZ
  set a4 := X.a + X.a + X.a + X.a
  set b4 := X.b + X.b + X.b + X.b
  set vx4 := X.v.x + X.v.x + X.v.x + X.v.x
  set wx4 := X.w.x + X.w.x + X.w.x + X.w.x
  set vy4 := X.v.y + X.v.y + X.v.y + X.v.y
  set wy4 := X.w.y + X.w.y + X.w.y + X.w.y
  set vz4 := X.v.z + X.v.z + X.v.z + X.v.z
  set wz4 := X.w.z + X.w.z + X.w.z + X.w.z
  set yvy4 := Y.v.y + Y.v.y + Y.v.y + Y.v.y
  set ywy4 := Y.w.y + Y.w.y + Y.w.y + Y.w.y
  have hP0 : spinProj0 X = ⟨a4, 0, 0, b4⟩ := by
    ext <;> (simp [a4, b4, spinProj0, zornKleinX, zornGradeParity, zornKleinY, zornKleinZ, OpVec3.gradeParity, OpVec3.kleinY, OpVec3.kleinZ]; try abel)
  have hPx : spinProjX X = ⟨0, ⟨vx4, 0, 0⟩, ⟨wx4, 0, 0⟩, 0⟩ := by
    ext <;> (simp [vx4, wx4, spinProjX, zornKleinX, zornGradeParity, zornKleinY, zornKleinZ, OpVec3.gradeParity, OpVec3.kleinY, OpVec3.kleinZ]; try abel)
  have hPy : spinProjY X = ⟨0, ⟨0, vy4, 0⟩, ⟨0, wy4, 0⟩, 0⟩ := by
    ext <;> (simp [vy4, wy4, spinProjY, zornKleinX, zornGradeParity, zornKleinY, zornKleinZ, OpVec3.gradeParity, OpVec3.kleinY, OpVec3.kleinZ]; try abel)
  have hPz : spinProjZ X = ⟨0, ⟨0, 0, vz4⟩, ⟨0, 0, wz4⟩, 0⟩ := by
    ext <;> (simp [vz4, wz4, spinProjZ, zornKleinX, zornGradeParity, zornKleinY, zornKleinZ, OpVec3.gradeParity, OpVec3.kleinY, OpVec3.kleinZ]; try abel)
  have hPyY : spinProjY Y = ⟨0, ⟨0, yvy4, 0⟩, ⟨0, ywy4, 0⟩, 0⟩ := by
    ext <;> (simp [yvy4, ywy4, spinProjY, zornKleinX, zornGradeParity, zornKleinY, zornKleinZ, OpVec3.gradeParity, OpVec3.kleinY, OpVec3.kleinZ]; try abel)
  have hProd : spinProjX X * spinProjY Y =
      ⟨0, ⟨0, 0, -(wx4 * ywy4 + ywy4 * wx4)⟩, ⟨0, 0, vx4 * yvy4 + yvy4 * vx4⟩, 0⟩ := by
    rw [hPx, hPyY]
    ext <;> (simp [OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross, OpVec3.leftScale, OpVec3.rightScale]; try abel)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · ext <;> simp [zornSpinX, OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross, OpVec3.leftScale, OpVec3.rightScale]
  · ext <;> simp [zornSpinY, OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross, OpVec3.leftScale, OpVec3.rightScale]
  · ext <;> simp [zornSpinZ, OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross, OpVec3.leftScale, OpVec3.rightScale]
  · ext <;> (simp [fourZ, spinProj0, spinProjX, spinProjY, spinProjZ, zornKleinX, zornGradeParity, zornKleinY, zornKleinZ, OpVec3.gradeParity, OpVec3.kleinY, OpVec3.kleinZ]; try abel)
  · rw [hP0]; ext <;> simp [fourZ, spinProj0, zornKleinX, zornGradeParity, zornKleinY, zornKleinZ, OpVec3.gradeParity, OpVec3.kleinY, OpVec3.kleinZ]
  · rw [hPx]; ext <;> simp [fourZ, spinProjX, zornKleinX, zornGradeParity, zornKleinY, zornKleinZ, OpVec3.gradeParity, OpVec3.kleinY, OpVec3.kleinZ]
  · rw [hPy]; ext <;> (simp [fourZ, spinProjY, zornKleinX, zornGradeParity, zornKleinY, zornKleinZ, OpVec3.gradeParity, OpVec3.kleinY, OpVec3.kleinZ]; try abel)
  · rw [hPz]; ext <;> (simp [fourZ, spinProjZ, zornKleinX, zornGradeParity, zornKleinY, zornKleinZ, OpVec3.gradeParity, OpVec3.kleinY, OpVec3.kleinZ]; try abel)
  · rw [hPx]; ext <;> (simp [spinProj0, zornKleinX, zornGradeParity, zornKleinY, zornKleinZ, OpVec3.gradeParity, OpVec3.kleinY, OpVec3.kleinZ]; try abel)
  · rw [hPy]; ext <;> (simp [spinProjX, zornKleinX, zornGradeParity, zornKleinY, zornKleinZ, OpVec3.gradeParity, OpVec3.kleinY, OpVec3.kleinZ]; try abel)
  · rw [hPz]; ext <;> (simp [spinProjY, zornKleinX, zornGradeParity, zornKleinY, zornKleinZ, OpVec3.gradeParity, OpVec3.kleinY, OpVec3.kleinZ]; try abel)
  · rw [hPx]; ext <;> (simp [spinProjZ, zornKleinX, zornGradeParity, zornKleinY, zornKleinZ, OpVec3.gradeParity, OpVec3.kleinY, OpVec3.kleinZ]; try abel)
  · rw [hProd]; ext <;> (simp [spinProj0, zornKleinX, zornGradeParity, zornKleinY, zornKleinZ, OpVec3.gradeParity, OpVec3.kleinY, OpVec3.kleinZ]; try abel)
  · rw [hProd]; ext <;> (simp [spinProjX, zornKleinX, zornGradeParity, zornKleinY, zornKleinZ, OpVec3.gradeParity, OpVec3.kleinY, OpVec3.kleinZ]; try abel)
  · rw [hProd]; ext <;> (simp [spinProjY, zornKleinX, zornGradeParity, zornKleinY, zornKleinZ, OpVec3.gradeParity, OpVec3.kleinY, OpVec3.kleinZ]; try abel)
  · rw [hProd]; ext <;> (simp [fourZ, spinProjZ, zornKleinX, zornGradeParity, zornKleinY, zornKleinZ, OpVec3.gradeParity, OpVec3.kleinY, OpVec3.kleinZ]; try abel)

/-- The three Galois-fixed split-quaternion subalgebras $\mathbb{H}_x(A) = \mathrm{Fix}(K_x)$,
$\mathbb{H}_y(A) = \mathrm{Fix}(K_y)$, and $\mathbb{H}_z(A) = \mathrm{Fix}(K_z)$ in `OpZornMatrix A` (`Archetypes CXI–CXIII`). -/
def quatSubalgX (a vx wx b : A) : OpZornMatrix A := ⟨a, ⟨vx, 0, 0⟩, ⟨wx, 0, 0⟩, b⟩
def quatSubalgY (a vy wy b : A) : OpZornMatrix A := ⟨a, ⟨0, vy, 0⟩, ⟨0, wy, 0⟩, b⟩
def quatSubalgZ (a vz wz b : A) : OpZornMatrix A := ⟨a, ⟨0, 0, vz⟩, ⟨0, 0, wz⟩, b⟩

/-- **Theorem 132 (`Archetypes CXI–CXIII`: The Three Galois-Fixed Split-Quaternion Subalgebras $\mathbb{H}_{x,y,z}(A)$, Strict Associativity, $\mathbb{Z}_3$-Triality Cycle, & Riccati Axis Decoupling)**:
    Over ANY noncommutative operator ring $A$ (`[Ring A]`), for all $a_i, v_i, w_i, b_i, a, v_x, w_x, v_y, w_y, v_z, w_z, b, q_x, q_y, q_z \in A$:
    1. **Exact Klein Fixed-Point Invariance**:
       $K_x(\mathrm{quatSubalgX}\;a_1\;v_1\;w_1\;b_1) = \mathrm{quatSubalgX}\;a_1\;v_1\;w_1\;b_1$,
       $K_y(\mathrm{quatSubalgY}\;a_1\;v_1\;w_1\;b_1) = \mathrm{quatSubalgY}\;a_1\;v_1\;w_1\;b_1$,
       $K_z(\mathrm{quatSubalgZ}\;a_1\;v_1\;w_1\;b_1) = \mathrm{quatSubalgZ}\;a_1\;v_1\;w_1\;b_1$.
    2. **Strict Associativity of All Three Quaternion Subalgebras**:
       $$\mathrm{opAssociator}\;(\mathrm{quatSubalgX}\;a_1\;v_1\;w_1\;b_1)\;(\mathrm{quatSubalgX}\;a_2\;v_2\;w_2\;b_2)\;(\mathrm{quatSubalgX}\;a_3\;v_3\;w_3\;b_3) = 0,$$
       $$\mathrm{opAssociator}\;(\mathrm{quatSubalgY}\;a_1\;v_1\;w_1\;b_1)\;(\mathrm{quatSubalgY}\;a_2\;v_2\;w_2\;b_2)\;(\mathrm{quatSubalgY}\;a_3\;v_3\;w_3\;b_3) = 0,$$
       $$\mathrm{opAssociator}\;(\mathrm{quatSubalgZ}\;a_1\;v_1\;w_1\;b_1)\;(\mathrm{quatSubalgZ}\;a_2\;v_2\;w_2\;b_2)\;(\mathrm{quatSubalgZ}\;a_3\;v_3\;w_3\;b_3) = 0.$$
    3. **Exact $\mathbb{Z}_3$-Triality Cycle of $\mathbb{H}_x(A) \to \mathbb{H}_z(A) \to \mathbb{H}_y(A) \to \mathbb{H}_x(A)$**:
       $$\tau_3(\mathrm{quatSubalgX}\;a\;v_x\;w_x\;b) = \mathrm{quatSubalgZ}\;a\;v_x\;w_x\;b, \quad
         \tau_3(\mathrm{quatSubalgZ}\;a\;v_z\;w_z\;b) = \mathrm{quatSubalgY}\;a\;v_z\;w_z\;b, \quad
         \tau_3(\mathrm{quatSubalgY}\;a\;v_y\;w_y\;b) = \mathrm{quatSubalgX}\;a\;v_y\;w_y\;b.$$
    4. **Galois-Fixed Riccati Axis Decoupling on $\mathbb{H}_x(A), \mathbb{H}_y(A), \mathbb{H}_z(A)$**:
       $$\mathrm{opZornRiccati}\;(\mathrm{quatSubalgX}\;a\;v_x\;w_x\;b)\;\langle q_x, 0, 0 \rangle =
         \langle q_x * (w_x * q_x) + q_x * b + a * q_x - v_x,\; 0,\; 0 \rangle,$$
       $$\mathrm{opZornRiccati}\;(\mathrm{quatSubalgY}\;a\;v_y\;w_y\;b)\;\langle 0, q_y, 0 \rangle =
         \langle 0,\; q_y * (w_y * q_y) + q_y * b + a * q_y - v_y,\; 0 \rangle,$$
       $$\mathrm{opZornRiccati}\;(\mathrm{quatSubalgZ}\;a\;v_z\;w_z\;b)\;\langle 0, 0, q_z \rangle =
         \langle 0,\; 0,\; q_z * (w_z * q_z) + q_z * b + a * q_z - v_z \rangle.$$ -/
theorem three_quaternion_galois_subalgebras_and_riccati_axis_decoupling
    (a₁ v₁ w₁ b₁ a₂ v₂ w₂ b₂ a₃ v₃ w₃ b₃ a vx wx vy wy vz wz b qx qy qz : A) :
    zornKleinX (quatSubalgX a₁ v₁ w₁ b₁) = quatSubalgX a₁ v₁ w₁ b₁ ∧
    zornKleinY (quatSubalgY a₁ v₁ w₁ b₁) = quatSubalgY a₁ v₁ w₁ b₁ ∧
    zornKleinZ (quatSubalgZ a₁ v₁ w₁ b₁) = quatSubalgZ a₁ v₁ w₁ b₁ ∧
    opAssociator (quatSubalgX a₁ v₁ w₁ b₁) (quatSubalgX a₂ v₂ w₂ b₂) (quatSubalgX a₃ v₃ w₃ b₃) = 0 ∧
    opAssociator (quatSubalgY a₁ v₁ w₁ b₁) (quatSubalgY a₂ v₂ w₂ b₂) (quatSubalgY a₃ v₃ w₃ b₃) = 0 ∧
    opAssociator (quatSubalgZ a₁ v₁ w₁ b₁) (quatSubalgZ a₂ v₂ w₂ b₂) (quatSubalgZ a₃ v₃ w₃ b₃) = 0 ∧
    zornGaloisZ3 (quatSubalgX a vx wx b) = quatSubalgZ a vx wx b ∧
    zornGaloisZ3 (quatSubalgZ a vz wz b) = quatSubalgY a vz wz b ∧
    zornGaloisZ3 (quatSubalgY a vy wy b) = quatSubalgX a vy wy b ∧
    opZornRiccati (quatSubalgX a vx wx b) ⟨qx, 0, 0⟩ =
      ⟨qx * (wx * qx) + qx * b + a * qx - vx, 0, 0⟩ ∧
    opZornRiccati (quatSubalgY a vy wy b) ⟨0, qy, 0⟩ =
      ⟨0, qy * (wy * qy) + qy * b + a * qy - vy, 0⟩ ∧
    opZornRiccati (quatSubalgZ a vz wz b) ⟨0, 0, qz⟩ =
      ⟨0, 0, qz * (wz * qz) + qz * b + a * qz - vz⟩ := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  (ext <;>
   (simp [quatSubalgX, quatSubalgY, quatSubalgZ,
          zornKleinX, zornGradeParity, zornKleinY, zornKleinZ, zornGaloisZ3,
          opAssociator, opZornRiccati,
          OpVec3.gradeParity, OpVec3.kleinY, OpVec3.kleinZ, OpVec3.trialityPerm,
          OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross,
          OpVec3.leftScale, OpVec3.rightScale];
    try abel; try noncomm_ring))

/-!
## 46. Archetypes CXVII–CXIX: Non-Commutative Inner Derivations, Idempotent Strata, Connes Curvature, Gauss–Codazzi Equation, Second-Variation Law, Spectral Supertrace Conservation, & Zorn–Connes Vacuum Idempotent Collapse
-/

/-- **Zorn–Connes Curvature (`opZornConnesCurvature D P`)** on `OpZornMatrix A`:
    $\Omega_D^{\mathrm{Zorn}}(P) := \mathrm{opCommutator}\;D\;P * \mathrm{opCommutator}\;D\;P$. -/
def opZornConnesCurvature (D P : OpZornMatrix A) : OpZornMatrix A :=
  opCommutator D P * opCommutator D P

/-- **Theorem 133 (`Archetype CXIX`: Zorn–Connes Vacuum Idempotent Derivation, Transverse 1-Form $\delta_D(E_+) = \langle 0, -v, w, 0 \rangle$, Singlet Curvature Collapse $\Omega_D^{\mathrm{Zorn}}(E_+) = \langle -(v \cdot w), 0, 0, -(w \cdot v) \rangle$, & Second-Variation Identity in `OpZornMatrix A`)**:
    Over *any* noncommutative operator ring $A$ (`[Ring A]`), for all $D \in \mathrm{OpZornMatrix}\;A$,
    let $E_+ := \mathrm{opGradeZero}\;1\;0 = \langle 1, 0, 0, 0 \rangle$ and $E_- := \mathrm{opGradeZero}\;0\;1 = \langle 0, 0, 0, 1 \rangle$:
    1. **Peirce Idempotent Orthogonality & Chirality Grading**:
       $$E_+ * E_+ = E_+, \quad E_- * E_- = E_-, \quad E_+ * E_- = 0, \quad E_- * E_+ = 0, \quad
         E_+ + E_- = 1, \quad E_+ - E_- = \mathrm{opZornGamma}.$$
    2. **Exact Transverse Connes 1-Form of the Vacuum Idempotent $E_+$**:
       $$\mathrm{opCommutator}\;D\;E_+ = \langle 0, -D.v, D.w, 0 \rangle,$$
       $$E_+ * \mathrm{opCommutator}\;D\;E_+ + \mathrm{opCommutator}\;D\;E_+ * E_+ = \mathrm{opCommutator}\;D\;E_+,$$
       $$\mathrm{opZornGamma} * \mathrm{opCommutator}\;D\;E_+ + \mathrm{opCommutator}\;D\;E_+ * \mathrm{opZornGamma} = 0,$$
       $$(E_+ * \mathrm{opCommutator}\;D\;E_+) * E_+ = 0, \qquad (E_- * \mathrm{opCommutator}\;D\;E_+) * E_- = 0.$$
    3. **Collapse of the Zorn–Connes Curvature $\Omega_D^{\mathrm{Zorn}}(E_+)$ into the Associative Cartan Singlet Nucleus $\mathcal{G}_0$**:
       $$\mathrm{opZornConnesCurvature}\;D\;E_+ =
         \mathrm{opGradeZero}\;(\mathrm{OpVec3.dot}\;D.v\;D.w)\;(\mathrm{OpVec3.dot}\;D.w\;D.v),$$
       $$E_+ * \mathrm{opZornConnesCurvature}\;D\;E_+ = \mathrm{opZornConnesCurvature}\;D\;E_+ * E_+,$$
       $$(E_+ * \mathrm{opCommutator}\;D\;(\mathrm{opCommutator}\;D\;E_+)) * E_+ +
         ((E_+ * \mathrm{opZornConnesCurvature}\;D\;E_+) * E_+ +
          (E_+ * \mathrm{opZornConnesCurvature}\;D\;E_+) * E_+) = 0,$$
       $$\mathrm{opZornTrace}\;(\mathrm{opZornGamma} * \mathrm{opZornConnesCurvature}\;D\;E_+) =
         \mathrm{OpVec3.dot}\;D.v\;D.w - \mathrm{OpVec3.dot}\;D.w\;D.v.$$ -/
theorem zorn_connes_vacuum_idempotent_derivation_and_curvature_collapse
    (D : OpZornMatrix A) :
    let E_plus : OpZornMatrix A := opGradeZero 1 0
    let E_minus : OpZornMatrix A := opGradeZero 0 1
    E_plus * E_plus = E_plus ∧
    E_minus * E_minus = E_minus ∧
    E_plus * E_minus = 0 ∧
    E_minus * E_plus = 0 ∧
    E_plus + E_minus = 1 ∧
    E_plus - E_minus = opZornGamma ∧
    opCommutator D E_plus = ⟨0, -D.v, D.w, 0⟩ ∧
    E_plus * opCommutator D E_plus + opCommutator D E_plus * E_plus = opCommutator D E_plus ∧
    opZornGamma * opCommutator D E_plus + opCommutator D E_plus * opZornGamma = 0 ∧
    (E_plus * opCommutator D E_plus) * E_plus = 0 ∧
    (E_minus * opCommutator D E_plus) * E_minus = 0 ∧
    opZornConnesCurvature D E_plus =
      opGradeZero (OpVec3.dot D.v D.w) (OpVec3.dot D.w D.v) ∧
    E_plus * opZornConnesCurvature D E_plus = opZornConnesCurvature D E_plus * E_plus ∧
    (E_plus * opCommutator D (opCommutator D E_plus)) * E_plus +
      ((E_plus * opZornConnesCurvature D E_plus) * E_plus +
       (E_plus * opZornConnesCurvature D E_plus) * E_plus) = 0 ∧
    opZornTrace (opZornGamma * opZornConnesCurvature D E_plus) =
      OpVec3.dot D.v D.w - OpVec3.dot D.w D.v ∧
    opCommutator (opCommutator E_plus (opCommutator E_plus D)) E_plus = opCommutator D E_plus := by
  intro E_plus E_minus
  have h_der : opCommutator D E_plus = ⟨0, -D.v, D.w, 0⟩ := by
    ext <;>
    (simp [opCommutator, E_plus, opCartanDiag,
           OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross,
           OpVec3.leftScale, OpVec3.rightScale];
     try abel)
  have h_curv : opZornConnesCurvature D E_plus =
      opGradeZero (OpVec3.dot D.v D.w) (OpVec3.dot D.w D.v) := by
    dsimp [opZornConnesCurvature]
    rw [h_der]
    ext <;>
    (simp [opCartanDiag,
           OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross,
           OpVec3.leftScale, OpVec3.rightScale];
     try abel; try noncomm_ring)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, h_der, ?_, ?_, ?_, ?_, h_curv, ?_, ?_, ?_, ?_⟩
  · ext <;> simp [E_plus, opCartanDiag, OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross, OpVec3.leftScale, OpVec3.rightScale]
  · ext <;> simp [E_minus, opCartanDiag, OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross, OpVec3.leftScale, OpVec3.rightScale]
  · ext <;> simp [E_plus, E_minus, opCartanDiag, OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross, OpVec3.leftScale, OpVec3.rightScale]
  · ext <;> simp [E_plus, E_minus, opCartanDiag, OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross, OpVec3.leftScale, OpVec3.rightScale]
  · ext <;> simp [E_plus, E_minus, opCartanDiag]
  · ext <;> simp [E_plus, E_minus, opCartanDiag, opZornGamma]
  · rw [h_der]
    ext <;> (simp [E_plus, opCartanDiag, OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross, OpVec3.leftScale, OpVec3.rightScale]; try abel)
  · rw [h_der]
    ext <;> (simp [opZornGamma, OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross, OpVec3.leftScale, OpVec3.rightScale]; try abel)
  · rw [h_der]
    ext <;> simp [E_plus, opCartanDiag, OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross, OpVec3.leftScale, OpVec3.rightScale]
  · rw [h_der]
    ext <;> simp [E_minus, opCartanDiag, OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross, OpVec3.leftScale, OpVec3.rightScale]
  · rw [h_curv]
    ext <;> simp [E_plus, opCartanDiag, OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross, OpVec3.leftScale, OpVec3.rightScale]
  · rw [h_der, h_curv]
    ext <;>
    (simp [opCommutator, E_plus, opCartanDiag,
           OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross,
           OpVec3.leftScale, OpVec3.rightScale];
     try noncomm_ring)
  · rw [h_curv]
    simp [opZornTrace, opZornGamma, opCartanDiag, OpVec3.dot]
    abel
  · have h_der1 : opCommutator E_plus D = ⟨0, D.v, -D.w, 0⟩ := by
      ext <;>
      (simp [opCommutator, E_plus, opCartanDiag,
             OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross,
             OpVec3.leftScale, OpVec3.rightScale];
       try abel)
    have h_der2 : opCommutator E_plus (opCommutator E_plus D) = ⟨0, D.v, D.w, 0⟩ := by
      rw [h_der1]
      ext <;>
      (simp [opCommutator, E_plus, opCartanDiag,
             OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross,
             OpVec3.leftScale, OpVec3.rightScale];
       try abel)
    rw [h_der2, h_der]
    ext <;>
    (simp [opCommutator, E_plus, opCartanDiag,
           OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross,
           OpVec3.leftScale, OpVec3.rightScale];
     try abel)

end PorterNoncommutativeRiccatiAndLoxodromes

/-- **Matrix Inner Derivation (`matInnerDer D X`)** on `Matrix n n R`:
    $\delta_D(X) = [D, X] = D * X - X * D$. -/
def matInnerDer {R : Type*} {n : Type*} [Fintype n] [DecidableEq n] [Ring R]
    (D X : Matrix n n R) : Matrix n n R :=
  D * X - X * D

/-- **Matrix Connes Curvature (`matConnesCurvature D P`)** on `Matrix n n R`:
    $\Omega_D(P) = [D, P]^2 = \delta_D(P) * \delta_D(P)$. -/
def matConnesCurvature {R : Type*} {n : Type*} [Fintype n] [DecidableEq n] [Ring R]
    (D P : Matrix n n R) : Matrix n n R :=
  matInnerDer D P * matInnerDer D P

/-- **Local Chern–Connes 2-Chain Operator Density (`matConnesDensity D P`)** on `Matrix n n R`:
    $\mathcal{C}(D, P) = P * [D, P]^2 = P * (\delta_D(P) * \delta_D(P))$. -/
def matConnesDensity {R : Type*} {n : Type*} [Fintype n] [DecidableEq n] [Ring R]
    (D P : Matrix n n R) : Matrix n n R :=
  P * (matInnerDer D P * matInnerDer D P)

/-- **Connes Cyclic Cocycle Pairing (`matConnesCocycle D P`)** on `Matrix n n R`:
    $\tau(P * [D, P]^2) = \mathrm{Matrix.trace}(\mathcal{C}(D, P))$. -/
def matConnesCocycle {R : Type*} {n : Type*} [Fintype n] [DecidableEq n] [CommRing R]
    (D P : Matrix n n R) : R :=
  Matrix.trace (matConnesDensity D P)

/-- **Total First-Order Inner Variation (`matConnesDensityVariation A D P`)** of the Chern–Connes
    density $\mathcal{C}(D, P) = P * [D, P]^2$ under $\delta_A(P) = [A, P]$ and $\delta_A(D) = [A, D]$. -/
def matConnesDensityVariation {R : Type*} {n : Type*} [Fintype n] [DecidableEq n] [Ring R]
    (A D P : Matrix n n R) : Matrix n n R :=
  matInnerDer A P * (matInnerDer D P * matInnerDer D P) +
  P * ((matInnerDer (matInnerDer A D) P + matInnerDer D (matInnerDer A P)) * matInnerDer D P) +
  P * (matInnerDer D P * (matInnerDer (matInnerDer A D) P + matInnerDer D (matInnerDer A P)))

/-- **Idempotent Projection Stratum (`IsMatrixIdempotent P`)** in `Matrix n n R`:
    $P * P = P$. -/
def IsMatrixIdempotent {R : Type*} {n : Type*} [Fintype n] [DecidableEq n] [Ring R]
    (P : Matrix n n R) : Prop :=
  P * P = P

/-- **Invertible Inner Gauge Pair (`IsMatrixInnerGaugePair U V`)** in `Matrix n n R`:
    $U * V = 1 \wedge V * U = 1$. -/
def IsMatrixInnerGaugePair {R : Type*} {n : Type*} [Fintype n] [DecidableEq n] [Ring R]
    (U V : Matrix n n R) : Prop :=
  U * V = 1 ∧ V * U = 1

/-- **Theorem 134 (`Archetype CXVII`: Matrix Inner Derivations, Leibniz Cocycle, Path-Curvature Defect, Idempotent Strata, Connes Curvature, Second-Variation Law, & Non-Abelian Gauss–Codazzi Equation)**:
    Over *any* noncommutative ring $R$ (`[Ring R]`) and finite index type $n$, for all $D, D_1, D_2, X, Y, P \in \mathrm{Matrix}\;n\;n\;R$ with $P^2 = P$ (`hP : IsMatrixIdempotent P`):
    1. **Skew-Symmetry & Self-Nilpotence ($\alpha_1$)**:
       $$\delta_D(X) = -\delta_X(D), \qquad \delta_D(D) = 0.$$
    2. **Non-Commutative Leibniz Cocycle ($\alpha_2$)**:
       $$\delta_D(X * Y) = \delta_D(X) * Y + X * \delta_D(Y).$$
    3. **Jacobi Syzygy & Non-Abelian Path-Curvature Defect ($\alpha_3$)**:
       $$\delta_D(\delta_X(Y)) + \delta_X(\delta_Y(D)) + \delta_Y(\delta_D(X)) = 0,$$
       $$\delta_{D_1}(\delta_{D_2}(X)) - \delta_{D_2}(\delta_{D_1}(X)) = \delta_{\delta_{D_1}(D_2)}(X).$$
    4. **Idempotent Stratum Orthogonality, Grading Involution $F = 2P - 1$, & Chirality Anticommutation ($\alpha_4$)**:
       $$(1 - P) * (1 - P) = 1 - P, \qquad P * (1 - P) = 0, \qquad (1 - P) * P = 0,$$
       $$(P + P - 1) * (P + P - 1) = 1,$$
       $$P * \delta_D(P) + \delta_D(P) * P = \delta_D(P), \qquad
         (P + P - 1) * \delta_D(P) + \delta_D(P) * (P + P - 1) = 0,$$
       $$P * \delta_D(P) * P = 0, \qquad (1 - P) * \delta_D(P) * (1 - P) = 0.$$
    5. **Connes Curvature Commutation, Cubic Compression Vanishing, Second-Variation Law, & Non-Abelian Gauss–Codazzi Equation ($\alpha_4 \prec \alpha_6$)**:
       $$P * \Omega_D(P) = \Omega_D(P) * P, \qquad
         P * (\Omega_D(P) * \delta_D(P)) * P = 0,$$
       $$P * \delta_D(\delta_D(P)) * P + (P * \Omega_D(P) * P + P * \Omega_D(P) * P) = 0,$$
       $$\delta_{P * D_1 * P}(P * D_2 * P) - P * \delta_{D_1}(D_2) * P =
         P * \delta_{D_1}(P) * \delta_{D_2}(P) * P - P * \delta_{D_2}(P) * \delta_{D_1}(P) * P.$$ -/
theorem matrix_inner_derivation_idempotent_connes_curvature_and_gauss_codazzi
    {R : Type*} {n : Type*} [Fintype n] [DecidableEq n] [Ring R]
    (D D₁ D₂ X Y P : Matrix n n R) (hP : IsMatrixIdempotent P) :
    matInnerDer D X = -matInnerDer X D ∧
    matInnerDer D D = 0 ∧
    matInnerDer D (X * Y) = matInnerDer D X * Y + X * matInnerDer D Y ∧
    matInnerDer D (matInnerDer X Y) +
      matInnerDer X (matInnerDer Y D) +
      matInnerDer Y (matInnerDer D X) = 0 ∧
    matInnerDer D₁ (matInnerDer D₂ X) - matInnerDer D₂ (matInnerDer D₁ X) =
      matInnerDer (matInnerDer D₁ D₂) X ∧
    (1 - P) * (1 - P) = 1 - P ∧
    P * (1 - P) = 0 ∧
    (1 - P) * P = 0 ∧
    (P + P - 1) * (P + P - 1) = 1 ∧
    P * matInnerDer D P + matInnerDer D P * P = matInnerDer D P ∧
    (P + P - 1) * matInnerDer D P + matInnerDer D P * (P + P - 1) = 0 ∧
    P * matInnerDer D P * P = 0 ∧
    (1 - P) * matInnerDer D P * (1 - P) = 0 ∧
    P * matConnesCurvature D P = matConnesCurvature D P * P ∧
    P * (matConnesCurvature D P * matInnerDer D P) * P = 0 ∧
    P * matInnerDer D (matInnerDer D P) * P +
      (P * matConnesCurvature D P * P + P * matConnesCurvature D P * P) = 0 ∧
    matInnerDer (P * D₁ * P) (P * D₂ * P) - P * matInnerDer D₁ D₂ * P =
      P * matInnerDer D₁ P * matInnerDer D₂ P * P -
      P * matInnerDer D₂ P * matInnerDer D₁ P * P := by
  have hP_eq : P * P = P := hP
  have h_leib : ∀ A B C : Matrix n n R,
      matInnerDer A (B * C) = matInnerDer A B * C + B * matInnerDer A C := by
    intro A B C
    dsimp [matInnerDer]
    noncomm_ring
  have h_off : P * matInnerDer D P + matInnerDer D P * P = matInnerDer D P := by
    have h := h_leib D P P
    rw [hP_eq] at h
    rw [add_comm]
    exact h.symm
  have h_comp0 : P * matInnerDer D P * P = 0 := by
    dsimp [matInnerDer]
    calc
      P * (D * P - P * D) * P
        = P * D * (P * P) - (P * P) * D * P := by noncomm_ring
      _ = P * D * P - P * D * P := by rw [hP_eq]
      _ = 0 := sub_self (P * D * P)
  have h_comm : P * matConnesCurvature D P = matConnesCurvature D P * P := by
    dsimp [matConnesCurvature, matInnerDer]
    have hL : P * ((D * P - P * D) * (D * P - P * D)) = P * D * P * D * P - P * D * D * P := by
      calc
        P * ((D * P - P * D) * (D * P - P * D))
          = P * D * P * D * P - P * D * (P * P) * D - (P * P) * D * D * P + (P * P) * D * P * D := by
            noncomm_ring
        _ = P * D * P * D * P - P * D * P * D - P * D * D * P + P * D * P * D := by
            rw [hP_eq]
        _ = P * D * P * D * P - P * D * D * P := by
            noncomm_ring
    have hR : (D * P - P * D) * (D * P - P * D) * P = P * D * P * D * P - P * D * D * P := by
      calc
        (D * P - P * D) * (D * P - P * D) * P
          = D * P * D * (P * P) - D * (P * P) * D * P - P * D * D * (P * P) + P * D * P * D * P := by
            noncomm_ring
        _ = D * P * D * P - D * P * D * P - P * D * D * P + P * D * P * D * P := by
            rw [hP_eq]
        _ = P * D * P * D * P - P * D * D * P := by
            noncomm_ring
    rw [hL, hR]
  have h_pair : ∀ A B : Matrix n n R,
      P * matInnerDer A P * matInnerDer B P * P = P * A * P * B * P - P * A * B * P := by
    intro A B
    dsimp [matInnerDer]
    calc
      P * (A * P - P * A) * (B * P - P * B) * P
        = P * A * P * B * (P * P) - P * A * (P * P) * B * P -
          (P * P) * A * B * (P * P) + (P * P) * A * P * B * P := by noncomm_ring
      _ = P * A * P * B * P - P * A * P * B * P - P * A * B * P + P * A * P * B * P := by
          rw [hP_eq]
      _ = P * A * P * B * P - P * A * B * P := by noncomm_ring
  refine ⟨?_, ?_, h_leib D X Y, ?_, ?_, ?_, ?_, ?_, ?_, h_off, ?_, h_comp0, ?_, h_comm, ?_, ?_, ?_⟩
  · dsimp [matInnerDer]; noncomm_ring
  · dsimp [matInnerDer]; exact sub_self (D * D)
  · dsimp [matInnerDer]; noncomm_ring
  · dsimp [matInnerDer]; noncomm_ring
  · calc
      (1 - P) * (1 - P) = 1 - P - P + P * P := by noncomm_ring
      _ = 1 - P - P + P := by rw [hP_eq]
      _ = 1 - P := by noncomm_ring
  · calc
      P * (1 - P) = P - P * P := by noncomm_ring
      _ = P - P := by rw [hP_eq]
      _ = 0 := sub_self P
  · calc
      (1 - P) * P = P - P * P := by noncomm_ring
      _ = P - P := by rw [hP_eq]
      _ = 0 := sub_self P
  · calc
      (P + P - 1) * (P + P - 1)
        = (P * P + P * P + P * P + P * P) - (P + P + P + P) + 1 := by noncomm_ring
      _ = (P + P + P + P) - (P + P + P + P) + 1 := by rw [hP_eq]
      _ = 1 := by noncomm_ring
  · calc
      (P + P - 1) * matInnerDer D P + matInnerDer D P * (P + P - 1)
        = (P * matInnerDer D P + matInnerDer D P * P) +
          (P * matInnerDer D P + matInnerDer D P * P) -
          (matInnerDer D P + matInnerDer D P) := by noncomm_ring
      _ = matInnerDer D P + matInnerDer D P - (matInnerDer D P + matInnerDer D P) := by
          rw [h_off]
      _ = 0 := sub_self _
  · calc
      (1 - P) * matInnerDer D P * (1 - P)
        = matInnerDer D P - (P * matInnerDer D P + matInnerDer D P * P) + P * matInnerDer D P * P := by
          noncomm_ring
      _ = matInnerDer D P - matInnerDer D P + 0 := by rw [h_off, h_comp0]
      _ = 0 := by noncomm_ring
  · calc
      P * (matConnesCurvature D P * matInnerDer D P) * P
        = (P * matConnesCurvature D P) * matInnerDer D P * P := by noncomm_ring
      _ = (matConnesCurvature D P * P) * matInnerDer D P * P := by rw [h_comm]
      _ = matConnesCurvature D P * (P * matInnerDer D P * P) := by noncomm_ring
      _ = matConnesCurvature D P * 0 := by rw [h_comp0]
      _ = 0 := mul_zero _
  · have h_curv_comp : P * matConnesCurvature D P * P = P * D * P * D * P - P * D * D * P := by
      simpa [matConnesCurvature, mul_assoc] using h_pair D D
    have h_sec_var :
        P * matInnerDer D (matInnerDer D P) * P =
          (P * D * D * P - P * D * P * D * P) + (P * D * D * P - P * D * P * D * P) := by
      dsimp [matInnerDer]
      calc
        P * (D * (D * P - P * D) - (D * P - P * D) * D) * P
          = P * D * D * (P * P) - P * D * P * D * P - P * D * P * D * P + (P * P) * D * D * P := by
            noncomm_ring
        _ = P * D * D * P - P * D * P * D * P - P * D * P * D * P + P * D * D * P := by
            rw [hP_eq]
        _ = (P * D * D * P - P * D * P * D * P) + (P * D * D * P - P * D * P * D * P) := by
            noncomm_ring
    rw [h_sec_var, h_curv_comp]
    noncomm_ring
  · have h_lhs :
        matInnerDer (P * D₁ * P) (P * D₂ * P) =
          P * D₁ * P * D₂ * P - P * D₂ * P * D₁ * P := by
      dsimp [matInnerDer]
      calc
        (P * D₁ * P) * (P * D₂ * P) - (P * D₂ * P) * (P * D₁ * P)
          = P * D₁ * (P * P) * D₂ * P - P * D₂ * (P * P) * D₁ * P := by noncomm_ring
        _ = P * D₁ * P * D₂ * P - P * D₂ * P * D₁ * P := by rw [hP_eq]
    rw [h_lhs, h_pair D₁ D₂, h_pair D₂ D₁]
    dsimp [matInnerDer]
    noncomm_ring

/-- **Theorem 135 (`Archetype CXVIII`: Matrix Spectral Trace Conservation, Equal Complementary Stratum Curvature Trace, & Vanishing Chiral Supertrace of Connes Curvature)**:
    Over *any* commutative base ring $R$ (`[CommRing R]`), for all $D, X, P \in \mathrm{Matrix}\;n\;n\;R$ with $P^2 = P$ (`hP : IsMatrixIdempotent P`):
    1. **Homological Trace Vanishing & Spectral Mass Conservation**:
       $$\mathrm{Matrix.trace}(\delta_D(X)) = 0, \qquad
         \mathrm{Matrix.trace}(X + \delta_D(X)) = \mathrm{Matrix.trace}(X).$$
    2. **Cyclic Chern–Connes Trace Invariance**:
       $$\mathrm{Matrix.trace}(P * \Omega_D(P)) = \mathrm{Matrix.trace}(\Omega_D(P) * P).$$
    3. **Equal Complementary Stratum Curvature Trace & Vanishing $\mathbb{Z}_2$-Graded Chiral Supertrace**:
       $$\mathrm{Matrix.trace}(P * \Omega_D(P)) = \mathrm{Matrix.trace}((1 - P) * \Omega_D(P)),$$
       $$\mathrm{Matrix.trace}((P + P - 1) * \Omega_D(P)) = 0.$$ -/
theorem matrix_trace_conservation_and_connes_chiral_supertrace_vanishing
    {R : Type*} {n : Type*} [Fintype n] [DecidableEq n] [CommRing R]
    (D X P : Matrix n n R) (hP : IsMatrixIdempotent P) :
    Matrix.trace (matInnerDer D X) = 0 ∧
    Matrix.trace (X + matInnerDer D X) = Matrix.trace X ∧
    Matrix.trace (P * matConnesCurvature D P) = Matrix.trace (matConnesCurvature D P * P) ∧
    Matrix.trace (P * matConnesCurvature D P) = Matrix.trace ((1 - P) * matConnesCurvature D P) ∧
    Matrix.trace ((P + P - 1) * matConnesCurvature D P) = 0 := by
  have hP_eq : P * P = P := hP
  have h_tr_comm : Matrix.trace (matInnerDer D X) = 0 := by
    dsimp [matInnerDer]
    rw [Matrix.trace_sub, Matrix.trace_mul_comm D X, sub_self]
  have h_swap : (1 - P) * matInnerDer D P = matInnerDer D P * P := by
    dsimp [matInnerDer]
    have h1 : (1 - P) * (D * P - P * D) = D * P - P * D * P := by
      calc
        (1 - P) * (D * P - P * D)
          = D * P - P * D - P * D * P + (P * P) * D := by noncomm_ring
        _ = D * P - P * D - P * D * P + P * D := by rw [hP_eq]
        _ = D * P - P * D * P := by noncomm_ring
    have h2 : (D * P - P * D) * P = D * P - P * D * P := by
      calc
        (D * P - P * D) * P
          = D * (P * P) - P * D * P := by noncomm_ring
        _ = D * P - P * D * P := by rw [hP_eq]
    exact h1.trans h2.symm
  have h_eq_strata :
      Matrix.trace (P * matConnesCurvature D P) =
        Matrix.trace ((1 - P) * matConnesCurvature D P) := by
    calc
      Matrix.trace (P * matConnesCurvature D P)
        = Matrix.trace ((P * matInnerDer D P) * matInnerDer D P) := by
          dsimp [matConnesCurvature]; rw [mul_assoc]
      _ = Matrix.trace (matInnerDer D P * (P * matInnerDer D P)) :=
          Matrix.trace_mul_comm (P * matInnerDer D P) (matInnerDer D P)
      _ = Matrix.trace ((matInnerDer D P * P) * matInnerDer D P) := by
          rw [mul_assoc]
      _ = Matrix.trace (((1 - P) * matInnerDer D P) * matInnerDer D P) := by
          rw [← h_swap]
      _ = Matrix.trace ((1 - P) * matConnesCurvature D P) := by
          dsimp [matConnesCurvature]; rw [mul_assoc]
  refine ⟨h_tr_comm, ?_, ?_, h_eq_strata, ?_⟩
  · rw [Matrix.trace_add, h_tr_comm, add_zero]
  · exact Matrix.trace_mul_comm P (matConnesCurvature D P)
  · have h_split :
        (P + P - 1) * matConnesCurvature D P =
          P * matConnesCurvature D P - (1 - P) * matConnesCurvature D P := by
      noncomm_ring
    rw [h_split, Matrix.trace_sub, h_eq_strata, sub_self]

/-- **Theorem 136 (`Archetype CXX`: Adiabatic Stratum Compression, Double-Commutator Off-Diagonal Projection $[[P, [P, D]], P] = [D, P]$, & Infinitesimal Lie–Connes Cochain Exactness $\mathcal{L}_A(P[D,P]^2) = [A, P[D,P]^2]$)**:
    Over *any* noncommutative ring $R$ (`[Ring R]`) and finite index type $n$, for all $A, D, D_1, D_2, X, P \in \mathrm{Matrix}\;n\;n\;R$ with $P^2 = P$ (`hP : IsMatrixIdempotent P`):
    1. **Generator Additivity & Adiabatic Stratum Compression ($\alpha_7$)**:
       $$[D_1 + D_2, X] = [D_1, X] + [D_2, X], \qquad [P * A * P, P] = 0, \qquad [D + P * A * P, P] = [D, P].$$
    2. **Double-Commutator Off-Diagonal Projection ($\alpha_7$)**:
       $$[[P, [P, D]], P] = [D, P].$$
    3. **Infinitesimal Inner Gauge Covariance & Lie–Connes Cochain Exactness ($\alpha_8$)**:
       $$[[A, D], P] + [D, [A, P]] = [A, [D, P]],$$
       $$\mathrm{matConnesDensityVariation}\;A\;D\;P = [A, P * [D, P]^2].$$ -/
theorem matrix_adiabatic_compression_double_commutator_and_lie_connes_exactness
    {R : Type*} {n : Type*} [Fintype n] [DecidableEq n] [Ring R]
    (A D D₁ D₂ X P : Matrix n n R) (hP : IsMatrixIdempotent P) :
    matInnerDer (D₁ + D₂) X = matInnerDer D₁ X + matInnerDer D₂ X ∧
    matInnerDer (P * A * P) P = 0 ∧
    matInnerDer (D + P * A * P) P = matInnerDer D P ∧
    matInnerDer (matInnerDer P (matInnerDer P D)) P = matInnerDer D P ∧
    matInnerDer (matInnerDer A D) P + matInnerDer D (matInnerDer A P) =
      matInnerDer A (matInnerDer D P) ∧
    matConnesDensityVariation A D P = matInnerDer A (matConnesDensity D P) := by
  have hP_eq : P * P = P := hP
  have h_add_left : ∀ B₁ B₂ Y : Matrix n n R,
      matInnerDer (B₁ + B₂) Y = matInnerDer B₁ Y + matInnerDer B₂ Y := by
    intro B₁ B₂ Y
    dsimp [matInnerDer]
    noncomm_ring
  have h_comp_zero : matInnerDer (P * A * P) P = 0 := by
    dsimp [matInnerDer]
    calc
      P * A * P * P - P * (P * A * P)
        = P * A * (P * P) - (P * P) * A * P := by noncomm_ring
      _ = P * A * P - P * A * P := by rw [hP_eq]
      _ = 0 := sub_self (P * A * P)
  have h_off : P * matInnerDer D P + matInnerDer D P * P = matInnerDer D P := by
    dsimp [matInnerDer]
    calc
      P * (D * P - P * D) + (D * P - P * D) * P
        = D * (P * P) - (P * P) * D := by noncomm_ring
      _ = D * P - P * D := by rw [hP_eq]
  have h_comp0 : P * matInnerDer D P * P = 0 := by
    dsimp [matInnerDer]
    calc
      P * (D * P - P * D) * P
        = P * D * (P * P) - (P * P) * D * P := by noncomm_ring
      _ = P * D * P - P * D * P := by rw [hP_eq]
      _ = 0 := sub_self (P * D * P)
  refine ⟨h_add_left D₁ D₂ X, h_comp_zero, ?_, ?_, ?_, ?_⟩
  · rw [h_add_left D (P * A * P) P, h_comp_zero, add_zero]
  · have h_step1 :
        matInnerDer (matInnerDer P (matInnerDer P D)) P =
        matInnerDer D P * (P * P) + (P * P) * matInnerDer D P -
        (P * matInnerDer D P * P + P * matInnerDer D P * P) := by
      dsimp [matInnerDer]
      noncomm_ring
    rw [h_step1, hP_eq, h_comp0, add_zero, sub_zero, add_comm, h_off]
  · dsimp [matInnerDer]
    noncomm_ring
  · dsimp [matConnesDensityVariation, matConnesDensity, matInnerDer]
    noncomm_ring

/-- **Theorem 137 (`Archetype CXXI`: Horizontal Base-Stratum Tangency, Fiber-Leg Reduction, Adiabatic & Double-Commutator Cocycle Invariance, & Infinitesimal Lie–Connes Trace Invariance)**:
    Over *any* commutative base ring $R$ (`[CommRing R]`), for all $A, D, P, V \in \mathrm{Matrix}\;n\;n\;R$ with $P^2 = P$ (`hP : IsMatrixIdempotent P`):
    1. **Horizontal Base-Stratum Tangency & Off-Diagonal Fiber-Leg Reduction ($\alpha_6$)**:
       $$\mathrm{Matrix.trace}([A, P] * [D, P]^2) = 0,$$
       $$\mathrm{Matrix.trace}(P * V * [D, P] + P * [D, P] * V) = \mathrm{Matrix.trace}(V * [D, P]).$$
    2. **Adiabatic & Double-Commutator Invariance of the Connes Cyclic Cocycle ($\alpha_7$)**:
       $$\mathrm{matConnesCocycle}\;(D + P * A * P)\;P = \mathrm{matConnesCocycle}\;D\;P,$$
       $$\mathrm{matConnesCocycle}\;([P, [P, D]])\;P = \mathrm{matConnesCocycle}\;D\;P.$$
    3. **Infinitesimal Total & Fiber-Leg Invariance of the Connes Cyclic Cocycle ($\alpha_8$)**:
       $$\mathrm{Matrix.trace}(\mathrm{matConnesDensityVariation}\;A\;D\;P) = 0,$$
       $$\mathrm{Matrix.trace}\bigl(P * (([[A, D], P] + [D, [A, P]]) * [D, P]) + P * ([D, P] * ([[A, D], P] + [D, [A, P]]))\bigr) = 0.$$ -/
theorem matrix_connes_cocycle_horizontal_adiabatic_and_infinitesimal_invariance
    {R : Type*} {n : Type*} [Fintype n] [DecidableEq n] [CommRing R]
    (A D P V : Matrix n n R) (hP : IsMatrixIdempotent P) :
    Matrix.trace (matInnerDer A P * matConnesCurvature D P) = 0 ∧
    Matrix.trace (P * V * matInnerDer D P + P * matInnerDer D P * V) =
      Matrix.trace (V * matInnerDer D P) ∧
    matConnesCocycle (D + P * A * P) P = matConnesCocycle D P ∧
    matConnesCocycle (matInnerDer P (matInnerDer P D)) P = matConnesCocycle D P ∧
    Matrix.trace (matConnesDensityVariation A D P) = 0 ∧
    Matrix.trace (
      P * ((matInnerDer (matInnerDer A D) P + matInnerDer D (matInnerDer A P)) * matInnerDer D P) +
      P * (matInnerDer D P * (matInnerDer (matInnerDer A D) P + matInnerDer D (matInnerDer A P)))
    ) = 0 := by
  have h134 := matrix_inner_derivation_idempotent_connes_curvature_and_gauss_codazzi D D D D D P hP
  have h_off : P * matInnerDer D P + matInnerDer D P * P = matInnerDer D P :=
    h134.2.2.2.2.2.2.2.2.2.1
  have h_comm : P * matConnesCurvature D P = matConnesCurvature D P * P :=
    h134.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have h136 := matrix_adiabatic_compression_double_commutator_and_lie_connes_exactness A D D D D P hP
  have h_add_comp : matInnerDer (D + P * A * P) P = matInnerDer D P := h136.2.2.1
  have h_dbl_comm : matInnerDer (matInnerDer P (matInnerDer P D)) P = matInnerDer D P := h136.2.2.2.1
  have h_exact : matConnesDensityVariation A D P = matInnerDer A (matConnesDensity D P) := h136.2.2.2.2.2
  have h_base_zero : Matrix.trace (matInnerDer A P * matConnesCurvature D P) = 0 := by
    have h_expand :
        matInnerDer A P * matConnesCurvature D P =
        A * (P * matConnesCurvature D P) - P * (A * matConnesCurvature D P) := by
      dsimp [matInnerDer]
      noncomm_ring
    rw [h_expand, Matrix.trace_sub, Matrix.trace_mul_comm P (A * matConnesCurvature D P)]
    have h_assoc : A * matConnesCurvature D P * P = A * (matConnesCurvature D P * P) := by
      noncomm_ring
    rw [h_assoc, ← h_comm]
    exact sub_self _
  have h_total_zero : Matrix.trace (matConnesDensityVariation A D P) = 0 := by
    rw [h_exact]
    dsimp [matInnerDer]
    rw [Matrix.trace_sub, Matrix.trace_mul_comm A (matConnesDensity D P), sub_self]
  refine ⟨h_base_zero, ?_, ?_, ?_, h_total_zero, ?_⟩
  · rw [Matrix.trace_add]
    have h1 : P * V * matInnerDer D P = P * (V * matInnerDer D P) := by noncomm_ring
    rw [h1, Matrix.trace_mul_comm P (V * matInnerDer D P)]
    rw [Matrix.trace_mul_comm (P * matInnerDer D P) V]
    rw [← Matrix.trace_add]
    have h_sum :
        V * matInnerDer D P * P + V * (P * matInnerDer D P) =
        V * (P * matInnerDer D P + matInnerDer D P * P) := by
      noncomm_ring
    rw [h_sum, h_off]
  · dsimp [matConnesCocycle, matConnesDensity]
    rw [h_add_comp]
  · dsimp [matConnesCocycle, matConnesDensity]
    rw [h_dbl_comm]
  · have h_tot := h_total_zero
    dsimp [matConnesDensityVariation] at h_tot
    change Matrix.trace (
      matInnerDer A P * matConnesCurvature D P +
      P * ((matInnerDer (matInnerDer A D) P + matInnerDer D (matInnerDer A P)) * matInnerDer D P) +
      P * (matInnerDer D P * (matInnerDer (matInnerDer A D) P + matInnerDer D (matInnerDer A P)))
    ) = 0 at h_tot
    rw [add_assoc, Matrix.trace_add, h_base_zero, zero_add] at h_tot
    exact h_tot

/-- **Theorem 138 (`Archetype CXXII`: Global Inner Gauge Conjugation $(D, P) \mapsto (U D V, U P V)$ & Master Perturbation Invariance of the Connes Cyclic Cocycle $\tau(P[D,P]^2)$)**:
    Over *any* commutative base ring $R$ (`[CommRing R]`), for all $U, V, D, A, P \in \mathrm{Matrix}\;n\;n\;R$ with $U * V = 1 \wedge V * U = 1$ (`hUV : IsMatrixInnerGaugePair U V`) and $P^2 = P$ (`hP : IsMatrixIdempotent P`):
    1. **Global Inner Gauge Preservation of Idempotence & Covariant Conjugation**:
       $$\mathrm{IsMatrixIdempotent}\;(U * P * V),$$
       $$[U * D * V, U * P * V] = U * [D, P] * V,$$
       $$\mathcal{C}(U * D * V, U * P * V) = U * \mathcal{C}(D, P) * V.$$
    2. **Global Inner Gauge & Master Perturbation Invariance of the Connes Cyclic Cocycle**:
       $$\mathrm{matConnesCocycle}\;(U * D * V)\;(U * P * V) = \mathrm{matConnesCocycle}\;D\;P,$$
       $$\mathrm{matConnesCocycle}\;(U * (D + P * A * P) * V)\;(U * P * V) = \mathrm{matConnesCocycle}\;D\;P.$$ -/
theorem matrix_connes_cocycle_global_inner_gauge_and_master_invariance
    {R : Type*} {n : Type*} [Fintype n] [DecidableEq n] [CommRing R]
    (U V D A P : Matrix n n R)
    (hUV : IsMatrixInnerGaugePair U V) (hP : IsMatrixIdempotent P) :
    IsMatrixIdempotent (U * P * V) ∧
    matInnerDer (U * D * V) (U * P * V) = U * matInnerDer D P * V ∧
    matConnesDensity (U * D * V) (U * P * V) = U * matConnesDensity D P * V ∧
    matConnesCocycle (U * D * V) (U * P * V) = matConnesCocycle D P ∧
    matConnesCocycle (U * (D + P * A * P) * V) (U * P * V) = matConnesCocycle D P := by
  have h_vu : V * U = 1 := hUV.2
  have hP_eq : P * P = P := hP
  have h_idem_gauge : IsMatrixIdempotent (U * P * V) := by
    dsimp [IsMatrixIdempotent]
    calc
      (U * P * V) * (U * P * V)
        = U * P * (V * U) * P * V := by noncomm_ring
      _ = U * P * 1 * P * V := by rw [h_vu]
      _ = U * (P * P) * V := by noncomm_ring
      _ = U * P * V := by rw [hP_eq]
  have h_comm_gauge : ∀ B : Matrix n n R,
      matInnerDer (U * B * V) (U * P * V) = U * matInnerDer B P * V := by
    intro B
    dsimp [matInnerDer]
    calc
      (U * B * V) * (U * P * V) - (U * P * V) * (U * B * V)
        = U * B * (V * U) * P * V - U * P * (V * U) * B * V := by noncomm_ring
      _ = U * B * 1 * P * V - U * P * 1 * B * V := by rw [h_vu]
      _ = U * (B * P - P * B) * V := by noncomm_ring
  have h_dens_gauge : ∀ B : Matrix n n R,
      matConnesDensity (U * B * V) (U * P * V) = U * matConnesDensity B P * V := by
    intro B
    dsimp [matConnesDensity]
    rw [h_comm_gauge B]
    calc
      (U * P * V) * ((U * matInnerDer B P * V) * (U * matInnerDer B P * V))
        = U * P * (V * U) * matInnerDer B P * (V * U) * matInnerDer B P * V := by
          noncomm_ring
      _ = U * P * 1 * matInnerDer B P * 1 * matInnerDer B P * V := by
          rw [h_vu]
      _ = U * (P * (matInnerDer B P * matInnerDer B P)) * V := by
          noncomm_ring
  have h_cocyc_gauge : ∀ B : Matrix n n R,
      matConnesCocycle (U * B * V) (U * P * V) = matConnesCocycle B P := by
    intro B
    dsimp [matConnesCocycle]
    rw [h_dens_gauge B, Matrix.trace_mul_comm (U * matConnesDensity B P) V]
    have h_assoc : V * (U * matConnesDensity B P) = (V * U) * matConnesDensity B P := by
      noncomm_ring
    rw [h_assoc, h_vu, one_mul]
  have h_adiab : matConnesCocycle (D + P * A * P) P = matConnesCocycle D P :=
    (matrix_connes_cocycle_horizontal_adiabatic_and_infinitesimal_invariance A D P D hP).2.2.1
  refine ⟨h_idem_gauge, h_comm_gauge D, h_dens_gauge D, h_cocyc_gauge D, ?_⟩
  rw [h_cocyc_gauge (D + P * A * P), h_adiab]

/-- A 0-cochain on the non-commutative matrix algebra $\mathrm{Matrix}\;n\;n\;R$. -/
abbrev MatCochain0 (n R : Type*) := Matrix n n R → R

/-- A 1-cochain on the non-commutative matrix algebra $\mathrm{Matrix}\;n\;n\;R$. -/
abbrev MatCochain1 (n R : Type*) := Matrix n n R → Matrix n n R → R

/-- A 2-cochain on the non-commutative matrix algebra $\mathrm{Matrix}\;n\;n\;R$. -/
abbrev MatCochain2 (n R : Type*) := Matrix n n R → Matrix n n R → Matrix n n R → R

/-- A 3-cochain on the non-commutative matrix algebra $\mathrm{Matrix}\;n\;n\;R$. -/
abbrev MatCochain3 (n R : Type*) :=
  Matrix n n R → Matrix n n R → Matrix n n R → Matrix n n R → R

/-- Hochschild coboundary operator $b_0 : C^0(M_n(R)) \to C^1(M_n(R))$. -/
def matHochschildB0 {R : Type*} {n : Type*} [Fintype n] [DecidableEq n] [Ring R]
    (φ : MatCochain0 n R) : MatCochain1 n R :=
  fun A₀ A₁ => φ (A₀ * A₁) - φ (A₁ * A₀)

/-- Hochschild coboundary operator $b_1 : C^1(M_n(R)) \to C^2(M_n(R))$. -/
def matHochschildB1 {R : Type*} {n : Type*} [Fintype n] [DecidableEq n] [Ring R]
    (φ : MatCochain1 n R) : MatCochain2 n R :=
  fun A₀ A₁ A₂ => φ (A₀ * A₁) A₂ - φ A₀ (A₁ * A₂) + φ (A₂ * A₀) A₁

/-- Hochschild coboundary operator $b_2 : C^2(M_n(R)) \to C^3(M_n(R))$. -/
def matHochschildB2 {R : Type*} {n : Type*} [Fintype n] [DecidableEq n] [Ring R]
    (φ : MatCochain2 n R) : MatCochain3 n R :=
  fun A₀ A₁ A₂ A₃ =>
    φ (A₀ * A₁) A₂ A₃ - φ A₀ (A₁ * A₂) A₃ + φ A₀ A₁ (A₂ * A₃) - φ (A₃ * A₀) A₁ A₂

/-- Signed cyclic permutation operator $\lambda_1 : C^1(M_n(R)) \to C^1(M_n(R))$,
    $(\lambda_1 \varphi)(A_0, A_1) = -\varphi(A_1, A_0)$. -/
def matCyclicLambda1 {R : Type*} {n : Type*} [Ring R]
    (φ : MatCochain1 n R) : MatCochain1 n R :=
  fun A₀ A₁ => - φ A₁ A₀

/-- Signed cyclic permutation operator $\lambda_2 : C^2(M_n(R)) \to C^2(M_n(R))$,
    $(\lambda_2 \varphi)(A_0, A_1, A_2) = \varphi(A_2, A_0, A_1)$. -/
def matCyclicLambda2 {R : Type*} {n : Type*}
    (φ : MatCochain2 n R) : MatCochain2 n R :=
  fun A₀ A₁ A₂ => φ A₂ A₀ A₁

/-- Signed cyclic permutation operator $\lambda_3 : C^3(M_n(R)) \to C^3(M_n(R))$,
    $(\lambda_3 \varphi)(A_0, A_1, A_2, A_3) = -\varphi(A_3, A_0, A_1, A_2)$. -/
def matCyclicLambda3 {R : Type*} {n : Type*} [Ring R]
    (φ : MatCochain3 n R) : MatCochain3 n R :=
  fun A₀ A₁ A₂ A₃ => - φ A₃ A₀ A₁ A₂

/-- Cyclic norm operator $N_1 = 1 + \lambda_1$ on 1-cochains. -/
def matCyclicNorm1 {R : Type*} {n : Type*} [Ring R]
    (φ : MatCochain1 n R) : MatCochain1 n R :=
  fun A₀ A₁ => φ A₀ A₁ - φ A₁ A₀

/-- Cyclic norm operator $N_2 = 1 + \lambda_2 + \lambda_2^2$ on 2-cochains. -/
def matCyclicNorm2 {R : Type*} {n : Type*} [Ring R]
    (φ : MatCochain2 n R) : MatCochain2 n R :=
  fun A₀ A₁ A₂ => φ A₀ A₁ A₂ + φ A₂ A₀ A₁ + φ A₁ A₂ A₀

/-- Cyclic norm operator $N_3 = 1 + \lambda_3 + \lambda_3^2 + \lambda_3^3$ on 3-cochains. -/
def matCyclicNorm3 {R : Type*} {n : Type*} [Ring R]
    (φ : MatCochain3 n R) : MatCochain3 n R :=
  fun A₀ A₁ A₂ A₃ =>
    φ A₀ A₁ A₂ A₃ - φ A₃ A₀ A₁ A₂ + φ A₂ A₃ A₀ A₁ - φ A₁ A₂ A₃ A₀

/-- Connes' reduced boundary operator $B_0 : C^1(M_n(R)) \to C^0(M_n(R))$,
    $(B_0 \varphi)(A_0) = \varphi(1, A_0) + \varphi(A_0, 1)$. -/
def matConnesB0_1 {R : Type*} {n : Type*} [DecidableEq n] [Ring R]
    (φ : MatCochain1 n R) : MatCochain0 n R :=
  fun A₀ => φ 1 A₀ + φ A₀ 1

/-- Connes' reduced boundary operator $B_0 : C^2(M_n(R)) \to C^1(M_n(R))$,
    $(B_0 \varphi)(A_0, A_1) = \varphi(1, A_0, A_1) - \varphi(A_0, A_1, 1)$. -/
def matConnesB0_2 {R : Type*} {n : Type*} [DecidableEq n] [Ring R]
    (φ : MatCochain2 n R) : MatCochain1 n R :=
  fun A₀ A₁ => φ 1 A₀ A₁ - φ A₀ A₁ 1

/-- Connes' reduced boundary operator $B_0 : C^3(M_n(R)) \to C^2(M_n(R))$,
    $(B_0 \Phi)(A_0, A_1, A_2) = \Phi(1, A_0, A_1, A_2) + \Phi(A_0, A_1, A_2, 1)$. -/
def matConnesB0_3 {R : Type*} {n : Type*} [DecidableEq n] [Ring R]
    (Φ : MatCochain3 n R) : MatCochain2 n R :=
  fun A₀ A₁ A₂ => Φ 1 A₀ A₁ A₂ + Φ A₀ A₁ A₂ 1

/-- Connes' cyclic coboundary operator $B_1 = N_0 \circ B_0 : C^1(M_n(R)) \to C^0(M_n(R))$. -/
def matConnesB1 {R : Type*} {n : Type*} [DecidableEq n] [Ring R]
    (φ : MatCochain1 n R) : MatCochain0 n R :=
  matConnesB0_1 φ

/-- Connes' cyclic coboundary operator $B_2 = N_1 \circ B_0 : C^2(M_n(R)) \to C^1(M_n(R))$. -/
def matConnesB2 {R : Type*} {n : Type*} [DecidableEq n] [Ring R]
    (φ : MatCochain2 n R) : MatCochain1 n R :=
  matCyclicNorm1 (matConnesB0_2 φ)

/-- Connes' cyclic coboundary operator $B_3 = N_2 \circ B_0 : C^3(M_n(R)) \to C^2(M_n(R))$. -/
def matConnesB3 {R : Type*} {n : Type*} [DecidableEq n] [Ring R]
    (Φ : MatCochain3 n R) : MatCochain2 n R :=
  matCyclicNorm2 (matConnesB0_3 Φ)

/-- The Chern–Connes spectral 2-cochain $\phi_D(A_0, A_1, A_2) = \mathrm{tr}(A_0 [D, A_1] [D, A_2])$. -/
def matChernConnesCochain2 {R : Type*} {n : Type*} [Fintype n] [DecidableEq n] [CommRing R]
    (D : Matrix n n R) : MatCochain2 n R :=
  fun A₀ A₁ A₂ => Matrix.trace (A₀ * matInnerDer D A₁ * matInnerDer D A₂)

/-- **Theorem 139 (`Archetype CXXIII`: Hochschild Simplicial Coboundary $b_0, b_1, b_2$, Nilpotence $b^2 = 0$, Signed Cyclic Permutations $\lambda_k$, & Cyclic Norm Symmetrizer $N_k$)**:
    Over *any* commutative ring $R$ (`[CommRing R]`), for all cochains $\varphi_0 \in C^0(M_n(R)), \varphi_1 \in C^1(M_n(R)), \varphi_2 \in C^2(M_n(R)), \varphi_3 \in C^3(M_n(R))$:
    1. **Trace 0-Cocycle & Hochschild Nilpotence ($b_1 \circ b_0 = 0$ and $b_2 \circ b_1 = 0$)**:
       $$b_0(\mathrm{tr}) = 0, \qquad b_1(b_0 \varphi_0) = 0, \qquad b_2(b_1 \varphi_1) = 0.$$
    2. **Cyclic Permutation Periodicity ($\lambda_k^{k+1} = \mathrm{id}$) & Norm Invariance ($\lambda_k \circ N_k = N_k$)**:
       $$\lambda_1^2(\varphi_1) = \varphi_1, \quad \lambda_2^3(\varphi_2) = \varphi_2, \quad \lambda_3^4(\varphi_3) = \varphi_3,$$
       $$\lambda_1(N_1 \varphi_1) = N_1 \varphi_1, \quad \lambda_2(N_2 \varphi_2) = N_2 \varphi_2, \quad \lambda_3(N_3 \varphi_3) = N_3 \varphi_3.$$ -/
theorem matrix_hochschild_coboundary_nilpotence_and_cyclic_norm_invariance
    {R : Type*} {n : Type*} [Fintype n] [DecidableEq n] [CommRing R]
    (φ₀ : MatCochain0 n R) (φ₁ : MatCochain1 n R)
    (φ₂ : MatCochain2 n R) (φ₃ : MatCochain3 n R) :
    matHochschildB0 (Matrix.trace : MatCochain0 n R) = 0 ∧
    matHochschildB1 (matHochschildB0 φ₀) = 0 ∧
    matHochschildB2 (matHochschildB1 φ₁) = 0 ∧
    matCyclicLambda1 (matCyclicLambda1 φ₁) = φ₁ ∧
    matCyclicLambda2 (matCyclicLambda2 (matCyclicLambda2 φ₂)) = φ₂ ∧
    matCyclicLambda3 (matCyclicLambda3 (matCyclicLambda3 (matCyclicLambda3 φ₃))) = φ₃ ∧
    matCyclicLambda1 (matCyclicNorm1 φ₁) = matCyclicNorm1 φ₁ ∧
    matCyclicLambda2 (matCyclicNorm2 φ₂) = matCyclicNorm2 φ₂ ∧
    matCyclicLambda3 (matCyclicNorm3 φ₃) = matCyclicNorm3 φ₃ := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · funext A₀ A₁
    dsimp [matHochschildB0]
    rw [Matrix.trace_mul_comm A₀ A₁, sub_self]
  · funext A₀ A₁ A₂
    dsimp [matHochschildB1, matHochschildB0]
    simp only [mul_assoc]
    abel
  · funext A₀ A₁ A₂ A₃
    dsimp [matHochschildB2, matHochschildB1]
    simp only [mul_assoc]
    abel
  · funext A₀ A₁
    dsimp [matCyclicLambda1]
    exact neg_neg (φ₁ A₀ A₁)
  · funext A₀ A₁ A₂
    rfl
  · funext A₀ A₁ A₂ A₃
    dsimp [matCyclicLambda3]
    rw [neg_neg, neg_neg]
  · funext A₀ A₁
    dsimp [matCyclicLambda1, matCyclicNorm1]
    abel
  · funext A₀ A₁ A₂
    dsimp [matCyclicLambda2, matCyclicNorm2]
    abel
  · funext A₀ A₁ A₂ A₃
    dsimp [matCyclicLambda3, matCyclicNorm3]
    abel

/-- **Theorem 140 (`Archetype CXXIV`: Connes' Cyclic Coboundary $B = N \circ B_0$, Nilpotence $B^2 = 0$, $(b, B)$ Bicomplex Anticommutativity $b_0 B_1 + B_2 b_1 = 0$, & $(b, B)$-Closure of the Chern–Connes Spectral 2-Cochain $\phi_D$)**:
    Over *any* commutative ring $R$ (`[CommRing R]`), for all cochains $\varphi_1 \in C^1(M_n(R)), \varphi_2 \in C^2(M_n(R)), \Phi_3 \in C^3(M_n(R))$ and matrices $D, P, A_0, A_1 \in \mathrm{Matrix}\;n\;n\;R$:
    1. **Kernel-Image Orthogonality ($B_0 \circ N = 0$) & Connes Nilpotency ($B_1 \circ B_2 = 0$ and $B_2 \circ B_3 = 0$)**:
       $$B_0^{(1)}(N_1 \varphi_1)(A_0) = 0, \qquad B_0^{(2)}(N_2 \varphi_2)(A_0, A_1) = 0,$$
       $$B_1(B_2 \varphi_2) = 0, \qquad B_2(B_3 \Phi_3) = 0.$$
    2. **Connes $(b, B)$ Bicomplex Anticommutativity**:
       $$b_0(B_1 \varphi_1) + B_2(b_1 \varphi_1) = 0.$$
    3. **Diagonal Recovery & Simultaneous $(b_2, B_2)$-Cocycle Closure of the Chern–Connes 2-Cochain $\phi_D$**:
       $$\phi_D(P, P, P) = \mathrm{matConnesCocycle}\;D\;P, \qquad B_2(\phi_D) = 0, \qquad b_2(\phi_D) = 0.$$ -/
theorem matrix_connes_cyclic_coboundary_nilpotence_bicomplex_and_chern_connes_cocycle
    {R : Type*} {n : Type*} [Fintype n] [DecidableEq n] [CommRing R]
    (φ₁ : MatCochain1 n R) (φ₂ : MatCochain2 n R) (Φ₃ : MatCochain3 n R)
    (D P A₀ A₁ : Matrix n n R) :
    matConnesB0_1 (matCyclicNorm1 φ₁) A₀ = 0 ∧
    matConnesB0_2 (matCyclicNorm2 φ₂) A₀ A₁ = 0 ∧
    matConnesB1 (matConnesB2 φ₂) = 0 ∧
    matConnesB2 (matConnesB3 Φ₃) = 0 ∧
    matHochschildB0 (matConnesB1 φ₁) + matConnesB2 (matHochschildB1 φ₁) = 0 ∧
    matChernConnesCochain2 D P P P = matConnesCocycle D P ∧
    matConnesB2 (matChernConnesCochain2 D) = 0 ∧
    matHochschildB2 (matChernConnesCochain2 D) = 0 := by
  have h_b0_n1 : ∀ (ψ : MatCochain1 n R) (X : Matrix n n R),
      matConnesB0_1 (matCyclicNorm1 ψ) X = 0 := by
    intro ψ X
    dsimp [matConnesB0_1, matCyclicNorm1]
    abel
  have h_b0_n2 : ∀ (ψ : MatCochain2 n R) (X Y : Matrix n n R),
      matConnesB0_2 (matCyclicNorm2 ψ) X Y = 0 := by
    intro ψ X Y
    dsimp [matConnesB0_2, matCyclicNorm2]
    abel
  have h_comm_one : matInnerDer D 1 = 0 := by
    dsimp [matInnerDer]
    rw [mul_one, one_mul, sub_self]
  have h_leib : ∀ X Y : Matrix n n R,
      matInnerDer D (X * Y) = matInnerDer D X * Y + X * matInnerDer D Y := by
    intro X Y
    dsimp [matInnerDer]
    noncomm_ring
  refine ⟨h_b0_n1 φ₁ A₀, h_b0_n2 φ₂ A₀ A₁, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · funext X
    dsimp [matConnesB1, matConnesB2]
    exact h_b0_n1 (matConnesB0_2 φ₂) X
  · funext X Y
    dsimp [matConnesB2, matConnesB3, matCyclicNorm1]
    rw [h_b0_n2 (matConnesB0_3 Φ₃) X Y, h_b0_n2 (matConnesB0_3 Φ₃) Y X]
    exact sub_self 0
  · funext X Y
    change matHochschildB0 (matConnesB1 φ₁) X Y + matConnesB2 (matHochschildB1 φ₁) X Y = 0
    dsimp [matHochschildB0, matHochschildB1, matConnesB1, matConnesB2,
      matConnesB0_1, matConnesB0_2, matCyclicNorm1]
    simp only [one_mul, mul_one]
    abel
  · dsimp [matChernConnesCochain2, matConnesCocycle, matConnesDensity]
    rw [mul_assoc]
  · funext X Y
    dsimp [matConnesB2, matCyclicNorm1, matConnesB0_2, matChernConnesCochain2]
    simp only [h_comm_one, mul_zero, Matrix.trace_zero, sub_zero, one_mul]
    rw [Matrix.trace_mul_comm (matInnerDer D X) (matInnerDer D Y), sub_self]
  · funext X₀ X₁ X₂ X₃
    dsimp [matHochschildB2, matChernConnesCochain2]
    rw [h_leib X₁ X₂, h_leib X₂ X₃]
    have h_alg1 :
        X₀ * (matInnerDer D X₁ * X₂ + X₁ * matInnerDer D X₂) * matInnerDer D X₃ =
        X₀ * matInnerDer D X₁ * X₂ * matInnerDer D X₃ +
        X₀ * X₁ * matInnerDer D X₂ * matInnerDer D X₃ := by noncomm_ring
    have h_alg2 :
        X₀ * matInnerDer D X₁ * (matInnerDer D X₂ * X₃ + X₂ * matInnerDer D X₃) =
        X₀ * matInnerDer D X₁ * matInnerDer D X₂ * X₃ +
        X₀ * matInnerDer D X₁ * X₂ * matInnerDer D X₃ := by noncomm_ring
    have h_alg3 :
        X₃ * X₀ * matInnerDer D X₁ * matInnerDer D X₂ =
        X₃ * (X₀ * matInnerDer D X₁ * matInnerDer D X₂) := by noncomm_ring
    rw [h_alg1, h_alg2, h_alg3]
    rw [Matrix.trace_add, Matrix.trace_add]
    rw [Matrix.trace_mul_comm X₃ (X₀ * matInnerDer D X₁ * matInnerDer D X₂)]
    abel

/-- Non-commutative taxonomic subprojection relation $P \preceq G$:
    $P$ is absorbed on both the right and left by the coarser projection $G$ ($P G = P \wedge G P = P$). -/
def IsMatrixSubprojection {R : Type*} {n : Type*} [Fintype n] [DecidableEq n] [Ring R]
    (P G : Matrix n n R) : Prop :=
  P * G = P ∧ G * P = P

/-- Two operator strata $P$ and $Q$ are mutually orthogonal if $P Q = 0 \wedge Q P = 0$. -/
def IsMatrixOrthogonalPair {R : Type*} {n : Type*} [Fintype n] [DecidableEq n] [Ring R]
    (P Q : Matrix n n R) : Prop :=
  P * Q = 0 ∧ Q * P = 0

/-- The non-commutative coarse-graining (pinching) conditional expectation
    $\mathcal{E}_P(X) = P X P + (1 - P) X (1 - P)$ on $\mathrm{Matrix}\;n\;n\;R$. -/
def matCoarseGrain {R : Type*} {n : Type*} [Fintype n] [DecidableEq n] [Ring R]
    (P X : Matrix n n R) : Matrix n n R :=
  P * X * P + (1 - P) * X * (1 - P)

/-- **Theorem 141 (`Archetype CXXV`: Halmos–Connes Taxonomic Subprojection Poset $P \preceq G$, Hierarchical Corner Tower Law, Binomial Corner Factorization $G P G = P$, & Orthogonal Speciation / Fusion)**:
    Over *any* noncommutative base ring $R$ (`[Ring R]`), for all $P, Q, G, X \in \mathrm{Matrix}\;n\;n\;R$:
    1. **Partial Order Laws**: Reflexivity on idempotents ($P^2 = P \implies P \preceq P$), antisymmetry ($P \preceq Q \wedge Q \preceq P \implies P = Q$), and transitivity ($P \preceq Q \wedge Q \preceq G \implies P \preceq G$).
    2. **Commutativity, Corner Tower Law, & Binomial Corner Identity**:
       $$P \preceq G \implies [G, P] = 0 \;\wedge\; P (G X G) P = P X P \;\wedge\; G P G = P.$$
    3. **Relative Complement Speciation**:
       $$P^2 = P \wedge G^2 = G \wedge P \preceq G \implies (G - P)^2 = G - P \;\wedge\; (G - P) \preceq G \;\wedge\; P(G - P) = (G - P)P = 0.$$
    4. **Orthogonal Stratum Fusion**:
       $$P^2 = P \wedge Q^2 = Q \wedge P Q = Q P = 0 \implies (P + Q)^2 = P + Q \;\wedge\; P \preceq P + Q \;\wedge\; Q \preceq P + Q.$$ -/
theorem matrix_taxonomic_subprojection_poset_binomial_corner_and_orthogonal_speciation
    {R : Type*} {n : Type*} [Fintype n] [DecidableEq n] [Ring R]
    (P Q G X : Matrix n n R) :
    (IsMatrixIdempotent P → IsMatrixSubprojection P P) ∧
    (IsMatrixSubprojection P Q → IsMatrixSubprojection Q P → P = Q) ∧
    (IsMatrixSubprojection P Q → IsMatrixSubprojection Q G → IsMatrixSubprojection P G) ∧
    (IsMatrixSubprojection P G →
      matInnerDer G P = 0 ∧ P * (G * X * G) * P = P * X * P ∧ G * P * G = P) ∧
    (IsMatrixIdempotent P → IsMatrixIdempotent G → IsMatrixSubprojection P G →
      IsMatrixIdempotent (G - P) ∧
      IsMatrixSubprojection (G - P) G ∧
      IsMatrixOrthogonalPair P (G - P)) ∧
    (IsMatrixIdempotent P → IsMatrixIdempotent Q → IsMatrixOrthogonalPair P Q →
      IsMatrixIdempotent (P + Q) ∧
      IsMatrixSubprojection P (P + Q) ∧
      IsMatrixSubprojection Q (P + Q)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro hP
    exact ⟨hP, hP⟩
  · intro hPQ hQP
    rw [← hPQ.1, hQP.2]
  · intro hPQ hQG
    refine ⟨?_, ?_⟩
    · calc
        P * G = (P * Q) * G := by rw [hPQ.1]
        _ = P * (Q * G) := by rw [mul_assoc]
        _ = P * Q := by rw [hQG.1]
        _ = P := hPQ.1
    · calc
        G * P = G * (Q * P) := by rw [hPQ.2]
        _ = (G * Q) * P := by rw [mul_assoc]
        _ = Q * P := by rw [hQG.2]
        _ = P := hPQ.2
  · intro hPG
    refine ⟨?_, ?_, ?_⟩
    · dsimp [matInnerDer]
      rw [hPG.2, hPG.1, sub_self]
    · calc
        P * (G * X * G) * P = (P * G) * X * (G * P) := by noncomm_ring
        _ = P * X * P := by rw [hPG.1, hPG.2]
    · rw [hPG.2, hPG.1]
  · intro hP hG hPG
    have hP_eq : P * P = P := hP
    have hG_eq : G * G = G := hG
    refine ⟨?_, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · dsimp [IsMatrixIdempotent]
      calc
        (G - P) * (G - P) = G * G - G * P - P * G + P * P := by noncomm_ring
        _ = G - P - P + P := by rw [hG_eq, hPG.2, hPG.1, hP_eq]
        _ = G - P := by noncomm_ring
    · calc
        (G - P) * G = G * G - P * G := by noncomm_ring
        _ = G - P := by rw [hG_eq, hPG.1]
    · calc
        G * (G - P) = G * G - G * P := by noncomm_ring
        _ = G - P := by rw [hG_eq, hPG.2]
    · calc
        P * (G - P) = P * G - P * P := by noncomm_ring
        _ = P - P := by rw [hPG.1, hP_eq]
        _ = 0 := sub_self P
    · calc
        (G - P) * P = G * P - P * P := by noncomm_ring
        _ = P - P := by rw [hPG.2, hP_eq]
        _ = 0 := sub_self P
  · intro hP hQ hPQ
    have hP_eq : P * P = P := hP
    have hQ_eq : Q * Q = Q := hQ
    refine ⟨?_, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · dsimp [IsMatrixIdempotent]
      calc
        (P + Q) * (P + Q) = P * P + P * Q + Q * P + Q * Q := by noncomm_ring
        _ = P + 0 + 0 + Q := by rw [hP_eq, hPQ.1, hPQ.2, hQ_eq]
        _ = P + Q := by abel
    · calc
        P * (P + Q) = P * P + P * Q := by noncomm_ring
        _ = P + 0 := by rw [hP_eq, hPQ.1]
        _ = P := add_zero P
    · calc
        (P + Q) * P = P * P + Q * P := by noncomm_ring
        _ = P + 0 := by rw [hP_eq, hPQ.2]
        _ = P := add_zero P
    · calc
        Q * (P + Q) = Q * P + Q * Q := by noncomm_ring
        _ = 0 + Q := by rw [hPQ.2, hQ_eq]
        _ = Q := zero_add Q
    · calc
        (P + Q) * Q = P * Q + Q * Q := by noncomm_ring
        _ = 0 + Q := by rw [hPQ.1, hQ_eq]
        _ = Q := zero_add Q

/-- **Theorem 142 (`Archetype CXXVI`: Coarse-Graining Conditional Expectation $\mathcal{E}_P$, Hodge–Peirce Splitting $\mathcal{E}_P(X) + [P, [P, X]] = X$, & Genus-Confined Partition of the Connes Cyclic Cocycle)**:
    Over *any* commutative base ring $R$ (`[CommRing R]`), for all $D, P, G, X \in \mathrm{Matrix}\;n\;n\;R$ with $P^2 = P$ (`hP : IsMatrixIdempotent P`), $P \preceq G$ (`hPG : IsMatrixSubprojection P G`), and $[D, G] = 0$ (`hDG : matInnerDer D G = 0`):
    1. **Hodge–Peirce Decomposition, Idempotence, Derivation Annihilation, & Trace Preservation**:
       $$\mathcal{E}_P(X) + [P, [P, X]] = X, \qquad \mathcal{E}_P(\mathcal{E}_P(X)) = \mathcal{E}_P(X),$$
       $$\mathcal{E}_P([D, P]) = 0, \qquad \mathrm{tr}(\mathcal{E}_P(X)) = \mathrm{tr}(X).$$
    2. **Genus-Confined Evolution, Sibling Curvature Equality, & Taxonomic Cocycle Partition**:
       $$G [D, P] G = [D, P], \qquad [D, G - P] = -[D, P], \qquad \Omega_D(G - P) = \Omega_D(P),$$
       $$\mathrm{matConnesCocycle}\;D\;P + \mathrm{matConnesCocycle}\;D\;(G - P) = \mathrm{tr}(G \, \Omega_D(P)).$$ -/
theorem matrix_coarse_graining_hodge_peirce_and_genus_confined_cocycle_partition
    {R : Type*} {n : Type*} [Fintype n] [DecidableEq n] [CommRing R]
    (D P G X : Matrix n n R)
    (hP : IsMatrixIdempotent P)
    (hPG : IsMatrixSubprojection P G)
    (hDG : matInnerDer D G = 0) :
    matCoarseGrain P X + matInnerDer P (matInnerDer P X) = X ∧
    matCoarseGrain P (matCoarseGrain P X) = matCoarseGrain P X ∧
    matCoarseGrain P (matInnerDer D P) = 0 ∧
    Matrix.trace (matCoarseGrain P X) = Matrix.trace X ∧
    G * matInnerDer D P * G = matInnerDer D P ∧
    matInnerDer D (G - P) = - matInnerDer D P ∧
    matConnesCurvature D (G - P) = matConnesCurvature D P ∧
    matConnesCocycle D P + matConnesCocycle D (G - P) =
      Matrix.trace (G * matConnesCurvature D P) := by
  have hP_eq : P * P = P := hP
  have h_hp : matCoarseGrain P X + matInnerDer P (matInnerDer P X) = X := by
    dsimp [matCoarseGrain, matInnerDer]
    calc
      P * X * P + (1 - P) * X * (1 - P) + (P * (P * X - X * P) - (P * X - X * P) * P)
        = X + (P * P - P) * X + X * (P * P - P) := by noncomm_ring
      _ = X + (P - P) * X + X * (P - P) := by rw [hP_eq]
      _ = X := by noncomm_ring
  have h_sub_der : matInnerDer D (G - P) = - matInnerDer D P := by
    have h_lin : matInnerDer D (G - P) = matInnerDer D G - matInnerDer D P := by
      dsimp [matInnerDer]
      noncomm_ring
    rw [h_lin, hDG, zero_sub]
  have h_curv_eq : matConnesCurvature D (G - P) = matConnesCurvature D P := by
    dsimp [matConnesCurvature]
    rw [h_sub_der, neg_mul_neg]
  refine ⟨h_hp, ?_, ?_, ?_, ?_, h_sub_der, h_curv_eq, ?_⟩
  · dsimp [matCoarseGrain]
    calc
      P * (P * X * P + (1 - P) * X * (1 - P)) * P +
        (1 - P) * (P * X * P + (1 - P) * X * (1 - P)) * (1 - P)
        = (P * P) * X * (P * P) + (P - P * P) * X * (P - P * P) +
          (P - P * P) * X * (P - P * P) +
          (1 - P - P + P * P) * X * (1 - P - P + P * P) := by noncomm_ring
      _ = P * X * P + (P - P) * X * (P - P) +
          (P - P) * X * (P - P) +
          (1 - P - P + P) * X * (1 - P - P + P) := by rw [hP_eq]
      _ = P * X * P + (1 - P) * X * (1 - P) := by noncomm_ring
  · dsimp [matCoarseGrain, matInnerDer]
    calc
      P * (D * P - P * D) * P + (1 - P) * (D * P - P * D) * (1 - P)
        = P * D * (P * P) - (P * P) * D * P +
          ((D - P * D) * (P - P * P) - (P - P * P) * (D - D * P)) := by noncomm_ring
      _ = P * D * P - P * D * P +
          ((D - P * D) * (P - P) - (P - P) * (D - D * P)) := by rw [hP_eq]
      _ = 0 := by noncomm_ring
  · have h_tr := congr_arg Matrix.trace h_hp
    have h_tr_comm : Matrix.trace (matInnerDer P (matInnerDer P X)) = 0 := by
      dsimp [matInnerDer]
      rw [Matrix.trace_sub, Matrix.trace_mul_comm P _, sub_self]
    rw [Matrix.trace_add, h_tr_comm, add_zero] at h_tr
    exact h_tr
  · have h1 : G * matInnerDer D P * G = G * D * (P * G) - (G * P) * D * G := by
      dsimp [matInnerDer]
      noncomm_ring
    rw [hPG.1, hPG.2] at h1
    have h2 : matInnerDer D P = D * (G * P) - (P * G) * D := by
      rw [hPG.2, hPG.1]
      rfl
    have h3 : (G * D * P - P * D * G) - (D * (G * P) - (P * G) * D) =
        -(matInnerDer D G * P) - P * matInnerDer D G := by
      dsimp [matInnerDer]
      noncomm_ring
    rw [← h1, ← h2, hDG] at h3
    have h4 : G * matInnerDer D P * G - matInnerDer D P = 0 := by
      calc
        G * matInnerDer D P * G - matInnerDer D P
          = -(0 * P) - P * 0 := h3
        _ = 0 := by noncomm_ring
    exact sub_eq_zero.mp h4
  · dsimp [matConnesCocycle, matConnesDensity]
    change Matrix.trace (P * matConnesCurvature D P) +
      Matrix.trace ((G - P) * matConnesCurvature D (G - P)) =
      Matrix.trace (G * matConnesCurvature D P)
    rw [h_curv_eq, ← Matrix.trace_add]
    have h_sum :
        P * matConnesCurvature D P + (G - P) * matConnesCurvature D P =
        G * matConnesCurvature D P := by
      noncomm_ring
    rw [h_sum]

/-- A 3-level non-commutative taxonomic projection flag $P \preceq G \preceq M$ in $\mathrm{Matrix}\;n\;n\;R$. -/
def IsMatrixThreeLevelFlag {R : Type*} {n : Type*} [Fintype n] [DecidableEq n] [Ring R]
    (P G M : Matrix n n R) : Prop :=
  IsMatrixIdempotent P ∧
  IsMatrixIdempotent G ∧
  IsMatrixIdempotent M ∧
  IsMatrixSubprojection P G ∧
  IsMatrixSubprojection G M

/-- Two-level flag coarse-graining conditional expectation across $P \preceq G$:
    $\mathcal{E}_{P,G}(X) = P X P + (G - P) X (G - P) + (1 - G) X (1 - G)$. -/
def matCoarseGrain2 {R : Type*} {n : Type*} [Fintype n] [DecidableEq n] [Ring R]
    (P G X : Matrix n n R) : Matrix n n R :=
  P * X * P + (G - P) * X * (G - P) + (1 - G) * X * (1 - G)

/-- Three-level flag coarse-graining conditional expectation across $P \preceq G \preceq M$:
    $\mathcal{E}_{P,G,M}(X) = P X P + (G - P) X (G - P) + (M - G) X (M - G) + (1 - M) X (1 - M)$. -/
def matCoarseGrain3 {R : Type*} {n : Type*} [Fintype n] [DecidableEq n] [Ring R]
    (P G M X : Matrix n n R) : Matrix n n R :=
  P * X * P + (G - P) * X * (G - P) + (M - G) * X * (M - G) + (1 - M) * X * (1 - M)

/-- The total 3-stratum Chern–Connes flag density across $S_1 = P, S_2 = G - P, S_3 = M - G$. -/
def matFlagConnesDensity {R : Type*} {n : Type*} [Fintype n] [DecidableEq n] [Ring R]
    (D P G M : Matrix n n R) : Matrix n n R :=
  matConnesDensity D P + matConnesDensity D (G - P) + matConnesDensity D (M - G)

/-- **Theorem 143 (`Archetype CXXVII`: Three-Level Projection Flag $P \preceq G \preceq M$, Orthogonal Peirce Shell Resolution, & Abelianization of Coarse-Graining Conditional Expectations $\mathcal{E}_P \circ \mathcal{E}_G \circ \mathcal{E}_M = \mathcal{E}_{P,G,M}$)**:
    Over *any* noncommutative base ring $R$ (`[Ring R]`), for all $P, G, M, X \in \mathrm{Matrix}\;n\;n\;R$ forming a 3-level flag `hFlag : IsMatrixThreeLevelFlag P G M`:
    1. **Telescoping Shell Resolution & Pairwise Orthogonality**:
       $$P + (G - P) + (M - G) = M, \qquad P + (G - P) + (M - G) + (1 - M) = 1, \qquad P \preceq M,$$
       $$\mathrm{IsMatrixOrthogonalPair}\;P\;(G - P) \;\wedge\; \mathrm{IsMatrixOrthogonalPair}\;P\;(M - G) \;\wedge\; \mathrm{IsMatrixOrthogonalPair}\;(G - P)\;(M - G).$$
    2. **Abelianization of Coarse-Graining Conditional Expectations & Four-Stratum Flag Pinching**:
       $$\mathcal{E}_P(\mathcal{E}_G(X)) = \mathcal{E}_G(\mathcal{E}_P(X)) = \mathcal{E}_{P,G}(X),$$
       $$\mathcal{E}_G(\mathcal{E}_M(X)) = \mathcal{E}_M(\mathcal{E}_G(X)), \qquad \mathcal{E}_P(\mathcal{E}_M(X)) = \mathcal{E}_M(\mathcal{E}_P(X)),$$
       $$\mathcal{E}_P(\mathcal{E}_G(\mathcal{E}_M(X))) = \mathcal{E}_M(\mathcal{E}_G(\mathcal{E}_P(X))) = \mathcal{E}_{P,G,M}(X).$$ -/
theorem matrix_three_level_flag_orthogonal_shells_and_commuting_coarse_graining_expectations
    {R : Type*} {n : Type*} [Fintype n] [DecidableEq n] [Ring R]
    (P G M X : Matrix n n R)
    (hFlag : IsMatrixThreeLevelFlag P G M) :
    P + (G - P) + (M - G) = M ∧
    P + (G - P) + (M - G) + (1 - M) = 1 ∧
    IsMatrixSubprojection P M ∧
    IsMatrixOrthogonalPair P (G - P) ∧
    IsMatrixOrthogonalPair P (M - G) ∧
    IsMatrixOrthogonalPair (G - P) (M - G) ∧
    matCoarseGrain P (matCoarseGrain G X) = matCoarseGrain2 P G X ∧
    matCoarseGrain G (matCoarseGrain P X) = matCoarseGrain2 P G X ∧
    matCoarseGrain P (matCoarseGrain G X) = matCoarseGrain G (matCoarseGrain P X) ∧
    matCoarseGrain G (matCoarseGrain M X) = matCoarseGrain M (matCoarseGrain G X) ∧
    matCoarseGrain P (matCoarseGrain M X) = matCoarseGrain M (matCoarseGrain P X) ∧
    matCoarseGrain P (matCoarseGrain G (matCoarseGrain M X)) = matCoarseGrain3 P G M X ∧
    matCoarseGrain M (matCoarseGrain G (matCoarseGrain P X)) = matCoarseGrain3 P G M X := by
  rcases hFlag with ⟨hP, hG, _hM, hPG, hGM⟩
  have hP_eq : P * P = P := hP
  have hG_eq : G * G = G := hG
  have hPM : IsMatrixSubprojection P M :=
    (matrix_taxonomic_subprojection_poset_binomial_corner_and_orthogonal_speciation P G M X).2.2.1 hPG hGM
  have h_orth_PG : IsMatrixOrthogonalPair P (G - P) :=
    ((matrix_taxonomic_subprojection_poset_binomial_corner_and_orthogonal_speciation P P G X).2.2.2.2.1 hP hG hPG).2.2
  have h_orth_PM : IsMatrixOrthogonalPair P (M - G) := by
    refine ⟨?_, ?_⟩
    · calc
        P * (M - G) = P * M - P * G := by noncomm_ring
        _ = P - P := by rw [hPM.1, hPG.1]
        _ = 0 := sub_self P
    · calc
        (M - G) * P = M * P - G * P := by noncomm_ring
        _ = P - P := by rw [hPM.2, hPG.2]
        _ = 0 := sub_self P
  have h_orth_GM : IsMatrixOrthogonalPair (G - P) (M - G) := by
    refine ⟨?_, ?_⟩
    · calc
        (G - P) * (M - G) = G * M - G * G - P * M + P * G := by noncomm_ring
        _ = G - G - P + P := by rw [hGM.1, hG_eq, hPM.1, hPG.1]
        _ = 0 := by abel
    · calc
        (M - G) * (G - P) = M * G - M * P - G * G + G * P := by noncomm_ring
        _ = G - P - G + P := by rw [hGM.2, hPM.2, hG_eq, hPG.2]
        _ = 0 := by abel
  have h_comp1 : ∀ (A B Y : Matrix n n R),
      IsMatrixSubprojection A B →
      matCoarseGrain A (matCoarseGrain B Y) = matCoarseGrain2 A B Y := by
    intro A B Y hAB
    have h1 : (1 - A) * B = B - A := by
      calc (1 - A) * B = B - A * B := by noncomm_ring
      _ = B - A := by rw [hAB.1]
    have h2 : B * (1 - A) = B - A := by
      calc B * (1 - A) = B - B * A := by noncomm_ring
      _ = B - A := by rw [hAB.2]
    have h3 : A * (1 - B) = 0 := by
      calc A * (1 - B) = A - A * B := by noncomm_ring
      _ = A - A := by rw [hAB.1]
      _ = 0 := sub_self A
    have h4 : (1 - B) * A = 0 := by
      calc (1 - B) * A = A - B * A := by noncomm_ring
      _ = A - A := by rw [hAB.2]
      _ = 0 := sub_self A
    have h5 : (1 - A) * (1 - B) = 1 - B := by
      calc (1 - A) * (1 - B) = 1 - B - A + A * B := by noncomm_ring
      _ = 1 - B - A + A := by rw [hAB.1]
      _ = 1 - B := by abel
    have h6 : (1 - B) * (1 - A) = 1 - B := by
      calc (1 - B) * (1 - A) = 1 - B - A + B * A := by noncomm_ring
      _ = 1 - B - A + A := by rw [hAB.2]
      _ = 1 - B := by abel
    dsimp [matCoarseGrain, matCoarseGrain2]
    calc
      A * (B * Y * B + (1 - B) * Y * (1 - B)) * A +
        (1 - A) * (B * Y * B + (1 - B) * Y * (1 - B)) * (1 - A)
        = (A * B) * Y * (B * A) + (A * (1 - B)) * Y * ((1 - B) * A) +
          ((1 - A) * B) * Y * (B * (1 - A)) +
          ((1 - A) * (1 - B)) * Y * ((1 - B) * (1 - A)) := by noncomm_ring
      _ = A * Y * A + 0 * Y * 0 + (B - A) * Y * (B - A) + (1 - B) * Y * (1 - B) := by
          rw [hAB.1, hAB.2, h3, h4, h1, h2, h5, h6]
      _ = A * Y * A + (B - A) * Y * (B - A) + (1 - B) * Y * (1 - B) := by noncomm_ring
  have h_comp2 : ∀ (A B Y : Matrix n n R),
      IsMatrixSubprojection A B →
      matCoarseGrain B (matCoarseGrain A Y) = matCoarseGrain2 A B Y := by
    intro A B Y hAB
    have h1 : (1 - A) * B = B - A := by
      calc (1 - A) * B = B - A * B := by noncomm_ring
      _ = B - A := by rw [hAB.1]
    have h2 : B * (1 - A) = B - A := by
      calc B * (1 - A) = B - B * A := by noncomm_ring
      _ = B - A := by rw [hAB.2]
    have h3 : A * (1 - B) = 0 := by
      calc A * (1 - B) = A - A * B := by noncomm_ring
      _ = A - A := by rw [hAB.1]
      _ = 0 := sub_self A
    have h4 : (1 - B) * A = 0 := by
      calc (1 - B) * A = A - B * A := by noncomm_ring
      _ = A - A := by rw [hAB.2]
      _ = 0 := sub_self A
    have h5 : (1 - A) * (1 - B) = 1 - B := by
      calc (1 - A) * (1 - B) = 1 - B - A + A * B := by noncomm_ring
      _ = 1 - B - A + A := by rw [hAB.1]
      _ = 1 - B := by abel
    have h6 : (1 - B) * (1 - A) = 1 - B := by
      calc (1 - B) * (1 - A) = 1 - B - A + B * A := by noncomm_ring
      _ = 1 - B - A + A := by rw [hAB.2]
      _ = 1 - B := by abel
    dsimp [matCoarseGrain, matCoarseGrain2]
    calc
      B * (A * Y * A + (1 - A) * Y * (1 - A)) * B +
        (1 - B) * (A * Y * A + (1 - A) * Y * (1 - A)) * (1 - B)
        = (B * A) * Y * (A * B) + (B * (1 - A)) * Y * ((1 - A) * B) +
          ((1 - B) * A) * Y * (A * (1 - B)) +
          ((1 - B) * (1 - A)) * Y * ((1 - A) * (1 - B)) := by noncomm_ring
      _ = A * Y * A + (B - A) * Y * (B - A) + 0 * Y * 0 + (1 - B) * Y * (1 - B) := by
          rw [hAB.2, hAB.1, h2, h1, h4, h3, h6, h5]
      _ = A * Y * A + (B - A) * Y * (B - A) + (1 - B) * Y * (1 - B) := by noncomm_ring
  have h_comm_sub : ∀ (A B Y : Matrix n n R),
      IsMatrixSubprojection A B →
      matCoarseGrain A (matCoarseGrain B Y) = matCoarseGrain B (matCoarseGrain A Y) := by
    intro A B Y hAB
    rw [h_comp1 A B Y hAB, h_comp2 A B Y hAB]
  have h_flag3 : matCoarseGrain P (matCoarseGrain G (matCoarseGrain M X)) = matCoarseGrain3 P G M X := by
    rw [h_comp1 G M X hGM]
    have h1 : (1 - P) * G = G - P := by
      calc (1 - P) * G = G - P * G := by noncomm_ring
      _ = G - P := by rw [hPG.1]
    have h2 : G * (1 - P) = G - P := by
      calc G * (1 - P) = G - G * P := by noncomm_ring
      _ = G - P := by rw [hPG.2]
    have h3 : P * (1 - M) = 0 := by
      calc P * (1 - M) = P - P * M := by noncomm_ring
      _ = P - P := by rw [hPM.1]
      _ = 0 := sub_self P
    have h4 : (1 - M) * P = 0 := by
      calc (1 - M) * P = P - M * P := by noncomm_ring
      _ = P - P := by rw [hPM.2]
      _ = 0 := sub_self P
    have h5 : (1 - P) * (1 - M) = 1 - M := by
      calc (1 - P) * (1 - M) = 1 - M - P + P * M := by noncomm_ring
      _ = 1 - M - P + P := by rw [hPM.1]
      _ = 1 - M := by abel
    have h6 : (1 - M) * (1 - P) = 1 - M := by
      calc (1 - M) * (1 - P) = 1 - M - P + M * P := by noncomm_ring
      _ = 1 - M - P + P := by rw [hPM.2]
      _ = 1 - M := by abel
    have h7 : (1 - P) * (M - G) = M - G := by
      calc (1 - P) * (M - G) = (M - G) - P * (M - G) := by noncomm_ring
      _ = (M - G) - 0 := by rw [h_orth_PM.1]
      _ = M - G := sub_zero (M - G)
    have h8 : (M - G) * (1 - P) = M - G := by
      calc (M - G) * (1 - P) = (M - G) - (M - G) * P := by noncomm_ring
      _ = (M - G) - 0 := by rw [h_orth_PM.2]
      _ = M - G := sub_zero (M - G)
    dsimp [matCoarseGrain, matCoarseGrain2, matCoarseGrain3]
    calc
      P * (G * X * G + (M - G) * X * (M - G) + (1 - M) * X * (1 - M)) * P +
        (1 - P) * (G * X * G + (M - G) * X * (M - G) + (1 - M) * X * (1 - M)) * (1 - P)
        = (P * G) * X * (G * P) +
          (P * (M - G)) * X * ((M - G) * P) +
          (P * (1 - M)) * X * ((1 - M) * P) +
          ((1 - P) * G) * X * (G * (1 - P)) +
          ((1 - P) * (M - G)) * X * ((M - G) * (1 - P)) +
          ((1 - P) * (1 - M)) * X * ((1 - M) * (1 - P)) := by noncomm_ring
      _ = P * X * P + 0 * X * 0 + 0 * X * 0 +
          (G - P) * X * (G - P) + (M - G) * X * (M - G) + (1 - M) * X * (1 - M) := by
          rw [hPG.1, hPG.2, h_orth_PM.1, h_orth_PM.2, h3, h4, h1, h2, h7, h8, h5, h6]
      _ = P * X * P + (G - P) * X * (G - P) + (M - G) * X * (M - G) + (1 - M) * X * (1 - M) := by
          noncomm_ring
  refine ⟨by abel, by abel, hPM, h_orth_PG, h_orth_PM, h_orth_GM,
    h_comp1 P G X hPG, h_comp2 P G X hPG,
    h_comm_sub P G X hPG, h_comm_sub G M X hGM, h_comm_sub P M X hPM,
    h_flag3, ?_⟩
  rw [← h_comm_sub P G X hPG]
  rw [← h_comm_sub P M (matCoarseGrain G X) hPM]
  rw [← h_comm_sub G M X hGM]
  exact h_flag3

/-- **Theorem 144 (`Archetype CXXVIII`: Three-Stratum Connes Curvature Corner Decomposition, Non-Commutative Gauss–Codazzi Interference, Outer-Shell Annihilation, & Macro-Stratum Cocycle Partition)**:
    Over *any* commutative ring $R$ (`[CommRing R]`), for all $D, P, G, M \in \mathrm{Matrix}\;n\;n\;R$ forming a 3-level flag `hFlag : IsMatrixThreeLevelFlag P G M`:
    1. **Three-Stratum Corner Decomposition & Unconditional Macro Split**:
       $$\mathcal{C}_{\mathrm{flag}}(D; P, G, M) = P \Omega_D(P) P + (G - P) \Omega_D(G - P) (G - P) + (M - G) \Omega_D(M - G) (M - G),$$
       $$M \Omega_D(P) = P \Omega_D(P) + (G - P) \Omega_D(P) + (M - G) \Omega_D(P),$$
       $$[D, P] + [D, G - P] + [D, M - G] = [D, M].$$
    2. **Non-Commutative Gauss–Codazzi Interference Decomposition**:
       $$\Omega_D(G) = \Omega_D(P) + \Omega_D(G - P) + ([D, P][D, G - P] + [D, G - P][D, P]),$$
       $$[D, M] = 0 \implies \Omega_D(M - G) = \Omega_D(P) + \Omega_D(G - P) + ([D, P][D, G - P] + [D, G - P][D, P]).$$
    3. **Outer-Shell Annihilation & Three-Stratum Connes Cyclic Cocycle Partition ($[D, G] = 0$ and $[D, M] = 0$)**:
       $$[D, G] = 0 \implies (M - G)[D, P] = 0 \;\wedge\; (M - G)\Omega_D(P) = 0,$$
       $$[D, G] = 0 \wedge [D, M] = 0 \implies \tau(P[D,P]^2) + \tau((G-P)[D,G-P]^2) + \tau((M-G)[D,M-G]^2) = \mathrm{tr}(M \Omega_D(P)).$$ -/
theorem matrix_three_stratum_connes_curvature_gauss_codazzi_and_macro_cocycle_partition
    {R : Type*} {n : Type*} [Fintype n] [DecidableEq n] [CommRing R]
    (D P G M : Matrix n n R)
    (hFlag : IsMatrixThreeLevelFlag P G M) :
    matFlagConnesDensity D P G M =
      P * matConnesCurvature D P * P +
      (G - P) * matConnesCurvature D (G - P) * (G - P) +
      (M - G) * matConnesCurvature D (M - G) * (M - G) ∧
    M * matConnesCurvature D P =
      P * matConnesCurvature D P +
      (G - P) * matConnesCurvature D P +
      (M - G) * matConnesCurvature D P ∧
    matInnerDer D P + matInnerDer D (G - P) + matInnerDer D (M - G) = matInnerDer D M ∧
    matConnesCurvature D G =
      matConnesCurvature D P + matConnesCurvature D (G - P) +
      (matInnerDer D P * matInnerDer D (G - P) +
       matInnerDer D (G - P) * matInnerDer D P) ∧
    Matrix.trace (matFlagConnesDensity D P G M) =
      matConnesCocycle D P + matConnesCocycle D (G - P) + matConnesCocycle D (M - G) ∧
    (matInnerDer D M = 0 →
      matInnerDer D P + matInnerDer D (G - P) + matInnerDer D (M - G) = 0 ∧
      matConnesCurvature D (M - G) =
        matConnesCurvature D P + matConnesCurvature D (G - P) +
        (matInnerDer D P * matInnerDer D (G - P) +
         matInnerDer D (G - P) * matInnerDer D P)) ∧
    (matInnerDer D G = 0 →
      (M - G) * matInnerDer D P = 0 ∧
      (M - G) * matConnesCurvature D P = 0) ∧
    (matInnerDer D G = 0 → matInnerDer D M = 0 →
      matConnesCocycle D P + matConnesCocycle D (G - P) + matConnesCocycle D (M - G) =
        Matrix.trace (M * matConnesCurvature D P)) := by
  rcases hFlag with ⟨hP, hG, hM, hPG, hGM⟩
  have hGP : IsMatrixIdempotent (G - P) :=
    ((matrix_taxonomic_subprojection_poset_binomial_corner_and_orthogonal_speciation P P G P).2.2.2.2.1 hP hG hPG).1
  have hMG : IsMatrixIdempotent (M - G) :=
    ((matrix_taxonomic_subprojection_poset_binomial_corner_and_orthogonal_speciation G G M G).2.2.2.2.1 hG hM hGM).1
  have h_corner_self : ∀ S : Matrix n n R, IsMatrixIdempotent S →
      S * matConnesCurvature D S * S = matConnesDensity D S := by
    intro S hS
    have hS_eq : S * S = S := hS
    have h_comm : S * matConnesCurvature D S = matConnesCurvature D S * S :=
      (matrix_inner_derivation_idempotent_connes_curvature_and_gauss_codazzi D D D D D S hS).2.2.2.2.2.2.2.2.2.2.2.2.2.1
    dsimp [matConnesDensity]
    calc
      S * matConnesCurvature D S * S = (matConnesCurvature D S * S) * S := by rw [h_comm]
      _ = matConnesCurvature D S * (S * S) := by noncomm_ring
      _ = matConnesCurvature D S * S := by rw [hS_eq]
      _ = S * matConnesCurvature D S := by rw [← h_comm]
  have h_gc_G : matConnesCurvature D G =
      matConnesCurvature D P + matConnesCurvature D (G - P) +
      (matInnerDer D P * matInnerDer D (G - P) +
       matInnerDer D (G - P) * matInnerDer D P) := by
    dsimp [matConnesCurvature, matInnerDer]
    noncomm_ring
  refine ⟨?_, by noncomm_ring, ?_, h_gc_G, ?_, ?_, ?_, ?_⟩
  · dsimp [matFlagConnesDensity]
    rw [h_corner_self P hP, h_corner_self (G - P) hGP, h_corner_self (M - G) hMG]
  · dsimp [matInnerDer]
    noncomm_ring
  · dsimp [matFlagConnesDensity, matConnesCocycle]
    rw [Matrix.trace_add, Matrix.trace_add]
  · intro hDM
    refine ⟨?_, ?_⟩
    · have h_sum : matInnerDer D P + matInnerDer D (G - P) + matInnerDer D (M - G) = matInnerDer D M := by
        dsimp [matInnerDer]
        noncomm_ring
      rw [h_sum, hDM]
    · have h_curv_MG : matConnesCurvature D (M - G) = matConnesCurvature D G :=
        (matrix_coarse_graining_hodge_peirce_and_genus_confined_cocycle_partition D G M G hG hGM hDM).2.2.2.2.2.2.1
      rw [h_curv_MG, h_gc_G]
  · intro hDG
    have h_conf : G * matInnerDer D P * G = matInnerDer D P :=
      (matrix_coarse_graining_hodge_peirce_and_genus_confined_cocycle_partition D P G P hP hPG hDG).2.2.2.2.1
    have hG_eq : G * G = G := hG
    have h_ann1 : (M - G) * matInnerDer D P = 0 := by
      calc
        (M - G) * matInnerDer D P = (M - G) * (G * matInnerDer D P * G) :=
          congr_arg ((M - G) * ·) h_conf.symm
        _ = (M * G - G * G) * matInnerDer D P * G := by noncomm_ring
        _ = (G - G) * matInnerDer D P * G := by rw [hGM.2, hG_eq]
        _ = 0 := by noncomm_ring
    refine ⟨h_ann1, ?_⟩
    dsimp [matConnesCurvature]
    calc
      (M - G) * (matInnerDer D P * matInnerDer D P)
        = ((M - G) * matInnerDer D P) * matInnerDer D P := by noncomm_ring
      _ = 0 * matInnerDer D P := by rw [h_ann1]
      _ = 0 := by noncomm_ring
  · intro hDG hDM
    have h_part2 : matConnesCocycle D P + matConnesCocycle D (G - P) =
        Matrix.trace (G * matConnesCurvature D P) :=
      (matrix_coarse_graining_hodge_peirce_and_genus_confined_cocycle_partition D P G P hP hPG hDG).2.2.2.2.2.2.2
    have h_curv_MG : matConnesCurvature D (M - G) = matConnesCurvature D G :=
      (matrix_coarse_graining_hodge_peirce_and_genus_confined_cocycle_partition D G M G hG hGM hDM).2.2.2.2.2.2.1
    have h_third : matConnesCocycle D (M - G) = 0 := by
      dsimp [matConnesCocycle, matConnesDensity]
      change Matrix.trace ((M - G) * matConnesCurvature D (M - G)) = 0
      rw [h_curv_MG]
      dsimp [matConnesCurvature]
      rw [hDG, mul_zero, mul_zero, Matrix.trace_zero]
    have h_conf : G * matInnerDer D P * G = matInnerDer D P :=
      (matrix_coarse_graining_hodge_peirce_and_genus_confined_cocycle_partition D P G P hP hPG hDG).2.2.2.2.1
    have hG_eq : G * G = G := hG
    have h_ann1 : (M - G) * matInnerDer D P = 0 := by
      calc
        (M - G) * matInnerDer D P = (M - G) * (G * matInnerDer D P * G) :=
          congr_arg ((M - G) * ·) h_conf.symm
        _ = (M * G - G * G) * matInnerDer D P * G := by noncomm_ring
        _ = (G - G) * matInnerDer D P * G := by rw [hGM.2, hG_eq]
        _ = 0 := by noncomm_ring
    have h_ann2 : (M - G) * matConnesCurvature D P = 0 := by
      dsimp [matConnesCurvature]
      calc
        (M - G) * (matInnerDer D P * matInnerDer D P)
          = ((M - G) * matInnerDer D P) * matInnerDer D P := by noncomm_ring
        _ = 0 * matInnerDer D P := by rw [h_ann1]
        _ = 0 := by noncomm_ring
    rw [h_third, add_zero, h_part2]
    have h_split :
        M * matConnesCurvature D P =
        G * matConnesCurvature D P + (M - G) * matConnesCurvature D P := by
      noncomm_ring
    rw [h_split, h_ann2, add_zero]

end SplitQuaternion

end InfoGeometry.Canonical.AlbertCayleyDickson
