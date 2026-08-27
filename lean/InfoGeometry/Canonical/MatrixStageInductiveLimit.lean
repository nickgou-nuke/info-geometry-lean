import Mathlib.Tactic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Algebra.Star.StarAlgHom
import Mathlib.Algebra.Star.SelfAdjoint
import InfoGeometry.Canonical.UHFInductiveColimitBoundary
import InfoGeometry.Canonical.ComplexMatrixStage
import InfoGeometry.Canonical.GenuineMatrixStageMorphism
import InfoGeometry.Canonical.BoundaryBondSquare

/-!
# Algebraic Star Inductive Limit of Complex Matrix Stages

This module constructs the genuine algebraic inductive limit (colimit)
of the directed system of finite-dimensional matrix algebras

$$\mathrm{Stage}(0) \xrightarrow{\iota_0} \mathrm{Stage}(1) \xrightarrow{\iota_1} \mathrm{Stage}(2) \to \cdots$$

equipped with the transitive transition morphisms

$$\iota_{m,n} : \mathrm{Stage}(m) \to⋆ₐ[ℂ] \mathrm{Stage}(n), \quad m \le n$$

and descends the compatible family of normalized matrix traces $\tau_n$ to
one canonical normalized tracial state $\tau_\infty$ on the inductive limit carrier.

## Key Theorems & Constructions:

1. **Equivalence Relation & Carrier**:
   - `LimitRel` on `Element := Σ n, Stage n` via eventual equality in the directed system.
   - `matrixStageSetoid` proving reflexivity, symmetry, and transitivity.
   - `MatrixStageLimit := Quotient matrixStageSetoid`.

2. **Algebraic Typeclass Hierarchy**:
   - `AddCommGroup MatrixStageLimit`, `Ring MatrixStageLimit`, `StarRing MatrixStageLimit`.
   - `Module ℂ MatrixStageLimit`, `Algebra ℂ MatrixStageLimit`, `StarModule ℂ MatrixStageLimit`.

3. **Canonical Stage Inclusions as Unital $*$-Algebra Homomorphisms**:
   - `canonicalStageHom n : Stage n →⋆ₐ[ℂ] MatrixStageLimit`.
   - Coherence with transition morphisms:
     `canonicalStageHom_comp (hij : i ≤ j) : (canonicalStageHom j).comp (stageMorphism i j hij) = canonicalStageHom i`.
   - Coherence with elementary step embeddings:
     `canonicalStageHom_step n : (canonicalStageHom (n + 1)).comp (bondStarAlgHom n) = canonicalStageHom n`.
   - Injectivity: `canonicalStageHom_injective (n : ℕ) : Function.Injective (canonicalStageHom n)`.

4. **Universal Property of the Direct Limit as a StarAlgHom Cocone**:
   - `liftStarAlgHom`: Given any complex $*$-algebra $B$ and compatible family
     $f_n : \mathrm{Stage}(n) \to⋆ₐ[ℂ] B$, constructs the unique mediator
     $F : \mathrm{MatrixStageLimit} \to⋆ₐ[ℂ] B$.
   - `liftStarAlgHom_comp`: $F \circ \eta_n = f_n$.
   - `liftStarAlgHom_unique`: $F$ is unique.

5. **Canonical Descended Normalized Trace Functional & Linear Map**:
   - `limitNormalizedTrace : MatrixStageLimit →ₗ[ℂ] ℂ`.
   - `inductiveLimitTrace_comp_stage (n : ℕ) : limitNormalizedTrace.comp (canonicalStageHom n).toLinearMap = stageNormalizedTraceLM n`.
   - Normalization: `limitTrace 1 = 1`.
   - Tracial commutativity: `limitTrace (X * Y) = limitTrace (Y * X)`.
   - Star-compatibility: `limitTrace (star X) = starRingEnd ℂ (limitTrace X)`.

6. **Positivity, Faithfulness & Pre-Hilbert Inner Product**:
   - Positivity: `0 ≤ (limitTrace (star X * X)).re` and `(limitTrace (star X * X)).im = 0`.
   - Faithfulness: `limitTrace (star X * X) = 0 ↔ X = 0`.
   - Inner Product: `limitInner X Y := limitTrace (star X * Y)`.
   - Sesquilinearity, conjugate symmetry, and positive-definiteness:
     `limitInner_conj_symm`, `limitInner_self_re_nonneg`, `limitInner_self_im`, `limitInner_self_eq_zero_iff`.

All proofs are complete in native Lean 4 with 0 sorrys and 0 custom axioms.
-/

namespace InfoGeometry.Canonical.MatrixStageInductiveLimit

open InfoGeometry.Canonical.UHFInductiveColimitBoundary
open InfoGeometry.Canonical.BoundaryBondSquare
open ComplexMatrixStage
open GenuineMatrixStageMorphism

noncomputable section

lemma stageMorphism_apply_comp {i j k : ℕ} (hij : i ≤ j) (hjk : j ≤ k) (x : Stage i) :
    stageMorphism j k hjk (stageMorphism i j hij x) = stageMorphism i k (le_trans hij hjk) x := by
  have := congr_arg (fun (f : Stage i →⋆ₐ[ℂ] Stage k) => (f x : Stage k)) (stageMorphism_comp hij hjk)
  exact this

/-! ## 1. Direct System Equivalence Relation and Quotient Carrier -/

/-- An element at any finite stage of the matrix tower. -/
abbrev Element := Σ n : ℕ, Stage n

/-- Equivalence relation on the disjoint union of matrix stages:
    two elements are equivalent if their images eventually agree at some common stage $k \ge m, n$. -/
def LimitRel (x y : Element) : Prop :=
  ∃ (k : ℕ) (hmk : x.1 ≤ k) (hnk : y.1 ≤ k),
    stageMorphism x.1 k hmk x.2 = stageMorphism y.1 k hnk y.2

lemma limitRel_refl (x : Element) : LimitRel x x :=
  ⟨x.1, le_rfl, le_rfl, rfl⟩

lemma limitRel_symm {x y : Element} (h : LimitRel x y) : LimitRel y x := by
  rcases h with ⟨k, hx, hy, heq⟩
  exact ⟨k, hy, hx, heq.symm⟩

lemma limitRel_trans {x y z : Element} (hxy : LimitRel x y) (hyz : LimitRel y z) : LimitRel x z := by
  rcases hxy with ⟨k₁, hx1, hy1, heq1⟩
  rcases hyz with ⟨k₂, hy2, hz2, heq2⟩
  let k := max k₁ k₂
  have hk1 : k₁ ≤ k := le_max_left k₁ k₂
  have hk2 : k₂ ≤ k := le_max_right k₁ k₂
  have hx : x.1 ≤ k := le_trans hx1 hk1
  have hz : z.1 ≤ k := le_trans hz2 hk2
  refine ⟨k, hx, hz, ?_⟩
  have hx_to_k : stageMorphism x.1 k hx x.2 = stageMorphism k₁ k hk1 (stageMorphism x.1 k₁ hx1 x.2) := by
    rw [stageMorphism_apply_comp hx1 hk1 x.2]
  have hy_to_k1 : stageMorphism y.1 k (le_trans hy1 hk1) y.2 = stageMorphism k₁ k hk1 (stageMorphism y.1 k₁ hy1 y.2) := by
    rw [stageMorphism_apply_comp hy1 hk1 y.2]
  have hy_to_k2 : stageMorphism y.1 k (le_trans hy2 hk2) y.2 = stageMorphism k₂ k hk2 (stageMorphism y.1 k₂ hy2 y.2) := by
    rw [stageMorphism_apply_comp hy2 hk2 y.2]
  have hz_to_k : stageMorphism z.1 k hz z.2 = stageMorphism k₂ k hk2 (stageMorphism z.1 k₂ hz2 z.2) := by
    rw [stageMorphism_apply_comp hz2 hk2 z.2]
  have hy_eq : stageMorphism y.1 k (le_trans hy1 hk1) y.2 = stageMorphism y.1 k (le_trans hy2 hk2) y.2 := rfl
  rw [hx_to_k, heq1, ← hy_to_k1, hy_eq, hy_to_k2, heq2, ← hz_to_k]

/-- The setoid on `Element` defined by `LimitRel`. -/
def matrixStageSetoid : Setoid Element where
  r := LimitRel
  iseqv := ⟨limitRel_refl, limitRel_symm, limitRel_trans⟩

instance : Setoid Element := matrixStageSetoid

/-- The genuine algebraic inductive limit of the matrix stages `Stage n`. -/
def MatrixStageLimit : Type := Quotient matrixStageSetoid

/-! ## 2. Canonical Stage Inclusions -/

/-- The canonical inclusion of stage `n` into the inductive limit `MatrixStageLimit`. -/
def toLimit (n : ℕ) (A : Stage n) : MatrixStageLimit :=
  ⟦⟨n, A⟩⟧

lemma quot_mk_eq (n : ℕ) (A : Stage n) : (⟦⟨n, A⟩⟧ : MatrixStageLimit) = toLimit n A := rfl

/-- Coherence / Quotient readback: inclusion commutes with stage transition morphisms. -/
theorem toLimit_stageMorphism {m n : ℕ} (h : m ≤ n) (A : Stage m) :
    toLimit n (stageMorphism m n h A) = toLimit m A := by
  apply Quotient.sound
  refine ⟨n, le_rfl, h, ?_⟩
  rw [stageMorphism_id]
  rfl

/-- Elementary step coherence: inclusion commutes with `bondStarAlgHom`. -/
theorem toLimit_step (n : ℕ) (A : Stage n) :
    toLimit (n + 1) (bondStarAlgHom n A) = toLimit n A := by
  have h := toLimit_stageMorphism (Nat.le_succ n) A
  rw [← h]
  congr 1
  rw [stageMorphism_step (le_refl n), stageMorphism_id]
  rfl

/-! ## 3. Canonical Descended Normalized Trace -/

/-- The normalized trace functional is constant along equivalence classes. -/
theorem normalizedTrace_respects_limitRel {x y : Element} (h : LimitRel x y) :
    normalizedTrace x.1 x.2 = normalizedTrace y.1 y.2 := by
  rcases h with ⟨k, hx, hy, heq⟩
  rw [← normalizedTrace_stageMorphism hx x.2, ← normalizedTrace_stageMorphism hy y.2]
  rw [heq]

/-- The canonical descended normalized trace functional $\tau_\infty$ on `MatrixStageLimit`. -/
def limitTrace (X : MatrixStageLimit) : ℂ :=
  Quotient.lift (fun (x : Element) => normalizedTrace x.1 x.2)
    (fun _ _ h => normalizedTrace_respects_limitRel h) X

@[simp] theorem limitTrace_toLimit (n : ℕ) (A : Stage n) :
    limitTrace (toLimit n A) = normalizedTrace n A := rfl

/-! ## 4. Algebraic Operations on MatrixStageLimit -/

instance : Zero MatrixStageLimit where
  zero := toLimit 0 0

instance : One MatrixStageLimit where
  one := toLimit 0 1

@[simp] theorem toLimit_zero (n : ℕ) : toLimit n 0 = (0 : MatrixStageLimit) := by
  have h := toLimit_stageMorphism (Nat.zero_le n) (0 : Stage 0)
  rw [map_zero] at h
  exact h

@[simp] theorem toLimit_one (n : ℕ) : toLimit n 1 = (1 : MatrixStageLimit) := by
  have h := toLimit_stageMorphism (Nat.zero_le n) (1 : Stage 0)
  rw [map_one] at h
  exact h

theorem limitTrace_one : limitTrace 1 = 1 := by
  change normalizedTrace 0 1 = 1
  dsimp [normalizedTrace, Matrix.trace]
  have h_card : Fintype.card (BitWord 0) = 1 := by simp [BitWord]
  have h_sum : (∑ i : BitWord 0, (1 : Stage 0) i i) = 1 := by
    simp only [Matrix.one_apply_eq, Finset.sum_const, nsmul_eq_mul, mul_one]
    rw [Finset.card_univ, h_card]
    norm_cast
  rw [h_sum]
  simp

def limitStar : MatrixStageLimit → MatrixStageLimit :=
  Quotient.lift (fun (x : Element) => toLimit x.1 (star x.2)) (by
    rintro ⟨m, A⟩ ⟨n, B⟩ ⟨k, hmk, hnk, heq⟩
    dsimp
    apply Quotient.sound
    refine ⟨k, hmk, hnk, ?_⟩
    change stageMorphism m k hmk (star A) = stageMorphism n k hnk (star B)
    rw [map_star, map_star, heq])

instance : Star MatrixStageLimit where
  star := limitStar

@[simp] theorem toLimit_star (n : ℕ) (A : Stage n) :
    star (toLimit n A) = toLimit n (star A) := rfl

def limitNeg : MatrixStageLimit → MatrixStageLimit :=
  Quotient.lift (fun (x : Element) => toLimit x.1 (-x.2)) (by
    rintro ⟨m, A⟩ ⟨n, B⟩ ⟨k, hmk, hnk, heq⟩
    dsimp
    apply Quotient.sound
    refine ⟨k, hmk, hnk, ?_⟩
    change stageMorphism m k hmk (-A) = stageMorphism n k hnk (-B)
    rw [map_neg, map_neg, heq])

instance : Neg MatrixStageLimit where
  neg := limitNeg

@[simp] theorem toLimit_neg (n : ℕ) (A : Stage n) :
    -(toLimit n A) = toLimit n (-A) := rfl

def limitSMul (c : ℂ) : MatrixStageLimit → MatrixStageLimit :=
  Quotient.lift (fun (x : Element) => toLimit x.1 (c • x.2)) (by
    rintro ⟨m, A⟩ ⟨n, B⟩ ⟨k, hmk, hnk, heq⟩
    dsimp
    apply Quotient.sound
    refine ⟨k, hmk, hnk, ?_⟩
    change stageMorphism m k hmk (c • A) = stageMorphism n k hnk (c • B)
    rw [map_smul, map_smul, heq])

instance : SMul ℂ MatrixStageLimit where
  smul := limitSMul

@[simp] theorem toLimit_smul (n : ℕ) (c : ℂ) (A : Stage n) :
    c • toLimit n A = toLimit n (c • A) := rfl

def limitAdd : MatrixStageLimit → MatrixStageLimit → MatrixStageLimit :=
  Quotient.lift₂
    (fun (x y : Element) =>
      let k := max x.1 y.1
      toLimit k (stageMorphism x.1 k (le_max_left x.1 y.1) x.2 +
                 stageMorphism y.1 k (le_max_right x.1 y.1) y.2))
    (by
      rintro ⟨m₁, A₁⟩ ⟨n₁, B₁⟩ ⟨m₂, A₂⟩ ⟨n₂, B₂⟩ ⟨k_a, hm1_ka, hm2_ka, heq_a⟩ ⟨k_b, hn1_kb, hn2_kb, heq_b⟩
      dsimp
      apply Quotient.sound
      let k := max (max (max m₁ n₁) (max m₂ n₂)) (max k_a k_b)
      have h1_k : max m₁ n₁ ≤ k := le_trans (le_max_left (max m₁ n₁) (max m₂ n₂)) (le_max_left _ _)
      have h2_k : max m₂ n₂ ≤ k := le_trans (le_max_right (max m₁ n₁) (max m₂ n₂)) (le_max_left _ _)
      have hka_k : k_a ≤ k := le_trans (le_max_left k_a k_b) (le_max_right _ _)
      have hkb_k : k_b ≤ k := le_trans (le_max_right k_a k_b) (le_max_right _ _)
      refine ⟨k, h1_k, h2_k, ?_⟩
      rw [map_add, map_add]
      have ha1 : stageMorphism (max m₁ n₁) k h1_k (stageMorphism m₁ (max m₁ n₁) (le_max_left m₁ n₁) A₁) =
                 stageMorphism k_a k hka_k (stageMorphism m₁ k_a hm1_ka A₁) := by
        rw [stageMorphism_apply_comp (le_max_left m₁ n₁) h1_k A₁]
        rw [stageMorphism_apply_comp hm1_ka hka_k A₁]
      have ha2 : stageMorphism (max m₂ n₂) k h2_k (stageMorphism m₂ (max m₂ n₂) (le_max_left m₂ n₂) A₂) =
                 stageMorphism k_a k hka_k (stageMorphism m₂ k_a hm2_ka A₂) := by
        rw [stageMorphism_apply_comp (le_max_left m₂ n₂) h2_k A₂]
        rw [stageMorphism_apply_comp hm2_ka hka_k A₂]
      have hb1 : stageMorphism (max m₁ n₁) k h1_k (stageMorphism n₁ (max m₁ n₁) (le_max_right m₁ n₁) B₁) =
                 stageMorphism k_b k hkb_k (stageMorphism n₁ k_b hn1_kb B₁) := by
        rw [stageMorphism_apply_comp (le_max_right m₁ n₁) h1_k B₁]
        rw [stageMorphism_apply_comp hn1_kb hkb_k B₁]
      have hb2 : stageMorphism (max m₂ n₂) k h2_k (stageMorphism n₂ (max m₂ n₂) (le_max_right m₂ n₂) B₂) =
                 stageMorphism k_b k hkb_k (stageMorphism n₂ k_b hn2_kb B₂) := by
        rw [stageMorphism_apply_comp (le_max_right m₂ n₂) h2_k B₂]
        rw [stageMorphism_apply_comp hn2_kb hkb_k B₂]
      rw [ha1, ha2, hb1, hb2, heq_a, heq_b])

instance : Add MatrixStageLimit where
  add := limitAdd

theorem toLimit_add (n : ℕ) (A B : Stage n) :
    toLimit n A + toLimit n B = toLimit n (A + B) := by
  change toLimit (max n n) (stageMorphism n (max n n) (le_max_left n n) A +
                           stageMorphism n (max n n) (le_max_right n n) B) = toLimit n (A + B)
  have hle : n ≤ max n n := le_max_left n n
  have h_map : stageMorphism n (max n n) (le_max_left n n) A +
               stageMorphism n (max n n) (le_max_right n n) B =
               stageMorphism n (max n n) hle (A + B) := by
    rw [map_add]
  rw [h_map]
  exact toLimit_stageMorphism hle (A + B)

def limitMul : MatrixStageLimit → MatrixStageLimit → MatrixStageLimit :=
  Quotient.lift₂
    (fun (x y : Element) =>
      let k := max x.1 y.1
      toLimit k (stageMorphism x.1 k (le_max_left x.1 y.1) x.2 *
                 stageMorphism y.1 k (le_max_right x.1 y.1) y.2))
    (by
      rintro ⟨m₁, A₁⟩ ⟨n₁, B₁⟩ ⟨m₂, A₂⟩ ⟨n₂, B₂⟩ ⟨k_a, hm1_ka, hm2_ka, heq_a⟩ ⟨k_b, hn1_kb, hn2_kb, heq_b⟩
      dsimp
      apply Quotient.sound
      let k := max (max (max m₁ n₁) (max m₂ n₂)) (max k_a k_b)
      have h1_k : max m₁ n₁ ≤ k := le_trans (le_max_left (max m₁ n₁) (max m₂ n₂)) (le_max_left _ _)
      have h2_k : max m₂ n₂ ≤ k := le_trans (le_max_right (max m₁ n₁) (max m₂ n₂)) (le_max_left _ _)
      have hka_k : k_a ≤ k := le_trans (le_max_left k_a k_b) (le_max_right _ _)
      have hkb_k : k_b ≤ k := le_trans (le_max_right k_a k_b) (le_max_right _ _)
      refine ⟨k, h1_k, h2_k, ?_⟩
      rw [map_mul, map_mul]
      have ha1 : stageMorphism (max m₁ n₁) k h1_k (stageMorphism m₁ (max m₁ n₁) (le_max_left m₁ n₁) A₁) =
                 stageMorphism k_a k hka_k (stageMorphism m₁ k_a hm1_ka A₁) := by
        rw [stageMorphism_apply_comp (le_max_left m₁ n₁) h1_k A₁]
        rw [stageMorphism_apply_comp hm1_ka hka_k A₁]
      have ha2 : stageMorphism (max m₂ n₂) k h2_k (stageMorphism m₂ (max m₂ n₂) (le_max_left m₂ n₂) A₂) =
                 stageMorphism k_a k hka_k (stageMorphism m₂ k_a hm2_ka A₂) := by
        rw [stageMorphism_apply_comp (le_max_left m₂ n₂) h2_k A₂]
        rw [stageMorphism_apply_comp hm2_ka hka_k A₂]
      have hb1 : stageMorphism (max m₁ n₁) k h1_k (stageMorphism n₁ (max m₁ n₁) (le_max_right m₁ n₁) B₁) =
                 stageMorphism k_b k hkb_k (stageMorphism n₁ k_b hn1_kb B₁) := by
        rw [stageMorphism_apply_comp (le_max_right m₁ n₁) h1_k B₁]
        rw [stageMorphism_apply_comp hn1_kb hkb_k B₁]
      have hb2 : stageMorphism (max m₂ n₂) k h2_k (stageMorphism n₂ (max m₂ n₂) (le_max_right m₂ n₂) B₂) =
                 stageMorphism k_b k hkb_k (stageMorphism n₂ k_b hn2_kb B₂) := by
        rw [stageMorphism_apply_comp (le_max_right m₂ n₂) h2_k B₂]
        rw [stageMorphism_apply_comp hn2_kb hkb_k B₂]
      rw [ha1, ha2, hb1, hb2, heq_a, heq_b])

instance : Mul MatrixStageLimit where
  mul := limitMul

theorem toLimit_mul (n : ℕ) (A B : Stage n) :
    toLimit n A * toLimit n B = toLimit n (A * B) := by
  change toLimit (max n n) (stageMorphism n (max n n) (le_max_left n n) A *
                           stageMorphism n (max n n) (le_max_right n n) B) = toLimit n (A * B)
  have hle : n ≤ max n n := le_max_left n n
  have h_map : stageMorphism n (max n n) (le_max_left n n) A *
               stageMorphism n (max n n) (le_max_right n n) B =
               stageMorphism n (max n n) hle (A * B) := by
    rw [map_mul]
  rw [h_map]
  exact toLimit_stageMorphism hle (A * B)

/-! ## 5. Complete Mathlib Typeclass Hierarchy for MatrixStageLimit -/

instance : AddSemigroup MatrixStageLimit where
  add_assoc := by
    intro X Y Z
    induction X, Y, Z using Quotient.inductionOn₃ with
    | h a b c =>
        rcases a with ⟨m, A⟩; rcases b with ⟨n, B⟩; rcases c with ⟨p, C⟩
        rw [quot_mk_eq, quot_mk_eq, quot_mk_eq]
        let k := max m (max n p)
        have hm : m ≤ k := le_max_left _ _
        have hn : n ≤ k := le_trans (le_max_left n p) (le_max_right m _)
        have hp : p ≤ k := le_trans (le_max_right n p) (le_max_right m _)
        rw [← toLimit_stageMorphism hm A, ← toLimit_stageMorphism hn B, ← toLimit_stageMorphism hp C]
        rw [toLimit_add, toLimit_add, toLimit_add, toLimit_add, add_assoc]

instance : AddMonoid MatrixStageLimit where
  zero_add := by
    intro X; induction X using Quotient.inductionOn with
    | h a => rcases a with ⟨n, A⟩; rw [quot_mk_eq, ← toLimit_zero n, toLimit_add, zero_add]
  add_zero := by
    intro X; induction X using Quotient.inductionOn with
    | h a => rcases a with ⟨n, A⟩; rw [quot_mk_eq, ← toLimit_zero n, toLimit_add, add_zero]
  nsmul := nsmulRec

instance : AddCommMonoid MatrixStageLimit where
  add_comm := by
    intro X Y; induction X, Y using Quotient.inductionOn₂ with
    | h a b =>
        rcases a with ⟨m, A⟩; rcases b with ⟨n, B⟩
        rw [quot_mk_eq, quot_mk_eq]
        rw [← toLimit_stageMorphism (le_max_left m n) A, ← toLimit_stageMorphism (le_max_right m n) B]
        rw [toLimit_add, toLimit_add, add_comm]

instance : SubNegMonoid MatrixStageLimit where
  zsmul := zsmulRec

instance : AddGroup MatrixStageLimit where
  neg_add_cancel := by
    intro X; induction X using Quotient.inductionOn with
    | h a => rcases a with ⟨n, A⟩; rw [quot_mk_eq, toLimit_neg, toLimit_add, neg_add_cancel, toLimit_zero]

instance : AddCommGroup MatrixStageLimit where

instance : Monoid MatrixStageLimit where
  mul_assoc := by
    intro X Y Z
    induction X, Y, Z using Quotient.inductionOn₃ with
    | h a b c =>
        rcases a with ⟨m, A⟩; rcases b with ⟨n, B⟩; rcases c with ⟨p, C⟩
        rw [quot_mk_eq, quot_mk_eq, quot_mk_eq]
        let k := max m (max n p)
        have hm : m ≤ k := le_max_left _ _
        have hn : n ≤ k := le_trans (le_max_left n p) (le_max_right m _)
        have hp : p ≤ k := le_trans (le_max_right n p) (le_max_right m _)
        rw [← toLimit_stageMorphism hm A, ← toLimit_stageMorphism hn B, ← toLimit_stageMorphism hp C]
        rw [toLimit_mul, toLimit_mul, toLimit_mul, toLimit_mul, mul_assoc]
  one_mul := by
    intro X; induction X using Quotient.inductionOn with
    | h a => rcases a with ⟨n, A⟩; rw [quot_mk_eq, ← toLimit_one n, toLimit_mul, one_mul]
  mul_one := by
    intro X; induction X using Quotient.inductionOn with
    | h a => rcases a with ⟨n, A⟩; rw [quot_mk_eq, ← toLimit_one n, toLimit_mul, mul_one]
  npow := npowRec

instance : Semiring MatrixStageLimit where
  left_distrib := by
    intro X Y Z
    induction X, Y, Z using Quotient.inductionOn₃ with
    | h a b c =>
        rcases a with ⟨m, A⟩; rcases b with ⟨n, B⟩; rcases c with ⟨p, C⟩
        rw [quot_mk_eq, quot_mk_eq, quot_mk_eq]
        let k := max m (max n p)
        have hm : m ≤ k := le_max_left _ _
        have hn : n ≤ k := le_trans (le_max_left n p) (le_max_right m _)
        have hp : p ≤ k := le_trans (le_max_right n p) (le_max_right m _)
        rw [← toLimit_stageMorphism hm A, ← toLimit_stageMorphism hn B, ← toLimit_stageMorphism hp C]
        rw [toLimit_add, toLimit_mul, toLimit_mul, toLimit_mul, toLimit_add, mul_add]
  right_distrib := by
    intro X Y Z
    induction X, Y, Z using Quotient.inductionOn₃ with
    | h a b c =>
        rcases a with ⟨m, A⟩; rcases b with ⟨n, B⟩; rcases c with ⟨p, C⟩
        rw [quot_mk_eq, quot_mk_eq, quot_mk_eq]
        let k := max m (max n p)
        have hm : m ≤ k := le_max_left _ _
        have hn : n ≤ k := le_trans (le_max_left n p) (le_max_right m _)
        have hp : p ≤ k := le_trans (le_max_right n p) (le_max_right m _)
        rw [← toLimit_stageMorphism hm A, ← toLimit_stageMorphism hn B, ← toLimit_stageMorphism hp C]
        rw [toLimit_add, toLimit_mul, toLimit_mul, toLimit_mul, toLimit_add, add_mul]
  zero_mul := by
    intro X; induction X using Quotient.inductionOn with
    | h a => rcases a with ⟨n, A⟩; rw [quot_mk_eq, ← toLimit_zero n, toLimit_mul, zero_mul, toLimit_zero]
  mul_zero := by
    intro X; induction X using Quotient.inductionOn with
    | h a => rcases a with ⟨n, A⟩; rw [quot_mk_eq, ← toLimit_zero n, toLimit_mul, mul_zero, toLimit_zero]

instance : Ring MatrixStageLimit where

instance : StarRing MatrixStageLimit where
  star_involutive := by
    intro X; induction X using Quotient.inductionOn with
    | h a => rcases a with ⟨n, A⟩; rw [quot_mk_eq, toLimit_star, toLimit_star, star_star]
  star_mul := by
    intro X Y; induction X, Y using Quotient.inductionOn₂ with
    | h a b =>
        rcases a with ⟨m, A⟩; rcases b with ⟨n, B⟩
        rw [quot_mk_eq, quot_mk_eq]
        let k := max m n
        rw [← toLimit_stageMorphism (le_max_left m n) A, ← toLimit_stageMorphism (le_max_right m n) B]
        rw [toLimit_mul, toLimit_star, StarMul.star_mul, ← toLimit_mul, toLimit_star, toLimit_star]
  star_add := by
    intro X Y; induction X, Y using Quotient.inductionOn₂ with
    | h a b =>
        rcases a with ⟨m, A⟩; rcases b with ⟨n, B⟩
        rw [quot_mk_eq, quot_mk_eq]
        let k := max m n
        rw [← toLimit_stageMorphism (le_max_left m n) A, ← toLimit_stageMorphism (le_max_right m n) B]
        rw [toLimit_add, toLimit_star, star_add, ← toLimit_add, toLimit_star, toLimit_star]

instance : Module ℂ MatrixStageLimit where
  one_smul := by
    intro X; induction X using Quotient.inductionOn with
    | h a => rcases a with ⟨n, A⟩; rw [quot_mk_eq, toLimit_smul, one_smul]
  mul_smul := by
    intro c d X; induction X using Quotient.inductionOn with
    | h a => rcases a with ⟨n, A⟩; rw [quot_mk_eq, toLimit_smul, toLimit_smul, toLimit_smul, SemigroupAction.mul_smul]
  smul_add := by
    intro c X Y; induction X, Y using Quotient.inductionOn₂ with
    | h a b =>
        rcases a with ⟨m, A⟩; rcases b with ⟨n, B⟩
        rw [quot_mk_eq, quot_mk_eq]
        let k := max m n
        rw [← toLimit_stageMorphism (le_max_left m n) A, ← toLimit_stageMorphism (le_max_right m n) B]
        rw [toLimit_add, toLimit_smul, smul_add, ← toLimit_add, toLimit_smul, toLimit_smul]
  smul_zero := by
    intro c; rw [← toLimit_zero 0, toLimit_smul, smul_zero]
  add_smul := by
    intro c d X; induction X using Quotient.inductionOn with
    | h a => rcases a with ⟨n, A⟩; rw [quot_mk_eq, toLimit_smul, add_smul, ← toLimit_add, toLimit_smul, toLimit_smul]
  zero_smul := by
    intro X; induction X using Quotient.inductionOn with
    | h a => rcases a with ⟨n, A⟩; rw [quot_mk_eq, toLimit_smul, zero_smul, toLimit_zero]

def limitAlgebraMap : ℂ →+* MatrixStageLimit where
  toFun c := toLimit 0 (algebraMap ℂ (Stage 0) c)
  map_one' := by rw [map_one, toLimit_one]
  map_mul' c d := by rw [map_mul, toLimit_mul]
  map_zero' := by rw [map_zero, toLimit_zero]
  map_add' c d := by rw [map_add, toLimit_add]

instance : Algebra ℂ MatrixStageLimit where
  algebraMap := limitAlgebraMap
  commutes' c X := by
    induction X using Quotient.inductionOn with
    | h a =>
        rcases a with ⟨n, A⟩
        rw [quot_mk_eq]
        change toLimit 0 (algebraMap ℂ (Stage 0) c) * toLimit n A = toLimit n A * toLimit 0 (algebraMap ℂ (Stage 0) c)
        have h0n : 0 ≤ n := Nat.zero_le n
        rw [← toLimit_stageMorphism h0n (algebraMap ℂ (Stage 0) c)]
        rw [toLimit_mul, toLimit_mul]
        have h_alg_comm : stageMorphism 0 n h0n (algebraMap ℂ (Stage 0) c) * A =
                          A * stageMorphism 0 n h0n (algebraMap ℂ (Stage 0) c) := by
          rw [show stageMorphism 0 n h0n (algebraMap ℂ (Stage 0) c) = algebraMap ℂ (Stage n) c by
                exact (stageMorphism 0 n h0n).commutes c]
          exact Algebra.commutes c A
        rw [h_alg_comm]
  smul_def' c X := by
    induction X using Quotient.inductionOn with
    | h a =>
        rcases a with ⟨n, A⟩
        rw [quot_mk_eq]
        change toLimit n (c • A) = toLimit 0 (algebraMap ℂ (Stage 0) c) * toLimit n A
        have h0n : 0 ≤ n := Nat.zero_le n
        rw [← toLimit_stageMorphism h0n (algebraMap ℂ (Stage 0) c)]
        rw [toLimit_mul]
        have h_smul : stageMorphism 0 n h0n (algebraMap ℂ (Stage 0) c) * A = c • A := by
          rw [show stageMorphism 0 n h0n (algebraMap ℂ (Stage 0) c) = algebraMap ℂ (Stage n) c by
                exact (stageMorphism 0 n h0n).commutes c]
          exact (Algebra.smul_def c A).symm
        rw [h_smul]

instance : StarModule ℂ MatrixStageLimit where
  star_smul c X := by
    induction X using Quotient.inductionOn with
    | h a =>
        rcases a with ⟨n, A⟩
        rw [quot_mk_eq, toLimit_smul, toLimit_star, toLimit_star, toLimit_smul, star_smul]

/-! ## 6. Canonical Stage Inclusions as StarAlgHom -/

/-- The canonical inclusion of stage `n` as a unital complex $*$-algebra homomorphism. -/
def canonicalStageHom (n : ℕ) : Stage n →⋆ₐ[ℂ] MatrixStageLimit where
  toFun := toLimit n
  map_one' := toLimit_one n
  map_mul' x y := (toLimit_mul n x y).symm
  map_zero' := toLimit_zero n
  map_add' x y := (toLimit_add n x y).symm
  commutes' c := by
    have h0n : 0 ≤ n := Nat.zero_le n
    change toLimit n (algebraMap ℂ (Stage n) c) = toLimit 0 (algebraMap ℂ (Stage 0) c)
    rw [← toLimit_stageMorphism h0n (algebraMap ℂ (Stage 0) c)]
    congr 1
    exact ((stageMorphism 0 n h0n).commutes c).symm
  map_star' := toLimit_star n

@[simp] theorem canonicalStageHom_apply (n : ℕ) (A : Stage n) :
    canonicalStageHom n A = toLimit n A := rfl

/-- Coherence: arbitrary-jump stage morphism commutes with canonical inclusions. -/
theorem canonicalStageHom_comp {i j : ℕ} (hij : i ≤ j) :
    (canonicalStageHom j).comp (stageMorphism i j hij) = canonicalStageHom i := by
  ext A
  exact toLimit_stageMorphism hij A

/-- Elementary-step coherence: `bondStarAlgHom` commutes with canonical inclusions. -/
theorem canonicalStageHom_step (n : ℕ) :
    (canonicalStageHom (n + 1)).comp (bondStarAlgHom n) = canonicalStageHom n := by
  ext A
  exact toLimit_step n A

/-- Canonical stage inclusions into the direct limit are strictly injective. -/
theorem canonicalStageHom_injective (n : ℕ) :
    Function.Injective (canonicalStageHom n) := by
  intro A B h
  have h_eq : toLimit n A = toLimit n B := h
  have hexact : LimitRel ⟨n, A⟩ ⟨n, B⟩ := Quotient.exact h_eq
  rcases hexact with ⟨k, hnk_a, hnk_b, heq⟩
  exact stageMorphism_injective n k hnk_a heq

/-! ## 7. Universal Property of the Direct Limit as a StarAlgHom Cocone -/

/-- Universal property for arbitrary maps. -/
def liftFun {B : Type*} (f : ∀ n : ℕ, Stage n → B)
    (hf : ∀ (m n : ℕ) (h : m ≤ n) (A : Stage m), f n (stageMorphism m n h A) = f m A) :
    MatrixStageLimit → B :=
  Quotient.lift (fun (x : Element) => f x.1 x.2) (by
    rintro ⟨m, A⟩ ⟨n, B⟩ ⟨k, hmk, hnk, heq⟩
    dsimp
    rw [← hf m k hmk A, ← hf n k hnk B]
    rw [heq])

@[simp] theorem liftFun_toLimit {B : Type*} (f : ∀ n : ℕ, Stage n → B)
    (hf : ∀ (m n : ℕ) (h : m ≤ n) (A : Stage m), f n (stageMorphism m n h A) = f m A)
    (n : ℕ) (A : Stage n) :
    liftFun f hf (toLimit n A) = f n A := rfl

/-- Universal Property: Given any complex $*$-algebra $B$ and compatible family
    of $*$-algebra homomorphisms $f_n : \mathrm{Stage}(n) \to⋆ₐ[ℂ] B$, there exists
    a unique $*$-algebra homomorphism $F : \mathrm{MatrixStageLimit} \to⋆ₐ[ℂ] B$
    mediating the direct limit cocone. -/
def liftStarAlgHom {B : Type*} [Semiring B] [Algebra ℂ B] [StarRing B] [StarModule ℂ B]
    (f : ∀ n : ℕ, Stage n →⋆ₐ[ℂ] B)
    (hf : ∀ (m n : ℕ) (h : m ≤ n), (f n).comp (stageMorphism m n h) = f m) :
    MatrixStageLimit →⋆ₐ[ℂ] B where
  toFun := liftFun (fun n => f n) (fun m n h A => by
    have := congr_arg (fun (g : Stage m →⋆ₐ[ℂ] B) => (g A : B)) (hf m n h)
    exact this)
  map_one' := by
    change liftFun (fun n => f n) _ (toLimit 0 1) = 1
    rw [liftFun_toLimit, map_one]
  map_mul' := by
    intro X Y
    induction X, Y using Quotient.inductionOn₂ with
    | h a b =>
        rcases a with ⟨m, A⟩; rcases b with ⟨n, B⟩
        rw [quot_mk_eq, quot_mk_eq]
        let k := max m n
        rw [← toLimit_stageMorphism (le_max_left m n) A, ← toLimit_stageMorphism (le_max_right m n) B]
        rw [toLimit_mul]
        rw [liftFun_toLimit, liftFun_toLimit, liftFun_toLimit]
        rw [map_mul]
  map_zero' := by
    change liftFun (fun n => f n) _ (toLimit 0 0) = 0
    rw [liftFun_toLimit, map_zero]
  map_add' := by
    intro X Y
    induction X, Y using Quotient.inductionOn₂ with
    | h a b =>
        rcases a with ⟨m, A⟩; rcases b with ⟨n, B⟩
        rw [quot_mk_eq, quot_mk_eq]
        let k := max m n
        rw [← toLimit_stageMorphism (le_max_left m n) A, ← toLimit_stageMorphism (le_max_right m n) B]
        rw [toLimit_add]
        rw [liftFun_toLimit, liftFun_toLimit, liftFun_toLimit]
        rw [map_add]
  commutes' c := by
    change liftFun (fun n => f n) _ (toLimit 0 (algebraMap ℂ (Stage 0) c)) = algebraMap ℂ B c
    rw [liftFun_toLimit]
    exact (f 0).commutes c
  map_star' := by
    intro X
    induction X using Quotient.inductionOn with
    | h a =>
        rcases a with ⟨n, A⟩
        rw [quot_mk_eq, toLimit_star]
        rw [liftFun_toLimit, liftFun_toLimit]
        rw [map_star]

/-- Commutation of the lifted mediator with finite stage inclusions. -/
theorem liftStarAlgHom_comp {B : Type*} [Semiring B] [Algebra ℂ B] [StarRing B] [StarModule ℂ B]
    (f : ∀ n : ℕ, Stage n →⋆ₐ[ℂ] B)
    (hf : ∀ (m n : ℕ) (h : m ≤ n), (f n).comp (stageMorphism m n h) = f m) (n : ℕ) :
    (liftStarAlgHom f hf).comp (canonicalStageHom n) = f n := by
  ext A
  rfl

/-- Uniqueness of the direct limit $*$-algebra homomorphism. -/
theorem liftStarAlgHom_unique {B : Type*} [Semiring B] [Algebra ℂ B] [StarRing B] [StarModule ℂ B]
    (f : ∀ n : ℕ, Stage n →⋆ₐ[ℂ] B)
    (hf : ∀ (m n : ℕ) (h : m ≤ n), (f n).comp (stageMorphism m n h) = f m)
    (F : MatrixStageLimit →⋆ₐ[ℂ] B)
    (hF : ∀ n : ℕ, F.comp (canonicalStageHom n) = f n) :
    F = liftStarAlgHom f hf := by
  ext X
  induction X using Quotient.inductionOn with
  | h a =>
      rcases a with ⟨n, A⟩
      rw [quot_mk_eq]
      change F (canonicalStageHom n A) = liftStarAlgHom f hf (canonicalStageHom n A)
      rw [← StarAlgHom.comp_apply, hF n, ← StarAlgHom.comp_apply, liftStarAlgHom_comp]

/-! ## 8. Tracial Functional Properties -/

theorem limitTrace_add (X Y : MatrixStageLimit) :
    limitTrace (X + Y) = limitTrace X + limitTrace Y := by
  induction X, Y using Quotient.inductionOn₂ with
  | h a b =>
      rcases a with ⟨m, A⟩; rcases b with ⟨n, B⟩
      rw [quot_mk_eq, quot_mk_eq, ← toLimit_stageMorphism (le_max_left m n) A,
          ← toLimit_stageMorphism (le_max_right m n) B, toLimit_add]
      rw [limitTrace_toLimit, limitTrace_toLimit, limitTrace_toLimit]
      dsimp [normalizedTrace]
      rw [Matrix.trace_add, mul_add]

theorem limitTrace_smul (c : ℂ) (X : MatrixStageLimit) :
    limitTrace (c • X) = c * limitTrace X := by
  induction X using Quotient.inductionOn with
  | h a =>
      rcases a with ⟨n, A⟩
      rw [quot_mk_eq, toLimit_smul, limitTrace_toLimit, limitTrace_toLimit]
      dsimp [normalizedTrace]
      rw [Matrix.trace_smul]
      simp [mul_left_comm]

theorem limitTrace_mul_comm (X Y : MatrixStageLimit) :
    limitTrace (X * Y) = limitTrace (Y * X) := by
  induction X, Y using Quotient.inductionOn₂ with
  | h a b =>
      rcases a with ⟨m, A⟩; rcases b with ⟨n, B⟩
      rw [quot_mk_eq, quot_mk_eq]
      let k := max m n
      rw [← toLimit_stageMorphism (le_max_left m n) A, ← toLimit_stageMorphism (le_max_right m n) B]
      rw [toLimit_mul, toLimit_mul]
      rw [limitTrace_toLimit, limitTrace_toLimit]
      dsimp [normalizedTrace]
      rw [Matrix.trace_mul_comm]

theorem limitTrace_star (X : MatrixStageLimit) :
    limitTrace (star X) = starRingEnd ℂ (limitTrace X) := by
  induction X using Quotient.inductionOn with
  | h a =>
      rcases a with ⟨n, A⟩
      rw [quot_mk_eq, toLimit_star, limitTrace_toLimit, limitTrace_toLimit]
      dsimp [normalizedTrace]
      have h_two : (starRingEnd ℂ) (2 : ℂ) = 2 := map_ofNat (starRingEnd ℂ) 2
      have h_pow : (starRingEnd ℂ) (2 ^ n : ℂ) = (2 ^ n : ℂ) := by
        rw [map_pow, h_two]
      have h_pow_star : starRingEnd ℂ (1 / (2 ^ n : ℂ)) = 1 / (2 ^ n : ℂ) := by
        rw [map_div₀, map_one, h_pow]
      have h_tr_star : Matrix.trace (star A) = starRingEnd ℂ (Matrix.trace A) := by
        dsimp [Matrix.trace]
        simp
      rw [map_mul, h_pow_star, h_tr_star]

/-- The canonical normalized trace descended to a genuine `LinearMap` on `MatrixStageLimit`. -/
def limitNormalizedTrace : MatrixStageLimit →ₗ[ℂ] ℂ where
  toFun := limitTrace
  map_add' := limitTrace_add
  map_smul' c X := by
    show limitTrace (c • X) = c • limitTrace X
    rw [limitTrace_smul, smul_eq_mul]

/-- The finite stage normalized trace as a bundled `LinearMap`. -/
def stageNormalizedTraceLM (n : ℕ) : Stage n →ₗ[ℂ] ℂ where
  toFun := normalizedTrace n
  map_add' := by
    intro A B
    dsimp [normalizedTrace]
    rw [Matrix.trace_add, mul_add]
  map_smul' := by
    intro c A
    dsimp [normalizedTrace]
    rw [Matrix.trace_smul, smul_eq_mul, mul_left_comm]

/-- Exact compatibility of the descended linear trace functional with each finite stage. -/
theorem inductiveLimitTrace_comp_stage (n : ℕ) :
    limitNormalizedTrace.comp (canonicalStageHom n).toLinearMap = stageNormalizedTraceLM n := by
  ext A
  exact limitTrace_toLimit n A

/-! ## 9. Positivity and Faithfulness of the Descended Tracial State -/

/-- Positivity of the real part of the descended trace on positive elements $X^* X$. -/
theorem limitTrace_star_mul_self_re_nonneg (X : MatrixStageLimit) :
    0 ≤ (limitTrace (star X * X)).re := by
  induction X using Quotient.inductionOn with
  | h a =>
      rcases a with ⟨n, A⟩
      rw [quot_mk_eq, toLimit_star, toLimit_mul, limitTrace_toLimit]
      exact normalizedTrace_stage_star_mul_self_re_nonneg n A

/-- The descended trace is strictly real on positive elements $X^* X$. -/
theorem limitTrace_star_mul_self_im (X : MatrixStageLimit) :
    (limitTrace (star X * X)).im = 0 := by
  have h_star : star (star X * X) = star X * X := by
    rw [StarMul.star_mul, star_star]
  have h_tr := limitTrace_star (star X * X)
  rw [h_star] at h_tr
  have h_conj : starRingEnd ℂ (limitTrace (star X * X)) = limitTrace (star X * X) := h_tr.symm
  exact Complex.conj_eq_iff_im.mp h_conj

/-- Strict faithfulness of the descended normalized trace state: $\tau_\infty(X^* X) = 0 \iff X = 0$. -/
theorem limitTrace_star_mul_self_eq_zero_iff (X : MatrixStageLimit) :
    limitTrace (star X * X) = 0 ↔ X = 0 := by
  induction X using Quotient.inductionOn with
  | h a =>
      rcases a with ⟨n, A⟩
      rw [quot_mk_eq, toLimit_star, toLimit_mul, limitTrace_toLimit]
      constructor
      · intro h
        rw [normalizedTrace_stage_star_mul_self_eq_zero_iff] at h
        rw [h, toLimit_zero]
      · intro h
        have hA : (toLimit n A : MatrixStageLimit) = toLimit n 0 := by
          rw [toLimit_zero, h]
        have h_inj := canonicalStageHom_injective n hA
        rw [h_inj]
        dsimp [normalizedTrace]
        simp

/-! ## 10. Canonical Pre-Hilbert Trace Inner Product Space -/

/-- The canonical trace inner product $\langle X, Y \rangle_\tau = \tau_\infty(X^* Y)$ on `MatrixStageLimit`. -/
def limitInner (X Y : MatrixStageLimit) : ℂ :=
  limitTrace (star X * Y)

theorem limitInner_toLimit (n : ℕ) (A B : Stage n) :
    limitInner (toLimit n A) (toLimit n B) = normalizedTrace n (star A * B) := by
  change limitTrace (star (toLimit n A) * toLimit n B) = normalizedTrace n (star A * B)
  rw [toLimit_star, toLimit_mul, limitTrace_toLimit]

theorem limitInner_add_left (X Y Z : MatrixStageLimit) :
    limitInner (X + Y) Z = limitInner X Z + limitInner Y Z := by
  dsimp [limitInner]
  rw [star_add, add_mul, limitTrace_add]

theorem limitInner_add_right (X Y Z : MatrixStageLimit) :
    limitInner X (Y + Z) = limitInner X Y + limitInner X Z := by
  dsimp [limitInner]
  rw [mul_add, limitTrace_add]

theorem limitInner_smul_left (c : ℂ) (X Y : MatrixStageLimit) :
    limitInner (c • X) Y = starRingEnd ℂ c * limitInner X Y := by
  dsimp [limitInner]
  rw [star_smul, smul_mul_assoc, limitTrace_smul]
  rfl

theorem limitInner_smul_right (c : ℂ) (X Y : MatrixStageLimit) :
    limitInner X (c • Y) = c * limitInner X Y := by
  dsimp [limitInner]
  rw [mul_smul_comm, limitTrace_smul]

theorem limitInner_conj_symm (X Y : MatrixStageLimit) :
    starRingEnd ℂ (limitInner X Y) = limitInner Y X := by
  dsimp [limitInner]
  rw [← limitTrace_star, star_mul, star_star, limitTrace_mul_comm]

theorem limitInner_self_re_nonneg (X : MatrixStageLimit) :
    0 ≤ (limitInner X X).re :=
  limitTrace_star_mul_self_re_nonneg X

theorem limitInner_self_im (X : MatrixStageLimit) :
    (limitInner X X).im = 0 :=
  limitTrace_star_mul_self_im X

theorem limitInner_self_eq_zero_iff (X : MatrixStageLimit) :
    limitInner X X = 0 ↔ X = 0 :=
  limitTrace_star_mul_self_eq_zero_iff X

end

end InfoGeometry.Canonical.MatrixStageInductiveLimit
