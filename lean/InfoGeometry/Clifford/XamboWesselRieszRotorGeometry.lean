/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Formalization Team
-/
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.Tactic.Abel
import InfoGeometry.OperatorAlgebra.PeirceSpine.BimetricSheetGeometry

/-!
# Non-Commutative Geometric Algebra: Wessel Involutions, Riesz Skew-Derivations & Rotors (X₀ ≺ ... ≺ X₄)

Formalized in Lean 4 (`Mathlib`) over an arbitrary **non-commutative** associative ring `[Ring B]`.
Zero `sorry`s. Zero custom axioms. Zero commutativity assumptions on `B`.

## Three-Bucket Audit Map
- **BUCKET 1 (Established Mathematical Target & Existing Owners)**:
  * `Mathlib.Algebra.Ring.Defs`, `Mathlib.Algebra.Ring.Hom.Defs`, `Mathlib.Tactic.Abel`.
  * `InfoGeometry.OperatorAlgebra.PeirceSpine.BimetricSheetGeometry`:
    Non-commutative 2×2 operator matrices `NonCommutativeBimetricSheetGeometry.Mat2`,
    symplectic unit `Ey`, transpose `trp`, and formal adjugate `adj`.
- **BUCKET 2 (Deconfabulation & Translation Dictionary)**:
  * Strips introductory geometric-trigonometric narrative from Sebastià Xambó's
    *Geometric Algebra: Mathematical Structures and Applications* (UPC/BSC, 2019)
    and replaces scalar-commutative assumptions with exact non-commutative identities
    and commutator/curvature obstructions over `[Ring B]`:
    - Wessel algebra $\mathcal{W} = \mathcal{G}_2 \simeq \mathbb{R}(2)$ and the three
      involutions $\widehat{a}, \widetilde{a}, \overline{a}$ (Slides 18, 29, 37, 45, 52)
      $\mapsto$ `wesselMap`, `parityHat` ($\widehat{M} = -E_y M E_y$, an exact ring
      automorphism over any `[Ring B]`), `revTilde` ($\widetilde{M} = M^\top$), and
      `cliffConj` ($\overline{M} = \operatorname{adj}(M) = \widehat{\widetilde{M}}$).
    - Riesz formulas $2(x \cdot a) = xa - \widehat{a}x$, $2(x \wedge a) = xa + \widehat{a}x$
      and the skew-derivation law (Slides 28–30) $\mapsto$ `rieszDot`, `rieszWedge`,
      and the universal telescoping skew-derivation identity over `[Ring B]`.
    - Reflections and twisted adjoint action (Slides 58–63, 75) $\mapsto$ `twistSandwich`
      and the inverse-free Householder–Clifford identity exposing the non-commutative
      metric commutator $[X^2, Y] = (X^2 Y - \iota_X(Y) X) - (-X Y X)$.
    - Dirac spacetime split $\sigma_k = e_k e_0$ and Slide 110 spherical rotor commutator
      identity (Slides 54, 55, 110) $\mapsto$ `Sig1, Sig2, Sig3` in `Op4 B = Mat2 (Mat2 B)`
      and $[R_A, \overline{R}_B] - [R_B, R_A] = [R_A, \mathrm{diagScalar}(\operatorname{tr}_2 R_B)]$.
    - Olinde Rodrigues rotor composition $R'' = R R'$ (Slides 83, 93, 102, 116) $\mapsto$
      `Rotor3.mul` and `Rotor3.rev`, showing that $(c, \mathbf{u})(c, -\mathbf{u})$ has
      scalar part $c^2 + \mathbf{u}\cdot\mathbf{u}$ and bivector part equal to the
      non-commutative Yang–Mills curvature obstruction $-[c, \mathbf{u}] + \mathbf{u}\times\mathbf{u}$.
- **BUCKET 3 (Constructive Lean 4 Theorems Proved Here)**:
  * `XamboGeometricAlgebraPosetStage` ($\mathcal{X}_0 \prec \mathcal{X}_1 \prec \mathcal{X}_2 \prec \mathcal{X}_3 \prec \mathcal{X}_4$)
    and `XamboGeometricAlgebraPosetStage.toNat_injective`.
  * `archetype_X0_wessel_matrix_isomorphism_and_three_clifford_involutions`
  * `archetype_X1_riesz_contraction_wedge_and_skew_derivation_law`
  * `archetype_X1_universal_ring_hom_skew_derivation`
  * `archetype_X2_versor_reflections_and_householder_commutator_anomaly`
  * `archetype_X3_dirac_spacetime_split_and_slide110_rotor_commutator`
  * `archetype_X4_noncomm_olinde_rodrigues_rotor_composition_and_curvature`
  * `xambo_bimetric_involutions_bridge`
-/

namespace NonCommutativeXamboGeometricAlgebra

universe u
variable {B : Type u} [Ring B]

-- ============================================================================
-- 0. ACYCLIC CAUSAL POSET (X₀ ≺ X₁ ≺ X₂ ≺ X₃ ≺ X₄)
-- ============================================================================

/-- The five stages of the Xambó non-commutative geometric algebra causal poset
$\mathcal{X}_0 \prec \mathcal{X}_1 \prec \mathcal{X}_2 \prec \mathcal{X}_3 \prec \mathcal{X}_4$. -/
inductive XamboGeometricAlgebraPosetStage : Type
  | X0 : XamboGeometricAlgebraPosetStage
  | X1 : XamboGeometricAlgebraPosetStage
  | X2 : XamboGeometricAlgebraPosetStage
  | X3 : XamboGeometricAlgebraPosetStage
  | X4 : XamboGeometricAlgebraPosetStage
  deriving DecidableEq, Repr

namespace XamboGeometricAlgebraPosetStage

/-- Numerical rank of each stage in the causal poset $\mathcal{X}_0 \prec \dots \prec \mathcal{X}_4$. -/
def toNat : XamboGeometricAlgebraPosetStage → ℕ
  | X0 => 0
  | X1 => 1
  | X2 => 2
  | X3 => 3
  | X4 => 4

/-- `toNat` is injective on `XamboGeometricAlgebraPosetStage`. -/
theorem toNat_injective : Function.Injective toNat := by
  intro a b h
  cases a <;> cases b <;> first | exact Eq.refl _ | cases h

instance : LinearOrder XamboGeometricAlgebraPosetStage :=
  LinearOrder.lift' toNat toNat_injective

/-- Strict causal chain $\mathcal{X}_0 \prec \mathcal{X}_1 \prec \mathcal{X}_2 \prec \mathcal{X}_3 \prec \mathcal{X}_4$. -/
theorem causal_poset_chain :
    (X0 : XamboGeometricAlgebraPosetStage) < X1 ∧
    (X1 : XamboGeometricAlgebraPosetStage) < X2 ∧
    (X2 : XamboGeometricAlgebraPosetStage) < X3 ∧
    (X3 : XamboGeometricAlgebraPosetStage) < X4 := by
  refine ⟨Nat.zero_lt_one, ?_, ?_, ?_⟩
  · exact Nat.lt_succ_self 1
  · exact Nat.lt_succ_self 2
  · exact Nat.lt_succ_self 3

end XamboGeometricAlgebraPosetStage

-- ============================================================================
-- 1. NON-COMMUTATIVE 2x2 MATRIX RING `Mat2 B` & WESSEL INVOLUTIONS
-- ============================================================================

/-- 2×2 matrix over a type `α`. -/
@[ext]
structure Mat2 (α : Type u) where
  a11 : α
  a12 : α
  a21 : α
  a22 : α
  deriving DecidableEq, Repr

instance : Inhabited (Mat2 B) := ⟨⟨0, 0, 0, 0⟩⟩

namespace Mat2

@[simp] def zero : Mat2 B := ⟨0, 0, 0, 0⟩
@[simp] def one  : Mat2 B := ⟨1, 0, 0, 1⟩

@[simp] def add (A M : Mat2 B) : Mat2 B :=
  ⟨A.a11 + M.a11, A.a12 + M.a12, A.a21 + M.a21, A.a22 + M.a22⟩

@[simp] def neg (A : Mat2 B) : Mat2 B :=
  ⟨-A.a11, -A.a12, -A.a21, -A.a22⟩

@[simp] def sub (A M : Mat2 B) : Mat2 B :=
  ⟨A.a11 - M.a11, A.a12 - M.a12, A.a21 - M.a21, A.a22 - M.a22⟩

@[simp] def mul (A M : Mat2 B) : Mat2 B :=
  ⟨A.a11 * M.a11 + A.a12 * M.a21, A.a11 * M.a12 + A.a12 * M.a22,
   A.a21 * M.a11 + A.a22 * M.a21, A.a21 * M.a12 + A.a22 * M.a22⟩

@[simp] def nsmulMat (n : ℕ) (A : Mat2 B) : Mat2 B :=
  ⟨n • A.a11, n • A.a12, n • A.a21, n • A.a22⟩

@[simp] def zsmulMat (n : ℤ) (A : Mat2 B) : Mat2 B :=
  ⟨n • A.a11, n • A.a12, n • A.a21, n • A.a22⟩

instance : Zero (Mat2 B) := ⟨zero⟩
instance : One (Mat2 B)  := ⟨one⟩
instance : Add (Mat2 B)  := ⟨add⟩
instance : Neg (Mat2 B)  := ⟨neg⟩
instance : Sub (Mat2 B)  := ⟨sub⟩
instance : Mul (Mat2 B)  := ⟨mul⟩

@[simp] lemma zero_a11 : (0 : Mat2 B).a11 = 0 := by
  have h : (0 : Mat2 B).a11 = 0 := Eq.refl _
  exact h
@[simp] lemma zero_a12 : (0 : Mat2 B).a12 = 0 := by
  have h : (0 : Mat2 B).a12 = 0 := Eq.refl _
  exact h
@[simp] lemma zero_a21 : (0 : Mat2 B).a21 = 0 := by
  have h : (0 : Mat2 B).a21 = 0 := Eq.refl _
  exact h
@[simp] lemma zero_a22 : (0 : Mat2 B).a22 = 0 := by
  have h : (0 : Mat2 B).a22 = 0 := Eq.refl _
  exact h
@[simp] lemma one_a11 : (1 : Mat2 B).a11 = 1 := by
  have h : (1 : Mat2 B).a11 = 1 := Eq.refl _
  exact h
@[simp] lemma one_a12 : (1 : Mat2 B).a12 = 0 := by
  have h : (1 : Mat2 B).a12 = 0 := Eq.refl _
  exact h
@[simp] lemma one_a21 : (1 : Mat2 B).a21 = 0 := by
  have h : (1 : Mat2 B).a21 = 0 := Eq.refl _
  exact h
@[simp] lemma one_a22 : (1 : Mat2 B).a22 = 1 := by
  have h : (1 : Mat2 B).a22 = 1 := Eq.refl _
  exact h
@[simp] lemma add_a11 (A M : Mat2 B) : (A + M).a11 = A.a11 + M.a11 := by
  have h : (A + M).a11 = A.a11 + M.a11 := Eq.refl _
  exact h
@[simp] lemma add_a12 (A M : Mat2 B) : (A + M).a12 = A.a12 + M.a12 := by
  have h : (A + M).a12 = A.a12 + M.a12 := Eq.refl _
  exact h
@[simp] lemma add_a21 (A M : Mat2 B) : (A + M).a21 = A.a21 + M.a21 := by
  have h : (A + M).a21 = A.a21 + M.a21 := Eq.refl _
  exact h
@[simp] lemma add_a22 (A M : Mat2 B) : (A + M).a22 = A.a22 + M.a22 := by
  have h : (A + M).a22 = A.a22 + M.a22 := Eq.refl _
  exact h
@[simp] lemma neg_a11 (A : Mat2 B) : (-A).a11 = -A.a11 := by
  have h : (-A).a11 = -A.a11 := Eq.refl _
  exact h
@[simp] lemma neg_a12 (A : Mat2 B) : (-A).a12 = -A.a12 := by
  have h : (-A).a12 = -A.a12 := Eq.refl _
  exact h
@[simp] lemma neg_a21 (A : Mat2 B) : (-A).a21 = -A.a21 := by
  have h : (-A).a21 = -A.a21 := Eq.refl _
  exact h
@[simp] lemma neg_a22 (A : Mat2 B) : (-A).a22 = -A.a22 := by
  have h : (-A).a22 = -A.a22 := Eq.refl _
  exact h
@[simp] lemma sub_a11 (A M : Mat2 B) : (A - M).a11 = A.a11 - M.a11 := by
  have h : (A - M).a11 = A.a11 - M.a11 := Eq.refl _
  exact h
@[simp] lemma sub_a12 (A M : Mat2 B) : (A - M).a12 = A.a12 - M.a12 := by
  have h : (A - M).a12 = A.a12 - M.a12 := Eq.refl _
  exact h
@[simp] lemma sub_a21 (A M : Mat2 B) : (A - M).a21 = A.a21 - M.a21 := by
  have h : (A - M).a21 = A.a21 - M.a21 := Eq.refl _
  exact h
@[simp] lemma sub_a22 (A M : Mat2 B) : (A - M).a22 = A.a22 - M.a22 := by
  have h : (A - M).a22 = A.a22 - M.a22 := Eq.refl _
  exact h
@[simp] lemma mul_a11 (A M : Mat2 B) : (A * M).a11 = A.a11 * M.a11 + A.a12 * M.a21 := by
  have h : (A * M).a11 = A.a11 * M.a11 + A.a12 * M.a21 := Eq.refl _
  exact h
@[simp] lemma mul_a12 (A M : Mat2 B) : (A * M).a12 = A.a11 * M.a12 + A.a12 * M.a22 := by
  have h : (A * M).a12 = A.a11 * M.a12 + A.a12 * M.a22 := Eq.refl _
  exact h
@[simp] lemma mul_a21 (A M : Mat2 B) : (A * M).a21 = A.a21 * M.a11 + A.a22 * M.a21 := by
  have h : (A * M).a21 = A.a21 * M.a11 + A.a22 * M.a21 := Eq.refl _
  exact h
@[simp] lemma mul_a22 (A M : Mat2 B) : (A * M).a22 = A.a21 * M.a12 + A.a22 * M.a22 := by
  have h : (A * M).a22 = A.a21 * M.a12 + A.a22 * M.a22 := Eq.refl _
  exact h

macro "xambo_nc_mat" : tactic =>
  `(tactic| (
    (try ext) <;> (try ext) <;>
    (simp only [zero, one, add, neg, sub, mul,
                zero_a11, zero_a12, zero_a21, zero_a22,
                one_a11, one_a12, one_a21, one_a22,
                add_a11, add_a12, add_a21, add_a22,
                neg_a11, neg_a12, neg_a21, neg_a22,
                sub_a11, sub_a12, sub_a21, sub_a22,
                mul_a11, mul_a12, mul_a21, mul_a22,
                mul_add, add_mul, sub_mul, mul_sub,
                mul_zero, zero_mul, mul_one, one_mul,
                add_zero, zero_add, sub_zero, zero_sub,
                neg_mul, mul_neg, neg_add_rev, neg_sub, sub_neg_eq_add, neg_neg, neg_zero,
                mul_assoc];
     try abel)))

instance instRingMat2 : Ring (Mat2 B) where
  add := add
  add_assoc := by intros; xambo_nc_mat
  zero := zero
  zero_add := by intros; xambo_nc_mat
  add_zero := by intros; xambo_nc_mat
  nsmul := nsmulMat
  nsmul_zero := by intros; ext <;> exact zero_smul ℕ _
  nsmul_succ := by intros; ext <;> exact succ_nsmul _ _
  zsmul := zsmulMat
  zsmul_zero' := by intros; ext <;> exact zero_smul ℤ _
  zsmul_succ' := by intros; ext <;> exact SubNegMonoid.zsmul_succ' _ _
  zsmul_neg' := by intros; ext <;> exact SubNegMonoid.zsmul_neg' _ _
  neg := neg
  sub := sub
  sub_eq_add_neg := by intros; xambo_nc_mat
  neg_add_cancel := by intros; xambo_nc_mat
  add_comm := by intros; xambo_nc_mat
  mul := mul
  left_distrib := by intros; xambo_nc_mat
  right_distrib := by intros; xambo_nc_mat
  zero_mul := by intros; xambo_nc_mat
  mul_zero := by intros; xambo_nc_mat
  mul_assoc := by intros; xambo_nc_mat
  one := one
  one_mul := by intros; xambo_nc_mat
  mul_one := by intros; xambo_nc_mat

/-- Ring commutator `[x, y] = x * y - y * x`. -/
@[simp] def rcomm {A : Type u} [Ring A] (x y : A) : A := x * y - y * x

/-- Ring anticommutator `{x, y} = x * y + y * x`. -/
@[simp] def racomm {A : Type u} [Ring A] (x y : A) : A := x * y + y * x

/-- Real Pauli-X / reflection generator `Ex = [[0, 1], [1, 0]]`. -/
@[simp] def Ex : Mat2 B := ⟨0, 1,  1,  0⟩

/-- Symplectic / Wessel bivector generator `Ey = [[0, -1], [1, 0]]`. -/
@[simp] def Ey : Mat2 B := ⟨0, -1, 1,  0⟩

/-- Diagonal grading generator `Ez = [[1, 0], [0, -1]]`. -/
@[simp] def Ez : Mat2 B := ⟨1, 0,  0, -1⟩

/-- Matrix trace `tr₂(M) = m₁₁ + m₂₂`. -/
@[simp] def tr2 (M : Mat2 B) : B := M.a11 + M.a22

/-- Scalar diagonal matrix `diagScalar(c) = [[c, 0], [0, c]]`. -/
@[simp] def diagScalar (c : B) : Mat2 B := ⟨c, 0, 0, c⟩

/--
Xambó's Wessel/Periodicity Matrix Map `W(a, β₁, β₂, γ)` (Slide 45 & Slide 52 Eq. (7)):
`[[a + β₁, β₂ + γ], [β₂ - γ, a - β₁]]`.
-/
@[simp] def wesselMap (a β1 β2 γ : B) : Mat2 B :=
  ⟨a + β1, β2 + γ, β2 - γ, a - β1⟩

/--
1. **Parity (Grade) Involution `a ↦ â`** (Slide 18):
   `parityHat M = -Ey * M * Ey = [[m₂₂, -m₂₁], [-m₁₂, m₁₁]]`.
-/
@[simp] def parityHat (M : Mat2 B) : Mat2 B :=
  ⟨M.a22, -M.a21, -M.a12, M.a11⟩

/--
2. **Reverse Involution `a ↦ ã`** (Slide 18):
   `revTilde M = Mᵀ = [[m₁₁, m₂₁], [m₁₂, m₂₂]]`.
-/
@[simp] def revTilde (M : Mat2 B) : Mat2 B :=
  ⟨M.a11, M.a21, M.a12, M.a22⟩

/--
3. **Clifford Conjugation `a ↦ ā = â˜`** (Slide 18):
   `cliffConj M = adj(M) = [[m₂₂, -m₁₂], [-m₂₁, m₁₁]]`.
-/
@[simp] def cliffConj (M : Mat2 B) : Mat2 B :=
  ⟨M.a22, -M.a12, -M.a21, M.a11⟩

/-- `parityHat` packaged as an exact ring endomorphism `Mat2 B →+* Mat2 B` over any `[Ring B]`. -/
def parityHatRingHom : Mat2 B →+* Mat2 B where
  toFun := parityHat
  map_one' := by simp only [parityHat]; xambo_nc_mat
  map_mul' M N := by simp only [parityHat]; xambo_nc_mat
  map_zero' := by simp only [parityHat]; xambo_nc_mat
  map_add' M N := by simp only [parityHat]; xambo_nc_mat

/--
**Archetype X₀ (`archetype_X0_wessel_matrix_isomorphism_and_three_clifford_involutions`):**
Formalizes Slides 18, 45, and 52 in `Mat2 B` over ANY non-commutative ring `[Ring B]`:
1. `parityHat M = -(Ey * M * Ey)` and `parityHat(M * N) = parityHat M * parityHat N`
   (an exact ring automorphism over any non-commutative ring `B`).
2. On `wesselMap a β₁ β₂ γ`:
   - `parityHat` negates the grade-1 vector `(β₁, β₂) ↦ (-β₁, -β₂)` while fixing `a` and `γ`.
   - `revTilde` negates the grade-2 bivector `γ ↦ -γ` while fixing `a, β₁, β₂`.
   - `cliffConj` negates both grade 1 and grade 2 `(β₁, β₂, γ) ↦ (-β₁, -β₂, -γ)`.
3. Exact Klein-four composition: `parityHat(revTilde M) = cliffConj M = revTilde(parityHat M)`.
-/
theorem archetype_X0_wessel_matrix_isomorphism_and_three_clifford_involutions
    (a β1 β2 γ : B) (M N : Mat2 B) :
    let W := wesselMap a β1 β2 γ
    -- 1. Inner realization & ring automorphism of parityHat:
    parityHat M = -(Ey * M * Ey) ∧
    parityHat (M * N) = parityHat M * parityHat N ∧
    parityHat (parityHat M) = M ∧
    -- 2. Grade actions on W(a, β₁, β₂, γ) (Slide 18):
    parityHat W = wesselMap a (-β1) (-β2) γ ∧
    revTilde W  = wesselMap a β1 β2 (-γ) ∧
    cliffConj W = wesselMap a (-β1) (-β2) (-γ) ∧
    -- 3. Composition of parity and reversal gives Clifford conjugation:
    parityHat (revTilde M) = cliffConj M ∧
    revTilde (parityHat M) = cliffConj M := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  · simp only [wesselMap, parityHat, revTilde, cliffConj, Ey]; try xambo_nc_mat

-- ============================================================================
-- 2. ARCHETYPE X₁: RIESZ FORMULAS & UNIVERSAL SKEW-DERIVATION LAW (SLIDES 28–30)
-- ============================================================================

/-- Riesz interior contraction (scaled by 2, Slide 29): `2(x · a) = x a - â x`. -/
@[simp] def rieszDot (X A : Mat2 B) : Mat2 B :=
  X * A - parityHat A * X

/-- Riesz exterior product (scaled by 2, Slide 29): `2(x ∧ a) = x a + â x`. -/
@[simp] def rieszWedge (X A : Mat2 B) : Mat2 B :=
  X * A + parityHat A * X

/-- Universal Riesz interior contraction on any ring `A` equipped with a ring endomorphism `hat`. -/
def rieszDotGen {A : Type u} [Ring A] (hat : A →+* A) (x a : A) : A :=
  x * a - hat a * x

/-- Universal Riesz exterior product on any ring `A` equipped with a ring endomorphism `hat`. -/
def rieszWedgeGen {A : Type u} [Ring A] (hat : A →+* A) (x a : A) : A :=
  x * a + hat a * x

/--
**Universal Ring-Hom Riesz Skew-Derivation Theorem (`archetype_X1_universal_ring_hom_skew_derivation`):**
In any associative ring `A` with a ring endomorphism `hat : A →+* A`, `rieszDotGen hat x`
and `rieszWedgeGen hat x` satisfy the unconditional telescoping skew-derivation and
skew-Leibniz laws.
-/
theorem archetype_X1_universal_ring_hom_skew_derivation
    {A : Type u} [Ring A] (hat : A →+* A) (x a b : A) :
    rieszDotGen hat x a + rieszWedgeGen hat x a = (x * a) + (x * a) ∧
    rieszDotGen hat x (a * b) =
      rieszDotGen hat x a * b + hat a * rieszDotGen hat x b ∧
    rieszWedgeGen hat x (a * b) =
      rieszDotGen hat x a * b + hat a * rieszWedgeGen hat x b := by
  refine ⟨?_, ?_, ?_⟩
  · dsimp [rieszDotGen, rieszWedgeGen]
    abel
  · dsimp [rieszDotGen]
    rw [hat.map_mul]
    simp only [sub_mul, mul_sub, mul_assoc]
    abel
  · dsimp [rieszDotGen, rieszWedgeGen]
    rw [hat.map_mul]
    simp only [sub_mul, mul_add, mul_assoc]
    abel

/--
**Archetype X₁ (`archetype_X1_riesz_contraction_wedge_and_skew_derivation_law`):**
Formalizes Slides 28, 29, and 30 in `Mat2 B` over ANY non-commutative ring `[Ring B]`:
1. **Geometric Product Reconstruction (Slide 28–29):**
   `rieszDot X A + rieszWedge X A = (X * A) + (X * A)`.
2. **Universal Skew-Derivation Law for Interior Contraction (Slide 30):**
   `rieszDot X (A * N) = rieszDot X A * N + parityHat A * rieszDot X N`.
3. **Universal Skew-Leibniz Law for Exterior Wedge:**
   `rieszWedge X (A * N) = rieszDot X A * N + parityHat A * rieszWedge X N` and
   `rieszWedge X (A * N) = rieszWedge X A * N - parityHat A * rieszDot X N`.
-/
theorem archetype_X1_riesz_contraction_wedge_and_skew_derivation_law
    (X A N : Mat2 B) :
    -- 1. Riesz decomposition of the geometric product:
    rieszDot X A + rieszWedge X A = (X * A) + (X * A) ∧
    -- 2. Interior contraction is a skew-derivation of the geometric product (Slide 30):
    rieszDot X (A * N) = rieszDot X A * N + parityHat A * rieszDot X N ∧
    -- 3. Dual skew-Leibniz identities for the Riesz exterior product:
    rieszWedge X (A * N) = rieszDot X A * N + parityHat A * rieszWedge X N ∧
    rieszWedge X (A * N) = rieszWedge X A * N - parityHat A * rieszDot X N := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · simp only [rieszDot, rieszWedge, parityHat]; xambo_nc_mat

-- ============================================================================
-- 3. ARCHETYPE X₂: VERSOR REFLECTIONS & HOUSEHOLDER COMMUTATOR ANOMALY (SLIDES 58–62)
-- ============================================================================

/-- Twisted adjoint sandwich `ρ̃(V)(A) = V̂ * A * V` (Slide 60–62). -/
@[simp] def twistSandwich (V A : Mat2 B) : Mat2 B :=
  parityHat V * A * V

/-- Pure grade-1 odd vector `vec1(β₁, β₂) = [[β₁, β₂], [β₂, -β₁]] ∈ Mat2 B` (Slide 45). -/
@[simp] def vec1 (β1 β2 : B) : Mat2 B :=
  ⟨β1, β2, β2, -β1⟩

/--
**Archetype X₂ (`archetype_X2_versor_reflections_and_householder_commutator_anomaly`):**
Formalizes Slides 58–62 in `Mat2 B` over ANY non-commutative ring `[Ring B]`:
1. Every 1-vector `Y = vec1 y₁ y₂` is strictly odd under `parityHat`: `parityHat Y = -Y`.
2. **Twisted Adjoint Composition (Slide 60):**
   `twistSandwich U (twistSandwich V A) = parityHat(U * V) * A * (V * U)`.
3. **Householder–Clifford Reflection vs. Non-Commutative Metric Commutator (Slide 58):**
   For any `X ∈ Mat2 B` and any odd vector `Y = vec1 y₁ y₂`, the difference between the
   Householder reflection `X² * Y - rieszDot X Y * X` and the sandwich reflection `-X * Y * X`
   is IDENTICALLY the commutator `[X², Y]`:
   `(X * X * Y - rieszDot X Y * X) - (-(X * Y * X)) = [X * X, Y]`.
-/
theorem archetype_X2_versor_reflections_and_householder_commutator_anomaly
    (U V A X : Mat2 B) (y1 y2 : B) :
    let Y := vec1 y1 y2
    -- 1. Grade-1 vectors are odd under parityHat:
    parityHat Y = -Y ∧
    -- 2. Twisted adjoint composition law (Slide 60):
    twistSandwich U (twistSandwich V A) = parityHat (U * V) * A * (V * U) ∧
    -- 3. Householder reflection formula & non-commutative metric commutator anomaly [X², Y]:
    (X * X * Y - rieszDot X Y * X) - (-(X * Y * X)) = rcomm (X * X) Y := by
  refine ⟨?_, ?_, ?_⟩ <;>
  · simp only [vec1, twistSandwich, rieszDot, parityHat, rcomm]; xambo_nc_mat

-- ============================================================================
-- 4. ARCHETYPE X₃: DIRAC SPACETIME SPLIT (SLIDES 54–55) & SLIDE 110 ROTOR IDENTITY
-- ============================================================================

/-- 4×4 block operator ring `Mat2 (Mat2 B)` over `B`. -/
abbrev Op4 (B : Type u) := Mat2 (Mat2 B)

/-- Xambó's Dirac generator `Γ₀ = [[1, 0], [0, -1]]` (Slide 55). -/
@[simp] def Gam0 : Op4 B := ⟨1, 0, 0, -1⟩

/-- Xambó's Dirac generator `Γ₁ = [[0, -Ex], [Ex, 0]]` (Slide 55). -/
@[simp] def Gam1 : Op4 B := ⟨0, -Ex, Ex, 0⟩

/-- Xambó's Dirac generator `Γ₂ = [[0, -Ey], [Ey, 0]]` (Slide 55). -/
@[simp] def Gam2 : Op4 B := ⟨0, -Ey, Ey, 0⟩

/-- Xambó's Dirac generator `Γ₃ = [[0, -Ez], [Ez, 0]]` (Slide 55). -/
@[simp] def Gam3 : Op4 B := ⟨0, -Ez, Ez, 0⟩

/-- Relative spacetime bivector `Σ₁ = Γ₁ * Γ₀` (Slide 54). -/
@[simp] def Sig1 : Op4 B := Gam1 * Gam0

/-- Relative spacetime bivector `Σ₂ = Γ₂ * Γ₀` (Slide 54). -/
@[simp] def Sig2 : Op4 B := Gam2 * Gam0

/-- Relative spacetime bivector `Σ₃ = Γ₃ * Γ₀` (Slide 54). -/
@[simp] def Sig3 : Op4 B := Gam3 * Gam0

/--
**Archetype X₃ (`archetype_X3_dirac_spacetime_split_and_slide110_rotor_commutator`):**
1. **Spacetime Relative Vector Split (Slide 54–55):**
   In `Op4 B`, `Σ_k = Γ_k * Γ_0 = [[0, σ_k], [σ_k, 0]]` satisfy `Σ₁² = 1`, `Σ₃² = 1`,
   `Σ₂² = -1`, and mutually anticommute (`{Σ_j, Σ_k} = 0` for `j ≠ k`).
2. **Xambó's Slide 110 Rotor Sine-Law Commutator Identity:**
   For ANY two matrices `R_A, R_B ∈ Mat2 B` over a non-commutative ring `B`:
   - `R_B + cliffConj R_B = diagScalar(tr₂ R_B)`,
   - `[R_A, cliffConj R_B] - [R_B, R_A] = [R_A, R_B + cliffConj R_B] = [R_A, diagScalar(tr₂ R_B)]`.
   (Thus `[R_A, cliffConj R_B] = [R_B, R_A]` holds identically whenever `tr₂ R_B` commutes with `R_A`.)
-/
theorem archetype_X3_dirac_spacetime_split_and_slide110_rotor_commutator
    (RA RB : Mat2 B) :
    -- 1. Spacetime split bivectors Σ_k = Γ_k Γ_0 (Slides 54–55):
    (Sig1 : Op4 B) * Sig1 = 1 ∧
    (Sig3 : Op4 B) * Sig3 = 1 ∧
    (Sig2 : Op4 B) * Sig2 = -1 ∧
    racomm (Sig1 : Op4 B) Sig2 = 0 ∧
    racomm (Sig1 : Op4 B) Sig3 = 0 ∧
    racomm (Sig2 : Op4 B) Sig3 = 0 ∧
    -- 2. Slide 110 Rotor Commutator Identity & Non-Commutative Trace Defect:
    RB + cliffConj RB = diagScalar (tr2 RB) ∧
    rcomm RA (cliffConj RB) - rcomm RB RA = rcomm RA (diagScalar (tr2 RB)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  · simp only [Sig1, Sig2, Sig3, Gam0, Gam1, Gam2, Gam3,
               cliffConj, diagScalar, tr2, Ex, Ey, Ez, rcomm, racomm]; xambo_nc_mat

-- ============================================================================
-- 5. ARCHETYPE X₄: NON-COMMUTATIVE OLINDE RODRIGUES ROTOR COMPOSITION (SLIDE 83)
-- ============================================================================

/-- 3-component vector over `B`. -/
@[ext]
structure Vec3 (B : Type u) where
  x : B
  y : B
  z : B
  deriving DecidableEq, Repr

instance : Inhabited (Vec3 B) := ⟨⟨0, 0, 0⟩⟩

/-- A 3D Rotor `R = c + i u` over a non-commutative ring `B` (Slide 83, Eq. (15)). -/
@[ext]
structure Rotor3 (B : Type u) where
  c : B
  u : Vec3 B
  deriving DecidableEq, Repr

instance : Inhabited (Rotor3 B) := ⟨⟨0, ⟨0, 0, 0⟩⟩⟩

namespace Rotor3

/-- Non-commutative 3D dot product `u · v = u_x v_x + u_y v_y + u_z v_z`. -/
@[simp] def dot3 (u v : Vec3 B) : B := u.x * v.x + u.y * v.y + u.z * v.z

/-- Non-commutative 3D cross product `u × v`. -/
@[simp] def cross3 (u v : Vec3 B) : Vec3 B :=
  ⟨u.y * v.z - u.z * v.y,
   u.z * v.x - u.x * v.z,
   u.x * v.y - u.y * v.x⟩

/-- Componentwise commutator `[c, u] = ([c, u_x], [c, u_y], [c, u_z])`. -/
@[simp] def commVec3 (c : B) (u : Vec3 B) : Vec3 B :=
  ⟨rcomm c u.x, rcomm c u.y, rcomm c u.z⟩

/--
Olinde Rodrigues Rotor Multiplication (Slide 83, Equation (16)):
`(c₁, u₁) * (c₂, u₂) = (c₁ c₂ - u₁ · u₂, c₁ u₂ + u₁ c₂ - u₁ × u₂)`.
-/
@[simp] def mul (R1 R2 : Rotor3 B) : Rotor3 B where
  c := R1.c * R2.c - dot3 R1.u R2.u
  u := ⟨R1.c * R2.u.x + R1.u.x * R2.c - (cross3 R1.u R2.u).x,
        R1.c * R2.u.y + R1.u.y * R2.c - (cross3 R1.u R2.u).y,
        R1.c * R2.u.z + R1.u.z * R2.c - (cross3 R1.u R2.u).z⟩

/-- Reverse conjugate of a 3D rotor `R̃ = (c, -u)` (Slide 93). -/
@[simp] def rev (R1 : Rotor3 B) : Rotor3 B :=
  ⟨R1.c, ⟨-R1.u.x, -R1.u.y, -R1.u.z⟩⟩

/--
**Archetype X₄ (`archetype_X4_noncomm_olinde_rodrigues_rotor_composition_and_curvature`):**
Formalizes Slide 83 (Eq. (16)) and Slide 93 over ANY non-commutative ring `[Ring B]`:
When a 3D rotor `R = (c, u)` with non-commuting operator components in `B` is multiplied
by its reverse `R̃ = (c, -u)`:
1. The scalar part is the quadratic norm `c² + u · u`.
2. The bivector part does NOT vanish when `B` is non-commutative, but exposes the exact
   **Yang–Mills Curvature Obstruction** `-[c, u] + u × u`.
-/
theorem archetype_X4_noncomm_olinde_rodrigues_rotor_composition_and_curvature
    (R1 : Rotor3 B) :
    let normProd := mul R1 (rev R1)
    normProd.c = R1.c * R1.c + dot3 R1.u R1.u ∧
    normProd.u = ⟨-(commVec3 R1.c R1.u).x + (cross3 R1.u R1.u).x,
                  -(commVec3 R1.c R1.u).y + (cross3 R1.u R1.u).y,
                  -(commVec3 R1.c R1.u).z + (cross3 R1.u R1.u).z⟩ := by
  refine ⟨?_, ?_⟩
  · dsimp [mul, rev, dot3]
    simp only [mul_neg]
    abel
  · ext <;>
    · dsimp [mul, rev, cross3, commVec3, rcomm]
      simp only [mul_neg, sub_neg_eq_add, neg_sub]
      abel

end Rotor3

-- ============================================================================
-- 6. OWNER ALIGNMENT BRIDGE TO `NonCommutativeBimetricSheetGeometry`
-- ============================================================================

/-- Equivalence between `NonCommutativeXamboGeometricAlgebra.Mat2 B` and
`NonCommutativeBimetricSheetGeometry.Mat2 B`. -/
@[simp] def toBimetricMat2 (M : Mat2 B) : NonCommutativeBimetricSheetGeometry.Mat2 B :=
  ⟨M.a11, M.a12, M.a21, M.a22⟩

/--
**Owner Alignment (`xambo_bimetric_involutions_alignment`):**
Aligns Xambó's three Clifford involutions (`parityHat`, `revTilde`, `cliffConj`) in
`NonCommutativeXamboGeometricAlgebra` with the transpose `trp`, symplectic adjugate `adj`,
and `Ey`-conjugation in `NonCommutativeBimetricSheetGeometry`:
1. `toBimetricMat2 (revTilde M) = trp (toBimetricMat2 M)`
2. `toBimetricMat2 (cliffConj M) = adj (toBimetricMat2 M)`
3. `toBimetricMat2 (parityHat M) = trp (adj (toBimetricMat2 M))`
-/
theorem xambo_bimetric_involutions_alignment (M : Mat2 B) :
    toBimetricMat2 (revTilde M) =
      NonCommutativeBimetricSheetGeometry.Mat2.trp (toBimetricMat2 M) ∧
    toBimetricMat2 (cliffConj M) =
      NonCommutativeBimetricSheetGeometry.Mat2.adj (toBimetricMat2 M) ∧
    toBimetricMat2 (parityHat M) =
      NonCommutativeBimetricSheetGeometry.Mat2.trp
        (NonCommutativeBimetricSheetGeometry.Mat2.adj (toBimetricMat2 M)) := by
  refine ⟨?_, ?_, ?_⟩
  · have h1 : toBimetricMat2 (revTilde M) =
        NonCommutativeBimetricSheetGeometry.Mat2.trp (toBimetricMat2 M) := Eq.refl _
    exact h1
  · have h2 : toBimetricMat2 (cliffConj M) =
        NonCommutativeBimetricSheetGeometry.Mat2.adj (toBimetricMat2 M) := Eq.refl _
    exact h2
  · have h3 : toBimetricMat2 (parityHat M) =
        NonCommutativeBimetricSheetGeometry.Mat2.trp
          (NonCommutativeBimetricSheetGeometry.Mat2.adj (toBimetricMat2 M)) := Eq.refl _
    exact h3

end Mat2

end NonCommutativeXamboGeometricAlgebra
