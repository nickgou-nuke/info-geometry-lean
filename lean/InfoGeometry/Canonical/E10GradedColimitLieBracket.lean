/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.E10Grading
import Mathlib.Algebra.Lie.Subalgebra

/-!
# The $E_{10}$ Graded Cutoff Union, Lie Subalgebra Closure, & Filtered Colimit Lie Equivalence

This canonical module completes the categorical Kac–Moody / $E_{10}$ filtration-to-colimit
bridge initiated in `InfoGeometry.Canonical.E10Grading`:

1. **Exhaustiveness of the Root-Height Cutoff Union (`heightCutoffUnion_eq_iSup_all`):**
   Proves that the directed supremum $\mathfrak{g}_\infty := \bigsqcup_{N \in \mathbb{N}} \mathfrak{g}_{\le N}$
   of all finite root-height cutoffs `heightCutoff A N` equals the full graded sum
   $\bigsqcup_{i \in \mathbb{Z}} A_i$, because every integer $i \in \mathbb{Z}$ satisfies
   $|i| \le (|i|_{\mathbb{N}} : \mathbb{Z})$.
2. **Lie Bracket Closure of the Directed Union (`heightCutoffUnion_lie_mem`, `heightCutoffUnionLieSubalgebra`):**
   Combining the kinematic filtration bound
   $[\mathfrak{g}_{\le N}, \mathfrak{g}_{\le M}] \subseteq \mathfrak{g}_{\le N+M}$
   (`heightCutoff_lie_le`) with double-supremum bracket distribution (`iSup_lie_iSup_le`),
   we prove that $\mathfrak{g}_\infty = \bigsqcup_{N \in \mathbb{N}} \mathfrak{g}_{\le N}$
   is closed under the Lie bracket and forms a canonical `LieSubalgebra R L`.
3. **Filtered Colimit Injectivity & Range Identification (`heightCutoffColimitMap_injective`, `heightCutoffColimitMap_range_eq_union`):**
   Using `ModuleCat.FilteredColimits`, every element of `heightCutoffColimit A` is represented
   at some finite stage $N \in \mathbb{N}$ (`heightCutoffColimit_exists_stage_rep`), the canonical
   comparison morphism `heightCutoffColimitMap A` is strictly injective, and its range is
   precisely `heightCutoffUnion A`.
4. **Canonical Linear Equivalence (`heightCutoffColimitEquivUnion`) & Transported Lie Bracket (`heightCutoffColimit_lie_bracket_laws`):**
   Establishes the linear isomorphism `heightCutoffColimit A ≃ₗ[R] heightCutoffUnion A` and proves
   that the induced colimit bracket satisfies skew-symmetry, the Jacobi / Leibniz identity, and
   exact compatibility with the ambient Lie bracket on $L$.

### Three-Bucket Epistemic Audit Classification

* **BUCKET 1 — Constructively Proved Lattice, Lie-Subalgebra, & Filtered-Colimit Theorems (`[kernel_verified]`):**
  - `heightCutoffUnion_eq_iSup_all`: $\bigsqcup_{N \in \mathbb{N}} \mathfrak{g}_{\le N} = \bigsqcup_{i \in \mathbb{Z}} A_i$.
  - `heightCutoffUnion_lieSpan_le`, `heightCutoffUnion_lie_mem`, and
    `heightCutoffUnionLieSubalgebra`: Bracket closure $[\mathfrak{g}_\infty, \mathfrak{g}_\infty] \subseteq \mathfrak{g}_\infty$
    and construction of the `LieSubalgebra R L`.
  - `heightCutoffColimit_exists_stage_rep`, `heightCutoffColimitMap_injective`,
    `heightCutoffColimitMap_range_eq_union`, and `heightCutoffColimitEquivUnion`:
    Bijectivity of the filtered colimit comparison map onto `heightCutoffUnion A`.
  - `heightCutoffColimitBracket` and `heightCutoffColimit_lie_bracket_laws`:
    Transported Lie bracket on `heightCutoffColimit A` satisfying `lie_self`, `leibniz_lie`,
    and stage compatibility with `heightCutoff_lie_le`.

* **BUCKET 2 — Eliminated Wrappers & Unverified Colimit Shells (Zero Remaining):**
  - Connects the abstract `ModuleCat` filtered colimit directly to the root-height grading chain
    without assuming an unconstructed filtration.

* **BUCKET 3 — Infinite Completion / Formal Power Series Completion (`[bucket_3_open_debt]`):**
  - The algebraic direct limit $\bigsqcup_{N} \mathfrak{g}_{\le N}$ consists of finite sums of
    root vectors; formal pro-nilpotent completions $\widehat{\mathfrak{g}}$ remain outside this
    filtered-colimit scope.
-/

namespace InfoGeometry.Canonical.E10GradedColimitLieBracket

open CategoryTheory
open CategoryTheory.Limits
open InfoGeometry.Canonical.E10Grading

universe u

-- ============================================================================
-- SECTION 1: Exhaustiveness & Lie Closure of the Root-Height Cutoff Union
-- ============================================================================

section GradedCutoffUnion

variable {R L : Type u} [CommRing R] [LieRing L] [LieAlgebra R L]

/-- The directed union (supremum) $\mathfrak{g}_\infty = \bigsqcup_{N \in \mathbb{N}} \mathfrak{g}_{\le N}$
of all finite root-height cutoffs `heightCutoff A N`. -/
def heightCutoffUnion (A : ℤ → Submodule R L) : Submodule R L :=
  ⨆ N : ℕ, heightCutoff A N

/-- Canonical inclusion of the $N$-th cutoff `heightCutoff A N` into `heightCutoffUnion A`. -/
lemma heightCutoff_le_union (A : ℤ → Submodule R L) (N : ℕ) :
    heightCutoff A N ≤ heightCutoffUnion A := by
  unfold heightCutoffUnion
  exact le_iSup (heightCutoff A) N

/-- **Exhaustiveness of the Root-Height Cutoff Union (`heightCutoffUnion_eq_iSup_all`):**
The supremum of all finite root-height cutoffs $\bigsqcup_{N \in \mathbb{N}} \mathfrak{g}_{\le N}$
equals the full supremum $\bigsqcup_{i \in \mathbb{Z}} A_i$ of all graded components. -/
theorem heightCutoffUnion_eq_iSup_all (A : ℤ → Submodule R L) :
    heightCutoffUnion A = ⨆ i : ℤ, A i := by
  apply le_antisymm
  · unfold heightCutoffUnion heightCutoff
    apply iSup_le
    intro N
    apply iSup_le
    intro i
    apply iSup_le
    intro _
    exact le_iSup A i
  · apply iSup_le
    intro i
    exact le_trans (component_le_heightCutoff A i.natAbs i (le_of_eq (Int.natCast_natAbs i).symm))
      (heightCutoff_le_union A i.natAbs)

/-- **Lie Span Closure of the Cutoff Union (`heightCutoffUnion_lieSpan_le`):**
For any $\mathbb{Z}$-graded family `A : ℤ → Submodule R L`, the Lie bracket span of
`heightCutoffUnion A` with itself is contained in `heightCutoffUnion A`:
$$[\mathfrak{g}_\infty, \mathfrak{g}_\infty] \subseteq \mathfrak{g}_\infty.$$ -/
theorem heightCutoffUnion_lieSpan_le
    (A : ℤ → Submodule R L)
    (hGrad : ∀ {i j : ℤ} {x y : L}, x ∈ A i → y ∈ A j → ⁅x, y⁆ ∈ A (i + j)) :
    lieSpan (heightCutoffUnion A) (heightCutoffUnion A) ≤ heightCutoffUnion A := by
  unfold heightCutoffUnion
  rw [lieSpan_le_iff_left]
  apply iSup_le
  intro N
  rw [← lieSpan_le_iff_left, lieSpan_le_iff_right]
  apply iSup_le
  intro M
  rw [← lieSpan_le_iff_right]
  exact le_trans (heightCutoff_lie_le A hGrad N M) (heightCutoff_le_union A (N + M))

/-- **Elementwise Lie Bracket Closure (`heightCutoffUnion_lie_mem`):**
If $x, y \in \mathrm{heightCutoffUnion}\;A$, then their Lie bracket $\⁅x, y\⁆$ belongs to
$\mathrm{heightCutoffUnion}\;A$. -/
theorem heightCutoffUnion_lie_mem
    (A : ℤ → Submodule R L)
    (hGrad : ∀ {i j : ℤ} {x y : L}, x ∈ A i → y ∈ A j → ⁅x, y⁆ ∈ A (i + j))
    {x y : L} (hx : x ∈ heightCutoffUnion A) (hy : y ∈ heightCutoffUnion A) :
    ⁅x, y⁆ ∈ heightCutoffUnion A := by
  have hSpan := heightCutoffUnion_lieSpan_le A hGrad
  rw [lieSpan_le_iff] at hSpan
  exact hSpan x hx y hy

/-- **The Graded Cutoff Union as a `LieSubalgebra R L` (`heightCutoffUnionLieSubalgebra`):**
Packages `heightCutoffUnion A` and `heightCutoffUnion_lie_mem` into a genuine Mathlib
`LieSubalgebra R L`. -/
def heightCutoffUnionLieSubalgebra
    (A : ℤ → Submodule R L)
    (hGrad : ∀ {i j : ℤ} {x y : L}, x ∈ A i → y ∈ A j → ⁅x, y⁆ ∈ A (i + j)) :
    LieSubalgebra R L :=
  { heightCutoffUnion A with
    lie_mem' := fun hx hy => heightCutoffUnion_lie_mem A hGrad hx hy }

end GradedCutoffUnion

-- ============================================================================
-- SECTION 2: Filtered Colimit Injectivity, Range Equality, & Linear Equivalence
-- ============================================================================

noncomputable section FilteredColimitEquivalence

variable {R L : Type u} [CommRing R] [LieRing L] [LieAlgebra R L]

/-- Canonical isomorphism between `heightCutoffColimit A` and the explicit filtered colimit
cocone point `ModuleCat.FilteredColimits.colimitCocone (heightCutoffDiagram A)`. -/
def heightCutoffIsoColimit (A : ℤ → Submodule R L) :
    heightCutoffColimit A ≅
      (ModuleCat.FilteredColimits.colimitCocone (heightCutoffDiagram A)).pt :=
  (colimit.isColimit (heightCutoffDiagram A)).coconePointUniqueUpToIso
    (ModuleCat.FilteredColimits.colimitCoconeIsColimit (heightCutoffDiagram A))

/-- **Finite-Stage Representation Theorem (`heightCutoffColimit_exists_stage_rep`):**
Every element $x \in \mathrm{heightCutoffColimit}\;A$ arises from some finite root-height cutoff
stage $N \in \mathbb{N}$ and some $z \in \mathrm{heightCutoff}\;A\;N$. -/
theorem heightCutoffColimit_exists_stage_rep (A : ℤ → Submodule R L)
    (x : ↑(heightCutoffColimit A)) :
    ∃ (N : ℕ) (z : (heightCutoffDiagram A).obj N),
      x = (colimit.ι (heightCutoffDiagram A) N).hom z := by
  let y := (heightCutoffIsoColimit A).hom x
  have hrep := ModuleCat.FilteredColimits.M.mk_surjective (heightCutoffDiagram A) y
  rcases hrep with ⟨N, z, hz⟩
  use N, z
  have hx : x = (heightCutoffIsoColimit A).inv y := by
    dsimp [y]
    have h_id : (heightCutoffIsoColimit A).hom ≫ (heightCutoffIsoColimit A).inv = 𝟙 _ :=
      (heightCutoffIsoColimit A).hom_inv_id
    have h_eval :
        (ModuleCat.Hom.hom ((heightCutoffIsoColimit A).hom ≫ (heightCutoffIsoColimit A).inv)) x = x :=
      congrArg (fun F => ModuleCat.Hom.hom F x) h_id
    exact h_eval.symm
  rw [hx, ← hz]
  have h_mk :
      ModuleCat.FilteredColimits.M.mk (heightCutoffDiagram A) ⟨N, z⟩ =
        ((ModuleCat.FilteredColimits.colimitCocone (heightCutoffDiagram A)).ι.app N).hom z := rfl
  rw [h_mk]
  have h_fac :=
    (ModuleCat.FilteredColimits.colimitCoconeIsColimit (heightCutoffDiagram A)).fac
      (colimit.cocone (heightCutoffDiagram A)) N
  have h_fac2 :
      ((ModuleCat.FilteredColimits.colimitCocone (heightCutoffDiagram A)).ι.app N) ≫
        (heightCutoffIsoColimit A).inv =
      colimit.ι (heightCutoffDiagram A) N := h_fac
  exact congrArg (fun F => ModuleCat.Hom.hom F z) h_fac2

/-- **Injectivity of the Filtered Colimit Comparison Map (`heightCutoffColimitMap_injective`):**
The canonical morphism `heightCutoffColimitMap A : heightCutoffColimit A ⟶ ModuleCat.of R L`
is strictly injective. -/
theorem heightCutoffColimitMap_injective (A : ℤ → Submodule R L) :
    Function.Injective (heightCutoffColimitMap A).hom := by
  intro x y hxy
  have h_diff : (heightCutoffColimitMap A).hom (x - y) = 0 := by
    rw [map_sub, hxy, sub_self]
  rcases heightCutoffColimit_exists_stage_rep A (x - y) with ⟨N, z, hz⟩
  have h_stage := heightCutoffColimitMap_stage A N
  have h_eval :
      (heightCutoffColimitMap A).hom ((colimit.ι (heightCutoffDiagram A) N).hom z) = z.1 :=
    congrArg (fun F => ModuleCat.Hom.hom F z) h_stage
  rw [← hz, h_diff] at h_eval
  have hz_zero : z = 0 := Subtype.ext h_eval.symm
  have hx_sub_y : x - y = 0 := by
    rw [hz, hz_zero, map_zero]
    rfl
  exact sub_eq_zero.mp hx_sub_y

/-- Cocone from `heightCutoffDiagram A` into `ModuleCat.of R (heightCutoffUnion A)`. -/
def heightCutoffUnionCocone (A : ℤ → Submodule R L) :
    Cocone (heightCutoffDiagram A) where
  pt := ModuleCat.of R (heightCutoffUnion A)
  ι :=
    { app := fun N =>
        ModuleCat.ofHom (Submodule.inclusion (heightCutoff_le_union A N))
      naturality := fun N M _ => by
        ext ⟨x, hx⟩
        rfl }

/-- **Range Equality Theorem (`heightCutoffColimitMap_range_eq_union`):**
The range of `(heightCutoffColimitMap A).hom` in $L$ equals `heightCutoffUnion A`. -/
theorem heightCutoffColimitMap_range_eq_union (A : ℤ → Submodule R L) :
    LinearMap.range (heightCutoffColimitMap A).hom = heightCutoffUnion A := by
  apply le_antisymm
  · intro x hx
    rcases hx with ⟨y, rfl⟩
    rcases heightCutoffColimit_exists_stage_rep A y with ⟨N, z, rfl⟩
    have hstage := heightCutoffColimitMap_stage A N
    have h_eval :
        (heightCutoffColimitMap A).hom
            ((colimit.ι (heightCutoffDiagram A) N).hom z) = z.1 :=
      congrArg (fun F => ModuleCat.Hom.hom F z) hstage
    rw [h_eval]
    exact (heightCutoff_le_union A N) z.2
  · apply iSup_le
    intro N x hx
    have hstage := heightCutoffColimitMap_stage A N
    let y : (heightCutoffDiagram A).obj N := ⟨x, hx⟩
    use (colimit.ι (heightCutoffDiagram A) N).hom y
    exact congrArg (fun F => ModuleCat.Hom.hom F y) hstage

/-- **Canonical Linear Equivalence (`heightCutoffColimitEquivUnion`):**
The filtered colimit `heightCutoffColimit A` is linearly isomorphic to the directed union
`heightCutoffUnion A`. -/
def heightCutoffColimitEquivUnion (A : ℤ → Submodule R L) :
    heightCutoffColimit A ≃ₗ[R] heightCutoffUnion A :=
  LinearEquiv.ofBijective
    (LinearMap.codRestrict (heightCutoffUnion A) (heightCutoffColimitMap A).hom
      (fun x => by
        rw [← heightCutoffColimitMap_range_eq_union A]
        exact LinearMap.mem_range_self _ _))
    ⟨fun x y h => heightCutoffColimitMap_injective A (Subtype.ext_iff.mp h),
     fun ⟨y, hy⟩ => by
       rw [← heightCutoffColimitMap_range_eq_union A] at hy
       rcases hy with ⟨x, rfl⟩
       exact ⟨x, rfl⟩⟩

/-- Induced Lie bracket on the categorical colimit `heightCutoffColimit A` transported across
`heightCutoffColimitEquivUnion A` from `heightCutoffUnionLieSubalgebra A hGrad`. -/
def heightCutoffColimitBracket
    (A : ℤ → Submodule R L)
    (hGrad : ∀ {i j : ℤ} {x y : L}, x ∈ A i → y ∈ A j → ⁅x, y⁆ ∈ A (i + j))
    (x y : heightCutoffColimit A) : heightCutoffColimit A :=
  (heightCutoffColimitEquivUnion A).symm
    ⟨⁅(heightCutoffColimitEquivUnion A x).1, (heightCutoffColimitEquivUnion A y).1⁆,
     heightCutoffUnion_lie_mem A hGrad
       (heightCutoffColimitEquivUnion A x).2
       (heightCutoffColimitEquivUnion A y).2⟩

/-- **Colimit Lie Algebra Laws (`heightCutoffColimit_lie_bracket_laws`):**
For any $\mathbb{Z}$-graded family `A : ℤ → Submodule R L`:
1. **Alternating / Self-Bracket Vanishing:**
   `heightCutoffColimitBracket A hGrad x x = 0`;
2. **Jacobi / Leibniz Identity:**
   $$[x, [y, z]] = [[x, y], z] + [y, [x, z]];$$
3. **Homomorphism Compatibility with the Ambient Lie Bracket:**
   Evaluating `heightCutoffColimitEquivUnion A` on `heightCutoffColimitBracket A hGrad x y`
   recovers the exact ambient Lie bracket `⁅(heightCutoffColimitEquivUnion A x).1, (heightCutoffColimitEquivUnion A y).1⁆` in $L$. -/
theorem heightCutoffColimit_lie_bracket_laws
    (A : ℤ → Submodule R L)
    (hGrad : ∀ {i j : ℤ} {x y : L}, x ∈ A i → y ∈ A j → ⁅x, y⁆ ∈ A (i + j))
    (x y z : heightCutoffColimit A) :
    heightCutoffColimitBracket A hGrad x x = 0 ∧
    heightCutoffColimitBracket A hGrad x (heightCutoffColimitBracket A hGrad y z) =
      heightCutoffColimitBracket A hGrad (heightCutoffColimitBracket A hGrad x y) z +
        heightCutoffColimitBracket A hGrad y (heightCutoffColimitBracket A hGrad x z) ∧
    ((heightCutoffColimitEquivUnion A (heightCutoffColimitBracket A hGrad x y)).1 =
      ⁅(heightCutoffColimitEquivUnion A x).1, (heightCutoffColimitEquivUnion A y).1⁆) := by
  let eqv := heightCutoffColimitEquivUnion A
  have hCompat : ∀ u v : heightCutoffColimit A,
      (eqv (heightCutoffColimitBracket A hGrad u v)).1 = ⁅(eqv u).1, (eqv v).1⁆ := by
    intro u v
    unfold heightCutoffColimitBracket
    change (eqv (eqv.symm ⟨⁅(eqv u).1, (eqv v).1⁆, _⟩)).1 = ⁅(eqv u).1, (eqv v).1⁆
    rw [LinearEquiv.apply_symm_apply]
  refine ⟨?_, ?_, hCompat x y⟩
  · apply eqv.injective
    apply Subtype.ext
    rw [hCompat x x, lie_self]
    simp only [map_zero, ZeroMemClass.coe_zero]
  · apply eqv.injective
    apply Subtype.ext
    simp only [map_add, Submodule.coe_add, hCompat]
    exact leibniz_lie (eqv x).1 (eqv y).1 (eqv z).1

end FilteredColimitEquivalence

end InfoGeometry.Canonical.E10GradedColimitLieBracket
