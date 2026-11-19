/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.Algebra.Lie.Subalgebra

/-!
# Graded root-height cutoffs and their filtered module colimit

For a Lie algebra equipped with a `ℤ`-indexed family of submodules, this file
constructs the finite absolute-height cutoffs and their natural directed
system. The grading family is arbitrary; closure under the Lie bracket is
provided explicitly when needed.
-/

namespace InfoGeometry.Canonical.E10Grading

open CategoryTheory CategoryTheory.Limits

universe u

section Cutoffs

variable {R L : Type u} [CommRing R] [LieRing L] [LieAlgebra R L]

/-- Elements supported in graded pieces of absolute index at most `N`. -/
def heightCutoff (A : ℤ → Submodule R L) (N : ℕ) : Submodule R L :=
  Submodule.span R {x | ∃ i : ℤ, i.natAbs ≤ N ∧ x ∈ A i}

/-- Every graded component occurs in the cutoff at its absolute index. -/
lemma component_le_heightCutoff (A : ℤ → Submodule R L) (N : ℕ) (i : ℤ)
    (hi : i.natAbs ≤ N) : A i ≤ heightCutoff A N := by
  unfold heightCutoff
  intro x hx
  exact Submodule.subset_span ⟨i, hi, hx⟩

/-- The absolute-height cutoffs form an increasing family. -/
lemma heightCutoff_mono (A : ℤ → Submodule R L) {N M : ℕ} (h : N ≤ M) :
    heightCutoff A N ≤ heightCutoff A M := by
  unfold heightCutoff
  apply Submodule.span_mono
  intro x hx
  rcases hx with ⟨i, hi, hxi⟩
  exact ⟨i, hi.trans h, hxi⟩

/-- The submodule spanned by brackets with one input in each of two submodules. -/
def lieSpan (P Q : Submodule R L) : Submodule R L :=
  Submodule.span R {z | ∃ x, x ∈ P ∧ ∃ y, y ∈ Q ∧ ⁅x, y⁆ = z}

/-- Membership criterion for the bracket span. -/
theorem lieSpan_le_iff (P Q S : Submodule R L) :
    lieSpan P Q ≤ S ↔ ∀ x ∈ P, ∀ y ∈ Q, ⁅x, y⁆ ∈ S := by
  rw [lieSpan, Submodule.span_le]
  constructor
  · intro h x hx y hy
    exact h ⟨x, hx, y, hy, rfl⟩
  · intro h z hz
    rcases hz with ⟨x, hx, y, hy, rfl⟩
    exact h x hx y hy

/-- A bracket-compatible grading gives the expected additive cutoff bound. -/
theorem heightCutoff_lie_le (A : ℤ → Submodule R L)
    (hGrad : ∀ {i j : ℤ} {x y : L}, x ∈ A i → y ∈ A j → ⁅x, y⁆ ∈ A (i + j))
    (N M : ℕ) :
    lieSpan (heightCutoff A N) (heightCutoff A M) ≤ heightCutoff A (N + M) := by
  rw [lieSpan_le_iff]
  intro x hx y hy
  unfold heightCutoff at hx hy ⊢
  apply Submodule.span_induction₂
    (mem_mem := by
      rintro x y ⟨i, hi, hxi⟩ ⟨j, hj, hyj⟩
      apply Submodule.subset_span
      refine ⟨i + j, ?_, hGrad hxi hyj⟩
      exact (Int.natAbs_add_le i j).trans (Nat.add_le_add hi hj))
    (zero_left := by intro y hy; simp)
    (zero_right := by intro x hx; simp)
    (add_left := by
      intro x₁ x₂ y hx₁ hx₂ hy h₁ h₂
      rw [add_lie]
      exact Submodule.add_mem _ h₁ h₂)
    (add_right := by
      intro x y₁ y₂ hx hy₁ hy₂ h₁ h₂
      rw [lie_add]
      exact Submodule.add_mem _ h₁ h₂)
    (smul_left := by
      intro a x y hx hy hxy
      rw [smul_lie]
      exact Submodule.smul_mem _ a hxy)
    (smul_right := by
      intro a x y hx hy hxy
      rw [lie_smul]
      exact Submodule.smul_mem _ a hxy)
    hx hy

end Cutoffs

section FilteredSystem

variable {R L : Type u} [CommRing R] [LieRing L] [LieAlgebra R L]

/-- The diagram of inclusions between finite root-height cutoffs. -/
noncomputable def heightCutoffDiagram (A : ℤ → Submodule R L) : ℕ ⥤ ModuleCat R where
  obj N := ModuleCat.of R (heightCutoff A N)
  map f := ModuleCat.ofHom (Submodule.inclusion (heightCutoff_mono A (leOfHom f)))
  map_id N := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    rfl
  map_comp f g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    rfl

/-- The categorical filtered colimit of the finite-height cutoff system. -/
noncomputable def heightCutoffColimit (A : ℤ → Submodule R L) : ModuleCat R :=
  colimit (heightCutoffDiagram A)

/-- The canonical cocone from finite cutoffs into the ambient Lie algebra. -/
noncomputable def heightCutoffCocone (A : ℤ → Submodule R L) :
    Cocone (heightCutoffDiagram A) where
  pt := ModuleCat.of R L
  ι := {
    app := fun N => ModuleCat.ofHom (Submodule.subtype (heightCutoff A N))
    naturality := fun N M f => by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      rfl
  }

/-- The comparison map from the filtered colimit into the ambient Lie algebra. -/
noncomputable def heightCutoffColimitMap (A : ℤ → Submodule R L) :
    heightCutoffColimit A ⟶ ModuleCat.of R L :=
  colimit.desc (heightCutoffDiagram A) (heightCutoffCocone A)

/-- On each finite stage the comparison map is the ordinary submodule inclusion. -/
theorem heightCutoffColimitMap_stage (A : ℤ → Submodule R L) (N : ℕ) :
    colimit.ι (heightCutoffDiagram A) N ≫ heightCutoffColimitMap A =
      (heightCutoffCocone A).ι.app N :=
  colimit.ι_desc (heightCutoffCocone A) N

end FilteredSystem

end InfoGeometry.Canonical.E10Grading
