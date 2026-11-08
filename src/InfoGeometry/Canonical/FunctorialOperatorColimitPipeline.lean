/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.Star.Basic
import Mathlib.Algebra.Star.StarAlgHom
import Mathlib.Topology.Algebra.Star
import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Tactic

/-!
# Star-Algebra Automorphism Conjugation Transport and Metric Isometry Preservation

This module formalizes the algebraic conjugation transport of star-algebra automorphisms:
1. **Conjugation Transport of Star-Automorphisms**: Given any star-algebra equivalence
   $e : A \simeq⋆\ₐ[R] B$ and an automorphism $\sigma$ of $B$, the transported map
   $e^{-1} \circ \sigma \circ e$ is a genuine star-algebra automorphism of $A$.
2. **Functorial Composition Law**: Transport preserves transitivity $\sigma_1 \circ \sigma_2$ and identity,
   guaranteeing group-law fidelity for continuous modular flows.
3. **Isometric Transport**: If the equivalence $e$ and automorphism $\sigma$ are isometries,
   the transported automorphism is strictly isometric and distance-preserving.

All theorems are proved without `sorry` or `admit` using standard Mathlib foundations.
-/

namespace InfoGeometry.Canonical.FunctorialColimit

variable {R A B : Type*}
variable [CommSemiring R] [Semiring A] [Algebra R A] [StarRing A]
variable [Semiring B] [Algebra R B] [StarRing B]

/-- Transport a star-algebra automorphism on $B$ to a star-algebra automorphism on $A$
along a star-algebra equivalence $e : A \simeq⋆\ₐ[R] B$. -/
def transportStarAlgAut (e : A ≃⋆ₐ[R] B) (σ : B ≃⋆ₐ[R] B) : A ≃⋆ₐ[R] A :=
  (e.trans σ).trans e.symm

@[simp] theorem transportStarAlgAut_apply (e : A ≃⋆ₐ[R] B) (σ : B ≃⋆ₐ[R] B) (x : A) :
    transportStarAlgAut e σ x = e.symm (σ (e x)) :=
  rfl

@[simp] theorem transportStarAlgAut_refl (e : A ≃⋆ₐ[R] B) :
    transportStarAlgAut e (StarAlgEquiv.refl (R := R) (A := B)) =
      StarAlgEquiv.refl (R := R) (A := A) := by
  ext x
  simp [transportStarAlgAut]

/-- Functorial composition: transport preserves the group law of modular flows. -/
theorem transportStarAlgAut_trans (e : A ≃⋆ₐ[R] B) (σ₁ σ₂ : B ≃⋆ₐ[R] B) :
    transportStarAlgAut e (σ₁.trans σ₂) =
      (transportStarAlgAut e σ₁).trans (transportStarAlgAut e σ₂) := by
  ext x
  simp [transportStarAlgAut]

/-! ### Metric Isometry Transport -/

variable [PseudoMetricSpace A] [PseudoMetricSpace B]

/-- If the equivalence $e$ and the automorphism $\sigma$ are isometries, the transported
automorphism on the completed carrier is strictly isometric. -/
theorem transportStarAlgAut_isometry (e : A ≃⋆ₐ[R] B) (σ : B ≃⋆ₐ[R] B)
    (he : Isometry (e : A → B))
    (hesymm : Isometry (e.symm : B → A))
    (hσ : Isometry (σ : B → B)) :
    Isometry (transportStarAlgAut e σ : A → A) := by
  have hcomp : (transportStarAlgAut e σ : A → A) =
      (e.symm : B → A) ∘ ((σ : B → B) ∘ (e : A → B)) := by
    ext x
    rfl
  rw [hcomp]
  exact hesymm.comp (hσ.comp he)

/-- The transported automorphism preserves distances. -/
theorem transportStarAlgAut_dist_eq (e : A ≃⋆ₐ[R] B) (σ : B ≃⋆ₐ[R] B)
    (he : Isometry (e : A → B))
    (hesymm : Isometry (e.symm : B → A))
    (hσ : Isometry (σ : B → B))
    (x y : A) :
    dist (transportStarAlgAut e σ x) (transportStarAlgAut e σ y) = dist x y := by
  exact (transportStarAlgAut_isometry e σ he hesymm hσ).dist_eq x y

end InfoGeometry.Canonical.FunctorialColimit
