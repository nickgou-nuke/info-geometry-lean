/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic.Abel

/-!
# Translation symmetry of finite language-statistics kernels

## i. Overview

For a finite additive group, a periodic pair kernel has entries depending on
the displacement `j - i`. This file proves that matrix composition preserves
simultaneous translation invariance, the finite algebraic content behind the
paper's claim that indirect paths preserve periodic symmetry.

## ii. Key results

* `relativeKernelMatrix` turns a displacement function into a finite matrix.
* `relativeKernelMatrix_mul_translation_invariant` proves that the product of
  two such matrices is invariant under translating both indices.

## iii. Table of contents

1. Finite translation equivalence.
2. Periodic difference-kernel matrices and composition.

## iv. References

* Karkada, Korchinski, Nava, Wyart, and Bahri, “Symmetry in language
  statistics shapes the geometry of model representations,” arXiv:2602.15029.
* `InfoGeometry.Canonical.SmithBlockCirculantMoorePenrose` for the concrete
  3-by-3 cyclic-shift commutation identity.
* `InfoGeometry.LLM.FourierSuperposition` for translation-invariant finite
  Fourier-character kernels.

### Three-Bucket Audit Classification

- **BUCKET 1 — Proved Here in Lean (Finite Algebraic Kernel):**
  - `translateEquiv`: Additive translation equivalence `x ↦ x + a` with inverse `x ↦ x - a`.
  - `relativeKernelMatrix`: Finite matrix `fun i j => f (j - i)` attached to a displacement kernel `f : G → R`.
  - `relativeKernelMatrix_mul_translation_invariant`: Exact preservation of simultaneous translation
    invariance `(relativeKernelMatrix f * relativeKernelMatrix g) (i + a) (j + a) = (relativeKernelMatrix f * relativeKernelMatrix g) i j`.
- **BUCKET 2 — Imported Supporting Owners:**
  - `Mathlib.Algebra.BigOperators.Group.Finset.Basic`, `Mathlib.Data.Matrix.Basic`, `Mathlib.Tactic.Abel`.
- **BUCKET 3 — Out-of-Scope Empirical / Continuum Claims (Explicitly Excluded):**
  - Empirical corpus statistics, large-vocabulary asymptotic limits, and SGD training dynamics from
    arXiv:2602.15029 remain outside this finite algebraic kernel module.
-/

namespace InfoGeometry.Canonical.LanguageStatisticsTranslationSymmetry

open scoped BigOperators

variable {G R : Type*}
variable [AddCommGroup G] [Fintype G] [Semiring R]

/-- Translation by `a`, with inverse translation by `-a`. -/
def translateEquiv (a : G) : G ≃ G where
  toFun x := x + a
  invFun x := x - a
  left_inv x := by simp [sub_eq_add_neg, add_assoc]
  right_inv x := by simp [sub_eq_add_neg, add_assoc]

/-- Matrix whose entry at `(i,j)` depends only on the displacement `j-i`. -/
def relativeKernelMatrix (f : G → R) : Matrix G G R :=
  fun i j => f (j - i)

/-- Finite convolution of two displacement kernels, with the convention used by
`relativeKernelMatrix`: `(f ⋆ g) d = ∑ u, f u * g (d - u)`. -/
def finiteKernelConvolution (f g : G → R) (d : G) : R :=
  ∑ u : G, f u * g (d - u)

/-- Composing two periodic difference kernels preserves simultaneous
translation invariance of the source and target indices. -/
lemma relativeKernelMatrix_mul_translation_invariant
    (f g : G → R) (a i j : G) :
    (relativeKernelMatrix f * relativeKernelMatrix g) (i + a) (j + a) =
      (relativeKernelMatrix f * relativeKernelMatrix g) i j := by
  classical
  simp only [Matrix.mul_apply, relativeKernelMatrix]
  rw [← Equiv.sum_comp (translateEquiv a)
    (fun k : G => f (k - (i + a)) * g ((j + a) - k))]
  apply Finset.sum_congr rfl
  intro k hk
  change f ((k + a) - (i + a)) * g ((j + a) - (k + a)) =
    f (k - i) * g (j - k)
  congr 2 <;> abel

/-- Composition of two periodic difference-kernel matrices is the matrix of
the finite convolution of their kernels. This identifies the exact kernel
carried by a two-step path; it does not identify that path with a projected
subspace excursion unless a separate projection/model theorem is supplied. -/
theorem relativeKernelMatrix_mul_eq_convolution
    (f g : G → R) (i j : G) :
    (relativeKernelMatrix f * relativeKernelMatrix g) i j =
      finiteKernelConvolution f g (j - i) := by
  classical
  simp only [Matrix.mul_apply, relativeKernelMatrix, finiteKernelConvolution]
  rw [← Equiv.sum_comp (translateEquiv i)
    (fun k : G => f (k - i) * g (j - k))]
  apply Finset.sum_congr rfl
  intro k hk
  change f ((k + i) - i) * g (j - (k + i)) = f k * g ((j - i) - k)
  congr 2 <;> abel

end InfoGeometry.Canonical.LanguageStatisticsTranslationSymmetry
