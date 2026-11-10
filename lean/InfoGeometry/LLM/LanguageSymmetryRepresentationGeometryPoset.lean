/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.LLM.LanguageSymmetryHelpers
import InfoGeometry.LLM.LanguageSymmetryFourier
import InfoGeometry.LLM.LanguageSymmetryBinary
import InfoGeometry.LLM.LanguageSymmetryWalsh
import InfoGeometry.LLM.LanguageSymmetryToeplitz

/-!
# Language symmetry: the dependency synthesis

The dependency order is a branching proof graph, not a postulated total order:

* the repository's Peirce defect gives the compressed-square ablation law;
* adjoints give positivity and the exact nonvanishing criterion;
* permutation covariance of a rectangular helper map gives a circulant Gramian;
* the native complex character basis diagonalizes that actual Gramian;
* the binary logarithm determines the explicit joint seasonal/attribute spectrum;
* the finite Toeplitz branch supplies a separate open-boundary calculation.

The requested `Poset` filename records this synthesis. No claim is made that
a list of stages itself proves a causal order, a learned representation, or all
results of arXiv:2602.15029. See `docs/LANGUAGE_SYMMETRY_FORMALIZATION.md`.
-/

namespace InfoGeometry.LLM.LanguageSymmetry

open Matrix
open scoped Classical

section Helpers

variable {G H : Type*} [AddCommGroup G] [Fintype G] [Fintype H]

omit [Fintype G] in
/-- A common permutation of helper columns preserves their Gram inner products.
No group-action axioms are needed beyond the explicitly stated covariance. -/
theorem helper_gram_translation_invariant
    (a : Matrix G H ℂ) (e : G → Equiv.Perm H)
    (ha : ∀ x t h, a (x + t) (e t h) = a x h) (x y t : G) :
    (a * aᴴ) (x + t) (y + t) = (a * aᴴ) x y := by
  classical
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
  symm
  refine Fintype.sum_equiv (e t) _ _ ?_
  intro h
  rw [ha x t h, ha y t h]

omit [Fintype G] in
/-- The equivariant helper Gramian is exactly a native relative-displacement
kernel. This supplies the missing bridge from helper symmetry to Fourier theory. -/
theorem helper_gram_eq_circulant
    (a : Matrix G H ℂ) (e : G → Equiv.Perm H)
    (ha : ∀ x t h, a (x + t) (e t h) = a x h) :
    a * aᴴ = circulant (fun x => (a * aᴴ) x 0) := by
  exact translation_invariant_eq_circulant _
    (helper_gram_translation_invariant a e ha)

/-- Exact Fourier eigenvectors of the helper Gramian, with eigenvalues computed
from its own kernel. No equality with an earlier target block is asserted. -/
theorem helper_gram_mulVec_character
    (a : Matrix G H ℂ) (e : G → Equiv.Perm H)
    (ha : ∀ x t h, a (x + t) (e t h) = a x h) (χ : AddChar G ℂ) :
    (a * aᴴ) *ᵥ (χ : G → ℂ) =
      kernelEigenvalue (fun x => (a * aᴴ) x 0) χ • (χ : G → ℂ) := by
  conv_lhs => rw [helper_gram_eq_circulant a e ha]
  exact circulant_mulVec_character _ χ

/-- The helper Gramian is diagonal in a complete basis, not merely on selected
character vectors. Its spectral support still depends on the coupling. -/
theorem helper_gram_toMatrix_complexBasis
    (a : Matrix G H ℂ) (e : G → Equiv.Perm H)
    (ha : ∀ x t h, a (x + t) (e t h) = a x h) :
    LinearMap.toMatrix (AddChar.complexBasis G) (AddChar.complexBasis G)
      (a * aᴴ).mulVecLin =
        diagonal (kernelEigenvalue (fun x => (a * aᴴ) x 0)) := by
  classical
  conv_lhs => rw [helper_gram_eq_circulant a e ha]
  exact circulant_toMatrix_complexBasis _

end Helpers

section JointSpectrum

variable {N d : ℕ} [NeZero N]

/-- Every eigenvalue of the seasonal plus actual logarithmic attribute kernel.
The normalization uses counting measure on `N * 2^d` joint states. -/
theorem seasonal_attribute_eigenvalue (K : ZMod N → ℂ) (s : Fin d → ℝ)
    (hs : ∀ r, |s r| < 1) (χ : AddChar (ZMod N) ℂ)
    (ψ : AddChar (Fin d → ZMod 2) ℂ) :
    kernelEigenvalue (fun z : ZMod N × (Fin d → ZMod 2) =>
      K z.1 + attributeLogKernel s z.2) (productCharacter χ ψ) =
        kernelEigenvalue K χ * (if ψ = 0 then (2 : ℂ) ^ d else 0) +
          (if χ = 0 then (N : ℂ) else 0) *
            ((2 : ℂ) ^ d *
              ((if ψ = 0 then ∑ r, (binaryLogMean (s r) : ℂ) else 0) +
                ∑ r, if ψ = coordinateCharacter d r then
                  (binaryLogContrast (s r) : ℂ) else 0)) := by
  rw [kernelEigenvalue_add_separable, attributeLogKernel_eigenvalue s hs,
    AddChar.sum_eq_ite ψ, AddChar.sum_eq_ite χ]
  simp

/-- A nonconstant seasonal mode carries the seasonal eigenvalue times the
number of attribute states. -/
theorem seasonal_attribute_seasonal_eigenvalue (K : ZMod N → ℂ) (s : Fin d → ℝ)
    (hs : ∀ r, |s r| < 1) (χ : AddChar (ZMod N) ℂ) (hχ : χ ≠ 0) :
    kernelEigenvalue (fun z : ZMod N × (Fin d → ZMod 2) =>
      K z.1 + attributeLogKernel s z.2) (productCharacter χ 0) =
        (2 : ℂ) ^ d * kernelEigenvalue K χ := by
  rw [seasonal_attribute_eigenvalue K s hs]
  simp [hχ, mul_comm]

/-- A coordinate mode at constant seasonal frequency carries exactly its own
logarithmic contrast, scaled by the total number of joint states. -/
theorem seasonal_attribute_coordinate_eigenvalue (K : ZMod N → ℂ) (s : Fin d → ℝ)
    (hs : ∀ r, |s r| < 1) (r : Fin d) :
    kernelEigenvalue (fun z : ZMod N × (Fin d → ZMod 2) =>
      K z.1 + attributeLogKernel s z.2)
        (productCharacter 0 (coordinateCharacter d r)) =
          (N : ℂ) * ((2 : ℂ) ^ d * (binaryLogContrast (s r) : ℂ)) := by
  rw [kernelEigenvalue_add_separable, attributeLogKernel_coordinate_eigenvalue s hs]
  rw [AddChar.sum_eq_ite]
  simp [coordinateCharacter_ne_zero]

end JointSpectrum

end InfoGeometry.LLM.LanguageSymmetry
