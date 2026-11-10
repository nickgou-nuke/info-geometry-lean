/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.CharP.Two
import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
import Mathlib.LinearAlgebra.Matrix.Circulant
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Tactic.Ring

/-!
# Finite translation kernels and product character spectra

The carrier is an arbitrary finite abelian group. A relative-displacement
kernel is a native `Matrix.circulant`; its diagonalizing basis is Mathlib's
`AddChar.complexBasis`. Product characters give a literal tensor-product
function basis. The additive kernel `K (x - y) + L (a - b)` has zero mixed
nontrivial modes; its matrix is not an identity-based Kronecker sum.

The cyclic-by-binary specialization uses `ZMod N × (Fin d → ZMod 2)`.
These exact finite identities make no claim about dominant frequencies,
training dynamics, corpus ablation, or recovery of an unchanged embedding.
-/

noncomputable section

namespace InfoGeometry.LLM.LanguageSymmetry

open Matrix Module
open scoped BigOperators Classical

section TranslationKernel

variable {G : Type*} [AddCommGroup G] [Fintype G]

/-- Fourier coefficient with the sign convention for the kernel `K (x - y)`. -/
def kernelEigenvalue (K : G → ℂ) (χ : AddChar G ℂ) : ℂ :=
  ∑ t, K t * χ (-t)

omit [Fintype G] in
/-- A relative-displacement matrix is invariant under simultaneous shifts. -/
theorem circulant_translation_invariant (K : G → ℂ) (x y t : G) :
    circulant K (x + t) (y + t) = circulant K x y := by
  simp only [circulant_apply]
  congr 1
  abel

omit [Fintype G] in
/-- Simultaneous translation invariance determines a relative-displacement
kernel, with the zero-column entries as its coefficients. -/
theorem translation_invariant_eq_circulant (M : Matrix G G ℂ)
    (hM : ∀ x y t : G, M (x + t) (y + t) = M x y) :
    M = circulant (fun x => M x 0) := by
  ext x y
  simpa [circulant_apply, sub_eq_add_neg] using (hM x y (-y)).symm

/-- Every finite additive character is an exact eigenvector of the relative
displacement kernel, with its actual Fourier coefficient as eigenvalue. -/
theorem circulant_mulVec_character (K : G → ℂ) (χ : AddChar G ℂ) :
    circulant K *ᵥ (χ : G → ℂ) = kernelEigenvalue K χ • (χ : G → ℂ) := by
  ext x
  simp only [mulVec, dotProduct, circulant_apply, Pi.smul_apply, smul_eq_mul,
    kernelEigenvalue, Finset.sum_mul]
  refine Fintype.sum_equiv (Equiv.subLeft x) _ _ ?_
  intro y
  simp only [Equiv.subLeft_apply]
  rw [mul_assoc, ← χ.map_add_eq_mul]
  have h : -(x - y) + x = y := by abel
  rw [h]

/-- The complex character family is a full native basis, not only a collection
of candidate eigenvectors. In these coordinates the kernel is diagonal. -/
theorem circulant_toMatrix_complexBasis (K : G → ℂ) :
    LinearMap.toMatrix (AddChar.complexBasis G) (AddChar.complexBasis G)
      (circulant K).mulVecLin = diagonal (kernelEigenvalue K) := by
  classical
  ext χ ψ
  rw [LinearMap.toMatrix_apply, Matrix.mulVecLin_apply]
  have hψ : circulant K *ᵥ AddChar.complexBasis G ψ =
      kernelEigenvalue K ψ • AddChar.complexBasis G ψ := by
    simpa only [AddChar.complexBasis_apply] using circulant_mulVec_character K ψ
  rw [hψ]
  rw [map_smul, (AddChar.complexBasis G).repr_self]
  by_cases h : χ = ψ
  · subst ψ
    simp
  · simp [h]

/-- Each character value lies exactly on the real unit circle. This identity
does not assert that a chosen mode is injective or spectrally dominant. -/
theorem character_real_imag_unit_circle (χ : AddChar G ℂ) (x : G) :
    (χ x).re ^ 2 + (χ x).im ^ 2 = 1 := by
  calc
    (χ x).re ^ 2 + (χ x).im ^ 2 = Complex.normSq (χ x) := by
      rw [Complex.normSq_apply, pow_two, pow_two]
    _ = ‖χ x‖ ^ 2 := Complex.normSq_eq_norm_sq _
    _ = 1 := by rw [χ.norm_apply x, one_pow]

end TranslationKernel

section ProductCharacters

variable {G H : Type*} [AddCommGroup G] [AddCommGroup H]

/-- The native additive character on a product induced by two characters. -/
def productCharacter (χ : AddChar G ℂ) (ψ : AddChar H ℂ) : AddChar (G × H) ℂ :=
  χ.compAddMonoidHom (AddMonoidHom.fst G H) *
    ψ.compAddMonoidHom (AddMonoidHom.snd G H)

@[simp]
theorem productCharacter_apply (χ : AddChar G ℂ) (ψ : AddChar H ℂ) (z : G × H) :
    productCharacter χ ψ z = χ z.1 * ψ z.2 := rfl

/-- Every character on a product splits uniquely into its two restrictions. -/
def productCharacterEquiv :
    (AddChar G ℂ × AddChar H ℂ) ≃ AddChar (G × H) ℂ where
  toFun p := productCharacter p.1 p.2
  invFun θ :=
    (θ.compAddMonoidHom (AddMonoidHom.inl G H),
      θ.compAddMonoidHom (AddMonoidHom.inr G H))
  left_inv p := by
    rcases p with ⟨χ, ψ⟩
    apply Prod.ext <;> ext x <;> simp [productCharacter]
  right_inv θ := by
    ext z
    rcases z with ⟨x, y⟩
    simp only [productCharacter_apply, AddChar.compAddMonoidHom_apply,
      AddMonoidHom.inl_apply, AddMonoidHom.inr_apply]
    rw [← θ.map_add_eq_mul]
    simp

variable [Fintype G] [Fintype H]

omit [Fintype G] [Fintype H] in
/-- The additive product kernel uses all-ones matrices in its tensor factors.
Those matrices must not be replaced by identities. -/
theorem circulant_add_separable_kronecker (K : G → ℂ) (L : H → ℂ) :
    circulant (fun z : G × H => K z.1 + L z.2) =
      Matrix.kronecker (circulant K) (fun _ _ : H => (1 : ℂ)) +
        Matrix.kronecker (fun _ _ : G => (1 : ℂ)) (circulant L) := by
  ext ⟨x, a⟩ ⟨y, b⟩
  change K (x - y) + L (a - b) = K (x - y) * 1 + 1 * L (a - b)
  simp only [mul_one, one_mul]

/-- A complete product-character basis obtained by reindexing Mathlib's
finite Pontryagin basis, with no additional basis assumption. -/
def productCharacterBasis :
    Basis (AddChar G ℂ × AddChar H ℂ) ℂ ((G × H) → ℂ) :=
  (AddChar.complexBasis (G × H)).reindex productCharacterEquiv.symm

@[simp]
theorem productCharacterBasis_apply (χ : AddChar G ℂ) (ψ : AddChar H ℂ)
    (z : G × H) : productCharacterBasis (χ, ψ) z = χ z.1 * ψ z.2 := by
  simp [productCharacterBasis, productCharacterEquiv]

/-- Exact eigenvalues of an additive separable kernel. The constant-factor
character sums are the all-ones-matrix factors in its tensor decomposition. -/
theorem kernelEigenvalue_add_separable (K : G → ℂ) (L : H → ℂ)
    (χ : AddChar G ℂ) (ψ : AddChar H ℂ) :
    kernelEigenvalue (fun z : G × H => K z.1 + L z.2) (productCharacter χ ψ) =
      kernelEigenvalue K χ * (∑ y : H, ψ y) +
        (∑ x : G, χ x) * kernelEigenvalue L ψ := by
  have hG : (∑ x : G, χ (-x)) = ∑ x : G, χ x :=
    Equiv.sum_comp (Equiv.neg G) (fun x => χ x)
  have hH : (∑ y : H, ψ (-y)) = ∑ y : H, ψ y :=
    Equiv.sum_comp (Equiv.neg H) (fun y => ψ y)
  rw [← hG, ← hH]
  simp only [kernelEigenvalue, Fintype.sum_prod_type, productCharacter_apply,
    Prod.fst_neg, Prod.snd_neg, Finset.sum_mul, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  ring

/-- Nontrivial characters in both factors are killed by an additive separable
kernel. This prevents a false claim of nonzero mixed Fourier-Walsh features. -/
theorem additive_kernel_mixed_character_zero (K : G → ℂ) (L : H → ℂ)
    (χ : AddChar G ℂ) (ψ : AddChar H ℂ) (hχ : χ ≠ 0) (hψ : ψ ≠ 0) :
    circulant (fun z : G × H => K z.1 + L z.2) *ᵥ
      (productCharacter χ ψ : (G × H) → ℂ) = 0 := by
  rw [circulant_mulVec_character, kernelEigenvalue_add_separable]
  rw [AddChar.sum_eq_zero_iff_ne_zero.mpr hχ,
    AddChar.sum_eq_zero_iff_ne_zero.mpr hψ]
  simp

end ProductCharacters

section SeasonalBinary

variable (N d : ℕ) [NeZero N]

/-- Complete Fourier-by-binary-character basis, indexed by a cyclic frequency
and a character of the finite binary group. -/
def seasonalBinaryBasis :
    Basis (ZMod N × AddChar (Fin d → ZMod 2) ℂ) ℂ
      ((ZMod N × (Fin d → ZMod 2)) → ℂ) :=
  (productCharacterBasis (G := ZMod N) (H := Fin d → ZMod 2)).reindex
    ((AddChar.zmodAddEquiv (n := N)).symm.toEquiv.prodCongr (Equiv.refl _))

@[simp]
theorem seasonalBinaryBasis_apply (k : ZMod N) (ψ : AddChar (Fin d → ZMod 2) ℂ)
    (z : ZMod N × (Fin d → ZMod 2)) :
    seasonalBinaryBasis N d (k, ψ) z =
      (AddChar.zmodAddEquiv (n := N) k) z.1 * ψ z.2 := by
  simp [seasonalBinaryBasis, Basis.reindex_apply]

/-- Characters on the binary group take the Walsh values `+1` and `-1`.
The group is finite for every natural dimension, including dimension zero. -/
theorem binary_character_eq_one_or_neg_one (ψ : AddChar (Fin d → ZMod 2) ℂ)
    (a : Fin d → ZMod 2) : ψ a = 1 ∨ ψ a = -1 := by
  apply mul_self_eq_one_iff.mp
  rw [← ψ.map_add_eq_mul]
  have ha : a + a = 0 := by
    ext r
    exact CharTwo.add_self_eq_zero (a r)
  rw [ha, ψ.map_zero_eq_one]

/-- Every element of the complete Fourier-Walsh basis is an eigenvector of
every translation kernel on the cyclic-by-binary group. -/
theorem circulant_mulVec_seasonalBinaryBasis
    (K : (ZMod N × (Fin d → ZMod 2)) → ℂ)
    (k : ZMod N) (ψ : AddChar (Fin d → ZMod 2) ℂ) :
    circulant K *ᵥ seasonalBinaryBasis N d (k, ψ) =
      kernelEigenvalue K
        (productCharacter (AddChar.zmodAddEquiv (n := N) k) ψ) •
          seasonalBinaryBasis N d (k, ψ) := by
  have hb : seasonalBinaryBasis N d (k, ψ) =
      (productCharacter (AddChar.zmodAddEquiv (n := N) k) ψ :
        (ZMod N × (Fin d → ZMod 2)) → ℂ) := by
    ext z
    simp
  rw [hb]
  exact circulant_mulVec_character K _

end SeasonalBinary

end InfoGeometry.LLM.LanguageSymmetry
