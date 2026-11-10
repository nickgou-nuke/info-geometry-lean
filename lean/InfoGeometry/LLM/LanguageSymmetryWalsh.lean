/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.LLM.LanguageSymmetryFourier
import InfoGeometry.LLM.LanguageSymmetryBinary
import Mathlib.Algebra.Group.Pi.Lemmas
import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
import Mathlib.Tactic.NormNum

/-!
# Binary attribute logarithms and their exact character support

Coordinate signs are native real additive characters on `Fin d → ZMod 2`.
Their complexifications are distinct nontrivial Walsh characters. For
`|s r| < 1`, the actual real logarithm of the positive attribute product is a
constant plus a weighted sum of these coordinate characters.

Finite character orthogonality then computes every eigenvalue, including
zero eigenvalues outside the constant and coordinate modes. No equality with
a learned embedding, coordinate spectral dominance, or identification of
arbitrary operator-valued logarithms is asserted.
-/

noncomputable section

namespace InfoGeometry.LLM.LanguageSymmetry

open Matrix
open scoped BigOperators Classical

section CharacterSupport

variable {G ι : Type*} [AddCommGroup G] [Fintype G] [Fintype ι]

/-- Orthogonality in the sign convention of `kernelEigenvalue`. -/
theorem kernelEigenvalue_character (φ ψ : AddChar G ℂ) :
    kernelEigenvalue (φ : G → ℂ) ψ =
      if φ = ψ then (Fintype.card G : ℂ) else 0 := by
  simpa only [kernelEigenvalue, ← AddChar.sub_apply, sub_eq_zero] using
    (AddChar.sum_eq_ite (φ - ψ))

/-- The spectrum of a constant plus a finite character expansion. Repeated
characters are allowed; their coefficients are added by the displayed sum. -/
theorem kernelEigenvalue_character_expansion
    (c : ℂ) (β : ι → ℂ) (φ : ι → AddChar G ℂ) (ψ : AddChar G ℂ) :
    kernelEigenvalue (fun x => c + ∑ r, β r * φ r x) ψ =
      (Fintype.card G : ℂ) *
        ((if ψ = 0 then c else 0) + ∑ r, if ψ = φ r then β r else 0) := by
  have hconst : kernelEigenvalue (fun _ : G => (1 : ℂ)) ψ =
      if ψ = 0 then (Fintype.card G : ℂ) else 0 := by
    calc
      kernelEigenvalue (fun _ : G => (1 : ℂ)) ψ = ∑ x, ψ (-x) := by
        simp only [kernelEigenvalue, one_mul]
      _ = ∑ x, ψ x := Equiv.sum_comp (Equiv.neg G) (fun x => ψ x)
      _ = _ := AddChar.sum_eq_ite ψ
  calc
    kernelEigenvalue (fun x => c + ∑ r, β r * φ r x) ψ =
        c * kernelEigenvalue (fun _ => 1) ψ +
          ∑ r, β r * kernelEigenvalue (φ r : G → ℂ) ψ := by
      simp only [kernelEigenvalue, add_mul, Finset.sum_add_distrib,
        Finset.sum_mul, Finset.mul_sum, one_mul]
      rw [Finset.sum_comm]
      apply congrArg₂ (· + ·)
      · rfl
      · apply Finset.sum_congr rfl
        intro r _
        apply Finset.sum_congr rfl
        intro x _
        ring
    _ = (Fintype.card G : ℂ) *
        ((if ψ = 0 then c else 0) + ∑ r, if ψ = φ r then β r else 0) := by
      rw [hconst]
      simp only [kernelEigenvalue_character, mul_add, Finset.mul_sum]
      apply congrArg₂ (· + ·)
      · split_ifs <;> ring
      · apply Finset.sum_congr rfl
        intro r _
        by_cases h : ψ = φ r
        · simp [h, mul_comm]
        · simp [h, Ne.symm h]

end CharacterSupport

section BinaryCoordinates

variable (d : ℕ)

/-- The real sign character of a single binary coordinate. -/
def coordinateSign (r : Fin d) : AddChar (Fin d → ZMod 2) ℝ :=
  (AddChar.zmodChar 2 (ζ := (-1 : ℝ)) (by norm_num)).compAddMonoidHom
    (Pi.evalAddMonoidHom (fun _ : Fin d => ZMod 2) r)

/-- The same coordinate character with values in the complex spectral field. -/
def coordinateCharacter (r : Fin d) : AddChar (Fin d → ZMod 2) ℂ :=
  Complex.ofRealHom.toMonoidHom.compAddChar (coordinateSign d r)

@[simp]
theorem coordinateCharacter_apply (r : Fin d) (a : Fin d → ZMod 2) :
    coordinateCharacter d r a = (coordinateSign d r a : ℂ) := rfl

/-- Each real coordinate value is a sign, including on the zero-dimensional
binary group where there are no coordinate indices. -/
theorem coordinateSign_sq (r : Fin d) (a : Fin d → ZMod 2) :
    coordinateSign d r a ^ 2 = 1 := by
  rw [pow_two, ← (coordinateSign d r).map_add_eq_mul]
  have ha : a + a = 0 := by
    ext j
    exact CharTwo.add_self_eq_zero (a j)
  rw [ha, (coordinateSign d r).map_zero_eq_one]

/-- Relative displacement gives the product of the two binary signs. -/
theorem coordinateSign_sub (r : Fin d) (a b : Fin d → ZMod 2) :
    coordinateSign d r (a - b) = coordinateSign d r a * coordinateSign d r b := by
  have hb : -b = b := by
    ext j
    exact CharTwo.neg_eq (b j)
  rw [sub_eq_add_neg, hb, (coordinateSign d r).map_add_eq_mul]

@[simp]
theorem coordinateCharacter_single (r t : Fin d) :
    coordinateCharacter d r (Pi.single t (1 : ZMod 2)) =
      if r = t then -1 else 1 := by
  by_cases h : r = t
  · subst t
    norm_num [coordinateCharacter, coordinateSign, AddChar.zmodChar_apply,
      ZMod.val_one_eq_one_mod]
  · simp [coordinateCharacter, coordinateSign, h]

/-- A coordinate character is nontrivial, as witnessed by its own single bit. -/
theorem coordinateCharacter_ne_zero (r : Fin d) : coordinateCharacter d r ≠ 0 := by
  intro h
  have he := DFunLike.congr_fun h (Pi.single r (1 : ZMod 2))
  simp only [coordinateCharacter_single, AddChar.zero_apply, ite_true] at he
  norm_num at he

/-- Different coordinates give different characters, witnessed by a single bit. -/
theorem coordinateCharacter_injective : Function.Injective (coordinateCharacter d) := by
  intro r t h
  by_contra hrt
  have he := DFunLike.congr_fun h (Pi.single r (1 : ZMod 2))
  simp only [coordinateCharacter_single, ite_eq_right (Ne.symm hrt)] at he
  norm_num at he

end BinaryCoordinates

section AttributeSpectrum

variable {d : ℕ}

/-- The complex-valued spectral kernel is the embedded real logarithm of an
explicit binary attribute product. -/
def attributeLogKernel (s : Fin d → ℝ) (a : Fin d → ZMod 2) : ℂ :=
  (Real.log (∏ r, (1 + s r * coordinateSign d r a)) : ℂ)

/-- The unary displacement kernel is exactly the pairwise sign-coupling
logarithm. This is the bridge to the attribute factors in Appendix D. -/
theorem attributeLogKernel_sub (s : Fin d → ℝ) (a b : Fin d → ZMod 2) :
    attributeLogKernel s (a - b) =
      (Real.log (∏ r, (1 + s r * (coordinateSign d r a * coordinateSign d r b))) : ℂ) := by
  simp only [attributeLogKernel, coordinateSign_sub]

/-- The coupling range places every factor of the unary kernel in the
positive real domain, so its logarithm has its ordinary probabilistic meaning. -/
theorem attributeLogKernel_product_pos (s : Fin d → ℝ) (hs : ∀ r, |s r| < 1)
    (a : Fin d → ZMod 2) : 0 < ∏ r, (1 + s r * coordinateSign d r a) := by
  apply Finset.prod_pos
  intro r _
  exact binary_factor_pos (hs r) (coordinateSign_sq d r a)

/-- The actual logarithmic kernel has only a constant and coordinate characters. -/
theorem attributeLogKernel_expansion (s : Fin d → ℝ) (hs : ∀ r, |s r| < 1)
    (a : Fin d → ZMod 2) :
    attributeLogKernel s a =
      (∑ r, (binaryLogMean (s r) : ℂ)) +
        ∑ r, (binaryLogContrast (s r) : ℂ) * coordinateCharacter d r a := by
  have h := log_attribute_product s (fun r => coordinateSign d r a)
    (fun _ => 1) hs (fun r => coordinateSign_sq d r a) (by intro r; norm_num)
  have hc := congrArg Complex.ofReal h
  simpa [attributeLogKernel] using hc

/-- Every Fourier coefficient of the logarithmic attribute kernel, with exact
normalization for counting measure on the `2^d` binary states. -/
theorem attributeLogKernel_eigenvalue (s : Fin d → ℝ) (hs : ∀ r, |s r| < 1)
    (ψ : AddChar (Fin d → ZMod 2) ℂ) :
    kernelEigenvalue (attributeLogKernel s) ψ =
      (2 : ℂ) ^ d *
        ((if ψ = 0 then ∑ r, (binaryLogMean (s r) : ℂ) else 0) +
          ∑ r, if ψ = coordinateCharacter d r then (binaryLogContrast (s r) : ℂ) else 0) := by
  have hexp : attributeLogKernel s = fun a =>
      (∑ r, (binaryLogMean (s r) : ℂ)) +
        ∑ r, (binaryLogContrast (s r) : ℂ) * coordinateCharacter d r a :=
    funext (attributeLogKernel_expansion s hs)
  rw [hexp, kernelEigenvalue_character_expansion]
  simp

/-- The constant-mode eigenvalue is the sum of logarithmic means times `2^d`. -/
theorem attributeLogKernel_constant_eigenvalue (s : Fin d → ℝ)
    (hs : ∀ r, |s r| < 1) :
    kernelEigenvalue (attributeLogKernel s) 0 =
      (2 : ℂ) ^ d * ∑ r, (binaryLogMean (s r) : ℂ) := by
  rw [attributeLogKernel_eigenvalue s hs]
  simp [Ne.symm (coordinateCharacter_ne_zero d _)]

/-- The eigenvalue of one coordinate is precisely its own contrast times `2^d`.
The injectivity proof discharges possible collisions between coordinate modes. -/
theorem attributeLogKernel_coordinate_eigenvalue (s : Fin d → ℝ)
    (hs : ∀ r, |s r| < 1) (r : Fin d) :
    kernelEigenvalue (attributeLogKernel s) (coordinateCharacter d r) =
      (2 : ℂ) ^ d * (binaryLogContrast (s r) : ℂ) := by
  rw [attributeLogKernel_eigenvalue s hs]
  simp [coordinateCharacter_ne_zero, (coordinateCharacter_injective d).eq_iff]

/-- All character modes outside the constant and coordinate support vanish. -/
theorem attributeLogKernel_other_eigenvalue_zero (s : Fin d → ℝ)
    (hs : ∀ r, |s r| < 1) (ψ : AddChar (Fin d → ZMod 2) ℂ)
    (hψ : ψ ≠ 0) (hout : ∀ r, ψ ≠ coordinateCharacter d r) :
    kernelEigenvalue (attributeLogKernel s) ψ = 0 := by
  rw [attributeLogKernel_eigenvalue s hs]
  simp [hψ, hout]

/-- The sparse coefficient formula is an eigenvector theorem for the actual
logarithmic circulant matrix, not only a formal coefficient identity. -/
theorem attributeLogKernel_mulVec_character (s : Fin d → ℝ)
    (hs : ∀ r, |s r| < 1) (ψ : AddChar (Fin d → ZMod 2) ℂ) :
    circulant (attributeLogKernel s) *ᵥ (ψ : (Fin d → ZMod 2) → ℂ) =
      ((2 : ℂ) ^ d *
        ((if ψ = 0 then ∑ r, (binaryLogMean (s r) : ℂ) else 0) +
          ∑ r, if ψ = coordinateCharacter d r then (binaryLogContrast (s r) : ℂ) else 0)) •
        (ψ : (Fin d → ZMod 2) → ℂ) := by
  rw [circulant_mulVec_character, attributeLogKernel_eigenvalue s hs]

end AttributeSpectrum

end InfoGeometry.LLM.LanguageSymmetry
