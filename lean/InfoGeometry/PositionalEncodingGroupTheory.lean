/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib
import InfoGeometry.LLM.PositionalEncodingRepresentation
import InfoGeometry.OperatorAlgebra.ComplexBoundedOperators.JordanChevalleyBridge

/-!
# Positional encodings as representations of translation

Compact, honest replacement for the earlier speculative file.  It keeps the
namespace and the basic carriers, proves the translation-covariance group law,
and reads the generator decomposition off the repository's packaged
Jordan–Chevalley bridge.  The differentiable exponential classification is
already owner-backed in `InfoGeometry.LLM.PositionalEncodingRepresentation`
(`eval_eq_exponential_of_hasDerivAt_zero`) and is not reproved here.

Nothing in this file asserts that a specific transformer implementation uses
these carriers.
-/

noncomputable section

namespace InfoGeometry.PositionalEncodingGroupTheory

open InfoGeometry.OperatorAlgebra.ComplexBoundedOperators.JordanChevalleyBridge

abbrev EncMatrix (d : ℕ) := Matrix (Fin d) (Fin d) ℝ

/-- Query and key vectors as continuous-time functions. -/
abbrev QueryVector (d : ℕ) := ℝ → Matrix (Fin d) (Fin 1) ℝ
abbrev KeyVector (d : ℕ) := ℝ → Matrix (Fin d) (Fin 1) ℝ

/-- Time-dependent linear modification of queries and keys. -/
structure PositionalEncoding (d : ℕ) where
  F : ℝ → EncMatrix d
  G : ℝ → EncMatrix d
  hF_cont : Continuous F
  hG_cont : Continuous G

/-- Translation-invariant encoding: `F(t)ᵀ G(s)` depends only on `t - s`. -/
structure TranslationInvariantEncoding (d : ℕ) extends PositionalEncoding d where
  A : ℝ → EncMatrix d
  hA_cont : Continuous A
  h_translation_invariance : ∀ t s : ℝ, (F t).transpose * G s = A (t - s)
  h_A_zero : A (0 : ℝ) = 1

/-- The one-parameter-group law `A(s) A(t) = A(s + t)`. -/
def OneParameterGroup (A : ℝ → EncMatrix d) : Prop :=
  ∀ s t : ℝ, A s * A t = A (s + t)

/-- The generator `A'(0)`. -/
def Generator (A : ℝ → EncMatrix d) (_hA : DifferentiableAt ℝ A 0) : EncMatrix d :=
  deriv A 0

/-- Translation covariance forces the one-parameter-group law. -/
theorem translation_invariance_implies_one_parameter_group
    (enc : TranslationInvariantEncoding d) : OneParameterGroup enc.A := by
  intro s t
  symm
  have ht : (enc.F t).transpose * enc.G t = 1 := by
    have h := enc.h_translation_invariance t t
    simpa [sub_self, enc.h_A_zero] using h
  have ht_left : enc.G t * (enc.F t).transpose = 1 :=
    mul_eq_one_comm.mp ht
  have hG0 : enc.G (0 : ℝ) = enc.G t * enc.A t := by
    calc
      enc.G 0 = 1 * enc.G 0 := by simp
      _ = (enc.G t * (enc.F t).transpose) * enc.G 0 := by rw [ht_left]
      _ = enc.G t * ((enc.F t).transpose * enc.G 0) := by rw [Matrix.mul_assoc]
      _ = enc.G t * enc.A t := by
        have h := enc.h_translation_invariance t (0 : ℝ)
        simpa [sub_zero] using congrArg (fun M => enc.G t * M) h
  calc
    enc.A (s + t) = (enc.F (s + t)).transpose * enc.G 0 := by
      have h := enc.h_translation_invariance (s + t) (0 : ℝ)
      simpa [sub_zero] using h.symm
    _ = (enc.F (s + t)).transpose * (enc.G t * enc.A t) := by rw [hG0]
    _ = ((enc.F (s + t)).transpose * enc.G t) * enc.A t := by rw [Matrix.mul_assoc]
    _ = enc.A s * enc.A t := by
      have h := enc.h_translation_invariance (s + t) t
      have hs : (s + t) - t = s := by ring
      simpa [hs] using congrArg (fun M => M * enc.A t) h

/-- Generator decomposition read off the existing Jordan–Chevalley bridge.
The semisimple and nilpotent laws are stated on the associated endomorphisms,
the carrier on which the repository's owner proves them. -/
theorem generator_decomposition (X : EncMatrix d) :
    ∃ Xs Xn : EncMatrix d,
      X = Xs + Xn ∧ Xs * Xn = Xn * Xs ∧
        Module.End.IsSemisimple (Matrix.toLinAlgEquiv' Xs) ∧
          IsNilpotent (Matrix.toLinAlgEquiv' Xn) := by
  let em : EncMatrix d ≃ₐ[ℝ] Module.End ℝ (Fin d → ℝ) := Matrix.toLinAlgEquiv'
  let im : Module.End ℝ (Fin d → ℝ) ≃ₐ[ℝ] EncMatrix d := em.symm
  obtain ⟨B, hsB, hnB, hcommB, hs_mem, hn_mem, hsumB⟩ :=
    JordanChevalleySplit.exists_split (f := em X)
  refine ⟨im B.semisimple, im B.nilpotent, ?_, ?_, ?_, ?_⟩
  · apply em.injective
    simpa [em, im, add_comm] using hsumB
  · apply em.injective
    simp [em, im]
    exact hcommB.eq
  · simpa [em, im, IsSemisimpleEnd] using hsB
  · simpa [em, im, IsNilpotentEnd] using hnB

end InfoGeometry.PositionalEncodingGroupTheory
