/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Quantum.TwoQubitPauliGeometry
import Mathlib.Algebra.Lie.Classical
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# A two-qubit basis of the full matrix algebra and its trace-zero Lie algebra

The trace pairing proves that the sixteen signed words are a basis over a
characteristic-zero field. The fifteen nonzero binary labels span exactly
Mathlib's special linear Lie algebra. Over the reals the trace-zero part is the
split real Lie algebra `sl₄(ℝ)`; no compact or quaternionic real form is claimed.
-/

namespace InfoGeometry.Quantum.TwoQubitPauli

open Matrix
open scoped Kronecker BigOperators
open Projective.BinarySymplectic BinaryWeyl

variable {R : Type*} [CommRing R]

/-- Orthogonality follows from the one-factor trace pairing and native Kronecker multiplication. -/
theorem pauli_trace_pair (v w : Label) :
    Matrix.trace ((pauli (R := R) v)ᵀ * pauli w) = if v = w then 4 else 0 := by
  have ht : (pauli (R := R) v)ᵀ =
      (word v.1.1 v.1.2)ᵀ ⊗ₖ (word v.2.1 v.2.2)ᵀ := rfl
  rw [ht, pauli, ← Matrix.mul_kronecker_mul, Matrix.trace_kronecker,
    word_trace_pair, word_trace_pair]
  by_cases h₁ : v.1 = w.1 <;> by_cases h₂ : v.2 = w.2 <;>
    norm_num [Prod.ext_iff, h₁, h₂]

/-- Every nonidentity word has trace zero. -/
theorem pauli_trace (v : Label) :
    Matrix.trace (pauli (R := R) v) = if v = 0 then 4 else 0 := by
  simpa [eq_comm] using pauli_trace_pair (R := R) 0 v

variable {K : Type*} [Field K] [CharZero K]

/-- The trace pairing detects every coefficient of a linear relation. -/
theorem pauli_linearIndependent : LinearIndependent K (pauli (R := K)) := by
  rw [Fintype.linearIndependent_iff]
  intro c h v
  have ht := congrArg (fun A : Operator K => Matrix.trace ((pauli v)ᵀ * A)) h
  simp [Matrix.mul_sum, Matrix.trace_sum, Matrix.trace_smul,
    pauli_trace_pair, mul_ite, smul_eq_mul] at ht
  exact ht

/-- The sixteen words constitute a native basis of the entire four-by-four matrix algebra. -/
noncomputable def pauliBasis : Module.Basis Label K (Operator K) :=
  basisOfLinearIndependentOfCardEqFinrank pauli_linearIndependent (by
    simp [Operator, Label, Bit, Module.finrank_matrix])

@[simp] theorem pauliBasis_apply (v : Label) :
    pauliBasis (K := K) v = pauli v := by
  simp [pauliBasis]

/-- The identity coefficient is exactly one quarter of the ordinary matrix trace. -/
theorem trace_eq_identity_coefficient (A : Operator K) :
    Matrix.trace A = (pauliBasis.repr A) 0 * 4 := by
  have ht := congrArg Matrix.trace ((pauliBasis (K := K)).sum_repr A)
  simpa [Matrix.trace_sum, Matrix.trace_smul, pauli_trace, smul_eq_mul,
    mul_ite] using ht.symm

theorem trace_zero_iff_identity_coefficient_zero (A : Operator K) :
    Matrix.trace A = 0 ↔ (pauliBasis.repr A) 0 = 0 := by
  rw [trace_eq_identity_coefficient]
  simp

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The fifteen nonzero labels span exactly the native special linear Lie algebra. -/
theorem nonzero_pauli_span_eq_sl :
    Submodule.span K (pauli (R := K) '' {v : Label | v ≠ 0}) =
      (LieAlgebra.SpecialLinear.sl (ZMod 2 × ZMod 2) K).toSubmodule := by
  ext A
  change A ∈ Submodule.span K (pauli (R := K) '' {v : Label | v ≠ 0}) ↔
    Matrix.trace A = 0
  have hb : pauli (R := K) = pauliBasis (K := K) := by
    funext v
    exact (pauliBasis_apply v).symm
  rw [hb, Module.Basis.mem_span_image, trace_zero_iff_identity_coefficient_zero]
  simp only [Set.subset_def, Finset.mem_coe, Finsupp.mem_support_iff, Set.mem_ofPred_eq]
  constructor
  · intro h
    by_contra hn
    exact h 0 hn rfl
  · intro h v hv hv0
    subst v
    exact hv h

theorem nonzero_pauli_span_finrank :
    Module.finrank K (Submodule.span K
      (pauli (R := K) '' {v : Label | v ≠ 0})) = 15 := by
  rw [Set.image_eq_range]
  have hli : LinearIndependent K
      (fun v : {v : Label // v ≠ 0} => pauli (R := K) v.1) :=
    pauli_linearIndependent.comp _ Subtype.val_injective
  exact (finrank_span_eq_card hli).trans (by decide)

end InfoGeometry.Quantum.TwoQubitPauli
