/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.SochichiuNambu3AlgebraObstruction
import InfoGeometry.Algebra.AssociativeNambuOperators
import InfoGeometry.OperatorAlgebra.PeirceSpine.AlternatingCornerTriple

/-!
# Canonical Bridge Between Sochichiu's Nambu-Lie Obstruction and the Peirce Alternating Cubic Spine

Connects `SochichiuNambu3AlgebraObstruction.nambu3` directly with
`PeirceSpine.alternatingProduct3` and `PeirceSpine.cyclicCommutatorTriple`:
1. Exact ring-level equality `nambu3 = alternatingProduct3 = cyclicCommutatorTriple`,
2. Transport of Sochichiu's alternating trace vanishing and Euclidean `A₄` finite Hermitian
   matrix no-go theorem directly onto `PeirceSpine.alternatingProduct3`,
3. Transport of `AssociativeNambuOperators` square-zero sandwich annihilation and Peirce
   positive-corner `qgtPlus` closure onto `nambu3`,
4. Sharpness contrast on `PeirceSpine.alternatingProduct3` via the `2 × 2` Hermitian Lorentzian
   `A_{3,1}` Pauli witness.
-/

set_option autoImplicit false

noncomputable section

open Matrix Complex
open InfoGeometry.Algebra.SochichiuNambu3AlgebraObstruction
open InfoGeometry.Algebra.AssociativeNambuOperators
open InfoGeometry.OperatorAlgebra
open InfoGeometry.OperatorAlgebra.PeirceSpine

namespace InfoGeometry.Algebra.SochichiuPeirceNambuBridge

/-- Explicit matrix non-commutativity witness for `M₂(ℂ)` reused from the Pauli carrier. -/
theorem exists_noncomm_mat2_complex :
    ∃ A B : Matrix (Fin 2) (Fin 2) ℂ, A * B ≠ B * A :=
  ⟨pauli1, pauli2, pauli1_mul_pauli2_ne_comm⟩

/-- Sochichiu's associative Nambu 3-commutator coincides definitionally with the Peirce spine's
degree-three alternating standard polynomial `alternatingProduct3`. -/
theorem nambu3_eq_alternatingProduct3 {A : Type*} [Ring A] (X Y Z : A) :
    nambu3 X Y Z = alternatingProduct3 X Y Z :=
  rfl

/-- Sochichiu's `nambu3` equals the Peirce spine's `cyclicCommutatorTriple`. -/
theorem nambu3_eq_cyclicCommutatorTriple {A : Type*} [Ring A] (X Y Z : A) :
    nambu3 X Y Z = cyclicCommutatorTriple X Y Z := by
  rw [nambu3_eq_alternatingProduct3, cyclicCommutatorTriple_eq_alternatingProduct3]

/-- Alternating trace identity transported onto `PeirceSpine.alternatingProduct3`:
`∑_cyc Tr(X_{σ(4)} * alternatingProduct3 X_{σ(1)} X_{σ(2)} X_{σ(3)}) = 0`. -/
theorem peirce_alternatingProduct3_trace_zero {R : Type*} [CommRing R] {n : ℕ}
    (T₁ T₂ T₃ T₄ : Matrix (Fin n) (Fin n) R) :
    Matrix.trace (T₄ * alternatingProduct3 T₁ T₂ T₃) -
      Matrix.trace (T₁ * alternatingProduct3 T₂ T₃ T₄) +
      Matrix.trace (T₂ * alternatingProduct3 T₃ T₄ T₁) -
      Matrix.trace (T₃ * alternatingProduct3 T₄ T₁ T₂) = 0 :=
  trace_alternating_nambu3_eq_zero T₁ T₂ T₃ T₄

/-- Square-zero sandwich annihilation transported onto Sochichiu's `nambu3`. -/
theorem nambu3_sandwich_range_zero {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
    (n : A) (hn : n * n = 0) {a b c : A}
    (ha : a ∈ LinearMap.range (LinearMap.mulLeftRight R (n, n)))
    (hb : b ∈ LinearMap.range (LinearMap.mulLeftRight R (n, n)))
    (hc : c ∈ LinearMap.range (LinearMap.mulLeftRight R (n, n))) :
    nambu3 a b c = 0 := by
  rw [nambu3_eq_alternatingProduct3]
  exact alternatingProduct3_sandwich_range n hn ha hb hc

/-- Three positive-sheet Peirce transition products remain supported inside the positive Peirce
corner under Sochichiu's `nambu3`. -/
theorem nambu3_peirce_transition_corner_support {B : Type*} [Ring B] {P : B} (hP : P * P = P)
    (A₁ C₁ A₂ C₂ A₃ C₃ : B) :
    P * nambu3 (qgtPlus P A₁ C₁) (qgtPlus P A₂ C₂) (qgtPlus P A₃ C₃) * P =
      nambu3 (qgtPlus P A₁ C₁) (qgtPlus P A₂ C₂) (qgtPlus P A₃ C₃) := by
  rw [nambu3_eq_cyclicCommutatorTriple]
  exact peirce_alternating_transition_cubic_support hP A₁ C₁ A₂ C₂ A₃ C₃

/-- Sochichiu's finite Hermitian no-go theorem for Euclidean `A₄`, stated natively in terms of
`PeirceSpine.alternatingProduct3`: any four `n × n` Hermitian matrices satisfying the `A₄` relations
under `alternatingProduct3` must all be zero. -/
theorem peirce_alternatingProduct3_euclidean_A4_hermitian_trivial {n : ℕ}
    (T₁ T₂ T₃ T₄ : Matrix (Fin n) (Fin n) ℂ)
    (hH₁ : T₁.IsHermitian) (hH₂ : T₂.IsHermitian) (hH₃ : T₃.IsHermitian) (hH₄ : T₄.IsHermitian)
    (h123 : alternatingProduct3 T₁ T₂ T₃ = I • T₄)
    (h234 : alternatingProduct3 T₂ T₃ T₄ = (-I) • T₁)
    (h341 : alternatingProduct3 T₃ T₄ T₁ = I • T₂)
    (h412 : alternatingProduct3 T₄ T₁ T₂ = (-I) • T₃) :
    T₁ = 0 ∧ T₂ = 0 ∧ T₃ = 0 ∧ T₄ = 0 :=
  euclidean_A4_hermitian_matrix_rep_trivial T₁ T₂ T₃ T₄ hH₁ hH₂ hH₃ hH₄ h123 h234 h341 h412

/-- Sharpness contrast in the Peirce operator spine: the explicit `2 × 2` Hermitian Pauli tuple
`(lorT1, lorT2, lorT3, lorT4)` gives a nonzero Lorentzian `A_{3,1}` realization of
`PeirceSpine.alternatingProduct3`. -/
theorem peirce_alternatingProduct3_lorentzian_A31_witness :
    lorT1.IsHermitian ∧ lorT2.IsHermitian ∧ lorT3.IsHermitian ∧ lorT4.IsHermitian ∧
    lorT1 ≠ 0 ∧ lorT2 ≠ 0 ∧ lorT3 ≠ 0 ∧ lorT4 ≠ 0 ∧
    alternatingProduct3 lorT1 lorT2 lorT3 = I • lorT4 ∧
    alternatingProduct3 lorT4 lorT1 lorT2 = I • lorT3 ∧
    alternatingProduct3 lorT4 lorT2 lorT3 = I • lorT1 ∧
    alternatingProduct3 lorT4 lorT3 lorT1 = I • lorT2 :=
  lorentzian_A31_hermitian_nontrivial_witness

end InfoGeometry.Algebra.SochichiuPeirceNambuBridge
