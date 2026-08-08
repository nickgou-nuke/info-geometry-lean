/-
Copyright (c) 2026 InfoGeometry Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Contributors.
-/
import InfoGeometry.Canonical.CausalVortexPauliWitness

/-!
# Quadratic-form positivity for the finite Cooper-pair property

`Matrix.PosSemidef` is an ordered-ring notion and therefore is not the right
type for a complex matrix.  This owner records the corresponding Hilbert-space
statement directly: the real part of the complex quadratic form is
nonnegative.
-/

namespace CausalVortex

open Matrix
open InfoGeometry.Physics.ChiralPoincareSouriauBridge

abbrev PauliVector := Fin 2 → ℂ

def QuadraticFormNonnegative (A : M2C) : Prop :=
  ∀ v : PauliVector,
    0 ≤ Complex.re (∑ i : Fin 2, star (v i) * (A.mulVec v) i)

theorem pauli_number_operator_quadratic_form_nonnegative :
    QuadraticFormNonnegative pauliNumberOperator := by
  intro v
  rw [pauli_number_operator_eq_one_add_sigma2]
  simp [Matrix.mulVec, Matrix.add_apply, Matrix.one_apply, σ2,
    Fin.sum_univ_two,
    Complex.mul_re, Complex.conj_re, Complex.conj_im]
  nlinarith [sq_nonneg ((v 0).re + (v 1).im),
    sq_nonneg ((v 0).im - (v 1).re)]

end CausalVortex
