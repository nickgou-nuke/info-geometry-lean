/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.MajoranaQuartic
import InfoGeometry.Algebra.MajoranaClockReencoding
import Mathlib.LinearAlgebra.Eigenspace.Matrix
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic

/-!
# Spectrum of the concrete four-Majorana interaction

The same native `4 × 4` Jordan--Wigner matrices used in the clock re-encoding
give the quartic `diag(-1, 1, 1, -1)`. Its interaction has exactly the spectrum
`{g, -g}` and characteristic polynomial `(X - g)^2 * (X + g)^2`.
For nonzero coupling the two distinct roots each have algebraic multiplicity
two; at zero coupling the polynomial is `X^4`.

These are finite spectral statements for one interaction. They do not prove
a thermodynamic gap, topological protection, or a parafermion condensation.
-/

noncomputable section

namespace InfoGeometry.Quantum.MajoranaQuarticFour

open InfoGeometry.Quantum.MajoranaVacuumWickFour (Mat4C gamma)
open InfoGeometry.Algebra.MajoranaClockReencoding
open InfoGeometry.Algebra.MajoranaQuartic
theorem quartet_diagonal :
    quartet majoranaSystem = Matrix.diagonal ![-1, 1, 1, -1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [quartet, majoranaSystem, gamma, Matrix.mul_apply,
      Fin.sum_univ_four]

/-- The quartet is minus the total parity of its two fermionic sites. -/
theorem quartet_eq_neg_parity :
    quartet majoranaSystem = -(firstParity * secondParity) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [quartet, majoranaSystem, firstParity, secondParity, gamma,
      Matrix.mul_apply, Fin.sum_univ_four]

theorem parity_anticommute_gamma (i : Fin 4) :
    (firstParity * secondParity) * gamma i =
      -(gamma i * (firstParity * secondParity)) := by
  have h := quartet_anticommute_gamma majoranaSystem i
  rw [quartet_eq_neg_parity] at h
  simpa only [majoranaSystem, neg_mul, mul_neg, neg_neg, neg_eq_iff_eq_neg] using h

/-- The finite parity operator is conserved by the actual quartic Hamiltonian. -/
theorem parity_commute_hamiltonian (g : ℂ) :
    Commute (firstParity * secondParity) (hamiltonian majoranaSystem g) :=
  commute_hamiltonian_of_anticommute majoranaSystem
    (firstParity * secondParity) parity_anticommute_gamma g

theorem hamiltonian_diagonal (g : ℂ) :
    hamiltonian majoranaSystem g = Matrix.diagonal ![g, -g, -g, g] := by
  rw [hamiltonian, quartet_diagonal]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- Real couplings give a self-adjoint matrix through the generic quartic theorem. -/
theorem real_hamiltonian_isSelfAdjoint (g : ℝ) :
    IsSelfAdjoint (hamiltonian majoranaSystem (g : ℂ)) := by
  apply hamiltonian_isSelfAdjoint majoranaSystem gamma_isSelfAdjoint
  change star (g : ℂ) = (g : ℂ)
  simp

/-- Both allowed spectral values are present in this concrete four-state model. -/
theorem hamiltonian_spectrum (g : ℂ) :
    spectrum ℂ (hamiltonian majoranaSystem g) = {g, -g} := by
  rw [hamiltonian_diagonal, spectrum_diagonal]
  ext z
  simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨i, hi⟩
    fin_cases i
    · exact Or.inl hi.symm
    · exact Or.inr hi.symm
    · exact Or.inr hi.symm
    · exact Or.inl hi.symm
  · rintro (rfl | rfl)
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩

/-- The native characteristic polynomial records the full four-state spectrum. -/
theorem hamiltonian_charpoly (g : ℂ) :
    Matrix.charpoly (hamiltonian majoranaSystem g) =
      (Polynomial.X - Polynomial.C g) ^ 2 *
        (Polynomial.X + Polynomial.C g) ^ 2 := by
  have hpoly : ∀ a b : Polynomial ℂ, a * b * b * a = a ^ 2 * b ^ 2 := by
    intro a b
    ring
  rw [hamiltonian_diagonal, Matrix.charpoly_diagonal, Fin.prod_univ_four]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons,
    Polynomial.C_neg, sub_neg_eq_add]
  exact hpoly _ _

end InfoGeometry.Quantum.MajoranaQuarticFour
