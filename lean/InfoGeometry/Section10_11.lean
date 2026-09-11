import Mathlib.Data.Matrix.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Sections 10-11: Curvature Antisymmetry & Bianchi — Lean 4

10: F_{μν} = -F_{νμ} — commutator antisymmetry
11: First Bianchi = Jacobi identity for commutator bracket
-/

noncomputable section

namespace Section10_11

open Matrix

/-- Commutator antisymmetry: [A,B] = -[B,A] always. -/
theorem commutator_antisymm (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    A*B - B*A = -(B*A - A*B) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- F_{μν} = -F_{νμ} — curvature is antisymmetric. -/
theorem curvature_antisymm (omega_mu omega_nu : Matrix (Fin 2) (Fin 2) ℂ) :
    (omega_mu*omega_nu - omega_nu*omega_mu) = -(omega_nu*omega_mu - omega_mu*omega_nu) :=
  commutator_antisymm omega_mu omega_nu

/-- Jacobi identity: [A,[B,C]] + [B,[C,A]] + [C,[A,B]] = 0. -/
theorem jacobi_identity (A B C : Matrix (Fin 2) (Fin 2) ℂ) :
    A*(B*C - C*B) - (B*C - C*B)*A +
    B*(C*A - A*C) - (C*A - A*C)*B +
    C*(A*B - B*A) - (A*B - B*A)*C = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- First Bianchi (algebraic): the cyclic commutator sum vanishes by Jacobi. -/
theorem first_bianchi_jacobi (A B C : Matrix (Fin 2) (Fin 2) ℂ) :
    A*(B*C - C*B) - (B*C - C*B)*A +
    B*(C*A - A*C) - (C*A - A*C)*B +
    C*(A*B - B*A) - (A*B - B*A)*C = 0 :=
  jacobi_identity A B C

end Section10_11
