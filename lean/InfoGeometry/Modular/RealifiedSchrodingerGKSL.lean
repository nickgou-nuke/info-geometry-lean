/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Modular.SchrodingerGKSL
import InfoGeometry.Quantum.Realification

/-!
# Realification of the finite-matrix Schrödinger GKSL generator

The complex matrix algebra is represented faithfully on its underlying real
phase double.  This owner proves the exact generator intertwining formula.
The realified matrices carry the ordinary positive Euclidean adjoint from
`Realification`; no identification with the separate Dirac--Krein form is
made here.
-/

noncomputable section

open Matrix
open scoped BigOperators

namespace InfoGeometry.Modular.RealifiedSchrodingerGKSL

open InfoGeometry.Modular.SchrodingerGKSL
open InfoGeometry.Quantum.Realification

variable {n ι : Type*}

local notation "CMat" => Matrix n n ℂ
local notation "RMat" => Matrix (n ⊕ n) (n ⊕ n) ℝ

/-- Real scalars acting through `ℂ` agree with the real-linear structure of
the phase-double representation. -/
lemma realify_ofReal_smul (r : ℝ) (A : CMat) :
    realify ((r : ℂ) • A) = r • realify A := by
  ext i j
  cases i <;> cases j <;>
    simp [InfoGeometry.Quantum.Realification.realify,
      Complex.mul_re, Complex.mul_im]

variable [Fintype n] [Fintype ι]

/-- The Lindblad jump term on the real phase double, using the ordinary
transpose, which is exactly the realification of complex conjugate transpose.
-/
def realifiedDissipatorTerm (V X : CMat) : RMat :=
  realify V * realify X * (realify V)ᵀ -
    (1 / 2 : ℝ) •
      ((realify V)ᵀ * realify V * realify X +
        realify X * (realify V)ᵀ * realify V)

/-- Realification transports each noncommutative Lindblad jump term, in its
actual multiplication order. -/
theorem realify_schrodingerDissipatorTerm (V X : CMat) :
    realify (schrodingerDissipatorTerm V X) = realifiedDissipatorTerm V X := by
  dsimp [schrodingerDissipatorTerm, realifiedDissipatorTerm]
  have hhalf : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by norm_num
  rw [realify_sub, realify_mul, realify_mul, Matrix.star_eq_conjTranspose,
    realify_star, Matrix.conjTranspose_eq_transpose_of_trivial]
  rw [hhalf, realify_ofReal_smul]
  simp only [realify_add, realify_mul, realify_star,
    Matrix.conjTranspose_eq_transpose_of_trivial]

variable [DecidableEq n]

/-- Multiplication by the internal real phase axis represents multiplication
by `Complex.I` on the complex matrix algebra. -/
theorem realify_I_smul (A : CMat) :
    realify ((Complex.I : ℂ) • A) = internalJ * realify A := by
  have hmul : ((Complex.I : ℂ) • (1 : CMat)) * A =
      (Complex.I : ℂ) • A := by
    calc
      ((Complex.I : ℂ) • (1 : CMat)) * A =
          (Complex.I : ℂ) • ((1 : CMat) * A) := by rw [smul_mul_assoc]
      _ = (Complex.I : ℂ) • A := by simp
  calc
    realify ((Complex.I : ℂ) • A) =
        realify (((Complex.I : ℂ) • (1 : CMat)) * A) := by rw [hmul]
    _ = realify ((Complex.I : ℂ) • (1 : CMat)) * realify A := realify_mul _ _
    _ = internalJ * realify A := by rw [internalJ_eq_realify]

/-- The Hamiltonian commutator term after realification. -/
def realifiedHamiltonianTerm (H X : CMat) : RMat :=
  -(internalJ * realify (H * X - X * H))

/-- The real matrix expression for the full finite-dimensional GKSL
generator. -/
def realifiedSchrodingerLindbladian (H : CMat) (V : ι → CMat) (X : CMat) : RMat :=
  realifiedHamiltonianTerm H X + ∑ k, realifiedDissipatorTerm (V k) X

/-- Realification transports the coherent Hamiltonian term exactly; the
complex factor `-i` becomes left multiplication by `-internalJ`. -/
theorem realify_hamiltonianTerm (H X : CMat) :
    realify (hamiltonianTerm H X) = realifiedHamiltonianTerm H X := by
  dsimp [hamiltonianTerm, realifiedHamiltonianTerm]
  have hnegI : (-Complex.I : ℂ) • (H * X - X * H) =
      -((Complex.I : ℂ) • (H * X - X * H)) := by
    simp
  rw [hnegI, realify_neg, realify_I_smul]

/-- The complete Schrödinger GKSL generator intertwines with the explicit
real phase-double generator for every finite matrix size and every finite
family of jumps. -/
theorem realify_schrodingerLindbladian (H X : CMat) (V : ι → CMat) :
    realify (schrodingerLindbladian H V X) =
      realifiedSchrodingerLindbladian H V X := by
  simp [schrodingerLindbladian, schrodingerDissipator,
    realifiedSchrodingerLindbladian, realify_hamiltonianTerm,
    realify_schrodingerDissipatorTerm]

end InfoGeometry.Modular.RealifiedSchrodingerGKSL

end noncomputable section
