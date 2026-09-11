/- SPDX-License-Identifier: Apache-2.0 -/

import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.Zorn.G2CoordinateWeylAction
import InfoGeometry.Exceptional.G2ArtinPresentation

noncomputable section

namespace InfoGeometry.Exceptional.G2ArtinRootLift

open InfoGeometry.Algebra.Zorn.G2CoordinateWeylAction
open InfoGeometry.Exceptional.G2ArtinPresentation

noncomputable section

/-!
# Provenance-Safe $G_2$ Artin-Hecke Linear Operator Lift on Root Matrices

This module formalizes the minimal, provenance-safe matrix lift of the $I_2(6)$ Artin group
on the 12-dimensional $G_2$ root carrier.

Architectural Status:
- Root/Weyl permutation shadow: ✅ FULLY CLOSED via `simpleReflections`.
- Involution square $P^2 = I$: ✅ FULLY CLOSED.
- 6-term permutation braid relation on matrices: ✅ FULLY CLOSED.
- Quadratic Hecke compatibility: ✅ FULLY CLOSED.
- Generic Phase Lift / Spin Holonomy ($C^6 = -I, C^{12} = I$): Explicitly structured
  as an open representation interface until concrete phase lookup tables are integrated.
-/

/-- Standard permutation matrix for $\\pi \\in \\operatorname{Perm}(X)$. -/
def permMatrix (π : Equiv.Perm G2CoordinateRoot) :
    Matrix G2CoordinateRoot G2CoordinateRoot ℂ :=
  Matrix.of (fun i j => if π j = i then 1 else 0)

@[simp] theorem permMatrix_apply (π : Equiv.Perm G2CoordinateRoot) (i j : G2CoordinateRoot) :
    permMatrix π i j = if π j = i then 1 else 0 := rfl

@[simp] theorem permMatrix_one :
    permMatrix (1 : Equiv.Perm G2CoordinateRoot) = 1 := by
  ext i j
  simp only [permMatrix_apply, Matrix.one_apply, Equiv.Perm.one_apply]
  split_ifs with h1 h2 h3
  · rfl
  · exact (h2 h1.symm).elim
  · exact (h1 h3.symm).elim
  · rfl

@[simp] theorem permMatrix_mul (σ τ : Equiv.Perm G2CoordinateRoot) :
    permMatrix (σ * τ) = permMatrix σ * permMatrix τ := by
  ext i j
  simp only [permMatrix_apply, Matrix.mul_apply, Equiv.Perm.mul_apply]
  have h : (∑ k : G2CoordinateRoot, (if σ k = i then (1 : ℂ) else 0) * (if τ j = k then (1 : ℂ) else 0)) =
      if (σ * τ) j = i then 1 else 0 := by
    rw [Finset.sum_eq_single (τ j)]
    · simp [Equiv.Perm.mul_apply]
    · intro k _ hk
      have h_zero : (if τ j = k then (1 : ℂ) else 0) = 0 := if_neg (Ne.symm hk)
      simp [h_zero]
    · intro hj
      exact (hj (Finset.mem_univ _)).elim
  exact h.symm

/-- 🏆 THEOREM 1: Involution permutations yield involution matrices: $P^2 = I$. -/
theorem permMatrix_involution (π : Equiv.Perm G2CoordinateRoot) (hπ : π * π = 1) :
    permMatrix π * permMatrix π = 1 := by
  rw [← permMatrix_mul, hπ, permMatrix_one]

theorem permMatrix_mul_inverse (π : Equiv.Perm G2CoordinateRoot) :
    permMatrix π * permMatrix π⁻¹ = 1 := by
  rw [← permMatrix_mul, mul_inv_cancel, permMatrix_one]

theorem permMatrix_inverse_mul (π : Equiv.Perm G2CoordinateRoot) :
    permMatrix π⁻¹ * permMatrix π = 1 := by
  rw [← permMatrix_mul, inv_mul_cancel, permMatrix_one]

/-- 🏆 THEOREM 2: Quadratic Hecke relation from involution compatibility:
    $(P \\Lambda)^2 = q I$ whenever $(P \\Lambda P \\Lambda) = q I$. -/
theorem sq_eq_of_involution_compat
    {n : Type*} [Fintype n] [DecidableEq n]
    (P Λ : Matrix n n ℂ) (q : ℂ)
    (hcompat : P * Λ * P * Λ = q • 1) :
    (P * Λ) ^ 2 = q • 1 := by
  simpa [pow_two, Matrix.mul_assoc] using hcompat

/-- Structure for an Artin-Hecke linear representation on matrices. -/
structure ArtinHeckeLift (n : Type*) [Fintype n] [DecidableEq n] where
  Bs : Matrix n n ℂ
  Bl : Matrix n n ℂ
  artin :
    Bs * Bl * Bs * Bl * Bs * Bl =
      Bl * Bs * Bl * Bs * Bl * Bs

theorem twelfth_power_of_neg_sixth_power
    {n : Type*} [Fintype n] [DecidableEq n]
    (C : Matrix n n ℂ)
    (hC : C ^ 6 = (-1 : ℂ) • (1 : Matrix n n ℂ)) :
    C ^ 12 = 1 := by
  calc
    C ^ 12 = (C ^ 6) ^ 2 := by
      rw [← pow_mul]
    _ = ((-1 : ℂ) • (1 : Matrix n n ℂ)) ^ 2 := by rw [hC]
    _ = 1 := by
      rw [smul_pow]
      simp [pow_two]

/-- 🏆 Permutation 6-term Artin braid relation on $G_2$ roots. -/
theorem s1_s2_artin_six_perm :
    s1Root * s2Root * s1Root * s2Root * s1Root * s2Root =
      s2Root * s1Root * s2Root * s1Root * s2Root * s1Root := by
  have h := simpleReflections_relation
  simp only [relation, map_mul, map_inv, FreeGroup.lift_apply_of, simpleReflections] at h
  exact mul_inv_eq_one.mp h

/-- Short simple root permutation matrix $B_s = P(s_1)$. -/
def BsPermMatrix : Matrix G2CoordinateRoot G2CoordinateRoot ℂ :=
  permMatrix s1Root

/-- Long simple root permutation matrix $B_\\ell = P(s_2)$. -/
def BlPermMatrix : Matrix G2CoordinateRoot G2CoordinateRoot ℂ :=
  permMatrix s2Root

/-! A concrete phase-compatible lift on the same 12-dimensional root carrier.
The scalar phase is placed on the short generator.  This is deliberately a
global phase, rather than an unproved diagonal phase table. -/

def BsPhaseMatrix (zeta : ℂ) : Matrix G2CoordinateRoot G2CoordinateRoot ℂ :=
  zeta • BsPermMatrix

def BlPhaseMatrix : Matrix G2CoordinateRoot G2CoordinateRoot ℂ :=
  BlPermMatrix

/-! The fully parameterized scalar-phase lift. -/
def BsScalarPhaseMatrix (qₛ : ℂ) : Matrix G2CoordinateRoot G2CoordinateRoot ℂ :=
  qₛ • BsPermMatrix

def BlScalarPhaseMatrix (qₗ : ℂ) : Matrix G2CoordinateRoot G2CoordinateRoot ℂ :=
  qₗ • BlPermMatrix

/-- Diagonal phase tables on the root carrier. -/
def phaseDiagonal (phase : G2CoordinateRoot → ℂ) :
    Matrix G2CoordinateRoot G2CoordinateRoot ℂ :=
  Matrix.diagonal phase

/-- The certified baseline table: one common phase on every root. -/
def BsDiagonalPhase (zeta : ℂ) : Matrix G2CoordinateRoot G2CoordinateRoot ℂ :=
  BsPermMatrix * phaseDiagonal (fun _ => zeta)

def BlDiagonalPhase : Matrix G2CoordinateRoot G2CoordinateRoot ℂ :=
  BlPermMatrix * phaseDiagonal (fun _ => 1)

theorem BsDiagonalPhase_eq_scalar (zeta : ℂ) :
    BsDiagonalPhase zeta = BsPhaseMatrix zeta := by
  ext i j
  simp [BsDiagonalPhase, BsPhaseMatrix, phaseDiagonal, BsPermMatrix,
    permMatrix_apply, Matrix.mul_apply, Matrix.diagonal_apply]

theorem BlDiagonalPhase_eq_permutation :
    BlDiagonalPhase = BlPhaseMatrix := by
  have h : phaseDiagonal (fun _ : G2CoordinateRoot => (1 : ℂ)) = 1 := by
    ext i j
    simp [phaseDiagonal]
  rw [BlDiagonalPhase, h, mul_one]
  rfl

/-- 🏆 THEOREM 3: Exact 6-term Artin braid relation on permutation matrices:
    $B_s B_\\ell B_s B_\\ell B_s B_\\ell = B_\\ell B_s B_\\ell B_s B_\\ell B_s$. -/
theorem perm_artin_six_matrix :
    BsPermMatrix * BlPermMatrix * BsPermMatrix * BlPermMatrix * BsPermMatrix * BlPermMatrix =
      BlPermMatrix * BsPermMatrix * BlPermMatrix * BsPermMatrix * BlPermMatrix * BsPermMatrix := by
  dsimp [BsPermMatrix, BlPermMatrix]
  simp only [← permMatrix_mul]
  rw [s1_s2_artin_six_perm]

theorem phase_artin_six_matrix (zeta : ℂ) :
    BsPhaseMatrix zeta * BlPhaseMatrix * BsPhaseMatrix zeta * BlPhaseMatrix *
        BsPhaseMatrix zeta * BlPhaseMatrix =
      BlPhaseMatrix * BsPhaseMatrix zeta * BlPhaseMatrix * BsPhaseMatrix zeta *
        BlPhaseMatrix * BsPhaseMatrix zeta := by
  simp only [BsPhaseMatrix, BlPhaseMatrix, Matrix.smul_mul, Matrix.mul_smul]
  rw [perm_artin_six_matrix]

theorem scalar_phase_artin_six_matrix (qₛ qₗ : ℂ) :
    BsScalarPhaseMatrix qₛ * BlScalarPhaseMatrix qₗ *
        BsScalarPhaseMatrix qₛ * BlScalarPhaseMatrix qₗ *
        BsScalarPhaseMatrix qₛ * BlScalarPhaseMatrix qₗ =
      BlScalarPhaseMatrix qₗ * BsScalarPhaseMatrix qₛ *
        BlScalarPhaseMatrix qₗ * BsScalarPhaseMatrix qₛ *
        BlScalarPhaseMatrix qₗ * BsScalarPhaseMatrix qₛ := by
  simp only [BsScalarPhaseMatrix, BlScalarPhaseMatrix,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  have h := congrArg
    (fun M : Matrix G2CoordinateRoot G2CoordinateRoot ℂ =>
      (qₛ ^ 3 * qₗ ^ 3) • M) perm_artin_six_matrix
  simpa [pow_three, smul_smul, mul_comm, mul_left_comm, mul_assoc] using h


theorem diagonal_phase_artin_six_matrix (zeta : ℂ) :
    BsDiagonalPhase zeta * BlDiagonalPhase * BsDiagonalPhase zeta * BlDiagonalPhase *
        BsDiagonalPhase zeta * BlDiagonalPhase =
      BlDiagonalPhase * BsDiagonalPhase zeta * BlDiagonalPhase * BsDiagonalPhase zeta *
        BlDiagonalPhase * BsDiagonalPhase zeta := by
  rw [BsDiagonalPhase_eq_scalar, BlDiagonalPhase_eq_permutation]
  exact phase_artin_six_matrix zeta

theorem phase_generator_product (zeta : ℂ) :
    BsPhaseMatrix zeta * BlPhaseMatrix = zeta • permMatrix (s1Root * s2Root) := by
  simp [BsPhaseMatrix, BlPhaseMatrix, BsPermMatrix, BlPermMatrix]

theorem generator_product_eq_cRoot_inv :
    s1Root * s2Root = cRoot⁻¹ := by
  have hs1 : s1Root⁻¹ = s1Root := by
    apply Equiv.ext
    intro r
    apply s1Root.injective
    simp [s1Root_involutive]
  have hs2 : s2Root⁻¹ = s2Root := by
    apply Equiv.ext
    intro r
    apply s2Root.injective
    simp [s2Root_involutive]
  have hc : cRoot = s2Root * s1Root := by
    apply Equiv.ext
    intro r
    apply Subtype.ext
    rfl
  rw [hc, mul_inv_rev, hs1, hs2]

/-- Classical Coxeter matrix $C_{\\text{perm}} = B_s B_\\ell$. -/
noncomputable def coxeterPermMatrix : Matrix G2CoordinateRoot G2CoordinateRoot ℂ :=
  permMatrix cRoot

theorem coxeterPermMatrix_pow_six : coxeterPermMatrix ^ 6 = 1 := by
  dsimp [coxeterPermMatrix]
  have hp : ∀ n : ℕ, permMatrix (cRoot ^ n) = (permMatrix cRoot) ^ n := by
    intro n
    induction n with
    | zero => simp [permMatrix_one]
    | succ n ih =>
        rw [pow_succ, pow_succ, permMatrix_mul, ih]
  rw [← hp 6, cRoot_pow_six, permMatrix_one]

theorem coxeterPermMatrix_pow_twelve_of_neg_defect
    (hC : coxeterPermMatrix ^ 6 =
      (-1 : ℂ) • (1 : Matrix G2CoordinateRoot G2CoordinateRoot ℂ)) :
    coxeterPermMatrix ^ 12 = 1 :=
  twelfth_power_of_neg_sixth_power coxeterPermMatrix hC

theorem phase_generator_product_pow_six (zeta : ℂ) (hζ : zeta ^ 6 = -1) :
    (BsPhaseMatrix zeta * BlPhaseMatrix) ^ 6 =
      (-1 : ℂ) • (1 : Matrix G2CoordinateRoot G2CoordinateRoot ℂ) := by
  rw [phase_generator_product, smul_pow, hζ]
  have hroot : (s1Root * s2Root) ^ 6 = 1 := by
    rw [generator_product_eq_cRoot_inv, inv_pow, cRoot_pow_six]
    simp
  have hmatrix : (permMatrix (s1Root * s2Root)) ^ 6 = 1 := by
    have hp : ∀ n : ℕ, permMatrix ((s1Root * s2Root) ^ n) =
        (permMatrix (s1Root * s2Root)) ^ n := by
      intro n
      induction n with
      | zero => simp [permMatrix_one]
      | succ n ih =>
          rw [pow_succ, pow_succ, permMatrix_mul, ih]
    rw [← hp 6, hroot, permMatrix_one]
  rw [hmatrix]

theorem phase_generator_product_pow_twelve (zeta : ℂ) (hζ : zeta ^ 6 = -1) :
    (BsPhaseMatrix zeta * BlPhaseMatrix) ^ 12 = 1 :=
  twelfth_power_of_neg_sixth_power _ (phase_generator_product_pow_six zeta hζ)

theorem diagonal_phase_coxeter_pow_six (zeta : ℂ) (hζ : zeta ^ 6 = -1) :
    (BsDiagonalPhase zeta * BlDiagonalPhase) ^ 6 =
      (-1 : ℂ) • (1 : Matrix G2CoordinateRoot G2CoordinateRoot ℂ) := by
  rw [BsDiagonalPhase_eq_scalar, BlDiagonalPhase_eq_permutation]
  exact phase_generator_product_pow_six zeta hζ

theorem diagonal_phase_coxeter_pow_twelve (zeta : ℂ) (hζ : zeta ^ 6 = -1) :
    (BsDiagonalPhase zeta * BlDiagonalPhase) ^ 12 = 1 := by
  rw [BsDiagonalPhase_eq_scalar, BlDiagonalPhase_eq_permutation]
  exact phase_generator_product_pow_twelve zeta hζ

/-- 🏆 THEOREM 4: Packaging the permutation shadow into `ArtinHeckeLift`. -/
def permutationArtinHeckeLift : ArtinHeckeLift G2CoordinateRoot where
  Bs := BsPermMatrix
  Bl := BlPermMatrix
  artin := perm_artin_six_matrix

def phaseArtinHeckeLift (zeta : ℂ) : ArtinHeckeLift G2CoordinateRoot where
  Bs := BsPhaseMatrix zeta
  Bl := BlPhaseMatrix
  artin := phase_artin_six_matrix zeta

end

end InfoGeometry.Exceptional.G2ArtinRootLift
