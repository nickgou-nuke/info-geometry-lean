/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.MajoranaCoefficientAction
import Mathlib.Data.Matrix.Basis

/-! Sparse coefficient matrices for the native finite noncommutative chain.
The kernel below is a coefficient kernel on the Majorana span, not the
state-space kernel of the many-body quadratic element. -/
noncomputable section

namespace InfoGeometry.Canonical.KitaevChainCoefficients

open Matrix MajoranaCoefficientAction KitaevChainMajoranaZeroModes
open scoped BigOperators

variable {A : Type*} [Ring A] [Algebra ℝ A]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem quadraticElement_add (g : ι → A) (K L : Matrix ι ι ℝ) :
    quadraticElement g (K + L) = quadraticElement g K + quadraticElement g L := by
  simp [quadraticElement, add_smul, Finset.sum_add_distrib, smul_add]

theorem quadraticElement_sub (g : ι → A) (K L : Matrix ι ι ℝ) :
    quadraticElement g (K - L) = quadraticElement g K - quadraticElement g L := by
  simp [quadraticElement, sub_smul, Finset.sum_sub_distrib, smul_sub]

theorem quadraticElement_sum {κ : Type*} (s : Finset κ)
    (g : ι → A) (K : κ → Matrix ι ι ℝ) :
    quadraticElement g (∑ k ∈ s, K k) = ∑ k ∈ s, quadraticElement g (K k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [quadraticElement]
  | @insert k s hk ih => simp [hk, quadraticElement_add, ih]

theorem quadraticElement_single (g : ι → A) (i j : ι) (c : ℝ) :
    quadraticElement g (Matrix.single i j c) =
      (c / 4) • (g i * g j) := by
  simp [quadraticElement, Matrix.single, ite_and, ite_smul, smul_smul, div_eq_mul_inv,
    mul_comm]

theorem quadraticElement_skew_single (g : ι → A)
    (hg : ∀ i j, g i * g j + g j * g i = if i = j then 2 else 0)
    (i j : ι) (hij : i ≠ j) (t : ℝ) :
    quadraticElement g (Matrix.single i j (2 * t) - Matrix.single j i (2 * t)) =
      t • (g i * g j) := by
  have hanti : g j * g i = -(g i * g j) := by
    have h := hg j i
    rw [if_neg hij.symm] at h
    exact eq_neg_of_add_eq_zero_left h
  rw [quadraticElement_sub, quadraticElement_single, quadraticElement_single, hanti]
  simp only [smul_neg]
  module

def bondLeft {N : ℕ} (j : Fin (N - 1)) : Fin (2 * N) :=
  ⟨2 * j.val + 1, by omega⟩

def bondRight {N : ℕ} (j : Fin (N - 1)) : Fin (2 * N) :=
  ⟨2 * j.val + 2, by omega⟩

theorem bondLeft_ne_bondRight {N : ℕ} (j : Fin (N - 1)) :
    bondLeft j ≠ bondRight j := by
  intro h
  have := congrArg Fin.val h
  simp only [bondLeft, bondRight] at this
  omega

/-- Each native chain bond contributes one skew matrix pair. -/
def chainCoefficientMatrix (N : ℕ) (t : ℝ) : Matrix (Fin (2 * N)) (Fin (2 * N)) ℝ :=
  ∑ j : Fin (N - 1),
    (Matrix.single (bondLeft j) (bondRight j) (2 * t) -
      Matrix.single (bondRight j) (bondLeft j) (2 * t))

theorem chainCoefficientMatrix_skew (N : ℕ) (t : ℝ) (i k : Fin (2 * N)) :
    chainCoefficientMatrix N t i k = -chainCoefficientMatrix N t k i := by
  simp only [chainCoefficientMatrix, Finset.sum_apply, Matrix.sub_apply]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j _
  simp only [Matrix.single, and_comm]
  ring

/-- Exact normalization against the existing chain, including N = 0 and N = 1. -/
theorem quadraticElement_chainCoefficientMatrix {N : ℕ}
    (g : Fin (2 * N) → A) (hg : IsMajoranaBasis N g) (t : ℝ) :
    quadraticElement g (chainCoefficientMatrix N t) =
      kitaevSweetSpotHamiltonian N (t • (1 : A)) g := by
  unfold chainCoefficientMatrix
  rw [quadraticElement_sum]
  unfold kitaevSweetSpotHamiltonian
  apply Finset.sum_congr rfl
  intro j _
  rw [quadraticElement_skew_single g hg _ _ (bondLeft_ne_bondRight j)]
  simp [bondLeft, bondRight, smul_mul_assoc]

/-- All conserved linear Majorana combinations are exactly this sparse kernel. -/
theorem chain_commutator_eq_zero_iff [Nontrivial A] {N : ℕ}
    (g : Fin (2 * N) → A) (hg : IsMajoranaBasis N g) (t : ℝ)
    (v : Fin (2 * N) → ℝ) :
    kitaevSweetSpotHamiltonian N (t • (1 : A)) g * Fintype.linearCombination ℝ g v -
      Fintype.linearCombination ℝ g v * kitaevSweetSpotHamiltonian N (t • (1 : A)) g = 0 ↔
      (chainCoefficientMatrix N t).mulVec v = 0 := by
  rw [← quadraticElement_chainCoefficientMatrix g hg t]
  exact quadraticElement_commutator_eq_zero_iff hg _ (chainCoefficientMatrix_skew N t) v

end InfoGeometry.Canonical.KitaevChainCoefficients
