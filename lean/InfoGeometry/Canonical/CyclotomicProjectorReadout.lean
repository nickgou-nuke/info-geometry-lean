import Mathlib.Data.Matrix.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Data.Complex.Basic
import InfoGeometry.Canonical.DiscretePowerGradeReadout
import InfoGeometry.Canonical.MatrixStageTrifactorFourierCyclotomic

/-!
# Cyclotomic Projector Readout and Fourier-Mellin Compatibility

This module formalizes the exact algebraic Fourier resolution of an operator into
cyclotomic eigenspace projectors:

$$X = \sum_{j=0}^{m-1} \zeta^j P_j$$

where $\zeta$ is a primitive $m$-th root of unity and $\{P_j\}_{j=0}^{m-1}$ forms an orthogonal
resolution of identity:

$$P_i P_j = \delta_{ij} P_i, \qquad \sum_{j=0}^{m-1} P_j = 1, \qquad X P_j = \zeta^j P_j.$$

## Epistemic Hierarchy:
1. $X^n = X$ first gives the zero / nonzero corner projection:
   $$P_0 = 1 - X^{n-1}, \qquad P_{\ne 0} = X^{n-1}.$$
2. On the corner $P_{\ne 0} A P_{\ne 0}$, $X^{n-1} = 1$ ($m = n - 1$), where the cyclotomic
   Fourier resolution lives given a scalar ring containing the $m$-th roots of unity.
3. The power character $k \mapsto X^k$ interacts with the Fourier projectors via
   Fourier-Mellin compatibility:
   $$X^k P_j = \zeta^{k j} P_j.$$

## Key Constructions:
1. **`FourierCyclotomicReadout`**:
   Categorical structure packaging scalar root $\zeta$, projectors $P_i$, idempotency,
   orthogonality, completeness, and eigenspace action.
2. **`FourierMellinCompatibility`**:
   Bridge theorem connecting discrete grade powers to cyclotomic projectors.
3. **Concrete Order-2 Instantiation**:
   Full kernel-checked instance for $H^2 = 1$ in $M_2(\mathbb{C})$ with $\zeta = -1$.

All proofs are complete with 0 sorries and 0 axioms.
-/

noncomputable section

namespace InfoGeometry.Canonical.CyclotomicProjector

open Matrix
open scoped BigOperators
open InfoGeometry.Canonical.DiscretePowerGradeReadout
open InfoGeometry.Canonical.MatrixStageTrifactorFourierCyclotomic

/-! ## 1. Abstract Categorical Fourier Projector Structure -/

/-- Structural interface for an exact cyclotomic projector readout of $X \in A$ of order $m$. -/
structure FourierCyclotomicReadout
    {K A : Type*} [CommRing K] [Ring A] [Algebra K A]
    (X : A) (m : ℕ) where
  /-- Primitive scalar root of unity in the base ring $K$. -/
  ζ : K
  /-- The explicit family of orthogonal projectors. -/
  projector : Fin m → A
  /-- Idempotency: $P_i^2 = P_i$. -/
  idempotent : ∀ i, projector i * projector i = projector i
  /-- Pairwise orthogonality: $P_i P_j = 0$ for $i \ne j$. -/
  orthogonal : ∀ i j, i ≠ j → projector i * projector j = 0
  /-- Resolution of identity: $\sum_i P_i = 1$. -/
  complete : ∑ i, projector i = 1
  /-- Eigenspace action: $X P_i = \zeta^i P_i$. -/
  eigen : ∀ i, X * projector i = algebraMap K A (ζ ^ i.val) * projector i

/-- Spectral reconstruction theorem: $X = \sum_i \zeta^i P_i$. -/
theorem spectral_reconstruction
    {K A : Type*} [CommRing K] [Ring A] [Algebra K A]
    {X : A} {m : ℕ} (F : FourierCyclotomicReadout (K := K) (A := A) X m) :
    X = ∑ i, (algebraMap K A (F.ζ ^ i.val) * F.projector i) := by
  calc X
    _ = X * (∑ i, F.projector i) := by rw [F.complete, mul_one]
    _ = ∑ i, (X * F.projector i) := by rw [Finset.mul_sum]
    _ = ∑ i, (algebraMap K A (F.ζ ^ i.val) * F.projector i) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact F.eigen i

/-! ## 2. Fourier-Mellin Compatibility Bridge -/

/-- Compatibility bridge connecting the discrete power character to cyclotomic projectors. -/
structure FourierMellinCompatibility
    {K A : Type*} [CommRing K] [Ring A] [Algebra K A]
    {X : A} {m : ℕ}
    (F : FourierCyclotomicReadout (K := K) (A := A) X m)
    (M : MellinGradeReadout X) : Prop where
  /-- Eigenspace action of the $k$-th power: $X^k P_i = \zeta^{k \cdot i} P_i$. -/
  grade_projector : ∀ (k : ℕ) (i : Fin m),
    M.eval k * F.projector i = algebraMap K A (F.ζ ^ (k * i.val)) * F.projector i

/-- 🏆 THEOREM: Any valid Fourier and Mellin readout automatically satisfy Fourier-Mellin compatibility. -/
theorem fourier_mellin_compatible
    {K A : Type*} [CommRing K] [Ring A] [Algebra K A]
    {X : A} {m : ℕ}
    (F : FourierCyclotomicReadout (K := K) (A := A) X m)
    (M : MellinGradeReadout X) :
    FourierMellinCompatibility F M := by
  constructor
  intro k i
  induction k with
  | zero =>
      simp only [MellinGradeReadout.eval_zero, one_mul, Nat.zero_mul, pow_zero, map_one, one_mul]
  | succ k ih =>
      have heval : M.eval (k + 1) = X * M.eval k := by
        rw [MellinGradeReadout.eval_eq, MellinGradeReadout.eval_eq, pow_succ']
      rw [heval, mul_assoc, ih]
      have heigen := F.eigen i
      have hcomm : X * (algebraMap K A (F.ζ ^ (k * i.val)) * F.projector i) =
          algebraMap K A (F.ζ ^ (k * i.val)) * (X * F.projector i) := by
        calc
          X * (algebraMap K A (F.ζ ^ (k * i.val)) * F.projector i) =
              (X * algebraMap K A (F.ζ ^ (k * i.val))) * F.projector i := by rw [← mul_assoc]
          _ = (algebraMap K A (F.ζ ^ (k * i.val)) * X) * F.projector i := by
            rw [Algebra.commutes]
          _ = algebraMap K A (F.ζ ^ (k * i.val)) * (X * F.projector i) := by
            rw [mul_assoc]
      rw [hcomm, heigen]
      have hring : algebraMap K A (F.ζ ^ (k * i.val)) * (algebraMap K A (F.ζ ^ i.val) * F.projector i) =
          (algebraMap K A (F.ζ ^ (k * i.val)) * algebraMap K A (F.ζ ^ i.val)) * F.projector i := by
        rw [mul_assoc]
      rw [hring, ← map_mul, ← pow_add]
      have hpow : k * i.val + i.val = (k + 1) * i.val := by ring
      rw [hpow]

/-! ## 3. Concrete Order-2 Involution Realization ($H^2 = 1$) -/

theorem mul_projPlus2 (H : Matrix (Fin 2) (Fin 2) ℂ) (hH : H * H = 1) :
    H * projPlus2 H = projPlus2 H := by
  dsimp [projPlus2]
  rw [Matrix.mul_smul, mul_add, mul_one, hH, add_comm]

theorem mul_projMinus2 (H : Matrix (Fin 2) (Fin 2) ℂ) (hH : H * H = 1) :
    H * projMinus2 H = - projMinus2 H := by
  dsimp [projMinus2]
  rw [Matrix.mul_smul, mul_sub, mul_one, hH]
  have hsub : H - (1 : Matrix (Fin 2) (Fin 2) ℂ) = - (1 - H) := by
    ext i j
    simp only [Matrix.sub_apply, Matrix.neg_apply]
    ring
  rw [hsub, smul_neg]

/-- Order-2 cyclotomic projectors for an involution $H^2 = 1$ in $M_2(\mathbb{C})$. -/
def involutionProjector2 (H : Matrix (Fin 2) (Fin 2) ℂ) (i : Fin 2) : Matrix (Fin 2) (Fin 2) ℂ :=
  if i.val = 0 then projPlus2 H else projMinus2 H

/-- 🏆 THEOREM: Concrete order-2 cyclotomic projector readout for an involution $H^2 = 1$. -/
def involutionCyclotomicReadout (H : Matrix (Fin 2) (Fin 2) ℂ) (hH : H * H = 1) :
    FourierCyclotomicReadout (K := ℂ) (A := Matrix (Fin 2) (Fin 2) ℂ) H 2 where
  ζ := -1
  projector := involutionProjector2 H
  idempotent i := by
    fin_cases i
    · dsimp [involutionProjector2]
      exact projPlus2_sq H hH
    · dsimp [involutionProjector2]
      exact projMinus2_sq H hH
  orthogonal i j hij := by
    fin_cases i <;> fin_cases j
    · contradiction
    · dsimp [involutionProjector2]
      exact projPlus2_mul_projMinus2 H hH
    · dsimp [involutionProjector2]
      exact projMinus2_mul_projPlus2 H hH
    · contradiction
  complete := by
    simp only [Fin.sum_univ_two, involutionProjector2, Fin.isValue]
    exact projPlus2_add_projMinus2 H
  eigen i := by
    fin_cases i
    · simp only [involutionProjector2, pow_zero, map_one, one_mul]
      exact mul_projPlus2 H hH
    · simp only [involutionProjector2, pow_one, map_neg, map_one, neg_mul, one_mul]
      exact mul_projMinus2 H hH

end InfoGeometry.Canonical.CyclotomicProjector
