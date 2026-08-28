/- SPDX-License-Identifier: Apache-2.0 -/

import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.CategoryTheory.Functor.OfSequence
import Mathlib.CategoryTheory.Limits.Filtered
import Mathlib.Tactic
import InfoGeometry.Arithmetic.FredholmClosure
import InfoGeometry.Arithmetic.ArithmeticKMS
import InfoGeometry.Canonical.CategoricalRiemannInductiveColimitBridge
import InfoGeometry.Canonical.FiniteDirichletFilteredColimitBridge
import InfoGeometry.Cocycle.MatrixDetExpTrace.Diagonal

/-!
# Recursive Exponent and Categorical Inductive Filtered Colimit Capstone

This capstone formally integrates:
1. **The Recursive Exponent Formula**: Step-by-step factorization of the modular
   flow exponent $e^{-\beta \sum H_k}$ and Fredholm characteristic determinant
   $\det(1 - e^{-\beta H_{N+1}}) = \det(1 - e^{-\beta H_N}) \cdot (1 - p_{N+1}^{-\beta})$.
2. **The Diagonal Trace-Determinant Identity**:
   $\det(e^{\operatorname{diag}(v)}) = e^{\operatorname{Tr}(\operatorname{diag}(v))}$.
3. **The Inductive Filtered Colimit Transport**:
   Embedding finite mode spaces into the canonical direct filtered colimit
   `colimit dirichletStageFunctor` via `colim.map` and natural transformations.
-/

open CategoryTheory CategoryTheory.Limits
open Complex

noncomputable section

namespace InfoGeometry.Canonical.RecursiveExponentFilteredColimitCapstone

open InfoGeometry.Arithmetic.FredholmClosure
open InfoGeometry.Arithmetic.ArithmeticKMS
open InfoGeometry.Canonical.FiniteDirichletFilteredColimitBridge
open InfoGeometry.Cocycle.MatrixDetExpTrace.Diagonal

/-! ## 1. Recursive Exponent and Fredholm Recurrence -/

/-- Cumulative product of exponential Boltzmann weights up to cutoff `N`. -/
noncomputable def expProductStage (weights : ℕ → ℂ) (N : ℕ) : ℂ :=
  ∏ i ∈ Finset.range N, weights i

@[simp] theorem expProductStage_zero (weights : ℕ → ℂ) :
    expProductStage weights 0 = 1 := by
  simp [expProductStage]

/-- 🏆 THEOREM 1: Step recurrence for the exponential weight product. -/
theorem expProductStage_succ (weights : ℕ → ℂ) (N : ℕ) :
    expProductStage weights (N + 1) = expProductStage weights N * weights N := by
  unfold expProductStage
  rw [Finset.prod_range_succ]

/-
The finite product of recursively generated exponential weights is the
exponential of the corresponding finite sum.  This is the exact finite
recursive exponent transport used by the filtered stages; no infinite
convergence claim is involved.
-/
theorem expProductStage_eq_exp_sum
    (exponents : ℕ → ℂ) (N : ℕ) :
    expProductStage (fun i => Complex.exp (exponents i)) N =
      Complex.exp (∑ i ∈ Finset.range N, exponents i) := by
  induction N with
  | zero => simp [expProductStage]
  | succ N ih =>
      rw [expProductStage_succ, ih, Finset.sum_range_succ]
      rw [Complex.exp_add]

/-- 🏆 THEOREM 2: Step recurrence for the Fredholm determinant factor. -/
theorem fredholm_det_succ (s : ℂ) (N : ℕ) :
    primeRegularizedDetStage s (N + 1) =
      primeRegularizedDetStage s N * primeCutoffFactor s N :=
  primeRegularizedDetStage_succ s N

theorem fredholm_det_succ_explicit (s : ℂ) (N : ℕ) :
    primeRegularizedDetStage s (N + 1) =
      primeRegularizedDetStage s N *
        (1 - Complex.exp (-s * (Real.log (primeAt N : ℝ) : ℂ))) := by
  rw [fredholm_det_succ, primeCutoffFactor_eq_exp_log]

@[simp] theorem fredholm_det_zero (s : ℂ) :
    primeRegularizedDetStage s 0 = 1 := by
  simp [primeRegularizedDetStage, regularizedDetStage]

theorem fredholm_det_inv_succ
    (factor : ℕ → ℂ) (N : ℕ) :
    (regularizedDetStage factor (N + 1))⁻¹ =
      (factor N)⁻¹ * (regularizedDetStage factor N)⁻¹ := by
  rw [regularizedDetStage_succ, mul_inv_rev, mul_comm]

theorem fredholm_prime_det_inv_succ
    (s : ℂ) (N : ℕ)
    :
    (primeRegularizedDetStage s (N + 1))⁻¹ =
      (primeCutoffFactor s N)⁻¹ * (primeRegularizedDetStage s N)⁻¹ := by
  exact fredholm_det_inv_succ
    (fun k => primeCutoffFactor s k) N

/-! The two native descriptions of the first `N` prime stages agree: the
`primeAt` image and the prime subtype cutoff below the next prime are the same
finite carrier.  This is the concrete set-theoretic wire needed before any
cutoff readout can be transported between the two owners. -/
theorem primeCutoff_eq_primeSubtypesBelow_primeAt (N : ℕ) :
    primeCutoff N =
      InfoGeometry.Canonical.PrimeEulerProductConvergenceBridge.primeSubtypesBelow
        (primeAt N) := by
  ext p
  rw [mem_primeCutoff_iff]
  simp [InfoGeometry.Canonical.PrimeEulerProductConvergenceBridge.primeSubtypesBelow]

theorem fredholm_det_inv_eq_product_inv
    (factor : ℕ → ℂ) (N : ℕ) :
    (regularizedDetStage factor N)⁻¹ =
      ∏ i ∈ Finset.range N, (factor i)⁻¹ := by
  induction N with
  | zero => simp [regularizedDetStage]
  | succ N ih =>
      rw [regularizedDetStage_succ, mul_inv_rev, mul_comm, ih, Finset.prod_range_succ]

/-- 🏆 THEOREM 3: Diagonal trace-determinant exponential identity: det(exp(A)) = exp(Tr(A)). -/
theorem diagonal_det_exp_trace {ι : Type*} [Fintype ι] [DecidableEq ι] (v : ι → ℂ) :
    Matrix.det (NormedSpace.exp (Matrix.diagonal v)) =
    NormedSpace.exp (Matrix.trace (Matrix.diagonal v)) :=
  det_exp_diagonal_eq_exp_trace_complex v

/-! ## 2. Categorical Inductive Filtered Colimit System -/

/-- The sequence of finite mode spaces is represented by `dirichletStageFunctor : ℕ ⥤ ModuleCat ℂ`. -/
abbrev ModeStageFunctor : ℕ ⥤ ModuleCat ℂ := dirichletStageFunctor

/-- Universal colimit space of the inductive mode sequence. -/
abbrev ColimitModeSpace : ModuleCat ℂ := colimit ModeStageFunctor

/-- Finite readout on stage `n` transported to the scale algebra. -/
noncomputable def finiteReadoutAt (n : ℕ) : DirichletStage n →ₗ[ℂ] DirichletTarget :=
  finiteDirichletStageReadout n

/-- Colimit readout morphism from the inductive colimit to the target colimit. -/
noncomputable def colimitReadoutMorphism :
    DirichletCoefficientColimit ⟶ DirichletReadoutColimit :=
  dirichletReadoutColimitMap

/-! The colimit readout is a genuine `ModuleCat` morphism.  Consequently its
algebraic laws are inherited directly from the native morphism, while its
stage action is fixed by the existing natural-transformation compatibility. -/
theorem colimitReadoutMorphism_zero :
    colimitReadoutMorphism (0 : DirichletCoefficientColimit) =
      (0 : DirichletReadoutColimit) := by
  exact map_zero (colimitReadoutMorphism.hom)

theorem colimitReadoutMorphism_add (x y : DirichletCoefficientColimit) :
    colimitReadoutMorphism (x + y) =
      colimitReadoutMorphism x + colimitReadoutMorphism y := by
  exact map_add (colimitReadoutMorphism.hom) x y

theorem colimitReadoutMorphism_smul (c : ℂ) (x : DirichletCoefficientColimit) :
    colimitReadoutMorphism (c • x) =
      c • colimitReadoutMorphism x := by
  exact map_smul (colimitReadoutMorphism.hom) c x

theorem colimitReadoutMorphism_stage_compatibility
    (n : ℕ) (a : DirichletStage n) :
    colimitReadoutMorphism ((colimit.ι dirichletStageFunctor n).hom a) =
      (colimit.ι dirichletReadoutTargetFunctor n).hom
        (finiteDirichletStageReadout n a) := by
  exact dirichletReadoutColimit_on_stage n a

theorem fredholm_inverse_colimit_stage_synthesis
    (s : ℂ) (N : ℕ) (n : ℕ) (a : DirichletStage n) :
    ((primeRegularizedDetStage s (N + 1))⁻¹ =
      (primeCutoffFactor s N)⁻¹ * (primeRegularizedDetStage s N)⁻¹) ∧
    (colimitReadoutMorphism ((colimit.ι dirichletStageFunctor n).hom a) =
      (colimit.ι dirichletReadoutTargetFunctor n).hom
        (finiteDirichletStageReadout n a)) :=
  ⟨fredholm_prime_det_inv_succ s N,
   dirichletReadoutColimit_on_stage n a⟩

/-! ## 3. Grand Synthesis Theorem -/

/--
🏆 GRAND RECURSIVE EXPONENT & FILTERED COLIMIT SYNTHESIS
Unites:
1. The step recurrence of the exponential Boltzmann weights $e^{-\beta \sum H_k}$.
2. The recursive step factorization of the Fredholm characteristic polynomial $D_{N+1}(s) = D_N(s)(1 - p_N^{-s})$.
3. The diagonal exponential trace-determinant identity $\det(e^A) = e^{\operatorname{Tr}(A)}$.
4. The finite product expansion $\prod_{p \le N} (1 - p^{-s})$.
5. The categorical descent to the inductive filtered colimit $\operatorname{colim} V_N$.
-/
theorem grand_recursive_exponent_filtered_colimit_synthesis
    (weights : ℕ → ℂ) (s : ℂ) (N : ℕ)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (v : ι → ℂ)
    (n : ℕ) (a : DirichletStage n) :
    (expProductStage weights (N + 1) = expProductStage weights N * weights N) ∧
    (primeRegularizedDetStage s (N + 1) = primeRegularizedDetStage s N * primeCutoffFactor s N) ∧
    (Matrix.det (NormedSpace.exp (Matrix.diagonal v)) =
     NormedSpace.exp (Matrix.trace (Matrix.diagonal v))) ∧
    (primeRegularizedDetStage s N =
     ∏ p ∈ primeCutoff N,
       (1 - InfoGeometry.Arithmetic.PrimeSuperalgebra.complexPrimeWeight s p)) ∧
    (colimitReadoutMorphism ((colimit.ι dirichletStageFunctor n).hom a) =
     (colimit.ι dirichletReadoutTargetFunctor n).hom (finiteDirichletStageReadout n a)) :=
  ⟨expProductStage_succ weights N,
   fredholm_det_succ s N,
   diagonal_det_exp_trace v,
   primeRegularizedDetStage_eq_primeCutoff_prod s N,
   dirichletReadoutColimit_on_stage n a⟩

/-! The cold inverse-temperature guard is transported alongside the finite
stage data.  No analytic limit is inferred: the final clause is precisely the
existing colimit injection/readout compatibility theorem. -/
theorem cold_recursive_exponent_filtered_colimit_synthesis
    (β : ColdInverseTemperature) (weights : ℕ → ℂ) (s : ℂ) (N : ℕ)
    (n : ℕ) (a : DirichletStage n) :
    (1 < β.value) ∧
    (expProductStage weights (N + 1) = expProductStage weights N * weights N) ∧
    (primeRegularizedDetStage s (N + 1) =
      primeRegularizedDetStage s N * primeCutoffFactor s N) ∧
    (colimitReadoutMorphism ((colimit.ι dirichletStageFunctor n).hom a) =
      (colimit.ι dirichletReadoutTargetFunctor n).hom
        (finiteDirichletStageReadout n a)) :=
  ⟨β.one_lt,
   expProductStage_succ weights N,
   fredholm_det_succ s N,
   dirichletReadoutColimit_on_stage n a⟩

end InfoGeometry.Canonical.RecursiveExponentFilteredColimitCapstone
