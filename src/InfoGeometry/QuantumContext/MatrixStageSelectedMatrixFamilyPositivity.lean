/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.QuantumContext.MatrixStageSelectedMatrixFamily
import InfoGeometry.Quantum.FiniteAttentionCanonicalBridges
import InfoGeometry.Canonical.CuntzMatrixCompatibleStateNet

/-!
# Positivity and Hermitian structure of a selected matrix family

This module transports the repository's full-matrix quadratic-form predicate
`ComplexPositive` and `Matrix.IsHermitian` through normalized partial trace,
stage reindexing, and the tower embedding `A ↦ A ⊗ I₂`. It then proves
nonnegative real parts for the selected functional on star-squares over the
canonical direct-limit carrier. Hermitian seed data makes those values real.
The separate `MatrixStageLimit` quotient carrier is not identified here.
-/

noncomputable section

namespace InfoGeometry.QuantumContext.MatrixStageSelectedMatrixFamilyPositivity

open scoped Kronecker
open InfoGeometry.Canonical.CuntzMatrixTowerInstantiation
open InfoGeometry.Canonical.CuntzMatrixTraceTower
open InfoGeometry.Canonical.CuntzMatrixAlgebraicStarColimit
open InfoGeometry.Canonical.CuntzMatrixCompatibleStateNet
open InfoGeometry.Quantum.FiniteAttentionCanonicalBridges
open InfoGeometry.QuantumContext.MatrixStagePartialTrace
open InfoGeometry.QuantumContext.MatrixStageSelectedMatrixFamily
open InfoGeometry.QuantumContext.MatrixStageSelectedFunctional

theorem complexPositive_partialTrace_reindexed {n : ℕ}
    {D : Matrix (Fin (2 ^ n) × Fin 2) (Fin (2 ^ n) × Fin 2) ℂ}
    (hD : ComplexPositive D) :
    ComplexPositive (partialTraceSecondOp D) :=
  complexPositive_partialTrace hD

theorem hermitian_partialTrace_reindexed {n : ℕ}
    {D : Matrix (Fin (2 ^ n) × Fin 2) (Fin (2 ^ n) × Fin 2) ℂ}
    (hD : D.IsHermitian) : (partialTraceSecondOp D).IsHermitian := by
  rw [Matrix.IsHermitian]
  ext i j
  simp [partialTraceSecondOp, hD.apply]

theorem complexPositive_smul_nonneg {ι : Type*} [Fintype ι]
    {A : Matrix ι ι ℂ} (hA : ComplexPositive A) {c : ℝ} (hc : 0 ≤ c) :
    ComplexPositive ((c : ℂ) • A) := by
  intro v
  have hq := hA v
  have hfactor :
      (∑ i, ∑ j, star (v i) * ((c : ℂ) * A i j) * v j) =
        (c : ℂ) * (∑ i, ∑ j, star (v i) * A i j * v j) := by
    calc
      (∑ i, ∑ j, star (v i) * ((c : ℂ) * A i j) * v j) =
          ∑ i, ∑ j, (c : ℂ) * (star (v i) * A i j * v j) := by
            apply Finset.sum_congr rfl
            intro i hi
            apply Finset.sum_congr rfl
            intro j hj
            ac_rfl
      _ = (c : ℂ) * (∑ i, ∑ j, star (v i) * A i j * v j) := by
            calc
              (∑ i, ∑ j, (c : ℂ) * (star (v i) * A i j * v j)) =
                  ∑ i, (c : ℂ) * ∑ j, star (v i) * A i j * v j := by
                    apply Finset.sum_congr rfl
                    intro i hi
                    rw [← Finset.mul_sum]
              _ = (c : ℂ) * (∑ i, ∑ j, star (v i) * A i j * v j) := by
                    rw [← Finset.mul_sum]
  change 0 ≤ (∑ i, ∑ j, star (v i) * ((c : ℂ) * A i j) * v j).re
  rw [hfactor, Complex.mul_re]
  simpa using mul_nonneg hc hq

theorem hermitian_smul_real {ι : Type*} [Fintype ι]
    {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (c : ℝ) :
    ((c : ℂ) • A).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  simp [Matrix.smul_apply, hA.apply]

theorem complexPositive_reindex_symm {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (e : ι ≃ κ) {A : Matrix κ κ ℂ} (hA : ComplexPositive A) :
    ComplexPositive ((Matrix.reindexAlgEquiv ℂ ℂ e).symm A) := by
  intro v
  have hv := hA (fun i : κ => v (e.symm i))
  change 0 ≤ (∑ i : ι, ∑ j : ι,
    star (v i) * A (e i) (e j) * v j).re
  have hq :
      (∑ i : ι, ∑ j : ι, star (v i) * A (e i) (e j) * v j) =
        ∑ x : κ, ∑ y : κ,
          star (v (e.symm x)) * A x y * v (e.symm y) := by
    rw [← Equiv.sum_comp e.symm (fun i : ι =>
      ∑ j : ι, star (v i) * A (e i) (e j) * v j)]
    apply Finset.sum_congr rfl
    intro x hx
    have hinner := Equiv.sum_comp e.symm (fun j : ι =>
      star (v (e.symm x)) * A x (e j) * v j)
    simpa using hinner.symm
  rw [hq]
  exact hv

theorem hermitian_reindex_symm {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (e : ι ≃ κ) {A : Matrix κ κ ℂ} (hA : A.IsHermitian) :
    ((Matrix.reindexAlgEquiv ℂ ℂ e).symm A).IsHermitian := by
  simpa [Matrix.reindexAlgEquiv] using hA.reindex e.symm

theorem normalizedPartialTraceStep_positive (n : ℕ)
    {D : MatrixStage (n + 1)} (hD : ComplexPositive D) :
    ComplexPositive (normalizedPartialTraceStep n D) := by
  unfold normalizedPartialTraceStep
  rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num]
  exact complexPositive_smul_nonneg
    (complexPositive_partialTrace
      (complexPositive_reindex_symm (stageIndexEquiv n) hD)) (by norm_num)

theorem normalizedPartialTraceStep_hermitian (n : ℕ)
    {D : MatrixStage (n + 1)} (hD : D.IsHermitian) :
    (normalizedPartialTraceStep n D).IsHermitian := by
  unfold normalizedPartialTraceStep
  have hcoef : ((1 / 2 : ℝ) : ℂ) = (1 / 2 : ℂ) := by norm_num
  rw [← hcoef]
  exact hermitian_smul_real
    (hermitian_partialTrace_reindexed
      (hermitian_reindex_symm (stageIndexEquiv n) hD)) (1 / 2 : ℝ)

theorem complexPositive_kronecker_one {m : ℕ}
    {A : Matrix (Fin m) (Fin m) ℂ} (hA : ComplexPositive A) :
    ComplexPositive (A ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)) := by
  classical
  intro v
  have hform :
      (∑ x : Fin m × Fin 2, ∑ y : Fin m × Fin 2,
        star (v x) * (A ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)) x y * v y) =
      ∑ t : Fin 2, ∑ i : Fin m, ∑ j : Fin m,
        star (v (i, t)) * A i j * v (j, t) := by
    simp [Fintype.sum_prod_type, Matrix.one_apply]
    rw [Finset.sum_add_distrib]
  rw [hform, Complex.re_sum]
  apply Finset.sum_nonneg
  intro t ht
  exact hA (fun i => v (i, t))

theorem hermitian_kronecker_one {m : ℕ}
    {A : Matrix (Fin m) (Fin m) ℂ} (hA : A.IsHermitian) :
    (A ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)).IsHermitian := by
  rw [Matrix.IsHermitian, Matrix.conjTranspose_kronecker, hA.eq]
  simp

theorem concreteStep_positive (n : ℕ) {A : MatrixStage n}
    (hA : ComplexPositive A) : ComplexPositive (concreteStep n A) := by
  change ComplexPositive
    (Matrix.reindexAlgEquiv ℂ ℂ (stageIndexEquiv n)
      (A ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)))
  simpa [Matrix.reindexAlgEquiv] using
    complexPositive_reindex_symm (stageIndexEquiv n).symm
      (complexPositive_kronecker_one hA)

theorem concreteStep_hermitian (n : ℕ) {A : MatrixStage n}
    (hA : A.IsHermitian) : (concreteStep n A).IsHermitian := by
  change (Matrix.reindexAlgEquiv ℂ ℂ (stageIndexEquiv n)
    (A ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ))).IsHermitian
  simpa [Matrix.reindexAlgEquiv] using
    (hermitian_kronecker_one hA).reindex (stageIndexEquiv n)

theorem rawMap_positive {i j : ℕ} (hij : i ≤ j) {A : MatrixStage i}
    (hA : ComplexPositive A) : ComplexPositive (rawMap hij A) := by
  induction hij with
  | refl => simpa [rawMap, concreteMap_id] using hA
  | @step j hij ih =>
      rw [rawMap_successor i j hij A]
      exact concreteStep_positive j ih

theorem rawMap_hermitian {i j : ℕ} (hij : i ≤ j) {A : MatrixStage i}
    (hA : A.IsHermitian) : (rawMap hij A).IsHermitian := by
  induction hij with
  | refl => simpa [rawMap, concreteMap_id] using hA
  | @step j hij ih =>
      rw [rawMap_successor i j hij A]
      exact concreteStep_hermitian j ih

theorem restrictMatrixByPartialTrace_positive (n k : ℕ) (Dk : MatrixStage k)
    (hnk : n ≤ k) (hD : ComplexPositive Dk) :
    ComplexPositive (restrictMatrixByPartialTrace n k Dk hnk) := by
  induction d : k - n using Nat.strong_induction_on generalizing n with
  | h d ih =>
      by_cases heq : n = k
      · subst k
        rw [restrictMatrixByPartialTrace_eq n n Dk le_rfl rfl]
        exact hD
      · have hlt : n < k := by omega
        rw [restrictMatrixByPartialTrace_succ n k hlt Dk]
        apply normalizedPartialTraceStep_positive
        apply ih (k - (n + 1)) (by omega) (n + 1)
        · omega

theorem restrictMatrixByPartialTrace_hermitian (n k : ℕ) (Dk : MatrixStage k)
    (hnk : n ≤ k) (hD : Dk.IsHermitian) :
    (restrictMatrixByPartialTrace n k Dk hnk).IsHermitian := by
  induction d : k - n using Nat.strong_induction_on generalizing n with
  | h d ih =>
      by_cases heq : n = k
      · subst k
        rw [restrictMatrixByPartialTrace_eq n n Dk le_rfl rfl]
        exact hD
      · have hlt : n < k := by omega
        rw [restrictMatrixByPartialTrace_succ n k hlt Dk]
        apply normalizedPartialTraceStep_hermitian
        apply ih (k - (n + 1)) (by omega) (n + 1)
        · omega

theorem selectedMatrixFamily_preserves (k : ℕ) (Dk : MatrixStage k)
    (hDpos : ComplexPositive Dk) (hDherm : Dk.IsHermitian) :
    ∀ n, (selectedMatrixFamily k Dk n).IsHermitian ∧
      ComplexPositive (selectedMatrixFamily k Dk n) := by
  intro n
  rw [selectedMatrixFamily]
  split_ifs with h
  · exact ⟨restrictMatrixByPartialTrace_hermitian n k Dk h hDherm,
      restrictMatrixByPartialTrace_positive n k Dk h hDpos⟩
  · have hkn : k ≤ n := Nat.le_of_not_ge h
    exact ⟨rawMap_hermitian hkn hDherm, rawMap_positive hkn hDpos⟩

theorem selectedMatrixFamily_positive (k : ℕ) (Dk : MatrixStage k)
    (hD : ComplexPositive Dk) (n : ℕ) :
    ComplexPositive (selectedMatrixFamily k Dk n) := by
  rw [selectedMatrixFamily]
  split_ifs with h
  · exact restrictMatrixByPartialTrace_positive n k Dk h hD
  · exact rawMap_positive (Nat.le_of_not_ge h) hD

theorem selectedMatrixFamily_hermitian (k : ℕ) (Dk : MatrixStage k)
    (hD : Dk.IsHermitian) (n : ℕ) :
    (selectedMatrixFamily k Dk n).IsHermitian := by
  rw [selectedMatrixFamily]
  split_ifs with h
  · exact restrictMatrixByPartialTrace_hermitian n k Dk h hD
  · exact rawMap_hermitian (Nat.le_of_not_ge h) hD

theorem matrixTraceFunctional_weighted_positive (n : ℕ)
    (D : MatrixStage n) (hD : ComplexPositive D) (x : MatrixStage n) :
    0 ≤ (matrixTraceFunctional n (star x * x * D)).re := by
  let v (a : Fin (2 ^ n)) : Fin (2 ^ n) → ℂ := fun i => star (x a i)
  have hrow (a : Fin (2 ^ n)) :
      0 ≤ (∑ i, ∑ j, star (v a i) * D i j * v a j).re := hD (v a)
  have htrace : Matrix.trace (star x * x * D) =
      ∑ a, ∑ i, ∑ j, x a i * D i j * star (x a j) := by
    calc
      Matrix.trace (star x * x * D) = Matrix.trace (x * D * star x) := by
        rw [Matrix.trace_mul_cycle, Matrix.trace_mul_cycle]
      _ = ∑ a, ∑ i, ∑ j, x a i * D i j * star (x a j) := by
        simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
          Finset.sum_mul]
        congr 1
        funext a
        simpa only [Matrix.star_apply] using
          (Finset.sum_comm (f := fun i j : Fin (2 ^ n) =>
            x a i * D i j * star (x a j))).symm
  have htrace_re : 0 ≤ (Matrix.trace (star x * x * D)).re := by
    rw [htrace, Complex.re_sum]
    apply Finset.sum_nonneg
    intro a ha
    have hrow' :
        (∑ i, ∑ j, x a i * D i j * star (x a j)).re =
          (∑ i, ∑ j, star (v a i) * D i j * v a j).re := by
      simp [v]
    rw [hrow']
    exact hrow a
  rw [matrixTraceFunctional_apply]
  have hcoef : (1 / (2 ^ n : ℂ)) = ((1 / (2 ^ n : ℝ) : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [hcoef, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
  simp only [zero_mul, sub_zero]
  exact mul_nonneg (by positivity) htrace_re

theorem selectedStageFunctional_eq_weightedSelectedFamily (k n : ℕ)
    (Dk : MatrixStage k) (A : MatrixStage n) :
    selectedStageFunctional k Dk n A =
      weightedStageFunctional (selectedMatrixFamily k Dk) n A := by
  have hselectedCompat : Compatible (selectedStageFunctional k Dk) :=
    selectedStageFunctional_compatible k Dk
  have hfamilyCompat : WeightedCompatible (selectedMatrixFamily k Dk) :=
    weightedStageFunctional_compatible_of_partialTraceCompatible
      (selectedMatrixFamily k Dk) (selectedMatrixFamily_partialTraceCompatible k Dk)
  by_cases hnk : n ≤ k
  · rw [← hselectedCompat (i := n) (j := k) hnk A,
      ← hfamilyCompat (i := n) (j := k) hnk A]
    simp [selectedStageFunctional, weightedMatrixTrace,
      weightedStageFunctional_apply, selectedMatrixFamily_at_selected,
      rawMap, concreteMap_id]
  · have hgt : k < n := by omega
    simp [selectedStageFunctional, not_le_of_gt hgt, weightedMatrixTrace,
      weightedStageFunctional_apply, selectedMatrixFamily, rawMap]

theorem weightedStageFunctional_star_of_hermitian
    (D : ∀ n : ℕ, MatrixStage n) (hD : ∀ n, (D n).IsHermitian)
    (n : ℕ) (A : MatrixStage n) :
    weightedStageFunctional D n (star A) =
      star (weightedStageFunctional D n A) := by
  rw [weightedStageFunctional_apply, weightedStageFunctional_apply]
  have h := matrixTraceFunctional_star_native n (A * D n)
  rw [star_mul] at h
  have h' : matrixTraceFunctional n (D n * star A) =
      star (matrixTraceFunctional n (A * D n)) := by
    have hstarD : star (D n) = D n := by
      simpa only [Matrix.IsHermitian, Matrix.star_eq_conjTranspose] using hD n
    rw [hstarD] at h
    exact h
  calc
    matrixTraceFunctional n (star A * D n) =
        matrixTraceFunctional n (D n * star A) := by
      simpa using Matrix.trace_mul_comm (star A) (D n)
    _ = star (matrixTraceFunctional n (A * D n)) := h'

theorem selectedStageFunctional_star_of_hermitian (k n : ℕ)
    (Dk : MatrixStage k)
    (hFamily : ∀ n, (selectedMatrixFamily k Dk n).IsHermitian)
    (A : MatrixStage n) :
    selectedStageFunctional k Dk n (star A) =
      star (selectedStageFunctional k Dk n A) := by
  rw [selectedStageFunctional_eq_weightedSelectedFamily,
    selectedStageFunctional_eq_weightedSelectedFamily]
  exact weightedStageFunctional_star_of_hermitian
    (selectedMatrixFamily k Dk) hFamily n A

theorem selectedStageColimitFunctional_star_of_hermitian (k : ℕ)
    (Dk : MatrixStage k)
    (hFamily : ∀ n, (selectedMatrixFamily k Dk n).IsHermitian)
    (x : InfoGeometry.Canonical.CuntzMatrixAlgebraicStarColimit.Carrier) :
    selectedStageColimitFunctional k Dk (star x) =
      star (selectedStageColimitFunctional k Dk x) := by
  induction x using DirectLimit.induction with
  | _ n A =>
      change selectedStageColimitFunctional k Dk
          (star (stageInjection n A)) =
        star (selectedStageColimitFunctional k Dk (stageInjection n A))
      rw [← stageInjection_star]
      change colimitFunctional (selectedStageFunctional k Dk)
          (selectedStageFunctional_compatible k Dk) (stageInjection n (star A)) =
        star (colimitFunctional (selectedStageFunctional k Dk)
          (selectedStageFunctional_compatible k Dk) (stageInjection n A))
      rw [colimitFunctional_stage, colimitFunctional_stage]
      exact selectedStageFunctional_star_of_hermitian k n Dk hFamily A

theorem selectedStageColimitFunctional_positive (k : ℕ) (Dk : MatrixStage k)
    (hD : ComplexPositive Dk)
    (x : InfoGeometry.Canonical.CuntzMatrixAlgebraicStarColimit.Carrier) :
    0 ≤ (selectedStageColimitFunctional k Dk (star x * x)).re := by
  have hstagePos : ∀ n A,
      0 ≤ (selectedStageFunctional k Dk n (star A * A)).re := by
    intro n A
    rw [selectedStageFunctional_eq_weightedSelectedFamily]
    exact matrixTraceFunctional_weighted_positive n
      (selectedMatrixFamily k Dk n) (selectedMatrixFamily_positive k Dk hD n) A
  induction x using DirectLimit.induction with
  | _ n A =>
      have harg :
          star (⟦⟨n, A⟩⟧ : InfoGeometry.Canonical.CuntzMatrixAlgebraicStarColimit.Carrier) *
              ⟦⟨n, A⟩⟧ = stageInjection n (star A * A) := by
        change star (stageInjection n A) * stageInjection n A =
          stageInjection n (star A * A)
        rw [← stageInjection_star, ← stageInjection_mul]
      rw [harg]
      change 0 ≤ (colimitFunctional (selectedStageFunctional k Dk)
        (selectedStageFunctional_compatible k Dk)
        (stageInjection n (star A * A))).re
      rw [colimitFunctional_stage]
      exact hstagePos n A

theorem selectedStageColimitFunctional_starSquare_im_zero (k : ℕ)
    (Dk : MatrixStage k) (hDherm : Dk.IsHermitian)
    (x : InfoGeometry.Canonical.CuntzMatrixAlgebraicStarColimit.Carrier) :
    (selectedStageColimitFunctional k Dk (star x * x)).im = 0 := by
  have hfamily : ∀ n, (selectedMatrixFamily k Dk n).IsHermitian :=
    fun n => selectedMatrixFamily_hermitian k Dk hDherm n
  have hstar_arg : star (star x * x) = star x * x := by
    simp [star_mul]
  have hstar := selectedStageColimitFunctional_star_of_hermitian
    k Dk hfamily (star x * x)
  rw [hstar_arg] at hstar
  have him := congrArg Complex.im hstar
  have him' : (selectedStageColimitFunctional k Dk (star x * x)).im =
      -(selectedStageColimitFunctional k Dk (star x * x)).im := by
    simpa using him
  linarith

end InfoGeometry.QuantumContext.MatrixStageSelectedMatrixFamilyPositivity

end
