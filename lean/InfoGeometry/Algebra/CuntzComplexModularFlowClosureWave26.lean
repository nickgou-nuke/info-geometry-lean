/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.CuntzKMSCondition

noncomputable section

namespace InfoGeometry.Algebra.CuntzComplexModularFlowClosureWave26

open InfoGeometry.Algebra.CuntzTensorQuotient
open InfoGeometry.Algebra.CuntzModularAutomorphism
open InfoGeometry.Algebra.CuntzKMSCondition
open Complex

/-- Complex-time modular flow composes additively on the tensor algebra. -/
theorem sigmaTensorComplex_add
    (n : ℕ) (primes : Fin n → ℕ) (z w : ℂ) (x : CuntzTensor n) :
    sigmaTensorComplex n primes (z + w) x =
      sigmaTensorComplex n primes z (sigmaTensorComplex n primes w x) := by
  induction x using TensorAlgebra.induction with
  | algebraMap r =>
      dsimp [sigmaTensorComplex]
      simp [modularPhaseComplex_add]
  | ι v =>
      refine Finsupp.induction_linear v (by simp [sigmaTensorComplex, AlgHom.comp_apply]) ?_ ?_
      · intro v₁ v₂ hv₁ hv₂
        dsimp [sigmaTensorComplex, AlgHom.comp_apply] at *
        simp [map_add, hv₁, hv₂]
      · intro g c
        rcases g with ⟨i, b⟩
        cases b with
        | false =>
            dsimp [sigmaTensorComplex, AlgHom.comp_apply, gen]
            simp_rw [TensorAlgebra.lift_ι_apply]
            rw [modularOnFreeComplex_single, modularOnFreeComplex_single]
            rw [map_smul (TensorAlgebra.lift ℂ (modularOnFreeComplex n primes z))]
            dsimp [gen]
            rw [TensorAlgebra.lift_ι_apply, modularOnFreeComplex_single]
            simp [gen, modularPhaseComplex_add, smul_smul, mul_comm, mul_left_comm, mul_assoc]
        | true =>
            dsimp [sigmaTensorComplex, AlgHom.comp_apply, gen]
            simp_rw [TensorAlgebra.lift_ι_apply]
            rw [modularOnFreeComplex_single, modularOnFreeComplex_single]
            rw [map_smul (TensorAlgebra.lift ℂ (modularOnFreeComplex n primes z))]
            dsimp [gen]
            rw [TensorAlgebra.lift_ι_apply, modularOnFreeComplex_single]
            have hphase : modularPhaseComplexInv (primes i) (z + w) =
                modularPhaseComplexInv (primes i) z * modularPhaseComplexInv (primes i) w := by
              dsimp [modularPhaseComplexInv]
              rw [← Complex.exp_add]
              congr 1
              push_cast
              ring
            simp [gen, hphase, smul_smul, mul_comm, mul_left_comm, mul_assoc]
  | mul x y hx hy =>
      dsimp [sigmaTensorComplex, AlgHom.comp_apply] at *
      simp [map_mul, hx, hy]
  | add x y hx hy =>
      dsimp [sigmaTensorComplex, AlgHom.comp_apply] at *
      simp [map_add, hx, hy]

/-- Complex-time modular flow composes additively on the Cuntz quotient. -/
theorem sigmaComplex_add
    (n : ℕ) (primes : Fin n → ℕ) (z w : ℂ) :
    sigmaComplex n primes (z + w) =
      (sigmaComplex n primes z).comp (sigmaComplex n primes w) := by
  apply DFunLike.ext
  intro x
  rcases RingQuot.mkAlgHom_surjective ℂ (CuntzRel n) x with ⟨y, rfl⟩
  calc
    sigmaComplex n primes (z + w) ((RingQuot.mkAlgHom ℂ (CuntzRel n)) y) =
        (RingQuot.mkAlgHom ℂ (CuntzRel n)) (sigmaTensorComplex n primes (z + w) y) :=
      sigmaComplex_mk n primes (z + w) y
    _ = (RingQuot.mkAlgHom ℂ (CuntzRel n))
        (sigmaTensorComplex n primes z (sigmaTensorComplex n primes w y)) := by
      rw [sigmaTensorComplex_add]
    _ = sigmaComplex n primes z ((RingQuot.mkAlgHom ℂ (CuntzRel n))
        (sigmaTensorComplex n primes w y)) :=
      (sigmaComplex_mk n primes z (sigmaTensorComplex n primes w y)).symm
    _ = sigmaComplex n primes z
        (sigmaComplex n primes w ((RingQuot.mkAlgHom ℂ (CuntzRel n)) y)) := by
      rw [sigmaComplex_mk n primes w y]

/-- Complex-time modular flow at zero is the identity automorphism. -/
theorem sigmaComplex_zero
    (n : ℕ) (primes : Fin n → ℕ) :
    sigmaComplex n primes (0 : ℂ) = AlgHom.id ℂ (CuntzAlg n) := by
  apply DFunLike.ext
  intro x
  rcases RingQuot.mkAlgHom_surjective ℂ (CuntzRel n) x with ⟨y, rfl⟩
  have hzero : sigmaTensorComplex n primes (0 : ℂ) = AlgHom.id ℂ (CuntzTensor n) := by
    ext v
    dsimp [sigmaTensorComplex, modularOnFreeComplex]
    simp [modularPhaseComplex, modularPhaseComplexInv]
  calc
    sigmaComplex n primes (0 : ℂ) ((RingQuot.mkAlgHom ℂ (CuntzRel n)) y) =
        (RingQuot.mkAlgHom ℂ (CuntzRel n)) (sigmaTensorComplex n primes (0 : ℂ) y) :=
      sigmaComplex_mk n primes 0 y
    _ = (RingQuot.mkAlgHom ℂ (CuntzRel n)) y := by rw [hzero]; rfl
    _ = AlgHom.id ℂ (CuntzAlg n) ((RingQuot.mkAlgHom ℂ (CuntzRel n)) y) := by rfl

end InfoGeometry.Algebra.CuntzComplexModularFlowClosureWave26
