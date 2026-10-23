/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Algebra.CuntzKMSCondition
import InfoGeometry.Algebra.CuntzComplexificationAlgEquiv

/-!
# Binary gauge flow on the corrected complex-star Cuntz carrier

The existing complex-time flow is indexed by the older `Fin n` quotient.  This
owner supplies the missing binary-indexed wire on the genuine carrier
`ComplexStarCuntzAlg Bool`.  It is obtained by the quotient universal
property, then transported through the existing complexification equivalence.
The construction acts on the full noncommutative quotient; no diagonalization,
commutativity, or spectral decomposition is used.

This is an algebraic flow on the finite binary Cuntz quotient.  It is not a
positive KMS functional, a C*-completion, or an analytic-strip theorem.
-/

noncomputable section

namespace InfoGeometry.Algebra.CuntzComplexStarBinaryGaugeFlow

open Complex
open InfoGeometry.Topology.AlgebraicCuntzQuotient
open InfoGeometry.Physics.ComplexStarCuntzRedesign
open InfoGeometry.Algebra.CuntzComplexification
open InfoGeometry.Algebra.CuntzKMSCondition

abbrev BinaryAlg := CuntzAlg ℂ Bool
abbrev Carrier := ComplexStarCuntzAlg Bool

lemma modularPhaseComplexInv_add (p : ℕ) (z w : ℂ) :
    modularPhaseComplexInv p (z + w) =
      modularPhaseComplexInv p z * modularPhaseComplexInv p w := by
  unfold modularPhaseComplexInv
  rw [show -(I * (z + w) * (Real.log (p : ℝ) : ℂ)) =
      -(I * z * (Real.log (p : ℝ) : ℂ)) +
        -(I * w * (Real.log (p : ℝ) : ℂ)) by ring]
  rw [Complex.exp_add]

def sigmaBinary (z : ℂ) : BinaryAlg →ₐ[ℂ] BinaryAlg :=
  lift
    (fun b => modularPhaseComplex 2 z • S (R := ℂ) b)
    (fun b => modularPhaseComplexInv 2 z • T (R := ℂ) b)
    (by
      intro i j
      rw [smul_mul_smul, T_mul_S]
      by_cases h : i = j
      · subst j
        rw [mul_comm, modularPhaseComplex_mul_inv]
        simp
      · simp [h])
    (by
      calc
        (∑ b : Bool,
            (modularPhaseComplex 2 z • S (R := ℂ) b) *
              (modularPhaseComplexInv 2 z • T (R := ℂ) b)) =
            ∑ b : Bool,
              (modularPhaseComplex 2 z * modularPhaseComplexInv 2 z) •
                (S (R := ℂ) b * T (R := ℂ) b) := by
          apply Finset.sum_congr rfl
          intro b hb
          rw [smul_mul_smul]
        _ = ∑ b : Bool, S (R := ℂ) b * T (R := ℂ) b := by
          simp [modularPhaseComplex_mul_inv]
        _ = 1 := partition_one)

@[simp] theorem sigmaBinary_S (z : ℂ) (b : Bool) :
    sigmaBinary z (S (R := ℂ) b) = modularPhaseComplex 2 z • S (R := ℂ) b := by
  exact lift_S _ _ _ _ b

@[simp] theorem sigmaBinary_T (z : ℂ) (b : Bool) :
    sigmaBinary z (T (R := ℂ) b) = modularPhaseComplexInv 2 z • T (R := ℂ) b := by
  exact lift_T _ _ _ _ b

theorem sigmaBinary_add (z w : ℂ) :
    sigmaBinary (z + w) = (sigmaBinary z).comp (sigmaBinary w) := by
  apply (lift_unique
    (fun b => modularPhaseComplex 2 (z + w) • S (R := ℂ) b)
    (fun b => modularPhaseComplexInv 2 (z + w) • T (R := ℂ) b)
    (by
      intro i j
      rw [smul_mul_smul, T_mul_S]
      by_cases h : i = j
      · subst j
        rw [mul_comm, modularPhaseComplex_mul_inv]
        simp
      · simp [h])
    (by
      calc
        (∑ b : Bool,
            (modularPhaseComplex 2 (z + w) • S (R := ℂ) b) *
              (modularPhaseComplexInv 2 (z + w) • T (R := ℂ) b)) =
            ∑ b : Bool,
              (modularPhaseComplex 2 (z + w) *
                  modularPhaseComplexInv 2 (z + w)) •
                (S (R := ℂ) b * T (R := ℂ) b) := by
          apply Finset.sum_congr rfl
          intro b hb
          rw [smul_mul_smul]
        _ = ∑ b : Bool, S (R := ℂ) b * T (R := ℂ) b := by
          simp [modularPhaseComplex_mul_inv]
        _ = 1 := partition_one)
    ((sigmaBinary z).comp (sigmaBinary w))
    (by
      intro b
      rw [AlgHom.comp_apply, sigmaBinary_S, map_smul, sigmaBinary_S]
      rw [smul_smul, mul_comm, modularPhaseComplex_add]
      )
    (by
      intro b
      rw [AlgHom.comp_apply, sigmaBinary_T, map_smul, sigmaBinary_T]
      rw [smul_smul, mul_comm, modularPhaseComplexInv_add]
      )).symm

def carrierFlow (z : ℂ) : Carrier →ₐ[ℂ] Carrier :=
  (complexificationAlgEquiv (ι := Bool)).symm.toAlgHom.comp
    ((sigmaBinary z).comp (complexificationAlgEquiv (ι := Bool)).toAlgHom)

@[simp] theorem carrierFlow_S (z : ℂ) (b : Bool) :
    carrierFlow z (Sℂ b) = modularPhaseComplex 2 z • Sℂ b := by
  simp [carrierFlow]

@[simp] theorem carrierFlow_T (z : ℂ) (b : Bool) :
    carrierFlow z (Tℂ b) = modularPhaseComplexInv 2 z • Tℂ b := by
  simp [carrierFlow]

theorem carrierFlow_add (z w : ℂ) :
    carrierFlow (z + w) = (carrierFlow z).comp (carrierFlow w) := by
  apply AlgHom.ext
  intro x
  apply (complexificationAlgEquiv (ι := Bool)).injective
  simp [carrierFlow, sigmaBinary_add]

end InfoGeometry.Algebra.CuntzComplexStarBinaryGaugeFlow
