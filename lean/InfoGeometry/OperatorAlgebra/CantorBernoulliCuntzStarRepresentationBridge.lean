/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Physics.CStarCuntzTensorQuotient
import InfoGeometry.OperatorAlgebra.CantorBernoulliCuntzCStarRealization
import InfoGeometry.Algebra.CuntzNativeGNSBridge
import InfoGeometry.OperatorAlgebra.CantorBernoulliSpatialNativeStateBridge
import InfoGeometry.Algebra.CuntzTensorQuotientComparison
import InfoGeometry.Algebra.CuntzTensorTreeRealizationBridge
import InfoGeometry.OperatorAlgebra.CantorBernoulliCuntzOperatorTreeBridge
import InfoGeometry.OperatorAlgebra.CantorBernoulliFiniteMatrixUnitBridge
import InfoGeometry.Physics.ComplexStarCuntzRedesign

/-!
# Cantor Bernoulli Cuntz Star Representation Bridge

This owner module formalizes the concrete representation of the Cuntz algebra $\mathcal{O}_2$
into the bounded operator algebra $\mathcal{B}(L^2(\mathcal{C}, \mu_C))$:
$$\pi : \mathcal{O}_2 \to \mathcal{B}(L^2(\mathcal{C}, \mu_C))$$

Key results:
1. **$C^*$-Cuntz Family on $\operatorname{Fin} 2$**:
   - `cantorBernoulliFin2CStarFamily : CStarCuntzFamily BoundedL2Operator (Fin 2)`
2. **Algebra Representation**:
   - `cantorBernoulliLiftAlgHom : CuntzAlg ℂ (Fin 2) →ₐ[ℂ] BoundedL2Operator`
3. **Cuntz-Krieger Relations**:
   - $S_i^\dagger S_j = \delta_{ij} I$
   - $S_0 S_0^\dagger + S_1 S_1^\dagger = I$
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.CantorBernoulliCuntzStarRepresentationBridge

open InfoGeometry.Physics.CStarCuntzTensorQuotient
open InfoGeometry.OperatorAlgebra.CantorBernoulliCuntzCStarRealization
open InfoGeometry.Algebra.CuntzNativeGNSBridge
open InfoGeometry.OperatorAlgebra.CantorBernoulliSpatialNativeStateBridge
open InfoGeometry.Algebra.CuntzTensorTreeRealizationBridge
open InfoGeometry.OperatorAlgebra.CantorBernoulliFiniteMatrixUnitBridge
open InfoGeometry.Physics.ComplexStarCuntzRedesign

abbrev B := BoundedL2Operator

/-- Equivalence between Fin 2 and Bool. -/
def finTwoEquivBool : Fin 2 ≃ Bool where
  toFun i := i = 1
  invFun b := if b then 1 else 0
  left_inv i := by fin_cases i <;> rfl
  right_inv b := by cases b <;> rfl

/-- The concrete Cuntz family indexed by Fin 2. -/
def cantorBernoulliFin2CStarFamily : CStarCuntzFamily B (Fin 2) where
  S i := cantorL2CuntzFamily.S (finTwoEquivBool i)
  ortho i j := by
    have h := cantorL2CuntzFamily.ortho (finTwoEquivBool i) (finTwoEquivBool j)
    by_cases hij : i = j
    · subst hij
      simp [h]
    · have hne : finTwoEquivBool i ≠ finTwoEquivBool j := by
        intro heq
        exact hij (finTwoEquivBool.injective heq)
      simp [hne] at h
      simp [hij, h]
  partition := by
    have hpart := cantorL2CuntzFamily.partition
    have hsum : (∑ i : Fin 2, cantorL2CuntzFamily.S (finTwoEquivBool i) * (cantorL2CuntzFamily.S (finTwoEquivBool i))†) =
        (∑ b : Bool, cantorL2CuntzFamily.S b * (cantorL2CuntzFamily.S b)†) :=
      Fintype.sum_equiv finTwoEquivBool _ _ (fun _ => rfl)
    rw [hsum]
    exact hpart

/-- The representation of CuntzAlg on BoundedL2Operator. -/
def cantorBernoulliLiftAlgHom :
    InfoGeometry.Topology.AlgebraicCuntzQuotient.CuntzAlg ℂ (Fin 2) →ₐ[ℂ] B :=
  cantorBernoulliFin2CStarFamily.lift

/-- 🏆 THEOREM: The representation satisfies the Cuntz-Krieger relations in B(L^2). -/
theorem cantorBernoulli_cuntz_relations :
    (∀ i j, cantorBernoulliLiftAlgHom
      (InfoGeometry.Topology.AlgebraicCuntzQuotient.T (R := ℂ) i *
       InfoGeometry.Topology.AlgebraicCuntzQuotient.S (R := ℂ) j) = if i = j then 1 else 0) ∧
    cantorBernoulliLiftAlgHom
      (∑ i : Fin 2, InfoGeometry.Topology.AlgebraicCuntzQuotient.S (R := ℂ) i *
       InfoGeometry.Topology.AlgebraicCuntzQuotient.T (R := ℂ) i) = 1 :=
  cantorBernoulliFin2CStarFamily.represented_cuntz_relations

/-! ## Star representation of the complexified quotient

The older `cantorBernoulliTensorLift` below is a representation of the
repository's ℂ-linear algebraic quotient. The following map instead uses the
complexification of the real Cuntz quotient, whose involution is compatible
with complex scalars. Both maps are constructed from the same concrete
Bernoulli-boundary C⋆-Cuntz family; this section does not assert an equivalence
between their source algebras.
-/

/-- The concrete Bernoulli-boundary Cuntz family represents the
complexified-real Cuntz quotient by a genuine complex star-algebra homomorphism. -/
def cantorBernoulliComplexStarLift :
    ComplexStarCuntzAlg Bool →⋆ₐ[ℂ] B :=
  complexStarLift cantorL2CuntzFamily

/-- The complexified quotient's isometry generator acts by the left/right
Bernoulli branch isometry. -/
@[simp] theorem cantorBernoulliComplexStarLift_Sℂ (b : Bool) :
    cantorBernoulliComplexStarLift (Sℂ b) = cantorL2CuntzFamily.S b := by
  exact complexStarLift_Sℂ cantorL2CuntzFamily b

/-- The complexified quotient's adjoint generator acts by the operator
adjoint of the corresponding Bernoulli branch isometry. -/
@[simp] theorem cantorBernoulliComplexStarLift_Tℂ (b : Bool) :
    cantorBernoulliComplexStarLift (Tℂ b) = star (cantorL2CuntzFamily.S b) := by
  exact complexStarLift_Tℂ cantorL2CuntzFamily b

/-! ## Readout from the tensor-algebra quotient presentation

The two quotient presentations are compared in
`CuntzTensorQuotientComparison`.  Composing that proved algebra equivalence's
forward map with the concrete boundary representation connects the native
tensor quotient directly to bounded operators on the Bernoulli boundary.
This remains an algebra homomorphism: no global star-homomorphism or C⋆
completion assertion is made here.
-/

/-- The tensor-quotient presentation of the binary Cuntz algebra represented
on the concrete Bernoulli-boundary Hilbert space. -/
def cantorBernoulliTensorLift :
    InfoGeometry.Algebra.CuntzTensorQuotient.CuntzAlg 2 →ₐ[ℂ] B :=
  cantorBernoulliLiftAlgHom.comp
    (InfoGeometry.Algebra.CuntzTensorQuotientComparison.tensorQuotientToLetterQuotient 2)

/-- The tensor quotient's isometry generator acts by the corresponding
normalized Bernoulli branch isometry. -/
@[simp] theorem cantorBernoulliTensorLift_cuntzS (i : Fin 2) :
    cantorBernoulliTensorLift
        (InfoGeometry.Algebra.CuntzTensorQuotient.cuntzS 2 i) =
      cantorBernoulliFin2CStarFamily.S i := by
  change cantorBernoulliLiftAlgHom
      (InfoGeometry.Algebra.CuntzTensorQuotientComparison.tensorQuotientToLetterQuotient 2
        (InfoGeometry.Algebra.CuntzTensorQuotient.cuntzS 2 i)) = _
  rw [InfoGeometry.Algebra.CuntzTensorQuotientComparison.tensorQuotientToLetterQuotient,
    InfoGeometry.Algebra.CuntzTensorQuotient.lift_cuntzS]
  exact CStarCuntzFamily.lift_S cantorBernoulliFin2CStarFamily i

/-- The tensor quotient's formal-adjoint generator acts by the Hilbert-space
adjoint of the corresponding normalized branch isometry. -/
@[simp] theorem cantorBernoulliTensorLift_cuntzSdag (i : Fin 2) :
    cantorBernoulliTensorLift
        (InfoGeometry.Algebra.CuntzTensorQuotient.cuntzSdag 2 i) =
      star (cantorBernoulliFin2CStarFamily.S i) := by
  change cantorBernoulliLiftAlgHom
      (InfoGeometry.Algebra.CuntzTensorQuotientComparison.tensorQuotientToLetterQuotient 2
        (InfoGeometry.Algebra.CuntzTensorQuotient.cuntzSdag 2 i)) = _
  rw [InfoGeometry.Algebra.CuntzTensorQuotientComparison.tensorQuotientToLetterQuotient,
    InfoGeometry.Algebra.CuntzTensorQuotient.lift_cuntzSdag]
  exact CStarCuntzFamily.lift_T cantorBernoulliFin2CStarFamily i

/-! The finite matrix units already have a concrete boundary-operator
representation. The following readbacks identify that representation with the
image of the corresponding actual quotient words; this is a representation
compatibility theorem, not an identification of the quotient with the UHF
matrix colimit. -/

theorem cantorBernoulliTensorLift_cuntzWordShift
    (w : List (Fin 2)) :
    cantorBernoulliTensorLift (cuntzWordShift w) =
      InfoGeometry.OperatorAlgebra.CantorBernoulliCuntzOperatorTreeBridge.operatorWord
        (w.map finTwoEquivBool) := by
  induction w with
  | nil =>
      rw [cuntzWordShift_nil, map_one]
      simp [List.map_nil,
        InfoGeometry.OperatorAlgebra.CantorBernoulliCuntzOperatorTreeBridge.operatorWord_nil,
        ContinuousLinearMap.one_def]
  | cons i w ih =>
      rw [cuntzWordShift, map_mul, cantorBernoulliTensorLift_cuntzS, ih]
      rfl

theorem cantorBernoulliTensorLift_cuntzWordShiftDag
    (w : List (Fin 2)) :
    cantorBernoulliTensorLift (cuntzWordShiftDag w) =
      InfoGeometry.OperatorAlgebra.CantorBernoulliCuntzOperatorTreeBridge.operatorWordDag
        (w.map finTwoEquivBool) := by
  induction w with
  | nil =>
      rw [cuntzWordShiftDag_nil, map_one]
      simp [List.map_nil,
        InfoGeometry.OperatorAlgebra.CantorBernoulliCuntzOperatorTreeBridge.operatorWordDag_nil,
        ContinuousLinearMap.one_def]
  | cons i w ih =>
      rw [cuntzWordShiftDag, map_mul, ih, cantorBernoulliTensorLift_cuntzSdag]
      rfl

theorem cantorBernoulliTensorLift_cuntzMatrixUnit
    (u v : List (Fin 2)) :
    cantorBernoulliTensorLift (cuntzWordShift u * cuntzWordShiftDag v) =
      InfoGeometry.OperatorAlgebra.CantorBernoulliCuntzOperatorTreeBridge.operatorMatrixUnit
        (u.map finTwoEquivBool) (v.map finTwoEquivBool) := by
  rw [map_mul, cantorBernoulliTensorLift_cuntzWordShift,
    cantorBernoulliTensorLift_cuntzWordShiftDag]
  rfl

theorem cantorBernoulliTensorLift_bitWordMatrixUnit
    (n : ℕ) (u v : Fin n → Bool) :
    cantorBernoulliTensorLift
        (cuntzWordShift (List.ofFn fun i => finTwoEquivBool.symm (u i)) *
          cuntzWordShiftDag (List.ofFn fun i => finTwoEquivBool.symm (v i))) =
      bitWordUnit n u v := by
  rw [cantorBernoulliTensorLift_cuntzMatrixUnit]
  have hu : List.map finTwoEquivBool
      (List.ofFn fun i : Fin n => finTwoEquivBool.symm (u i)) = List.ofFn u := by
    rw [List.map_ofFn]
    congr 1
    funext i
    exact finTwoEquivBool.apply_symm_apply (u i)
  have hv : List.map finTwoEquivBool
      (List.ofFn fun i : Fin n => finTwoEquivBool.symm (v i)) = List.ofFn v := by
    rw [List.map_ofFn]
    congr 1
    funext i
    exact finTwoEquivBool.apply_symm_apply (v i)
  change InfoGeometry.OperatorAlgebra.CantorBernoulliCuntzOperatorTreeBridge.operatorMatrixUnit
      (List.map finTwoEquivBool
        (List.ofFn fun i : Fin n => finTwoEquivBool.symm (u i)))
      (List.map finTwoEquivBool
        (List.ofFn fun i : Fin n => finTwoEquivBool.symm (v i))) = _
  rw [hu, hv]
  rfl

end InfoGeometry.OperatorAlgebra.CantorBernoulliCuntzStarRepresentationBridge
