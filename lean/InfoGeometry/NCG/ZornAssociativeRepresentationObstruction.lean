/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Algebra.AssociativityObstruction
import InfoGeometry.NCG.ZornLeftRegularOperatorDefect

/-!
# No faithful multiplicative representation of operator-valued Zorn matrices

The concrete coefficient ring is the genuinely noncommutative operator ring
`M₂(ℤ)`. A nonzero native Zorn associator on this carrier, together with the
generic associativity obstruction, rules out injective multiplicative maps
into every associative semigroup (in particular, ordinary matrix algebras).
-/

namespace InfoGeometry.NCG.ZornAssociativeRepresentationObstruction

open InfoGeometry.Canonical.AlbertCayleyDickson
open InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion
open InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.OpZornMatrix
open InfoGeometry.NCG.ZornCommutatorLeibnizCounterexample
open InfoGeometry.NCG.ZornLeftRegularOperatorDefect

abbrev CoefficientOperator := Matrix (Fin 2) (Fin 2) ℤ

/-- The existing matrix-unit witness gives a concrete associativity defect on
the noncommutative operator-coefficient Zorn carrier. -/
theorem operatorZorn_nonassociative_witness :
    ∃ X Y Z : OpZornMatrix CoefficientOperator,
      (X * Y) * Z ≠ X * (Y * Z) := by
  refine ⟨diagonalOperator, upperXOperator e11, upperYOperator e12, ?_⟩
  intro h
  have hassoc : opAssociator diagonalOperator (upperXOperator e11)
      (upperYOperator e12) = 0 := sub_eq_zero.mpr h
  have hcoord := congrArg
    (fun T : OpZornMatrix CoefficientOperator => T.w.z) hassoc
  exact operatorZorn_associator_component_ne_zero hcoord

/-- The full noncommutative operator-valued Zorn product has no injective
multiplicative representation into an associative semigroup. -/
theorem no_injective_mul_representation_to_associative_semigroup
    {B : Type*} [Semigroup B] :
    ¬ ∃ φ : OpZornMatrix CoefficientOperator → B,
        Function.Injective φ ∧
          (∀ X Y : OpZornMatrix CoefficientOperator,
            φ (X * Y) = φ X * φ Y) := by
  apply InfoGeometry.Algebra.no_injective_mul_map_to_semigroup_of_nonassociative
  exact operatorZorn_nonassociative_witness

/-- In particular, no injective multiplicative map into any ordinary square
matrix algebra can represent this operator-valued Zorn product. -/
theorem no_injective_matrix_representation
    {ι R : Type*} [Fintype ι] [DecidableEq ι] [Semiring R] :
    ¬ ∃ φ : OpZornMatrix CoefficientOperator → Matrix ι ι R,
        Function.Injective φ ∧
          (∀ X Y : OpZornMatrix CoefficientOperator,
            φ (X * Y) = φ X * φ Y) := by
  exact no_injective_mul_representation_to_associative_semigroup

end InfoGeometry.NCG.ZornAssociativeRepresentationObstruction
