/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.CuntzTensorQuotient
import InfoGeometry.Topology.AlgebraicCuntzQuotient

/-!
# Comparison of the two finite algebraic Cuntz quotient presentations

The tensor-algebra quotient and the letter-indexed quotient have distinct
carriers.  Their defining relations give canonical algebra homomorphisms in
both directions.  This file proves those maps and their action on generators;
it does not identify either algebra with a C⋆-completion.
-/

noncomputable section

namespace InfoGeometry.Algebra.CuntzTensorQuotientComparison

/-- The tensor presentation maps to the letter presentation by matching the
`S` and formal-adjoint generators.  The map is obtained by descending the
tensor-algebra universal map through the two Cuntz relations. -/
def tensorQuotientToLetterQuotient (n : ℕ) :
    InfoGeometry.Algebra.CuntzTensorQuotient.CuntzAlg n →ₐ[ℂ]
      InfoGeometry.Topology.AlgebraicCuntzQuotient.CuntzAlg ℂ (Fin n) :=
  InfoGeometry.Algebra.CuntzTensorQuotient.lift n
    (fun i => InfoGeometry.Topology.AlgebraicCuntzQuotient.S (R := ℂ) i)
    (fun i => InfoGeometry.Topology.AlgebraicCuntzQuotient.T (R := ℂ) i)
    (by
      intro i j
      exact InfoGeometry.Topology.AlgebraicCuntzQuotient.T_mul_S i j)
    (InfoGeometry.Topology.AlgebraicCuntzQuotient.partition_one (R := ℂ))

/-- The letter presentation maps back to the tensor presentation by the same
generator assignment, now using the letter quotient's universal property. -/
def letterQuotientToTensorQuotient (n : ℕ) :
    InfoGeometry.Topology.AlgebraicCuntzQuotient.CuntzAlg ℂ (Fin n) →ₐ[ℂ]
      InfoGeometry.Algebra.CuntzTensorQuotient.CuntzAlg n :=
  InfoGeometry.Topology.AlgebraicCuntzQuotient.lift (R := ℂ)
    (fun i => InfoGeometry.Algebra.CuntzTensorQuotient.cuntzS n i)
    (fun i => InfoGeometry.Algebra.CuntzTensorQuotient.cuntzSdag n i)
    (by
      intro i j
      exact InfoGeometry.Algebra.CuntzTensorQuotient.cuntz_orthogonality n i j)
    (InfoGeometry.Algebra.CuntzTensorQuotient.cuntz_ranges_sum_one n)

/-- The composite from the tensor presentation to the letter presentation and
back is the identity algebra homomorphism. The proof uses the tensor quotient's
generator uniqueness theorem. -/
theorem letterToTensor_comp_tensorToLetter (n : ℕ) :
    (letterQuotientToTensorQuotient n).comp
        (tensorQuotientToLetterQuotient n) =
      AlgHom.id ℂ (InfoGeometry.Algebra.CuntzTensorQuotient.CuntzAlg n) := by
  calc
    (letterQuotientToTensorQuotient n).comp
        (tensorQuotientToLetterQuotient n) =
      InfoGeometry.Algebra.CuntzTensorQuotient.lift n
        (InfoGeometry.Algebra.CuntzTensorQuotient.cuntzS n)
        (InfoGeometry.Algebra.CuntzTensorQuotient.cuntzSdag n)
        (InfoGeometry.Algebra.CuntzTensorQuotient.cuntz_orthogonality n)
        (InfoGeometry.Algebra.CuntzTensorQuotient.cuntz_ranges_sum_one n) := by
      apply InfoGeometry.Algebra.CuntzTensorQuotient.lift_unique
      · intro i
        change letterQuotientToTensorQuotient n
          (tensorQuotientToLetterQuotient n
            (InfoGeometry.Algebra.CuntzTensorQuotient.cuntzS n i)) = _
        rw [tensorQuotientToLetterQuotient,
          InfoGeometry.Algebra.CuntzTensorQuotient.lift_cuntzS]
        exact InfoGeometry.Topology.AlgebraicCuntzQuotient.lift_S
          (s := InfoGeometry.Algebra.CuntzTensorQuotient.cuntzS n)
          (t := InfoGeometry.Algebra.CuntzTensorQuotient.cuntzSdag n)
          (h_ortho := InfoGeometry.Algebra.CuntzTensorQuotient.cuntz_orthogonality n)
          (h_partition := InfoGeometry.Algebra.CuntzTensorQuotient.cuntz_ranges_sum_one n)
          i
      · intro i
        change letterQuotientToTensorQuotient n
          (tensorQuotientToLetterQuotient n
            (InfoGeometry.Algebra.CuntzTensorQuotient.cuntzSdag n i)) = _
        rw [tensorQuotientToLetterQuotient,
          InfoGeometry.Algebra.CuntzTensorQuotient.lift_cuntzSdag]
        exact InfoGeometry.Topology.AlgebraicCuntzQuotient.lift_T
          (s := InfoGeometry.Algebra.CuntzTensorQuotient.cuntzS n)
          (t := InfoGeometry.Algebra.CuntzTensorQuotient.cuntzSdag n)
          (h_ortho := InfoGeometry.Algebra.CuntzTensorQuotient.cuntz_orthogonality n)
          (h_partition := InfoGeometry.Algebra.CuntzTensorQuotient.cuntz_ranges_sum_one n)
          i
    _ = AlgHom.id ℂ _ := by
      symm
      exact InfoGeometry.Algebra.CuntzTensorQuotient.lift_unique n
        (InfoGeometry.Algebra.CuntzTensorQuotient.cuntzS n)
        (InfoGeometry.Algebra.CuntzTensorQuotient.cuntzSdag n)
        (InfoGeometry.Algebra.CuntzTensorQuotient.cuntz_orthogonality n)
        (InfoGeometry.Algebra.CuntzTensorQuotient.cuntz_ranges_sum_one n)
        (AlgHom.id ℂ _)
        (by intro i; rfl)
        (by intro i; rfl)

/-- The composite from the letter presentation to the tensor presentation and
back is the identity algebra homomorphism. The proof uses the letter quotient's
generator uniqueness theorem. -/
theorem tensorToLetter_comp_letterToTensor (n : ℕ) :
    (tensorQuotientToLetterQuotient n).comp
        (letterQuotientToTensorQuotient n) =
      AlgHom.id ℂ
        (InfoGeometry.Topology.AlgebraicCuntzQuotient.CuntzAlg ℂ (Fin n)) := by
  calc
    (tensorQuotientToLetterQuotient n).comp
        (letterQuotientToTensorQuotient n) =
      InfoGeometry.Topology.AlgebraicCuntzQuotient.lift (R := ℂ)
        (InfoGeometry.Topology.AlgebraicCuntzQuotient.S (R := ℂ))
        (InfoGeometry.Topology.AlgebraicCuntzQuotient.T (R := ℂ))
        (InfoGeometry.Topology.AlgebraicCuntzQuotient.T_mul_S)
        (InfoGeometry.Topology.AlgebraicCuntzQuotient.partition_one (R := ℂ)) := by
      apply InfoGeometry.Topology.AlgebraicCuntzQuotient.lift_unique
      · intro i
        change tensorQuotientToLetterQuotient n
          (letterQuotientToTensorQuotient n
            (InfoGeometry.Topology.AlgebraicCuntzQuotient.S (R := ℂ) i)) = _
        rw [letterQuotientToTensorQuotient,
          InfoGeometry.Topology.AlgebraicCuntzQuotient.lift_S]
        exact InfoGeometry.Algebra.CuntzTensorQuotient.lift_cuntzS n
          (fun i => InfoGeometry.Topology.AlgebraicCuntzQuotient.S (R := ℂ) i)
          (fun i => InfoGeometry.Topology.AlgebraicCuntzQuotient.T (R := ℂ) i)
          (fun i j => InfoGeometry.Topology.AlgebraicCuntzQuotient.T_mul_S i j)
          (InfoGeometry.Topology.AlgebraicCuntzQuotient.partition_one (R := ℂ)) i
      · intro i
        change tensorQuotientToLetterQuotient n
          (letterQuotientToTensorQuotient n
            (InfoGeometry.Topology.AlgebraicCuntzQuotient.T (R := ℂ) i)) = _
        rw [letterQuotientToTensorQuotient,
          InfoGeometry.Topology.AlgebraicCuntzQuotient.lift_T]
        exact InfoGeometry.Algebra.CuntzTensorQuotient.lift_cuntzSdag n
          (fun i => InfoGeometry.Topology.AlgebraicCuntzQuotient.S (R := ℂ) i)
          (fun i => InfoGeometry.Topology.AlgebraicCuntzQuotient.T (R := ℂ) i)
          (fun i j => InfoGeometry.Topology.AlgebraicCuntzQuotient.T_mul_S i j)
          (InfoGeometry.Topology.AlgebraicCuntzQuotient.partition_one (R := ℂ)) i
    _ = AlgHom.id ℂ _ := by
      symm
      exact InfoGeometry.Topology.AlgebraicCuntzQuotient.lift_unique
        (R := ℂ)
        (s := InfoGeometry.Topology.AlgebraicCuntzQuotient.S (R := ℂ))
        (t := InfoGeometry.Topology.AlgebraicCuntzQuotient.T (R := ℂ))
        (InfoGeometry.Topology.AlgebraicCuntzQuotient.T_mul_S)
        (InfoGeometry.Topology.AlgebraicCuntzQuotient.partition_one (R := ℂ))
        (AlgHom.id ℂ _)
        (by intro i; rfl)
        (by intro i; rfl)

/-- The two finite algebraic presentations are isomorphic as complex algebras.
This equivalence is built from their quotient universal properties and the
proved inverse laws; it asserts nothing about C⋆ completions or representations. -/
noncomputable def cuntzQuotientAlgEquiv (n : ℕ) :
    InfoGeometry.Algebra.CuntzTensorQuotient.CuntzAlg n ≃ₐ[ℂ]
      InfoGeometry.Topology.AlgebraicCuntzQuotient.CuntzAlg ℂ (Fin n) :=
  AlgEquiv.ofAlgHom (tensorQuotientToLetterQuotient n)
    (letterQuotientToTensorQuotient n)
    (tensorToLetter_comp_letterToTensor n)
    (letterToTensor_comp_tensorToLetter n)

end InfoGeometry.Algebra.CuntzTensorQuotientComparison
