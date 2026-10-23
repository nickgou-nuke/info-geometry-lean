/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Physics.ComplexStarCuntzRedesign

/-!
# Algebraic comparison of the complexified and complex Cuntz presentations

This owner supplies the quotient comparison used by the corrected complex-* carrier.

Contract: for finite decidable `ι`, construct
`ComplexStarCuntzAlg ι ≃ₐ[ℂ] CuntzAlg ℂ ι`, matching both S/T generators.
The owner `Topology.AlgebraicCuntzQuotient` supplies `lift`, `lift_S`,
`lift_T`, `lift_unique`, `T_mul_S`, and `partition_one`. Mathlib supplies
`AlgHom.liftEquiv` and `Algebra.TensorProduct.ext_ring`.
Both inverse laws below follow from these universal properties.

This is only an algebra equivalence. The target's existing formal star fixes
complex scalars, whereas the source's star conjugates them. No compatibility
of those stars, positive state, KMS state, or completion is asserted.
For `ι = Fin n`, composition with `CuntzTensorQuotientComparison` permits
transport from the tensor presentation; word-span transport is downstream.
-/

noncomputable section

namespace InfoGeometry.Algebra.CuntzComplexification

open scoped TensorProduct
open InfoGeometry.Topology.AlgebraicCuntzQuotient
open InfoGeometry.Physics.ComplexStarCuntzRedesign

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Generator extensionality, derived from the quotient's universal property. -/
theorem quotientHom_ext {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
    (f g : CuntzAlg R ι →ₐ[R] A)
    (hS : ∀ i, f (S i) = g (S i)) (hT : ∀ i, f (T i) = g (T i)) : f = g := by
  have ho : ∀ i j, g (T i) * g (S j) = if i = j then 1 else 0 := by
    intro i j
    rw [← map_mul, T_mul_S]
    split_ifs <;> simp
  have hp : (∑ i, g (S i) * g (T i)) = 1 := by
    simpa only [map_sum, map_mul, map_one] using
      congrArg g (partition_one (R := R) (ι := ι))
  exact (lift_unique (fun i => g (S i)) (fun i => g (T i)) ho hp f hS hT).trans
    (lift_unique (fun i => g (S i)) (fun i => g (T i)) ho hp g
      (fun _ => rfl) (fun _ => rfl)).symm

-- The imported complex-to-real algebra is restriction along ℝ → ℂ.
-- Supply its tower explicitly, without requiring a Ring instance on CuntzAlg.
local instance complexQuotientTower : IsScalarTower ℝ ℂ (CuntzAlg ℂ ι) :=
  IsScalarTower.of_algebraMap_eq (fun _ => rfl)

/-- Change the coefficients of the real presentation to complex coefficients. -/
def realToLetter : CuntzAlg ℝ ι →ₐ[ℝ] CuntzAlg ℂ ι :=
  lift (R := ℝ) (S (R := ℂ)) (T (R := ℂ))
    (T_mul_S (R := ℂ)) (partition_one (R := ℂ))

/-- Extend the real coefficient map by the tensor-product universal property. -/
def toLetter : ComplexStarCuntzAlg ι →ₐ[ℂ] CuntzAlg ℂ ι :=
  (realToLetter (ι := ι)).liftEquiv ℝ ℂ (CuntzAlg ℝ ι) (CuntzAlg ℂ ι)

@[simp] theorem toLetter_tmul (z : ℂ) (a : CuntzAlg ℝ ι) :
    toLetter (z ⊗ₜ[ℝ] a) = z • realToLetter a :=
  AlgHom.liftEquiv_tmul _ _ _

@[simp] theorem toLetter_S (i : ι) : toLetter (Sℂ i) = S (R := ℂ) i := by
  simp [Sℂ, realToLetter, lift_S]

@[simp] theorem toLetter_T (i : ι) : toLetter (Tℂ i) = T (R := ℂ) i := by
  simp [Tℂ, realToLetter, lift_T]

/-- Tensor inclusion preserves the orthogonality relation. -/
theorem complexified_ortho (i j : ι) :
    Tℂ i * Sℂ j = if i = j then 1 else 0 := by
  have h := congrArg
    (Algebra.TensorProduct.includeRight : CuntzAlg ℝ ι →ₐ[ℝ] ComplexStarCuntzAlg ι)
    (T_mul_S (R := ℝ) i j)
  simpa [Sℂ, Tℂ, Algebra.TensorProduct.one_def] using h

/-- Tensor inclusion preserves the partition relation. -/
theorem complexified_partition : (∑ i : ι, Sℂ i * Tℂ i) = 1 := by
  have h := congrArg
    (Algebra.TensorProduct.includeRight : CuntzAlg ℝ ι →ₐ[ℝ] ComplexStarCuntzAlg ι)
    (partition_one (R := ℝ) (ι := ι))
  simpa [Sℂ, Tℂ, Algebra.TensorProduct.one_def] using h

/-- The complex quotient maps back by its defining Cuntz family. -/
def fromLetter : CuntzAlg ℂ ι →ₐ[ℂ] ComplexStarCuntzAlg ι :=
  lift (R := ℂ) Sℂ Tℂ complexified_ortho complexified_partition

@[simp] theorem fromLetter_S (i : ι) : fromLetter (S (R := ℂ) i) = Sℂ i := by
  exact lift_S Sℂ Tℂ complexified_ortho complexified_partition i

@[simp] theorem fromLetter_T (i : ι) : fromLetter (T (R := ℂ) i) = Tℂ i := by
  exact lift_T Sℂ Tℂ complexified_ortho complexified_partition i

/-- The composite on the complex letter quotient is the identity. -/
theorem toLetter_comp_fromLetter :
    (toLetter (ι := ι)).comp fromLetter = AlgHom.id ℂ (CuntzAlg ℂ ι) := by
  apply quotientHom_ext
  · intro i
    change toLetter (fromLetter (S (R := ℂ) i)) = S (R := ℂ) i
    simp
  · intro i
    change toLetter (fromLetter (T (R := ℂ) i)) = T (R := ℂ) i
    simp

/-- Tensor extensionality reduces the other inverse law to real generators. -/
theorem fromLetter_comp_toLetter :
    (fromLetter (ι := ι)).comp toLetter = AlgHom.id ℂ (ComplexStarCuntzAlg ι) := by
  apply Algebra.TensorProduct.ext_ring
  apply quotientHom_ext
  · intro i
    change fromLetter (toLetter (Sℂ i)) = Sℂ i
    simp
  · intro i
    change fromLetter (toLetter (Tℂ i)) = Tℂ i
    simp

/-- Canonical complex algebra equivalence, with no assertion about stars. -/
def complexificationAlgEquiv : ComplexStarCuntzAlg ι ≃ₐ[ℂ] CuntzAlg ℂ ι :=
  AlgEquiv.ofAlgHom toLetter fromLetter toLetter_comp_fromLetter fromLetter_comp_toLetter

@[simp] theorem complexificationAlgEquiv_S (i : ι) :
    complexificationAlgEquiv (Sℂ i) = S (R := ℂ) i := toLetter_S i

@[simp] theorem complexificationAlgEquiv_T (i : ι) :
    complexificationAlgEquiv (Tℂ i) = T (R := ℂ) i := toLetter_T i

@[simp] theorem complexificationAlgEquiv_symm_S (i : ι) :
    complexificationAlgEquiv.symm (S (R := ℂ) i) = Sℂ i := fromLetter_S i

@[simp] theorem complexificationAlgEquiv_symm_T (i : ι) :
    complexificationAlgEquiv.symm (T (R := ℂ) i) = Tℂ i := fromLetter_T i

end InfoGeometry.Algebra.CuntzComplexification
