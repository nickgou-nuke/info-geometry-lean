/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Physics.CStarCuntzTensorQuotient
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.Algebra.Star.TensorProduct
import Mathlib.LinearAlgebra.Complex.Module

/-!
# Genuine complex star redesign for the algebraic Cuntz source

Mathlib's bundled `StarAlgHom R A B` is `R`-linear and star-preserving.  For
`R = ℂ`, this is correct for C*-algebra morphisms: the map is complex-linear,
while the star operation on both source and target is conjugate-semilinear.

Therefore the source star must satisfy

`star (algebraMap ℂ A z) = algebraMap ℂ A (star z)`.

The earlier quotient `CuntzAlg ℂ ι` carried a formal `ℂ`-linear star, so it fixed
complex scalars.  This file gives a genuine replacement: complexify the real
algebraic Cuntz quotient,

`ComplexStarCuntzAlg ι = ℂ ⊗[ℝ] CuntzAlg ℝ ι`.

The tensor-product star is `star z ⊗ star x`, so complex scalars conjugate by
construction, while the real Cuntz star still swaps `Sᵢ` and `Tᵢ`.
-/

noncomputable section

namespace InfoGeometry.Physics.ComplexStarCuntzRedesign

open scoped TensorProduct
open MulOpposite
open InfoGeometry.Topology.AlgebraicCuntzQuotient

/-! ## Real source star as a real star module -/

instance realCuntzStarModule {ι : Type*} [Fintype ι] [DecidableEq ι] :
    StarModule ℝ (CuntzAlg ℝ ι) where
  star_smul r x := by
    simp [Algebra.smul_def, InfoGeometry.Topology.AlgebraicCuntzQuotient.star_mul,
      InfoGeometry.Topology.AlgebraicCuntzQuotient.star_algebraMap, Algebra.commutes]

/-! ## Genuine complexified Cuntz star algebra -/

/-- The genuine complex star source: complexification of the real algebraic
Cuntz quotient. -/
abbrev ComplexStarCuntzAlg (ι : Type*) [Fintype ι] [DecidableEq ι] :=
  ℂ ⊗[ℝ] CuntzAlg ℝ ι

/-- Complexified Cuntz creation generator. -/
def Sℂ {ι : Type*} [Fintype ι] [DecidableEq ι] (i : ι) : ComplexStarCuntzAlg ι :=
  (1 : ℂ) ⊗ₜ[ℝ] S (R := ℝ) i

/-- Complexified Cuntz annihilation/formal-adjoint generator. -/
def Tℂ {ι : Type*} [Fintype ι] [DecidableEq ι] (i : ι) : ComplexStarCuntzAlg ι :=
  (1 : ℂ) ⊗ₜ[ℝ] T (R := ℝ) i

@[simp] theorem star_Sℂ {ι : Type*} [Fintype ι] [DecidableEq ι] (i : ι) :
    star (Sℂ i) = Tℂ i := by
  simp [Sℂ, Tℂ]

@[simp] theorem star_Tℂ {ι : Type*} [Fintype ι] [DecidableEq ι] (i : ι) :
    star (Tℂ i) = Sℂ i := by
  simp [Sℂ, Tℂ]

/-- Complex scalars are conjugated by the source star. -/
@[simp] theorem star_algebraMap_complex {ι : Type*} [Fintype ι] [DecidableEq ι] (z : ℂ) :
    star (algebraMap ℂ (ComplexStarCuntzAlg ι) z) =
      algebraMap ℂ (ComplexStarCuntzAlg ι) (star z) := by
  simp

/-- Equivalent scalar-smul form of conjugate semilinearity. -/
@[simp] theorem star_complex_smul {ι : Type*} [Fintype ι] [DecidableEq ι]
    (z : ℂ) (x : ComplexStarCuntzAlg ι) :
    star (z • x) = star z • star x := by
  refine TensorProduct.inductionOn x (fun w a => ?_) (fun x y hx hy => ?_)
  ·
    change star (z * w) ⊗ₜ[ℝ] star a = (star z * star w) ⊗ₜ[ℝ] star a
    rw [StarMul.star_mul, mul_comm]
  · simp [hx, hy]

/-- Concrete sanity check: the redesigned source admits genuine complex
`StarAlgHom`s. -/
def idComplexStarAlgHom {ι : Type*} [Fintype ι] [DecidableEq ι] :
    ComplexStarCuntzAlg ι →⋆ₐ[ℂ] ComplexStarCuntzAlg ι :=
  StarAlgHom.id ℂ (ComplexStarCuntzAlg ι)

@[simp] theorem idComplexStarAlgHom_Sℂ {ι : Type*} [Fintype ι] [DecidableEq ι] (i : ι) :
    idComplexStarAlgHom (ι := ι) (Sℂ i) = Sℂ i := rfl

@[simp] theorem idComplexStarAlgHom_Tℂ {ι : Type*} [Fintype ι] [DecidableEq ι] (i : ι) :
    idComplexStarAlgHom (ι := ι) (Tℂ i) = Tℂ i := rfl

/-! ## Constructive star-preserving lift -/

/-- The adjoint, viewed as a real algebra homomorphism into the opposite
algebra of a complex C⋆-algebra. -/
private def cstarStarToOpposite {A : Type*} [CStarAlgebra A] :
    A →ₐ[ℝ] Aᵐᵒᵖ where
  toFun a := op (star a)
  map_one' := by simp
  map_mul' a b := by simp [StarMul.star_mul]
  map_zero' := by simp
  map_add' a b := by simp
  commutes' r := by
    change op (star (algebraMap ℝ A r)) = algebraMap ℝ Aᵐᵒᵖ r
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one]
    simp [star_smul]

/-! ## Real Cuntz families inside complex C*-algebras -/

/-- A C*-Cuntz family whose generators satisfy the Cuntz relations.  This is the
same relation package as `CStarCuntzFamily`, but exposed here to build the real
star representation first and then complexify it. -/
abbrev RealCuntzLiftTarget (A ι : Type*) [Fintype ι] [DecidableEq ι] [CStarAlgebra A] :=
  CuntzAlg ℝ ι →ₐ[ℝ] A

/-- The real algebraic Cuntz quotient maps into any complex C*-Cuntz family by
forgetting scalars from `ℂ` to `ℝ`. -/
def realLift {ι A : Type*} [Fintype ι] [DecidableEq ι] [CStarAlgebra A]
    (F : CStarCuntzTensorQuotient.CStarCuntzFamily A ι) : RealCuntzLiftTarget A ι :=
  lift (R := ℝ) (A := A) F.S (fun i => star (F.S i))
    F.ortho
    F.partition

@[simp] theorem realLift_S {ι A : Type*} [Fintype ι] [DecidableEq ι] [CStarAlgebra A]
    (F : CStarCuntzTensorQuotient.CStarCuntzFamily A ι) (i : ι) :
    realLift F (S (R := ℝ) i) = F.S i := by
  exact lift_S (R := ℝ) (A := A) F.S (fun i => star (F.S i)) F.ortho F.partition i

@[simp] theorem realLift_T {ι A : Type*} [Fintype ι] [DecidableEq ι] [CStarAlgebra A]
    (F : CStarCuntzTensorQuotient.CStarCuntzFamily A ι) (i : ι) :
    realLift F (T (R := ℝ) i) = star (F.S i) := by
  exact lift_T (R := ℝ) (A := A) F.S (fun i => star (F.S i)) F.ortho F.partition i

/-- The real lift preserves star on Cuntz generators. -/
@[simp] theorem realLift_star_S {ι A : Type*} [Fintype ι] [DecidableEq ι] [CStarAlgebra A]
    (F : CStarCuntzTensorQuotient.CStarCuntzFamily A ι) (i : ι) :
    realLift F (star (S (R := ℝ) i)) = star (realLift F (S (R := ℝ) i)) := by
  simp

@[simp] theorem realLift_star_T {ι A : Type*} [Fintype ι] [DecidableEq ι] [CStarAlgebra A]
    (F : CStarCuntzTensorQuotient.CStarCuntzFamily A ι) (i : ι) :
    realLift F (star (T (R := ℝ) i)) = star (realLift F (T (R := ℝ) i)) := by
  simp

private def realLiftAfterStarToOpposite {ι A : Type*} [Fintype ι] [DecidableEq ι]
    [CStarAlgebra A] (F : CStarCuntzTensorQuotient.CStarCuntzFamily A ι) :
    CuntzAlg ℝ ι →ₐ[ℝ] Aᵐᵒᵖ where
  toFun x := op (realLift F (star x))
  map_one' := by simp
  map_mul' x y := by
    simp only [InfoGeometry.Topology.AlgebraicCuntzQuotient.star_mul,
      map_mul, op_mul]
  map_zero' := by simp
  map_add' x y := by simp
  commutes' r := by
    change op (realLift F (star (algebraMap ℝ (CuntzAlg ℝ ι) r))) =
      algebraMap ℝ Aᵐᵒᵖ r
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one]
    simp [star_smul]

/-- The real universal Cuntz lift intertwines the formal quotient adjoint with
the actual C⋆-adjoint on every quotient element. -/
theorem realLift_map_star {ι A : Type*} [Fintype ι] [DecidableEq ι]
    [CStarAlgebra A] (F : CStarCuntzTensorQuotient.CStarCuntzFamily A ι)
    (x : CuntzAlg ℝ ι) :
    realLift F (star x) = star (realLift F x) := by
  let g := (cstarStarToOpposite (A := A)).comp (realLift F)
  have hgS : ∀ i, g (S (R := ℝ) i) = op (star (F.S i)) := by
    intro i
    simp [g, cstarStarToOpposite, realLift_S]
  have hgT : ∀ i, g (T (R := ℝ) i) = op (F.S i) := by
    intro i
    simp [g, cstarStarToOpposite, realLift_T]
  have hconditions : ∀ i j,
      op (F.S i) * op (star (F.S j)) = (if i = j then 1 else 0 : Aᵐᵒᵖ) := by
    intro i j
    apply unop_injective
    by_cases hij : i = j
    · subst j
      simpa using F.ortho i i
    · have hji : j ≠ i := fun h => hij h.symm
      simpa [hij, hji] using F.ortho j i
  have hpartition :
      (∑ i, op (star (F.S i)) * op (F.S i)) = (1 : Aᵐᵒᵖ) := by
    apply unop_injective
    simpa using F.partition
  have h := lift_unique (R := ℝ) (A := Aᵐᵒᵖ)
    (fun i => op (star (F.S i))) (fun i => op (F.S i))
    hconditions hpartition
    g hgS hgT
  have h' := lift_unique (R := ℝ) (A := Aᵐᵒᵖ)
    (fun i => op (star (F.S i))) (fun i => op (F.S i))
    hconditions hpartition (realLiftAfterStarToOpposite F)
    (by intro i; simp [realLiftAfterStarToOpposite, realLift_T])
    (by intro i; simp [realLiftAfterStarToOpposite, realLift_S])
  have hh := h.trans h'.symm
  have hx := congrArg (fun f : CuntzAlg ℝ ι →ₐ[ℝ] Aᵐᵒᵖ => f x) hh
  change op (star (realLift F x)) = op (realLift F (star x)) at hx
  exact (MulOpposite.op_injective hx).symm

/-! ## Extension to the complexification -/

/-- The algebra map induced on the complexification by the real universal
Cuntz lift. -/
def complexLift {ι A : Type*} [Fintype ι] [DecidableEq ι] [CStarAlgebra A]
    (F : CStarCuntzTensorQuotient.CStarCuntzFamily A ι) :
    ComplexStarCuntzAlg ι →ₐ[ℂ] A :=
  (realLift F).liftEquiv ℝ ℂ (CuntzAlg ℝ ι) A

/-- The complexified universal lift preserves star on every element of the
tensor product, not only on its Cuntz generators. -/
theorem complexLift_map_star {ι A : Type*} [Fintype ι] [DecidableEq ι]
    [CStarAlgebra A] (F : CStarCuntzTensorQuotient.CStarCuntzFamily A ι)
    (x : ComplexStarCuntzAlg ι) :
    complexLift F (star x) = star (complexLift F x) := by
  refine TensorProduct.inductionOn x (fun z a => ?_) (fun x y hx hy => ?_)
  · simp [complexLift, AlgHom.liftEquiv_tmul, realLift_map_star]
  · simp [map_add, hx, hy]

/-- A genuine complex star-algebra representation of the complexified Cuntz
quotient, constructed from a C⋆-Cuntz family. -/
def complexStarLift {ι A : Type*} [Fintype ι] [DecidableEq ι]
    [CStarAlgebra A] (F : CStarCuntzTensorQuotient.CStarCuntzFamily A ι) :
    ComplexStarCuntzAlg ι →⋆ₐ[ℂ] A where
  toAlgHom := complexLift F
  map_star' := complexLift_map_star F

@[simp] theorem complexStarLift_Sℂ {ι A : Type*} [Fintype ι] [DecidableEq ι]
    [CStarAlgebra A] (F : CStarCuntzTensorQuotient.CStarCuntzFamily A ι) (i : ι) :
    complexStarLift F (Sℂ i) = F.S i := by
  simp [complexStarLift, complexLift, Sℂ, realLift_S]

@[simp] theorem complexStarLift_Tℂ {ι A : Type*} [Fintype ι] [DecidableEq ι]
    [CStarAlgebra A] (F : CStarCuntzTensorQuotient.CStarCuntzFamily A ι) (i : ι) :
    complexStarLift F (Tℂ i) = star (F.S i) := by
  simp [complexStarLift, complexLift, Tℂ, realLift_T]

#check ComplexStarCuntzAlg
#check Sℂ
#check Tℂ
#check star_Sℂ
#check star_Tℂ
#check star_algebraMap_complex
#check star_complex_smul
#check idComplexStarAlgHom
#check realLift
#check complexLift
#check complexStarLift
#check complexStarLift_Sℂ
#check complexStarLift_Tℂ

end InfoGeometry.Physics.ComplexStarCuntzRedesign
