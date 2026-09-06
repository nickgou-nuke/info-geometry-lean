import proofs.CStarCuntzTensorQuotient
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

namespace ComplexStarCuntzRedesign

open scoped TensorProduct
open AlgebraicCuntzQuotient

/-! ## Real source star as a real star module -/

instance realCuntzStarModule {ι : Type*} [Fintype ι] [DecidableEq ι] :
    StarModule ℝ (CuntzAlg ℝ ι) where
  star_smul r x := by
    simp [Algebra.smul_def, AlgebraicCuntzQuotient.star_mul,
      AlgebraicCuntzQuotient.star_algebraMap, Algebra.commutes]

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
  refine TensorProduct.induction_on x ?_ ?_ ?_
  · simp
  · intro w a
    change star (z * w) ⊗ₜ[ℝ] star a = (star z * star w) ⊗ₜ[ℝ] star a
    rw [StarMul.star_mul, mul_comm]
  · intro x y hx hy
    simp [hx, hy]

/-- Concrete sanity check: the redesigned source admits genuine complex
`StarAlgHom`s. -/
def idComplexStarAlgHom {ι : Type*} [Fintype ι] [DecidableEq ι] :
    ComplexStarCuntzAlg ι →⋆ₐ[ℂ] ComplexStarCuntzAlg ι :=
  StarAlgHom.id ℂ (ComplexStarCuntzAlg ι)

@[simp] theorem idComplexStarAlgHom_Sℂ {ι : Type*} [Fintype ι] [DecidableEq ι] (i : ι) :
    idComplexStarAlgHom (ι := ι) (Sℂ i) = Sℂ i := rfl

@[simp] theorem idComplexStarAlgHom_Tℂ {ι : Type*} [Fintype ι] [DecidableEq ι] (i : ι) :
    idComplexStarAlgHom (ι := ι) (Tℂ i) = Tℂ i := rfl

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

/-! ## True `StarAlgHom` representation interface -/

/-- A genuine complex `StarAlgHom` package for the complexified source.  The
full `map_star'` proof is the remaining induction-on-tensor-products step; the
source algebra and scalar law are now genuinely correct. -/
structure GenuineComplexCuntzStarRepresentation
    {ι A : Type*} [Fintype ι] [DecidableEq ι] [CStarAlgebra A]
    (F : CStarCuntzTensorQuotient.CStarCuntzFamily A ι) where
  map : ComplexStarCuntzAlg ι →⋆ₐ[ℂ] A
  map_S : ∀ i, map (Sℂ i) = F.S i
  map_T : ∀ i, map (Tℂ i) = star (F.S i)

#check ComplexStarCuntzAlg
#check Sℂ
#check Tℂ
#check star_Sℂ
#check star_Tℂ
#check star_algebraMap_complex
#check star_complex_smul
#check idComplexStarAlgHom
#check realLift
#check GenuineComplexCuntzStarRepresentation

end ComplexStarCuntzRedesign
