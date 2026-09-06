import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RingTheory.TensorProduct.Basic
import InfoGeometry.Physics.ChiralCausalCone
import InfoGeometry.Physics.ChiralTensorRecoupling

/-!
# The canonical finite chiral matrix representation

`Matrix.toLin'` is the native Mathlib representation of a square matrix as a
linear endomorphism of its column vectors.  This owner records the exact
carrier-level bridge needed before coupling the Pauli/TL algebra to token
dynamics; it makes no claim about an arbitrary graph carrier.
-/

namespace InfoGeometry.Physics

open ChiralCausalCone

abbrev ChiralCarrier := Fin 2 → ℂ
abbrev ChiralTensorCarrier := TensorProduct ℂ ChiralCarrier ChiralCarrier
abbrev ChiralMatrixTensor := TensorProduct ℂ M2C M2C

/- These are Mathlib's canonical algebraic tensor-product instances.  They
   are local because the same underlying tensor type is also used elsewhere
   as a purely linear carrier. -/
local instance chiralMatrixTensorSemiring : Semiring ChiralMatrixTensor :=
  Algebra.TensorProduct.instSemiring
local instance chiralMatrixTensorRing : Ring ChiralMatrixTensor :=
  Algebra.TensorProduct.instRing
local instance chiralMatrixTensorNonAssocSemiring : NonAssocSemiring ChiralMatrixTensor :=
  chiralMatrixTensorSemiring.toNonAssocSemiring
local instance chiralMatrixTensorNonUnitalNonAssocSemiring :
    NonUnitalNonAssocSemiring ChiralMatrixTensor :=
  chiralMatrixTensorSemiring.toNonUnitalNonAssocSemiring
local instance chiralMatrixTensorAlgebra : Algebra ℂ ChiralMatrixTensor :=
  Algebra.TensorProduct.instAlgebra

def chiralMatrixAction : M2C →ₗ[ℂ] (ChiralCarrier →ₗ[ℂ] ChiralCarrier) :=
  (Matrix.toLin' : M2C ≃ₗ[ℂ] (ChiralCarrier →ₗ[ℂ] ChiralCarrier)).toLinearMap

@[simp] theorem chiralMatrixAction_apply (A : M2C) (v : ChiralCarrier) :
    chiralMatrixAction A v = Matrix.mulVec A v := by
  rfl

theorem chiralMatrixAction_mul (A B : M2C) :
    chiralMatrixAction (A * B) =
      (chiralMatrixAction A).comp (chiralMatrixAction B) := by
  exact Matrix.mulVecLin_mul A B

theorem chiralMatrixAction_one :
    chiralMatrixAction (1 : M2C) = LinearMap.id := by
  exact Matrix.mulVecLin_one

noncomputable def chiralTensorMatrixAction (A B : M2C) :
    ChiralTensorCarrier →ₗ[ℂ] ChiralTensorCarrier :=
  TensorProduct.map (chiralMatrixAction A) (chiralMatrixAction B)

@[simp] theorem chiralTensorMatrixAction_tmul
    (A B : M2C) (u v : ChiralCarrier) :
    chiralTensorMatrixAction A B (u ⊗ₜ[ℂ] v) =
      chiralMatrixAction A u ⊗ₜ[ℂ] chiralMatrixAction B v := by
  rfl

theorem chiralTensorMatrixAction_comp_tmul
    (A A' B B' : M2C) (u v : ChiralCarrier) :
    chiralTensorMatrixAction (A * A') (B * B') (u ⊗ₜ[ℂ] v) =
      (chiralTensorMatrixAction A B)
        (chiralTensorMatrixAction A' B' (u ⊗ₜ[ℂ] v)) := by
  simp only [chiralTensorMatrixAction_tmul, chiralMatrixAction_mul,
    LinearMap.comp_apply]

noncomputable def chiralMatrixTensorAction :
    ChiralMatrixTensor →ₗ[ℂ]
      (ChiralTensorCarrier →ₗ[ℂ] ChiralTensorCarrier) :=
  TensorProduct.lift
    { toFun := fun A =>
        { toFun := fun B => chiralTensorMatrixAction A B
          map_add' := by
            intro B C
            ext u
            simp [chiralTensorMatrixAction, TensorProduct.tmul_add]
          map_smul' := by
            intro c B
            ext u
            simp [chiralTensorMatrixAction] }
      map_add' := by
        intro A B
        ext C u
        simp [chiralTensorMatrixAction, TensorProduct.add_tmul]
      map_smul' := by
        intro c A
        ext B u
        simp [chiralTensorMatrixAction, TensorProduct.smul_tmul] }

@[simp] theorem chiralMatrixTensorAction_tmul
    (A B : M2C) :
    chiralMatrixTensorAction (A ⊗ₜ[ℂ] B) = chiralTensorMatrixAction A B := by
  exact TensorProduct.lift.tmul _ _

theorem chiralMatrixTensorAction_mul_tmul
    (A A' B B' : M2C) :
    chiralMatrixTensorAction ((A ⊗ₜ[ℂ] B) * (A' ⊗ₜ[ℂ] B')) =
      (chiralTensorMatrixAction A B).comp
        (chiralTensorMatrixAction A' B') := by
  rw [Algebra.TensorProduct.tmul_mul_tmul]
  apply LinearMap.ext
  intro u
  induction u using TensorProduct.induction_on with
  | zero => simp
  | add u v hu hv =>
      rw [map_add, map_add, hu, hv]
  | tmul u v =>
      simp only [chiralMatrixTensorAction_tmul, chiralTensorMatrixAction_tmul,
        LinearMap.comp_apply, chiralMatrixAction_mul]

theorem chiralMatrixTensorAction_mul (x y : ChiralMatrixTensor) :
    chiralMatrixTensorAction (x * y) =
      (chiralMatrixTensorAction x).comp (chiralMatrixTensorAction y) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x₁ x₂ hx₁ hx₂ =>
      rw [add_mul, map_add, hx₁, hx₂]
      ext u
      simp [LinearMap.add_apply, LinearMap.comp_apply]
  | tmul A B =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | add y₁ y₂ hy₁ hy₂ =>
          rw [mul_add, map_add, hy₁, hy₂]
          ext u
          simp [LinearMap.add_apply, LinearMap.comp_apply]
      | tmul A' B' =>
          exact chiralMatrixTensorAction_mul_tmul A A' B B'

theorem chiralTLGeneratorAction_sq :
    (chiralMatrixTensorAction ChiralTensorRecoupling.e).comp
        (chiralMatrixTensorAction ChiralTensorRecoupling.e) =
      (2 : ℂ) • chiralMatrixTensorAction ChiralTensorRecoupling.e := by
  rw [← chiralMatrixTensorAction_mul]
  rw [ChiralTensorRecoupling.e_sq]
  simp

noncomputable def chiralTLProjector : ChiralTensorCarrier →ₗ[ℂ] ChiralTensorCarrier :=
  (1 / 2 : ℂ) • chiralMatrixTensorAction ChiralTensorRecoupling.e

theorem chiralTLProjector_idempotent :
    (chiralTLProjector).comp chiralTLProjector = chiralTLProjector := by
  unfold chiralTLProjector
  rw [LinearMap.smul_comp, LinearMap.comp_smul, smul_smul,
    chiralTLGeneratorAction_sq]
  norm_num [smul_smul]

end InfoGeometry.Physics
