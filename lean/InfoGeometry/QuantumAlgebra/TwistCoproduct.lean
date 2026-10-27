import Mathlib

/-!
# Native bialgebra tensor units: twisted coproduct and triangular R

Equations (3.3)--(3.5) of arXiv:2601.19983v1. Multiplicativity of the conjugated
coproduct and triangularity use only invertibility. Coassociativity additionally
requires the Drinfel'd cocycle and is not claimed from a bare tensor unit.
-/
noncomputable section
namespace InfoGeometry.QuantumAlgebra.TwistCoproduct
open scoped TensorProduct
variable {R H : Type*} [CommRing R] [Ring H] [Bialgebra R H]

/-- The paper's F Delta(x) F^-1, on the actual native bialgebra tensor product. -/
def coproduct (F : (H ⊗[R] H)ˣ) : H →ₐ[R] H ⊗[R] H where
  toFun x := (F : H ⊗[R] H) * Bialgebra.comulAlgHom R H x * ↑F⁻¹
  map_one' := by simp
  map_mul' x y := by simp [mul_assoc]
  map_zero' := by simp
  map_add' x y := by simp [mul_add, add_mul]
  commutes' r := by
    rw [(Bialgebra.comulAlgHom R H).commutes]
    rw [← (Algebra.commutes r (F : H ⊗[R] H)).eq]
    simp [mul_assoc]

@[simp] theorem coproduct_apply (F : (H ⊗[R] H)ˣ) (x : H) :
    coproduct F x = (F : H ⊗[R] H)*Coalgebra.comul x*↑F⁻¹ := rfl

theorem untwist_coproduct (F : (H ⊗[R] H)ˣ) (x : H) :
    (↑F⁻¹ : H ⊗[R] H)*coproduct F x*↑F=Coalgebra.comul x := by
  simp [coproduct_apply, mul_assoc]

/-- Tensor exchange is an algebra equivalence even when H is noncommutative. -/
abbrev flip : H ⊗[R] H ≃ₐ[R] H ⊗[R] H := Algebra.TensorProduct.comm R H H

theorem flip_involutive (x : H ⊗[R] H) : flip (flip x)=x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp
  | add a b ha hb => simp [ha, hb]

/-- R = F_op F^-1, represented as an actual unit. -/
def rUnit (F : (H ⊗[R] H)ˣ) : (H ⊗[R] H)ˣ :=
  Units.map (flip (R := R) (H := H)).toAlgHom.toMonoidHom F * F⁻¹

@[simp] theorem rUnit_val (F : (H ⊗[R] H)ˣ) :
    (rUnit F : H ⊗[R] H) = flip (F : H ⊗[R] H) * (↑F⁻¹ : H ⊗[R] H) := rfl

/-- The triangular equation R_op R=1; it does not assert Yang--Baxter by itself. -/
theorem triangular_left (F : (H ⊗[R] H)ˣ) :
    flip (rUnit F : H ⊗[R] H)*(rUnit F : H ⊗[R] H)=1 := by
  rw [rUnit_val, map_mul, flip_involutive]
  calc
    (F : H ⊗[R] H)*flip (↑F⁻¹ : H ⊗[R] H)*
        (flip (F : H ⊗[R] H)*(↑F⁻¹ : H ⊗[R] H)) =
      (F : H ⊗[R] H)*flip ((↑F⁻¹ : H ⊗[R] H)*(F : H ⊗[R] H))*(↑F⁻¹ : H ⊗[R] H) := by
        rw [map_mul]
        simp only [mul_assoc]
    _ = 1 := by simp

theorem triangular_right (F : (H ⊗[R] H)ˣ) :
    (rUnit F : H ⊗[R] H)*flip (rUnit F : H ⊗[R] H)=1 := by
  have h := congrArg (flip (R := R) (H := H)) (triangular_left F)
  simpa only [map_mul, flip_involutive, map_one] using h

end InfoGeometry.QuantumAlgebra.TwistCoproduct
