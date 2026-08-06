import Mathlib.Algebra.Group.Defs
import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import InfoGeometry.Riemannian.ConeAction
import InfoGeometry.Clifford.HestenesNaturalConeStandardForm
import InfoGeometry.Clifford.HestenesOddSector

namespace InfoGeometry.Riemannian

open InfoGeometry.Clifford.Hestenes
open CliffordAlgebra

variable {R : Type*} [CommRing R] [Invertible (2 : R)]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable (Q : QuadraticForm R M)

class CartanGeometry (Q : QuadraticForm R M) where
  hTrace : ClPlus Q → R
  hTrace_add (A B : ClPlus Q) : hTrace (A + B) = hTrace A + hTrace B
  hTrace_one : hTrace 1 = 1
  hTrace_zero : hTrace 0 = 0
  hTrace_mul_comm (A B : ClPlus Q) : hTrace (A * B) = hTrace (B * A)
  hTrace_vect_eq_polar (u v : M) (V : ClPlus Q) (hV : V.val = ι Q u * ι Q v) : hTrace V = QuadraticMap.polar Q u v
  clInv (S : ClPlus Q) [Invertible S.val] : ClPlus Q
  clInv_val (S : ClPlus Q) [Invertible S.val] : (clInv S).val = ⅟(S.val)
  clExp (X : ClPlus Q) : ClPlus Q
  clSqrt (X : ClPlus Q) [Invertible X.val] : ClPlus Q
  clSqrt_sq (X : ClPlus Q) [Invertible X.val] : (clSqrt X).val * (clSqrt X).val = X.val
  clSqrt_invertible (X : ClPlus Q) [Invertible X.val] : Invertible (clSqrt X).val
  clExp_invertible (X : ClPlus Q) : Invertible (clExp X).val

variable [cg : CartanGeometry Q]

def hTrace (X : ClPlus Q) : R := CartanGeometry.hTrace X
theorem hTrace_add (A B : ClPlus Q) : hTrace Q (A + B) = hTrace Q A + hTrace Q B := CartanGeometry.hTrace_add A B
theorem hTrace_one : hTrace Q 1 = 1 := CartanGeometry.hTrace_one
theorem hTrace_zero : hTrace Q 0 = 0 := CartanGeometry.hTrace_zero
theorem hTrace_mul_comm (A B : ClPlus Q) : hTrace Q (A * B) = hTrace Q (B * A) := CartanGeometry.hTrace_mul_comm A B

def clInv (S : ClPlus Q) [Invertible S.val] : ClPlus Q := CartanGeometry.clInv S
def clExp (X : ClPlus Q) : ClPlus Q := CartanGeometry.clExp X
def clSqrt (X : ClPlus Q) [Invertible X.val] : ClPlus Q := CartanGeometry.clSqrt X

instance clSqrt_invertible (X : ClPlus Q) [Invertible X.val] : Invertible (clSqrt Q X).val := 
  CartanGeometry.clSqrt_invertible X

instance (X : ClPlus Q) : Invertible (clExp Q X).val := 
  CartanGeometry.clExp_invertible X

def cartanMetric (S : ClPlus Q) [Invertible S.val] (V1 V2 : ClPlus Q) : R :=
  hTrace Q (clInv Q S * V1 * clInv Q S * V2)

variable (v0 : M) (hv0_norm : Q v0 = 1)

class CartanGeometryWithAdjoint (Q : QuadraticForm R M) (v0 : M) [CartanGeometry Q] where
  hestenesAdjoint_inv (G : ClPlus Q) [Invertible G.val] [Invertible (hestenesAdjoint Q v0 G).val] :
    hestenesAdjoint Q v0 (clInv Q G) = clInv Q (hestenesAdjoint Q v0 G)
  cartanMetric_invariance (G : ClPlus Q) [Invertible G.val] [Invertible (hestenesAdjoint Q v0 G).val]
    (S : ClPlus Q) [Invertible S.val] [Invertible (coneConjugationAction Q v0 G S).val]
    (V1 V2 : ClPlus Q) :
    hTrace Q (clInv Q (coneConjugationAction Q v0 G S) * coneConjugationAction Q v0 G V1 * clInv Q (coneConjugationAction Q v0 G S) * coneConjugationAction Q v0 G V2) = 
    hTrace Q (clInv Q S * V1 * clInv Q S * V2)

variable [cga : CartanGeometryWithAdjoint Q v0]

theorem hestenesAdjoint_inv (G : ClPlus Q) [Invertible G.val] [Invertible (hestenesAdjoint Q v0 G).val] :
  hestenesAdjoint Q v0 (clInv Q G) = clInv Q (hestenesAdjoint Q v0 G) := 
  CartanGeometryWithAdjoint.hestenesAdjoint_inv G

theorem cartanMetric_invariance (G : ClPlus Q) [Invertible G.val] [Invertible (hestenesAdjoint Q v0 G).val]
    (S : ClPlus Q) [Invertible S.val] [Invertible (coneConjugationAction Q v0 G S).val]
    (V1 V2 : ClPlus Q) :
    cartanMetric Q (coneConjugationAction Q v0 G S) (coneConjugationAction Q v0 G V1) (coneConjugationAction Q v0 G V2) = 
    cartanMetric Q S V1 V2 := by
  apply CartanGeometryWithAdjoint.cartanMetric_invariance G S V1 V2

noncomputable def cartanGeodesicMap (S : ClPlus Q) [Invertible S.val] (V : ClPlus Q) (t : R) : ClPlus Q :=
  let S_half := clSqrt Q S
  let S_half_inv := clInv Q S_half
  let V_scaled := clExp Q (t • (S_half_inv * V * S_half_inv))
  S_half * V_scaled * S_half

noncomputable instance cartanGeodesic_complete (S : ClPlus Q) [Invertible S.val] (V : ClPlus Q) (t : R) :
    Invertible (cartanGeodesicMap Q S V t).val := by
  dsimp [cartanGeodesicMap]
  let A := clSqrt Q S
  let B := clExp Q (t • (clInv Q A * V * clInv Q A))
  haveI hA : Invertible A.val := inferInstance
  haveI hB : Invertible B.val := inferInstance
  haveI hAB : Invertible (A.val * B.val) := Invertible.mul hA hB
  exact Invertible.mul hAB hA

end InfoGeometry.Riemannian
