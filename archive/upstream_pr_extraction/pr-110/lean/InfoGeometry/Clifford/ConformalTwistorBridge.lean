import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import InfoGeometry.Clifford.HestenesOddSector
import InfoGeometry.Riemannian.CartanMetric

namespace InfoGeometry.Clifford.Conformal

open CliffordAlgebra
open InfoGeometry.Clifford.Hestenes
open InfoGeometry.Riemannian

variable {R : Type*} [CommRing R] [Invertible (2 : R)]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable (Q : QuadraticForm R M)

/--
The Conformal Dirac/Twistor Embedding:
A Minkowski vector x in the odd sector ClMinus(1,3) can be conformally lifted
into the projective null cone of a higher dimensional space Cl(2,4) or Cl(5,5).

We define the ConformalLift as a structure capturing the projective coordinate (infinity)
and the origin coordinate, bounding the physical vector x.
-/
structure ConformalTwistorLift where
  /-- The physical spacetime vector (odd sector) -/
  x_phys : ClMinus Q
  /-- The projective scale factor (e_infinity) -/
  scale_inf : R
  /-- The conformal origin component (e_origin) -/
  origin_comp : R

/--
The conformal null condition: a lift is a valid Twistor/null-cone representation
if its internal quadratic form evaluates to zero. 
In terms of the physical paravector X = x * γ₀, this corresponds to the determinant
matching the hyperbolic radius, mapping to the Jordan symmetric cone.
-/
def ConformalTwistorLift.isNull (T : ConformalTwistorLift Q) : Prop :=
  InfoGeometry.Riemannian.hTrace Q ⟨T.x_phys.val * T.x_phys.val, clMinus_mul_clMinus Q T.x_phys.val T.x_phys.val T.x_phys.property T.x_phys.property⟩ = T.scale_inf * T.origin_comp

/--
A conformal translation by a physical vector `a`.
In the Twistor / Conformal null cone embedding, this shifts the physical coordinate 
and updates the origin component to maintain the null boundary.
-/
def conformalTranslation (a : ClMinus Q) (T : ConformalTwistorLift Q) : ConformalTwistorLift Q :=
  { x_phys := ⟨T.x_phys.val + T.scale_inf • a.val, Submodule.add_mem _ T.x_phys.property (Submodule.smul_mem _ T.scale_inf a.property)⟩,
    scale_inf := T.scale_inf,
    origin_comp := T.origin_comp + InfoGeometry.Riemannian.hTrace Q ⟨T.x_phys.val * a.val + a.val * T.x_phys.val, 
      Submodule.add_mem _ (clMinus_mul_clMinus Q _ _ T.x_phys.property a.property) (clMinus_mul_clMinus Q _ _ a.property T.x_phys.property)⟩ + 
      T.scale_inf * InfoGeometry.Riemannian.hTrace Q ⟨a.val * a.val, clMinus_mul_clMinus Q _ _ a.property a.property⟩ }

/--
A Special Conformal Transformation (SCT) by a physical vector `b`.
In Twistor space, an SCT is the dual to translation, shifting the origin component
and coupling to the infinity scale.
-/
def conformalSCT (b : ClMinus Q) (T : ConformalTwistorLift Q) : ConformalTwistorLift Q :=
  { x_phys := ⟨T.x_phys.val + T.origin_comp • b.val, Submodule.add_mem _ T.x_phys.property (Submodule.smul_mem _ T.origin_comp b.property)⟩,
    scale_inf := T.scale_inf + InfoGeometry.Riemannian.hTrace Q ⟨T.x_phys.val * b.val + b.val * T.x_phys.val, 
      Submodule.add_mem _ (clMinus_mul_clMinus Q _ _ T.x_phys.property b.property) (clMinus_mul_clMinus Q _ _ b.property T.x_phys.property)⟩ + 
      T.origin_comp * InfoGeometry.Riemannian.hTrace Q ⟨b.val * b.val, clMinus_mul_clMinus Q _ _ b.property b.property⟩,
    origin_comp := T.origin_comp }

end InfoGeometry.Clifford.Conformal
