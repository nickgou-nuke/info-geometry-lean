import InfoGeometry.QuantumAlgebra.TwistCoproduct
import InfoGeometry.QuantumAlgebra.RepresentedTwistProduct
import InfoGeometry.Twistor.MeierVianaIncidence
import InfoGeometry.Twistor.PoincareFirstOrderTwist

/-!
# Source-aligned checks for Twisting Twistor space

The constructions target incidence, represented twist associativity, an exact
first-order polynomial deformation, and coefficient gauge calculus. They do not
identify this algebraic coverage with the paper's full action equivalence.
-/
noncomputable section
namespace InfoGeometry.Twistor.TwistingTwistorAudit
open scoped Matrix
open PenroseIncidence MeierViana PoincareFirstOrder
open InfoGeometry.QuantumAlgebra.FirstOrderTwist
open InfoGeometry.Optics.OperatorValuedConnection

example (l : Spinor2) : hat (hat l) = -l := hat_hat l
example (x : ComplexSpacetime) (l : Spinor2) :
    toPenroseConvention (paperIncidence x l)=incidenceLinearMap x l :=
  paper_to_existing_incidence x l
example (l m : Spinor2) (hl : l≠0) : reconstruct l m *ᵥ l=m := reconstruct_incidence l m hl
example : hbar*hbar=0 := hbar_square_zero
example : coordinate 0*coordinate 1=coordinate 1*coordinate 0 := left_fibre_commutes 0 1
example : coordinate 2*coordinate 1≠coordinate 1*coordinate 2 := fibre_not_central
example (x y z : TwistedCoordinates) : (x*y)*z=x*(y*z) := mul_assoc x y z

/-- The sign obstruction is nonzero in an associative matrix algebra, not only
as a formal expression. Inner differentiation gives an exact Leibniz map. -/
def matrixDerivative : Matrix (Fin 2) (Fin 2) ℤ →+ Matrix (Fin 2) (Fin 2) ℤ where
  toFun x := !![1,0;0,0]*x-x*!![1,0;0,0]
  map_zero' := by simp
  map_add' x y := by simp [mul_add, add_mul]; abel

def testDifferential (i : Fin 2) : Matrix (Fin 2) (Fin 2) ℤ →+ Matrix (Fin 2) (Fin 2) ℤ :=
  if i=0 then matrixDerivative else 0

def testField (i : Fin 2) : Matrix (Fin 2) (Fin 2) ℤ := if i=0 then 0 else !![0,0;1,0]

def testParameter : Matrix (Fin 2) (Fin 2) ℤ := !![0,1;0,0]

theorem printed_plus_sign_not_covariant :
    TwistedGauge.curvatureVariation testDifferential testField
      (TwistedGauge.plusVariation testDifferential testField testParameter) 0 1 ≠
    testParameter*curvature (TwistedGauge.connection testDifferential testField) () 0 1-
      curvature (TwistedGauge.connection testDifferential testField) () 0 1*testParameter := by
  intro h
  have hh := congrFun (congrFun h (0 : Fin 2)) (0 : Fin 2)
  norm_num [TwistedGauge.curvatureVariation, TwistedGauge.plusVariation,
    TwistedGauge.curvature_coeff, testDifferential, testField, testParameter,
    matrixDerivative, Matrix.mul_apply, Fin.sum_univ_two] at hh

#check InfoGeometry.QuantumAlgebra.TwistCoproduct.coproduct
#check InfoGeometry.QuantumAlgebra.TwistCoproduct.triangular_left
#check InfoGeometry.QuantumAlgebra.RepresentedTwist.InverseTwist.product_assoc
#check InfoGeometry.QuantumAlgebra.RepresentedTwist.InverseTwist.braiding_involutive
#check InfoGeometry.QuantumAlgebra.RepresentedTwist.InverseTwist.differential_product
#check Cocycle.classicalLimit
#check poincare_legs_commute
#check mixed_commutator
#check TwistedGauge.variation_covariance
#check TwistedGauge.bianchi
#check TwistedGauge.bf_with_central_volume
#check twisted_curvature_covariant
#check projectivePaperIncidence_injective
#check reconstruct_unique

end InfoGeometry.Twistor.TwistingTwistorAudit
