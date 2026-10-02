import InfoGeometry.Synthesis.ChiralSpinNetworkHDK
import InfoGeometry.Synthesis.CuntzDoubledHopping
import InfoGeometry.Topology.KleinPointwiseOperatorDescent
import Mathlib.Algebra.Algebra.Pi

noncomputable section

namespace InfoGeometry.Synthesis.CuntzKleinHDKInstance

open KleinBrillouinBase KleinBottleOrbitQuotient
open InfoGeometry.Topology.CantorBoundaryCuntzO2
open InfoGeometry.Topology.CantorBoundaryRealClockShift
open InfoGeometry.Topology.KleinPointwiseOperatorDescent
open InfoGeometry.Synthesis.CuntzDoubledHopping
open InfoGeometry.Synthesis.ChiralSpinNetworkHDK

abbrev Fields := BrillouinTorus → BoundaryOperator ℝ

def fibreReflection : BoundaryFunction ℝ ≃ₗ[ℝ] BoundaryFunction ℝ :=
  LinearEquiv.ofInvolutive shift (fun field => LinearMap.congr_fun shift_sq field)

def fibreTwist : BoundaryOperator ℝ ≃ₐ[ℝ] BoundaryOperator ℝ :=
  fibreReflection.conjAlgEquiv ℝ

@[simp] theorem fibreTwist_apply (operator : BoundaryOperator ℝ) :
    fibreTwist operator = shift * operator * shift := rfl

theorem fibreTwist_involutive : Function.Involutive fibreTwist := by
  intro operator
  simp only [fibreTwist_apply]
  calc
    shift * (shift * operator * shift) * shift =
        (shift * shift) * operator * (shift * shift) := by simp only [mul_assoc]
    _ = operator := by rw [shift_sq]; simp

theorem fibreTwist_difference : fibreTwist doubledDifference = doubledDifference := by
  rw [fibreTwist_apply, doubledDifference_commutes_shift.eq, mul_assoc, shift_sq, mul_one]

theorem fibreTwist_clock : fibreTwist clock = -clock := by
  have reversed : shift * clock = -(clock * shift) := by
    rw [clock_shift_weyl, neg_neg]
  rw [fibreTwist_apply, reversed, neg_mul, mul_assoc, shift_sq, mul_one]

theorem fibreTwist_shift : fibreTwist shift = shift := by
  rw [fibreTwist_apply, shift_sq, one_mul]

theorem fibreTwist_phase : fibreTwist phase = -phase := by
  simp only [phase, map_mul, fibreTwist_clock, fibreTwist_shift, neg_mul]

def liftedGlide : Fields ≃ₐ[ℝ] Fields :=
  (AlgEquiv.piCongrLeft' ℝ (fun _ : BrillouinTorus => BoundaryOperator ℝ)
    (torusGlide_involutive.toPerm torusGlide)).trans
      (AlgEquiv.piCongrRight (fun _ : BrillouinTorus => fibreTwist))

@[simp] theorem liftedGlide_apply (field : Fields) (point : BrillouinTorus) :
    liftedGlide field point = fibreTwist (field (torusGlide point)) := rfl

theorem liftedGlide_involutive : Function.Involutive liftedGlide := by
  intro field
  funext point
  simp only [liftedGlide_apply, torusGlide_involutive, fibreTwist_involutive]

def kleinInvolution :
    InfoGeometry.Canonical.KleinBottleTwistedCommutant.KleinInvolution Fields where
  toRingAut := liftedGlide.toRingEquiv
  involutive := liftedGlide_involutive

def difference : Fields := fun _ => doubledDifference
def coefficient : Fields := fun _ => clock
def bivector : Fields := fun _ => phase

theorem difference_fixed : liftedGlide difference = difference := by
  funext point
  exact fibreTwist_difference

theorem coefficient_odd : liftedGlide coefficient = -coefficient := by
  funext point
  exact fibreTwist_clock

theorem bivector_odd : liftedGlide bivector = -bivector := by
  funext point
  exact fibreTwist_phase

theorem difference_coefficient_anticommute :
    difference * coefficient = -(coefficient * difference) := by
  funext point
  exact doubledDifference_anticommutes_clock

theorem bivector_square : bivector * bivector = -1 := by
  funext point
  exact phase_sq

theorem solution_covariance (state : Fields)
    (equation : difference * state = coefficient * state * bivector) :
    difference * liftedGlide state = coefficient * liftedGlide state * bivector :=
  KleinDiracKahler.equation_covariant liftedGlide.toAlgHom.toRingHom
    difference coefficient bivector state difference_fixed coefficient_odd bivector_odd equation

theorem solution_square (state : Fields)
    (equation : difference * state = coefficient * state * bivector) :
    difference * difference * state = coefficient * coefficient * state :=
  CuntzKleinPropagation.square_equation_of_anticommute difference coefficient state bivector
    bivector_square difference_coefficient_anticommute equation

def quotientResidual : Module.End ℝ (KleinBrillouinQuotient → BoundaryOperator ℝ) :=
  descendedPointwise (residual doubledDifference clock phase)

theorem quotientResidual_is_descent :
    quotientResidual =
      InfoGeometry.Topology.KleinRealOperatorDescent.quotientOperator
        (residual difference coefficient bivector)
        (pointwise_preserves_invariants (residual doubledDifference clock phase)) := rfl

theorem quotient_solution_iff (field : KleinBrillouinQuotient → BoundaryOperator ℝ) :
    field ∈ LinearMap.ker quotientResidual ↔
      ∀ point, doubledDifference * field point = clock * field point * phase := by
  change field ∈ LinearMap.ker (descendedPointwise (residual doubledDifference clock phase)) ↔ _
  rw [descendedPointwise_kernel_iff]
  simp only [mem_residual_kernel_iff]

theorem quotient_solution_square (field : KleinBrillouinQuotient → BoundaryOperator ℝ)
    (solution : field ∈ LinearMap.ker quotientResidual) (point : KleinBrillouinQuotient) :
    doubledDifference * doubledDifference * field point = field point := by
  have squared := CuntzKleinPropagation.square_equation_of_anticommute
    doubledDifference clock (field point) phase phase_sq
    doubledDifference_anticommutes_clock ((quotient_solution_iff field).mp solution point)
  simpa only [clock_sq, one_mul] using squared

end InfoGeometry.Synthesis.CuntzKleinHDKInstance
