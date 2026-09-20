import InfoGeometry.Synthesis.ChiralSpinNetworkHDK
import InfoGeometry.Synthesis.CuntzKleinHDKInstance

namespace InfoGeometry.Synthesis.ChiralSpinNetworkHDKTests

open InfoGeometry.Synthesis.ChiralSpinNetworkHDK
open InfoGeometry.Topology.CantorBoundaryCuntzO2
open InfoGeometry.Topology.CantorBoundaryRealClockShift

example : (1 : BoundaryOperator ℝ) ∈ LinearMap.ker (residual shift clock phase) := by
  rw [mem_residual_kernel_iff]
  simp only [mul_one, phase, ← mul_assoc, clock_sq, one_mul]

example (state : BoundaryOperator ℝ)
    (member : state ∈ LinearMap.ker (residual shift clock phase)) :
    shift * shift * state = clock * clock * state := by
  have anticommutes : shift * clock = -(clock * shift) := by
    rw [clock_shift_weyl, neg_neg]
  have squared := first_order_kernel_le_second_order shift clock phase
    phase_sq anticommutes member
  change shift * shift * state - clock * clock * state = 0 at squared
  exact sub_eq_zero.mp squared

example {Carrier : Type*} [Ring Carrier] [Algebra ℝ Carrier]
    (difference coefficient phase : Carrier) :
    (0 : Carrier) ∈ LinearMap.ker (residual difference coefficient phase) :=
  (LinearMap.ker _).zero_mem

#print axioms residual_commutes_twist
#print axioms mem_kernel_iff_chiral_parts
#print axioms seam_solution_decomposition
#print axioms first_order_kernel_le_second_order

example : T 0 * CuntzDoubledHopping.doubledDifference * S 1 =
    CuntzKleinPropagation.branchDifference :=
  CuntzDoubledHopping.doubledDifference_readout

example : CuntzKleinHDKInstance.liftedGlide CuntzKleinHDKInstance.coefficient =
    -CuntzKleinHDKInstance.coefficient :=
  CuntzKleinHDKInstance.coefficient_odd

example (field : KleinBottleOrbitQuotient.KleinBrillouinQuotient → BoundaryOperator ℝ)
    (solution : field ∈ LinearMap.ker CuntzKleinHDKInstance.quotientResidual)
    (point : KleinBottleOrbitQuotient.KleinBrillouinQuotient) :
    CuntzDoubledHopping.doubledDifference * CuntzDoubledHopping.doubledDifference *
        field point = field point :=
  CuntzKleinHDKInstance.quotient_solution_square field solution point

#print axioms CuntzDoubledHopping.doubledDifference_readout
#print axioms CuntzDoubledHopping.doubledDifference_anticommutes_clock
#print axioms CuntzKleinHDKInstance.liftedGlide_involutive
#print axioms CuntzKleinHDKInstance.solution_covariance
#print axioms CuntzKleinHDKInstance.quotientResidual_is_descent
#print axioms CuntzKleinHDKInstance.quotient_solution_square

end InfoGeometry.Synthesis.ChiralSpinNetworkHDKTests
