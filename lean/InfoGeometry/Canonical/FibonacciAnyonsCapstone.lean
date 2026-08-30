import InfoGeometry.Topological.FibonacciAnyons

namespace InfoGeometry.Canonical.FibonacciAnyonsCapstone

open InfoGeometry.Topological.FibonacciAnyons

set_option linter.unusedVariables false

theorem verification_capstone :
    (phi ^ 2 = phi + 1) ∧
      (totalQuantumDimSq = 2 + phi) ∧
      (fibonacciFMatrix * fibonacciFMatrix = 1) ∧
      (fibonacciFMatrix.det = -1) ∧
      (‖braidPhaseVac‖ = 1 ∧ ‖braidPhaseTau‖ = 1) := by
  exact grand_fibonacci_anyons_synthesis

end InfoGeometry.Canonical.FibonacciAnyonsCapstone
