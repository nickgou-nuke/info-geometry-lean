import InfoGeometry.Canonical.PauliHestenesSpinMomentum
import InfoGeometry.Algebra.FiniteSpinAlgebra
namespace InfoGeometry.SignedNetwork.PauliContextBridge
noncomputable section
open InfoGeometry.Canonical.PauliHestenesSpinMomentum
open scoped Matrix
abbrev Mat2 := InfoGeometry.Algebra.FiniteSpin.Mat2C
def contextProjector (x y z : ℝ) : Mat2 := PauliParavector.pauliMatrix ⟨1/2,x/2,y/2,z/2⟩
theorem contextProjector_trace (x y z : ℝ) : Matrix.trace (contextProjector x y z) = 1 := by
  simp [contextProjector, PauliParavector.trace_pauliMatrix_eq_two_energy]
end
end InfoGeometry.SignedNetwork.PauliContextBridge
