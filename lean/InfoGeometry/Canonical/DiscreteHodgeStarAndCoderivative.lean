import InfoGeometry.Canonical.DiscreteDiracKahlerOperator
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Canonical

def discreteCodifferential
    (hodgeStar : StandardIntegralSplitOctonion → StandardIntegralSplitOctonion)
    (theta omega : StandardIntegralSplitOctonion) : StandardIntegralSplitOctonion :=
  hodgeStar (discreteExteriorDerivative theta (hodgeStar omega))

theorem discrete_codifferential_sq_zero
    (hodgeStar : StandardIntegralSplitOctonion → StandardIntegralSplitOctonion)
    (theta omega : StandardIntegralSplitOctonion)
    (hodgeStar_involution : ∀ x, hodgeStar (hodgeStar x) = x)
    (h_theta_sq : splitOctonionMul theta theta = (fun _ => 0))
    (h_assoc : ∀ x, splitOctonionMul theta (splitOctonionMul theta x) =
      splitOctonionMul (splitOctonionMul theta theta) x)
    (hodgeStar_zero : hodgeStar (fun _ => 0) = (fun _ => 0)) :
    discreteCodifferential hodgeStar theta
        (discreteCodifferential hodgeStar theta omega) = (fun _ => 0) := by
  unfold discreteCodifferential
  rw [hodgeStar_involution]
  have h_d2 :
      discreteExteriorDerivative theta
          (discreteExteriorDerivative theta (hodgeStar omega)) = (fun _ => 0) := by
    apply discrete_d_sq_zero_of_associative
    · exact h_theta_sq
    · exact h_assoc (hodgeStar omega)
  rw [h_d2]
  exact hodgeStar_zero

end InfoGeometry.Canonical
