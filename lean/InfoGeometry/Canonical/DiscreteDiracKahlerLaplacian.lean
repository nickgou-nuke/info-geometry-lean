import InfoGeometry.Canonical.DiscreteHodgeStarAndCoderivative
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.DiscreteDiracHodgeChiral

namespace InfoGeometry.Canonical

/-- 1. Пълен Дирак-Келеров Оператор D_θ(ω) = d_θ(ω) + δ_θ(ω) -/
def discreteDiracKahlerOperator
    (hodgeStar : StandardIntegralSplitOctonion → StandardIntegralSplitOctonion)
    (theta omega : StandardIntegralSplitOctonion) : StandardIntegralSplitOctonion :=
  discreteExteriorDerivative theta omega +
    discreteCodifferential hodgeStar theta omega

/-- 2. Дискретен Лапласиан на Ходж-де Рам Δ_HD(ω) = (d δ + δ d)(ω) -/
def discreteHodgeLaplacian
    (hodgeStar : StandardIntegralSplitOctonion → StandardIntegralSplitOctonion)
    (theta omega : StandardIntegralSplitOctonion) : StandardIntegralSplitOctonion :=
  discreteExteriorDerivative theta (discreteCodifferential hodgeStar theta omega) +
    discreteCodifferential hodgeStar theta (discreteExteriorDerivative theta omega)

/-- **Теорема за Разлагане на Дирак-Келер**: D_θ² = Δ_HD при d² = 0 и δ² = 0.
Доказателството е на функционално ниво, подготвяйки почвата за 
свързване с абстрактния пръстен `diracHodge` от `DiscreteDiracHodgeChiral`. -/
theorem dirac_kahler_square_eq_laplacian
    (hodgeStar : StandardIntegralSplitOctonion → StandardIntegralSplitOctonion)
    (theta omega : StandardIntegralSplitOctonion)
    (h_linear_d : ∀ a b,
      discreteExteriorDerivative theta (a + b) =
        discreteExteriorDerivative theta a + discreteExteriorDerivative theta b)
    (h_linear_delta : ∀ a b,
      discreteCodifferential hodgeStar theta (a + b) =
        discreteCodifferential hodgeStar theta a + discreteCodifferential hodgeStar theta b)
    (h_d_sq : discreteExteriorDerivative theta
        (discreteExteriorDerivative theta omega) = 0)
    (h_delta_sq : discreteCodifferential hodgeStar theta
        (discreteCodifferential hodgeStar theta omega) = 0) :
    discreteDiracKahlerOperator hodgeStar theta
        (discreteDiracKahlerOperator hodgeStar theta omega) =
      discreteHodgeLaplacian hodgeStar theta omega := by
  unfold discreteDiracKahlerOperator discreteHodgeLaplacian
  rw [h_linear_d, h_linear_delta]
  have hd0 : discreteExteriorDerivative theta (discreteExteriorDerivative theta omega) = 0 := h_d_sq
  have hδ0 : discreteCodifferential hodgeStar theta (discreteCodifferential hodgeStar theta omega) = 0 := h_delta_sq
  rw [hd0, hδ0]
  abel

/-- 
Бридж към `DiscreteDiracHodgeChiral.lean`:
Ако повдигнем `d` и `δ` до ендоморфизми `AddMonoid.End StandardIntegralSplitOctonion`,
можем да използваме директно `diracHodge_sq_eq_hodgeLaplacian`.
-/
def diracHodgeEndomorphismBridge
    (d cod : AddMonoid.End StandardIntegralSplitOctonion) :
    AddMonoid.End StandardIntegralSplitOctonion :=
  DiscreteDiracHodgeChiral.diracHodge d cod

end InfoGeometry.Canonical
