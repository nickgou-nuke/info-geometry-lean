import InfoGeometry.Canonical.SU11MetriplecticCoadjointOrbit
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Concrete `SU(1,1)` KKS bridge

The existing Poincare-disk owner exposes the complex coordinate expression for
the Poisson tensor.  This file gives that expression a typed two-slot carrier
and transports its algebraic alternating identities without adding analytic
or Fisher-metric assumptions.
-/

namespace InfoGeometry.Canonical.SouriauSU11KKSBridge

open InfoGeometry.Canonical.SU11MetriplecticCoadjointOrbit

abbrev DerivativePair := ℂ × ℂ

noncomputable def poincareKKS (rho : ℝ) (u v : DerivativePair) : ℂ :=
  poincarePoissonBracket rho u.1 u.2 v.1 v.2

theorem poincareKKS_skew (rho : ℝ) (u v : DerivativePair) :
    poincareKKS rho u v = -poincareKKS rho v u := by
  exact poincarePoissonBracket_skew rho u.1 u.2 v.1 v.2

theorem poincareKKS_self (rho : ℝ) (u : DerivativePair) :
    poincareKKS rho u u = 0 := by
  exact poincarePoissonBracket_self rho u.1 u.2

theorem poincareKKS_add_left (rho : ℝ) (u₁ u₂ v : DerivativePair) :
    poincareKKS rho (u₁.1 + u₂.1, u₁.2 + u₂.2) v =
      poincareKKS rho u₁ v + poincareKKS rho u₂ v := by
  dsimp [poincareKKS, poincarePoissonBracket]
  ring

theorem poincareKKS_smul_left (rho : ℝ) (a : ℂ) (u v : DerivativePair) :
    poincareKKS rho (a * u.1, a * u.2) v =
      a * poincareKKS rho u v := by
  dsimp [poincareKKS, poincarePoissonBracket]
  ring

/- On each nonzero symplectic leaf, the concrete KKS expression is polynomial
  in the four complex derivative coordinates with a fixed nonzero scalar
  denominator. -/
theorem continuous_poincareKKS_of_ne_zero (rho : ℝ) (hrho : rho ≠ 0) :
    Continuous (fun q : ℂ × ℂ × ℂ × ℂ =>
      poincareKKS rho (q.1, q.2.1)
        (q.2.2.1, q.2.2.2)) := by
  unfold poincareKKS poincarePoissonBracket
  have hden : (2 * Complex.I * (rho : ℂ)) ≠ 0 := by
    norm_num [hrho]
  fun_prop (disch := aesop)

end InfoGeometry.Canonical.SouriauSU11KKSBridge
