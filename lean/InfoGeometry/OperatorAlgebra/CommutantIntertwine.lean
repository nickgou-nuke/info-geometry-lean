import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.OperatorAlgebra.SheetConnection

open MulOpposite

namespace InfoGeometry.OperatorAlgebra

/-- Tomita modular conjugation intertwining L and R connections. -/
structure CommutantIntertwine (L R_alg : Type*) [Ring L] [Ring R_alg] where
  J : L ≃+* R_algᵐᵒᵖ
  Γ_L : SheetConnection L
  Γ_R : SheetConnection R_alg
  /-- J (Γ_L u v) = Γ_R (J u) (J v)
      Since J maps L to R_algᵐᵒᵖ, we carefully unop before applying Γ_R -/
  intertwine : ∀ u v : L, J (Γ_L.Γ u v) = op (Γ_R.Γ (unop (J u)) (unop (J v)))

end InfoGeometry.OperatorAlgebra
