import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.OperatorAlgebra.SheetConnection

namespace InfoGeometry.OperatorAlgebra

/-- Sum/Difference Coupling (Mari Geometry).
    Creates sum and difference connections for the L and R sheets. -/
def sumConnection {A : Type*} [Add A] (Γ_L Γ_R : SheetConnection A) : SheetConnection A where
  Γ u v := Γ_L.Γ u v + Γ_R.Γ u v
  α := Γ_L.α + Γ_R.α

def diffConnection {A : Type*} [Add A] [Sub A] (Γ_L Γ_R : SheetConnection A) : SheetConnection A where
  Γ u v := Γ_L.Γ u v - Γ_R.Γ u v
  α := Γ_L.α - Γ_R.α

end InfoGeometry.OperatorAlgebra
