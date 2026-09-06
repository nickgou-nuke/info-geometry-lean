import InfoGeometry.OperatorAlgebra.D4StarCrossedProductNonUnitalStarSurface

/-!
# Continuity of coefficientwise crossed-product star homomorphisms

At the finite D₄ stage, an equivariant coefficient `StarAlgHom` acts
coefficientwise on the crossed-product carrier.  This owner records the
topological part of that action.  It does not identify the carrier with a
completion and does not install a C*-norm.
-/

namespace InfoGeometry.OperatorAlgebra.D4StarCrossedProductStarAlgHomContinuity

open InfoGeometry.OperatorAlgebra.D4StarFiniteCrossedProduct

noncomputable section

def continuousObservableStarAlgHom
    (Φ : EquivariantObservableMap) :
    Continuous (Φ.map : D4StarObservable → D4StarObservable) := by
  exact LinearMap.continuous_of_finiteDimensional Φ.map.toLinearMap

theorem continuous_crossedProductMap
    (Φ : EquivariantObservableMap) :
    Continuous (crossedProductMap Φ) := by
  apply continuous_pi
  intro r
  apply continuous_pi
  intro v
  exact (continuous_apply v).comp
    ((continuousObservableStarAlgHom Φ).comp (continuous_apply r))

end

end InfoGeometry.OperatorAlgebra.D4StarCrossedProductStarAlgHomContinuity
