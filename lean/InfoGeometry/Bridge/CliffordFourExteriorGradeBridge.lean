import Mathlib.LinearAlgebra.ExteriorPower.Basis
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.LinearAlgebra.ExteriorAlgebra.Grading
import Mathlib.Data.Complex.Basic

/-! Exterior-degree dimensions for the four-dimensional complex symbol carrier.
This is deliberately an exterior grading, not a Lie or contact grading. -/

namespace InfoGeometry.Bridge.CliffordFourExteriorGradeBridge

abbrev V4 := InfoGeometry.Algebra.FiniteSpin.Vec4C

noncomputable def vBasis : Module.Basis (Fin 4) ℂ V4 := Pi.basisFun ℂ (Fin 4)

noncomputable def degreeBasis (k : ℕ) :
    Module.Basis (Set.powersetCard (Fin 4) k) ℂ (⋀[ℂ]^k V4) :=
  vBasis.exteriorPower k

instance degree_finiteDimensional (k : ℕ) :
    FiniteDimensional ℂ (⋀[ℂ]^k V4) :=
  Module.Basis.finiteDimensional_of_finite (degreeBasis k)

theorem exteriorDegree_finrank (k : ℕ) :
    Module.finrank ℂ (⋀[ℂ]^k V4) = Nat.choose 4 k := by
  rw [exteriorPower.finrank_eq]
  simp [V4]

theorem exteriorDegree_dimension_packet :
    Module.finrank ℂ (⋀[ℂ]^0 V4) = 1 ∧
    Module.finrank ℂ (⋀[ℂ]^1 V4) = 4 ∧
    Module.finrank ℂ (⋀[ℂ]^2 V4) = 6 ∧
    Module.finrank ℂ (⋀[ℂ]^3 V4) = 4 ∧
    Module.finrank ℂ (⋀[ℂ]^4 V4) = 1 := by
  rw [exteriorDegree_finrank, exteriorDegree_finrank, exteriorDegree_finrank,
    exteriorDegree_finrank, exteriorDegree_finrank]
  norm_num [Nat.choose]

theorem even_exterior_dimension :
    Module.finrank ℂ (⋀[ℂ]^0 V4) + Module.finrank ℂ (⋀[ℂ]^2 V4) +
      Module.finrank ℂ (⋀[ℂ]^4 V4) = 8 := by
  rw [exteriorDegree_finrank, exteriorDegree_finrank, exteriorDegree_finrank]
  norm_num [Nat.choose]

theorem odd_exterior_dimension :
    Module.finrank ℂ (⋀[ℂ]^1 V4) + Module.finrank ℂ (⋀[ℂ]^3 V4) = 8 := by
  rw [exteriorDegree_finrank, exteriorDegree_finrank]
  norm_num [Nat.choose]

noncomputable def exteriorAlgebraBasisFinset :
    Module.Basis (Finset (Fin 4)) ℂ (ExteriorAlgebra ℂ V4) := by
  let b := (DirectSum.Decomposition.isInternal
      (ℳ := fun k : ℕ => ⋀[ℂ]^k V4)).collectedBasis (fun k => degreeBasis k)
  exact b.reindex (Equiv.sigmaFiberEquiv Finset.card)

theorem exteriorAlgebra_finrank :
    Module.finrank ℂ (ExteriorAlgebra ℂ V4) = 16 := by
  rw [Module.finrank_eq_card_basis exteriorAlgebraBasisFinset]
  rw [Fintype.card_finset, Fintype.card_fin]
  norm_num

end InfoGeometry.Bridge.CliffordFourExteriorGradeBridge
