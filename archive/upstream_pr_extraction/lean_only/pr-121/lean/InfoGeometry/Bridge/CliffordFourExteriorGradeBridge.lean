import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.LinearAlgebra.ExteriorAlgebra.Grading

/-!
# Four-dimensional Clifford symbol grade ledger

The associated graded vector space of a four-dimensional complex Clifford
symbol algebra is the exterior algebra on `Fin 4 → ℂ`.  This file proves the
homogeneous dimensions `1, 4, 6, 4, 1`, the even/odd dimensions `8 + 8`,
and the total dimension `16` using Mathlib's exterior-power bases.

This is an exterior-degree ledger.  It deliberately does not identify these
five degrees with a Kantor/TKK Lie five-grading, and it does not assert a
Clifford-algebra equivalence without a separately chosen quadratic form and
filtered/graded comparison map.
-/

namespace InfoGeometry.Bridge.CliffordFourExteriorGradeBridge

abbrev V4 := Fin 4 → ℂ

noncomputable def vBasis : Module.Basis (Fin 4) ℂ V4 :=
  Pi.basisFun ℂ (Fin 4)

noncomputable def degreeBasis (k : ℕ) :
    Module.Basis (Set.powersetCard (Fin 4) k) ℂ (⋀[ℂ]^k V4) :=
  vBasis.exteriorPower k

instance degree_finiteDimensional (k : ℕ) :
    FiniteDimensional ℂ (⋀[ℂ]^k V4) :=
  Module.Basis.finiteDimensional_of_finite (degreeBasis k)

/-- Native homogeneous dimension formula for the four-dimensional exterior
symbol grades. -/
theorem exteriorDegree_finrank (k : ℕ) :
    Module.finrank ℂ (⋀[ℂ]^k V4) = Nat.choose 4 k := by
  rw [exteriorPower.finrank_eq]
  simp [V4]

theorem exteriorDegree_zero_finrank :
    Module.finrank ℂ (⋀[ℂ]^0 V4) = 1 := by
  rw [exteriorDegree_finrank]
  norm_num

theorem exteriorDegree_one_finrank :
    Module.finrank ℂ (⋀[ℂ]^1 V4) = 4 := by
  rw [exteriorDegree_finrank]
  norm_num

theorem exteriorDegree_two_finrank :
    Module.finrank ℂ (⋀[ℂ]^2 V4) = 6 := by
  rw [exteriorDegree_finrank]
  norm_num

theorem exteriorDegree_three_finrank :
    Module.finrank ℂ (⋀[ℂ]^3 V4) = 4 := by
  rw [exteriorDegree_finrank]
  norm_num

theorem exteriorDegree_four_finrank :
    Module.finrank ℂ (⋀[ℂ]^4 V4) = 1 := by
  rw [exteriorDegree_finrank]
  norm_num

/-- The five exterior symbol grades have dimensions `1,4,6,4,1`. -/
theorem exteriorDegree_dimension_packet :
    Module.finrank ℂ (⋀[ℂ]^0 V4) = 1 ∧
    Module.finrank ℂ (⋀[ℂ]^1 V4) = 4 ∧
    Module.finrank ℂ (⋀[ℂ]^2 V4) = 6 ∧
    Module.finrank ℂ (⋀[ℂ]^3 V4) = 4 ∧
    Module.finrank ℂ (⋀[ℂ]^4 V4) = 1 :=
  ⟨exteriorDegree_zero_finrank, exteriorDegree_one_finrank,
    exteriorDegree_two_finrank, exteriorDegree_three_finrank,
    exteriorDegree_four_finrank⟩

/-- Scalar, bivector, and pseudoscalar degrees form an eight-dimensional even
sector. -/
theorem even_exterior_dimension :
    Module.finrank ℂ (⋀[ℂ]^0 V4) +
      Module.finrank ℂ (⋀[ℂ]^2 V4) +
      Module.finrank ℂ (⋀[ℂ]^4 V4) = 8 := by
  rw [exteriorDegree_zero_finrank, exteriorDegree_two_finrank,
    exteriorDegree_four_finrank]

/-- Vector and trivector degrees form an eight-dimensional odd sector. -/
theorem odd_exterior_dimension :
    Module.finrank ℂ (⋀[ℂ]^1 V4) +
      Module.finrank ℂ (⋀[ℂ]^3 V4) = 8 := by
  rw [exteriorDegree_one_finrank, exteriorDegree_three_finrank]

noncomputable def exteriorAlgebraBasisSigma :
    Module.Basis
      (Σ k : ℕ, Set.powersetCard (Fin 4) k) ℂ
      (ExteriorAlgebra ℂ V4) :=
  (DirectSum.Decomposition.isInternal
      (ℳ := fun k : ℕ => ⋀[ℂ]^k V4)).collectedBasis
    (fun k => degreeBasis k)

noncomputable def exteriorAlgebraBasisFinset :
    Module.Basis (Finset (Fin 4)) ℂ (ExteriorAlgebra ℂ V4) :=
  exteriorAlgebraBasisSigma.reindex (Equiv.sigmaFiberEquiv Finset.card)

/-- The complete four-dimensional complex exterior symbol carrier has
dimension sixteen. -/
theorem exteriorAlgebra_finrank :
    Module.finrank ℂ (ExteriorAlgebra ℂ V4) = 16 := by
  rw [Module.finrank_eq_card_basis exteriorAlgebraBasisFinset]
  rw [Fintype.card_finset, Fintype.card_fin]
  norm_num

end InfoGeometry.Bridge.CliffordFourExteriorGradeBridge
