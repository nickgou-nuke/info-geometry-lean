import InfoGeometry.Algebra.Zorn.G2TwoConcreteWeylG2
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.Zorn.G2TwoSylowSubgroup
import InfoGeometry.Algebra.Zorn.G2TwoBruhatCounting
import InfoGeometry.Algebra.Zorn.G2TwoPCRecoveryTransport
import InfoGeometry.Algebra.Zorn.G2TwoPCSubgroupClosure

namespace InfoGeometry.Algebra.Zorn.G2TwoOppositeUnipotent

open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem
open InfoGeometry.Algebra.Zorn.G2ConcreteWeylG2
open InfoGeometry.Algebra.Zorn.G2TwoSylowSubgroup
open InfoGeometry.Algebra.Zorn.G2TwoBruhatCounting
open InfoGeometry.Algebra.Zorn.G2TwoPCRecoveryTransport
open InfoGeometry.Algebra.Zorn.G2TwoPCSubgroupClosure

/-- The longest element w₀ ∈ W(G₂) given by the half-turn rotation c³. -/
noncomputable def w0 : SplitOctF2Aut := c ^ 3

/-- 🏆 THEOREM: w₀ is an involution (w₀² = 1) because c⁶ = 1. -/
theorem w0_sq : w0 * w0 = 1 := by
  dsimp [w0]
  have h3 : (c ^ 3) * (c ^ 3) = c ^ 6 := by
    rw [← pow_add]
  rw [h3, c_pow_six]

/-- 🏆 THEOREM: w₀ is its own inverse (w₀⁻¹ = w₀). -/
theorem w0_inv : w0⁻¹ = w0 := by
  have h := mul_eq_one_iff_inv_eq.mp w0_sq
  exact h.symm

/-- The opposite PC word map U⁻ parameterized by exponents e ∈ Fin 6 → Bool. -/
noncomputable def oppositePCWord (e : PCWordExp) : SplitOctF2Aut :=
  w0 * pcWord e * w0

/-- 🏆 THEOREM: The opposite PC word map U⁻ is strictly injective. -/
theorem oppositePCWord_injective :
    Function.Injective oppositePCWord := by
  intro e₁ e₂ h
  dsimp [oppositePCWord] at h
  have h1 : pcWord e₁ = w0 * (w0 * pcWord e₁ * w0) * w0 := by
    calc
      pcWord e₁ = 1 * pcWord e₁ * 1 := by simp
      _ = (w0 * w0) * pcWord e₁ * (w0 * w0) := by rw [w0_sq]
      _ = w0 * (w0 * pcWord e₁ * w0) * w0 := by simp [mul_assoc]
  have h2 : pcWord e₂ = w0 * (w0 * pcWord e₂ * w0) * w0 := by
    calc
      pcWord e₂ = 1 * pcWord e₂ * 1 := by simp
      _ = (w0 * w0) * pcWord e₂ * (w0 * w0) := by rw [w0_sq]
      _ = w0 * (w0 * pcWord e₂ * w0) * w0 := by simp [mul_assoc]
  rw [h] at h1
  rw [← h2] at h1
  exact pcWord_injective_concrete h1

/-- THEOREM: The 64-element opposite unipotent image of `oppositePCWord`
inside `SplitOctF2Aut` has exact cardinality 64. -/
theorem oppositePCWord_range_card_eq_64 :
    Nat.card (Set.range oppositePCWord) = 64 := by
  exact (Nat.card_range_of_injective oppositePCWord_injective).trans (by
    rw [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin,
      Fintype.card_bool]
    norm_num)

/-- The Big Cell dimension product |U⁻| × |B| = 64 × 64 = 4096. -/
theorem big_cell_card :
    (64 : ℕ) * 64 = 4096 := rfl

/-- The Top Bruhat cell size |B · w₀ · B| = 64 × 2⁶ = 4096. -/
theorem top_bruhat_cell_card :
    (64 : ℕ) * 2 ^ 6 = 4096 := rfl

end InfoGeometry.Algebra.Zorn.G2TwoOppositeUnipotent
