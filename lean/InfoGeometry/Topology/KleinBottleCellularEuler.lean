/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.OperatorAlgebra.FiniteParityEulerPoincare
import InfoGeometry.Topology.KleinBottleCWChain

/-!
# A finite parity Euler calculation for the Klein-bottle polygon chain model

The standard one-vertex, two-edge, one-face polygon presentation has chain
carriers of ranks one, two, and one. This file groups those algebraic carriers
by parity and proves Euler--Poincaré using the repository's native
finite-dimensional complex API.

The two-periodic carrier is the parity grouping
`(C₀ ⊕ C₂, C₁)` of the degree-resolved algebraic chain model.  Its positive
differential is the modeled algebraic map `∂₂ : C₂ → C₁` and its negative
differential is `∂₁ : C₁ → C₀`, with zero `C₀`-component in the even carrier.
The degree-two map is derived from the relator exponent sums; this file does
not construct a CW attachment. Identifying the chain model with the orbit
quotient still requires a topological cellular comparison theorem.
-/

noncomputable section

namespace InfoGeometry.Topology.KleinBottleCellularEuler

open InfoGeometry.OperatorAlgebra.FiniteParityComplex
open InfoGeometry.Topology.KleinBottleCWChain

abbrev EvenCells := C0 × C2

/- The even-to-odd differential is the degree-two algebraic boundary from the
   relator exponent-sum model, after grouping degrees zero and two. -/
def evenToOdd : EvenCells →ₗ[ℝ] C1 where
  toFun x := boundary₂ x.2
  map_add' x y := by simp
  map_smul' c x := by simp

/- The odd-to-even differential is the degree-one algebraic boundary into
   `C₀`; the `C₂` component is zero. -/
def oddToEven : C1 →ₗ[ℝ] EvenCells where
  toFun x := (boundary₁ x, 0)
  map_add' x y := by simp
  map_smul' c x := by simp

def polygonParityComplex : TwoPeriodicComplex EvenCells C1 where
  dPlus := evenToOdd
  dMinus := oddToEven
  dMinus_comp_dPlus := by
    apply LinearMap.ext
    intro x
    change (boundary₁ (boundary₂ x.2), (0 : C2)) = 0
    apply Prod.ext
    · have h := congrArg (fun f : C2 →ₗ[ℝ] C0 => f x.2)
        boundary₁_comp_boundary₂
      simpa [LinearMap.comp_apply, evenToOdd, oddToEven] using h
    · rfl
  dPlus_comp_dMinus := by
    apply LinearMap.ext
    intro x
    change boundary₂ 0 = 0
    simp

/-- Euler–Poincaré equality for the actual two-periodic complex: the alternating
carrier-rank sum equals the alternating cohomology-rank sum. -/
theorem polygonEulerPoincare :
    (Module.finrank ℝ EvenCells : ℤ) - Module.finrank ℝ C1 =
      Module.finrank ℝ polygonParityComplex.PositiveCohomology -
        Module.finrank ℝ polygonParityComplex.NegativeCohomology := by
  exact TwoPeriodicComplex.eulerCharacteristic_eq polygonParityComplex

/-- The alternating cohomology-rank sum vanishes, by Euler–Poincaré and the
explicit rank calculation for the algebraic polygon chain model. -/
theorem polygonCohomologyEuler_zero :
    (Module.finrank ℝ polygonParityComplex.PositiveCohomology : ℤ) -
      Module.finrank ℝ polygonParityComplex.NegativeCohomology = 0 := by
  rw [← polygonEulerPoincare]
  norm_num [EvenCells, C0, C1, C2]

theorem evenToOdd_nonzero : evenToOdd ≠ 0 := by
  intro h
  let x : EvenCells := (0, fun _ => 1)
  have hz := congrArg (fun f : EvenCells →ₗ[ℝ] C1 => f x 1) h
  simp [x, evenToOdd, boundary₂] at hz

theorem evenToOdd_range_eq_polygonBoundary₂ :
    LinearMap.range evenToOdd = LinearMap.range boundary₂ := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x.2, rfl⟩
  · rintro ⟨x, rfl⟩
    exact ⟨(0, x), by simp [evenToOdd]⟩

theorem polygonBoundarySquared_zero :
    oddToEven.comp evenToOdd = 0 ∧ evenToOdd.comp oddToEven = 0 := by
  exact ⟨polygonParityComplex.dMinus_comp_dPlus,
    polygonParityComplex.dPlus_comp_dMinus⟩

end InfoGeometry.Topology.KleinBottleCellularEuler
