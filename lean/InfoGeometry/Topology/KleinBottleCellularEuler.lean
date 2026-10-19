/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.OperatorAlgebra.FiniteParityEulerPoincare

/-!
# A finite cellular Euler calculation for the Klein-bottle cell counts

The standard one-vertex, two-edge, one-face cell count has even and odd
cellular ranks two and two.  This file proves the resulting Euler--Poincaré
identity using the repository's native finite-dimensional complex API.

The carrier below is a cellular rank model.  It is deliberately not asserted
to be the quotient `KleinBrillouinQuotient`; that identification requires a
separate cellular equivalence theorem.
-/

noncomputable section

namespace InfoGeometry.Topology.KleinBottleCellularEuler

open InfoGeometry.OperatorAlgebra.FiniteParityComplex

abbrev EvenCells := Fin 2 → ℝ
abbrev OddCells := Fin 2 → ℝ

/- The cellular boundary of the two one-cells is zero.  We retain two
   coordinates on the odd carrier so that the first is the one-cell and the
   second is the attaching-circle coordinate of the two-cell. -/
def evenToOdd : EvenCells →ₗ[ℝ] OddCells := 0

/- The two-cell attaches by the word `aba⁻¹b⁻¹` in the usual polygon model;
   after abelianisation its boundary is twice the `b`-edge.  The map below is
   the corresponding real cellular boundary. -/
def oddToEven : OddCells →ₗ[ℝ] EvenCells where
  toFun x := fun i => if i = 0 then 0 else 2 * x 0
  map_add' x y := by
    funext i
    by_cases hi : i = 0
    · simp [hi]
    · simp [hi]
      ring
  map_smul' c x := by
    funext i
    by_cases hi : i = 0
    · simp [hi]
    · simp [hi]
      ring

def cellularComplex : TwoPeriodicComplex EvenCells OddCells where
  dPlus := evenToOdd
  dMinus := oddToEven
  dMinus_comp_dPlus := by simp [evenToOdd, oddToEven]
  dPlus_comp_dMinus := by simp [evenToOdd, oddToEven]

theorem cellularEulerCharacteristic_zero :
    (Module.finrank ℝ EvenCells : ℤ) - Module.finrank ℝ OddCells = 0 := by
  have h := TwoPeriodicComplex.eulerCharacteristic_eq cellularComplex
  simpa [EvenCells, OddCells] using h

theorem cellularEulerPoincare_balance :
    Module.finrank ℝ EvenCells = Module.finrank ℝ OddCells := by
  have h := cellularEulerCharacteristic_zero
  exact_mod_cast (show (Module.finrank ℝ EvenCells : ℤ) =
    (Module.finrank ℝ OddCells : ℤ) by omega)

theorem oddToEven_nonzero : oddToEven ≠ 0 := by
  intro h
  let x : OddCells := fun i => if i = 0 then 1 else 0
  have hz := congrArg (fun f : OddCells →ₗ[ℝ] EvenCells => f x 1) h
  simp [x, oddToEven] at hz

theorem cellular_boundary_squared_zero :
    oddToEven.comp evenToOdd = 0 ∧ evenToOdd.comp oddToEven = 0 := by
  exact ⟨cellularComplex.dMinus_comp_dPlus, cellularComplex.dPlus_comp_dMinus⟩

end InfoGeometry.Topology.KleinBottleCellularEuler
