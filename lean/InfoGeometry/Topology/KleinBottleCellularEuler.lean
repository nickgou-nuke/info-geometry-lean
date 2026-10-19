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

def evenToOdd : EvenCells →ₗ[ℝ] OddCells := 0

def oddToEven : OddCells →ₗ[ℝ] EvenCells := 0

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

end InfoGeometry.Topology.KleinBottleCellularEuler
