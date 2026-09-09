import Mathlib.Tactic
import InfoGeometry.Canonical.RelativeModularHamiltonian
import InfoGeometry.Canonical.SplitCartanChiralNilpotentBlock

/-!
# Finite `Fin 2` readout of the canonical relative modular operator

This is an interoperability layer only.  The generic projective positive-ray
owners remain authoritative for `Δ` and its logarithmic surprisal; the explicit
2-by-2 split-Cartan block is used only as a finite coordinate readout.
-/

open scoped BigOperators

namespace InfoGeometry.Canonical.SplitCartanRelativeModularTwoByTwoBridge

open InfoGeometry.Canonical.PositiveRayCore
open InfoGeometry.Canonical.RelativePotentialCore
open InfoGeometry.Canonical.RelativeModularOperator
open InfoGeometry.Canonical.RelativeModularHamiltonian

abbrev Two := Fin 2
abbrev FinTwoMatrix := Matrix Two Two ℝ

theorem relativeModularOperator_fin_two_readout
    (q q0 : PositiveRay Two) :
    relativeModularOperator q q0 =
      !![relativeDensity q q0 0, 0;
         0, relativeDensity q q0 1] := by
  ext i j
  fin_cases i <;> fin_cases j
  · change relativeModularOperator q q0 0 0 = relativeDensity q q0 0
    exact relativeModularOperator_diag q q0 0
  · change relativeModularOperator q q0 0 1 = 0
    exact relativeModularOperator_offdiag q q0 (by decide)
  · change relativeModularOperator q q0 1 0 = 0
    exact relativeModularOperator_offdiag q q0 (by decide)
  · change relativeModularOperator q q0 1 1 = relativeDensity q q0 1
    exact relativeModularOperator_diag q q0 1

theorem relativeSurprisalOperator_fin_two_readout
    (q q0 : PositiveRay Two) :
    relativeModularHamiltonianOperator q q0 =
      !![relativeModularPotential q q0 0, 0;
         0, relativeModularPotential q q0 1] := by
  ext i j
  fin_cases i <;> fin_cases j
  · change relativeModularHamiltonianOperator q q0 0 0 = relativeModularPotential q q0 0
    exact relativeModularHamiltonianOperator_diag q q0 0
  · change relativeModularHamiltonianOperator q q0 0 1 = 0
    exact relativeModularHamiltonianOperator_offdiag q q0 (by decide)
  · change relativeModularHamiltonianOperator q q0 1 0 = 0
    exact relativeModularHamiltonianOperator_offdiag q q0 (by decide)
  · change relativeModularHamiltonianOperator q q0 1 1 = relativeModularPotential q q0 1
    exact relativeModularHamiltonianOperator_diag q q0 1

theorem relativeModularVolumeShadow_fin_two_readout
  (q q0 : PositiveRay Two) :
    relativeModularVolumeShadow q q0 =
      relativeDensity q q0 0 * relativeDensity q q0 1 := by
  rw [relativeModularVolumeShadow_eq_prod_relativeDensity]
  exact Fin.prod_univ_two (f := fun i : Fin 2 => relativeDensity q q0 i)

theorem relativeSurprisal_trace_fin_two_readout
    (q q0 : PositiveRay Two) :
    Matrix.trace (relativeModularHamiltonianOperator q q0) =
      relativeModularPotential q q0 0 + relativeModularPotential q q0 1 := by
  rw [Matrix.trace]
  simp only [Fin.sum_univ_two]
  change relativeModularHamiltonianOperator q q0 0 0 +
      relativeModularHamiltonianOperator q q0 1 1 =
    relativeModularPotential q q0 0 + relativeModularPotential q q0 1
  rw [relativeModularHamiltonianOperator_diag, relativeModularHamiltonianOperator_diag]

end InfoGeometry.Canonical.SplitCartanRelativeModularTwoByTwoBridge
