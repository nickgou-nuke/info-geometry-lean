import InfoGeometry.LatticeGauge.FiniteResamplingDynamics
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.Perm.Fin

noncomputable section

namespace InfoGeometry.LatticeGauge.FiniteResamplingTests

open InfoGeometry.Inference InfoGeometry.Probability.FiniteResamplingGap

def square : PlaquetteLattice (Fin 4) (Fin 4) Unit where
  source := ![0, 1, 3, 0]
  target := ![1, 2, 2, 3]
  bottom := fun _ => 0
  right := fun _ => 1
  top := fun _ => 2
  left := fun _ => 3
  bottom_right := fun _ => rfl
  right_top := fun _ => rfl
  top_left := fun _ => rfl
  left_bottom := fun _ => rfl

abbrev NonabelianGauge := Equiv.Perm (Fin 3)
abbrev AbelianGauge := Multiplicative (ZMod 2)

example (links : Configuration (Fin 4) NonabelianGauge) :
    plaquetteHolonomy square links () = links 0 * links 1 * (links 2)⁻¹ * (links 3)⁻¹ := rfl

example : plaquetteAction square (fun _ => (1 : NonabelianGauge)) = 0 :=
  trivial_configuration_action square

example (links : Configuration (Fin 4) NonabelianGauge)
    (nonflat : plaquetteHolonomy square links () ≠ 1) :
    plaquetteAction square links = 1 := by
  simp [plaquetteAction, plaquetteCost, nonflat]

example (beta : ℝ) :
    ∑ links : Configuration (Fin 4) NonabelianGauge, equilibriumWeight square beta links = 1 :=
  equilibriumWeight_sum_one square beta

example (beta : ℝ) (gauge : Fin 4 → NonabelianGauge)
    (links : Configuration (Fin 4) NonabelianGauge) :
    equilibriumWeight square beta (gaugeTransform square gauge links) =
      equilibriumWeight square beta links :=
  equilibriumWeight_gauge_invariant square beta gauge links

example (beta : ℝ) (source target : Configuration (Fin 4) NonabelianGauge) :
    equilibriumWeight square beta source * equilibriumKernel square beta source target =
      equilibriumWeight square beta target * equilibriumKernel square beta target source :=
  equilibriumKernel_detailed_balance square beta source target

example (beta : ℝ) (observable : Configuration (Fin 4) NonabelianGauge → ℝ) :
    weightedVariance (equilibriumWeight square beta) observable ≤
      pairing (equilibriumWeight square beta) observable
        (equilibriumHamiltonian square beta observable) := by
  simpa using equilibrium_poincare_gap_one square beta observable

example (beta : ℝ) :
    spectrum ℝ (equilibriumHamiltonian square beta (Gauge := NonabelianGauge)) = {0, 1} :=
  equilibriumHamiltonian_spectrum square beta

example (beta : ℝ) :
    spectrum ℝ (equilibriumHamiltonian square beta (Gauge := AbelianGauge)) = {0, 1} :=
  equilibriumHamiltonian_spectrum square beta

example : hamiltonian (fun _ : Unit => (1 : ℝ)) = 0 := by
  ext observable state
  simp [hamiltonian_apply, weightedMean]

#print axioms InfoGeometry.LatticeGauge.plaquetteHolonomy_gauge_covariant
#print axioms InfoGeometry.LatticeGauge.equilibriumWeight_sum_one
#print axioms InfoGeometry.LatticeGauge.equilibrium_poincare_gap_one
#print axioms InfoGeometry.LatticeGauge.equilibriumHamiltonian_spectrum

end InfoGeometry.LatticeGauge.FiniteResamplingTests
