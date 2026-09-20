import InfoGeometry.LatticeGauge.FiniteGibbsModel
import InfoGeometry.Probability.FiniteResamplingSpectrum

noncomputable section

namespace InfoGeometry.LatticeGauge

open InfoGeometry.Inference InfoGeometry.Probability.FiniteResamplingGap

variable {Vertex Edge Face Gauge : Type*}
variable [Fintype Edge] [DecidableEq Edge] [Fintype Face]
variable [Group Gauge] [Fintype Gauge] [DecidableEq Gauge]

def equilibriumKernel (lattice : PlaquetteLattice Vertex Edge Face) (beta : ℝ) :
    Configuration Edge Gauge → Configuration Edge Gauge → ℝ :=
  resamplingKernel (equilibriumWeight lattice beta)

def equilibriumHamiltonian (lattice : PlaquetteLattice Vertex Edge Face) (beta : ℝ) :
    Module.End ℝ (Configuration Edge Gauge → ℝ) :=
  hamiltonian (equilibriumWeight lattice beta)

theorem equilibriumKernel_pos (lattice : PlaquetteLattice Vertex Edge Face) (beta : ℝ)
    (source target : Configuration Edge Gauge) :
    0 < equilibriumKernel lattice beta source target :=
  equilibriumWeight_pos lattice beta target

theorem equilibriumKernel_stochastic (lattice : PlaquetteLattice Vertex Edge Face) (beta : ℝ)
    (source : Configuration Edge Gauge) :
    ∑ target, equilibriumKernel lattice beta source target = 1 :=
  resampling_stochastic _ (equilibriumWeight_sum_one lattice beta) source

theorem equilibriumKernel_detailed_balance (lattice : PlaquetteLattice Vertex Edge Face)
    (beta : ℝ) (source target : Configuration Edge Gauge) :
    equilibriumWeight lattice beta source * equilibriumKernel lattice beta source target =
      equilibriumWeight lattice beta target * equilibriumKernel lattice beta target source :=
  resampling_detailed_balance _ source target

theorem equilibriumKernel_stationary (lattice : PlaquetteLattice Vertex Edge Face) (beta : ℝ)
    (target : Configuration Edge Gauge) :
    ∑ source, equilibriumWeight lattice beta source * equilibriumKernel lattice beta source target =
      equilibriumWeight lattice beta target :=
  resampling_stationary _ (equilibriumWeight_sum_one lattice beta) target

theorem equilibriumHamiltonian_self_adjoint (lattice : PlaquetteLattice Vertex Edge Face)
    (beta : ℝ) (observable test : Configuration Edge Gauge → ℝ) :
    pairing (equilibriumWeight lattice beta) observable (equilibriumHamiltonian lattice beta test) =
      pairing (equilibriumWeight lattice beta) (equilibriumHamiltonian lattice beta observable) test :=
  hamiltonian_self_adjoint _ observable test

theorem equilibrium_dirichlet_eq_variance (lattice : PlaquetteLattice Vertex Edge Face)
    (beta : ℝ) (observable : Configuration Edge Gauge → ℝ) :
    dirichletEnergy (equilibriumWeight lattice beta) (equilibriumKernel lattice beta) observable =
      weightedVariance (equilibriumWeight lattice beta) observable :=
  resampling_dirichlet_eq_variance _ observable (equilibriumWeight_sum_one lattice beta)

theorem equilibrium_poincare_gap_one (lattice : PlaquetteLattice Vertex Edge Face)
    (beta : ℝ) (observable : Configuration Edge Gauge → ℝ) :
    1 * weightedVariance (equilibriumWeight lattice beta) observable ≤
      pairing (equilibriumWeight lattice beta) observable
        (equilibriumHamiltonian lattice beta observable) :=
  poincare_gap_one _ observable (equilibriumWeight_sum_one lattice beta)

theorem equilibriumHamiltonian_spectrum [Nonempty Edge] [Nontrivial Gauge]
    (lattice : PlaquetteLattice Vertex Edge Face) (beta : ℝ) :
    spectrum ℝ (equilibriumHamiltonian lattice beta (Gauge := Gauge)) = {0, 1} :=
  hamiltonian_spectrum_eq _ (equilibriumWeight_sum_one lattice beta)

end InfoGeometry.LatticeGauge
