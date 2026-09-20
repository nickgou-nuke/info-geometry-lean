import InfoGeometry.Automorphic.RoelckeSelbergSpectral
import InfoGeometry.OperatorAlgebra.IntertwinedSpectralLowerBound

namespace InfoGeometry.Automorphic.CuspidalSpectralLowerBound

open SiegelResonance RoelckeSelbergSpectral
open InfoGeometry.OperatorAlgebra.IntertwinedSpectralLowerBound

variable {Bulk Boundary HeckeIndex Space : Type*}
  [AddCommGroup Bulk] [Module ℝ Bulk]
  [AddCommGroup Boundary] [Module ℝ Boundary]
  [NormedAddCommGroup Space] [InnerProductSpace ℝ Space]

theorem cuspidal_eigenspace_eq_bot_below_bound
    (splitting : SiegelEisensteinWitness Bulk Boundary)
    (spectral : RoelckeSelbergSpectralDatum splitting HeckeIndex)
    (target : Space →ₗ[ℝ] Space) (observation : Bulk →ₗ[ℝ] Space)
    (faithful : Function.Injective observation)
    (intertwines : observation.comp spectral.laplacian = target.comp observation)
    (lower : ℝ)
    (bound : ∀ vector, lower * inner ℝ vector vector ≤ inner ℝ vector (target vector))
    (eigenvalue : ℝ) (below : eigenvalue < lower) :
    cuspidalEigenspace splitting spectral.laplacian eigenvalue = ⊥ := by
  apply le_antisymm ?_ bot_le
  intro vector membership
  change vector = 0
  by_contra nonzero
  have visible : observation vector ≠ 0 := by
    intro vanished
    apply nonzero
    apply faithful
    simpa using vanished
  have eigen := (mem_cuspidalEigenspace_iff splitting spectral.laplacian
    eigenvalue vector).mp membership
  have lowerBound := lower_bound_of_intertwining spectral.laplacian target observation
    intertwines lower bound visible eigen.2
  exact (not_le_of_gt below) lowerBound

end InfoGeometry.Automorphic.CuspidalSpectralLowerBound
