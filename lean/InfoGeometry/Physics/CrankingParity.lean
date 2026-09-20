import Mathlib

namespace InfoGeometry.Physics.CrankingParity

variable {Space : Type*} [AddCommGroup Space] [Module ℝ Space]

def routhian (hamiltonian angularMomentum : Space →ₗ[ℝ] Space) (speed : ℝ) :
    Space →ₗ[ℝ] Space :=
  hamiltonian - speed • angularMomentum

theorem routhian_commutes_parity
    (parity hamiltonian angularMomentum : Space →ₗ[ℝ] Space) (speed : ℝ)
    (energySymmetry : parity.comp hamiltonian = hamiltonian.comp parity)
    (momentumSymmetry : parity.comp angularMomentum = angularMomentum.comp parity) :
    parity.comp (routhian hamiltonian angularMomentum speed) =
      (routhian hamiltonian angularMomentum speed).comp parity := by
  ext vector
  have energy := congrArg (fun operator : Space →ₗ[ℝ] Space => operator vector)
    energySymmetry
  have momentum := congrArg (fun operator : Space →ₗ[ℝ] Space => operator vector)
    momentumSymmetry
  change parity (hamiltonian vector) = hamiltonian (parity vector) at energy
  change parity (angularMomentum vector) = angularMomentum (parity vector) at momentum
  simp only [routhian, LinearMap.comp_apply, LinearMap.sub_apply,
    LinearMap.smul_apply, map_sub, map_smul, energy, momentum]

theorem routhian_preserves_parity_eigenvectors
    (parity hamiltonian angularMomentum : Space →ₗ[ℝ] Space) (speed eigenvalue : ℝ)
    (energySymmetry : parity.comp hamiltonian = hamiltonian.comp parity)
    (momentumSymmetry : parity.comp angularMomentum = angularMomentum.comp parity)
    (vector : Space) (eigenvector : parity vector = eigenvalue • vector) :
    parity (routhian hamiltonian angularMomentum speed vector) =
      eigenvalue • routhian hamiltonian angularMomentum speed vector := by
  have commuting := congrArg (fun operator : Space →ₗ[ℝ] Space => operator vector)
    (routhian_commutes_parity parity hamiltonian angularMomentum speed
      energySymmetry momentumSymmetry)
  simpa only [LinearMap.comp_apply, eigenvector, map_smul] using commuting

theorem routhian_joint_eigenvector
    (hamiltonian angularMomentum : Space →ₗ[ℝ] Space) (speed energy spin : ℝ)
    (vector : Space) (energyEigenvector : hamiltonian vector = energy • vector)
    (spinEigenvector : angularMomentum vector = spin • vector) :
    routhian hamiltonian angularMomentum speed vector = (energy - speed * spin) • vector := by
  simp only [routhian, LinearMap.sub_apply, LinearMap.smul_apply,
    energyEigenvector, spinEigenvector, smul_smul, sub_smul]

end InfoGeometry.Physics.CrankingParity
