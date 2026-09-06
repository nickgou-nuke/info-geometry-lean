import InfoGeometry.Physics.NuclearGradedBathCommutant
import InfoGeometry.Physics.NuclearHeisenbergChannelDecomposition
import InfoGeometry.Physics.NuclearSpinIsospinTensorRepresentation
import InfoGeometry.Physics.NuclearChargeExchangeBridge
import InfoGeometry.Physics.NuclearWignerSupermultipletSymmetry
import InfoGeometry.Physics.NuclearQuasiparticleCARBridge
import InfoGeometry.Physics.NuclearPhononRPAAlgebra
import InfoGeometry.Physics.SolovievQuasiparticlePhononEigenproblem
import InfoGeometry.Physics.SolovievProjectedParameterBridge
import InfoGeometry.Physics.SolovievTransitionStrength
import InfoGeometry.Physics.SolovievFiniteSecularEigenproblem
import InfoGeometry.Physics.SolovievInteractionParameterBridge
import InfoGeometry.Physics.NuclearFiniteCARProjection
import InfoGeometry.Physics.GammasphereZornMap
import InfoGeometry.Physics.NuclearCartanProjectorParityBridge
import InfoGeometry.Physics.NuclearFiniteCARCartanSolovievBridge
import InfoGeometry.Physics.NuclearParityGradedHamiltonian
import InfoGeometry.Physics.NuclearSolovievParitySymmetry
import InfoGeometry.Physics.NuclearSpectroscopyZ2GradingBridge
import InfoGeometry.Physics.NuclearQuantumNumberPacket
import InfoGeometry.Physics.NuclearRPAQuantumNumberSeparation
import InfoGeometry.Physics.NuclearCl55CartanParityDictionary
import InfoGeometry.Physics.NuclearWignerDensityProjectorBridge
import InfoGeometry.Physics.NuclearCartanGradeNormalizationBridge

/-!
# Nuclear formalization umbrella

This declaration-free umbrella exposes the current finite nuclear lane:

* spin/isospin and Wigner ladder symmetry;
* quasiparticle CAR and RPA phonon algebras;
* Soloviev finite quasiparticle-phonon eigenproblem and transition strengths;
* finite CAR projection and spectral readouts;
* Cartan generators in both `±2` and balanced `±1` normalizations;
* occupation/isospin projectors and quasiparticle fermion parity;
* generic parity-graded Hamiltonians with the theorem
  `P (H₀ + λV) P = H₀ - λV` for even `H₀` and odd `V`;
* the finite Soloviev coupling-sign symmetry as a specialization of that
  generic theorem;
* the shared Z₂-odd conjugation invariant between the zero-diagonal Soloviev
  Hamiltonian and the mass-spectrometry doubled transfer operator, without
  identifying their distinct matrix representations;
* finite quantum-number packets (`2J`, occupation, `2T₃`);
* CAR/RPA commuting quantum-number separation;
* Cartan/parity dictionaries to the `SL2SpinorLadder` and `Cl(5,5)`
  Cartan-Fock owners;
* Wigner charge-exchange amplitudes as normalized left/right Gram densities.

The umbrella does not assert a complete phenomenological nuclear model, a
complete shell-model quantum-number classification, or empirical predictive
validity.  It is the stable import surface for the theorem-bearing finite
structural lane currently present in the repository.
-/

namespace InfoGeometry.Physics.NuclearAll

end InfoGeometry.Physics.NuclearAll
