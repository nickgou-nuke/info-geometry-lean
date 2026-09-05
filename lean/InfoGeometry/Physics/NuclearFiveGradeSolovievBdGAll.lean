import InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel
import InfoGeometry.Physics.NuclearTwoModeFiveGradeSubmodules
import InfoGeometry.Physics.NuclearFiveGradeCommonCarrierRepresentation
import InfoGeometry.Physics.NuclearFiveGradeCommonCarrierLieHom
import InfoGeometry.Physics.NuclearFiveGradeSolovievCommonCompression
import InfoGeometry.Physics.NuclearCARPhononCommonCarrier
import InfoGeometry.Physics.NuclearSolovievCompression
import InfoGeometry.Physics.NuclearSolovievProjectedHamiltonian
import InfoGeometry.Physics.NuclearBdGTwoLevelExact
import InfoGeometry.Physics.NuclearBdGSolovievAffineBridge
import InfoGeometry.Physics.NuclearFiveGradeSolovievBdGClosure
import InfoGeometry.Physics.NuclearFiveGradeSameCarrierClosure

/-!
# Focused aggregate for the closed finite nuclear symmetry lane

This declaration-free surface exports:

* the globally Jacobi-closed two-mode CAR five-grading;
* its five adjoint eigenspaces as native Mathlib submodules with bracket maps;
* a native Lie homomorphism representing that five-grading on a common
  two-mode CAR--phonon carrier;
* exact CAR and CCR on that carrier, with commuting Zorn-derivation symmetry;
* a same-carrier idempotent `P H P` compression to the Soloviev QPNM block;
* the earlier one-mode concrete `CoupledQuasiparticlePhononSystem` instance;
* the exact two-level BdG square, spectrum, and conjugate-linear symmetry;
* the affine BdG decomposition of the Soloviev block;
* one end-to-end same-carrier closure theorem exposing all these identities.

The transitive axiom audit remains a separate executable target.
-/
