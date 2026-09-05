import InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel
import InfoGeometry.Physics.NuclearTwoModeFiveGradeSubmodules
import InfoGeometry.Physics.NuclearFiveGradeCommonCarrierRepresentation
import InfoGeometry.Physics.NuclearCARPhononCommonCarrier
import InfoGeometry.Physics.NuclearSolovievCompression
import InfoGeometry.Physics.NuclearSolovievProjectedHamiltonian
import InfoGeometry.Physics.NuclearBdGTwoLevelExact
import InfoGeometry.Physics.NuclearBdGSolovievAffineBridge
import InfoGeometry.Physics.NuclearFiveGradeSolovievBdGClosure

/-!
# Focused aggregate for the closed finite nuclear symmetry lane

This declaration-free surface exports:

* the globally Jacobi-closed two-mode CAR five-grading;
* its five adjoint eigenspaces as native Mathlib submodules with bracket maps;
* a multiplicative, grade-preserving representation of that five-grading on a
  common two-mode CAR--phonon carrier;
* the concrete one-quasiparticle common carrier with exact CAR and CCR used by
  the finite Soloviev compression;
* the explicit compression to the finite Soloviev QPNM matrix;
* the idempotent model-space projector and exact `P H P` relation;
* the exact two-level BdG square, spectrum, and conjugate-linear symmetry;
* the affine BdG decomposition of the Soloviev block.

The transitive axiom audit remains a separate executable target.
-/
