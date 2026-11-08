import InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Physics.NuclearTwoModeFiveGradeSubmodules
import InfoGeometry.Physics.NuclearFiveGradeKantorComponentBridge
import InfoGeometry.Physics.NuclearFiveGradeCommonCarrierRepresentation
import InfoGeometry.Physics.NuclearFiveGradeCommonCarrierLieHom
import InfoGeometry.Physics.NuclearFiveGradeDegreeZeroSL2
import InfoGeometry.Physics.NuclearFiveGradeSolovievCommonCompression
import InfoGeometry.Physics.NuclearCARPhononCommonCarrier
import InfoGeometry.Physics.NuclearSolovievCompression
import InfoGeometry.Physics.NuclearSolovievProjectedHamiltonian
import InfoGeometry.Physics.NuclearBdGTwoLevelExact
import InfoGeometry.Physics.NuclearBdGBogoliubovCAR
import InfoGeometry.Physics.NuclearBdGSolovievAffineBridge
import InfoGeometry.Physics.NuclearFiveGradeSolovievBdGClosure
import InfoGeometry.Physics.NuclearFiveGradeSameCarrierClosure

/-!
# Focused aggregate for the closed finite nuclear symmetry lane

This declaration-free surface exports:

* the globally Jacobi-closed two-mode CAR five-grading;
* its five adjoint eigenspaces as native Mathlib submodules with bracket maps;
* the exact identification of those eigenspaces with the generic associative
  Kantor--Peirce commutator-component predicate for a tripotent grading matrix;
* a native Lie homomorphism representing the five-grading on a common
  two-mode CAR--phonon carrier;
* a number-preserving degree-zero `sl₂` with explicit doublet selection rules;
* exact CAR and CCR on the common carrier, with commuting Zorn-derivation
  symmetry;
* a same-carrier idempotent `P H P` compression to the Soloviev QPNM block;
* the exact two-level BdG square, characteristic roots, spectral intertwiner,
  and conjugate-linear particle--hole symmetry;
* an explicit normalized positive-energy BdG eigenmode whose associated
  Bogoliubov creation/annihilation pair preserves CAR;
* the affine BdG decomposition of the Soloviev block;
* one end-to-end same-carrier closure theorem exposing these identities.

The transitive axiom audit remains a separate executable target.
-/
