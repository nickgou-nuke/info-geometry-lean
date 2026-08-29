import InfoGeometry.Canonical.CayleyCriticalLineCircleBridge
import InfoGeometry.Canonical.PrimeLeeYangFerromagneticChain
import InfoGeometry.Canonical.PrimeGasSuperKMSBridge
import InfoGeometry.Canonical.PrimeBinaryCantorSuperalgebraBridge
import InfoGeometry.Arithmetic.PrimeSuperalgebraReadback
import InfoGeometry.Tessellation.CantorDiracSeaOperatorGeometry
import InfoGeometry.Canonical.HodgeDiracLaplacianBridge
import InfoGeometry.Canonical.YangBaxterProof

/-!
# Prime/Cantor/Thermo/Yang--Baxter Bridge

Theorem-safe synthesis for the requested lane:

* Cayley compactification of the Riemann critical line to the Lee--Yang circle;
* prime ferromagnetic chain couplings;
* finite prime/Cantor supertrace and Möbius parity readbacks;
* Cantor binary Dirac-sea operator geometry;
* super-KMS zero odd temperature/detailed balance;
* algebraic Hodge--Dirac Laplacian evenness;
* finite Fibonacci Yang--Baxter/Artin relation.

This file does not assert RH, zeta analytic continuation, a Lee--Yang theorem
for the prime chain, or a full braided-category instance.  Those remain owned
by their existing property-gated or categorical files.
-/

noncomputable section

namespace InfoGeometry.Canonical.PrimeCantorThermoYangBaxterBridge

open InfoGeometry.Canonical.CayleyCriticalLineCircleBridge
open InfoGeometry.Canonical.PrimeLeeYangFerromagneticChain
open InfoGeometry.Canonical.PrimeGasSuperKMS
open InfoGeometry.Canonical.AlgebraicKMSStateColimit
open InfoGeometry.Canonical.PrimeBinaryCantorSuperalgebraBridge
open InfoGeometry.Canonical.TypeIIIModularCantorSystem
open InfoGeometry.Arithmetic.PrimeSuperalgebraReadback
open InfoGeometry.Tessellation
open InfoGeometry.Canonical.HodgeDiracLaplacianBridge

/-! ## Cayley compactification and prime Lee--Yang geometry -/

/-- Cayley compactification sends the critical line exactly to the Lee--Yang circle. -/
theorem criticalLine_iff_cayleyCircle
    (s : ℂ) :
    OnCriticalLine s ↔ OnLeeYangCircle (cayleyToFugacity s) :=
  criticalLine_iff_cayley_unitCircle s

/-- Riemann reflection becomes inversion in the Cayley fugacity coordinate. -/
theorem riemannReflection_eq_fugacityInversion
    (s : ℂ) :
    cayleyToFugacity (1 - s) = (cayleyToFugacity s)⁻¹ :=
  cayleyToFugacity_one_sub_eq_inv s

/-! ## Prime chain and noncommutative KMS readout -/

/-- Prime-chain couplings are ferromagnetic and symmetric. -/
theorem primeChain_coupling_nonnegative_symmetric
    {n : ℕ}
    (C : PrimeFerromagneticChain n)
    (i j : Fin n) :
    0 ≤ C.couplingMatrix i j ∧ C.couplingMatrix i j = C.couplingMatrix j i :=
  ⟨C.couplingMatrix_entry_nonneg i j, C.couplingMatrix_symm i j⟩

/-- The primon bridge exposes the native noncommutative KMS boundary law. -/
theorem primeGas_superKMS_boundary
    (B : PrimeGasSuperKMSBridge)
    (x y : Carrier) :
    deltaWeightedFunctional B.density (x * y) =
      deltaWeightedFunctional B.density (y * B.imaginaryTime x) :=
  B.kms_boundary x y

/-! ## Cantor binary words and finite Euler-product structure -/

/-- The binary Cantor cylinder splits into root, left child, and right child. -/
theorem cantorCylinder_binarySplit
    (w : List Bool) :
    TypeIIIModularCantorSystem.closedCylinder w =
      ({w} : Set (List Bool))
        ∪ TypeIIIModularCantorSystem.closedCylinder (TypeIIIModularCantorSystem.child w false)
        ∪ TypeIIIModularCantorSystem.closedCylinder (TypeIIIModularCantorSystem.child w true) :=
  TypeIIIModularCantorSystem.closedCylinder_split w

/-! ## Hodge--Dirac and Yang--Baxter owner readouts -/

/-- If `Δ = Q²` and `Q` anticommutes with Hodge star, then `Δ` is Hodge-even. -/
theorem hodgeDirac_laplacian_even
    {Op : Type*} [Ring Op]
    (C : HodgeDiracLaplacianCarrier Op)
    (hChiral : IsDiracHodgeChiral C)
    (hDelta : IsLaplacianFromDirac C) :
    laplacian C * hodgeStar C =
      hodgeStar C * laplacian C :=
  laplacian_commutes_hodge_of_dirac_closure C hChiral hDelta

/-- Finite Fibonacci Yang--Baxter/Artin relation from the exact owner matrix proof. -/
theorem fibonacci_yangBaxter_artin :
    InfoGeometry.Canonical.YangBaxterProof.R *
        InfoGeometry.Canonical.YangBaxterProof.B *
          InfoGeometry.Canonical.YangBaxterProof.R =
      InfoGeometry.Canonical.YangBaxterProof.B *
        InfoGeometry.Canonical.YangBaxterProof.R *
          InfoGeometry.Canonical.YangBaxterProof.B :=
  InfoGeometry.Canonical.YangBaxterProof.braid_relation

end InfoGeometry.Canonical.PrimeCantorThermoYangBaxterBridge
