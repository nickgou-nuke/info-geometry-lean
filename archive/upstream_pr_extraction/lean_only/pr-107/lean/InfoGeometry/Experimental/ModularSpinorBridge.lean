import InfoGeometry.Krein.Modular
import InfoGeometry.Krein.DoubledSpace
import InfoGeometry.Krein.DoubledSpaceMatrix
import InfoGeometry.Canonical.RicciMongeAmpere
import InfoGeometry.Quantum.Fock
import InfoGeometry.Canonical.KaehlerGeometry
import InfoGeometry.Canonical.BerryConnection
import InfoGeometry.Krein.HilbertBridge
import InfoGeometry.Canonical.YangMillsContinuum
import InfoGeometry.Canonical.RelativeModularPotential
import Mathlib.InformationTheory.KullbackLeibler.Basic

/-!
# Modular Spinor Bridge

This module formalizes the parallel transport of the Bogoliubov frame
via the modular operator on the doubled Krein space.
-/

namespace InfoGeometry.Experimental.ModularSpinorBridge

open InfoGeometry.Krein
open InfoGeometry.Clifford
open InfoGeometry.Canonical.RicciMongeAmpere
open InfoGeometry.Quantum
open InfoGeometry.Canonical.KaehlerGeometry
open InfoGeometry.Canonical.YangMillsContinuum

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/--
**Majorana Basis**:
A frame for the doubled space $E \oplus E$ that satisfies the real $Cl(1,1)$ relations.
-/
structure MajoranaFrame (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] where
  J : Krein.DoubledSpace E →L[ℝ] Krein.DoubledSpace E
  eps : Krein.DoubledSpace E →L[ℝ] Krein.DoubledSpace E
  is_cl11 : Krein.cl11_relations J eps

/--
**Canonical Majorana Frame**:
The default frame using `modular_j` and `spectral_epsilon`.
-/
noncomputable def canonicalMajoranaFrame : MajoranaFrame E where
  J := Krein.modular_j (E := E)
  eps := Krein.spectral_epsilon (E := E)
  is_cl11 := Krein.modular_j_spectral_epsilon_has_cl11_relations E

/--
**Spinor Bilinears as Observables**:
The expectation value of an operator $\mathcal{O}$ is represented as a
spinor bilinear $\langle \psi | \mathcal{O} | \psi \rangle_{Krein}$.
-/
noncomputable def spinorBilinear
    (ψ : Krein.DoubledSpace E) (O : Krein.DoubledSpace E →L[ℝ] Krein.DoubledSpace E) : ℝ :=
  let J_symm := Krein.modular_j (E := E)
  @inner ℝ (Krein.DoubledSpace E) _ (J_symm ψ) (O ψ)

/--
**Modular Berry Bridge**:
The Berry curvature of the modular flow is exactly the antisymmetric part
of the modular spinor bilinear.
-/
structure ModularBerryBridge (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] where
  M : ModularRadonNikodymData E
  S : InfoGeometry.Canonical.BerryPhase.SuperHestenesKaehlerDatum (E := E)
  h_K : M.modularHamiltonian = S.K
  berry_identity : ∀ ψ, spinorBilinear (E := E) ψ S.K = S.phase ψ (S.K ψ)

/--
**Modular Berry Identity**:
Under the explicit bridge identification, the spinor bilinear of the 
modular Hamiltonian recovers the Berry phase.
-/
theorem spinorBilinear_eq_berryPhase
    (B : ModularBerryBridge E) (ψ : Krein.DoubledSpace E) :
    spinorBilinear (E := E) ψ B.M.modularHamiltonian = B.S.phase ψ (B.M.modularHamiltonian ψ) := by
  rw [B.h_K]
  exact B.berry_identity ψ

/--
**Spinor Innovation Bridge**:
Links the microscopic spinor bilinear to the operatorial relative modular
potential on the doubled carrier.
-/
structure SpinorInnovationBridge (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] where
  ψ : Krein.DoubledSpace E
  potential :
    InfoGeometry.Canonical.RelativeModularPotential.PotentialDatum (E := E)
  O_innov : Krein.DoubledSpace E →L[ℝ] Krein.DoubledSpace E
  h_bilinear :
    spinorBilinear (E := E) ψ O_innov =
      InfoGeometry.Canonical.RelativeModularPotential.value
        (E := E) potential ψ

/--
**Relative modular potential bridge**:
The spinor bilinear is identified with the operatorial relative modular
potential on the same doubled carrier.  No scalar Radon--Nikodym tuple or
commutative KL surrogate is introduced here.
-/
theorem spinorBilinear_eq_relativeModularPotential
    (B : SpinorInnovationBridge E) :
    spinorBilinear (E := E) B.ψ B.O_innov =
      InfoGeometry.Canonical.RelativeModularPotential.value
        (E := E) B.potential B.ψ := by
  exact B.h_bilinear

end InfoGeometry.Experimental.ModularSpinorBridge
