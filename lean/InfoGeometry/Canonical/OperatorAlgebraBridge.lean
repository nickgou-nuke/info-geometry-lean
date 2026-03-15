import InfoGeometry.Canonical.AQFTOperatorInterface
import InfoGeometry.Canonical.KKFoundation
import InfoGeometry.Canonical.TomitaTakesaki

open scoped InnerProductSpace

/-!
# InfoGeometry.Canonical.OperatorAlgebraBridge

Canonical bridge from the framework's dynamical layers to operator-algebra
interfaces:

- C*-ready and von-Neumann-ready AQFT targets
- Sinkhorn-to-KMS closure in operator targets
- Tomita-Takesaki modular atom on doubled real space
- bounded KK supercommutator compactness interface
-/

namespace InfoGeometry.Canonical.OperatorAlgebraBridge

open InfoGeometry.Krein
open InfoGeometry.Canonical.AQFTOperatorInterface
open InfoGeometry.Canonical.KMSSinkhornBridge
open InfoGeometry.Canonical.MoE
open InfoGeometry.Canonical.BogoliubovFockSuper
open InfoGeometry.Canonical.RicciMongeAmpere
open InfoGeometry.Canonical.TomitaTakesaki

open InfoGeometry.KK

section Signatures

variable (Obs : Type*) [NonUnitalNormedRing Obs] [StarRing Obs]

/-- Canonical alias for C*-ready operator targets. -/
abbrev IsCStarLayer : Prop := IsCStarReady (Obs := Obs)

/-- Canonical alias for von-Neumann-ready operator targets. -/
abbrev IsVonNeumannLayer : Prop := IsVonNeumannReady (Obs := Obs)

end Signatures

section ModularAtom

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The Tomita modular pair realizes split `Cl(1,1)` on doubled real space. -/
theorem modular_atom_is_cl11 :
    InfoGeometry.Krein.cl11_algebra
      (modularConjugationJ (E := E))
      (modularSignEpsilon (E := E)) := by
  simpa [modularConjugationJ, modularSignEpsilon] using
    (InfoGeometry.Krein.modular_j_spectral_epsilon_is_cl11 (E := E))

end ModularAtom

section AqftClosure

variable (n : Nat)
variable {F : Type} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
variable {Obs : Type*} [NonUnitalNormedRing Obs] [StarRing Obs] [CStarRing Obs]

/--
Sinkhorn-driven KMS closure persists under realizations into C*-algebra targets.
-/
theorem sinkhorn_kms_closure_in_cstar
    (real : AQFTOperatorRealization (F := F) (Obs := Obs))
    (T : SinkhornTrajectory n)
    (K : AlgebraEnd F)
    (ω : Nat → AlgebraEnd F →L[ℝ] ℝ)
    (β : ℝ)
    (h_closure : SinkhornKMSClosure n T K ω β) :
    IsCStarLayer (Obs := Obs) ∧ SinkhornKMSClosure n T K ω β := by
  exact sinkhorn_kmsClosure_with_cstarRealization
    (n := n) (F := F) (Obs := Obs) real
    (T := T) (K := K) (ω := ω) (β := β) h_closure

end AqftClosure

section UnifiedPackage

variable (n : Nat)
variable {F : Type} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
variable {ObsKMS : Type*}
  [NonUnitalNormedRing ObsKMS] [StarRing ObsKMS] [CStarRing ObsKMS]
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {ObsFock : Type*}
  [NonUnitalNormedRing ObsFock] [StarRing ObsFock] [CStarRing ObsFock]
  [CompleteSpace ObsFock]

/--
Canonical AQFT package combining C* readiness, von-Neumann readiness, KMS
closure, and the reduced grand-canonical Euler law.
-/
theorem cstar_vonneumann_kms_fock_package
    (real_kms : AQFTOperatorRealization (F := F) (Obs := ObsKMS))
    (real_fock : AQFTOperatorRealization (F := E) (Obs := ObsFock))
    (T : SinkhornTrajectory n)
    (K : AlgebraEnd F)
    (ω : Nat → AlgebraEnd F →L[ℝ] ℝ)
    (β : ℝ)
    (η : ℝ)
    (B : BogoliubovMixingParams)
    (H : FockEndomorphism E)
    (R : RicciTensor E)
    (Kgeo : InfoGeometry.Canonical.KaehlerGeometry.KaehlerInformationGeometry E)
    (x : E)
    (scalar Λ : ℝ)
    (V : InfoGeometry.Canonical.RicciMongeAmpere.SplitVielbein Kgeo x)
    (Γ : InfoGeometry.Canonical.RicciMongeAmpere.SpinConnection Kgeo x V)
    (ψ : DoubledSpace E)
    (h_closure : SinkhornKMSClosure n T K ω β)
    (h_vac_split : VacuumEinsteinOnTransportedSplit R Kgeo x scalar Λ V Γ) :
    IsCStarLayer (Obs := ObsKMS) ∧
      IsVonNeumannLayer (Obs := ObsFock) ∧
      SinkhornKMSClosure n T K ω β ∧
      grandCanonicalFockEulerStep (E := E) η B H
          (einsteinInducedChemicalPotential (R := R) (K := Kgeo) (x := x)
            (scalar := scalar) (Λ := Λ) (V := V) (Γ := Γ)) ψ
          = ψ + η • H ψ := by
  exact aqft_interface_package_with_realizations
    (n := n)
    (F := F) (ObsKMS := ObsKMS)
    (E := E) (ObsFock := ObsFock)
    (realKMS := real_kms) (realFock := real_fock)
    (T := T) (K := K) (ω := ω) (β := β)
    (η := η) (B := B) (H := H)
    (R := R) (Kgeo := Kgeo) (x := x)
    (scalar := scalar) (Λ := Λ) (V := V) (Γ := Γ) (ψ := ψ)
    h_closure h_vac_split

end UnifiedPackage

section KkBridge

variable {A B H : Type*}
variable [NormedRing A] [NormedRing B]
variable [NormedAlgebra ℝ A] [NormedAlgebra ℝ B]
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [KreinSpace H] [KreinGradedModule H]

/--
In the bounded KK layer, for even algebra representation, the graded
supercommutator compactness condition reduces to the cycle's compactness axiom.
-/
theorem kk_supercomm_compact_of_even_rep
    (X : KasparovCycle A B H)
    (hπ_even : ∀ a : A, KreinGradedModule.IsEven (H := H) (X.π a))
    (a : A) :
    IsCompactEnd H (KreinGradedModule.superComm (H := H) X.F (X.π a)) := by
  exact InfoGeometry.KK.superComm_compact_of_even_rep (X := X) hπ_even a

end KkBridge

end InfoGeometry.Canonical.OperatorAlgebraBridge
