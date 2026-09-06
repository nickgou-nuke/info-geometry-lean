import InfoGeometry.Canonical.AnalyticalIndexCoupled
import InfoGeometry.Canonical.KMSSinkhornSeedState
import InfoGeometry.Canonical.KMSSinkhornScalarPotential
import InfoGeometry.Canonical.KMSSinkhornWeightedTransport
import InfoGeometry.Canonical.RicciMongeAmpere
import InfoGeometry.Canonical.SinkhornFoundation

set_option linter.unnecessarySimpa false

namespace InfoGeometry.Canonical.AnalyticalIndex

open InfoGeometry.Canonical.BottDirac
open InfoGeometry.Canonical.ChiralAnomaly
open InfoGeometry.Krein
open InfoGeometry.Canonical.KMSSinkhornBridge
open InfoGeometry.Canonical.MoE
open InfoGeometry.Canonical.RicciMongeAmpere

/-
This file owns the KMS/full-capstone packaging layer above the analytical-index
and coupled invariant trunks.
-/

section KMSCapstone

variable (n : Nat)
variable {F : Type} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/--
Explicit thermodynamic KMS capstone package:
exact KMS closure at each next step.
-/
def SinkhornKMSCapstone
    (T : SinkhornTrajectory n)
    (K : AlgebraEnd F)
    (ω : Nat → AlgebraEnd F →L[ℝ] ℝ)
    (β : ℝ) : Prop :=
  SinkhornKMSClosure n T K ω β

/-- Lemma `SinkhornKMSCapstone`. -/
lemma SinkhornKMSCapstone.kmsState
    (T : SinkhornTrajectory n)
    (K : AlgebraEnd F)
    (ω : Nat → AlgebraEnd F →L[ℝ] ℝ)
    (β : ℝ)
    (hCap : SinkhornKMSCapstone n T K ω β) :
    SinkhornKMSClosure n T K ω β :=
  hCap

/--
Constructive iterate specialization from closure (primary closure-first form).
-/
theorem sinkhornIterate_sinkhornKMSCapstone_of_closure
    (M0 : SinkhornMatrix n)
    (hrow : ∀ M : SinkhornMatrix n, HasPositiveRowSums n M)
    (hcol : ∀ M : SinkhornMatrix n, HasPositiveColSums n M)
    (K : AlgebraEnd F)
    (ω : Nat → AlgebraEnd F →L[ℝ] ℝ)
    (β : ℝ)
    (hClosure : SinkhornKMSClosure n
      (sinkhornIterateTrajectory (n := n) M0 hrow hcol) K ω β) :
    SinkhornKMSCapstone n (sinkhornIterateTrajectory (n := n) M0 hrow hcol) K ω β := by
  simpa [SinkhornKMSCapstone] using hClosure

end KMSCapstone

section FullCapstone

variable (n : Nat)
variable {X V Fth : Type}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup Fth] [InnerProductSpace ℝ Fth] [CompleteSpace Fth]

/--
Full capstone package:
thermodynamic/KMS control + geometric fixed-point collapse + index invariance.
-/
def FullThermoGeoIndexCapstone
    (T : DoublyStochasticSinkhornTrajectory n)
    (flow : ScalarRicciFlow X)
    (D Γ : ℝ → Endomorphism V)
    (K : AlgebraEnd Fth)
    (ω : Nat → AlgebraEnd Fth →L[ℝ] ℝ)
    (β : ℝ) : Prop :=
  SinkhornRicciIndexInvariant n T flow D Γ ∧
    SinkhornKMSCapstone n T.traj K ω β

/--
Canonical constructor for the full capstone package from the two state-level
components.
-/
theorem fullThermoGeoIndexCapstone_of_states
    (T : DoublyStochasticSinkhornTrajectory n)
    (flow : ScalarRicciFlow X)
    (D Γ : ℝ → Endomorphism V)
    (K : AlgebraEnd Fth)
    (ω : Nat → AlgebraEnd Fth →L[ℝ] ℝ)
    (β : ℝ)
    (hGeoAlg : SinkhornRicciIndexInvariant n T flow D Γ)
    (hClosure : SinkhornKMSClosure n T.traj K ω β) :
    FullThermoGeoIndexCapstone n T flow D Γ K ω β := by
  exact ⟨hGeoAlg, hClosure⟩

/-- Lemma `FullThermoGeoIndexCapstone`. -/
lemma FullThermoGeoIndexCapstone.geometricAlgebraicState
    (T : DoublyStochasticSinkhornTrajectory n)
    (flow : ScalarRicciFlow X)
    (D Γ : ℝ → Endomorphism V)
    (K : AlgebraEnd Fth)
    (ω : Nat → AlgebraEnd Fth →L[ℝ] ℝ)
    (β : ℝ)
    (hCap : FullThermoGeoIndexCapstone n T flow D Γ K ω β) :
    SinkhornRicciIndexInvariant n T flow D Γ :=
  hCap.1

/-- Lemma `FullThermoGeoIndexCapstone`. -/
lemma FullThermoGeoIndexCapstone.thermodynamicKMSState
    (T : DoublyStochasticSinkhornTrajectory n)
    (flow : ScalarRicciFlow X)
    (D Γ : ℝ → Endomorphism V)
    (K : AlgebraEnd Fth)
    (ω : Nat → AlgebraEnd Fth →L[ℝ] ℝ)
    (β : ℝ)
    (hCap : FullThermoGeoIndexCapstone n T flow D Γ K ω β) :
    SinkhornKMSClosure n T.traj K ω β :=
  hCap.2

end FullCapstone

section UnifiedNaming

variable (n : Nat)
variable {X V Fth : Type}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup Fth] [InnerProductSpace ℝ Fth] [CompleteSpace Fth]

/--
Unified thermodynamic state naming used by higher-level synthesis modules.
-/
abbrev ThermodynamicKMSState
    (T : DoublyStochasticSinkhornTrajectory n)
    (K : AlgebraEnd Fth)
    (ω : Nat → AlgebraEnd Fth →L[ℝ] ℝ)
    (β : ℝ) : Prop :=
  SinkhornKMSClosure n T.traj K ω β

/--
Unified geometric-algebraic state naming used by higher-level synthesis modules.
-/
abbrev GeometricAlgebraicState
    (T : DoublyStochasticSinkhornTrajectory n)
    (flow : ScalarRicciFlow X)
    (D Γ : ℝ → Endomorphism V) : Prop :=
  SinkhornRicciIndexInvariant n T flow D Γ

/--
Unified full capstone naming used by higher-level synthesis modules.
-/
abbrev ThermoGeoIndexCapstoneState
    (T : DoublyStochasticSinkhornTrajectory n)
    (flow : ScalarRicciFlow X)
    (D Γ : ℝ → Endomorphism V)
    (K : AlgebraEnd Fth)
    (ω : Nat → AlgebraEnd Fth →L[ℝ] ℝ)
    (β : ℝ) : Prop :=
  FullThermoGeoIndexCapstone n T flow D Γ K ω β

end UnifiedNaming

end InfoGeometry.Canonical.AnalyticalIndex
