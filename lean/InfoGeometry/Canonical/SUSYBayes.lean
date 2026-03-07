import InfoGeometry.Canonical.BogoliubovFockSuper
import InfoGeometry.Canonical.Fierz
import InfoGeometry.Canonical.Fock

/-!
# InfoGeometry.Canonical.SUSYBayes

Canonical bridge lemmas for the SUSY/Bayesian synthesis on doubled Krein state
spaces.
-/

namespace InfoGeometry.Canonical.SUSYBayes

open InfoGeometry.Krein
open InfoGeometry.Canonical.RicciMongeAmpere
open InfoGeometry.Canonical.KaehlerGeometry

section BayesianFock

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem bayesian_inference_as_creation
    (prior dataInnovation : Krein.DoubledSpace E) :
    InfoGeometry.Canonical.Fock.bayesianUpdate (E := E) prior dataInnovation
      = prior + InfoGeometry.Canonical.Fock.creationOp (E := E) dataInnovation :=
  InfoGeometry.Canonical.Fock.bayesianUpdate_eq_creationExcitation (E := E) prior dataInnovation

theorem data_model_split_is_projector_split (v : Krein.DoubledSpace E) :
    v = InfoGeometry.Canonical.Fock.dataPart (E := E) v
      + InfoGeometry.Canonical.Fock.modelPart (E := E) v :=
  InfoGeometry.Canonical.Fock.data_model_decomposition (E := E) v

end BayesianFock

section MajoranaFierz

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem majorana_belief_iff_zero_uncertainty (ψ : Krein.DoubledSpace E) :
    InfoGeometry.Canonical.Fierz.IsMajoranaBelief (E := E) ψ
      ↔ InfoGeometry.Canonical.Fierz.infoArea (E := E) ψ = 0 :=
  InfoGeometry.Canonical.Fierz.majoranaBelief_iff_zeroArea (E := E) ψ

theorem fierz_power_conservation [CompleteSpace E] (ψ : Krein.DoubledSpace E) :
    (InfoGeometry.Canonical.Fierz.infoHilbert (E := E) ψ) ^ 2
      = (InfoGeometry.Canonical.Fierz.infoScalar (E := E) ψ) ^ 2
        + (InfoGeometry.Canonical.Fierz.infoSymplectic (E := E) ψ) ^ 2
        + 4 * InfoGeometry.Canonical.Fierz.infoArea (E := E) ψ :=
  InfoGeometry.Canonical.Fierz.information_fierz_identity (E := E) ψ

end MajoranaFierz

section SuperBracket

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem super_even_even_eq_commutator
    (A B : InfoGeometry.Canonical.BogoliubovFockSuper.FockEndomorphism E) :
    InfoGeometry.Canonical.BogoliubovFockSuper.fockSuperBracket (E := E)
        InfoGeometry.Canonical.BogoliubovFockSuper.SuperParity.even
        InfoGeometry.Canonical.BogoliubovFockSuper.SuperParity.even A B
      = InfoGeometry.Canonical.BogoliubovFockSuper.fockCommutator (E := E) A B := rfl

theorem super_odd_odd_eq_anticommutator
    (A B : InfoGeometry.Canonical.BogoliubovFockSuper.FockEndomorphism E) :
    InfoGeometry.Canonical.BogoliubovFockSuper.fockSuperBracket (E := E)
        InfoGeometry.Canonical.BogoliubovFockSuper.SuperParity.odd
        InfoGeometry.Canonical.BogoliubovFockSuper.SuperParity.odd A B
      = InfoGeometry.Canonical.BogoliubovFockSuper.fockAnticommutator (E := E) A B := rfl

end SuperBracket

section EinsteinChemicalPotential

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable (R : RicciTensor E)
variable (K : KaehlerInformationGeometry E) (x : E)
variable (scalar Λ : ℝ)
variable (V : SplitVielbein K x) (Γ : SpinConnection K x V)

theorem einstein_inducedChemicalPotential_eq_transportedResidual :
    InfoGeometry.Canonical.BogoliubovFockSuper.einsteinInducedChemicalPotential
      (E := E) R K x scalar Λ V Γ
      =
    transportedEinsteinResidual (R := R) (K := K) (x := x)
      (scalar := scalar) (Λ := Λ) V Γ := rfl

theorem grandCanonical_eq_hamiltonian_of_vacuumTransported
    (B : InfoGeometry.Canonical.BogoliubovFockSuper.BogoliubovMixingParams)
    (H : InfoGeometry.Canonical.BogoliubovFockSuper.FockEndomorphism E)
    (hVacSplit : VacuumEinsteinOnTransportedSplit R K x scalar Λ V Γ) :
    InfoGeometry.Canonical.BogoliubovFockSuper.grandCanonicalFockGenerator (E := E) B H
      (InfoGeometry.Canonical.BogoliubovFockSuper.einsteinInducedChemicalPotential
        (E := E) R K x scalar Λ V Γ) = H := by
  simpa using
    InfoGeometry.Canonical.BogoliubovFockSuper.grandCanonicalFockGenerator_eq_hamiltonian_of_vacuumTransported
      (E := E) (B := B) (H := H) (R := R) (K := K) (x := x)
      (scalar := scalar) (Λ := Λ) (V := V) (Γ := Γ) hVacSplit

end EinsteinChemicalPotential

end InfoGeometry.Canonical.SUSYBayes
