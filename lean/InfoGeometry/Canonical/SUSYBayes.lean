import InfoGeometry.Canonical.BogoliubovFockSuper
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Quantum.Fierz
import InfoGeometry.Quantum.Fock

/-!
# InfoGeometry.Canonical.SUSYBayes

Information integration across doubled-space Clifford variables.
-/

open InfoGeometry.Krein
open InfoGeometry.Quantum

namespace InfoGeometry.Canonical.SUSYBayes

section BayesianFock

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Theorem `bayesian_inference_as_creation`. -/
theorem bayesian_inference_as_creation
    (prior dataInnovation : Krein.DoubledSpace E) :
    bayesianUpdate (E := E) prior dataInnovation
      = prior + creationOp (E := E) dataInnovation :=
  rfl

/-- Theorem `data_model_split_is_projector_split`. -/
theorem data_model_split_is_projector_split (v : Krein.DoubledSpace E) :
    v = dataPart (E := E) v + modelPart (E := E) v :=
  data_model_decomposition (E := E) v

end BayesianFock

section MajoranaFierz

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Theorem `majorana_belief_iff_zero_uncertainty`. -/
theorem majorana_belief_iff_zero_uncertainty (ψ : Krein.DoubledSpace E) :
    InfoGeometry.Quantum.Fierz.IsMajoranaBelief (E := E) ψ
      ↔ InfoGeometry.Quantum.Fierz.infoArea (E := E) ψ = 0 :=
  Iff.rfl

/-- Theorem `fierz_power_conservation`. -/
theorem fierz_power_conservation [CompleteSpace E] (ψ : Krein.DoubledSpace E) :
    (InfoGeometry.Quantum.Fierz.infoHilbert (E := E) ψ) ^ 2
      = (InfoGeometry.Quantum.Fierz.infoScalar (E := E) ψ) ^ 2
        + (InfoGeometry.Quantum.Fierz.infoSymplectic (E := E) ψ) ^ 2
        + 4 * InfoGeometry.Quantum.Fierz.infoArea (E := E) ψ :=
  InfoGeometry.Quantum.Fierz.information_fierz_identity (E := E) ψ

end MajoranaFierz

section SuperBracket

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Theorem `super_even_even_eq_commutator`. -/
theorem super_even_even_eq_commutator
    (A B : InfoGeometry.Canonical.BogoliubovFockSuper.FockEndomorphism E) :
    InfoGeometry.Canonical.BogoliubovFockSuper.fockSuperBracket (E := E)
        InfoGeometry.Canonical.BogoliubovFockSuper.SuperParity.even
        InfoGeometry.Canonical.BogoliubovFockSuper.SuperParity.even A B
      = InfoGeometry.Canonical.BogoliubovFockSuper.fockCommutator (E := E) A B := rfl

/-- Theorem `super_odd_odd_eq_anticommutator`. -/
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

/-- Theorem `einstein_inducedChemicalPotential_eq_transportedResidual`. -/
theorem einstein_inducedChemicalPotential_eq_transportedResidual :
    InfoGeometry.Canonical.BogoliubovFockSuper.einsteinInducedChemicalPotential
      (E := E) R K x scalar Λ V Γ
      =
    transportedEinsteinResidual (R := R) (K := K) (x := x)
      (scalar := scalar) (Λ := Λ) V Γ := rfl

/-- Theorem `grandCanonical_eq_hamiltonian_of_vacuumTransported`. -/
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
