import InfoGeometry.Canonical.SouriauMetriplecticOptimalTransport
import InfoGeometry.GromovWittenErlangen.GWCanonicalCountRayBridge
import InfoGeometry.Meta.Architecture

/-!
# Souriau / GW count / optimal-transport bridge

Witness-gated bridge from Souriau thermal Hamiltonians to the installed
Gromov--Witten projective count Hamiltonian profile and the installed
metriplectic optimal-transport free-energy packet.

This file does not construct GW localization, coadjoint orbits, Wasserstein
metrics, or gradient flows.  Those are owned by the imported modules.  It only
records the explicit calibration needed to read the GW projective count
Hamiltonian as the Souriau thermal generator and as the expectation term in the
free-energy functional.
-/

namespace SouriauGWCountOTBridge

open InfoGeometry.Canonical.SouriauMetriplecticOptimalTransport
open InfoGeometry.GromovWittenErlangen

variable {State LieGroup LieAlgebra LieDual Observable : Type*}
variable {n : ℕ} [Nonempty (Fin n)]
variable {LG T Target Coeff : Type*}

/--
Calibration connecting Souriau thermal dynamics, GW projective count rays, and
metriplectic optimal transport.

The two index maps are intentionally separate: `SouriauLieThermoData.K_beta`
is a state-level readout, while `FreeEnergyFunctional.expectationTerm` is a
readout on densities `State → ℝ`.
-/
@[rep_depth thermo]
structure SouriauGWCountOTCalibration where
  /-- Souriau Lie-thermodynamic moment/temperature/pairing data. -/
  souriau : SouriauLieThermoData State LieGroup LieAlgebra LieDual

  /-- GW projective count-ray realization. -/
  gw : GWCanonicalCountRayBridge n LG T Target Coeff

  /-- Free-energy functional on density states. -/
  freeEnergy : FreeEnergyFunctional State

  /-- Installed metriplectic optimal-transport flow packet. -/
  flow : SouriauMetriplecticOTFlow State LieGroup LieAlgebra LieDual Observable

  /-- State-level sector map into the finite GW count carrier. -/
  stateIndex : State → Fin n

  /-- Density-level sector map into the finite GW count carrier. -/
  densityIndex : Density State → Fin n

  /-- The Souriau thermal Hamiltonian is calibrated to the GW projective Hamiltonian. -/
  K_beta_eq_projectiveHamiltonian :
    ∀ x : State,
      souriau.K_beta x = gw.projectiveHamiltonianProfile (stateIndex x)

  /-- The free-energy expectation term is calibrated to the GW projective Hamiltonian. -/
  expectation_eq_projectiveHamiltonian :
    ∀ ρ : Density State,
      freeEnergy.expectationTerm ρ = gw.projectiveHamiltonianProfile (densityIndex ρ)

namespace SouriauGWCountOTCalibration

variable (C : SouriauGWCountOTCalibration
  (State := State) (LieGroup := LieGroup) (LieAlgebra := LieAlgebra)
  (LieDual := LieDual) (Observable := Observable) (n := n)
  (LG := LG) (T := T) (Target := Target) (Coeff := Coeff))

/-- The Souriau thermal Hamiltonian is the calibrated GW count Hamiltonian. -/
@[rep_depth thermo]
theorem thermalHamiltonian_eq_gwCountHamiltonian
    (x : State) :
    C.souriau.K_beta x = C.gw.projectiveHamiltonianProfile (C.stateIndex x) :=
  C.K_beta_eq_projectiveHamiltonian x

/-- The expectation term of the OT free energy is the calibrated GW count Hamiltonian. -/
@[rep_depth thermo]
theorem expectationTerm_eq_gwCountHamiltonian
    (ρ : Density State) :
    C.freeEnergy.expectationTerm ρ =
      C.gw.projectiveHamiltonianProfile (C.densityIndex ρ) :=
  C.expectation_eq_projectiveHamiltonian ρ

/-- The installed metriplectic OT flow splits into reversible and dissipative parts. -/
@[rep_depth thermo]
theorem metriplecticFlow_total_eq_reversible_add_dissipative
    (ρ : Density State) :
    C.flow.totalFlow ρ = C.flow.reversibleFlow ρ + C.flow.dissipativeFlow ρ :=
  SouriauMetriplecticOTFlow.totalFlow_eq_add_at C.flow ρ

/--
Free energy splits into entropy plus the calibrated GW projective count
Hamiltonian expectation.
-/
@[rep_depth thermo]
theorem freeEnergy_eq_entropy_add_gwCountHamiltonian
    (ρ : Density State) :
    C.freeEnergy.freeEnergy ρ =
      C.freeEnergy.entropyTerm ρ + C.gw.projectiveHamiltonianProfile (C.densityIndex ρ) := by
  calc
    C.freeEnergy.freeEnergy ρ
        = C.freeEnergy.entropyTerm ρ + C.freeEnergy.expectationTerm ρ :=
            FreeEnergyFunctional.freeEnergy_eq_split C.freeEnergy ρ
    _ = C.freeEnergy.entropyTerm ρ +
          C.gw.projectiveHamiltonianProfile (C.densityIndex ρ) := by
            rw [C.expectation_eq_projectiveHamiltonian ρ]

/--
Combined packet: the calibrated GW count Hamiltonian gives the expectation part,
and the installed flow gives the metriplectic OT split.
-/
@[rep_depth thermo]
theorem gwCount_freeEnergy_and_flow_packet
    (ρ : Density State) :
    C.freeEnergy.freeEnergy ρ =
        C.freeEnergy.entropyTerm ρ + C.gw.projectiveHamiltonianProfile (C.densityIndex ρ)
      ∧ C.flow.totalFlow ρ = C.flow.reversibleFlow ρ + C.flow.dissipativeFlow ρ :=
  ⟨C.freeEnergy_eq_entropy_add_gwCountHamiltonian ρ,
    C.metriplecticFlow_total_eq_reversible_add_dissipative ρ⟩

end SouriauGWCountOTCalibration

end SouriauGWCountOTBridge
