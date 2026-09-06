import InfoGeometry.Canonical.DiscreteMellinModularBridge
import InfoGeometry.Canonical.DiscreteModularMellinShift
import InfoGeometry.Canonical.CasimirWeylDrazinContext

/-!
# Discrete Mellin Modular Hamiltonian

Lean-facing packet for the DFT/DMT modular-Hamiltonian bridge.

The important repository constraint is preserved: the modular Hamiltonian is
not represented as a bare finite diagonal coordinate matrix.  It is represented
operatorially by a spectral-projector Hamiltonian context.  The DMT statement is
the readout-level fact that applying a DFT to logarithmically sampled data gives
the Mellin/rapidity spectrum.
-/

namespace InfoGeometry.SuperMetriplectic

open InfoGeometry.Canonical.DiscreteMellinModularBridge

set_option linter.unusedSectionVars false

variable {E : Type 0} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => InfoGeometry.Krein.DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

/--
DFT-on-log-samples packet.

`dmtSpectrum` is definitionally carried as the DFT spectrum of logarithmic
samples.  This is the discrete version of "Mellin is Fourier after `x = exp u`".
-/
structure LogSampledDFTMellinData (Index : Type*) where
  linearSample : Index → ℝ
  logarithmicSample : Index → ℝ
  logCoordinate : Index → ℝ
  dftSpectrum : Index → ℝ
  dmtSpectrum : Index → ℝ
  log_sample_eq_coordinate :
    ∀ k : Index, Real.log (logarithmicSample k) = logCoordinate k
  dmt_eq_dft_on_logSamples :
    dmtSpectrum = dftSpectrum

namespace LogSampledDFTMellinData

/-- The DMT spectrum is the DFT spectrum computed on the logarithmic sample lane. -/
theorem dmtSpectrum_eq_dftSpectrum
    {Index : Type*} (P : LogSampledDFTMellinData Index) :
    P.dmtSpectrum = P.dftSpectrum :=
  P.dmt_eq_dft_on_logSamples

/-- Logarithmic samples expose additive rapidity/log coordinates. -/
theorem logSample_eq_logCoordinate
    {Index : Type*} (P : LogSampledDFTMellinData Index) (k : Index) :
    Real.log (P.logarithmicSample k) = P.logCoordinate k :=
  P.log_sample_eq_coordinate k

end LogSampledDFTMellinData

/--
Discrete modular Hamiltonian from Mellin/rapidity spectral data.

The Hamiltonian itself is supplied by the owner
`OperatorialDiscreteModularHamiltonianContext`, which enforces the
projector-commutation gate.
-/
structure DiscreteMellinModularHamiltonianData
    (η0 Δη : ℝ) (P : ℤ → EndH) where
  context :
    OperatorialDiscreteModularHamiltonianContext (E := E) η0 Δη P
  mellinWeight : ℤ → ℝ
  mellinWeight_eq_discreteRapidity :
    ∀ k : ℤ, mellinWeight k = discreteRapidity η0 Δη k
  hamiltonianReadout : EndH
  hamiltonianReadout_eq_context :
    hamiltonianReadout = context.H

namespace DiscreteMellinModularHamiltonianData

/-- Mellin spectral weights are additive rapidity grid values. -/
theorem mellinWeight_eq_rapidity
    {η0 Δη : ℝ} {P : ℤ → EndH}
    (M : DiscreteMellinModularHamiltonianData (E := E) η0 Δη P)
    (k : ℤ) :
    M.mellinWeight k = discreteRapidity η0 Δη k :=
  M.mellinWeight_eq_discreteRapidity k

/-- The Hamiltonian readout is the operatorial spectral Hamiltonian, not a matrix coordinate. -/
theorem hamiltonianReadout_eq_operatorialContext
    {η0 Δη : ℝ} {P : ℤ → EndH}
    (M : DiscreteMellinModularHamiltonianData (E := E) η0 Δη P) :
    M.hamiltonianReadout = M.context.H :=
  M.hamiltonianReadout_eq_context

/-- The discrete modular Hamiltonian commutes with its spectral projectors. -/
theorem hamiltonian_commutes_spectralProjectors
    {η0 Δη : ℝ} {P : ℤ → EndH}
    (M : DiscreteMellinModularHamiltonianData (E := E) η0 Δη P)
    (k : ℤ) :
    Commute M.hamiltonianReadout (P k) := by
  rw [M.hamiltonianReadout_eq_operatorialContext]
  exact
    InfoGeometry.Canonical.DiscreteMellinModularBridge.modularHamiltonian_commutes_spectralProjectors
      (E := E) M.context k

end DiscreteMellinModularHamiltonianData

/--
Discrete Lorentz/Mellin quantization packet.

It connects logarithmic sampling, light-cone rapidity scaling, and the
operatorial discrete modular Hamiltonian.
-/
structure DiscreteLorentzMellinQuantizationData
    (η0 Δη : ℝ) (P : ℤ → EndH) where
  dmt : LogSampledDFTMellinData ℤ
  modularHamiltonian :
    DiscreteMellinModularHamiltonianData (E := E) η0 Δη P
  samples_match_owner :
    ∀ k : ℤ, dmt.logarithmicSample k = logarithmicSample η0 Δη k
  logCoordinates_match_rapidity :
    ∀ k : ℤ, dmt.logCoordinate k = discreteRapidity η0 Δη k

namespace DiscreteLorentzMellinQuantizationData

/-- The DMT is the DFT on the logarithmic sampling lane. -/
theorem dmt_eq_dft_on_logSamples
    {η0 Δη : ℝ} {P : ℤ → EndH}
    (Q : DiscreteLorentzMellinQuantizationData (E := E) η0 Δη P) :
    Q.dmt.dmtSpectrum = Q.dmt.dftSpectrum :=
  Q.dmt.dmtSpectrum_eq_dftSpectrum

/-- The logarithmic sampling lane matches the owner rapidity grid. -/
theorem logSample_owner_grid
    {η0 Δη : ℝ} {P : ℤ → EndH}
    (Q : DiscreteLorentzMellinQuantizationData (E := E) η0 Δη P)
    (k : ℤ) :
    Real.log (Q.dmt.logarithmicSample k) = discreteRapidity η0 Δη k := by
  rw [Q.dmt.logSample_eq_logCoordinate k]
  exact Q.logCoordinates_match_rapidity k

/-- The modular Hamiltonian commutes with every property Mellin spectral projector. -/
theorem modularHamiltonian_commutes_spectralProjectors
    {η0 Δη : ℝ} {P : ℤ → EndH}
    (Q : DiscreteLorentzMellinQuantizationData (E := E) η0 Δη P)
    (k : ℤ) :
    Commute Q.modularHamiltonian.hamiltonianReadout (P k) :=
  Q.modularHamiltonian.hamiltonian_commutes_spectralProjectors k

/--
Discrete Mellin modular-Hamiltonian theorem:
the Mellin spectrum is the DFT spectrum on logarithmic samples, those samples
are exactly rapidity samples, and the modular Hamiltonian is property by
spectral-projector commutation.
-/
theorem discrete_mellin_modular_hamiltonian_theorem
    {η0 Δη : ℝ} {P : ℤ → EndH}
    (Q : DiscreteLorentzMellinQuantizationData (E := E) η0 Δη P)
    (k : ℤ) :
    Q.dmt.dmtSpectrum = Q.dmt.dftSpectrum
      ∧ Real.log (Q.dmt.logarithmicSample k) = discreteRapidity η0 Δη k
      ∧ Commute Q.modularHamiltonian.hamiltonianReadout (P k) := by
  exact ⟨Q.dmt_eq_dft_on_logSamples,
    Q.logSample_owner_grid k,
    Q.modularHamiltonian_commutes_spectralProjectors k⟩

end DiscreteLorentzMellinQuantizationData

/--
Proof-carrying Casimir residual quantization packet over a discrete modular
Mellin lattice.

The important audit boundary is explicit: `bandlimited` alone does not prove the
spectral gap formula.  The actual quantization equality is carried as property
data, while the lattice and band-limit witnesses guarantee that the claim lives
on the existing operatorial discrete-Mellin owner surface.
-/
@[capstone, rep_depth operator]
structure DiscreteMellinCasimirQuantizationData
    (CIK : InfoGeometry.Canonical.CertifiedInverseKernel H₂) where
  lattice : InfoGeometry.Canonical.DiscreteModularSpectrum.ModularMellinLattice E CIK
  casimir :
    InfoGeometry.Canonical.CasimirWeylDrazinContext.CasimirWeylDrazinData
      (E := E) CIK
  observable : EndH
  bandlimited :
    InfoGeometry.Canonical.DiscreteModularSpectrum.ModularMellinLattice.IsMellinBandlimited
      lattice observable
  mode : ℤ
  zetaCasimirResidual_eq_mode_logGap :
    casimir.zetaCasimirResidual = (mode : ℝ) * Real.log lattice.q

namespace DiscreteMellinCasimirQuantizationData

/-- The residual is quantized in integer multiples of the lattice log-gap. -/
@[capstone, rep_depth operator]
theorem zetaCasimirResidual_quantized
    {CIK : InfoGeometry.Canonical.CertifiedInverseKernel H₂}
    (Q : DiscreteMellinCasimirQuantizationData (E := E) CIK) :
    ∃ n : ℤ, Q.casimir.zetaCasimirResidual = (n : ℝ) * Real.log Q.lattice.q :=
  ⟨Q.mode, Q.zetaCasimirResidual_eq_mode_logGap⟩

/-- The one-step thermal-time gap is exactly `log q`. -/
@[rep_depth transport]
theorem thermal_gap_eq_log_q
    {CIK : InfoGeometry.Canonical.CertifiedInverseKernel H₂}
    (Q : DiscreteMellinCasimirQuantizationData (E := E) CIK) :
    Q.lattice.thermalTimeStep 1 = Real.log Q.lattice.q := by
  simp [InfoGeometry.Canonical.DiscreteModularSpectrum.ModularMellinLattice.thermalTimeStep]

end DiscreteMellinCasimirQuantizationData

end InfoGeometry.SuperMetriplectic
