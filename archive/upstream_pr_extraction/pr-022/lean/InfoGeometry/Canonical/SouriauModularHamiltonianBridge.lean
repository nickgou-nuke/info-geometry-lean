import InfoGeometry.Canonical.SouriauOperatorialLogPotential
import InfoGeometry.Canonical.SuperchargeModularHamiltonianBridge
import InfoGeometry.Meta.Architecture

open scoped InnerProductSpace

/-!
# InfoGeometry.Canonical.SouriauModularHamiltonianBridge

Calibration bridge between the Drazin/MP bounded modular-Hamiltonian surrogate
and the Souriau operatorial thermodynamic dictionary.

The bridge identifies the Souriau bare generator with the bounded surrogate:

`Khat_beta = K_sur`.

The normalized Souriau modular Hamiltonian is then read back as

`H_mod,beta = K_sur + Φ(beta) • 1`.

The scalar Massieu/free-energy term is a central thermodynamic normalization.
It is not absorbed into the Drazin causal dynamics.

This file does not construct Type III modular flow, does not prove `Q² = Δ`,
and does not construct `log Δ`. It only transports support/evenness properties
from the already-owned `SuperchargeModularHamiltonianBridge`.
-/

namespace InfoGeometry.Canonical.SouriauModularHamiltonianBridge

open InfoGeometry.Canonical
open InfoGeometry.Canonical.SouriauOperatorialLogPotential
open InfoGeometry.Canonical.SuperchargeModularHamiltonianBridge

section Core

variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {LieAlgebra : Type*}

local notation "EndH" => E →L[ℝ] E

noncomputable local instance souriauModularHamiltonianNormedRing : NormedRing EndH :=
  inferInstance
noncomputable local instance souriauModularHamiltonianNormedAlgebra : NormedAlgebra ℝ EndH :=
  inferInstance
noncomputable local instance souriauModularHamiltonianNormedAlgebraRat : NormedAlgebra ℚ EndH :=
  NormedAlgebra.restrictScalars ℚ ℝ EndH
local instance souriauModularHamiltonianTopologicalRing : IsTopologicalRing EndH :=
  inferInstance
local instance souriauModularHamiltonianSMulCommClass : SMulCommClass ℝ EndH EndH :=
  inferInstance
local instance souriauModularHamiltonianIsScalarTower : IsScalarTower ℝ EndH EndH :=
  inferInstance

/--
A minimal calibrated carrier connecting the bounded Drazin/supercharge modular
Hamiltonian surrogate to a Souriau/free-energy/negative-log operator readout.

This carrier is deliberately weaker than `SouriauModularHamiltonianBridge`: it
only records the calibrated origin statement `K_sur = F_Souriau` as external
witness data.
-/
@[rep_depth operator]
structure SouriauModularHamiltonianCarrier (BetaSource : Type*) where
  /-- The already-owned bounded Drazin/supercharge surrogate bridge. -/
  superchargeBridge : SuperchargeModularHamiltonianBridge (E := E)

  /-- External Souriau beta/source coordinate. -/
  betaSource : BetaSource

  /-- Souriau/free-energy/negative-log operator readout. -/
  freeEnergyOperator : EndH

  /-- Optional scalar gauge readout of the Souriau beta/source coordinate. -/
  scalarBetaGauge : BetaSource → ℝ

/--
Calibration predicate: the bounded supercharge surrogate is the Souriau
free-energy/negative-log operator readout.
-/
@[rep_depth operator]
def IsSouriauModularHamiltonianOrigin {BetaSource : Type*}
    (C : SouriauModularHamiltonianCarrier (E := E) BetaSource) : Prop :=
  C.superchargeBridge.Ksur = C.freeEnergyOperator

/-- Readback of the calibrated Souriau/free-energy origin predicate. -/
@[rep_depth operator]
theorem Ksur_eq_freeEnergy_of_origin {BetaSource : Type*}
    (C : SouriauModularHamiltonianCarrier (E := E) BetaSource)
    (h : IsSouriauModularHamiltonianOrigin C) :
    C.superchargeBridge.Ksur = C.freeEnergyOperator :=
  h

/--
Calibration packet connecting the bounded Drazin/supercharge surrogate to the
operatorial Souriau modular Hamiltonian law.

The operator laws are explicit because `QuantumOperatorialSouriauFamily` keeps
`opAdd`, `opScale`, and `opIdentity` abstract witness fields.
-/
@[rep_depth operator]
structure SouriauModularHamiltonianBridge where
  /-- The already-owned bounded Drazin/supercharge surrogate bridge. -/
  superBridge : SuperchargeModularHamiltonianBridge (E := E)

  /-- The operatorial Souriau family carrying `K̂_β`, `Φ(β)`, and `H_mod`. -/
  family : QuantumOperatorialSouriauFamily LieAlgebra EndH

  /-- Calibration socket: the Souriau bare source is the bounded surrogate. -/
  Khat_beta_eq_Ksur : family.Khat_beta = superBridge.Ksur

  /-- Concrete readback of Souriau addition as ambient operator addition. -/
  opAdd_eq_add : ∀ A B : EndH, family.opAdd A B = A + B

  /-- Concrete readback of Souriau scalar scaling as ambient scalar action. -/
  opScale_eq_smul : ∀ r : ℝ, ∀ A : EndH, family.opScale r A = r • A

  /-- Concrete readback of the Souriau identity as the ambient operator unit. -/
  opIdentity_eq_one : family.opIdentity = (1 : EndH)

namespace SouriauModularHamiltonianBridge

variable (B : SouriauModularHamiltonianBridge (E := E) (LieAlgebra := LieAlgebra))

/-- Readback of the calibrated bare Souriau source. -/
@[rep_depth operator]
theorem Khat_beta_eq_Ksur_theorem :
    B.family.Khat_beta = B.superBridge.Ksur :=
  B.Khat_beta_eq_Ksur

/--
The Souriau bare source is the calibrated Drazin super-Hamiltonian surrogate.

This is the negative-log/free-energy readback of the already-owned
`SuperchargeModularHamiltonianBridge`: it does not identify a Hodge star or
central charge with the Hamiltonian. It only transports the explicit
calibration `Ksur = μ_Q • P_D Q² P_D`.
-/
@[rep_depth operator]
theorem Khat_beta_eq_calibrated_regularRestrictedSuperHamiltonian :
    B.family.Khat_beta =
      B.superBridge.modularEnergyUnit •
        DrazinSupercharge.CertifiedInverseKernel.regularRestrictedSuperHamiltonian
          B.superBridge.CIK := by
  rw [B.Khat_beta_eq_Ksur, B.superBridge.Ksur_law]

/--
The normalized Souriau modular Hamiltonian is the Drazin/supercharge surrogate
plus the Massieu/free-energy scalar times the identity.
-/
@[rep_depth operator]
theorem modularHamiltonian_eq_Ksur_add_partitionPotential_one :
    B.family.modularHamiltonian =
      B.superBridge.Ksur + B.family.partitionPotential • (1 : EndH) := by
  calc
    B.family.modularHamiltonian
        = B.family.opAdd B.family.Khat_beta
            (B.family.opScale B.family.partitionPotential B.family.opIdentity) := by
            exact B.family.modularHamiltonian_eq
    _ = B.family.opAdd B.superBridge.Ksur
            (B.family.opScale B.family.partitionPotential B.family.opIdentity) := by
            rw [B.Khat_beta_eq_Ksur]
    _ = B.superBridge.Ksur
            + B.family.opScale B.family.partitionPotential B.family.opIdentity := by
            rw [B.opAdd_eq_add B.superBridge.Ksur
              (B.family.opScale B.family.partitionPotential B.family.opIdentity)]
    _ = B.superBridge.Ksur
            + B.family.partitionPotential • B.family.opIdentity := by
            rw [B.opScale_eq_smul B.family.partitionPotential B.family.opIdentity]
    _ = B.superBridge.Ksur + B.family.partitionPotential • (1 : EndH) := by
            rw [B.opIdentity_eq_one]

/--
The normalized Souriau modular Hamiltonian is the calibrated regular compressed
super-Hamiltonian plus the Massieu/free-energy scalar identity term.
-/
@[rep_depth operator]
theorem modularHamiltonian_eq_calibrated_regularRestrictedSuperHamiltonian_add_partitionPotential_one :
    B.family.modularHamiltonian =
      B.superBridge.modularEnergyUnit •
          DrazinSupercharge.CertifiedInverseKernel.regularRestrictedSuperHamiltonian
            B.superBridge.CIK
        + B.family.partitionPotential • (1 : EndH) := by
  rw [B.modularHamiltonian_eq_Ksur_add_partitionPotential_one, B.superBridge.Ksur_law]

/-- The Souriau bare generator is left-supported on the Drazin regular sector. -/
@[rep_depth operator]
theorem spectralProjector_mul_Khat_beta :
    B.superBridge.CIK.spectralProjector * B.family.Khat_beta = B.family.Khat_beta := by
  rw [B.Khat_beta_eq_Ksur]
  exact B.superBridge.spectralProjector_mul_Ksur

/-- The Souriau bare generator is right-supported on the Drazin regular sector. -/
@[rep_depth operator]
theorem Khat_beta_mul_spectralProjector :
    B.family.Khat_beta * B.superBridge.CIK.spectralProjector = B.family.Khat_beta := by
  rw [B.Khat_beta_eq_Ksur]
  exact B.superBridge.Ksur_mul_spectralProjector

/-- The Drazin defect sector annihilates the Souriau bare generator on the left. -/
@[rep_depth operator]
theorem spectralComplementaryProjector_mul_Khat_beta_eq_zero :
    B.superBridge.CIK.spectralComplementaryProjector * B.family.Khat_beta = 0 := by
  rw [B.Khat_beta_eq_Ksur]
  exact B.superBridge.spectralComplementaryProjector_mul_Ksur_eq_zero

/-- The Drazin defect sector annihilates the Souriau bare generator on the right. -/
@[rep_depth operator]
theorem Khat_beta_mul_spectralComplementaryProjector_eq_zero :
    B.family.Khat_beta * B.superBridge.CIK.spectralComplementaryProjector = 0 := by
  rw [B.Khat_beta_eq_Ksur]
  exact B.superBridge.Ksur_mul_spectralComplementaryProjector_eq_zero

/-- The Souriau bare generator is even for the Drazin spectral grading. -/
@[rep_depth operator]
theorem Khat_beta_commutes_GammaS :
    B.family.Khat_beta * B.superBridge.CIK.GammaS =
      B.superBridge.CIK.GammaS * B.family.Khat_beta := by
  rw [B.Khat_beta_eq_Ksur]
  exact B.superBridge.Ksur_commutes_GammaS

/-- The Souriau bare generator lies in the spectrally compact/even lane. -/
@[rep_depth operator]
theorem Khat_beta_isSpectralCompact :
    let T := B.superBridge.CIK.toInformationCartanTriple
    T.IsSpectralCompact B.family.Khat_beta := by
  rw [B.Khat_beta_eq_Ksur]
  exact B.superBridge.Ksur_isSpectralCompact

/--
Adding the Souriau Massieu scalar does not break spectral evenness: if `K_sur`
commutes with `Γ_S`, then the normalized modular Hamiltonian also commutes with
`Γ_S`.
-/
@[rep_depth operator]
theorem modularHamiltonian_commutes_GammaS :
    B.family.modularHamiltonian * B.superBridge.CIK.GammaS =
      B.superBridge.CIK.GammaS * B.family.modularHamiltonian := by
  rw [B.modularHamiltonian_eq_Ksur_add_partitionPotential_one]
  have hK :
      B.superBridge.Ksur * B.superBridge.CIK.GammaS =
        B.superBridge.CIK.GammaS * B.superBridge.Ksur :=
    B.superBridge.Ksur_commutes_GammaS
  have hScalar :
      (B.family.partitionPotential • (1 : EndH)) * B.superBridge.CIK.GammaS =
        B.superBridge.CIK.GammaS * (B.family.partitionPotential • (1 : EndH)) := by
    simp
  rw [add_mul, mul_add, hK, hScalar]

/--
The normalized Souriau modular Hamiltonian stays in the spectrally compact/even
lane inherited from `K_sur`.
-/
@[rep_depth operator]
theorem modularHamiltonian_isSpectralCompact :
    let T := B.superBridge.CIK.toInformationCartanTriple
    T.IsSpectralCompact B.family.modularHamiltonian := by
  let T := B.superBridge.CIK.toInformationCartanTriple
  rw [CartanDecomposition.InformationCartanTriple.isSpectralCompact_iff_commute
        T B.superBridge.CIK.hDrazin]
  simpa [T, CertifiedInverseKernel.GammaS, CertifiedInverseKernel.cartanTriple,
    CertifiedInverseKernel.toInformationCartanTriple] using
    B.modularHamiltonian_commutes_GammaS

end SouriauModularHamiltonianBridge

end Core

end InfoGeometry.Canonical.SouriauModularHamiltonianBridge
