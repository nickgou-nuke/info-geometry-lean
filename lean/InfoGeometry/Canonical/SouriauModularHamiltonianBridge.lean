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
variable [AddMonoid LieAlgebra]

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

This carrier is deliberately weaker than the calibrated bridge structure: it
only records the calibrated origin statement `K_sur = F_Souriau` as external
property data.
-/
@[rep_depth operator]
structure SouriauModularHamiltonianCarrier (BetaSource : Type*) where
  /-- The already-owned bounded Drazin/supercharge surrogate bridge. -/
  superchargeBridge : SuperchargeModularHamiltonianBridge.Bridge (E := E)

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

/--
Calibration packet connecting the bounded Drazin/supercharge surrogate to the
operatorial Souriau modular Hamiltonian law.

The operator laws use the native additive, real-module, and unital structure of
the bounded operator algebra.
-/
@[rep_depth operator]
structure Bridge where
  /-- The already-owned bounded Drazin/supercharge surrogate bridge. -/
  superBridge : SuperchargeModularHamiltonianBridge.Bridge (E := E)

  /-- The operatorial Souriau family carrying `K̂_β`, `Φ(β)`, and `H_mod`. -/
  family : QuantumOperatorialSouriauFamily LieAlgebra EndH

  /-- Calibration interface: the Souriau bare source is the bounded surrogate. -/
  Khat_beta_eq_Ksur : family.Khat_beta = superBridge.Ksur

namespace Bridge

variable (B : Bridge (E := E) (LieAlgebra := LieAlgebra))

/-- Readback of the calibrated bare Souriau source. -/
@[rep_depth operator]
theorem Khat_beta_eq_Ksur_theorem :
    B.family.Khat_beta = B.superBridge.Ksur :=
  B.Khat_beta_eq_Ksur

/-- Souriau addition is the native bounded-operator addition. -/
@[rep_depth operator]
theorem opAdd_eq_add (A C : EndH) :
    B.family.opAdd A C = A + C :=
  B.family.opAdd_eq_add A C

/-- Souriau scaling is the native real scalar action on bounded operators. -/
@[rep_depth operator]
theorem opScale_eq_smul (r : ℝ) (A : EndH) :
    B.family.opScale r A = r • A :=
  B.family.opScale_eq_smul r A

/-- Souriau's identity is the native bounded-operator unit. -/
@[rep_depth operator]
theorem opIdentity_eq_one :
    B.family.opIdentity = (1 : EndH) :=
  B.family.opIdentity_eq_one

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
  rw [B.Khat_beta_eq_Ksur, B.superBridge.Ksur_eq]

/--
The normalized Souriau modular Hamiltonian is the Drazin/supercharge surrogate
plus the Massieu/free-energy scalar times the identity.
-/
@[rep_depth operator]
theorem modularHamiltonian_eq_Ksur_add_partitionPotential_one :
    B.family.modularHamiltonian =
      B.superBridge.Ksur + B.family.partitionPotential • (1 : EndH) := by
  rw [QuantumOperatorialSouriauFamily.modularHamiltonian,
    B.Khat_beta_eq_Ksur]

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
  rw [B.modularHamiltonian_eq_Ksur_add_partitionPotential_one, B.superBridge.Ksur_eq]

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

end Bridge

end Core

section ExpectationCalibration

/--
A real expectation state for the Souriau/free-energy readout layer.

In applications this is the compressed state `φ_A`.  No traciality or full
Tomita--Takesaki modular theory is asserted here.
-/
@[rep_depth operator]
structure RealExpectationState
    (Obs : Type*) [One Obs] [Mul Obs] [Star Obs] where
  expect : Obs → ℝ
  unital : expect 1 = 1
  positive : ∀ a : Obs, 0 ≤ expect (star a * a)

/--
Souriau free-energy owner lane.

`freeEnergyObservable` is the operator-valued representative, when the local
Souriau model supplies one.  `freeEnergy` is the scalar thermodynamic readout.
-/
@[rep_depth operator]
structure SouriauFreeEnergyOwner
    (Source Obs : Type*) where
  freeEnergyObservable : Source → Obs
  freeEnergy : Source → ℝ

/--
Bounded Drazin quadratic modular-Hamiltonian surrogate.

Intended formula:

`K_sur = μ_Q • (P_D * (Q * Q) * P_D)`.

This is a bounded/compressed surrogate interface.  It is not asserted to be the
unbounded Type III modular Hamiltonian.
-/
@[rep_depth operator]
structure BoundedModularHamiltonianSurrogate
    (Obs : Type*) [One Obs] [Mul Obs] [Star Obs] [SMul ℝ Obs] where
  μ_Q : ℝ
  P_D : Obs
  Q : Obs
  K_sur : Obs
  P_D_idempotent : P_D * P_D = P_D
  P_D_self_adjoint : star P_D = P_D
  Q_self_adjoint : star Q = Q
  K_sur_eq : K_sur = μ_Q • (P_D * (Q * Q) * P_D)

namespace BoundedModularHamiltonianSurrogate

variable {Obs : Type*} [One Obs] [Mul Obs] [Star Obs] [SMul ℝ Obs]
variable (K : BoundedModularHamiltonianSurrogate Obs)

/-- Formula readback for the bounded Drazin quadratic surrogate. -/
@[rep_depth operator]
theorem formula :
    K.K_sur = K.μ_Q • (K.P_D * (K.Q * K.Q) * K.P_D) :=
  K.K_sur_eq

end BoundedModularHamiltonianSurrogate

/--
Operator-level calibration.

This property is required before identifying the bounded Drazin surrogate with a
Souriau operator-valued free-energy representative.
-/
@[rep_depth operator]
def IsOperatorCalibratedBySouriau
    {Source Obs : Type*}
    [One Obs] [Mul Obs] [Star Obs] [SMul ℝ Obs]
    (S : SouriauFreeEnergyOwner Source Obs)
    (K : BoundedModularHamiltonianSurrogate Obs)
    (src : Source) : Prop :=
  K.K_sur = S.freeEnergyObservable src

/--
Expectation-level calibration.

This property states that the compressed expectation of the Souriau operator
representative is the scalar Souriau free energy.
-/
@[rep_depth operator]
def IsSouriauFreeEnergyReadoutCalibrated
    {Source Obs : Type*}
    [One Obs] [Mul Obs] [Star Obs]
    (φA : RealExpectationState Obs)
    (S : SouriauFreeEnergyOwner Source Obs)
    (src : Source) : Prop :=
  φA.expect (S.freeEnergyObservable src) = S.freeEnergy src

/--
Operator-level calibrated equality.

This is not automatic.  It is exactly the supplied operator calibration property.
-/
@[rep_depth operator]
theorem surrogate_eq_souriau_freeEnergyObservable
    {Source Obs : Type*}
    [One Obs] [Mul Obs] [Star Obs] [SMul ℝ Obs]
    (S : SouriauFreeEnergyOwner Source Obs)
    (K : BoundedModularHamiltonianSurrogate Obs)
    (src : Source)
    (hOp : IsOperatorCalibratedBySouriau S K src) :
    K.K_sur = S.freeEnergyObservable src :=
  hOp

/--
Main calibrated expectation bridge.

If the bounded Drazin surrogate is operator-calibrated by the Souriau
free-energy observable, and that Souriau observable has the correct compressed
expectation readout, then the surrogate expectation is the scalar Souriau free
energy:

`φ_A(K_sur) = F_Souriau(src)`.
-/
@[rep_depth operator]
theorem surrogate_expectation_eq_souriau_free_energy
    {Source Obs : Type*}
    [One Obs] [Mul Obs] [Star Obs] [SMul ℝ Obs]
    (φA : RealExpectationState Obs)
    (S : SouriauFreeEnergyOwner Source Obs)
    (K : BoundedModularHamiltonianSurrogate Obs)
    (src : Source)
    (hOp : IsOperatorCalibratedBySouriau S K src)
    (hRead : IsSouriauFreeEnergyReadoutCalibrated φA S src) :
    φA.expect K.K_sur = S.freeEnergy src := by
  rw [hOp]
  exact hRead

end ExpectationCalibration

end InfoGeometry.Canonical.SouriauModularHamiltonianBridge
