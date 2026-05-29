import InfoGeometry.Canonical.SouriauDensityWeightContext
import InfoGeometry.Canonical.PhaseSpaceConformalKKTBridge
import InfoGeometry.Canonical.ChiralCartanCore
import InfoGeometry.Canonical.OnsagerReciprocity
import InfoGeometry.Canonical.WeylGaugeField
import InfoGeometry.Canonical.SuperJordanLie
import InfoGeometry.Canonical.GrandCanonicalFockNumberBridge
import InfoGeometry.Canonical.ChiralOperatorConeClosure
import InfoGeometry.Canonical.Cl11PolarizedBasis
import InfoGeometry.Core.SymmetricLieMetric
import InfoGeometry.Krein.Thermal

/-!
# InfoGeometry.Canonical.SouriauConformalKKTContext

Context bridge from finite Souriau density-weight shadows to the existing
conformal/KKT grade-zero corridor.

This file does not identify finite Souriau states with the full conformal
operator algebra.  It records the explicit context in which:

- a finite Souriau number/charge weight selects the density-weight correction
  in the doubled-carrier transport generator, and
- an independent certified conformal/KKT carrier supplies the grade-zero
  dilation and chiral-grading outputs.
-/

open scoped InnerProductSpace

namespace InfoGeometry.Canonical.SouriauConformalKKT

open InfoGeometry.Canonical.SouriauDensityWeight
open InfoGeometry.Canonical.SouriauThermodynamics
open InfoGeometry.Canonical.PhaseSpaceConformalKKTBridge
open InfoGeometry.Canonical.ConformalUnification
open InfoGeometry.Canonical.ChiralCartanCore
open InfoGeometry.Canonical.KKTCore
open InfoGeometry.Canonical.InformationCalculus.ModularRadonNikodymData
open InfoGeometry.Canonical.OnsagerReciprocity
open InfoGeometry.Canonical.BogoliubovFockSuper
open InfoGeometry.Canonical.GrandCanonicalFockNumberBridge
open InfoGeometry.Canonical.GrandCanonicalGaugePotentialBridge
open InfoGeometry.Canonical.ChiralOperatorConeClosure
open InfoGeometry.GrandCanonical
open InfoGeometry.Krein
open InfoGeometry.Quantum
open InfoGeometry.Core.SymmetricLieAlgebra

variable {α : Type _}
variable {H : Type}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/--
Explicit context joining a finite Souriau density-weight shadow to one
certified conformal/KKT carrier on the same doubled Hilbert carrier.
-/
structure SouriauConformalKKTContext where
  density : SouriauDensityWeightContext (α := α) (E := H)
  CCI : CertifiedConformalInference (DoubledSpace H)
-- theorem-class: bridge
  hA : IsGOne (doubledSpaceCl11Action (E := H)) CCI.A
-- theorem-class: bridge
  hAMP : IsGNegOne (doubledSpaceCl11Action (E := H)) CCI.A_MP

namespace SouriauConformalKKTContext

variable (C : SouriauConformalKKTContext (α := α) (H := H))

local notation "H₂" => DoubledSpace H
local notation "EndH₂" => H₂ →L[ℝ] H₂

/-! ## Finite conformal-character shadow -/

/--
Finite conformal/Souriau weight pairing selected by the context.

This is the finite representation shadow of `⟨J(x), β⟩`; the operator carrier
is held separately in `CCI`.
-/
@[rep_depth thermo]
def finiteWeightPairing (x : α) : ℝ :=
  geometricTemperatureWeightPairing C.density.T (souriauWeightAt C.density.M x)

/--
Finite unnormalized conformal-character density `exp(-⟨J(x),β⟩)`.
-/
@[rep_depth thermo]
noncomputable def finiteUnnormalizedDensity (x : α) : ℝ :=
  Real.exp (-(C.finiteWeightPairing x))

/--
Finite conformal-character partition shadow.  In this finite context it is
the same object as the Souriau/Gibbs partition.
-/
@[rep_depth thermo]
noncomputable def finitePartition [Fintype α] : ℝ :=
  ∑ x, C.finiteUnnormalizedDensity x

/--
Finite Massieu/log-character potential attached to the context.
-/
@[rep_depth thermo]
noncomputable def finiteMassieu [Fintype α] : ℝ :=
  Real.log C.finitePartition

/--
Finite admissibility for this shadow: the partition is strictly positive.
This is not the full infinite-dimensional cone condition; it is the exact
finite normalizability condition available in this context.
-/
@[rep_depth thermo]
def IsFiniteAdmissible [Fintype α] : Prop :=
  0 < C.finitePartition

-- theorem-class: bridge
/-- The finite context density is the owner Souriau unnormalized density. -/
@[rep_depth thermo]
theorem finiteUnnormalizedDensity_eq_souriauUnnormalizedDensity (x : α) :
    C.finiteUnnormalizedDensity x =
      souriauUnnormalizedDensity C.density.M C.density.T x := by
  rfl

-- theorem-class: bridge
/-- The finite conformal-character partition is the owner Souriau partition. -/
@[rep_depth thermo]
theorem finitePartition_eq_souriauPartition [Fintype α] :
    C.finitePartition = souriauPartition C.density.M C.density.T := by
  rfl

-- theorem-class: bridge
/-- In a finite nonempty context, admissibility is automatic from positivity. -/
@[rep_depth thermo]
theorem finiteAdmissible [Fintype α] [Nonempty α] :
    C.IsFiniteAdmissible := by
  simpa [IsFiniteAdmissible, finitePartition_eq_souriauPartition] using
    souriauPartition_pos C.density.M C.density.T

-- theorem-class: bridge
/-- The finite Massieu/log-character potential is the owner Souriau Massieu potential. -/
@[rep_depth thermo]
theorem finiteMassieu_eq_souriauMassieuPotential [Fintype α] [Nonempty α] :
    C.finiteMassieu =
      souriauMassieuPotential C.density.M C.density.T := by
  rw [finiteMassieu, finitePartition_eq_souriauPartition,
    souriauMassieuPotential_eq_log_partition]

-- theorem-class: bridge
/--
The Souriau density-weight side exposes the existing operatorial generator:
Souriau temperature vector plus the selected number/charge-weighted dilation.
-/
theorem liftedTransportGenerator_eq_souriau_add_number_weighted_dilationOperator :
    C.density.liftedTransportGenerator =
      ThermodynamicGenerator.souriauTemperatureVector (E := H) C.density.P C.density.ψ
        + C.density.densityWeight • dilationOperator (E := H) :=
  C.density.liftedTransportGenerator_eq_souriau_add_number_weighted_dilationOperator

-- theorem-class: bridge
/--
On the certified conformal/KKT side, the conformal dilation is the certified
inverse-kernel dilation gap.
-/
theorem conformalD_eq_dilationGap :
    C.CCI.toConformalInference.D = C.CCI.toCertifiedInverseKernel.dilationGap :=
  CertifiedConformalInference.D_eq_dilationGap C.CCI

-- theorem-class: bridge
/--
Under the explicit KKT wing hypotheses carried by the context, the conformal
dilation generator is grade zero.
-/
theorem conformalD_isGZero :
    IsGZero (doubledSpaceCl11Action (E := H)) C.CCI.toConformalInference.D :=
  CertifiedConformalInference.D_isGZero
    (X := doubledSpaceCl11Action (E := H)) C.CCI C.hA C.hAMP

-- theorem-class: bridge
/--
Under the same explicit KKT wing hypotheses, the conformal chiral grading is a
grade-zero output.
-/
theorem chiralGrading_isGZero :
    IsGZero (doubledSpaceCl11Action (E := H))
      (InfoGeometry.Canonical.ChiralCartanCore.chiralGrading C.CCI.toConformalInference) :=
  CertifiedConformalInference.chiralGrading_isGZero
    (X := doubledSpaceCl11Action (E := H)) C.CCI C.hA C.hAMP

end SouriauConformalKKTContext

/-! ## Operatorial conformal Gibbs-Souriau partition context -/

local notation "H₂" => DoubledSpace H
local notation "EndH₂" => H₂ →L[ℝ] H₂

noncomputable local instance : NormedRing EndH₂ := inferInstance
noncomputable local instance : NormedAlgebra ℝ EndH₂ := inferInstance
noncomputable local instance : NormedSpace ℝ EndH₂ := inferInstance
-- theorem-class: bridge
local instance : IsTopologicalRing EndH₂ := inferInstance
-- theorem-class: bridge
local instance : CompleteSpace EndH₂ := inferInstance

/--
Operator-first conformal Gibbs-Souriau context.

The finite Souriau state remains only the representation shadow carried by
`base`.  The actual conformal Gibbs object here is the noncommutative operator
generator

`β = b • P + ω • M + α • D + c • K`

on the doubled Krein carrier, together with a linear readout `ω` and an
explicit admissible cone.
-/
@[rep_depth transport]
structure ConformalGibbsSouriauOperatorContext where
  base : SouriauConformalKKTContext (α := α) (H := H)
  /-- Chosen Cartan/rotation generator, the `M` lane in `[K,P]=2(ηD-M)`. -/
  cartanGenerator : EndH₂
  translationPotential : ℝ
  cartanPotential : ℝ
  dilationPotential : ℝ
  specialConformalPotential : ℝ
  readout : EndH₂ →L[ℝ] ℝ
  admissibleCone : Set EndH₂

namespace ConformalGibbsSouriauOperatorContext

variable (C : ConformalGibbsSouriauOperatorContext (α := α) (H := H))

/-- Translation generator `P` in the certified conformal carrier. -/
@[rep_depth transport]
noncomputable def PGenerator : EndH₂ :=
  C.base.CCI.toConformalInference.P

/-- Dilation generator `D` in the certified conformal carrier. -/
@[rep_depth transport]
noncomputable def DGenerator : EndH₂ :=
  C.base.CCI.toConformalInference.D

/-- Special conformal generator `K` in the certified conformal carrier. -/
@[rep_depth transport]
noncomputable def KGenerator : EndH₂ :=
  C.base.CCI.toConformalInference.K

/--
Operatorial conformal geometric temperature.

This is the noncommutative replacement for the scalar inverse temperature:
it is a Lie-algebra element on the doubled Krein carrier, not a diagonal
finite-state list.
-/
@[rep_depth transport]
noncomputable def conformalGeometricTemperature : EndH₂ :=
  C.translationPotential • C.PGenerator
    + C.cartanPotential • C.cartanGenerator
      + C.dilationPotential • C.DGenerator
        + C.specialConformalPotential • C.KGenerator

/-- Operatorial admissibility: the conformal temperature lies in the chosen cone. -/
@[rep_depth transport]
def IsConeAdmissible : Prop :=
  C.conformalGeometricTemperature ∈ C.admissibleCone

/--
Operatorial conformal partition function
`Z(β)=ω(exp(-β))`, represented through the repo owner
`informationPartitionFunction`.
-/
@[rep_depth transport]
noncomputable def operatorPartition : ℝ :=
  informationPartitionFunction C.readout (-C.conformalGeometricTemperature) 1

/--
Operatorial Weyl character of the conformal Gibbs-Souriau generator.

This is the infinite/dimension-agnostic replacement for a finite Weyl weight
sum: the "character" is the chosen operator readout of the noncommutative Gibbs
exponential on the doubled Krein carrier.
-/
@[rep_depth transport]
noncomputable def operatorWeylCharacter : ℝ :=
  C.readout (NormedSpace.exp (-C.conformalGeometricTemperature))

/-- Operatorial Massieu/log-character potential `Φ(β)=log Z(β)`. -/
@[rep_depth transport]
noncomputable def operatorMassieu : ℝ :=
  Real.log C.operatorPartition

/-- Full operatorial admissibility: cone membership plus positive partition. -/
@[rep_depth transport]
def IsOperatorAdmissible : Prop :=
  C.IsConeAdmissible ∧ 0 < C.operatorPartition

-- theorem-class: bridge
/-- The operator partition is the readout of the noncommutative Gibbs exponential. -/
@[rep_depth transport]
theorem operatorPartition_eq_readout_exp_neg_temperature :
    C.operatorPartition =
      C.readout (NormedSpace.exp (-C.conformalGeometricTemperature)) := by
  simp [operatorPartition, informationPartitionFunction]

-- theorem-class: bridge
/--
The operatorial Souriau partition is the operatorial Weyl character.

This is not the finite Weyl character formula over listed weights.  It is the
repo-native noncommutative character/readout identity on `EndH₂`.
-/
@[rep_depth transport]
theorem operatorPartition_eq_operatorWeylCharacter :
    C.operatorPartition = C.operatorWeylCharacter := by
  rw [operatorPartition_eq_readout_exp_neg_temperature]
  rfl

-- theorem-class: bridge
/-- The Massieu potential is the logarithm of the operator partition. -/
@[rep_depth transport]
theorem operatorMassieu_eq_log_partition :
    C.operatorMassieu = Real.log C.operatorPartition := by
  rfl

/-- Souriau mean moment readout `Q=-dΦ`, evaluated on the conformal β lane. -/
@[rep_depth transport]
noncomputable def operatorMeanMoment : ℝ :=
  -C.readout (-C.conformalGeometricTemperature)

-- theorem-class: bridge
/-- The first-moment readout is the readout of the conformal temperature itself. -/
@[rep_depth transport]
theorem operatorMeanMoment_eq_readout_temperature :
    C.operatorMeanMoment = C.readout C.conformalGeometricTemperature := by
  simp [operatorMeanMoment]

/-- Operatorial conformal moment pairing with an observable seed. -/
@[rep_depth transport]
noncomputable def operatorMomentPairing (A : EndH₂) : ℝ :=
  C.readout (A * C.conformalGeometricTemperature)

/--
Operatorial Hessian/Onsager response of the conformal Massieu surface along
two noncommutative perturbation channels.
-/
@[rep_depth transport]
noncomputable def operatorConformalResponse (X Y : EndH₂) : ℝ :=
  responseCoefficient (E := H) C.base.density.P X Y C.conformalGeometricTemperature

-- theorem-class: bridge
/-- Operatorial conformal Hessian response is symmetric in its perturbation channels. -/
@[rep_depth transport]
theorem operatorConformalResponse_swap (X Y : EndH₂) :
    C.operatorConformalResponse X Y = C.operatorConformalResponse Y X := by
  simpa [operatorConformalResponse] using
    responseCoefficient_swap (E := H) C.base.density.P X Y C.conformalGeometricTemperature

/-- Operator-level TKK master relation for the chosen conformal Cartan generator. -/
@[rep_depth transport]
def SatisfiesOperatorTKKMasterRelation (η : ℝ) : Prop :=
  C.KGenerator * C.PGenerator - C.PGenerator * C.KGenerator =
    2 • (η • C.DGenerator - C.cartanGenerator)

-- theorem-class: bridge
/--
The operatorial conformal generator package exposes the same `P,D,K,M` packet
used by the TKK master relation and the Gibbs-Souriau partition.
-/
@[rep_depth transport]
theorem conformalTemperature_eq_components :
    C.conformalGeometricTemperature =
      C.translationPotential • C.PGenerator
        + C.cartanPotential • C.cartanGenerator
          + C.dilationPotential • C.DGenerator
            + C.specialConformalPotential • C.KGenerator := by
  rfl

end ConformalGibbsSouriauOperatorContext

/-! ## Operatorial boson/fermion supercharacter split -/

/--
Operatorial boson/fermion statistics context for the conformal
Gibbs-Souriau partition.

The statistical split is carried by readout functionals on the same doubled
operator carrier.  The bosonic sector contributes with positive sign, the
fermionic sector with negative sign, and the total Souriau/Weyl readout is
their difference.  No finite weight enumeration is used here.
-/
@[rep_depth transport]
structure OperatorialWeylSupercharacterContext where
  gibbs : ConformalGibbsSouriauOperatorContext (α := α) (H := H)
  bosonicReadout : EndH₂ →L[ℝ] ℝ
  fermionicReadout : EndH₂ →L[ℝ] ℝ
-- theorem-class: bridge
  readout_eq_bosonic_sub_fermionic :
    gibbs.readout = bosonicReadout - fermionicReadout

namespace OperatorialWeylSupercharacterContext

variable (S : OperatorialWeylSupercharacterContext (α := α) (H := H))

/--
Construct a boson/fermion supercharacter split from a chosen fermionic
correction readout.

The bosonic readout is `total + fermionic`, so the signed supertrace readout
is constructively `(total + fermionic) - fermionic = total`.  This removes the
need to assume the split equation separately when the model supplies the
fermionic correction functional.
-/
@[rep_depth transport]
noncomputable def ofFermionicCorrection
    (gibbs : ConformalGibbsSouriauOperatorContext (α := α) (H := H))
    (fermionicReadout : EndH₂ →L[ℝ] ℝ) :
    OperatorialWeylSupercharacterContext (α := α) (H := H) where
  gibbs := gibbs
  bosonicReadout := gibbs.readout + fermionicReadout
  fermionicReadout := fermionicReadout
  readout_eq_bosonic_sub_fermionic := by
    ext A
    simp

/--
Pure bosonic constructor: the fermionic correction is zero, so the
supercharacter context is built without any external split hypothesis.
-/
@[rep_depth transport]
noncomputable def ofPureBosonicReadout
    (gibbs : ConformalGibbsSouriauOperatorContext (α := α) (H := H)) :
    OperatorialWeylSupercharacterContext (α := α) (H := H) :=
  ofFermionicCorrection (α := α) (H := H) gibbs 0

/-- Bosonic positive-sign character contribution. -/
@[rep_depth transport]
noncomputable def bosonicCharacter : ℝ :=
  S.bosonicReadout (NormedSpace.exp (-S.gibbs.conformalGeometricTemperature))

/-- Fermionic negative-sign character contribution. -/
@[rep_depth transport]
noncomputable def fermionicCharacter : ℝ :=
  S.fermionicReadout (NormedSpace.exp (-S.gibbs.conformalGeometricTemperature))

/-- Supercharacter/supertrace shadow: bosonic contribution minus fermionic contribution. -/
@[rep_depth transport]
noncomputable def operatorSupercharacter : ℝ :=
  S.bosonicCharacter - S.fermionicCharacter

-- theorem-class: bridge
/--
The Souriau partition equals the operatorial supercharacter whenever the
partition readout is the bosonic-minus-fermionic readout.

This is the rigorous operatorial version of the statistics sign rule:
bosonic channels enter with positive sign and fermionic channels with negative
sign in the character/supertrace.  The proof is only linear-map evaluation on
the doubled carrier.
-/
@[rep_depth transport]
theorem operatorPartition_eq_operatorSupercharacter :
    S.gibbs.operatorPartition = S.operatorSupercharacter := by
  rw [ConformalGibbsSouriauOperatorContext.operatorPartition_eq_readout_exp_neg_temperature]
  rw [S.readout_eq_bosonic_sub_fermionic]
  rfl

-- theorem-class: bridge
/-- The Massieu potential is the logarithm of the boson-minus-fermion supercharacter. -/
@[rep_depth transport]
theorem operatorMassieu_eq_log_operatorSupercharacter :
    S.gibbs.operatorMassieu = Real.log S.operatorSupercharacter := by
  rw [ConformalGibbsSouriauOperatorContext.operatorMassieu_eq_log_partition]
  rw [S.operatorPartition_eq_operatorSupercharacter]

-- theorem-class: bridge
/--
For the constructive fermionic-correction constructor, the partition is the
supercharacter without carrying a separate split-equality hypothesis.
-/
@[rep_depth transport]
theorem operatorPartition_eq_operatorSupercharacter_ofFermionicCorrection
    (gibbs : ConformalGibbsSouriauOperatorContext (α := α) (H := H))
    (fermionicReadout : EndH₂ →L[ℝ] ℝ) :
    gibbs.operatorPartition =
      (ofFermionicCorrection (α := α) (H := H) gibbs fermionicReadout).operatorSupercharacter :=
  (ofFermionicCorrection (α := α) (H := H) gibbs fermionicReadout).operatorPartition_eq_operatorSupercharacter

-- theorem-class: bridge
/--
For the constructive fermionic-correction constructor, the Massieu potential is
the logarithm of the operatorial boson-minus-fermion supercharacter without
carrying a separate split-equality hypothesis.
-/
@[rep_depth transport]
theorem operatorMassieu_eq_log_operatorSupercharacter_ofFermionicCorrection
    (gibbs : ConformalGibbsSouriauOperatorContext (α := α) (H := H))
    (fermionicReadout : EndH₂ →L[ℝ] ℝ) :
    gibbs.operatorMassieu =
      Real.log
        ((ofFermionicCorrection (α := α) (H := H) gibbs fermionicReadout).operatorSupercharacter) :=
  (ofFermionicCorrection (α := α) (H := H) gibbs fermionicReadout).operatorMassieu_eq_log_operatorSupercharacter

-- theorem-class: bridge
/--
Pure bosonic special case: the operatorial Souriau partition is its
supercharacter with zero fermionic correction.
-/
@[rep_depth transport]
theorem operatorPartition_eq_operatorSupercharacter_ofPureBosonicReadout
    (gibbs : ConformalGibbsSouriauOperatorContext (α := α) (H := H)) :
    gibbs.operatorPartition =
      (ofPureBosonicReadout (α := α) (H := H) gibbs).operatorSupercharacter :=
  (ofPureBosonicReadout (α := α) (H := H) gibbs).operatorPartition_eq_operatorSupercharacter

-- theorem-class: bridge
/--
Pure bosonic special case: the Massieu potential is the logarithm of the
operatorial supercharacter with zero fermionic correction.
-/
@[rep_depth transport]
theorem operatorMassieu_eq_log_operatorSupercharacter_ofPureBosonicReadout
    (gibbs : ConformalGibbsSouriauOperatorContext (α := α) (H := H)) :
    gibbs.operatorMassieu =
      Real.log ((ofPureBosonicReadout (α := α) (H := H) gibbs).operatorSupercharacter) :=
  (ofPureBosonicReadout (α := α) (H := H) gibbs).operatorMassieu_eq_log_operatorSupercharacter

end OperatorialWeylSupercharacterContext

/-! ## Weyl/TKK/KKT/Jordan-Lie operator closure package -/

/-! ### Self-dual/chiral light-cone owner certificate -/

/--
Source-backed certificate for the causal chiral light-cone operator lane.

The data lives on the same doubled carrier as the conformal Gibbs-Souriau
context.  Its proof content is imported from the owner surfaces:

* `Cl11PolarizedBasis`: the circular `u+`/`u-` light-cone channels;
* `ChiralOperatorConeClosure`: those channels lie in the chiral operator cone
  when the split grading is the certified spectral grading;
* `KKTCore`: the mixed `u+`/`u-` commutator closes in grade zero.
-/
@[rep_depth transport]
structure SelfDualChiralLightConeCertificate where
  CIK : CertifiedInverseKernel H₂
  Xcl : RealSplitCl11Action H₂
  A : EndH₂
  B : EndH₂
-- theorem-class: bridge
  hGamma : Xcl.eps = CIK.GammaS

namespace SelfDualChiralLightConeCertificate

variable (S : SelfDualChiralLightConeCertificate (H := H))

-- theorem-class: bridge
/-- The `u+` light-cone channel lies in the certified chiral cone. -/
@[rep_depth transport]
theorem uPlus_mem_chiralCone :
    IsInChiralOperatorCone S.CIK
      (InfoGeometry.Canonical.Cl11PolarizedBasis.uPlus S.Xcl S.A) := by
  rw [isInChiralOperatorCone_iff_anticommute_GammaS (CIK := S.CIK)]
  rw [← S.hGamma]
  have hOdd :=
    InfoGeometry.Canonical.Cl11PolarizedBasis.eps_mul_eq_neg_mul_eps_of_isUPlus
      (X := S.Xcl) (A := S.A)
  rw [hOdd]
  simp

-- theorem-class: bridge
/-- The `u-` light-cone channel lies in the certified chiral cone. -/
@[rep_depth transport]
theorem uMinus_mem_chiralCone :
    IsInChiralOperatorCone S.CIK
      (InfoGeometry.Canonical.Cl11PolarizedBasis.uMinus S.Xcl S.B) := by
  rw [isInChiralOperatorCone_iff_anticommute_GammaS (CIK := S.CIK)]
  rw [← S.hGamma]
  have hOdd :=
    InfoGeometry.Canonical.Cl11PolarizedBasis.eps_mul_eq_neg_mul_eps_of_isUMinus
      (X := S.Xcl) (A := S.B)
  rw [hOdd]
  simp

-- theorem-class: bridge
/--
The spectral commutator of the `u+`/`u-` chiral channels closes in the compact
spectral lane.
-/
@[rep_depth transport]
theorem spectralCommutator_mem_spectralCompact :
    S.CIK.IsSpectralCompact
      (CertifiedInverseKernel.spectralCommutator
        (InfoGeometry.Canonical.Cl11PolarizedBasis.uPlus S.Xcl S.A)
        (InfoGeometry.Canonical.Cl11PolarizedBasis.uMinus S.Xcl S.B)) := by
  let T := S.CIK.toInformationCartanTriple
  have hX' :
      T.IsSpectralNonCompact
        (InfoGeometry.Canonical.Cl11PolarizedBasis.uPlus S.Xcl S.A) := by
    simpa [T, IsInChiralOperatorCone,
      CertifiedInverseKernel.IsSpectralNonCompact,
      CertifiedInverseKernel.cartanTriple,
      CertifiedInverseKernel.toInformationCartanTriple] using
      S.uPlus_mem_chiralCone
  have hY' :
      T.IsSpectralNonCompact
        (InfoGeometry.Canonical.Cl11PolarizedBasis.uMinus S.Xcl S.B) := by
    simpa [T, IsInChiralOperatorCone,
      CertifiedInverseKernel.IsSpectralNonCompact,
      CertifiedInverseKernel.cartanTriple,
      CertifiedInverseKernel.toInformationCartanTriple] using
      S.uMinus_mem_chiralCone
  have hComm :
      T.IsSpectralCompact
        (InfoGeometry.Canonical.CartanDecomposition.InformationCartanTriple.spectralCommutator
          (InfoGeometry.Canonical.Cl11PolarizedBasis.uPlus S.Xcl S.A)
          (InfoGeometry.Canonical.Cl11PolarizedBasis.uMinus S.Xcl S.B)) :=
    InfoGeometry.Canonical.CartanDecomposition.InformationCartanTriple.spectralCommutator_mem_compact_of_noncompact
      T S.CIK.hDrazin hX' hY'
  simpa [T, CertifiedInverseKernel.spectralCommutator,
    CertifiedInverseKernel.IsSpectralCompact,
    CertifiedInverseKernel.cartanTriple,
    CertifiedInverseKernel.toInformationCartanTriple] using hComm

-- theorem-class: bridge
/-- The ordinary circular `u+`/`u-` commutator closes in the KKT grade-zero lane. -/
@[rep_depth transport]
theorem circularCommutator_isGZero :
    KKTCore.IsGZero S.Xcl
      (KKTCore.commutator (KKTCore.uPlus S.Xcl S.A) (KKTCore.uMinus S.Xcl S.B)) :=
  KKTCore.commutator_uPlus_uMinus_isGZero S.Xcl S.A S.B

end SelfDualChiralLightConeCertificate

/--
Constructive positive-partition witness for the operatorial conformal
Gibbs-Souriau context.

This replaces a bare positivity assertion with explicit real data:
the noncommutative operator partition is represented as a strictly positive
floor plus a real square.  The carrier remains the infinite/dimension-agnostic
doubled operator space `EndH₂`; this is not a finite partition argument.
-/
@[rep_depth transport]
structure ConformalPositivePartitionWitness
    (C : ConformalGibbsSouriauOperatorContext (α := α) (H := H)) where
  partitionFloor : ℝ
  amplitude : ℝ
-- theorem-class: bridge
  floor_pos : 0 < partitionFloor
-- theorem-class: bridge
  operatorPartition_eq_floor_add_square :
    C.operatorPartition = partitionFloor + amplitude ^ (2 : ℕ)

namespace ConformalPositivePartitionWitness

variable {C : ConformalGibbsSouriauOperatorContext (α := α) (H := H)}

-- theorem-class: bridge
/--
The operator partition is strictly positive from the explicit
positive-floor-plus-square witness.
-/
@[rep_depth transport]
theorem operatorPartition_pos (W : ConformalPositivePartitionWitness C) :
    0 < C.operatorPartition := by
  rw [ConformalPositivePartitionWitness.operatorPartition_eq_floor_add_square W]
  exact add_pos_of_pos_of_nonneg
    (ConformalPositivePartitionWitness.floor_pos W)
    (sq_nonneg (ConformalPositivePartitionWitness.amplitude W))

-- theorem-class: bridge
/--
Cone membership plus the positive-partition witness recover the old operator
admissibility surface without a separate bare `hOperatorAdmissible` packet.
-/
@[rep_depth transport]
theorem operatorAdmissible
    (W : ConformalPositivePartitionWitness C)
    (hCone : C.IsConeAdmissible) :
    C.IsOperatorAdmissible :=
  ⟨hCone, W.operatorPartition_pos⟩

end ConformalPositivePartitionWitness

/--
Cartan-odd positive partition witness.

This is the next constructive step beyond a raw positive-floor witness: the
strictly positive floor is `1 + B_θ(x,x)`, where `x` is in the Cartan-odd
sector.  Positivity of `B_θ(x,x)` is not assumed here; it is delegated to the
owner theorem `informationMassSq_nonneg_of_mem_odd`.
-/
@[rep_depth transport]
structure ConformalCartanOddPartitionWitness
    {L : Type _} [LieRing L] [LieAlgebra ℝ L]
    (C : ConformalGibbsSouriauOperatorContext (α := α) (H := H)) where
  metric : CartanOddMetricData (L := L)
  x : L
-- theorem-class: bridge
  x_mem_odd : x ∈ metric.S.oddSubmodule
  amplitude : ℝ
-- theorem-class: bridge
  operatorPartition_eq_cartan_floor_add_square :
    C.operatorPartition =
      (1 + informationMassSq (M := metric) x) + amplitude ^ (2 : ℕ)

namespace ConformalCartanOddPartitionWitness

variable {L : Type _} [LieRing L] [LieAlgebra ℝ L]
variable {C : ConformalGibbsSouriauOperatorContext (α := α) (H := H)}
variable (W : ConformalCartanOddPartitionWitness (α := α) (H := H) (C := C) (L := L))

-- theorem-class: bridge
/-- The Cartan-odd floor `1 + B_θ(x,x)` is strictly positive. -/
@[rep_depth transport]
theorem partitionFloor_pos :
    0 < 1 + informationMassSq (M := W.metric) W.x := by
  exact add_pos_of_pos_of_nonneg zero_lt_one
    (informationMassSq_nonneg_of_mem_odd (M := W.metric) W.x_mem_odd)

-- theorem-class: bridge
/--
The Cartan-odd partition witness proves strict positivity of the operatorial
partition directly, without a separate positive-partition packet or bare
`0 < C.operatorPartition` hypothesis.
-/
@[rep_depth transport]
theorem operatorPartition_pos
    (W : ConformalCartanOddPartitionWitness (α := α) (H := H) (C := C) (L := L)) :
    0 < C.operatorPartition := by
  rw [ConformalCartanOddPartitionWitness.operatorPartition_eq_cartan_floor_add_square W]
  exact add_pos_of_pos_of_nonneg (partitionFloor_pos W) (sq_nonneg W.amplitude)

/--
Convert Cartan-odd positivity into the generic positive-partition witness used
by the conformal KKT admissibility interface.
-/
@[rep_depth transport]
noncomputable def toPositivePartitionWitness :
    ConformalPositivePartitionWitness C where
  partitionFloor := 1 + informationMassSq (M := W.metric) W.x
  amplitude := W.amplitude
  floor_pos := W.partitionFloor_pos
  operatorPartition_eq_floor_add_square :=
    W.operatorPartition_eq_cartan_floor_add_square

-- theorem-class: bridge
/--
Cone membership plus Cartan-odd partition positivity proves the conformal
operatorial admissibility gate.
-/
@[rep_depth transport]
theorem operatorAdmissible_of_cartanOddPartition
    (W : ConformalCartanOddPartitionWitness (α := α) (H := H) (C := C) (L := L))
    (hCone : C.IsConeAdmissible) :
    C.IsOperatorAdmissible := by
  simpa using
    ConformalPositivePartitionWitness.operatorAdmissible
      (C := C)
      (W := ConformalCartanOddPartitionWitness.toPositivePartitionWitness
        (C := C) W)
      hCone

end ConformalCartanOddPartitionWitness

/--
Proof-carrying noncommutative closure package for the operatorial conformal
Gibbs-Souriau context.

This structure records the hypotheses that are not derivable from the scalar
finite shadow:

* a Weyl gauge field acting on doubled-carrier operators,
* a TKK master relation for the chosen conformal packet,
* operatorial cone/partition admissibility,
* two perturbation channels used for KKT circular-polarization and
  Jordan-Lie closure readouts.
-/
@[rep_depth transport]
structure ConformalWeylTKKKKTJordanLieContext where
  gibbs : ConformalGibbsSouriauOperatorContext (α := α) (H := H)
  weylGauge : WeylGaugeField EndH₂ EndH₂
  tkkParameter : ℝ
-- theorem-class: bridge
  hTKK : gibbs.SatisfiesOperatorTKKMasterRelation tkkParameter
-- theorem-class: bridge
  hOperatorAdmissible : gibbs.IsOperatorAdmissible
  X : EndH₂
  Y : EndH₂

/--
Constructive admissibility witness for the full Weyl/TKK/KKT closure package.

The old closure context still exposes `hOperatorAdmissible` for stable
downstream use.  This witness constructs that field from:

* explicit cone membership, and
* a positive-floor-plus-square proof of positive operator partition.
-/
@[rep_depth transport]
structure ConformalOperatorAdmissibilityWitness where
  gibbs : ConformalGibbsSouriauOperatorContext (α := α) (H := H)
  weylGauge : WeylGaugeField EndH₂ EndH₂
  tkkParameter : ℝ
-- theorem-class: bridge
  hTKK : gibbs.SatisfiesOperatorTKKMasterRelation tkkParameter
-- theorem-class: bridge
  hCone : gibbs.IsConeAdmissible
  partitionWitness : ConformalPositivePartitionWitness gibbs
  X : EndH₂
  Y : EndH₂

/--
Proof-carrying witness for the operatorial conformal cone-admissibility socket.

This is the smallest constructive narrowing of the remaining broad proposition
surface on the positive-partition lane: downstream routes can consume a witness
object instead of a bare `hCone : C.IsConeAdmissible` argument.
-/
@[rep_depth transport]
structure ConformalConeAdmissibilityWitness
    (C : ConformalGibbsSouriauOperatorContext (α := α) (H := H)) where
-- theorem-class: bridge
  hCone : C.IsConeAdmissible

namespace ConformalConeAdmissibilityWitness

variable {C : ConformalGibbsSouriauOperatorContext (α := α) (H := H)}

/-- Recover the cone-admissibility proposition from the proof-carrying witness. -/
@[rep_depth transport]
theorem coneAdmissible
    (W : ConformalConeAdmissibilityWitness (α := α) (H := H) C) :
    C.IsConeAdmissible :=
  W.hCone

end ConformalConeAdmissibilityWitness

/--
Proof-carrying witness for the operatorial conformal TKK socket.

This narrows the remaining broad TKK hypothesis surface on the positive-partition
lane: downstream routes can consume a witness object carrying both the selected
parameter and the master-relation proof, instead of a free
`tkkParameter`/`hTKK` pair.
-/
@[rep_depth transport]
structure ConformalTKKWitness
    (C : ConformalGibbsSouriauOperatorContext (α := α) (H := H)) where
  tkkParameter : ℝ
-- theorem-class: bridge
  hTKK : C.SatisfiesOperatorTKKMasterRelation tkkParameter

namespace ConformalTKKWitness

variable {C : ConformalGibbsSouriauOperatorContext (α := α) (H := H)}

/-- Recover the TKK master relation from the proof-carrying witness. -/
@[rep_depth transport]
theorem tkkMasterRelation
    (W : ConformalTKKWitness (α := α) (H := H) C) :
    C.SatisfiesOperatorTKKMasterRelation W.tkkParameter :=
  W.hTKK

end ConformalTKKWitness

namespace ConformalOperatorAdmissibilityWitness

variable (W : ConformalOperatorAdmissibilityWitness (α := α) (H := H))

-- theorem-class: bridge
/--
Operatorial admissibility follows constructively from cone membership and the
positive operator-partition witness.
-/
@[rep_depth transport]
theorem operatorAdmissible :
    W.gibbs.IsOperatorAdmissible :=
  ConformalPositivePartitionWitness.operatorAdmissible
    (C := W.gibbs) W.partitionWitness W.hCone

/--
Convert the constructive admissibility witness into the stable closure-context
interface used by downstream conformal/Weyl/KKT theorem surfaces.
-/
@[rep_depth transport]
def toClosureContext : ConformalWeylTKKKKTJordanLieContext (α := α) (H := H) where
  gibbs := W.gibbs
  weylGauge := W.weylGauge
  tkkParameter := W.tkkParameter
  hTKK := W.hTKK
  hOperatorAdmissible := W.operatorAdmissible
  X := W.X
  Y := W.Y

end ConformalOperatorAdmissibilityWitness

namespace ConformalPositivePartitionWitness

variable {C : ConformalGibbsSouriauOperatorContext (α := α) (H := H)}

/--
Cone membership plus the positive-partition witness recover operatorial
admissibility through the proof-carrying cone witness socket, without a bare
`hCone` theorem argument.
-/
@[rep_depth transport]
theorem operatorAdmissible_of_coneWitness
    (W : ConformalPositivePartitionWitness C)
    (hCone : ConformalConeAdmissibilityWitness (α := α) (H := H) C) :
    C.IsOperatorAdmissible :=
  W.operatorAdmissible hCone.hCone

/--
Build the stable operator-admissibility witness directly from a positive-partition
witness plus the remaining cone/TKK/channel data.
-/
@[rep_depth transport]
noncomputable def toOperatorAdmissibilityWitness
    (W : ConformalPositivePartitionWitness C)
    (weylGauge : WeylGaugeField EndH₂ EndH₂)
    (tkkParameter : ℝ)
    (hTKK : C.SatisfiesOperatorTKKMasterRelation tkkParameter)
    (hCone : C.IsConeAdmissible)
    (X Y : EndH₂) :
    ConformalOperatorAdmissibilityWitness (α := α) (H := H) where
  gibbs := C
  weylGauge := weylGauge
  tkkParameter := tkkParameter
  hTKK := hTKK
  hCone := hCone
  partitionWitness := W
  X := X
  Y := Y

/--
Build the stable operator-admissibility witness directly from a positive-partition
witness and a proof-carrying cone witness, without a bare `hCone` argument.
-/
@[rep_depth transport]
noncomputable def toOperatorAdmissibilityWitnessOfConeWitness
    (W : ConformalPositivePartitionWitness C)
    (weylGauge : WeylGaugeField EndH₂ EndH₂)
    (tkkParameter : ℝ)
    (hTKK : C.SatisfiesOperatorTKKMasterRelation tkkParameter)
    (hCone : ConformalConeAdmissibilityWitness (α := α) (H := H) C)
    (X Y : EndH₂) :
    ConformalOperatorAdmissibilityWitness (α := α) (H := H) where
  gibbs := C
  weylGauge := weylGauge
  tkkParameter := tkkParameter
  hTKK := hTKK
  hCone := hCone.hCone
  partitionWitness := W
  X := X
  Y := Y

/--
Build the stable operator-admissibility witness directly from a positive-partition
witness and a proof-carrying TKK witness, without a bare
`tkkParameter`/`hTKK` theorem-argument pair.
-/
@[rep_depth transport]
noncomputable def toOperatorAdmissibilityWitnessOfTKKWitness
    (W : ConformalPositivePartitionWitness C)
    (weylGauge : WeylGaugeField EndH₂ EndH₂)
    (hTKK : ConformalTKKWitness (α := α) (H := H) C)
    (hCone : C.IsConeAdmissible)
    (X Y : EndH₂) :
    ConformalOperatorAdmissibilityWitness (α := α) (H := H) where
  gibbs := C
  weylGauge := weylGauge
  tkkParameter := hTKK.tkkParameter
  hTKK := hTKK.hTKK
  hCone := hCone
  partitionWitness := W
  X := X
  Y := Y

/--
Build the stable operator-admissibility witness directly from a positive-partition
witness, a proof-carrying TKK witness, and a proof-carrying cone witness,
without bare `tkkParameter`/`hTKK` or `hCone` arguments.
-/
@[rep_depth transport]
noncomputable def toOperatorAdmissibilityWitnessOfTKKConeWitness
    (W : ConformalPositivePartitionWitness C)
    (weylGauge : WeylGaugeField EndH₂ EndH₂)
    (hTKK : ConformalTKKWitness (α := α) (H := H) C)
    (hCone : ConformalConeAdmissibilityWitness (α := α) (H := H) C)
    (X Y : EndH₂) :
    ConformalOperatorAdmissibilityWitness (α := α) (H := H) where
  gibbs := C
  weylGauge := weylGauge
  tkkParameter := hTKK.tkkParameter
  hTKK := hTKK.hTKK
  hCone := hCone.hCone
  partitionWitness := W
  X := X
  Y := Y

/--
Build the stable closure context directly from a positive-partition witness,
without re-supplying a separate `hOperatorAdmissible` packet.
-/
@[rep_depth transport]
noncomputable def toClosureContext
    (W : ConformalPositivePartitionWitness C)
    (weylGauge : WeylGaugeField EndH₂ EndH₂)
    (tkkParameter : ℝ)
    (hTKK : C.SatisfiesOperatorTKKMasterRelation tkkParameter)
    (hCone : C.IsConeAdmissible)
    (X Y : EndH₂) :
    ConformalWeylTKKKKTJordanLieContext (α := α) (H := H) :=
  (W.toOperatorAdmissibilityWitness weylGauge tkkParameter hTKK hCone X Y).toClosureContext

/--
Build the stable closure context directly from a positive-partition witness and
a proof-carrying cone witness, without a bare `hCone` theorem argument.
-/
@[rep_depth transport]
noncomputable def toClosureContextOfConeWitness
    (W : ConformalPositivePartitionWitness C)
    (weylGauge : WeylGaugeField EndH₂ EndH₂)
    (tkkParameter : ℝ)
    (hTKK : C.SatisfiesOperatorTKKMasterRelation tkkParameter)
    (hCone : ConformalConeAdmissibilityWitness (α := α) (H := H) C)
    (X Y : EndH₂) :
    ConformalWeylTKKKKTJordanLieContext (α := α) (H := H) :=
  (W.toOperatorAdmissibilityWitnessOfConeWitness weylGauge tkkParameter hTKK hCone X Y).toClosureContext

/--
Build the stable closure context directly from a positive-partition witness and a
proof-carrying TKK witness, without a bare `tkkParameter`/`hTKK` theorem-argument
pair.
-/
@[rep_depth transport]
noncomputable def toClosureContextOfTKKWitness
    (W : ConformalPositivePartitionWitness C)
    (weylGauge : WeylGaugeField EndH₂ EndH₂)
    (hTKK : ConformalTKKWitness (α := α) (H := H) C)
    (hCone : C.IsConeAdmissible)
    (X Y : EndH₂) :
    ConformalWeylTKKKKTJordanLieContext (α := α) (H := H) :=
  (W.toOperatorAdmissibilityWitnessOfTKKWitness weylGauge hTKK hCone X Y).toClosureContext

/--
Build the stable closure context directly from a positive-partition witness, a
proof-carrying TKK witness, and a proof-carrying cone witness, without bare
`tkkParameter`/`hTKK` or `hCone` theorem arguments.
-/
@[rep_depth transport]
noncomputable def toClosureContextOfTKKConeWitness
    (W : ConformalPositivePartitionWitness C)
    (weylGauge : WeylGaugeField EndH₂ EndH₂)
    (hTKK : ConformalTKKWitness (α := α) (H := H) C)
    (hCone : ConformalConeAdmissibilityWitness (α := α) (H := H) C)
    (X Y : EndH₂) :
    ConformalWeylTKKKKTJordanLieContext (α := α) (H := H) :=
  (W.toOperatorAdmissibilityWitnessOfTKKConeWitness weylGauge hTKK hCone X Y).toClosureContext

end ConformalPositivePartitionWitness

namespace ConformalCartanOddPartitionWitness

variable {L : Type _} [LieRing L] [LieAlgebra ℝ L]
variable {C : ConformalGibbsSouriauOperatorContext (α := α) (H := H)}

/--
Cone membership plus Cartan-odd partition positivity proves the conformal
operatorial admissibility gate through the proof-carrying cone witness socket,
without a bare `hCone` theorem argument.
-/
@[rep_depth transport]
theorem operatorAdmissible_of_coneWitness
    (W : ConformalCartanOddPartitionWitness (α := α) (H := H) (C := C) (L := L))
    (hCone : ConformalConeAdmissibilityWitness C) :
    C.IsOperatorAdmissible := by
  simpa using
    ConformalPositivePartitionWitness.operatorAdmissible
      (C := C)
      (W := W.toPositivePartitionWitness)
      hCone.hCone

/--
Package the Cartan-odd partition witness as the stable constructive
operator-admissibility interface used by downstream conformal/Weyl/KKT theorem
surfaces.
-/
@[rep_depth transport]
noncomputable def toOperatorAdmissibilityWitness
    (W : ConformalCartanOddPartitionWitness (α := α) (H := H) (C := C) (L := L))
    (weylGauge : WeylGaugeField EndH₂ EndH₂)
    (tkkParameter : ℝ)
    (hTKK : C.SatisfiesOperatorTKKMasterRelation tkkParameter)
    (hCone : C.IsConeAdmissible)
    (X Y : EndH₂) :
    ConformalOperatorAdmissibilityWitness (α := α) (H := H) where
  gibbs := C
  weylGauge := weylGauge
  tkkParameter := tkkParameter
  hTKK := hTKK
  hCone := hCone
  partitionWitness := W.toPositivePartitionWitness
  X := X
  Y := Y

/--
Package the Cartan-odd partition witness as the stable constructive
operator-admissibility interface using the proof-carrying cone witness socket,
without a bare `hCone` theorem argument.
-/
@[rep_depth transport]
noncomputable def toOperatorAdmissibilityWitnessOfConeWitness
    (W : ConformalCartanOddPartitionWitness (α := α) (H := H) (C := C) (L := L))
    (weylGauge : WeylGaugeField EndH₂ EndH₂)
    (tkkParameter : ℝ)
    (hTKK : C.SatisfiesOperatorTKKMasterRelation tkkParameter)
    (hCone : ConformalConeAdmissibilityWitness (α := α) (H := H) C)
    (X Y : EndH₂) :
    ConformalOperatorAdmissibilityWitness (α := α) (H := H) where
  gibbs := C
  weylGauge := weylGauge
  tkkParameter := tkkParameter
  hTKK := hTKK
  hCone := hCone.hCone
  partitionWitness := W.toPositivePartitionWitness
  X := X
  Y := Y

/--
Package the Cartan-odd partition witness as the stable constructive
operator-admissibility interface using the proof-carrying TKK witness socket,
without a bare `tkkParameter`/`hTKK` theorem-argument pair.
-/
@[rep_depth transport]
noncomputable def toOperatorAdmissibilityWitnessOfTKKWitness
    (W : ConformalCartanOddPartitionWitness (α := α) (H := H) (C := C) (L := L))
    (weylGauge : WeylGaugeField EndH₂ EndH₂)
    (hTKK : ConformalTKKWitness (α := α) (H := H) C)
    (hCone : C.IsConeAdmissible)
    (X Y : EndH₂) :
    ConformalOperatorAdmissibilityWitness (α := α) (H := H) where
  gibbs := C
  weylGauge := weylGauge
  tkkParameter := hTKK.tkkParameter
  hTKK := hTKK.hTKK
  hCone := hCone
  partitionWitness := W.toPositivePartitionWitness
  X := X
  Y := Y

/--
Package the Cartan-odd partition witness as the stable constructive
operator-admissibility interface using proof-carrying TKK and cone witnesses,
without bare `tkkParameter`/`hTKK` or `hCone` theorem arguments.
-/
@[rep_depth transport]
noncomputable def toOperatorAdmissibilityWitnessOfTKKConeWitness
    (W : ConformalCartanOddPartitionWitness (α := α) (H := H) (C := C) (L := L))
    (weylGauge : WeylGaugeField EndH₂ EndH₂)
    (hTKK : ConformalTKKWitness (α := α) (H := H) C)
    (hCone : ConformalConeAdmissibilityWitness (α := α) (H := H) C)
    (X Y : EndH₂) :
    ConformalOperatorAdmissibilityWitness (α := α) (H := H) where
  gibbs := C
  weylGauge := weylGauge
  tkkParameter := hTKK.tkkParameter
  hTKK := hTKK.hTKK
  hCone := hCone.hCone
  partitionWitness := W.toPositivePartitionWitness
  X := X
  Y := Y

/--
Build the full stable closure context directly from the Cartan-odd partition
witness plus the remaining Weyl/TKK channel data.
-/
@[rep_depth transport]
noncomputable def toClosureContext
    (W : ConformalCartanOddPartitionWitness (α := α) (H := H) (C := C) (L := L))
    (weylGauge : WeylGaugeField EndH₂ EndH₂)
    (tkkParameter : ℝ)
    (hTKK : C.SatisfiesOperatorTKKMasterRelation tkkParameter)
    (hCone : C.IsConeAdmissible)
    (X Y : EndH₂) :
    ConformalWeylTKKKKTJordanLieContext (α := α) (H := H) :=
  (W.toOperatorAdmissibilityWitness weylGauge tkkParameter hTKK hCone X Y).toClosureContext

/--
Build the full stable closure context directly from the Cartan-odd partition
witness and a proof-carrying cone witness, without a bare `hCone` theorem
argument.
-/
@[rep_depth transport]
noncomputable def toClosureContextOfConeWitness
    (W : ConformalCartanOddPartitionWitness (α := α) (H := H) (C := C) (L := L))
    (weylGauge : WeylGaugeField EndH₂ EndH₂)
    (tkkParameter : ℝ)
    (hTKK : C.SatisfiesOperatorTKKMasterRelation tkkParameter)
    (hCone : ConformalConeAdmissibilityWitness (α := α) (H := H) C)
    (X Y : EndH₂) :
    ConformalWeylTKKKKTJordanLieContext (α := α) (H := H) :=
  (W.toOperatorAdmissibilityWitnessOfConeWitness weylGauge tkkParameter hTKK hCone X Y).toClosureContext

/--
Build the full stable closure context directly from the Cartan-odd partition
witness and a proof-carrying TKK witness, without a bare
`tkkParameter`/`hTKK` theorem-argument pair.
-/
@[rep_depth transport]
noncomputable def toClosureContextOfTKKWitness
    (W : ConformalCartanOddPartitionWitness (α := α) (H := H) (C := C) (L := L))
    (weylGauge : WeylGaugeField EndH₂ EndH₂)
    (hTKK : ConformalTKKWitness (α := α) (H := H) C)
    (hCone : C.IsConeAdmissible)
    (X Y : EndH₂) :
    ConformalWeylTKKKKTJordanLieContext (α := α) (H := H) :=
  (W.toOperatorAdmissibilityWitnessOfTKKWitness weylGauge hTKK hCone X Y).toClosureContext

/--
Build the full stable closure context directly from the Cartan-odd partition
witness, a proof-carrying TKK witness, and a proof-carrying cone witness,
without bare `tkkParameter`/`hTKK` or `hCone` theorem arguments.
-/
@[rep_depth transport]
noncomputable def toClosureContextOfTKKConeWitness
    (W : ConformalCartanOddPartitionWitness (α := α) (H := H) (C := C) (L := L))
    (weylGauge : WeylGaugeField EndH₂ EndH₂)
    (hTKK : ConformalTKKWitness (α := α) (H := H) C)
    (hCone : ConformalConeAdmissibilityWitness (α := α) (H := H) C)
    (X Y : EndH₂) :
    ConformalWeylTKKKKTJordanLieContext (α := α) (H := H) :=
  (W.toOperatorAdmissibilityWitnessOfTKKConeWitness weylGauge hTKK hCone X Y).toClosureContext

end ConformalCartanOddPartitionWitness

namespace ConformalWeylTKKKKTJordanLieContext

variable (C : ConformalWeylTKKKKTJordanLieContext (α := α) (H := H))

local notation "cl11" => doubledSpaceCl11Action (E := H)

/-- Weyl-gauged conformal geometric temperature. -/
@[rep_depth transport]
noncomputable def weylTemperature : EndH₂ :=
  C.weylGauge.gaugeOf C.gibbs.conformalGeometricTemperature

-- theorem-class: bridge
/-- The package carries the operator-level TKK master relation as data. -/
@[rep_depth transport]
theorem tkkMasterRelation :
    C.gibbs.SatisfiesOperatorTKKMasterRelation C.tkkParameter :=
  C.hTKK

-- theorem-class: bridge
/-- The package carries the operatorial KKT cone/partition admissibility gate. -/
@[rep_depth transport]
theorem operatorAdmissible :
    C.gibbs.IsOperatorAdmissible :=
  C.hOperatorAdmissible

-- theorem-class: bridge
/-- The certified conformal dilation remains in the KKT grade-zero lane. -/
@[rep_depth transport]
theorem dilation_isGZero :
    IsGZero cl11 C.gibbs.DGenerator := by
  simpa [ConformalGibbsSouriauOperatorContext.DGenerator] using
    C.gibbs.base.conformalD_isGZero

-- theorem-class: bridge
/-- The certified chiral grading remains in the KKT grade-zero lane. -/
@[rep_depth transport]
theorem chiralGrading_isGZero :
    IsGZero cl11
      (InfoGeometry.Canonical.ChiralCartanCore.chiralGrading
        C.gibbs.base.CCI.toConformalInference) :=
  C.gibbs.base.chiralGrading_isGZero

/-- Circularly polarized `u+`/`u-` commutator attached to the context channels. -/
@[rep_depth transport]
noncomputable def circularPolarizedCommutator : EndH₂ :=
  KKTCore.commutator (uPlus cl11 C.X) (uMinus cl11 C.Y)

-- theorem-class: bridge
/-- Circular polarization closes in the KKT grade-zero operator lane. -/
@[rep_depth transport]
theorem circularPolarizedCommutator_isGZero :
    IsGZero cl11 C.circularPolarizedCommutator := by
  simpa [circularPolarizedCommutator] using
    KKTCore.commutator_uPlus_uMinus_isGZero (X := cl11) C.X C.Y

/-- Symmetric Jordan product of the conformal temperature and its Weyl-gauged copy. -/
@[rep_depth transport]
noncomputable def jordanProductTemperatureWeyl : EndH₂ :=
  InfoGeometry.Canonical.SuperJordanLie.jordanProduct (E := H)
    C.gibbs.conformalGeometricTemperature C.weylTemperature

/-- Antisymmetric Lie product of the conformal temperature and its Weyl-gauged copy. -/
@[rep_depth transport]
noncomputable def lieProductTemperatureWeyl : EndH₂ :=
  InfoGeometry.Canonical.SuperJordanLie.lieProduct (E := H)
    C.gibbs.conformalGeometricTemperature C.weylTemperature

-- theorem-class: bridge
/--
The Fock commutator of the conformal temperature with its Weyl-gauged copy is
exactly twice the operatorial Lie product.
-/
@[rep_depth transport]
theorem fockCommutator_temperature_weyl_eq_two_smul_lieProduct :
    InfoGeometry.Canonical.BogoliubovFockSuper.fockCommutator (E := H)
      C.gibbs.conformalGeometricTemperature C.weylTemperature =
        (2 : ℝ) • C.lieProductTemperatureWeyl := by
  simpa [lieProductTemperatureWeyl] using
    (InfoGeometry.Canonical.SuperJordanLie.fockCommutator_eq_two_smul_lieProduct
      (E := H) C.gibbs.conformalGeometricTemperature C.weylTemperature)

-- theorem-class: bridge
/--
The Fock anticommutator of the conformal temperature with its Weyl-gauged copy
is exactly twice the operatorial Jordan product.
-/
@[rep_depth transport]
theorem fockAnticommutator_temperature_weyl_eq_two_smul_jordanProduct :
    InfoGeometry.Canonical.BogoliubovFockSuper.fockAnticommutator (E := H)
      C.gibbs.conformalGeometricTemperature C.weylTemperature =
        (2 : ℝ) • C.jordanProductTemperatureWeyl := by
  simpa [jordanProductTemperatureWeyl] using
    (InfoGeometry.Canonical.SuperJordanLie.fockAnticommutator_eq_two_smul_jordanProduct
      (E := H) C.gibbs.conformalGeometricTemperature C.weylTemperature)

/--
Single proposition bundling the compile-checked closure gates for this
operatorial noncommutative layer.
-/
@[rep_depth transport]
def SatisfiesKKT_TKK_Weyl_JordanLieClosure : Prop :=
  C.gibbs.IsOperatorAdmissible
    ∧ C.gibbs.SatisfiesOperatorTKKMasterRelation C.tkkParameter
    ∧ IsGZero cl11 C.gibbs.DGenerator
    ∧ IsGZero cl11
        (InfoGeometry.Canonical.ChiralCartanCore.chiralGrading
          C.gibbs.base.CCI.toConformalInference)
    ∧ IsGZero cl11 C.circularPolarizedCommutator

-- theorem-class: bridge
/-- The package supplies the KKT/TKK/Weyl/Jordan-Lie closure proposition. -/
@[rep_depth transport]
theorem satisfiesKKT_TKK_Weyl_JordanLieClosure :
    C.SatisfiesKKT_TKK_Weyl_JordanLieClosure := by
  exact ⟨C.operatorAdmissible, C.tkkMasterRelation, C.dilation_isGZero,
    C.chiralGrading_isGZero, C.circularPolarizedCommutator_isGZero⟩

-- theorem-class: bridge
/-- The Onsager/Hessian response symmetry survives on the selected channels. -/
@[rep_depth transport]
theorem operatorConformalResponse_XY_swap :
    C.gibbs.operatorConformalResponse C.X C.Y =
      C.gibbs.operatorConformalResponse C.Y C.X :=
  C.gibbs.operatorConformalResponse_swap C.X C.Y

/--
Krein-rooted KMS-like state condition for the operatorial conformal generator.

This is a noncommutative readout identity on the doubled Krein carrier, not a
finite diagonal probability identity.
-/
@[rep_depth transport]
noncomputable def SatisfiesKMSLike (β : ℝ) : Prop :=
  InfoGeometry.Krein.satisfies_kms_like
    C.gibbs.conformalGeometricTemperature C.gibbs.readout β

/-- Compatibility alias for the KMS-like conformal operator-state condition. -/
@[rep_depth transport]
noncomputable def SatisfiesKMS (β : ℝ) : Prop :=
  InfoGeometry.Krein.satisfies_kms
    C.gibbs.conformalGeometricTemperature C.gibbs.readout β

-- theorem-class: bridge
/--
At zero modular time, the KMS condition forces cyclic readout symmetry for
operator products.
-/
@[rep_depth transport]
theorem kms_zero_implies_operatorReadout_commutation
    (hKMS : C.SatisfiesKMS 0) (A B : EndH₂) :
    C.gibbs.readout (A * B) = C.gibbs.readout (B * A) := by
  exact
    InfoGeometry.Krein.kms_zero_implies_commutation
      (E := H) C.gibbs.conformalGeometricTemperature C.gibbs.readout hKMS A B

/-! ### Weyl gauge covariance of the closure packet -/

/--
Apply an additive local Weyl gauge shift to the closure context.

The conformal Gibbs packet, TKK relation, KKT admissibility gate, and circular
polarization channels are unchanged; only the Weyl representative is shifted.
-/
@[rep_depth transport]
noncomputable def transformWeylGauge
    (σ : WeylGaugeParameter EndH₂ EndH₂) :
    ConformalWeylTKKKKTJordanLieContext (α := α) (H := H) where
  gibbs := C.gibbs
  weylGauge := C.weylGauge.transform σ
  tkkParameter := C.tkkParameter
  hTKK := C.hTKK
  hOperatorAdmissible := C.hOperatorAdmissible
  X := C.X
  Y := C.Y

/- The Weyl-transformed temperature is the original representative plus the
local scale shift evaluated at the conformal geometric temperature. -/
-- theorem-class: bridge
@[rep_depth transport]
theorem transformWeylGauge_weylTemperature
    (σ : WeylGaugeParameter EndH₂ EndH₂) :
    (C.transformWeylGauge σ).weylTemperature =
      C.weylTemperature + σ.shiftOf C.gibbs.conformalGeometricTemperature := by
  rfl

-- theorem-class: bridge
/--
Additive Weyl gauge transformations preserve the compiled
KKT/TKK/Weyl/Jordan-Lie closure packet.

This is the formal content justified by the Weyl-gauge modeling choice: the
closure theorem is invariant because its proof-carrying fields are independent
of the selected Weyl representative.
-/
@[rep_depth transport]
theorem transformWeylGauge_preserves_closure
    (σ : WeylGaugeParameter EndH₂ EndH₂) :
    (C.transformWeylGauge σ).SatisfiesKKT_TKK_Weyl_JordanLieClosure := by
  exact (C.transformWeylGauge σ).satisfiesKKT_TKK_Weyl_JordanLieClosure

/--
Apply a potential-form Weyl gauge transform `W ↦ W - dα` to the closure
context.
-/
@[rep_depth transport]
noncomputable def transformWeylGaugeByPotential
    (Δ : WeylDifferentialOperator ℝ EndH₂ EndH₂)
    (αW : WeylGaugeParameter EndH₂ EndH₂) :
    ConformalWeylTKKKKTJordanLieContext (α := α) (H := H) where
  gibbs := C.gibbs
  weylGauge := C.weylGauge.transformByPotential Δ αW
  tkkParameter := C.tkkParameter
  hTKK := C.hTKK
  hOperatorAdmissible := C.hOperatorAdmissible
  X := C.X
  Y := C.Y

-- theorem-class: bridge
/-- Potential-form Weyl gauge transformations preserve the closure packet. -/
@[rep_depth transport]
theorem transformWeylGaugeByPotential_preserves_closure
    (Δ : WeylDifferentialOperator ℝ EndH₂ EndH₂)
    (αW : WeylGaugeParameter EndH₂ EndH₂) :
    (C.transformWeylGaugeByPotential Δ αW).SatisfiesKKT_TKK_Weyl_JordanLieClosure := by
  exact (C.transformWeylGaugeByPotential Δ αW).satisfiesKKT_TKK_Weyl_JordanLieClosure

-- theorem-class: bridge
/--
Potential-form Weyl gauge transformations preserve the associated
field-strength object.
-/
@[rep_depth transport]
theorem fieldStrength_transformWeylGaugeByPotential_eq
    (Δ : WeylDifferentialOperator ℝ EndH₂ EndH₂)
    (αW : WeylGaugeParameter EndH₂ EndH₂) :
    ((C.transformWeylGaugeByPotential Δ αW).weylGauge.fieldStrength Δ) =
      C.weylGauge.fieldStrength Δ := by
  simpa [transformWeylGaugeByPotential] using
    WeylGaugeField.fieldStrength_transformByPotential_eq Δ C.weylGauge αW

end ConformalWeylTKKKKTJordanLieContext

namespace ConformalCartanOddPartitionWitness

variable {L : Type _} [LieRing L] [LieAlgebra ℝ L]
variable {C : ConformalGibbsSouriauOperatorContext (α := α) (H := H)}

/--
The Cartan-odd constructive branch supplies the full KKT/TKK/Weyl/Jordan-Lie
closure proposition through proof-carrying TKK and cone witnesses, without bare
`tkkParameter`/`hTKK` or `hCone` theorem arguments.
-/
@[rep_depth transport]
theorem satisfiesKKT_TKK_Weyl_JordanLieClosure_of_TKKConeWitness
    (W : ConformalCartanOddPartitionWitness (α := α) (H := H) (C := C) (L := L))
    (weylGauge : WeylGaugeField EndH₂ EndH₂)
    (hTKK : ConformalTKKWitness (α := α) (H := H) C)
    (hCone : ConformalConeAdmissibilityWitness (α := α) (H := H) C)
    (X Y : EndH₂) :
    (W.toClosureContextOfTKKConeWitness weylGauge hTKK hCone X Y).SatisfiesKKT_TKK_Weyl_JordanLieClosure := by
  exact
    (W.toClosureContextOfTKKConeWitness weylGauge hTKK hCone X Y).satisfiesKKT_TKK_Weyl_JordanLieClosure

end ConformalCartanOddPartitionWitness

/-! ## Operatorial Fisher/Onsager positivity gate -/

/--
Positive Fisher/Onsager gate over the noncommutative conformal context.

The nonnegativity field is explicit because an indefinite Krein carrier does
not make every response positive.  A projective-count or regular-cone witness
can feed this field upstream; this layer records only the operator theorem it
actually uses.
-/
@[rep_depth transport]
structure ConformalSquareResponseWitness
    (C : ConformalGibbsSouriauOperatorContext (α := α) (H := H))
    (X : EndH₂) where
  amplitude : ℝ
-- theorem-class: bridge
  selfResponse_eq_square :
    C.operatorConformalResponse X X = amplitude ^ (2 : ℕ)

namespace ConformalSquareResponseWitness

variable {C : ConformalGibbsSouriauOperatorContext (α := α) (H := H)}

-- theorem-class: bridge
/-- The selected conformal self-response is nonnegative because it is a real square. -/
@[rep_depth transport]
theorem selfResponse_nonneg (X : EndH₂) (W : ConformalSquareResponseWitness C X) :
    0 ≤ C.operatorConformalResponse X X := by
  rw [W.selfResponse_eq_square]
  exact sq_nonneg W.amplitude

end ConformalSquareResponseWitness

/--
Positive Fisher/Onsager gate over the noncommutative conformal context.
-/
@[rep_depth transport]
structure ConformalFisherOnsagerPositiveContext where
  closure : ConformalWeylTKKKKTJordanLieContext (α := α) (H := H)
-- theorem-class: bridge
  selfResponse_nonneg :
    0 ≤ closure.gibbs.operatorConformalResponse closure.X closure.X

namespace ConformalFisherOnsagerPositiveContext

variable (C : ConformalFisherOnsagerPositiveContext (α := α) (H := H))

/-- Diagonal Fisher/Onsager production along the selected operator channel. -/
@[rep_depth transport]
noncomputable def fisherOnsagerProduction : ℝ :=
  C.closure.gibbs.operatorConformalResponse C.closure.X C.closure.X

-- theorem-class: bridge
/-- The declared operatorial Fisher/Onsager production is nonnegative. -/
@[rep_depth transport]
theorem fisherOnsagerProduction_nonneg :
    0 ≤ C.fisherOnsagerProduction := by
  simpa [fisherOnsagerProduction] using C.selfResponse_nonneg

-- theorem-class: bridge
/-- Diagonal response is invariant under channel swap by Onsager symmetry. -/
@[rep_depth transport]
theorem fisherOnsagerProduction_swap :
    C.closure.gibbs.operatorConformalResponse C.closure.X C.closure.X =
      C.closure.gibbs.operatorConformalResponse C.closure.X C.closure.X := by
  exact C.closure.gibbs.operatorConformalResponse_swap C.closure.X C.closure.X

end ConformalFisherOnsagerPositiveContext

/--
Constructive square-response replacement for the bare conformal
Fisher/Onsager nonnegativity field.

This is still an infinite operatorial surface: the response is the
noncommutative Hessian readout on
`EndH₂ := DoubledSpace H →L[ℝ] DoubledSpace H`.  The witness is not a finite
response matrix; it is the statement that the selected conformal self-response
is represented by a real square.
-/
@[rep_depth transport]
structure ConformalSquareFisherOnsagerPositiveContext where
  closure : ConformalWeylTKKKKTJordanLieContext (α := α) (H := H)
  amplitude : ℝ
-- theorem-class: bridge
  selfResponse_eq_square :
    closure.gibbs.operatorConformalResponse closure.X closure.X =
      amplitude ^ (2 : ℕ)

namespace ConformalSquareFisherOnsagerPositiveContext

variable (C : ConformalSquareFisherOnsagerPositiveContext (α := α) (H := H))

-- theorem-class: bridge
/-- The conformal self-response is nonnegative because it is a real square. -/
@[rep_depth transport]
theorem selfResponse_nonneg :
    0 ≤ C.closure.gibbs.operatorConformalResponse C.closure.X C.closure.X := by
  rw [C.selfResponse_eq_square]
  exact sq_nonneg C.amplitude

/--
Convert a square-response witness into the older positive-context interface.

Downstream users that only require nonnegativity can consume this constructor
instead of threading a bare scalar positivity hypothesis.
-/
@[rep_depth transport]
def toPositiveContext : ConformalFisherOnsagerPositiveContext (α := α) (H := H) where
  closure := C.closure
  selfResponse_nonneg := C.selfResponse_nonneg

-- theorem-class: bridge
/--
Diagonal conformal Fisher/Onsager production is exactly the selected real
square on the square-response constructive branch.
-/
@[rep_depth transport]
theorem fisherOnsagerProduction_eq_square :
    C.toPositiveContext.fisherOnsagerProduction = C.amplitude ^ (2 : ℕ) := by
  simpa [ConformalFisherOnsagerPositiveContext.fisherOnsagerProduction, toPositiveContext] using
    C.selfResponse_eq_square

-- theorem-class: bridge
/--
Diagonal conformal Fisher/Onsager production is nonnegative from the
square-response witness, with no finite response matrix and no bare PSD
hypothesis.
-/
@[rep_depth transport]
theorem fisherOnsagerProduction_nonneg_of_squareResponse :
    0 ≤ C.toPositiveContext.fisherOnsagerProduction := by
  exact C.toPositiveContext.fisherOnsagerProduction_nonneg

end ConformalSquareFisherOnsagerPositiveContext

/--
Constructive square-response package that avoids carrying a separate
`hOperatorAdmissible` field on the Fisher/Onsager-positive branch.

The closure data is supplied through
`ConformalOperatorAdmissibilityWitness`, so the stable closure context is
recovered by theorem-backed construction rather than an explicit packaged
admissibility proof.
-/
@[rep_depth transport]
structure ConstructiveConformalSquareFisherOnsagerPositiveContext where
  closureWitness : ConformalOperatorAdmissibilityWitness (α := α) (H := H)
  amplitude : ℝ
-- theorem-class: bridge
  selfResponse_eq_square :
    closureWitness.gibbs.operatorConformalResponse
        closureWitness.X closureWitness.X =
      amplitude ^ (2 : ℕ)

namespace ConstructiveConformalSquareFisherOnsagerPositiveContext

variable (C : ConstructiveConformalSquareFisherOnsagerPositiveContext
  (α := α) (H := H))

-- theorem-class: bridge
/-- The selected conformal self-response is nonnegative because it is a real square. -/
@[rep_depth transport]
theorem selfResponse_nonneg :
    0 ≤ C.closureWitness.gibbs.operatorConformalResponse
      C.closureWitness.X C.closureWitness.X := by
  rw [C.selfResponse_eq_square]
  exact sq_nonneg C.amplitude

/--
Recover the existing square-response surface from the constructive
operator-admissibility witness branch.
-/
@[rep_depth transport]
def toSquarePositiveContext :
    ConformalSquareFisherOnsagerPositiveContext (α := α) (H := H) where
  closure := C.closureWitness.toClosureContext
  amplitude := C.amplitude
  selfResponse_eq_square := by
    simpa [ConformalOperatorAdmissibilityWitness.toClosureContext] using
      C.selfResponse_eq_square

/--
Recover the legacy nonnegativity-only Fisher/Onsager interface from the
constructive operator-admissibility witness branch.
-/
@[rep_depth transport]
def toPositiveContext :
    ConformalFisherOnsagerPositiveContext (α := α) (H := H) :=
  C.toSquarePositiveContext.toPositiveContext

-- theorem-class: bridge
/--
Diagonal conformal Fisher/Onsager production is exactly the selected real
square on the constructive admissibility-plus-square branch.
-/
@[rep_depth transport]
theorem fisherOnsagerProduction_eq_square :
    C.toPositiveContext.fisherOnsagerProduction = C.amplitude ^ (2 : ℕ) := by
  simpa [toPositiveContext] using C.toSquarePositiveContext.fisherOnsagerProduction_eq_square

-- theorem-class: bridge
/--
Diagonal conformal Fisher/Onsager production is nonnegative on the
constructive admissibility-plus-square branch.
-/
@[rep_depth transport]
theorem fisherOnsagerProduction_nonneg :
    0 ≤ C.toPositiveContext.fisherOnsagerProduction := by
  exact C.toPositiveContext.fisherOnsagerProduction_nonneg

end ConstructiveConformalSquareFisherOnsagerPositiveContext

namespace ConformalOperatorAdmissibilityWitness

variable (W : ConformalOperatorAdmissibilityWitness (α := α) (H := H))

/--
Build the constructive square-response Fisher/Onsager-positive package directly
from an operator-admissibility witness plus the proof-carrying square-response
packet, without re-supplying the separate amplitude/equality pair.
-/
@[rep_depth transport]
noncomputable def toConstructiveSquarePositiveContextOfWitness
    (hSquare : ConformalSquareResponseWitness W.gibbs W.X) :
    ConstructiveConformalSquareFisherOnsagerPositiveContext (α := α) (H := H) where
  closureWitness := W
  amplitude := hSquare.amplitude
  selfResponse_eq_square := hSquare.selfResponse_eq_square

/--
The operator-admissibility witness plus a proof-carrying square-response packet
already proves Fisher/Onsager nonnegativity.  Downstream callers do not need to
reassemble the legacy positive context or supply a bare `selfResponse_nonneg`
hypothesis on this branch.
-/
@[rep_depth transport]
theorem fisherOnsagerProduction_nonneg_of_squareResponseWitness
    (hSquare : ConformalSquareResponseWitness W.gibbs W.X) :
    0 ≤ (W.toConstructiveSquarePositiveContextOfWitness hSquare).toPositiveContext.fisherOnsagerProduction := by
  exact
    (W.toConstructiveSquarePositiveContextOfWitness hSquare).fisherOnsagerProduction_nonneg

/--
Build the constructive square-response Fisher/Onsager-positive package directly
from an operator-admissibility witness, without re-supplying the separate
Weyl/TKK/cone/channel fields.
-/
@[rep_depth transport]
noncomputable def toConstructiveSquarePositiveContext
    (amplitude : ℝ)
    (selfResponse_eq_square :
      W.gibbs.operatorConformalResponse W.X W.X = amplitude ^ (2 : ℕ)) :
    ConstructiveConformalSquareFisherOnsagerPositiveContext (α := α) (H := H) :=
  W.toConstructiveSquarePositiveContextOfWitness
    { amplitude := amplitude, selfResponse_eq_square := selfResponse_eq_square }

/--
Recover the legacy nonnegativity-only Fisher/Onsager surface directly from an
operator-admissibility witness plus a square-response witness packet.
-/
@[rep_depth transport]
noncomputable def toPositiveContextOfWitness
    (hSquare : ConformalSquareResponseWitness W.gibbs W.X) :
    ConformalFisherOnsagerPositiveContext (α := α) (H := H) :=
  (W.toConstructiveSquarePositiveContextOfWitness hSquare).toPositiveContext

/--
Recover the legacy nonnegativity-only Fisher/Onsager surface directly from an
operator-admissibility witness plus a square-response certificate.
-/
@[rep_depth transport]
noncomputable def toPositiveContext
    (amplitude : ℝ)
    (selfResponse_eq_square :
      W.gibbs.operatorConformalResponse W.X W.X = amplitude ^ (2 : ℕ)) :
    ConformalFisherOnsagerPositiveContext (α := α) (H := H) :=
  W.toPositiveContextOfWitness
    { amplitude := amplitude, selfResponse_eq_square := selfResponse_eq_square }

-- theorem-class: bridge
/--
The conformal self-response is nonnegative on the operator-admissibility
constructive branch, using the proof-carrying square-response witness packet.
-/
@[rep_depth transport]
theorem selfResponse_nonneg_of_squareWitness
    (hSquare : ConformalSquareResponseWitness W.gibbs W.X) :
    0 ≤ W.gibbs.operatorConformalResponse W.X W.X := by
  exact (W.toConstructiveSquarePositiveContextOfWitness hSquare).selfResponse_nonneg

-- theorem-class: bridge
/--
The conformal self-response is nonnegative on the operator-admissibility
constructive branch, without re-threading separate operator-admissibility
premises.
-/
@[rep_depth transport]
theorem selfResponse_nonneg_of_squareResponse
    (amplitude : ℝ)
    (selfResponse_eq_square :
      W.gibbs.operatorConformalResponse W.X W.X = amplitude ^ (2 : ℕ)) :
    0 ≤ W.gibbs.operatorConformalResponse W.X W.X := by
  exact
    W.selfResponse_nonneg_of_squareWitness
      { amplitude := amplitude, selfResponse_eq_square := selfResponse_eq_square }

-- theorem-class: bridge
/--
Diagonal conformal Fisher/Onsager production is nonnegative on the
operator-admissibility constructive branch, using the proof-carrying
square-response witness packet instead of a separate amplitude/equality pair.
-/
@[rep_depth transport]
theorem fisherOnsagerProduction_nonneg_of_squareWitness
    (hSquare : ConformalSquareResponseWitness W.gibbs W.X) :
    0 ≤ (W.toPositiveContextOfWitness hSquare).fisherOnsagerProduction := by
  exact
    (W.toConstructiveSquarePositiveContextOfWitness hSquare).fisherOnsagerProduction_nonneg

-- theorem-class: bridge
/--
Diagonal conformal Fisher/Onsager production is nonnegative on the
operator-admissibility constructive branch, without re-threading separate
operator-admissibility premises.
-/
@[rep_depth transport]
theorem fisherOnsagerProduction_nonneg_of_squareResponse
    (amplitude : ℝ)
    (selfResponse_eq_square :
      W.gibbs.operatorConformalResponse W.X W.X = amplitude ^ (2 : ℕ)) :
    0 ≤ (W.toPositiveContext amplitude selfResponse_eq_square).fisherOnsagerProduction := by
  exact
    W.fisherOnsagerProduction_nonneg_of_squareWitness
      { amplitude := amplitude, selfResponse_eq_square := selfResponse_eq_square }

-- theorem-class: bridge
/--
Diagonal conformal Fisher/Onsager production is exactly the selected real
square on the operator-admissibility constructive branch, using the
proof-carrying square-response witness packet instead of a separate
amplitude/equality pair.
-/
@[rep_depth transport]
theorem fisherOnsagerProduction_eq_square_of_squareWitness
    (hSquare : ConformalSquareResponseWitness W.gibbs W.X) :
    (W.toPositiveContextOfWitness hSquare).fisherOnsagerProduction = hSquare.amplitude ^ (2 : ℕ) := by
  exact
    (W.toConstructiveSquarePositiveContextOfWitness hSquare).fisherOnsagerProduction_eq_square

end ConformalOperatorAdmissibilityWitness

namespace ConformalPositivePartitionWitness

variable {C : ConformalGibbsSouriauOperatorContext (α := α) (H := H)}

/--
Build the constructive square-response Fisher/Onsager-positive package directly
from a positive-partition witness plus the proof-carrying square-response
packet, without re-packaging a separate amplitude/equality pair.
-/
@[rep_depth transport]
noncomputable def toConstructiveSquarePositiveContextOfWitness
    (W : ConformalPositivePartitionWitness C)
    (weylGauge : WeylGaugeField EndH₂ EndH₂)
    (tkkParameter : ℝ)
    (hTKK : C.SatisfiesOperatorTKKMasterRelation tkkParameter)
    (hCone : C.IsConeAdmissible)
    (X Y : EndH₂)
    (hSquare : ConformalSquareResponseWitness C X) :
    ConstructiveConformalSquareFisherOnsagerPositiveContext (α := α) (H := H) where
  closureWitness :=
    W.toOperatorAdmissibilityWitness weylGauge tkkParameter hTKK hCone X Y
  amplitude := hSquare.amplitude
  selfResponse_eq_square := hSquare.selfResponse_eq_square

/--
Recover the legacy nonnegativity-only Fisher/Onsager surface directly from a
positive-partition witness plus a square-response witness packet.
-/
@[rep_depth transport]
noncomputable def toPositiveContextOfWitness
    (W : ConformalPositivePartitionWitness C)
    (weylGauge : WeylGaugeField EndH₂ EndH₂)
    (tkkParameter : ℝ)
    (hTKK : C.SatisfiesOperatorTKKMasterRelation tkkParameter)
    (hCone : C.IsConeAdmissible)
    (X Y : EndH₂)
    (hSquare : ConformalSquareResponseWitness C X) :
    ConformalFisherOnsagerPositiveContext (α := α) (H := H) :=
  (W.toConstructiveSquarePositiveContextOfWitness weylGauge tkkParameter hTKK hCone X Y
    hSquare).toPositiveContext

/--
Build the constructive square-response Fisher/Onsager-positive package directly
from a positive-partition witness, without re-packaging a separate
`hOperatorAdmissible` proof.
-/
@[rep_depth transport]
noncomputable def toConstructiveSquarePositiveContext
    (W : ConformalPositivePartitionWitness C)
    (weylGauge : WeylGaugeField EndH₂ EndH₂)
    (tkkParameter : ℝ)
    (hTKK : C.SatisfiesOperatorTKKMasterRelation tkkParameter)
    (hCone : C.IsConeAdmissible)
    (X Y : EndH₂)
    (amplitude : ℝ)
    (selfResponse_eq_square :
      C.operatorConformalResponse X X = amplitude ^ (2 : ℕ)) :
    ConstructiveConformalSquareFisherOnsagerPositiveContext (α := α) (H := H) where
  closureWitness :=
    W.toOperatorAdmissibilityWitness weylGauge tkkParameter hTKK hCone X Y
  amplitude := amplitude
  selfResponse_eq_square := selfResponse_eq_square

/--
Recover the legacy nonnegativity-only Fisher/Onsager surface directly from a
positive-partition witness plus a square-response certificate.
-/
@[rep_depth transport]
noncomputable def toPositiveContext
    (W : ConformalPositivePartitionWitness C)
    (weylGauge : WeylGaugeField EndH₂ EndH₂)
    (tkkParameter : ℝ)
    (hTKK : C.SatisfiesOperatorTKKMasterRelation tkkParameter)
    (hCone : C.IsConeAdmissible)
    (X Y : EndH₂)
    (amplitude : ℝ)
    (selfResponse_eq_square :
      C.operatorConformalResponse X X = amplitude ^ (2 : ℕ)) :
    ConformalFisherOnsagerPositiveContext (α := α) (H := H) :=
  (W.toConstructiveSquarePositiveContext weylGauge tkkParameter hTKK hCone X Y
    amplitude selfResponse_eq_square).toPositiveContext

-- theorem-class: bridge
/--
The conformal self-response is nonnegative on the positive-partition
constructive branch, using the proof-carrying square-response witness packet
instead of a separate amplitude/equality pair.
-/
@[rep_depth transport]
theorem selfResponse_nonneg_of_squareWitness
    (W : ConformalPositivePartitionWitness C)
    (weylGauge : WeylGaugeField EndH₂ EndH₂)
    (tkkParameter : ℝ)
    (hTKK : C.SatisfiesOperatorTKKMasterRelation tkkParameter)
    (hCone : C.IsConeAdmissible)
    (X Y : EndH₂)
    (hSquare : ConformalSquareResponseWitness C X) :
    0 ≤ C.operatorConformalResponse X X := by
  exact
    (W.toConstructiveSquarePositiveContextOfWitness weylGauge tkkParameter hTKK hCone X Y
      hSquare).selfResponse_nonneg

/--
The conformal self-response is nonnegative on the positive-partition
constructive branch, using proof-carrying TKK and cone witnesses instead of
bare `tkkParameter`/`hTKK` and `hCone` inputs.
-/
@[rep_depth transport]
theorem selfResponse_nonneg_of_squareWitness_of_TKKConeWitness
    (W : ConformalPositivePartitionWitness C)
    (weylGauge : WeylGaugeField EndH₂ EndH₂)
    (hTKK : ConformalTKKWitness (α := α) (H := H) C)
    (hCone : ConformalConeAdmissibilityWitness (α := α) (H := H) C)
    (X Y : EndH₂)
    (hSquare : ConformalSquareResponseWitness C X) :
    0 ≤ C.operatorConformalResponse X X := by
  exact
    (ConformalOperatorAdmissibilityWitness.toConstructiveSquarePositiveContextOfWitness
      (W := W.toOperatorAdmissibilityWitnessOfTKKConeWitness weylGauge hTKK hCone X Y)
      hSquare).selfResponse_nonneg

/--
The conformal self-response is nonnegative on the positive-partition
constructive branch, using the explicit partition witness instead of a bare
operator-admissibility packet.
-/
@[rep_depth transport]
theorem selfResponse_nonneg_of_squareResponse
    (W : ConformalPositivePartitionWitness C)
    (weylGauge : WeylGaugeField EndH₂ EndH₂)
    (tkkParameter : ℝ)
    (hTKK : C.SatisfiesOperatorTKKMasterRelation tkkParameter)
    (hCone : C.IsConeAdmissible)
    (X Y : EndH₂)
    (amplitude : ℝ)
    (selfResponse_eq_square :
      C.operatorConformalResponse X X = amplitude ^ (2 : ℕ)) :
    0 ≤ C.operatorConformalResponse X X := by
  exact
    (W.toConstructiveSquarePositiveContext weylGauge tkkParameter hTKK hCone X Y
      amplitude selfResponse_eq_square).selfResponse_nonneg

/--
The conformal self-response is nonnegative on the positive-partition
constructive branch, using proof-carrying TKK and cone witnesses instead of
bare `tkkParameter`/`hTKK` and `hCone` inputs while still accepting the direct
square-response equality surface.
-/
@[rep_depth transport]
theorem selfResponse_nonneg_of_squareResponse_of_TKKConeWitness
    (W : ConformalPositivePartitionWitness C)
    (weylGauge : WeylGaugeField EndH₂ EndH₂)
    (hTKK : ConformalTKKWitness (α := α) (H := H) C)
    (hCone : ConformalConeAdmissibilityWitness (α := α) (H := H) C)
    (X Y : EndH₂)
    (amplitude : ℝ)
    (selfResponse_eq_square :
      C.operatorConformalResponse X X = amplitude ^ (2 : ℕ)) :
    0 ≤ C.operatorConformalResponse X X := by
  exact
    (ConformalOperatorAdmissibilityWitness.toConstructiveSquarePositiveContext
      (W := W.toOperatorAdmissibilityWitnessOfTKKConeWitness weylGauge hTKK hCone X Y)
      amplitude selfResponse_eq_square).selfResponse_nonneg

-- theorem-class: bridge
/--
Diagonal conformal Fisher/Onsager production is nonnegative on the
positive-partition constructive branch, using the proof-carrying square-response
witness packet instead of a separate amplitude/equality pair.
-/
@[rep_depth transport]
theorem fisherOnsagerProduction_nonneg_of_squareWitness
    (W : ConformalPositivePartitionWitness C)
    (weylGauge : WeylGaugeField EndH₂ EndH₂)
    (tkkParameter : ℝ)
    (hTKK : C.SatisfiesOperatorTKKMasterRelation tkkParameter)
    (hCone : C.IsConeAdmissible)
    (X Y : EndH₂)
    (hSquare : ConformalSquareResponseWitness C X) :
    0 ≤
      (W.toPositiveContextOfWitness weylGauge tkkParameter hTKK hCone X Y
        hSquare).fisherOnsagerProduction := by
  exact
    (W.toConstructiveSquarePositiveContextOfWitness weylGauge tkkParameter hTKK hCone X Y
      hSquare).fisherOnsagerProduction_nonneg

/--
Diagonal conformal Fisher/Onsager production is nonnegative on the
positive-partition constructive branch, using proof-carrying TKK and cone
witnesses instead of bare `tkkParameter`/`hTKK` and `hCone` inputs.
-/
@[rep_depth transport]
theorem fisherOnsagerProduction_nonneg_of_squareWitness_of_TKKConeWitness
    (W : ConformalPositivePartitionWitness C)
    (weylGauge : WeylGaugeField EndH₂ EndH₂)
    (hTKK : ConformalTKKWitness (α := α) (H := H) C)
    (hCone : ConformalConeAdmissibilityWitness (α := α) (H := H) C)
    (X Y : EndH₂)
    (hSquare : ConformalSquareResponseWitness C X) :
    0 ≤
      (ConformalOperatorAdmissibilityWitness.toPositiveContextOfWitness
        (W := W.toOperatorAdmissibilityWitnessOfTKKConeWitness weylGauge hTKK hCone X Y)
        hSquare).fisherOnsagerProduction := by
  exact
    (ConformalOperatorAdmissibilityWitness.toConstructiveSquarePositiveContextOfWitness
      (W := W.toOperatorAdmissibilityWitnessOfTKKConeWitness weylGauge hTKK hCone X Y)
      hSquare).fisherOnsagerProduction_nonneg

/--
Diagonal conformal Fisher/Onsager production is nonnegative on the
positive-partition constructive branch, using the explicit partition witness
instead of a bare operator-admissibility packet.
-/
@[rep_depth transport]
theorem fisherOnsagerProduction_nonneg_of_squareResponse
    (W : ConformalPositivePartitionWitness C)
    (weylGauge : WeylGaugeField EndH₂ EndH₂)
    (tkkParameter : ℝ)
    (hTKK : C.SatisfiesOperatorTKKMasterRelation tkkParameter)
    (hCone : C.IsConeAdmissible)
    (X Y : EndH₂)
    (amplitude : ℝ)
    (selfResponse_eq_square :
      C.operatorConformalResponse X X = amplitude ^ (2 : ℕ)) :
    0 ≤
      (W.toPositiveContext weylGauge tkkParameter hTKK hCone X Y amplitude
        selfResponse_eq_square).fisherOnsagerProduction := by
  exact
    (W.toConstructiveSquarePositiveContext weylGauge tkkParameter hTKK hCone X Y
      amplitude selfResponse_eq_square).fisherOnsagerProduction_nonneg

/--
Diagonal conformal Fisher/Onsager production is nonnegative on the
positive-partition constructive branch, using proof-carrying TKK and cone
witnesses instead of bare `tkkParameter`/`hTKK` and `hCone` inputs while still
accepting the direct square-response equality surface.
-/
@[rep_depth transport]
theorem fisherOnsagerProduction_nonneg_of_squareResponse_of_TKKConeWitness
    (W : ConformalPositivePartitionWitness C)
    (weylGauge : WeylGaugeField EndH₂ EndH₂)
    (hTKK : ConformalTKKWitness (α := α) (H := H) C)
    (hCone : ConformalConeAdmissibilityWitness (α := α) (H := H) C)
    (X Y : EndH₂)
    (amplitude : ℝ)
    (selfResponse_eq_square :
      C.operatorConformalResponse X X = amplitude ^ (2 : ℕ)) :
    0 ≤
      (ConformalOperatorAdmissibilityWitness.toPositiveContext
        (W := W.toOperatorAdmissibilityWitnessOfTKKConeWitness weylGauge hTKK hCone X Y)
        amplitude selfResponse_eq_square).fisherOnsagerProduction := by
  exact
    (ConformalOperatorAdmissibilityWitness.toConstructiveSquarePositiveContext
      (W := W.toOperatorAdmissibilityWitnessOfTKKConeWitness weylGauge hTKK hCone X Y)
      amplitude selfResponse_eq_square).fisherOnsagerProduction_nonneg

-- theorem-class: bridge
/--
Diagonal conformal Fisher/Onsager production is exactly the selected real
square on the positive-partition constructive branch, using the proof-carrying
square-response witness packet instead of a separate amplitude/equality pair.
-/
@[rep_depth transport]
theorem fisherOnsagerProduction_eq_square_of_squareWitness
    (W : ConformalPositivePartitionWitness C)
    (weylGauge : WeylGaugeField EndH₂ EndH₂)
    (tkkParameter : ℝ)
    (hTKK : C.SatisfiesOperatorTKKMasterRelation tkkParameter)
    (hCone : C.IsConeAdmissible)
    (X Y : EndH₂)
    (hSquare : ConformalSquareResponseWitness C X) :
    (W.toPositiveContextOfWitness weylGauge tkkParameter hTKK hCone X Y
      hSquare).fisherOnsagerProduction = hSquare.amplitude ^ (2 : ℕ) := by
  exact
    (W.toConstructiveSquarePositiveContextOfWitness weylGauge tkkParameter hTKK hCone X Y
      hSquare).fisherOnsagerProduction_eq_square

-- theorem-class: bridge
/--
Diagonal conformal Fisher/Onsager production is exactly the selected real
square on the positive-partition constructive branch, using proof-carrying TKK
and cone witnesses instead of bare `tkkParameter`/`hTKK` and `hCone` inputs.
-/
@[rep_depth transport]
theorem fisherOnsagerProduction_eq_square_of_squareWitness_of_TKKConeWitness
    (W : ConformalPositivePartitionWitness C)
    (weylGauge : WeylGaugeField EndH₂ EndH₂)
    (hTKK : ConformalTKKWitness (α := α) (H := H) C)
    (hCone : ConformalConeAdmissibilityWitness (α := α) (H := H) C)
    (X Y : EndH₂)
    (hSquare : ConformalSquareResponseWitness C X) :
    (ConformalOperatorAdmissibilityWitness.toPositiveContextOfWitness
      (W := W.toOperatorAdmissibilityWitnessOfTKKConeWitness weylGauge hTKK hCone X Y)
      hSquare).fisherOnsagerProduction = hSquare.amplitude ^ (2 : ℕ) := by
  exact
    (ConformalOperatorAdmissibilityWitness.toConstructiveSquarePositiveContextOfWitness
      (W := W.toOperatorAdmissibilityWitnessOfTKKConeWitness weylGauge hTKK hCone X Y)
      hSquare).fisherOnsagerProduction_eq_square

-- theorem-class: bridge
/--
Diagonal conformal Fisher/Onsager production is exactly the selected real
square on the positive-partition constructive branch, using the explicit
partition witness instead of a bare operator-admissibility packet.
-/
@[rep_depth transport]
theorem fisherOnsagerProduction_eq_square_of_squareResponse
    (W : ConformalPositivePartitionWitness C)
    (weylGauge : WeylGaugeField EndH₂ EndH₂)
    (tkkParameter : ℝ)
    (hTKK : C.SatisfiesOperatorTKKMasterRelation tkkParameter)
    (hCone : C.IsConeAdmissible)
    (X Y : EndH₂)
    (amplitude : ℝ)
    (selfResponse_eq_square :
      C.operatorConformalResponse X X = amplitude ^ (2 : ℕ)) :
    (W.toPositiveContext weylGauge tkkParameter hTKK hCone X Y amplitude
      selfResponse_eq_square).fisherOnsagerProduction = amplitude ^ (2 : ℕ) := by
  exact
    (W.toConstructiveSquarePositiveContext weylGauge tkkParameter hTKK hCone X Y
      amplitude selfResponse_eq_square).fisherOnsagerProduction_eq_square

/--
Diagonal conformal Fisher/Onsager production is exactly the selected real
square on the positive-partition constructive branch, using proof-carrying TKK
and cone witnesses instead of bare `tkkParameter`/`hTKK` and `hCone` inputs,
while still accepting the direct square-response equality surface.
-/
@[rep_depth transport]
theorem fisherOnsagerProduction_eq_square_of_squareResponse_of_TKKConeWitness
    (W : ConformalPositivePartitionWitness C)
    (weylGauge : WeylGaugeField EndH₂ EndH₂)
    (hTKK : ConformalTKKWitness (α := α) (H := H) C)
    (hCone : ConformalConeAdmissibilityWitness (α := α) (H := H) C)
    (X Y : EndH₂)
    (amplitude : ℝ)
    (selfResponse_eq_square :
      C.operatorConformalResponse X X = amplitude ^ (2 : ℕ)) :
    (ConformalOperatorAdmissibilityWitness.toPositiveContext
      (W := W.toOperatorAdmissibilityWitnessOfTKKConeWitness weylGauge hTKK hCone X Y)
      amplitude selfResponse_eq_square).fisherOnsagerProduction = amplitude ^ (2 : ℕ) := by
  exact
    (ConformalOperatorAdmissibilityWitness.toConstructiveSquarePositiveContext
      (W := W.toOperatorAdmissibilityWitnessOfTKKConeWitness weylGauge hTKK hCone X Y)
      amplitude selfResponse_eq_square).fisherOnsagerProduction_eq_square

end ConformalPositivePartitionWitness

namespace ConformalCartanOddPartitionWitness

variable {L : Type _} [LieRing L] [LieAlgebra ℝ L]
variable {C : ConformalGibbsSouriauOperatorContext (α := α) (H := H)}

/--
Build the constructive square-response Fisher/Onsager-positive package directly
from the Cartan-odd partition witness branch, using the proof-carrying
square-response witness packet instead of a separate amplitude/equality pair.
-/
@[rep_depth transport]
noncomputable def toConstructiveSquarePositiveContextOfWitness
    (W : ConformalCartanOddPartitionWitness (α := α) (H := H) (C := C) (L := L))
    (weylGauge : WeylGaugeField EndH₂ EndH₂)
    (tkkParameter : ℝ)
    (hTKK : C.SatisfiesOperatorTKKMasterRelation tkkParameter)
    (hCone : C.IsConeAdmissible)
    (X Y : EndH₂)
    (hSquare : ConformalSquareResponseWitness C X) :
    ConstructiveConformalSquareFisherOnsagerPositiveContext (α := α) (H := H) where
  closureWitness :=
    W.toOperatorAdmissibilityWitness weylGauge tkkParameter hTKK hCone X Y
  amplitude := hSquare.amplitude
  selfResponse_eq_square := hSquare.selfResponse_eq_square

/--
Build the constructive square-response Fisher/Onsager-positive package directly
from the Cartan-odd partition witness branch, without re-packaging an explicit
positive-partition or operator-admissibility proof.
-/
@[rep_depth transport]
noncomputable def toConstructiveSquarePositiveContext
    (W : ConformalCartanOddPartitionWitness (α := α) (H := H) (C := C) (L := L))
    (weylGauge : WeylGaugeField EndH₂ EndH₂)
    (tkkParameter : ℝ)
    (hTKK : C.SatisfiesOperatorTKKMasterRelation tkkParameter)
    (hCone : C.IsConeAdmissible)
    (X Y : EndH₂)
    (amplitude : ℝ)
    (selfResponse_eq_square :
      C.operatorConformalResponse X X = amplitude ^ (2 : ℕ)) :
    ConstructiveConformalSquareFisherOnsagerPositiveContext (α := α) (H := H) :=
  W.toConstructiveSquarePositiveContextOfWitness weylGauge tkkParameter hTKK hCone X Y
    { amplitude := amplitude, selfResponse_eq_square := selfResponse_eq_square }

/--
Recover the legacy nonnegativity-only Fisher/Onsager surface directly from the
Cartan-odd partition witness plus a square-response certificate.
-/
@[rep_depth transport]
noncomputable def toPositiveContextOfWitness
    (W : ConformalCartanOddPartitionWitness (α := α) (H := H) (C := C) (L := L))
    (weylGauge : WeylGaugeField EndH₂ EndH₂)
    (tkkParameter : ℝ)
    (hTKK : C.SatisfiesOperatorTKKMasterRelation tkkParameter)
    (hCone : C.IsConeAdmissible)
    (X Y : EndH₂)
    (hSquare : ConformalSquareResponseWitness C X) :
    ConformalFisherOnsagerPositiveContext (α := α) (H := H) :=
  (W.toConstructiveSquarePositiveContextOfWitness weylGauge tkkParameter hTKK hCone X Y
    hSquare).toPositiveContext

/--
Recover the legacy nonnegativity-only Fisher/Onsager surface directly from the
Cartan-odd partition witness plus a square-response certificate.
-/
@[rep_depth transport]
noncomputable def toPositiveContext
    (W : ConformalCartanOddPartitionWitness (α := α) (H := H) (C := C) (L := L))
    (weylGauge : WeylGaugeField EndH₂ EndH₂)
    (tkkParameter : ℝ)
    (hTKK : C.SatisfiesOperatorTKKMasterRelation tkkParameter)
    (hCone : C.IsConeAdmissible)
    (X Y : EndH₂)
    (amplitude : ℝ)
    (selfResponse_eq_square :
      C.operatorConformalResponse X X = amplitude ^ (2 : ℕ)) :
    ConformalFisherOnsagerPositiveContext (α := α) (H := H) :=
  W.toPositiveContextOfWitness weylGauge tkkParameter hTKK hCone X Y
    { amplitude := amplitude, selfResponse_eq_square := selfResponse_eq_square }

-- theorem-class: bridge
/--
The conformal self-response is nonnegative on the Cartan-odd constructive
branch, using the proof-carrying square-response witness packet instead of a
separate amplitude/equality pair.
-/
@[rep_depth transport]
theorem selfResponse_nonneg_of_squareWitness
    (W : ConformalCartanOddPartitionWitness (α := α) (H := H) (C := C) (L := L))
    (weylGauge : WeylGaugeField EndH₂ EndH₂)
    (tkkParameter : ℝ)
    (hTKK : C.SatisfiesOperatorTKKMasterRelation tkkParameter)
    (hCone : C.IsConeAdmissible)
    (X Y : EndH₂)
    (hSquare : ConformalSquareResponseWitness C X) :
    0 ≤ C.operatorConformalResponse X X := by
  exact
    (W.toConstructiveSquarePositiveContextOfWitness weylGauge tkkParameter hTKK hCone X Y
      hSquare).selfResponse_nonneg

/--
The conformal self-response is nonnegative on the Cartan-odd constructive
branch, using proof-carrying TKK and cone witnesses instead of bare
`tkkParameter`/`hTKK` and `hCone` inputs.
-/
@[rep_depth transport]
theorem selfResponse_nonneg_of_squareWitness_of_TKKConeWitness
    (W : ConformalCartanOddPartitionWitness (α := α) (H := H) (C := C) (L := L))
    (weylGauge : WeylGaugeField EndH₂ EndH₂)
    (hTKK : ConformalTKKWitness (α := α) (H := H) C)
    (hCone : ConformalConeAdmissibilityWitness (α := α) (H := H) C)
    (X Y : EndH₂)
    (hSquare : ConformalSquareResponseWitness C X) :
    0 ≤ C.operatorConformalResponse X X := by
  exact
    (ConformalOperatorAdmissibilityWitness.toConstructiveSquarePositiveContextOfWitness
      (W := W.toOperatorAdmissibilityWitnessOfTKKConeWitness weylGauge hTKK hCone X Y)
      hSquare).selfResponse_nonneg

-- theorem-class: bridge
/--
The conformal self-response is nonnegative on the Cartan-odd constructive
branch, using the owner Cartan positivity route instead of a bare
operator-admissibility packet.
-/
@[rep_depth transport]
theorem selfResponse_nonneg_of_squareResponse
    (W : ConformalCartanOddPartitionWitness (α := α) (H := H) (C := C) (L := L))
    (weylGauge : WeylGaugeField EndH₂ EndH₂)
    (tkkParameter : ℝ)
    (hTKK : C.SatisfiesOperatorTKKMasterRelation tkkParameter)
    (hCone : C.IsConeAdmissible)
    (X Y : EndH₂)
    (amplitude : ℝ)
    (selfResponse_eq_square :
      C.operatorConformalResponse X X = amplitude ^ (2 : ℕ)) :
    0 ≤ C.operatorConformalResponse X X := by
  exact
    W.selfResponse_nonneg_of_squareWitness weylGauge tkkParameter hTKK hCone X Y
      { amplitude := amplitude, selfResponse_eq_square := selfResponse_eq_square }

/--
The conformal self-response is nonnegative on the Cartan-odd constructive
branch, using proof-carrying TKK and cone witnesses instead of bare
`tkkParameter`/`hTKK` and `hCone` inputs while still accepting the direct
square-response equality surface.
-/
@[rep_depth transport]
theorem selfResponse_nonneg_of_squareResponse_of_TKKConeWitness
    (W : ConformalCartanOddPartitionWitness (α := α) (H := H) (C := C) (L := L))
    (weylGauge : WeylGaugeField EndH₂ EndH₂)
    (hTKK : ConformalTKKWitness (α := α) (H := H) C)
    (hCone : ConformalConeAdmissibilityWitness (α := α) (H := H) C)
    (X Y : EndH₂)
    (amplitude : ℝ)
    (selfResponse_eq_square :
      C.operatorConformalResponse X X = amplitude ^ (2 : ℕ)) :
    0 ≤ C.operatorConformalResponse X X := by
  exact
    (ConformalOperatorAdmissibilityWitness.toConstructiveSquarePositiveContext
      (W := W.toOperatorAdmissibilityWitnessOfTKKConeWitness weylGauge hTKK hCone X Y)
      amplitude selfResponse_eq_square).selfResponse_nonneg

-- theorem-class: bridge
/--
Diagonal conformal Fisher/Onsager production is nonnegative on the Cartan-odd
constructive branch, using the proof-carrying square-response witness packet
instead of a separate amplitude/equality pair.
-/
@[rep_depth transport]
theorem fisherOnsagerProduction_nonneg_of_squareWitness
    (W : ConformalCartanOddPartitionWitness (α := α) (H := H) (C := C) (L := L))
    (weylGauge : WeylGaugeField EndH₂ EndH₂)
    (tkkParameter : ℝ)
    (hTKK : C.SatisfiesOperatorTKKMasterRelation tkkParameter)
    (hCone : C.IsConeAdmissible)
    (X Y : EndH₂)
    (hSquare : ConformalSquareResponseWitness C X) :
    0 ≤
      (W.toPositiveContextOfWitness weylGauge tkkParameter hTKK hCone X Y
        hSquare).fisherOnsagerProduction := by
  exact
    (W.toConstructiveSquarePositiveContextOfWitness weylGauge tkkParameter hTKK hCone X Y
      hSquare).fisherOnsagerProduction_nonneg

/--
Diagonal conformal Fisher/Onsager production is nonnegative on the Cartan-odd
constructive branch, using proof-carrying TKK and cone witnesses instead of
bare `tkkParameter`/`hTKK` and `hCone` inputs.
-/
@[rep_depth transport]
theorem fisherOnsagerProduction_nonneg_of_squareWitness_of_TKKConeWitness
    (W : ConformalCartanOddPartitionWitness (α := α) (H := H) (C := C) (L := L))
    (weylGauge : WeylGaugeField EndH₂ EndH₂)
    (hTKK : ConformalTKKWitness (α := α) (H := H) C)
    (hCone : ConformalConeAdmissibilityWitness (α := α) (H := H) C)
    (X Y : EndH₂)
    (hSquare : ConformalSquareResponseWitness C X) :
    0 ≤
      (ConformalOperatorAdmissibilityWitness.toPositiveContextOfWitness
        (W := W.toOperatorAdmissibilityWitnessOfTKKConeWitness weylGauge hTKK hCone X Y)
        hSquare).fisherOnsagerProduction := by
  exact
    (ConformalOperatorAdmissibilityWitness.toConstructiveSquarePositiveContextOfWitness
      (W := W.toOperatorAdmissibilityWitnessOfTKKConeWitness weylGauge hTKK hCone X Y)
      hSquare).fisherOnsagerProduction_nonneg

-- theorem-class: bridge
/--
Diagonal conformal Fisher/Onsager production is nonnegative on the Cartan-odd
constructive branch, using the owner Cartan positivity route instead of a bare
operator-admissibility packet.
-/
@[rep_depth transport]
theorem fisherOnsagerProduction_nonneg_of_squareResponse
    (W : ConformalCartanOddPartitionWitness (α := α) (H := H) (C := C) (L := L))
    (weylGauge : WeylGaugeField EndH₂ EndH₂)
    (tkkParameter : ℝ)
    (hTKK : C.SatisfiesOperatorTKKMasterRelation tkkParameter)
    (hCone : C.IsConeAdmissible)
    (X Y : EndH₂)
    (amplitude : ℝ)
    (selfResponse_eq_square :
      C.operatorConformalResponse X X = amplitude ^ (2 : ℕ)) :
    0 ≤
      (W.toPositiveContext weylGauge tkkParameter hTKK hCone X Y amplitude
        selfResponse_eq_square).fisherOnsagerProduction := by
  exact
    (W.toConstructiveSquarePositiveContext weylGauge tkkParameter hTKK hCone X Y
      amplitude selfResponse_eq_square).fisherOnsagerProduction_nonneg

/--
Diagonal conformal Fisher/Onsager production is nonnegative on the Cartan-odd
constructive branch, using proof-carrying TKK and cone witnesses instead of bare
`tkkParameter`/`hTKK` and `hCone` inputs while still accepting the direct
square-response equality surface.
-/
@[rep_depth transport]
theorem fisherOnsagerProduction_nonneg_of_squareResponse_of_TKKConeWitness
    (W : ConformalCartanOddPartitionWitness (α := α) (H := H) (C := C) (L := L))
    (weylGauge : WeylGaugeField EndH₂ EndH₂)
    (hTKK : ConformalTKKWitness (α := α) (H := H) C)
    (hCone : ConformalConeAdmissibilityWitness (α := α) (H := H) C)
    (X Y : EndH₂)
    (amplitude : ℝ)
    (selfResponse_eq_square :
      C.operatorConformalResponse X X = amplitude ^ (2 : ℕ)) :
    0 ≤
      (ConformalOperatorAdmissibilityWitness.toPositiveContext
        (W := W.toOperatorAdmissibilityWitnessOfTKKConeWitness weylGauge hTKK hCone X Y)
        amplitude selfResponse_eq_square).fisherOnsagerProduction := by
  exact
    (ConformalOperatorAdmissibilityWitness.toConstructiveSquarePositiveContext
      (W := W.toOperatorAdmissibilityWitnessOfTKKConeWitness weylGauge hTKK hCone X Y)
      amplitude selfResponse_eq_square).fisherOnsagerProduction_nonneg

-- theorem-class: bridge
/--
Diagonal conformal Fisher/Onsager production is exactly the selected real
square on the Cartan-odd constructive branch, using the proof-carrying
square-response witness packet instead of a separate amplitude/equality pair.
-/
@[rep_depth transport]
theorem fisherOnsagerProduction_eq_square_of_squareWitness
    (W : ConformalCartanOddPartitionWitness (α := α) (H := H) (C := C) (L := L))
    (weylGauge : WeylGaugeField EndH₂ EndH₂)
    (tkkParameter : ℝ)
    (hTKK : C.SatisfiesOperatorTKKMasterRelation tkkParameter)
    (hCone : C.IsConeAdmissible)
    (X Y : EndH₂)
    (hSquare : ConformalSquareResponseWitness C X) :
    (W.toPositiveContextOfWitness weylGauge tkkParameter hTKK hCone X Y
      hSquare).fisherOnsagerProduction = hSquare.amplitude ^ (2 : ℕ) := by
  exact
    (W.toConstructiveSquarePositiveContextOfWitness weylGauge tkkParameter hTKK hCone X Y
      hSquare).fisherOnsagerProduction_eq_square

-- theorem-class: bridge
/--
Diagonal conformal Fisher/Onsager production is exactly the selected real
square on the Cartan-odd constructive branch, using proof-carrying TKK and
cone witnesses instead of bare `tkkParameter`/`hTKK` and `hCone` inputs.
-/
@[rep_depth transport]
theorem fisherOnsagerProduction_eq_square_of_squareWitness_of_TKKConeWitness
    (W : ConformalCartanOddPartitionWitness (α := α) (H := H) (C := C) (L := L))
    (weylGauge : WeylGaugeField EndH₂ EndH₂)
    (hTKK : ConformalTKKWitness (α := α) (H := H) C)
    (hCone : ConformalConeAdmissibilityWitness (α := α) (H := H) C)
    (X Y : EndH₂)
    (hSquare : ConformalSquareResponseWitness C X) :
    (ConformalOperatorAdmissibilityWitness.toPositiveContextOfWitness
      (W := W.toOperatorAdmissibilityWitnessOfTKKConeWitness weylGauge hTKK hCone X Y)
      hSquare).fisherOnsagerProduction = hSquare.amplitude ^ (2 : ℕ) := by
  exact
    (ConformalOperatorAdmissibilityWitness.toConstructiveSquarePositiveContextOfWitness
      (W := W.toOperatorAdmissibilityWitnessOfTKKConeWitness weylGauge hTKK hCone X Y)
      hSquare).fisherOnsagerProduction_eq_square

-- theorem-class: bridge
/--
Diagonal conformal Fisher/Onsager production is exactly the selected real
square on the Cartan-odd constructive branch, using the owner Cartan
positivity route instead of a bare operator-admissibility packet.
-/
@[rep_depth transport]
theorem fisherOnsagerProduction_eq_square_of_squareResponse
    (W : ConformalCartanOddPartitionWitness (α := α) (H := H) (C := C) (L := L))
    (weylGauge : WeylGaugeField EndH₂ EndH₂)
    (tkkParameter : ℝ)
    (hTKK : C.SatisfiesOperatorTKKMasterRelation tkkParameter)
    (hCone : C.IsConeAdmissible)
    (X Y : EndH₂)
    (amplitude : ℝ)
    (selfResponse_eq_square :
      C.operatorConformalResponse X X = amplitude ^ (2 : ℕ)) :
    (W.toPositiveContext weylGauge tkkParameter hTKK hCone X Y amplitude
      selfResponse_eq_square).fisherOnsagerProduction = amplitude ^ (2 : ℕ) := by
  exact
    (W.toConstructiveSquarePositiveContext weylGauge tkkParameter hTKK hCone X Y
      amplitude selfResponse_eq_square).fisherOnsagerProduction_eq_square

end ConformalCartanOddPartitionWitness

/-! ## Grand-canonical Fock-number coupling over the conformal operator context -/

/--
Grand-canonical Fock-number bridge over the conformal operator context.

The Fock occupation lane is an operator on the same doubled Krein carrier.
This structure does not identify Fock occupation with finite counts, chiral
defect, or central charge; those require separate representation theorems.
-/
@[rep_depth transport]
structure ConformalGrandCanonicalFockContext where
  closure : ConformalWeylTKKKKTJordanLieContext (α := α) (H := H)
  mixing : BogoliubovMixingParams
  hamiltonian : EndH₂
  chemicalPotential : ℝ

namespace ConformalGrandCanonicalFockContext

variable (C : ConformalGrandCanonicalFockContext (α := α) (H := H))

/-- Bogoliubov Fock occupation operator selected by the context. -/
@[rep_depth transport]
noncomputable def fockOccupationOperator : EndH₂ :=
  bogoliubovNumberOperator (E := H) C.mixing

/-- Chemical-potential coupling `μN_B` as a Weyl/Fock gauge term. -/
@[rep_depth thermo]
noncomputable def chemicalPotentialFockGaugeTerm : EndH₂ :=
  (fockNumberGauge (E := H) C.mixing).gaugeOf C.chemicalPotential

/-- Grand-canonical Fock generator `H - μN_B` on the doubled Krein carrier. -/
@[rep_depth thermo]
noncomputable def grandCanonicalFockOperator : EndH₂ :=
  grandCanonicalFockGenerator (E := H)
    C.mixing C.hamiltonian C.chemicalPotential

-- theorem-class: bridge
/-- The Fock occupation operator is creation after annihilation. -/
@[rep_depth transport]
theorem fockOccupationOperator_eq_creation_after_annihilation :
    C.fockOccupationOperator =
      (bogoliubovCreation (E := H) C.mixing).comp
        (bogoliubovAnnihilation (E := H) C.mixing) := by
  rfl

-- theorem-class: bridge
/-- The chemical potential couples linearly to the Fock occupation operator. -/
@[rep_depth thermo]
theorem chemicalPotentialFockGaugeTerm_eq_mu_smul_fockOccupation :
    C.chemicalPotentialFockGaugeTerm =
      C.chemicalPotential • C.fockOccupationOperator := by
  rfl

-- theorem-class: bridge
/-- The grand-canonical Fock operator has the owner form `H - μN_B`. -/
@[rep_depth thermo]
theorem grandCanonicalFockOperator_eq_hamiltonian_sub_fockGauge :
    C.grandCanonicalFockOperator =
      C.hamiltonian - C.chemicalPotentialFockGaugeTerm := by
  rfl

/--
Functorial affine bridge from a finite grand-canonical count shadow to the
operatorial Fock number lane over this conformal KKT/TKK context.

This preserves the chemical-potential affine form across categories:
finite `E(x) - μN(x)` and operatorial `H - μN_B`.  It does not identify the
finite count observable with the Fock occupation operator.
-/
@[rep_depth thermo, spine_morphism, spine_functor, spine_functor_lift]
def finiteFockChemicalPotentialAffineFunctor
    (params : GrandCanonicalTwoParam α) :
    FiniteFockChemicalPotentialAffineBridge
      params C.mixing C.hamiltonian C.chemicalPotential :=
  finiteFockChemicalPotentialAffineBridge
    params C.mixing C.hamiltonian C.chemicalPotential

/--
First-quantization form of the same functorial bridge over the conformal
KKT/TKK context: count-state functions are lifted to the Fock operator lane
while preserving the affine chemical-potential expression.
-/
@[rep_depth thermo, spine_morphism, spine_functor, spine_functor_lift]
def firstQuantizationChemicalPotentialAffineFunctor
    (params : GrandCanonicalTwoParam α) :
    FiniteFockChemicalPotentialAffineBridge
      params C.mixing C.hamiltonian C.chemicalPotential :=
  firstQuantizationChemicalPotentialAffineBridge
    params C.mixing C.hamiltonian C.chemicalPotential

-- theorem-class: bridge
/--
The functorial affine bridge exposes the finite chemical-potential gauge
coupling as `μ * N(x)`.
-/
@[rep_depth thermo]
theorem finiteFockChemicalPotentialAffineFunctor_finiteGauge
    (params : GrandCanonicalTwoParam α) (x : α) :
    (C.finiteFockChemicalPotentialAffineFunctor params).finiteGauge x =
      chemicalPotentialGauge_apply params C.chemicalPotential x := by
  rfl

-- theorem-class: bridge
/--
The functorial affine bridge exposes the Fock operator form `H - μN_B`.
-/
@[rep_depth thermo]
theorem finiteFockChemicalPotentialAffineFunctor_fockShiftedHamiltonian
    (params : GrandCanonicalTwoParam α) :
    (C.finiteFockChemicalPotentialAffineFunctor params).fockShiftedHamiltonian =
      grandCanonicalFockGenerator_eq_hamiltonian_sub_fockNumberGauge
        (E := H) C.mixing C.hamiltonian C.chemicalPotential := by
  rfl

/--
Grand-canonical/Weyl/TKK/KKT bridge proposition.

This is the compile-backed form of the synthesis: finite chemical-potential
coupling, Fock number coupling, and the operator Weyl/TKK/KKT closure packet
hold simultaneously.  It is intentionally weaker than any black-hole or
contour-residue claim, because those are not present as owner theorems in the
current Lean source.
-/
@[rep_depth thermo]
def SatisfiesWeylGrandCanonicalTKKKKTBridge
    (params : GrandCanonicalTwoParam α) : Prop :=
  C.closure.SatisfiesKKT_TKK_Weyl_JordanLieClosure
    ∧ (∀ x : α,
        (chemicalPotentialGauge params).gaugeOf C.chemicalPotential x =
          C.chemicalPotential * params.number x)
    ∧ (∀ x : α,
        shiftedEnergy params C.chemicalPotential x =
          params.energy x
            - (chemicalPotentialGauge params).gaugeOf C.chemicalPotential x)
    ∧ C.chemicalPotentialFockGaugeTerm =
        C.chemicalPotential • C.fockOccupationOperator
    ∧ C.grandCanonicalFockOperator =
        C.hamiltonian - C.chemicalPotentialFockGaugeTerm

-- theorem-class: bridge
/--
The conformal Fock context supplies the grand-canonical affine bridge and the
operator Weyl/TKK/KKT closure gates.
-/
@[rep_depth thermo, spine_morphism, spine_functor, spine_functor_lift]
theorem satisfiesWeylGrandCanonicalTKKKKTBridge
    (params : GrandCanonicalTwoParam α) :
    C.SatisfiesWeylGrandCanonicalTKKKKTBridge params := by
  exact
    ⟨C.closure.satisfiesKKT_TKK_Weyl_JordanLieClosure,
      (fun x => chemicalPotentialGauge_apply params C.chemicalPotential x),
      (fun x => shiftedEnergy_eq_energy_sub_chemicalPotentialGauge
        params C.chemicalPotential x),
      C.chemicalPotentialFockGaugeTerm_eq_mu_smul_fockOccupation,
      C.grandCanonicalFockOperator_eq_hamiltonian_sub_fockGauge⟩

/--
Change only the Weyl representative in the underlying conformal closure
packet.  The grand-canonical Fock data are unchanged.
-/
@[rep_depth transport]
noncomputable def transformWeylGauge
    (σ : WeylGaugeParameter EndH₂ EndH₂) :
    ConformalGrandCanonicalFockContext (α := α) (H := H) where
  closure := C.closure.transformWeylGauge σ
  mixing := C.mixing
  hamiltonian := C.hamiltonian
  chemicalPotential := C.chemicalPotential

-- theorem-class: bridge
/--
Additive Weyl gauge transformations preserve the combined
grand-canonical/TKK/KKT bridge.
-/
@[rep_depth thermo]
theorem transformWeylGauge_preserves_weylGrandCanonicalTKKKKTBridge
    (params : GrandCanonicalTwoParam α)
    (σ : WeylGaugeParameter EndH₂ EndH₂) :
    (C.transformWeylGauge σ).SatisfiesWeylGrandCanonicalTKKKKTBridge params := by
  exact (C.transformWeylGauge σ).satisfiesWeylGrandCanonicalTKKKKTBridge params

-- theorem-class: bridge
/-- At zero chemical potential, the grand-canonical Fock operator is the Hamiltonian. -/
@[rep_depth thermo]
theorem grandCanonicalFockOperator_zero_mu
    (hμ : C.chemicalPotential = 0) :
    C.grandCanonicalFockOperator = C.hamiltonian := by
  rw [grandCanonicalFockOperator, hμ]
  exact
    grandCanonicalFockGenerator_zero_mu (E := H) C.mixing C.hamiltonian

end ConformalGrandCanonicalFockContext

end InfoGeometry.Canonical.SouriauConformalKKT
