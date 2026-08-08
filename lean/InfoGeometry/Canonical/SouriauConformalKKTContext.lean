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
- an independent property conformal/KKT carrier supplies the grade-zero
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
property conformal/KKT carrier on the same doubled Hilbert carrier.
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
On the property conformal/KKT side, the conformal dilation is the property
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

/-- Translation generator `P` in the property conformal carrier. -/
@[rep_depth transport]
noncomputable def PGenerator : EndH₂ :=
  C.base.CCI.toConformalInference.P

/-- Dilation generator `D` in the property conformal carrier. -/
@[rep_depth transport]
noncomputable def DGenerator : EndH₂ :=
  C.base.CCI.toConformalInference.D

/-- Special conformal generator `K` in the property conformal carrier. -/
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
supercharacter context is built without any external split property.
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
supercharacter without carrying a separate split-equality property.
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
carrying a separate split-equality property.
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

/-! ### Self-dual/chiral light-cone owner property -/

/--
Source-backed property for the causal chiral light-cone operator lane.

The data lives on the same doubled carrier as the conformal Gibbs-Souriau
context.  Its proof content is imported from the owner surfaces:

* `Cl11PolarizedBasis`: the circular `u+`/`u-` light-cone channels;
* `ChiralOperatorConeClosure`: those channels lie in the chiral operator cone
  when the split grading is the property spectral grading;
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
/-- The `u+` light-cone channel lies in the property chiral cone. -/
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
/-- The `u-` light-cone channel lies in the property chiral cone. -/
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

/-!
# InfoGeometry.Canonical.SouriauConformalKKTContext

This file has been fully mathematically flattened, and all wrapper structures
and trivial `And`-packaging theorems have been removed according to Mathlib policy.
-/

open InfoGeometry.Canonical.YangMillsContinuum
open ConformalGibbsSouriauOperatorContext

local notation "cl11" => doubledSpaceCl11Action (E := H)

/-- Weyl-gauged conformal geometric temperature. -/
@[rep_depth transport]
noncomputable def weylTemperature
    (C : ConformalGibbsSouriauOperatorContext (α := α) (H := H))
    (weylGauge : WeylGaugeField EndH₂ EndH₂) : EndH₂ :=
  weylGauge.gaugeOf C.conformalGeometricTemperature

-- theorem-class: bridge
/-- The property conformal dilation remains in the KKT grade-zero lane. -/
@[rep_depth transport]
theorem dilation_isGZero
    (C : ConformalGibbsSouriauOperatorContext (α := α) (H := H)) :
    IsGZero cl11 C.DGenerator := by
  simpa [ConformalGibbsSouriauOperatorContext.DGenerator] using
    C.base.conformalD_isGZero

-- theorem-class: bridge
/-- The property chiral grading remains in the KKT grade-zero lane. -/
@[rep_depth transport]
theorem chiralGrading_isGZero
    (C : ConformalGibbsSouriauOperatorContext (α := α) (H := H)) :
    IsGZero cl11
      (InfoGeometry.Canonical.ChiralCartanCore.chiralGrading
        C.base.CCI.toConformalInference) :=
  C.base.chiralGrading_isGZero

/-- Circularly polarized `u+`/`u-` commutator attached to the context channels. -/
@[rep_depth transport]
noncomputable def circularPolarizedCommutator (X Y : EndH₂) : EndH₂ :=
  KKTCore.commutator (uPlus cl11 X) (uMinus cl11 Y)

-- theorem-class: bridge
/-- Circular polarization closes in the KKT grade-zero operator lane. -/
@[rep_depth transport]
theorem circularPolarizedCommutator_isGZero (X Y : EndH₂) :
    IsGZero cl11 (circularPolarizedCommutator X Y) := by
  simpa [circularPolarizedCommutator] using
    KKTCore.commutator_uPlus_uMinus_isGZero (X := cl11) X Y

/-- Symmetric Jordan product of the conformal temperature and its Weyl-gauged copy. -/
@[rep_depth transport]
noncomputable def jordanProductTemperatureWeyl
    (C : ConformalGibbsSouriauOperatorContext (α := α) (H := H))
    (weylGauge : WeylGaugeField EndH₂ EndH₂) : EndH₂ :=
  InfoGeometry.Canonical.SuperJordanLie.jordanProduct (E := H)
    C.conformalGeometricTemperature (weylTemperature C weylGauge)

/-- Antisymmetric Lie product of the conformal temperature and its Weyl-gauged copy. -/
@[rep_depth transport]
noncomputable def lieProductTemperatureWeyl
    (C : ConformalGibbsSouriauOperatorContext (α := α) (H := H))
    (weylGauge : WeylGaugeField EndH₂ EndH₂) : EndH₂ :=
  InfoGeometry.Canonical.SuperJordanLie.lieProduct (E := H)
    C.conformalGeometricTemperature (weylTemperature C weylGauge)

-- theorem-class: bridge
/--
The Fock commutator of the conformal temperature with its Weyl-gauged copy is
exactly twice the operatorial Lie product.
-/
@[rep_depth transport]
theorem fockCommutator_temperature_weyl_eq_two_smul_lieProduct
    (C : ConformalGibbsSouriauOperatorContext (α := α) (H := H))
    (weylGauge : WeylGaugeField EndH₂ EndH₂) :
    InfoGeometry.Canonical.BogoliubovFockSuper.fockCommutator (E := H)
      C.conformalGeometricTemperature (weylTemperature C weylGauge) =
        (2 : ℝ) • lieProductTemperatureWeyl C weylGauge := by
  simpa [lieProductTemperatureWeyl] using
    (InfoGeometry.Canonical.SuperJordanLie.fockCommutator_eq_two_smul_lieProduct
      (E := H) C.conformalGeometricTemperature (weylTemperature C weylGauge))

-- theorem-class: bridge
/--
The Fock anticommutator of the conformal temperature with its Weyl-gauged copy
is exactly twice the operatorial Jordan product.
-/
@[rep_depth transport]
theorem fockAnticommutator_temperature_weyl_eq_two_smul_jordanProduct
    (C : ConformalGibbsSouriauOperatorContext (α := α) (H := H))
    (weylGauge : WeylGaugeField EndH₂ EndH₂) :
    InfoGeometry.Canonical.BogoliubovFockSuper.fockAnticommutator (E := H)
      C.conformalGeometricTemperature (weylTemperature C weylGauge) =
        (2 : ℝ) • jordanProductTemperatureWeyl C weylGauge := by
  simpa [jordanProductTemperatureWeyl] using
    (InfoGeometry.Canonical.SuperJordanLie.fockAnticommutator_eq_two_smul_jordanProduct
      (E := H) C.conformalGeometricTemperature (weylTemperature C weylGauge))

-- theorem-class: bridge
/-- The Onsager/Hessian response symmetry survives on the selected channels. -/
@[rep_depth transport]
theorem operatorConformalResponse_XY_swap
    (C : ConformalGibbsSouriauOperatorContext (α := α) (H := H))
    (X Y : EndH₂) :
    C.operatorConformalResponse X Y =
      C.operatorConformalResponse Y X :=
  C.operatorConformalResponse_swap X Y

/--
Krein-rooted KMS-like state condition for the operatorial conformal generator.

This is a noncommutative readout identity on the doubled Krein carrier, not a
finite diagonal probability identity.
-/
@[rep_depth transport]
noncomputable def SatisfiesKMSLike
    (C : ConformalGibbsSouriauOperatorContext (α := α) (H := H))
    (β : ℝ) : Prop :=
  InfoGeometry.Krein.satisfies_kms_like
    C.conformalGeometricTemperature C.readout β

/-- Compatibility alias for the KMS-like conformal operator-state condition. -/
@[rep_depth transport]
noncomputable def SatisfiesKMS
    (C : ConformalGibbsSouriauOperatorContext (α := α) (H := H))
    (β : ℝ) : Prop :=
  InfoGeometry.Krein.satisfies_kms
    C.conformalGeometricTemperature C.readout β

-- theorem-class: bridge
/--
At zero modular time, the KMS condition forces cyclic readout symmetry for
operator products.
-/
@[rep_depth transport]
theorem kms_zero_implies_operatorReadout_commutation
    (C : ConformalGibbsSouriauOperatorContext (α := α) (H := H))
    (hKMS : SatisfiesKMS C 0) (A B : EndH₂) :
    C.readout (A * B) = C.readout (B * A) := by
  exact
    InfoGeometry.Krein.kms_zero_implies_commutation
      (E := H) C.conformalGeometricTemperature C.readout hKMS A B

/-- Diagonal Fisher/Onsager production along the selected operator channel. -/
@[rep_depth transport]
noncomputable def fisherOnsagerProduction
    (C : ConformalGibbsSouriauOperatorContext (α := α) (H := H))
    (X : EndH₂) : ℝ :=
  C.operatorConformalResponse X X

-- theorem-class: bridge
/-- Diagonal response is invariant under channel swap by Onsager symmetry. -/
@[rep_depth transport]
theorem fisherOnsagerProduction_swap
    (C : ConformalGibbsSouriauOperatorContext (α := α) (H := H))
    (X : EndH₂) :
    C.operatorConformalResponse X X =
      C.operatorConformalResponse X X := by
  exact C.operatorConformalResponse_swap X X

end InfoGeometry.Canonical.SouriauConformalKKT
