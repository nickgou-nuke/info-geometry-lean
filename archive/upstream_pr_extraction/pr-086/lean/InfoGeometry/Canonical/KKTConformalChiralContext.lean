import InfoGeometry.Canonical.KKTCore
import InfoGeometry.Canonical.KKTClosureSymmetry
import InfoGeometry.Canonical.ConformalAlgebra
import InfoGeometry.Canonical.ChiralOperatorConeClosure
import InfoGeometry.Canonical.PhaseSpaceConformalKKTBridge
import InfoGeometry.Canonical.AssociativeSuperBracket
import InfoGeometry.Meta.Architecture

set_option linter.unusedSectionVars false

/-!
# InfoGeometry.Canonical.KKTConformalChiralContext

Operatorial context bridge for the KKT, conformal/TKK, and chiral-cone
closure surfaces.

This file deliberately stays on the property operator/Krein lane.  It does
not identify these closure theorems with finite block matrices or finite
character shadows.  It records the explicit context in which the already
proved owner theorems can be used together.
-/

open scoped InnerProductSpace

namespace InfoGeometry.Canonical.KKTConformalChiralContext

open InfoGeometry.Canonical
open InfoGeometry.Canonical.KKTCore
open InfoGeometry.Canonical.KKTClosure
open InfoGeometry.Canonical.ConformalAlgebra
open InfoGeometry.Canonical.ConformalAlgebra.ConformalBeliefAlgebra
open InfoGeometry.Canonical.ConformalUnification
open InfoGeometry.Canonical.ChiralOperatorConeClosure
open InfoGeometry.Canonical.PhaseSpaceConformalKKTBridge
open InfoGeometry.Canonical.DrazinSupercharge
open InfoGeometry.Canonical.AssociativeSuperBracket
open InfoGeometry.Quantum

section OperatorContext

variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [FiniteDimensional ℝ E]

local notation "EndH" => E →L[ℝ] E

/--
Certified operator context joining:

* a conformal/KKT property inverse-kernel carrier,
* an explicit split-`Cl(1,1)` grading action with the required KKT wing
  hypotheses,
* and a conformal belief algebra carrying the Cartan closure relations.

The weight/master conformal relations are hypotheses of the context, not
proved here from unrelated data.
-/
@[rep_depth krein]
structure OperatorContext where
  CCI : CertifiedConformalInference E
  X : RealSplitCl11Action E
  hA : IsGOne X CCI.A
  hAMP : IsGNegOne X CCI.A_MP
  CBA : ConformalBeliefAlgebra E
  eta : ℝ
  pWeight : CBA.SatisfiesPWeight
  kWeight : CBA.SatisfiesKWeight
  masterRelation : CBA.SatisfiesMasterRelation eta

namespace OperatorContext

variable (C : OperatorContext (E := E))

/-- The property inverse-kernel carrier exposed by the conformal context. -/
@[rep_depth krein]
abbrev CIK : CertifiedInverseKernel E :=
  C.CCI.toCertifiedInverseKernel

/-! ## KKT closure -/

/-- The property Drazin supercharge satisfies the KKT odd-odd closure. -/
@[rep_depth krein]
theorem anticommutator_QD_QD_eq_two_smul_HD :
    DrazinSupercharge.anticommutator (QD C.CIK) (QD C.CIK) =
      (2 : ℝ) • HD C.CIK :=
  KKTClosure.anticommutator_QD_QD_eq_two_smul_HD C.CIK

/-- The polarized `u₊/u₋` commutator closes in the grade-zero lane. -/
@[rep_depth krein]
theorem commutator_uPlus_uMinus_isGZero
    (A B : EndH) :
    IsGZero C.X (KKTCore.commutator (uPlus C.X A) (uMinus C.X B)) :=
  KKTCore.commutator_uPlus_uMinus_isGZero C.X A B

/-- Unit conjugations preserving the KKT packet form the existing subgroup. -/
@[rep_depth krein]
def kktClosureSymmetrySubgroup : Subgroup EndHˣ :=
  KKTClosure.kktClosureSymmetrySubgroup C.CIK

/--
KKT/TKK structure group on this operatorial surface.

This is not a new group: it is the existing repo-native subgroup of units
preserving the property KKT generator packet, exposed under the
structure-group name for the conformal/Jordan-Lie lift.
-/
@[rep_depth krein]
def kktTkkStructureGroup : Subgroup EndHˣ :=
  C.kktClosureSymmetrySubgroup

/-- The spectral Cartan grading is an involution. -/
@[rep_depth krein]
theorem spectralGrading_involutive :
    C.CIK.GammaS * C.CIK.GammaS = (1 : EndH) :=
  C.CIK.GammaS_sq_eq_one

/-- The spectral Cartan involution squares to the identity. -/
@[rep_depth krein]
theorem spectralCartanInvolution_involutive
    (A : EndH) :
    C.CIK.thetaS (C.CIK.thetaS A) = A :=
  C.CIK.thetaS_involutive A

/-! ## Conformal/TKK closure -/

/-- The context carries the conformal translation weight relation. -/
@[rep_depth krein]
theorem satisfiesPWeight : C.CBA.SatisfiesPWeight :=
  C.pWeight

/-- The context carries the conformal special-conformal weight relation. -/
@[rep_depth krein]
theorem satisfiesKWeight : C.CBA.SatisfiesKWeight :=
  C.kWeight

/-- The context carries the master conformal relation for its selected `η`. -/
@[rep_depth krein]
theorem satisfiesMasterRelation :
    C.CBA.SatisfiesMasterRelation C.eta :=
  C.masterRelation

/-- Cartan bracket law `[𝔨, 𝔨] ⊆ 𝔨` on the conformal belief algebra. -/
@[rep_depth krein]
theorem commutator_volumePreserving_volumePreserving
    {A B : EndH}
    (hA : C.CBA.IsVolumePreservingPart A)
    (hB : C.CBA.IsVolumePreservingPart B) :
    C.CBA.IsVolumePreservingPart (ConformalBeliefAlgebra.commutator A B) :=
  ConformalBeliefAlgebra.commutator_volumePreserving_volumePreserving
    (CBA := C.CBA) A B hA hB

/-- Cartan bracket law `[𝔨, 𝔭] ⊆ 𝔭` on the conformal belief algebra. -/
@[rep_depth krein]
theorem commutator_volumePreserving_weylDilation
    {A B : EndH}
    (hA : C.CBA.IsVolumePreservingPart A)
    (hB : C.CBA.IsWeylDilationPart B) :
    C.CBA.IsWeylDilationPart (ConformalBeliefAlgebra.commutator A B) :=
  ConformalBeliefAlgebra.commutator_volumePreserving_weylDilation
    (CBA := C.CBA) A B hA hB

/-- Cartan bracket law `[𝔭, 𝔭] ⊆ 𝔨` on the conformal belief algebra. -/
@[rep_depth krein]
theorem commutator_weylDilation_weylDilation
    {A B : EndH}
    (hA : C.CBA.IsWeylDilationPart A)
    (hB : C.CBA.IsWeylDilationPart B) :
    C.CBA.IsVolumePreservingPart (ConformalBeliefAlgebra.commutator A B) :=
  ConformalBeliefAlgebra.commutator_weylDilation_weylDilation
    (CBA := C.CBA) A B hA hB

/-! ## Certified conformal/KKT bridge -/

/-- The conformal dilation generator is the property inverse-kernel dilation gap. -/
@[rep_depth krein]
theorem conformalD_eq_dilationGap :
    C.CCI.toConformalInference.D = C.CIK.dilationGap :=
  CertifiedConformalInference.D_eq_dilationGap C.CCI

/-- Under the explicit KKT wing hypotheses, the conformal dilation is grade zero. -/
@[rep_depth krein]
theorem conformalD_isGZero :
    IsGZero C.X C.CCI.toConformalInference.D :=
  CertifiedConformalInference.D_isGZero C.X C.CCI C.hA C.hAMP

/-! ## Chiral cone closure -/

/-- The chiral cone is characterized by anticommutation with `Γ_S`. -/
@[rep_depth krein]
theorem isInChiralOperatorCone_iff_anticommute_GammaS
    {A : EndH} :
    IsInChiralOperatorCone C.CIK A ↔ A * C.CIK.GammaS = -(C.CIK.GammaS * A) :=
  ChiralOperatorConeClosure.isInChiralOperatorCone_iff_anticommute_GammaS
    (CIK := C.CIK)

/-- The chiral cone is stable under spectral-adjoint flow by compact generators. -/
@[rep_depth krein]
theorem spectralAdjointFlow_mem_chiralOperatorCone
    {A B : EndH}
    (hA : C.CIK.IsSpectralCompact A)
    (hB : IsInChiralOperatorCone C.CIK B)
    (t : ℝ) :
    IsInChiralOperatorCone C.CIK (C.CIK.spectralAdjointFlow A t B) :=
  ChiralOperatorConeClosure.spectralAdjointFlow_mem_chiralOperatorCone
    (CIK := C.CIK) hA hB t

/-- The compact/chiral spectral commutator remains in the chiral cone. -/
@[rep_depth krein]
theorem spectralCommutator_compact_mem_chiralOperatorCone
    {A B : EndH}
    (hA : C.CIK.IsSpectralCompact A)
    (hB : IsInChiralOperatorCone C.CIK B) :
    IsInChiralOperatorCone C.CIK (CertifiedInverseKernel.spectralCommutator A B) :=
  ChiralOperatorConeClosure.spectralCommutator_compact_mem_chiralOperatorCone
    (CIK := C.CIK) hA hB

/-- The property Drazin supercharge is enrolled in the chiral operator cone. -/
@[rep_depth krein]
theorem supercharge_mem_chiralOperatorCone :
    IsInChiralOperatorCone C.CIK
      (DrazinSupercharge.CertifiedInverseKernel.supercharge C.CIK) :=
  ChiralOperatorConeClosure.supercharge_mem_chiralOperatorCone C.CIK

/-! ## Supergraded Jordan-Lie lift -/

/-- Symmetric Jordan product on the operator algebra. -/
@[rep_depth krein]
noncomputable def jordanProduct (A B : EndH) : EndH :=
  (1 / 2 : ℝ) • (A * B + B * A)

/-- Antisymmetric Lie product on the operator algebra. -/
@[rep_depth krein]
noncomputable def lieProduct (A B : EndH) : EndH :=
  (1 / 2 : ℝ) • (A * B - B * A)

/-- Spectral compactness is closed under real scalar multiplication. -/
@[rep_depth krein]
theorem smul_mem_spectralCompact
    (r : ℝ)
    {A : EndH}
    (hA : C.CIK.IsSpectralCompact A) :
    C.CIK.IsSpectralCompact (r • A) := by
  rw [CertifiedInverseKernel.isSpectralCompact_iff_commute_GammaS] at hA ⊢
  calc
    (r • A) * C.CIK.GammaS = r • (A * C.CIK.GammaS) := by
      simp
    _ = r • (C.CIK.GammaS * A) := by rw [hA]
    _ = C.CIK.GammaS * (r • A) := by
      simp

/--
Odd/chiral times odd/chiral closes into the even/spectral-compact lane through
the Jordan product.
-/
@[rep_depth krein]
theorem jordanProduct_chiral_chiral_mem_spectralCompact
    {A B : EndH}
    (hA : IsInChiralOperatorCone C.CIK A)
    (hB : IsInChiralOperatorCone C.CIK B) :
    C.CIK.IsSpectralCompact (jordanProduct A B) := by
  have hAnti :
      C.CIK.IsSpectralCompact (DrazinSupercharge.anticommutator A B) :=
    ChiralOperatorConeClosure.anticommutator_mem_spectralCompact_of_chiralOperatorCone
      (CIK := C.CIK) hA hB
  unfold jordanProduct
  exact C.smul_mem_spectralCompact (1 / 2 : ℝ) hAnti

/--
Odd/chiral times odd/chiral closes into the even/spectral-compact lane through
the Lie product.
-/
@[rep_depth krein]
theorem lieProduct_chiral_chiral_mem_spectralCompact
    {A B : EndH}
    (hA : IsInChiralOperatorCone C.CIK A)
    (hB : IsInChiralOperatorCone C.CIK B) :
    C.CIK.IsSpectralCompact (lieProduct A B) := by
  have hLie :
      C.CIK.IsSpectralCompact (CertifiedInverseKernel.spectralCommutator A B) :=
    ChiralOperatorConeClosure.spectralCommutator_chiral_chiral_mem_spectralCompact
      (CIK := C.CIK) hA hB
  unfold lieProduct
  exact C.smul_mem_spectralCompact (1 / 2 : ℝ) hLie

/--
Supergraded odd-odd bracket closure: the associative superbracket of two
chiral operators is spectrally compact.
-/
@[rep_depth krein]
theorem superBracket_odd_odd_chiral_mem_spectralCompact
    {A B : EndH}
    (hA : IsInChiralOperatorCone C.CIK A)
    (hB : IsInChiralOperatorCone C.CIK B) :
    C.CIK.IsSpectralCompact
      (AssociativeSuperBracket.superBracket
        SuperAnomaly.SuperParity.odd SuperAnomaly.SuperParity.odd A B) := by
  simpa [AssociativeSuperBracket.superBracket, SuperAnomaly.paritySign,
    DrazinSupercharge.anticommutator, sub_eq_add_neg] using
    (ChiralOperatorConeClosure.anticommutator_mem_spectralCompact_of_chiralOperatorCone
      (CIK := C.CIK) hA hB)

end OperatorContext

end OperatorContext

end InfoGeometry.Canonical.KKTConformalChiralContext
