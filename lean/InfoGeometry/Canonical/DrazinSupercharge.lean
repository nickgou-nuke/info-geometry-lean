import InfoGeometry.Canonical.CertifiedInverseKernel
import InfoGeometry.Canonical.InverseKernelAlgebra
import InfoGeometry.Canonical.InverseKernelCartanCore
import InfoGeometry.Canonical.SuperchargeCentralChargeClosure
import InfoGeometry.Meta.Architecture

open scoped InnerProductSpace

namespace InfoGeometry.Canonical.DrazinSupercharge

open InfoGeometry.Canonical

variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "EndH" => E →L[ℝ] E

noncomputable local instance : NormedRing EndH := inferInstance
noncomputable local instance : NormedAlgebra ℝ EndH := inferInstance
noncomputable local instance : NormedAlgebra ℚ EndH :=
  NormedAlgebra.restrictScalars ℚ ℝ EndH
local instance : IsTopologicalRing EndH := inferInstance
local instance : SMulCommClass ℝ EndH EndH := inferInstance
local instance : IsScalarTower ℝ EndH EndH := inferInstance

/-- Repo-owned commutator. -/
@[rep_depth operator]
def commutator (X Y : EndH) : EndH := X * Y - Y * X

/-- Repo-owned anticommutator. -/
@[rep_depth operator]
def anticommutator (X Y : EndH) : EndH := X * Y + Y * X

/--
Scalar-operator predicate on the doubled real carrier lane.

`Z` is scalar when it is an identity multiple.
-/
@[rep_depth operator]
def IsScalarOperator (Z : EndH) : Prop :=
  ∃ c : ℝ, Z = c • (1 : EndH)

/-- Krein-depth bridge wrapper for the commutator surface. -/
@[rep_depth krein]
def commutatorK (X Y : EndH) : EndH := commutator X Y

/-- Krein-depth bridge wrapper for the anticommutator surface. -/
@[rep_depth krein]
def anticommutatorK (X Y : EndH) : EndH := anticommutator X Y

/-- Krein-depth bridge wrapper for scalar-operator classification. -/
@[rep_depth krein]
def IsScalarOperatorK (Z : EndH) : Prop := IsScalarOperator Z

namespace CertifiedInverseKernel

variable (CIK : CertifiedInverseKernel E)

/--
The canonical odd generator already latent in the certified inverse kernel:
`Q := χ_R - χ_L`.
-/
@[rep_depth operator]
def supercharge : EndH :=
  CIK.rightChiralAnomaly - CIK.chiralAnomaly

/-- Krein-depth bridge alias for the canonical odd generator `Q`. -/
@[rep_depth krein]
def superchargeK : EndH := supercharge CIK

/--
Equivalent commutator presentation:
`Q = 2 • [P_D, G]`.
-/
theorem supercharge_eq_two_smul_commutator_spectralProjector_dilationGap :
    supercharge CIK = (2 : ℝ) • commutator CIK.spectralProjector CIK.dilationGap := by
  have h :=
    congrArg (fun Z : EndH => (2 : ℝ) • Z)
      CIK.spectralProjector_commutator_dilationGap_eq_half_sub_anomalies
  simpa [supercharge, commutator, smul_smul] using h.symm

/--
Equivalent geometric-Cartan commutator presentation:
`Q = [P_D, Γ_G]`.
-/
theorem supercharge_eq_commutator_spectralProjector_GammaG :
    supercharge CIK = commutator CIK.spectralProjector CIK.GammaG := by
  simpa [supercharge, commutator] using
    (CIK.spectralProjector_commutator_GammaG_eq_sub_anomalies).symm

/--
Geometric-range mismatch relative to a chosen sign/chiral axis `sigma`.

This packages the obstruction `Xi := Γ_G - sigma`.
-/
@[rep_depth operator]
noncomputable def geometricMismatch (sigma : EndH) : EndH :=
  CIK.GammaG - sigma

/-- Geometric Cartan generator decomposition through a chosen axis `sigma`. -/
theorem GammaG_eq_sigma_add_geometricMismatch (sigma : EndH) :
    CIK.GammaG = sigma + geometricMismatch CIK sigma := by
  unfold geometricMismatch
  abel

/--
Commutator split through a chosen axis `sigma`:
`[P_D, Γ_G] = [P_D, sigma] + [P_D, Xi]`, where `Xi := Γ_G - sigma`.
-/
theorem commutator_spectralProjector_GammaG_eq_commutator_spectralProjector_sigma_add_commutator_spectralProjector_geometricMismatch
    (sigma : EndH) :
    commutator CIK.spectralProjector CIK.GammaG
      =
    commutator CIK.spectralProjector sigma
      +
    commutator CIK.spectralProjector (geometricMismatch CIK sigma) := by
  rw [GammaG_eq_sigma_add_geometricMismatch (CIK := CIK) sigma]
  unfold commutator
  noncomm_ring

/--
Supercharge split through a chosen axis `sigma`:
`Q = [P_D, sigma] + [P_D, Xi]`, where `Xi := Γ_G - sigma`.
-/
theorem supercharge_eq_commutator_spectralProjector_sigma_add_commutator_spectralProjector_geometricMismatch
    (sigma : EndH) :
    supercharge CIK
      =
    commutator CIK.spectralProjector sigma
      +
    commutator CIK.spectralProjector (geometricMismatch CIK sigma) := by
  calc
    supercharge CIK = commutator CIK.spectralProjector CIK.GammaG :=
      supercharge_eq_commutator_spectralProjector_GammaG (CIK := CIK)
    _ =
      commutator CIK.spectralProjector sigma
        +
      commutator CIK.spectralProjector (geometricMismatch CIK sigma) :=
      commutator_spectralProjector_GammaG_eq_commutator_spectralProjector_sigma_add_commutator_spectralProjector_geometricMismatch
        (CIK := CIK) sigma

/--
Calibrated specialization:
if the geometric mismatch vanishes (`Xi = 0`), then
`Q = [P_D, sigma]`.
-/
theorem supercharge_eq_commutator_spectralProjector_sigma_of_geometricMismatch_eq_zero
    (sigma : EndH)
    (hMismatch : geometricMismatch CIK sigma = 0) :
    supercharge CIK = commutator CIK.spectralProjector sigma := by
  calc
    supercharge CIK
        =
      commutator CIK.spectralProjector sigma
        +
      commutator CIK.spectralProjector (geometricMismatch CIK sigma) :=
      supercharge_eq_commutator_spectralProjector_sigma_add_commutator_spectralProjector_geometricMismatch
        (CIK := CIK) sigma
    _ = commutator CIK.spectralProjector sigma + commutator CIK.spectralProjector 0 := by
          simp [hMismatch]
    _ = commutator CIK.spectralProjector sigma + 0 := by
          simp [commutator]
    _ = commutator CIK.spectralProjector sigma := by simp

/-- Krein-depth bridge form of `Q = 2 • [P_D, G]`. -/
@[rep_depth krein]
theorem supercharge_eq_two_smul_commutatorK_spectralProjector_dilationGap :
    supercharge CIK = (2 : ℝ) • commutatorK CIK.spectralProjector CIK.dilationGap := by
  simpa [commutatorK] using
    supercharge_eq_two_smul_commutator_spectralProjector_dilationGap (CIK := CIK)

/--
The supercharge is odd with respect to the spectral grading:
`{Γ_S, Q} = 0`.
-/
theorem supercharge_is_odd :
    anticommutator CIK.toInformationCartanTriple.GammaS (supercharge CIK) = 0 := by
  let ΓS := CIK.toInformationCartanTriple.GammaS
  have hR :
      CIK.rightChiralAnomaly * ΓS = -(ΓS * CIK.rightChiralAnomaly) := by
    simpa [ΓS] using CIK.rightChiralAnomaly_anticommutes_GammaS
  have hL :
      CIK.chiralAnomaly * ΓS = -(ΓS * CIK.chiralAnomaly) := by
    simpa [ΓS] using CIK.chiralAnomaly_anticommutes_GammaS
  unfold anticommutator supercharge
  calc
    CIK.toInformationCartanTriple.GammaS *
          (CIK.rightChiralAnomaly - CIK.chiralAnomaly)
        +
        (CIK.rightChiralAnomaly - CIK.chiralAnomaly) *
          CIK.toInformationCartanTriple.GammaS
      =
        (CIK.toInformationCartanTriple.GammaS * CIK.rightChiralAnomaly
            + CIK.rightChiralAnomaly * CIK.toInformationCartanTriple.GammaS)
          -
        (CIK.toInformationCartanTriple.GammaS * CIK.chiralAnomaly
            + CIK.chiralAnomaly * CIK.toInformationCartanTriple.GammaS) := by
          noncomm_ring
    _ = 0 := by
      rw [hR, hL]
      noncomm_ring

/-- Krein-depth bridge form of supercharge oddness. -/
@[rep_depth krein]
theorem supercharge_is_oddK :
    anticommutatorK CIK.toInformationCartanTriple.GammaS (supercharge CIK) = 0 := by
  simpa [anticommutatorK] using supercharge_is_odd (CIK := CIK)

/--
Derived sector statement: the supercharge lies in the spectral noncompact (`𝔭`) sector.
-/
theorem supercharge_isSpectralNonCompact :
    let T := CIK.toInformationCartanTriple
    T.IsSpectralNonCompact (supercharge CIK) := by
  let T := CIK.toInformationCartanTriple
  rw [CartanDecomposition.InformationCartanTriple.isSpectralNonCompact_iff_anticommute
        T CIK.hDrazin]
  have hOdd :
      anticommutator T.GammaS (supercharge CIK) = 0 := by
    simpa [T] using supercharge_is_odd CIK
  unfold anticommutator at hOdd
  have hOdd' :
      (supercharge CIK) * T.GammaS + T.GammaS * (supercharge CIK) = 0 := by
    simpa [add_comm] using hOdd
  exact eq_neg_of_add_eq_zero_left hOdd'

/-- Kinetic even operator generated by the odd supercharge. -/
@[rep_depth operator]
def superHamiltonian : EndH :=
  supercharge CIK * supercharge CIK

/-- Krein-depth bridge wrapper for the projected even generator `Q²`. -/
@[rep_depth krein]
def superHamiltonianK : EndH := superHamiltonian CIK

/--
Regular-support compressed superHamiltonian on the Drazin lane:
`K_reg := P_D * Q² * P_D`.

This is the repo-native projector-controlled realization of the support
restriction used before logarithmic-generator readouts.
-/
@[rep_depth operator]
def regularRestrictedSuperHamiltonian : EndH :=
  CIK.spectralProjector * superHamiltonian CIK * CIK.spectralProjector

/-- Krein-depth bridge wrapper for the regular-support compressed Hamiltonian. -/
@[rep_depth krein]
def regularRestrictedSuperHamiltonianK : EndH :=
  regularRestrictedSuperHamiltonian CIK

/--
Left support invariance on the regular Drazin projector lane:
`P_D * K_reg = K_reg`.
-/
@[rep_depth operator]
theorem spectralProjector_mul_regularRestrictedSuperHamiltonian :
    CIK.spectralProjector * regularRestrictedSuperHamiltonian CIK
      = regularRestrictedSuperHamiltonian CIK := by
  unfold regularRestrictedSuperHamiltonian
  calc
    CIK.spectralProjector
          * (CIK.spectralProjector * superHamiltonian CIK * CIK.spectralProjector)
        = (CIK.spectralProjector * CIK.spectralProjector) * superHamiltonian CIK
            * CIK.spectralProjector := by
              simp [mul_assoc]
    _ = CIK.spectralProjector * superHamiltonian CIK * CIK.spectralProjector := by
          simpa [mul_assoc, CIK.spectralProjector_idempotent]
    _ = regularRestrictedSuperHamiltonian CIK := by rfl

/--
Right support invariance on the regular Drazin projector lane:
`K_reg * P_D = K_reg`.
-/
@[rep_depth operator]
theorem regularRestrictedSuperHamiltonian_mul_spectralProjector :
    regularRestrictedSuperHamiltonian CIK * CIK.spectralProjector
      = regularRestrictedSuperHamiltonian CIK := by
  unfold regularRestrictedSuperHamiltonian
  calc
    (CIK.spectralProjector * superHamiltonian CIK * CIK.spectralProjector)
          * CIK.spectralProjector
        = CIK.spectralProjector * superHamiltonian CIK
            * (CIK.spectralProjector * CIK.spectralProjector) := by
              simp [mul_assoc]
    _ = CIK.spectralProjector * superHamiltonian CIK * CIK.spectralProjector := by
          simpa [mul_assoc, CIK.spectralProjector_idempotent]
    _ = regularRestrictedSuperHamiltonian CIK := by rfl

/--
Left defect annihilation of the regular-support compressed Hamiltonian:
`P₀ * K_reg = 0`.
-/
@[rep_depth operator]
theorem spectralComplementaryProjector_mul_regularRestrictedSuperHamiltonian_eq_zero :
    CIK.spectralComplementaryProjector * regularRestrictedSuperHamiltonian CIK = 0 := by
  unfold regularRestrictedSuperHamiltonian
  calc
    CIK.spectralComplementaryProjector
          * (CIK.spectralProjector * superHamiltonian CIK * CIK.spectralProjector)
        = (CIK.spectralComplementaryProjector * CIK.spectralProjector)
            * superHamiltonian CIK * CIK.spectralProjector := by
              simp [mul_assoc]
    _ = 0 := by
          simp [CIK.spectralComplementaryProjector_mul_spectralProjector, mul_assoc]

/--
Right defect annihilation of the regular-support compressed Hamiltonian:
`K_reg * P₀ = 0`.
-/
@[rep_depth operator]
theorem regularRestrictedSuperHamiltonian_mul_spectralComplementaryProjector_eq_zero :
    regularRestrictedSuperHamiltonian CIK * CIK.spectralComplementaryProjector = 0 := by
  unfold regularRestrictedSuperHamiltonian
  calc
    (CIK.spectralProjector * superHamiltonian CIK * CIK.spectralProjector)
          * CIK.spectralComplementaryProjector
        = CIK.spectralProjector * superHamiltonian CIK
            * (CIK.spectralProjector * CIK.spectralComplementaryProjector) := by
              simp [mul_assoc]
    _ = 0 := by
          simp [CIK.spectralProjector_mul_spectralComplementaryProjector, mul_assoc]

/--
Defect-block compression vanishes for the regular-support compressed Hamiltonian:
`P₀ * K_reg * P₀ = 0`.
-/
@[rep_depth operator]
theorem defectCompression_regularRestrictedSuperHamiltonian_eq_zero :
    CIK.spectralComplementaryProjector
      * regularRestrictedSuperHamiltonian CIK
      * CIK.spectralComplementaryProjector = 0 := by
  rw [spectralComplementaryProjector_mul_regularRestrictedSuperHamiltonian_eq_zero (CIK := CIK)]
  simp

/--
Right-anticommutation form of the oddness law:
`Q * Γ_S = -(Γ_S * Q)`.
This is the algebraic input for the evenness of `Q²`.
-/
theorem supercharge_mul_GammaS_eq_neg :
    supercharge CIK * CIK.toInformationCartanTriple.GammaS =
      -(CIK.toInformationCartanTriple.GammaS * supercharge CIK) := by
  let T := CIK.toInformationCartanTriple
  have hQ : T.IsSpectralNonCompact (supercharge CIK) := by
    simpa [T] using supercharge_isSpectralNonCompact CIK
  exact
    (CartanDecomposition.InformationCartanTriple.isSpectralNonCompact_iff_anticommute
      T CIK.hDrazin).1 hQ

/--
The square of the odd supercharge commutes with the spectral grading:
`Q² * Γ_S = Γ_S * Q²`.
-/
theorem superHamiltonian_commutes_GammaS :
    superHamiltonian CIK * CIK.toInformationCartanTriple.GammaS =
      CIK.toInformationCartanTriple.GammaS * superHamiltonian CIK := by
  let T := CIK.toInformationCartanTriple
  have hAnti :
      supercharge CIK * T.GammaS = -(T.GammaS * supercharge CIK) := by
    simpa [T] using supercharge_mul_GammaS_eq_neg CIK
  unfold superHamiltonian
  calc
    (supercharge CIK * supercharge CIK) * T.GammaS
        = supercharge CIK * (supercharge CIK * T.GammaS) := by
            simp [mul_assoc]
    _ = supercharge CIK * (-(T.GammaS * supercharge CIK)) := by
          rw [hAnti]
    _ = -(supercharge CIK * (T.GammaS * supercharge CIK)) := by
          simp
    _ = -((supercharge CIK * T.GammaS) * supercharge CIK) := by
          simp [mul_assoc]
    _ = -((-(T.GammaS * supercharge CIK)) * supercharge CIK) := by
          rw [hAnti]
    _ = (T.GammaS * supercharge CIK) * supercharge CIK := by
          simp
    _ = T.GammaS * (supercharge CIK * supercharge CIK) := by
          simp [mul_assoc]

/--
The kinetic operator `Q²` lies in the spectral compact/even sector.
-/
theorem superHamiltonian_isSpectralCompact :
    let T := CIK.toInformationCartanTriple
    T.IsSpectralCompact (superHamiltonian CIK) := by
  let T := CIK.toInformationCartanTriple
  rw [CartanDecomposition.InformationCartanTriple.isSpectralCompact_iff_commute
        T CIK.hDrazin]
  simpa [T] using superHamiltonian_commutes_GammaS CIK

/--
Equivalently: the spectral Cartan involution fixes `Q²`.
-/
theorem thetaS_superHamiltonian :
    let T := CIK.toInformationCartanTriple
    T.thetaS (superHamiltonian CIK) = superHamiltonian CIK := by
  let T := CIK.toInformationCartanTriple
  show T.IsSpectralCompact (superHamiltonian CIK)
  simpa [T] using superHamiltonian_isSpectralCompact CIK

/--
The grading adjoint flow fixes the kinetic operator `Q²`.
This is the first flow-level consequence of evenness.
-/
theorem superHamiltonian_fixed_under_spectralGradingFlow
    (t : ℝ) :
    let T := CIK.toInformationCartanTriple
    T.spectralAdjointFlow T.GammaS t (superHamiltonian CIK) = superHamiltonian CIK := by
  let T := CIK.toInformationCartanTriple
  have hComm : Commute (superHamiltonian CIK) T.GammaS := by
    simpa [T] using superHamiltonian_commutes_GammaS CIK
  simpa [T] using
    T.spectralAdjointFlow_eq_self_of_commute_GammaS hComm t

/-- Krein-depth bridge: evenness of the projected generator. -/
@[rep_depth krein]
theorem superHamiltonianK_isSpectralCompact :
    let T := CIK.toInformationCartanTriple
    T.IsSpectralCompact (superHamiltonianK CIK) := by
  simpa [superHamiltonianK] using superHamiltonian_isSpectralCompact (CIK := CIK)

/-- Krein-depth bridge: grading-flow fixedness of the projected generator. -/
@[rep_depth krein]
theorem superHamiltonianK_fixed_under_spectralGradingFlow
    (t : ℝ) :
    let T := CIK.toInformationCartanTriple
    T.spectralAdjointFlow T.GammaS t (superHamiltonianK CIK) = superHamiltonianK CIK := by
  simpa [superHamiltonianK] using
    superHamiltonian_fixed_under_spectralGradingFlow (CIK := CIK) t

/--
The superHamiltonian commutes with the full grading flow.
-/
theorem superHamiltonian_commutes_spectralGradingFlow
    (t : ℝ) :
    let T := CIK.toInformationCartanTriple
    Commute (superHamiltonian CIK) (T.spectralGradingFlow t) := by
  let T := CIK.toInformationCartanTriple
  have hComm : Commute (superHamiltonian CIK) T.GammaS := by
    simpa [T] using superHamiltonian_commutes_GammaS CIK
  simpa [T] using
    T.commute_spectralGradingFlow_of_commute_GammaS hComm t

/--
Defect-support predicate on the Drazin singular block.

`Z` is defect-supported when its full action is carried by the complementary
spectral projector `Q₀ = 1 - P_D`.
-/
@[rep_depth operator]
def IsDefectSupported (Z : EndH) : Prop :=
  CIK.spectralComplementaryProjector * Z * CIK.spectralComplementaryProjector = Z

/-- Krein-depth bridge wrapper for defect support. -/
@[rep_depth krein]
def IsDefectSupportedK (Z : EndH) : Prop :=
  CIK.spectralComplementaryProjector * Z * CIK.spectralComplementaryProjector = Z

/--
Vanishing-defect-block predicate for a kinetic candidate.

`H` has no singular Drazin block when its `Q₀`-compressed component is zero.
-/
@[rep_depth operator]
def HasVanishingDefectBlock (H : EndH) : Prop :=
  CIK.spectralComplementaryProjector * H * CIK.spectralComplementaryProjector = 0

/-- Krein-depth bridge wrapper for vanishing defect block. -/
@[rep_depth krein]
def HasVanishingDefectBlockK (H : EndH) : Prop :=
  CIK.spectralComplementaryProjector * H * CIK.spectralComplementaryProjector = 0

/--
Internal centrality predicate for the Drazin spectral lane.

`Z` is central on this lane when it commutes with both the regular and defect
spectral projectors.
-/
@[rep_depth operator]
def IsDrazinSpectralCentral (Z : EndH) : Prop :=
  Commute Z CIK.spectralProjector
    ∧ Commute Z CIK.spectralComplementaryProjector

/-- Krein-depth bridge wrapper for Drazin spectral centrality. -/
@[rep_depth krein]
def IsDrazinSpectralCentralK (Z : EndH) : Prop :=
  Commute Z CIK.spectralProjector
    ∧ Commute Z CIK.spectralComplementaryProjector

/--
Centrality predicate for the full Drazin algebra lane.

This extends spectral-projector centrality by requiring commutation with the
spectral grading `Γ_S`.
-/
@[rep_depth operator]
def IsDrazinLaneCentral (Z : EndH) : Prop :=
  IsDrazinSpectralCentral CIK Z
    ∧ Commute Z CIK.toInformationCartanTriple.GammaS

/-- Krein-depth bridge wrapper for full Drazin-lane centrality. -/
@[rep_depth krein]
def IsDrazinLaneCentralK (Z : EndH) : Prop :=
  IsDrazinSpectralCentralK CIK Z
    ∧ Commute Z CIK.toInformationCartanTriple.GammaS

/--
Canonical defect-supported extraction from `Q²`.

This is the singular-block compression of the projected superHamiltonian.
-/
@[rep_depth operator]
def canonicalDefectCentral : EndH :=
  CIK.spectralComplementaryProjector * superHamiltonian CIK * CIK.spectralComplementaryProjector

/--
Canonical kinetic remainder after removing the defect-supported central channel.
-/
@[rep_depth operator]
def canonicalKineticPart : EndH :=
  superHamiltonian CIK - canonicalDefectCentral CIK

/-- Krein-depth bridge wrapper for the canonical defect-central extraction. -/
@[rep_depth krein]
def canonicalDefectCentralK : EndH := canonicalDefectCentral CIK

/-- Krein-depth bridge wrapper for the canonical kinetic remainder. -/
@[rep_depth krein]
def canonicalKineticPartK : EndH := canonicalKineticPart CIK

/-- The canonical defect-central part is supported on the defect block. -/
@[rep_depth operator]
theorem canonicalDefectCentral_isDefectSupported :
    IsDefectSupported CIK (canonicalDefectCentral CIK) := by
  set Q0 : EndH := CIK.spectralComplementaryProjector
  set SH : EndH := superHamiltonian CIK
  have hQ0 : Q0 * Q0 = Q0 := by
    simpa [Q0] using CIK.spectralComplementaryProjector_idempotent
  unfold IsDefectSupported canonicalDefectCentral
  change Q0 * (Q0 * SH * Q0) * Q0 = Q0 * SH * Q0
  calc
    Q0 * (Q0 * SH * Q0) * Q0 = ((Q0 * Q0) * SH) * (Q0 * Q0) := by
      simp [mul_assoc]
    _ = (Q0 * SH) * Q0 := by
      simpa [hQ0, mul_assoc]
    _ = Q0 * SH * Q0 := by
      simp [mul_assoc]

/-- Krein-depth bridge form of defect support for the canonical central extraction. -/
@[rep_depth krein]
theorem canonicalDefectCentralK_isDefectSupportedK :
    IsDefectSupportedK CIK (canonicalDefectCentralK CIK) := by
  simpa [canonicalDefectCentralK] using
    canonicalDefectCentral_isDefectSupported (CIK := CIK)

/--
Nontrivial defect projector criterion:
if `Q₀` is neither `0` nor `1`, it cannot be scalar.
-/
@[rep_depth operator]
theorem spectralComplementaryProjector_not_scalar_of_nontrivial
    (hQ0ne0 : CIK.spectralComplementaryProjector ≠ 0)
    (hQ0ne1 : CIK.spectralComplementaryProjector ≠ (1 : EndH)) :
    ¬ IsScalarOperator CIK.spectralComplementaryProjector := by
  intro hScalar
  rcases hScalar with ⟨c, hc⟩
  have hIdem : CIK.spectralComplementaryProjector * CIK.spectralComplementaryProjector
      = CIK.spectralComplementaryProjector :=
    CIK.spectralComplementaryProjector_idempotent
  have hScalarIdem :
      (c • (1 : EndH)) * (c • (1 : EndH)) = c • (1 : EndH) := by
    simpa [hc] using hIdem
  have hOneNe : (1 : EndH) ≠ 0 := by
    intro hOneZero
    apply hQ0ne0
    calc
      CIK.spectralComplementaryProjector
          = CIK.spectralComplementaryProjector * (1 : EndH) := by simp
      _ = CIK.spectralComplementaryProjector * 0 := by simpa [hOneZero]
      _ = 0 := by simp
  have hCoeffEq :
      (c * c : ℝ) • (1 : EndH) = c • (1 : EndH) := by
    simpa [smul_smul, mul_assoc] using hScalarIdem
  have hCoeff : c * c = c := by
    exact smul_left_injective ℝ hOneNe hCoeffEq
  have hmul : c * (c - 1) = 0 := by
    nlinarith [hCoeff]
  have hc01 : c = 0 ∨ c = 1 := by
    rcases mul_eq_zero.mp hmul with hc0 | hc1
    · exact Or.inl hc0
    · exact Or.inr (sub_eq_zero.mp hc1)
  cases hc01 with
  | inl hc0 =>
      apply hQ0ne0
      simpa [hc, hc0]
  | inr hc1 =>
      apply hQ0ne1
      simpa [hc, hc1]

/-- Krein-depth bridge form of non-scalarity for a nontrivial defect projector. -/
@[rep_depth krein]
theorem spectralComplementaryProjector_not_scalar_of_nontrivialK
    (hQ0ne0 : CIK.spectralComplementaryProjector ≠ 0)
    (hQ0ne1 : CIK.spectralComplementaryProjector ≠ (1 : EndH)) :
    ¬ IsScalarOperatorK CIK.spectralComplementaryProjector := by
  simpa [IsScalarOperatorK] using
    spectralComplementaryProjector_not_scalar_of_nontrivial
      (CIK := CIK) hQ0ne0 hQ0ne1

/-- The canonical kinetic remainder has vanishing defect block. -/
@[rep_depth operator]
theorem canonicalKineticPart_hasVanishingDefectBlock :
    HasVanishingDefectBlock CIK (canonicalKineticPart CIK) := by
  set Q0 : EndH := CIK.spectralComplementaryProjector
  set SH : EndH := superHamiltonian CIK
  have hQ0 : Q0 * Q0 = Q0 := by
    simpa [Q0] using CIK.spectralComplementaryProjector_idempotent
  unfold HasVanishingDefectBlock canonicalKineticPart canonicalDefectCentral
  change Q0 * (SH - Q0 * SH * Q0) * Q0 = 0
  have hcompress : Q0 * (Q0 * SH * Q0) * Q0 = Q0 * SH * Q0 := by
    calc
      Q0 * (Q0 * SH * Q0) * Q0 = ((Q0 * Q0) * SH) * (Q0 * Q0) := by
        simp [mul_assoc]
      _ = (Q0 * SH) * Q0 := by
        simpa [hQ0, mul_assoc]
      _ = Q0 * SH * Q0 := by
        simp [mul_assoc]
  calc
    Q0 * (SH - Q0 * SH * Q0) * Q0
        = Q0 * SH * Q0 - Q0 * (Q0 * SH * Q0) * Q0 := by
            simp [mul_sub, sub_mul, mul_assoc]
    _ = Q0 * SH * Q0 - Q0 * SH * Q0 := by
          simpa [hcompress]
    _ = 0 := by simp

/-- Krein-depth bridge form of defect-block vanishing for the canonical kinetic part. -/
@[rep_depth krein]
theorem canonicalKineticPartK_hasVanishingDefectBlockK :
    HasVanishingDefectBlockK CIK (canonicalKineticPartK CIK) := by
  simpa [canonicalKineticPartK] using
    canonicalKineticPart_hasVanishingDefectBlock (CIK := CIK)

/--
Defect support implies left compression by the complementary projector.
-/
@[rep_depth operator]
theorem spectralComplementaryProjector_mul_eq_of_isDefectSupported
    {Z : EndH}
    (hDefect : IsDefectSupported CIK Z) :
    CIK.spectralComplementaryProjector * Z = Z := by
  have hQ0 : CIK.spectralComplementaryProjector * CIK.spectralComplementaryProjector
      = CIK.spectralComplementaryProjector := CIK.spectralComplementaryProjector_idempotent
  unfold IsDefectSupported at hDefect
  calc
    CIK.spectralComplementaryProjector * Z
        = CIK.spectralComplementaryProjector
            * (CIK.spectralComplementaryProjector * Z * CIK.spectralComplementaryProjector) := by
              rw [hDefect]
    _ = (CIK.spectralComplementaryProjector * CIK.spectralComplementaryProjector) * Z
          * CIK.spectralComplementaryProjector := by
            simp [mul_assoc]
    _ = CIK.spectralComplementaryProjector * Z * CIK.spectralComplementaryProjector := by
          simpa [hQ0, mul_assoc]
    _ = Z := hDefect

/--
Defect support implies right compression by the complementary projector.
-/
@[rep_depth operator]
theorem mul_spectralComplementaryProjector_eq_of_isDefectSupported
    {Z : EndH}
    (hDefect : IsDefectSupported CIK Z) :
    Z * CIK.spectralComplementaryProjector = Z := by
  have hQ0 : CIK.spectralComplementaryProjector * CIK.spectralComplementaryProjector
      = CIK.spectralComplementaryProjector := CIK.spectralComplementaryProjector_idempotent
  unfold IsDefectSupported at hDefect
  calc
    Z * CIK.spectralComplementaryProjector
        = (CIK.spectralComplementaryProjector * Z * CIK.spectralComplementaryProjector)
            * CIK.spectralComplementaryProjector := by
              rw [hDefect]
    _ = CIK.spectralComplementaryProjector * Z
          * (CIK.spectralComplementaryProjector * CIK.spectralComplementaryProjector) := by
            simp [mul_assoc]
    _ = CIK.spectralComplementaryProjector * Z * CIK.spectralComplementaryProjector := by
          simpa [hQ0, mul_assoc]
    _ = Z := hDefect

/--
Defect support forces annihilation by the regular Drazin projector on the left.
-/
@[rep_depth operator]
theorem spectralProjector_mul_eq_zero_of_isDefectSupported
    {Z : EndH}
    (hDefect : IsDefectSupported CIK Z) :
    CIK.spectralProjector * Z = 0 := by
  unfold IsDefectSupported at hDefect
  calc
    CIK.spectralProjector * Z
        = CIK.spectralProjector
            * (CIK.spectralComplementaryProjector * Z * CIK.spectralComplementaryProjector) := by
              conv_lhs => rw [← hDefect]
    _ = ((CIK.spectralProjector * CIK.spectralComplementaryProjector) * Z)
          * CIK.spectralComplementaryProjector := by
            simp [mul_assoc]
    _ = 0 := by
          simp [CIK.spectralProjector_mul_spectralComplementaryProjector]

/--
Defect support forces annihilation by the regular Drazin projector on the right.
-/
@[rep_depth operator]
theorem mul_spectralProjector_eq_zero_of_isDefectSupported
    {Z : EndH}
    (hDefect : IsDefectSupported CIK Z) :
    Z * CIK.spectralProjector = 0 := by
  unfold IsDefectSupported at hDefect
  calc
    Z * CIK.spectralProjector
        = (CIK.spectralComplementaryProjector * Z * CIK.spectralComplementaryProjector)
            * CIK.spectralProjector := by
              conv_lhs => rw [← hDefect]
    _ = CIK.spectralComplementaryProjector
          * Z * (CIK.spectralComplementaryProjector * CIK.spectralProjector) := by
            simp [mul_assoc]
    _ = 0 := by
          simp [CIK.spectralComplementaryProjector_mul_spectralProjector]

/--
Any defect-supported operator is central on the internal Drazin spectral lane.
-/
@[rep_depth operator]
theorem isDrazinSpectralCentral_of_isDefectSupported
    {Z : EndH}
    (hDefect : IsDefectSupported CIK Z) :
    IsDrazinSpectralCentral CIK Z := by
  refine ⟨?_, ?_⟩
  ·
    have hLeft :
        CIK.spectralProjector * Z = 0 :=
      spectralProjector_mul_eq_zero_of_isDefectSupported (CIK := CIK) hDefect
    have hRight :
        Z * CIK.spectralProjector = 0 :=
      mul_spectralProjector_eq_zero_of_isDefectSupported (CIK := CIK) hDefect
    calc
      Z * CIK.spectralProjector = 0 := hRight
      _ = CIK.spectralProjector * Z := by simpa [hLeft]
  ·
    have hLeft :
        CIK.spectralComplementaryProjector * Z = Z :=
      spectralComplementaryProjector_mul_eq_of_isDefectSupported (CIK := CIK) hDefect
    have hRight :
        Z * CIK.spectralComplementaryProjector = Z :=
      mul_spectralComplementaryProjector_eq_of_isDefectSupported (CIK := CIK) hDefect
    calc
      Z * CIK.spectralComplementaryProjector = Z := hRight
      _ = CIK.spectralComplementaryProjector * Z := hLeft.symm

/--
Spectral centrality implies commutation with the spectral grading `Γ_S`.
-/
@[rep_depth operator]
theorem commute_GammaS_of_isDrazinSpectralCentral
    {Z : EndH}
    (hCentral : IsDrazinSpectralCentral CIK Z) :
    Commute Z CIK.toInformationCartanTriple.GammaS := by
  rcases hCentral with ⟨hP, hQ0⟩
  have hGamma :
      CIK.toInformationCartanTriple.GammaS
        = CIK.spectralProjector - CIK.spectralComplementaryProjector := by
    simpa [CertifiedInverseKernel.GammaS] using
      CIK.GammaS_eq_spectralProjector_sub_spectralComplementaryProjector
  calc
    Z * CIK.toInformationCartanTriple.GammaS
        = Z * (CIK.spectralProjector - CIK.spectralComplementaryProjector) := by rw [hGamma]
    _ = Z * CIK.spectralProjector - Z * CIK.spectralComplementaryProjector := by
          simp [mul_sub]
    _ = CIK.spectralProjector * Z - CIK.spectralComplementaryProjector * Z := by
          rw [hP.eq, hQ0.eq]
    _ = (CIK.spectralProjector - CIK.spectralComplementaryProjector) * Z := by
          simp [sub_mul]
    _ = CIK.toInformationCartanTriple.GammaS * Z := by rw [hGamma]

/-- The canonical defect-central extraction is central on the Drazin spectral lane. -/
@[rep_depth operator]
theorem canonicalDefectCentral_isDrazinSpectralCentral :
    IsDrazinSpectralCentral CIK (canonicalDefectCentral CIK) := by
  exact isDrazinSpectralCentral_of_isDefectSupported (CIK := CIK)
    (canonicalDefectCentral_isDefectSupported (CIK := CIK))

/-- The canonical defect-central extraction is central on the full Drazin algebra lane. -/
@[rep_depth operator]
theorem canonicalDefectCentral_isDrazinLaneCentral :
    IsDrazinLaneCentral CIK (canonicalDefectCentral CIK) := by
  refine ⟨canonicalDefectCentral_isDrazinSpectralCentral (CIK := CIK), ?_⟩
  exact commute_GammaS_of_isDrazinSpectralCentral (CIK := CIK)
    (canonicalDefectCentral_isDrazinSpectralCentral (CIK := CIK))

/-- Krein-depth bridge form of spectral centrality for the canonical central extraction. -/
@[rep_depth krein]
theorem canonicalDefectCentralK_isDrazinSpectralCentralK :
    IsDrazinSpectralCentralK CIK (canonicalDefectCentralK CIK) := by
  simpa [canonicalDefectCentralK, IsDrazinSpectralCentralK] using
    canonicalDefectCentral_isDrazinSpectralCentral (CIK := CIK)

/-- Krein-depth bridge form of full Drazin-lane centrality for the canonical central extraction. -/
@[rep_depth krein]
theorem canonicalDefectCentralK_isDrazinLaneCentralK :
    IsDrazinLaneCentralK CIK (canonicalDefectCentralK CIK) := by
  simpa [canonicalDefectCentralK, IsDrazinLaneCentralK] using
    canonicalDefectCentral_isDrazinLaneCentral (CIK := CIK)

/-- Krein-depth bridge: scalar multiples of `Q₀` are defect-supported. -/
@[rep_depth krein]
theorem isDefectSupportedK_smul_spectralComplementaryProjector (c : ℝ) :
    IsDefectSupportedK CIK (c • CIK.spectralComplementaryProjector) := by
  unfold IsDefectSupportedK
  simp [mul_assoc, smul_mul_assoc, mul_smul_comm, CIK.spectralComplementaryProjector_idempotent]

/-- Krein-depth bridge: defect-supported operators are spectrally central on the Drazin lane. -/
@[rep_depth krein]
theorem isDrazinSpectralCentralK_of_isDefectSupportedK
    {Z : EndH}
    (hDefect : IsDefectSupportedK CIK Z) :
    IsDrazinSpectralCentralK CIK Z := by
  exact isDrazinSpectralCentral_of_isDefectSupported (CIK := CIK) hDefect

/-- Krein-depth bridge: spectral centrality implies commutation with `Γ_S`. -/
@[rep_depth krein]
theorem commute_GammaS_of_isDrazinSpectralCentralK
    {Z : EndH}
    (hCentral : IsDrazinSpectralCentralK CIK Z) :
    Commute Z CIK.toInformationCartanTriple.GammaS := by
  exact commute_GammaS_of_isDrazinSpectralCentral (CIK := CIK) hCentral

/--
Internal operator-valued Drazin split:
`Q² = H + Z` with `Z` canonically extracted from the singular block.
-/
@[rep_depth operator]
theorem superHamiltonian_eq_canonicalKinetic_plus_canonicalDefectCentral :
    superHamiltonian CIK
      = canonicalKineticPart (CIK := CIK) + canonicalDefectCentral CIK := by
  unfold canonicalKineticPart
  exact (sub_add_cancel (superHamiltonian CIK) (canonicalDefectCentral CIK)).symm

/-- Krein-depth bridge form of the canonical internal split `Q² = H + Z`. -/
@[rep_depth krein]
theorem superHamiltonianK_eq_canonicalKineticPartK_plus_canonicalDefectCentralK :
    superHamiltonianK CIK
      = canonicalKineticPartK (CIK := CIK) + canonicalDefectCentralK CIK := by
  simpa [superHamiltonianK, canonicalKineticPartK, canonicalDefectCentralK] using
    superHamiltonian_eq_canonicalKinetic_plus_canonicalDefectCentral (CIK := CIK)

/--
Canonical existence form of the Drazin central split `Q² = H + Z`.
-/
@[rep_depth operator]
theorem exists_superHamiltonian_canonical_split :
    ∃ H Z : EndH,
      IsDefectSupported CIK Z
        ∧ HasVanishingDefectBlock CIK H
        ∧ superHamiltonian CIK = H + Z := by
  refine ⟨canonicalKineticPart (CIK := CIK), canonicalDefectCentral CIK, ?_, ?_, ?_⟩
  · exact canonicalDefectCentral_isDefectSupported (CIK := CIK)
  · exact canonicalKineticPart_hasVanishingDefectBlock (CIK := CIK)
  · exact superHamiltonian_eq_canonicalKinetic_plus_canonicalDefectCentral (CIK := CIK)

/-- Krein-depth bridge form of the canonical internal split `Q² = H + Z`. -/
@[rep_depth krein]
theorem exists_superHamiltonian_canonical_splitK :
    ∃ H Z : EndH,
      IsDefectSupportedK CIK Z
        ∧ HasVanishingDefectBlockK CIK H
        ∧ superHamiltonianK CIK = H + Z := by
  rcases exists_superHamiltonian_canonical_split (CIK := CIK) with
    ⟨H, Z, hDef, hVan, hSplit⟩
  exact ⟨H, Z, hDef, hVan, by simpa [superHamiltonianK] using hSplit⟩

/--
Canonical Drazin split with an internal spectral centrality witness for `Z`.
-/
@[rep_depth operator]
theorem exists_superHamiltonian_canonical_split_with_spectral_centrality :
    ∃ H Z : EndH,
      IsDrazinSpectralCentral CIK Z
        ∧ IsDefectSupported CIK Z
        ∧ HasVanishingDefectBlock CIK H
        ∧ superHamiltonian CIK = H + Z := by
  refine ⟨canonicalKineticPart (CIK := CIK), canonicalDefectCentral CIK, ?_, ?_, ?_, ?_⟩
  · exact canonicalDefectCentral_isDrazinSpectralCentral (CIK := CIK)
  · exact canonicalDefectCentral_isDefectSupported (CIK := CIK)
  · exact canonicalKineticPart_hasVanishingDefectBlock (CIK := CIK)
  · exact superHamiltonian_eq_canonicalKinetic_plus_canonicalDefectCentral (CIK := CIK)

/-- Krein-depth bridge form of the centralized canonical split `Q² = H + Z`. -/
@[rep_depth krein]
theorem exists_superHamiltonian_canonical_split_with_spectral_centralityK :
    ∃ H Z : EndH,
      IsDrazinSpectralCentralK CIK Z
        ∧ IsDefectSupportedK CIK Z
        ∧ HasVanishingDefectBlockK CIK H
        ∧ superHamiltonianK CIK = H + Z := by
  rcases exists_superHamiltonian_canonical_split_with_spectral_centrality (CIK := CIK) with
    ⟨H, Z, hCentral, hDef, hVan, hSplit⟩
  exact ⟨H, Z, hCentral, hDef, hVan, by simpa [superHamiltonianK] using hSplit⟩

/--
Canonical Drazin split with full Drazin-lane centrality witness for `Z`.
-/
@[rep_depth operator]
theorem exists_superHamiltonian_canonical_split_with_drazin_lane_centrality :
    ∃ H Z : EndH,
      IsDrazinLaneCentral CIK Z
        ∧ IsDefectSupported CIK Z
        ∧ HasVanishingDefectBlock CIK H
        ∧ superHamiltonian CIK = H + Z := by
  refine ⟨canonicalKineticPart (CIK := CIK), canonicalDefectCentral CIK, ?_, ?_, ?_, ?_⟩
  · exact canonicalDefectCentral_isDrazinLaneCentral (CIK := CIK)
  · exact canonicalDefectCentral_isDefectSupported (CIK := CIK)
  · exact canonicalKineticPart_hasVanishingDefectBlock (CIK := CIK)
  · exact superHamiltonian_eq_canonicalKinetic_plus_canonicalDefectCentral (CIK := CIK)

/--
Krein-depth bridge form of the Drazin-lane centralized canonical split `Q² = H + Z`.
-/
@[rep_depth krein]
theorem exists_superHamiltonian_canonical_split_with_drazin_lane_centralityK :
    ∃ H Z : EndH,
      IsDrazinLaneCentralK CIK Z
        ∧ IsDefectSupportedK CIK Z
        ∧ HasVanishingDefectBlockK CIK H
        ∧ superHamiltonianK CIK = H + Z := by
  rcases exists_superHamiltonian_canonical_split_with_drazin_lane_centrality (CIK := CIK) with
    ⟨H, Z, hCentral, hDef, hVan, hSplit⟩
  exact ⟨H, Z, hCentral, hDef, hVan, by simpa [superHamiltonianK] using hSplit⟩

/--
Uniqueness of the canonical defect-central extraction:
any split with defect-supported `Z` and vanishing-defect-block `H`
must recover `Z = Q₀ Q² Q₀`.
-/
@[rep_depth operator]
theorem defectCentral_eq_of_split
    {H Z : EndH}
    (hDefect : IsDefectSupported CIK Z)
    (hKinetic : HasVanishingDefectBlock CIK H)
    (hSplit : superHamiltonian CIK = H + Z) :
    Z = canonicalDefectCentral CIK := by
  unfold IsDefectSupported at hDefect
  unfold HasVanishingDefectBlock at hKinetic
  unfold canonicalDefectCentral
  have hQSplit :
      CIK.spectralComplementaryProjector * superHamiltonian CIK *
          CIK.spectralComplementaryProjector
        =
      CIK.spectralComplementaryProjector * H *
          CIK.spectralComplementaryProjector
        +
      CIK.spectralComplementaryProjector * Z *
          CIK.spectralComplementaryProjector := by
    rw [hSplit]
    simp [add_mul, mul_add, mul_assoc]
  calc
    Z = CIK.spectralComplementaryProjector * Z *
          CIK.spectralComplementaryProjector := by
          symm
          exact hDefect
    _ =
      CIK.spectralComplementaryProjector * H *
          CIK.spectralComplementaryProjector
        +
      CIK.spectralComplementaryProjector * Z *
          CIK.spectralComplementaryProjector := by
            rw [hKinetic]
            simp
    _ =
      CIK.spectralComplementaryProjector * superHamiltonian CIK *
          CIK.spectralComplementaryProjector := by
            exact hQSplit.symm

/-- Uniqueness of the canonical kinetic remainder under the split axioms. -/
@[rep_depth operator]
theorem canonicalKineticPart_eq_of_split
    {H Z : EndH}
    (hDefect : IsDefectSupported CIK Z)
    (hKinetic : HasVanishingDefectBlock CIK H)
    (hSplit : superHamiltonian CIK = H + Z) :
    H = canonicalKineticPart (CIK := CIK) := by
  have hZ : Z = canonicalDefectCentral CIK :=
    defectCentral_eq_of_split (CIK := CIK) hDefect hKinetic hSplit
  have hH : H = superHamiltonian CIK - Z := by
    calc
      H = (H + Z) - Z := by simp
      _ = superHamiltonian CIK - Z := by rw [← hSplit]
  rw [hH, hZ]
  rfl

/-- Any two lawful defect/kinetic splits are equal to the canonical one. -/
@[rep_depth operator]
theorem canonical_split_unique
    {H₁ Z₁ H₂ Z₂ : EndH}
    (hDefect₁ : IsDefectSupported CIK Z₁)
    (hKinetic₁ : HasVanishingDefectBlock CIK H₁)
    (hSplit₁ : superHamiltonian CIK = H₁ + Z₁)
    (hDefect₂ : IsDefectSupported CIK Z₂)
    (hKinetic₂ : HasVanishingDefectBlock CIK H₂)
    (hSplit₂ : superHamiltonian CIK = H₂ + Z₂) :
    H₁ = H₂ ∧ Z₁ = Z₂ := by
  have hH₁ :
      H₁ = canonicalKineticPart (CIK := CIK) :=
    canonicalKineticPart_eq_of_split (CIK := CIK) hDefect₁ hKinetic₁ hSplit₁
  have hH₂ :
      H₂ = canonicalKineticPart (CIK := CIK) :=
    canonicalKineticPart_eq_of_split (CIK := CIK) hDefect₂ hKinetic₂ hSplit₂
  have hZ₁ :
      Z₁ = canonicalDefectCentral CIK :=
    defectCentral_eq_of_split (CIK := CIK) hDefect₁ hKinetic₁ hSplit₁
  have hZ₂ :
      Z₂ = canonicalDefectCentral CIK :=
    defectCentral_eq_of_split (CIK := CIK) hDefect₂ hKinetic₂ hSplit₂
  constructor
  · calc
      H₁ = canonicalKineticPart (CIK := CIK) := hH₁
      _ = H₂ := hH₂.symm
  · calc
      Z₁ = canonicalDefectCentral CIK := hZ₁
      _ = Z₂ := hZ₂.symm

end CertifiedInverseKernel

section CentralSupercharge

open InfoGeometry.Canonical.SuperchargeCentralChargeClosure
open InfoGeometry.Canonical.OperatorialCentralCharge
open InfoGeometry.Canonical.BogoliubovVielbein
open InfoGeometry.Canonical.SuperchargeGapHessianBridge
open InfoGeometry.Canonical.RelationalInformationDynamics
open InfoGeometry.Canonical.BogoliubovTransport
open InfoGeometry.KK
open InfoGeometry.KK.RealSplitKreinKasparovCycle
open InfoGeometry.Krein

variable {A B F : Type}
variable [NormedRing A] [NormedRing B]
variable [NormedAlgebra ℝ A] [NormedAlgebra ℝ B]
variable [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
variable [KreinSpace (DoubledSpace F)] [KreinGradedModule (DoubledSpace F)]

local notation "H₂" => DoubledSpace F
local notation "EndH₂" => H₂ →L[ℝ] H₂

noncomputable local instance : NormedRing EndH₂ := inferInstance
noncomputable local instance : NormedAlgebra ℝ EndH₂ := inferInstance
noncomputable local instance : NormedAlgebra ℚ EndH₂ :=
  NormedAlgebra.restrictScalars ℚ ℝ EndH₂
local instance : IsTopologicalRing EndH₂ := inferInstance
local instance : SMulCommClass ℝ EndH₂ EndH₂ := inferInstance
local instance : IsScalarTower ℝ EndH₂ EndH₂ := inferInstance

/--
Transported operatorial-central-charge shadow on the intrinsic Drazin defect lane.

Unlike the identity-multiple scalar shadow, this is carried by the defect
projector `Q₀ = 1 - P_D`, so it is generally non-scalar as an operator.
-/
@[rep_depth transport]
noncomputable def operatorialCentralDefectShadow
    (CIK : InfoGeometry.Canonical.CertifiedInverseKernel H₂)
    (X : RealSplitKreinDiracFredholmModule A B H₂)
    (hX : ChiralFredholmSurface X) : EndH₂ :=
  ((operatorialCentralCharge (A := A) (B := B) (E := F) X hX : ℝ))
    • CIK.spectralComplementaryProjector

/--
Strict non-scalarity witness for the transported operatorial-central defect
shadow.

Under nonzero operatorial central charge and a nontrivial defect projector
(`Q₀ ≠ 0`, `Q₀ ≠ 1`), the defect shadow cannot collapse to a scalar operator.
-/
@[rep_depth transport]
theorem operatorialCentralDefectShadow_not_scalar_of_nonzero_charge_of_nontrivial_defect_projector
    (CIK : InfoGeometry.Canonical.CertifiedInverseKernel H₂)
    (X : RealSplitKreinDiracFredholmModule A B H₂)
    (hX : ChiralFredholmSurface X)
    (hCharge : operatorialCentralCharge (A := A) (B := B) (E := F) X hX ≠ 0)
    (hQ0ne0 : CIK.spectralComplementaryProjector ≠ 0)
    (hQ0ne1 : CIK.spectralComplementaryProjector ≠ (1 : EndH₂)) :
    ¬ IsScalarOperatorK (operatorialCentralDefectShadow (A := A) (B := B) CIK X hX) := by
  intro hScalarShadow
  set z : ℝ := (operatorialCentralCharge (A := A) (B := B) (E := F) X hX : ℝ)
  have hz0 :
      ((operatorialCentralCharge (A := A) (B := B) (E := F) X hX : ℤ) : ℝ) ≠ 0 := by
    exact_mod_cast hCharge
  have hz : z ≠ 0 := by
    simpa [z] using hz0
  rcases hScalarShadow with ⟨c, hc⟩
  have hScaleQ0 :
      (z⁻¹ : ℝ) • (operatorialCentralDefectShadow (A := A) (B := B) CIK X hX)
        = CIK.spectralComplementaryProjector := by
    unfold operatorialCentralDefectShadow
    calc
      (z⁻¹ : ℝ)
            • (((operatorialCentralCharge (A := A) (B := B) (E := F) X hX : ℝ))
                • CIK.spectralComplementaryProjector)
          =
        ((z⁻¹ : ℝ) * (operatorialCentralCharge (A := A) (B := B) (E := F) X hX : ℝ))
          • CIK.spectralComplementaryProjector := by
            simp [smul_smul]
      _ = ((z⁻¹ : ℝ) * z) • CIK.spectralComplementaryProjector := by
            simp [z]
      _ = CIK.spectralComplementaryProjector := by
            simp [inv_mul_cancel₀ hz]
  have hScaleScalar :
      (z⁻¹ : ℝ) • (operatorialCentralDefectShadow (A := A) (B := B) CIK X hX)
        = ((z⁻¹ : ℝ) * c) • (1 : EndH₂) := by
    calc
      (z⁻¹ : ℝ) • (operatorialCentralDefectShadow (A := A) (B := B) CIK X hX)
          = (z⁻¹ : ℝ) • (c • (1 : EndH₂)) := by
              simpa [hc]
      _ = ((z⁻¹ : ℝ) * c) • (1 : EndH₂) := by
            simp [smul_smul]
  have hQ0Scalar : IsScalarOperatorK CIK.spectralComplementaryProjector := by
    refine ⟨(z⁻¹ : ℝ) * c, ?_⟩
    calc
      CIK.spectralComplementaryProjector
          = (z⁻¹ : ℝ) • (operatorialCentralDefectShadow (A := A) (B := B) CIK X hX) := by
              exact hScaleQ0.symm
      _ = ((z⁻¹ : ℝ) * c) • (1 : EndH₂) := hScaleScalar
  exact
    (InfoGeometry.Canonical.DrazinSupercharge.CertifiedInverseKernel.spectralComplementaryProjector_not_scalar_of_nontrivialK
      (CIK := CIK) hQ0ne0 hQ0ne1) hQ0Scalar

/--
The operatorial-central defect shadow is defect-supported by construction.
-/
@[rep_depth transport]
theorem operatorialCentralDefectShadow_isDefectSupported
    (CIK : InfoGeometry.Canonical.CertifiedInverseKernel H₂)
    (X : RealSplitKreinDiracFredholmModule A B H₂)
    (hX : ChiralFredholmSurface X) :
    InfoGeometry.Canonical.DrazinSupercharge.CertifiedInverseKernel.IsDefectSupportedK
      CIK (operatorialCentralDefectShadow (A := A) (B := B) CIK X hX) := by
  simpa [operatorialCentralDefectShadow] using
    InfoGeometry.Canonical.DrazinSupercharge.CertifiedInverseKernel.isDefectSupportedK_smul_spectralComplementaryProjector
      (CIK := CIK)
      (operatorialCentralCharge (A := A) (B := B) (E := F) X hX : ℝ)

/--
The operatorial-central defect shadow is central on the Drazin spectral lane.
-/
@[rep_depth transport]
theorem operatorialCentralDefectShadow_isDrazinSpectralCentral
    (CIK : InfoGeometry.Canonical.CertifiedInverseKernel H₂)
    (X : RealSplitKreinDiracFredholmModule A B H₂)
    (hX : ChiralFredholmSurface X) :
    InfoGeometry.Canonical.DrazinSupercharge.CertifiedInverseKernel.IsDrazinSpectralCentralK
      CIK (operatorialCentralDefectShadow (A := A) (B := B) CIK X hX) := by
  exact
    InfoGeometry.Canonical.DrazinSupercharge.CertifiedInverseKernel.isDrazinSpectralCentralK_of_isDefectSupportedK
      (CIK := CIK)
      (operatorialCentralDefectShadow_isDefectSupported
        (A := A) (B := B) CIK X hX)

/--
The operatorial-central defect shadow is central on the full Drazin lane.
-/
@[rep_depth transport]
theorem operatorialCentralDefectShadow_isDrazinLaneCentral
    (CIK : InfoGeometry.Canonical.CertifiedInverseKernel H₂)
    (X : RealSplitKreinDiracFredholmModule A B H₂)
    (hX : ChiralFredholmSurface X) :
    InfoGeometry.Canonical.DrazinSupercharge.CertifiedInverseKernel.IsDrazinLaneCentralK
      CIK (operatorialCentralDefectShadow (A := A) (B := B) CIK X hX) := by
  refine ⟨?_, ?_⟩
  · exact operatorialCentralDefectShadow_isDrazinSpectralCentral
      (A := A) (B := B) CIK X hX
  · exact
      InfoGeometry.Canonical.DrazinSupercharge.CertifiedInverseKernel.commute_GammaS_of_isDrazinSpectralCentralK
        (CIK := CIK)
        (operatorialCentralDefectShadow_isDrazinSpectralCentral
          (A := A) (B := B) CIK X hX)

/--
Transported-slice equality written directly on the intrinsic defect shadow.
-/
@[rep_depth transport]
theorem operatorialCentralDefectShadow_eq_transport_slice
    (CIK : InfoGeometry.Canonical.CertifiedInverseKernel H₂)
    (V : BogoliubovVielbeinBundle (E := F))
    (X : RealSplitKreinDiracFredholmModule A B H₂)
    (hX : ChiralFredholmSurface X)
    (hEven : KreinGradedModule.IsEven (H := H₂) V.connectionGenerator)
    (t : ℝ) :
    operatorialCentralDefectShadow (A := A) (B := B) CIK X hX
      =
    ((quasilatticeAnalyticalIndex V X t
        (quasilatticeChiralFredholmSurfaceOf (E := F) V X hX hEven t) : ℝ))
      • CIK.spectralComplementaryProjector := by
  have hIdx :
      quasilatticeAnalyticalIndex V X t
          (quasilatticeChiralFredholmSurfaceOf (E := F) V X hX hEven t)
        =
      operatorialCentralCharge (A := A) (B := B) (E := F) X hX := by
    exact operatorialCentralCharge_eq_transport_slice
      (A := A) (B := B) (E := F) V X hX hEven t
  have hIdxR :
      (operatorialCentralCharge (A := A) (B := B) (E := F) X hX : ℝ)
        =
      (quasilatticeAnalyticalIndex V X t
          (quasilatticeChiralFredholmSurfaceOf (E := F) V X hX hEven t) : ℝ) := by
    exact congrArg (fun z : ℤ => (z : ℝ)) hIdx.symm
  simpa [operatorialCentralDefectShadow, hIdxR]

/--
Intrinsic mismatch between the canonical non-scalar internal central term and
the transported operatorial-index defect shadow.
-/
@[rep_depth transport]
noncomputable def intrinsicCentralIndexResidual
    (CIK : InfoGeometry.Canonical.CertifiedInverseKernel H₂)
    (X : RealSplitKreinDiracFredholmModule A B H₂)
    (hX : ChiralFredholmSurface X) : EndH₂ :=
  InfoGeometry.Canonical.DrazinSupercharge.CertifiedInverseKernel.canonicalDefectCentralK CIK
    - operatorialCentralDefectShadow (A := A) (B := B) CIK X hX

/--
The intrinsic residual is defect-supported.
-/
@[rep_depth transport]
theorem intrinsicCentralIndexResidual_isDefectSupported
    (CIK : InfoGeometry.Canonical.CertifiedInverseKernel H₂)
    (X : RealSplitKreinDiracFredholmModule A B H₂)
    (hX : ChiralFredholmSurface X) :
    InfoGeometry.Canonical.DrazinSupercharge.CertifiedInverseKernel.IsDefectSupportedK
      CIK (intrinsicCentralIndexResidual (A := A) (B := B) CIK X hX) := by
  set Q0 : EndH₂ := CIK.spectralComplementaryProjector
  have hCan :
      InfoGeometry.Canonical.DrazinSupercharge.CertifiedInverseKernel.IsDefectSupportedK
        CIK (InfoGeometry.Canonical.DrazinSupercharge.CertifiedInverseKernel.canonicalDefectCentralK CIK) :=
    InfoGeometry.Canonical.DrazinSupercharge.CertifiedInverseKernel.canonicalDefectCentralK_isDefectSupportedK
      (CIK := CIK)
  have hShadow :
      InfoGeometry.Canonical.DrazinSupercharge.CertifiedInverseKernel.IsDefectSupportedK
        CIK (operatorialCentralDefectShadow (A := A) (B := B) CIK X hX) :=
    operatorialCentralDefectShadow_isDefectSupported
      (A := A) (B := B) CIK X hX
  have hCanQ :
      Q0 * InfoGeometry.Canonical.DrazinSupercharge.CertifiedInverseKernel.canonicalDefectCentralK CIK * Q0
        =
      InfoGeometry.Canonical.DrazinSupercharge.CertifiedInverseKernel.canonicalDefectCentralK CIK := by
    simpa [Q0] using hCan
  have hShadowQ :
      Q0 * operatorialCentralDefectShadow (A := A) (B := B) CIK X hX * Q0
        =
      operatorialCentralDefectShadow (A := A) (B := B) CIK X hX := by
    simpa [Q0] using hShadow
  unfold InfoGeometry.Canonical.DrazinSupercharge.CertifiedInverseKernel.IsDefectSupportedK
  unfold intrinsicCentralIndexResidual
  change
    Q0
          * (InfoGeometry.Canonical.DrazinSupercharge.CertifiedInverseKernel.canonicalDefectCentralK CIK
              - operatorialCentralDefectShadow (A := A) (B := B) CIK X hX)
          * Q0
        =
    InfoGeometry.Canonical.DrazinSupercharge.CertifiedInverseKernel.canonicalDefectCentralK CIK
      - operatorialCentralDefectShadow (A := A) (B := B) CIK X hX
  calc
    Q0
          * (InfoGeometry.Canonical.DrazinSupercharge.CertifiedInverseKernel.canonicalDefectCentralK CIK
              - operatorialCentralDefectShadow (A := A) (B := B) CIK X hX)
          * Q0
        =
      Q0 * InfoGeometry.Canonical.DrazinSupercharge.CertifiedInverseKernel.canonicalDefectCentralK CIK * Q0
        -
      Q0 * operatorialCentralDefectShadow (A := A) (B := B) CIK X hX * Q0 := by
            simp [mul_sub, sub_mul, mul_assoc]
    _ =
      InfoGeometry.Canonical.DrazinSupercharge.CertifiedInverseKernel.canonicalDefectCentralK CIK
        - operatorialCentralDefectShadow (A := A) (B := B) CIK X hX := by
          rw [hCanQ, hShadowQ]

/--
The intrinsic residual is central on the full Drazin lane.
-/
@[rep_depth transport]
theorem intrinsicCentralIndexResidual_isDrazinLaneCentral
    (CIK : InfoGeometry.Canonical.CertifiedInverseKernel H₂)
    (X : RealSplitKreinDiracFredholmModule A B H₂)
    (hX : ChiralFredholmSurface X) :
    InfoGeometry.Canonical.DrazinSupercharge.CertifiedInverseKernel.IsDrazinLaneCentralK
      CIK (intrinsicCentralIndexResidual (A := A) (B := B) CIK X hX) := by
  have hDef :
      InfoGeometry.Canonical.DrazinSupercharge.CertifiedInverseKernel.IsDefectSupportedK
        CIK (intrinsicCentralIndexResidual (A := A) (B := B) CIK X hX) :=
    intrinsicCentralIndexResidual_isDefectSupported
      (A := A) (B := B) CIK X hX
  have hSpec :
      InfoGeometry.Canonical.DrazinSupercharge.CertifiedInverseKernel.IsDrazinSpectralCentralK
        CIK (intrinsicCentralIndexResidual (A := A) (B := B) CIK X hX) :=
    InfoGeometry.Canonical.DrazinSupercharge.CertifiedInverseKernel.isDrazinSpectralCentralK_of_isDefectSupportedK
      (CIK := CIK) hDef
  exact ⟨hSpec,
    InfoGeometry.Canonical.DrazinSupercharge.CertifiedInverseKernel.commute_GammaS_of_isDrazinSpectralCentralK
      (CIK := CIK) hSpec⟩

/--
Canonical non-scalar Drazin split + transported index-shadow packet:

1. internal split `Q_D² = H + Z` with intrinsic non-scalar `Z`,
2. operatorial-central defect shadow is lane-central and defect-supported,
3. residual `Z - Z_shadow` stays lane-central and defect-supported,
4. transported analytical-index equality on the same slice.
-/
@[rep_depth transport]
theorem canonical_split_with_intrinsic_nonScalar_and_index_shadow
    (CIK : InfoGeometry.Canonical.CertifiedInverseKernel H₂)
    (V : BogoliubovVielbeinBundle (E := F))
    (X : RealSplitKreinDiracFredholmModule A B H₂)
    (hX : ChiralFredholmSurface X)
    (hEven : KreinGradedModule.IsEven (H := H₂) V.connectionGenerator)
    (t : ℝ) :
    InfoGeometry.Canonical.DrazinSupercharge.CertifiedInverseKernel.superHamiltonianK CIK
      =
    InfoGeometry.Canonical.DrazinSupercharge.CertifiedInverseKernel.canonicalKineticPartK (CIK := CIK)
      +
    InfoGeometry.Canonical.DrazinSupercharge.CertifiedInverseKernel.canonicalDefectCentralK CIK
      ∧
    InfoGeometry.Canonical.DrazinSupercharge.CertifiedInverseKernel.IsDrazinLaneCentralK
      CIK
      (InfoGeometry.Canonical.DrazinSupercharge.CertifiedInverseKernel.canonicalDefectCentralK CIK)
      ∧
    InfoGeometry.Canonical.DrazinSupercharge.CertifiedInverseKernel.IsDrazinLaneCentralK
      CIK
      (operatorialCentralDefectShadow (A := A) (B := B) CIK X hX)
      ∧
    InfoGeometry.Canonical.DrazinSupercharge.CertifiedInverseKernel.IsDefectSupportedK
      CIK
      (operatorialCentralDefectShadow (A := A) (B := B) CIK X hX)
      ∧
    InfoGeometry.Canonical.DrazinSupercharge.CertifiedInverseKernel.IsDrazinLaneCentralK
      CIK
      (intrinsicCentralIndexResidual (A := A) (B := B) CIK X hX)
      ∧
    InfoGeometry.Canonical.DrazinSupercharge.CertifiedInverseKernel.IsDefectSupportedK
      CIK
      (intrinsicCentralIndexResidual (A := A) (B := B) CIK X hX)
      ∧
    quasilatticeAnalyticalIndex V X t
        (quasilatticeChiralFredholmSurfaceOf (E := F) V X hX hEven t)
      =
    operatorialCentralCharge (A := A) (B := B) (E := F) X hX := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact
      InfoGeometry.Canonical.DrazinSupercharge.CertifiedInverseKernel.superHamiltonianK_eq_canonicalKineticPartK_plus_canonicalDefectCentralK
        (CIK := CIK)
  · exact
      InfoGeometry.Canonical.DrazinSupercharge.CertifiedInverseKernel.canonicalDefectCentralK_isDrazinLaneCentralK
        (CIK := CIK)
  · exact operatorialCentralDefectShadow_isDrazinLaneCentral
      (A := A) (B := B) CIK X hX
  · exact operatorialCentralDefectShadow_isDefectSupported
      (A := A) (B := B) CIK X hX
  · exact intrinsicCentralIndexResidual_isDrazinLaneCentral
      (A := A) (B := B) CIK X hX
  · exact intrinsicCentralIndexResidual_isDefectSupported
      (A := A) (B := B) CIK X hX
  · exact operatorialCentralCharge_eq_transport_slice
      (A := A) (B := B) (E := F) V X hX hEven t

/--
Central supercharge theorem (repo-native root form):

1. root transported gap/Hessian closure (contains the root Lichnerowicz split),
2. transported analytical index equals operatorial central charge,
3. nonzero central charge forces nonvanishing transported index.
-/
@[rep_depth transport]
theorem central_supercharge_theorem
    (V : BogoliubovVielbeinBundle (E := F))
    (X : RealSplitKreinDiracFredholmModule A B H₂)
    (hX : ChiralFredholmSurface X)
    (hEven : KreinGradedModule.IsEven (H := H₂) V.connectionGenerator)
    (t : ℝ) :
    rootGapHessianClosure (E := F) V
      ∧
    (quasilatticeAnalyticalIndex V X t
        (quasilatticeChiralFredholmSurfaceOf (E := F) V X hX hEven t)
      =
    operatorialCentralCharge (A := A) (B := B) (E := F) X hX)
      ∧
    (operatorialCentralCharge (A := A) (B := B) (E := F) X hX ≠ 0 →
      quasilatticeAnalyticalIndex V X t
          (quasilatticeChiralFredholmSurfaceOf (E := F) V X hX hEven t)
        ≠ 0) := by
  exact root_gap_hessian_centralCharge_closure
    (A := A) (B := B) (E := F) V X hX hEven t

/--
Integrated central supercharge closure:
the local Drazin superHamiltonian `Q²` is spectrally even and grading-flow
fixed, and the root transported supercharge lane carries the
Lichnerowicz/central-charge closure package.
-/
@[rep_depth transport]
theorem central_supercharge_theorem_with_drazin_evenness
    (CIK : InfoGeometry.Canonical.CertifiedInverseKernel (DoubledSpace F))
    (V : BogoliubovVielbeinBundle (E := F))
    (X : RealSplitKreinDiracFredholmModule A B H₂)
    (hX : ChiralFredholmSurface X)
    (hEven : KreinGradedModule.IsEven (H := H₂) V.connectionGenerator)
    (τ t : ℝ) :
    (let T := CIK.toInformationCartanTriple;
      T.IsSpectralCompact
          (InfoGeometry.Canonical.DrazinSupercharge.CertifiedInverseKernel.superHamiltonianK CIK)
        ∧
      T.spectralAdjointFlow T.GammaS τ
          (InfoGeometry.Canonical.DrazinSupercharge.CertifiedInverseKernel.superHamiltonianK CIK)
        =
      InfoGeometry.Canonical.DrazinSupercharge.CertifiedInverseKernel.superHamiltonianK CIK)
      ∧
    rootGapHessianClosure (E := F) V
      ∧
    (quasilatticeAnalyticalIndex V X t
        (quasilatticeChiralFredholmSurfaceOf (E := F) V X hX hEven t)
      =
    operatorialCentralCharge (A := A) (B := B) (E := F) X hX)
      ∧
    (operatorialCentralCharge (A := A) (B := B) (E := F) X hX ≠ 0 →
      quasilatticeAnalyticalIndex V X t
          (quasilatticeChiralFredholmSurfaceOf (E := F) V X hX hEven t)
        ≠ 0) := by
  refine ⟨?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · simpa using
        (InfoGeometry.Canonical.DrazinSupercharge.CertifiedInverseKernel.superHamiltonianK_isSpectralCompact
          (CIK := CIK))
    · simpa using
        (InfoGeometry.Canonical.DrazinSupercharge.CertifiedInverseKernel.superHamiltonianK_fixed_under_spectralGradingFlow
          (CIK := CIK) τ)
  · exact central_supercharge_theorem
      (A := A) (B := B) (F := F) V X hX hEven t

end CentralSupercharge

end InfoGeometry.Canonical.DrazinSupercharge
