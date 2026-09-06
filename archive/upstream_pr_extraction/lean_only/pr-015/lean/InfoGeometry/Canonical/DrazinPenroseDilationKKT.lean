import InfoGeometry.Canonical.DrazinPenroseDilationAlgebra
import InfoGeometry.Canonical.OperatorialCentralCharge
import InfoGeometry.Meta.Architecture

open scoped InnerProductSpace

namespace InfoGeometry.Canonical.DrazinPenroseDilationKKT

open InfoGeometry.Canonical
open InfoGeometry.Canonical.CartanDecomposition
open InfoGeometry.Canonical.OperatorialCentralCharge

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

/-- Repo-owned commutator on the Drazin–Penrose–dilation lane. -/
@[rep_depth operator]
def commutator (X Y : EndH) : EndH := X * Y - Y * X

/-- Repo-owned anticommutator on the Drazin–Penrose–dilation lane. -/
@[rep_depth operator]
def anticommutator (X Y : EndH) : EndH := X * Y + Y * X

/--
Canonical KKT-style algebra slice already latent in the repo:
a certified inverse kernel together with its spectral/geometric gradings,
dilation gap, mismatch, and left/right anomaly operators.
-/
structure DPDKKT (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] where
  kernel : CertifiedInverseKernel E

attribute [spine_object] DPDKKT

namespace DPDKKT

variable (K : DPDKKT E)

/-- Drazin spectral projector. -/
abbrev P_D : EndH := K.kernel.drazinProjector

/-- Drazin complementary projector. -/
abbrev Q_D : EndH := K.kernel.spectralComplementaryProjector

/-- Moore–Penrose range projector. -/
abbrev P_R : EndH := K.kernel.mpRightProjector

/-- Moore–Penrose domain/metric projector. -/
abbrev P_L : EndH := K.kernel.mpLeftProjector

/-- Spectral grading `Γ_S = 2 P_D - 1`. -/
noncomputable abbrev GammaS : EndH := K.kernel.spectralCartanGenerator

/-- Geometric grading `Γ_G = P_R - P_L`. -/
abbrev GammaG : EndH := K.kernel.geometricCartanGenerator

/-- Dilation gap `G = (1/2) (P_R - P_L)`. -/
noncomputable abbrev G : EndH := K.kernel.dilationGenerator

/-- Projector mismatch `Δ = P_D - P_L`. -/
abbrev Delta : EndH := K.kernel.projectorMismatchGenerator

/-- Left odd generator / anomaly operator `χ_L = [P_D, P_L]`. -/
abbrev leftSupercharge : EndH := K.kernel.leftAnomalyGenerator

/-- Right odd generator / anomaly operator `χ_R = [P_D, P_R]`. -/
abbrev rightSupercharge : EndH := K.kernel.rightAnomalyGenerator

/-- The repo geometric grading is exactly twice the dilation gap. -/
theorem two_smul_G_eq_GammaG :
    (2 : ℝ) • K.G = K.GammaG := by
  change (2 : ℝ) • K.kernel.dilationGenerator = K.kernel.geometricCartanGenerator
  exact (K.kernel.geometricCartanGenerator_eq_two_smul_dilationGenerator).symm

/-- The spectral grading is the defining `2 P_D - 1` involution. -/
theorem GammaS_eq_two_mul_P_D_sub_one :
    K.GammaS = 2 * K.P_D - 1 := by
  simpa [DPDKKT.GammaS, DPDKKT.P_D] using
    K.kernel.GammaS_eq_two_mul_spectralProjector_sub_one

/-- The Drazin projector is a `+1` eigen-operator of the spectral grading. -/
theorem GammaS_mul_P_D :
    K.GammaS * K.P_D = K.P_D := by
  simpa [DPDKKT.GammaS, DPDKKT.P_D] using
    K.kernel.GammaS_mul_spectralProjector

/-- The Drazin projector is a right `+1` eigen-operator of the spectral grading. -/
theorem P_D_mul_GammaS :
    K.P_D * K.GammaS = K.P_D := by
  have hComm : K.P_D * K.GammaS = K.GammaS * K.P_D := by
    exact (K.kernel.isSpectralCompact_iff_commute_GammaS).1
      K.kernel.spectralProjector_isSpectralCompact
  calc
    K.P_D * K.GammaS = K.GammaS * K.P_D := hComm
    _ = K.P_D := K.GammaS_mul_P_D

/-- The Drazin complementary projector is a `-1` eigen-operator of the spectral grading. -/
theorem GammaS_mul_Q_D :
    K.GammaS * K.Q_D = -K.Q_D := by
  simpa [DPDKKT.GammaS, DPDKKT.Q_D] using
    K.kernel.GammaS_mul_spectralComplementaryProjector

/-- The Drazin complementary projector is a right `-1` eigen-operator of the spectral grading. -/
theorem Q_D_mul_GammaS :
    K.Q_D * K.GammaS = -K.Q_D := by
  have hComm : K.Q_D * K.GammaS = K.GammaS * K.Q_D := by
    exact (K.kernel.isSpectralCompact_iff_commute_GammaS).1
      K.kernel.spectralComplementaryProjector_isSpectralCompact
  calc
    K.Q_D * K.GammaS = K.GammaS * K.Q_D := hComm
    _ = -K.Q_D := K.GammaS_mul_Q_D

/--
Exact repo-specific KKT closure law:
`[P_D, Γ_G] = χ_R - χ_L`.
-/
theorem commutator_P_D_GammaG_eq_rightSupercharge_sub_leftSupercharge :
    commutator K.P_D K.GammaG = K.rightSupercharge - K.leftSupercharge := by
  simpa [commutator, DPDKKT.P_D, DPDKKT.GammaG,
    DPDKKT.rightSupercharge, DPDKKT.leftSupercharge] using
    K.kernel.drazinProjector_commutator_geometricCartanGenerator_eq_sub_anomalies

/--
Equivalent commutator law written through the dilation gap:
`[P_D, G] = (1/2) (χ_R - χ_L)`.
This is already proved in the certified inverse-kernel owner.
-/
theorem commutator_P_D_G_eq_half_sub_supercharges :
    commutator K.P_D K.G =
      ((2 : ℝ)⁻¹) • (K.rightSupercharge - K.leftSupercharge) := by
  simpa [commutator, DPDKKT.P_D, DPDKKT.G, DPDKKT.rightSupercharge,
    DPDKKT.leftSupercharge] using
    K.kernel.spectralProjector_commutator_dilationGap_eq_half_sub_anomalies

/-- The left odd generator anticommutes with the spectral grading. -/
theorem anticommutator_GammaS_leftSupercharge_eq_zero :
    anticommutator K.GammaS K.leftSupercharge = 0 := by
  have hAnti :
      K.leftSupercharge * K.GammaS = -(K.GammaS * K.leftSupercharge) := by
    simpa [DPDKKT.GammaS, DPDKKT.leftSupercharge] using
      K.kernel.chiralAnomaly_anticommutes_GammaS
  unfold anticommutator
  calc
    K.GammaS * K.leftSupercharge + K.leftSupercharge * K.GammaS
        = K.GammaS * K.leftSupercharge + -(K.GammaS * K.leftSupercharge) := by
            rw [hAnti]
    _ = 0 := by simp

/-- The right odd generator anticommutes with the spectral grading. -/
theorem anticommutator_GammaS_rightSupercharge_eq_zero :
    anticommutator K.GammaS K.rightSupercharge = 0 := by
  have hAnti :
      K.rightSupercharge * K.GammaS = -(K.GammaS * K.rightSupercharge) := by
    simpa [DPDKKT.GammaS, DPDKKT.rightSupercharge] using
      K.kernel.rightChiralAnomaly_anticommutes_GammaS
  unfold anticommutator
  calc
    K.GammaS * K.rightSupercharge + K.rightSupercharge * K.GammaS
        = K.GammaS * K.rightSupercharge + -(K.GammaS * K.rightSupercharge) := by
            rw [hAnti]
    _ = 0 := by simp

/-- The left odd generator lies in the spectral noncompact sector. -/
theorem leftSupercharge_isSpectralNonCompact :
    let T := K.kernel.toInformationCartanTriple
    T.IsSpectralNonCompact K.leftSupercharge := by
  simpa [DPDKKT.leftSupercharge] using
    K.kernel.chiralAnomaly_isSpectralNonCompact

/-- The right odd generator lies in the spectral noncompact sector. -/
theorem rightSupercharge_isSpectralNonCompact :
    let T := K.kernel.toInformationCartanTriple
    T.IsSpectralNonCompact K.rightSupercharge := by
  simpa [DPDKKT.rightSupercharge] using
    K.kernel.rightChiralAnomaly_isSpectralNonCompact

end DPDKKT

section CentralChargeHook

open InfoGeometry.KK
open InfoGeometry.KK.RealSplitKreinKasparovCycle
open InfoGeometry.Krein

variable {A B E : Type}
variable [NormedRing A] [NormedRing B]
variable [NormedAlgebra ℝ A] [NormedAlgebra ℝ B]
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [KreinSpace (DoubledSpace E)] [KreinGradedModule (DoubledSpace E)]

local notation "H₂" => DoubledSpace E

/--
Repo-specific central supercharge hook:
this is not yet an internal operator of the DPD algebra, but the
Fredholm/chiral analytical index already owned as `operatorialCentralCharge`.
-/
@[rep_depth transport]
noncomputable abbrev centralSupercharge
    (X : RealSplitKreinDiracFredholmModule A B H₂)
    (hX : ChiralFredholmSurface X) : ℤ :=
  operatorialCentralCharge (A := A) (B := B) (E := E) X hX

/-- The central supercharge is Bogoliubov-transport invariant. -/
@[rep_depth transport]
theorem centralSupercharge_transport_invariant
    (V : InfoGeometry.Canonical.BogoliubovVielbein.BogoliubovVielbeinBundle (E := E))
    (X : RealSplitKreinDiracFredholmModule A B H₂)
    (hX : ChiralFredholmSurface X)
    (hEven : KreinGradedModule.IsEven (H := H₂) V.connectionGenerator)
    (s t : ℝ) :
    quasilatticeAnalyticalIndex V X s
        (quasilatticeChiralFredholmSurfaceOf (E := E) V X hX hEven s)
      =
    quasilatticeAnalyticalIndex V X t
        (quasilatticeChiralFredholmSurfaceOf (E := E) V X hX hEven t) := by
  simpa [centralSupercharge] using
    operatorialCentralCharge_transport_invariant
      (A := A) (B := B) (E := E) V X hX hEven s t

end CentralChargeHook

end InfoGeometry.Canonical.DrazinPenroseDilationKKT
