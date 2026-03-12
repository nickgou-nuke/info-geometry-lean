import InfoGeometry.Canonical.BottDirac
import InfoGeometry.Canonical.GrandSynthesis
import InfoGeometry.Canonical.GrandUnification
import InfoGeometry.Canonical.LogDet
import InfoGeometry.Canonical.PerelmanW
import InfoGeometry.Canonical.ThermoFromLogDet

/-!
# InfoGeometry.Canonical.DiracRicciBridge

Bridge layer connecting:
- RN/Jacobian log-volume deformation and positivity,
- Jordan/log-det barrier positivity,
- Bott-Dirac splitting,
- and Perelman-style Ricci/Dirac entropy flow monotonicity.
-/

namespace InfoGeometry.Canonical.DiracRicciBridge

open InfoGeometry.Canonical.BottDirac
open InfoGeometry.Canonical.CalabiYauBridge
open InfoGeometry.Canonical.GrandSynthesis
open InfoGeometry.Canonical.GrandUnification
open InfoGeometry.Canonical.KaehlerGeometry
open InfoGeometry.Canonical.LogDet
open InfoGeometry.Canonical.MoE
open InfoGeometry.Canonical.PerelmanW
open InfoGeometry.Canonical.RicciMongeAmpere
open InfoGeometry.Canonical.SpectralInference
open InfoGeometry.Canonical.ThermoFromLogDet

section RnJacobian

variable (n : Nat)

/-- RN relative-volume change is exactly `exp(-K_RN)`. -/
@[simp] theorem relative_volume_change_rn_eq_exp_neg_kahler
    (M : SinkhornMatrix n) :
    relativeVolumeChangeRN n M = Real.exp (-kahlerPotentialRN n M) := rfl

/-- Positivity of the RN relative-volume factor. -/
theorem relative_volume_change_rn_pos
    (M : SinkhornMatrix n) :
    0 < relativeVolumeChangeRN n M := by
  unfold relativeVolumeChangeRN
  exact Real.exp_pos _

/-- Negative log of RN relative volume recovers the RN Kähler potential. -/
theorem neg_log_relative_volume_change_rn
    (M : SinkhornMatrix n) :
    -Real.log (relativeVolumeChangeRN n M) = kahlerPotentialRN n M := by
  rw [relative_volume_change_rn_eq_exp_neg_kahler (n := n) M]
  simp

end RnJacobian

section DeterminantChain

variable {E : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- Jacobian determinant multiplicativity under composition. -/
theorem jac_det_clm_comp
    (L₁ L₂ : E →L[ℝ] E) :
    jacDetCLM (L₁.comp L₂) = jacDetCLM L₁ * jacDetCLM L₂ :=
  jacDetCLM_comp L₁ L₂

/-- Negative log-absolute Jacobian is additive under composition. -/
theorem neg_log_abs_jac_det_clm_comp
    (L₁ L₂ : E →L[ℝ] E)
    (h₁ : jacDetCLM L₁ ≠ 0)
    (h₂ : jacDetCLM L₂ ≠ 0) :
    -logAbsJacDetCLM (L₁.comp L₂)
      = -logAbsJacDetCLM L₁ - logAbsJacDetCLM L₂ := by
  rw [logAbsJacDetCLM_comp (L₁ := L₁) (L₂ := L₂) h₁ h₂]
  ring

end DeterminantChain

section JordanBarrier

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Jordan/KKT barrier potential has the canonical `-log(detJ)` form. -/
@[simp] theorem jordan_kkt_barrier_eq_neg_log_det
    (J : JordanKKTData E) (x : E) :
    J.K x = -Real.log (J.detJ x) := by
  exact JordanKKTData.K_def (J := J) x

/-- Jordan/KKT Bregman divergence is nonnegative. -/
theorem jordan_kkt_bregman_nonneg
    (J : JordanKKTData E) (x y : E) :
    0 ≤ J.DBregman x y :=
  J.DBregman_nonneg x y

end JordanBarrier

section LogDetBarrier

variable {n : ℕ}

/-- Log-det barrier is the negative logarithm of the Jordan determinant. -/
@[simp] theorem log_det_barrier_eq_neg_log_det'
    (X : InfoGeometry.Jordan.SPD n) :
    logDetBarrier X = -Real.log (Matrix.det X.mat) := by
  exact logDetBarrier_eq_neg_log_det (X := X)

/-- Burg/Bregman energy from the log-det barrier is nonnegative. -/
theorem burg_energy_nonnegative
    (X Y : InfoGeometry.Jordan.SPD n) :
    0 ≤ logDetBregman X Y :=
  logDetBregman_nonneg X Y

end LogDetBarrier

section ThermoBarrier

variable {n : ℕ} {Ω : Type _} [Fintype Ω]

/-- Log-det free energy keeps the canonical `-ε log Z` form. -/
@[simp] theorem free_energy_from_log_det_eq_neg_scale_log_partition'
    (X0 : InfoGeometry.Jordan.SPD n)
    (X : Ω → InfoGeometry.Jordan.SPD n)
    (ε : ℝ) :
    freeEnergyFromLogDet X0 X ε = -ε * Real.log (partitionFromLogDet X0 X ε) := by
  exact freeEnergyFromLogDet_eq_neg_scale_log_partition (X0 := X0) (X := X) ε

variable [Nonempty Ω]

/-- Positivity of the partition function induced by Burg energy. -/
theorem partition_from_log_det_pos
    (X0 : InfoGeometry.Jordan.SPD n)
    (X : Ω → InfoGeometry.Jordan.SPD n)
    (ε : ℝ) :
    0 < partitionFromLogDet X0 X ε :=
  partitionFromLogDet_pos' (X0 := X0) (X := X) ε

end ThermoBarrier

section BottDiracRicci

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/--
Coupled law: normalized scalar Kähler-Ricci flow tracked by spinorial scalar,
with `W` derivative given by spinorial dissipation.
-/
def satisfies_dirac_ricci_entropy_law
    (flow : ScalarRicciFlow E) (IST : InfoSpectralTriple E) (W : ℝ → ℝ) : Prop :=
  (∀ s : ℝ, deriv W s = spinorialWDissipation flow IST s) ∧
    SatisfiesNormalizedKaehlerRicciFlow (E := E) flow ∧
    (∀ t : ℝ, flow t = spinorialScalarCurvature IST)

/-- Monotonicity of `W` under the coupled Dirac-Ricci entropy law. -/
theorem w_monotone_of_dirac_ricci_entropy_law
    (flow : ScalarRicciFlow E) (IST : InfoSpectralTriple E) (W : ℝ → ℝ)
    (hDiff : Differentiable ℝ W)
    (hLaw : satisfies_dirac_ricci_entropy_law flow IST W) :
    Monotone W := by
  rcases hLaw with ⟨hW, hNorm, hTrack⟩
  exact W_monotone_of_spinorial_normalized_tracking
    (E := E) (flow := flow) (IST := IST) (W := W) hDiff hW hNorm hTrack

/-- Strict monotonicity when the tracked spinorial scalar curvature is nonzero. -/
theorem w_strict_mono_of_dirac_ricci_entropy_law
    (flow : ScalarRicciFlow E) (IST : InfoSpectralTriple E) (W : ℝ → ℝ)
    (hLaw : satisfies_dirac_ricci_entropy_law flow IST W)
    (hSpin : spinorialScalarCurvature IST ≠ 0) :
    StrictMono W := by
  rcases hLaw with ⟨hW, hNorm, hTrack⟩
  exact W_strictMono_of_spinorial_nonzero
    (E := E) (flow := flow) (IST := IST) (W := W) hW hNorm hTrack hSpin

end BottDiracRicci

section BottSplitting

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Canonical Cl(1,1) Bott-Dirac square equals the canonical Bott Laplacian. -/
theorem cl11_bott_square_eq_laplacian
    (Dn : Endomorphism F) :
    (bottDirac (cl11DiracSeed (E := E)) (cl11Grading (E := E)) Dn).comp
      (bottDirac (cl11DiracSeed (E := E)) (cl11Grading (E := E)) Dn)
      = cl11BottLaplacian (E := E) Dn := by
  simpa using
    cl11_bottDirac_sq_eq_cl11BottLaplacian (E := E) (F := F) (Dn := Dn)

end BottSplitting

section EntropyGravity

variable (n : Nat)
variable {X : Type}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]

/-- RN entropy sourcing plus Monge-Ampere closure yields Ricci-flat vacuum gravity. -/
theorem gravity_from_rn_entropy
    (Kgeo : KaehlerInformationGeometry X)
    (R : RicciTensor X)
    (x : X) (Λ : ℝ)
    (M : SinkhornMatrix n)
    (hSource : RNEntropySourcesMongeAmpere n Kgeo M)
    (hBridge : MongeAmpereRicciClosure R Kgeo) :
    IsRicciFlat R ∧ VacuumEinsteinEquationAt R Kgeo x (2 * Λ) Λ :=
  gravity_generated_by_rnEntropy
    (n := n) (Kgeo := Kgeo) (R := R) (x := x) (Λ := Λ)
    (M := M) hSource hBridge

end EntropyGravity

end InfoGeometry.Canonical.DiracRicciBridge
