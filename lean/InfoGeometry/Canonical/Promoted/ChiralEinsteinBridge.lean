import InfoGeometry.Canonical.Promoted.ChiralAnomaly
import InfoGeometry.Canonical.Promoted.RicciMongeAmpere

namespace InfoGeometry.Research.ChiralEinsteinBridge

open InfoGeometry.Research.ChiralAnomaly
open InfoGeometry.Research.MoE
open InfoGeometry.Research.KaehlerGeometry
open InfoGeometry.Research.RicciMongeAmpere

section EinsteinSource

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/--
Chiral-anomaly sourced stress-energy tensor: isotropic source `T = A g` at basepoint `x`.
-/
noncomputable def anomalyStressEnergyAt
    (K : KaehlerInformationGeometry E) (x : E) (A : ℝ) :
    StressEnergyTensor E :=
  fun u v => A * K.H.metric x u v

/-- Canonical alias for anomaly-sourced isotropic stress-energy model. -/
noncomputable abbrev anomalyStressEnergyModelAt
    (K : KaehlerInformationGeometry E) (x : E) (A : ℝ) :
    StressEnergyTensor E :=
  anomalyStressEnergyAt K x A

@[simp] lemma anomalyStressEnergyAt_apply
    (K : KaehlerInformationGeometry E) (x : E) (A : ℝ) (u v : E) :
    anomalyStressEnergyAt K x A u v = A * K.H.metric x u v := rfl

@[simp] lemma anomalyStressEnergyAt_zero
    (K : KaehlerInformationGeometry E) (x : E) :
    anomalyStressEnergyAt K x 0 = fun _ _ => 0 := by
  funext u v
  simp [anomalyStressEnergyAt]

/--
If `Ric = c g`, then anomaly source `T = A g` closes Einstein's equation
with scalar relation `R = 2(c + Λ - κA)`.
-/
theorem einsteinEquation_of_anomaly_source
    (c : ℝ) (R : RicciTensor E) (K : KaehlerInformationGeometry E) (x : E)
    (Λ κ A : ℝ)
    (hEin : IsEinsteinKaehlerAtWith c R K x) :
    EinsteinEquationAt R K x (2 * (c + Λ - κ * A)) Λ κ
      (anomalyStressEnergyAt K x A) := by
  intro u v
  rw [einsteinTensor_eq_metric_multiple_of_einsteinKaehlerWith
      (c := c) (R := R) (K := K) (x := x)
      (scalar := 2 * (c + Λ - κ * A)) hEin u v]
  unfold anomalyStressEnergyAt
  ring

end EinsteinSource

section RoutingEinsteinSource

variable {V : Type*} [NormedAddCommGroup V]
variable (n : Nat) [Nonempty (Fin n)]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/--
A bistochastic router induces a bounded chiral source `A = ε_route ∈ [0,1]`,
which then sources Einstein's equation on the information geometry.
-/
theorem exists_einsteinEquation_of_bistochastic_routingAnomaly
    (β : ℝ) (xRoute : Fin n → V) (hcol : IsBistochasticSwitch n β xRoute)
    (label : PermMode n → CliffordLabel)
    (c : ℝ) (R : RicciTensor E) (K : KaehlerInformationGeometry E) (x : E)
    (Λ κ : ℝ)
    (hEin : IsEinsteinKaehlerAtWith c R K x) :
    ∃ A : ℝ, 0 ≤ A ∧ A ≤ 1 ∧
      EinsteinEquationAt R K x (2 * (c + Λ - κ * A)) Λ κ
        (anomalyStressEnergyAt K x A) := by
  rcases exists_routingEpsilon_of_bistochastic (n := n) β xRoute hcol label with
    ⟨w, _hw_nonneg, _hw_sum, _hw_matrix, hA_le⟩
  refine ⟨routingEpsilon w label, routingEpsilon_nonneg w label, hA_le, ?_⟩
  exact einsteinEquation_of_anomaly_source
    (c := c) (R := R) (K := K) (x := x) (Λ := Λ) (κ := κ)
    (A := routingEpsilon w label) hEin

end RoutingEinsteinSource

section AnomalyRicciFlow

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/--
Anomaly-driven normalized Kähler-Ricci flow:
`∂_Λ R = -R + A(Λ)`.
-/
def SatisfiesAnomalyDrivenKaehlerRicciFlow
    (flow : ScalarRicciFlow E) (A : ℝ → ℝ) : Prop :=
  ∀ s : ℝ, scalarRicciBetaFunction (E := E) flow s = - flow s + A s

/-- Canonical scalar-Ricci naming alias for anomaly-driven evolution law. -/
abbrev SatisfiesAnomalyDrivenScalarRicciFlow
    (flow : ScalarRicciFlow E) (A : ℝ → ℝ) : Prop :=
  SatisfiesAnomalyDrivenKaehlerRicciFlow (E := E) flow A

lemma anomalyDriven_zeroSource_iff_normalized
    (flow : ScalarRicciFlow E) :
    SatisfiesAnomalyDrivenKaehlerRicciFlow (E := E) flow (fun _ => 0)
      ↔ SatisfiesNormalizedKaehlerRicciFlow (E := E) flow := by
  constructor <;> intro h s <;> simpa [SatisfiesAnomalyDrivenKaehlerRicciFlow] using h s

/--
At RG fixed point (`β_R = 0`), the scalar curvature equals the anomaly source.
-/
theorem anomalyDriven_fixedpoint_tracks_source
    (flow : ScalarRicciFlow E) (A : ℝ → ℝ)
    (hFlow : SatisfiesAnomalyDrivenKaehlerRicciFlow (E := E) flow A)
    (hFixed : ∀ s, scalarRicciBetaFunction (E := E) flow s = 0) :
    ∀ s, flow s = A s := by
  intro s
  have hEq : 0 = - flow s + A s := by
    calc
      0 = scalarRicciBetaFunction (E := E) flow s := by
            symm
            exact hFixed s
      _ = - flow s + A s := hFlow s
  have hEq' : - flow s + A s = 0 := by
    simpa using hEq.symm
  calc
    flow s = flow s + 0 := by ring
    _ = flow s + (- flow s + A s) := by simp [hEq']
    _ = A s := by ring

theorem anomalyDrivenScalarRicci_fixedpoint_tracks_source
    (flow : ScalarRicciFlow E) (A : ℝ → ℝ)
    (hFlow : SatisfiesAnomalyDrivenScalarRicciFlow (E := E) flow A)
    (hFixed : ∀ s, scalarRicciBetaFunction (E := E) flow s = 0) :
    ∀ s, flow s = A s := by
  exact anomalyDriven_fixedpoint_tracks_source
    (E := E) (flow := flow) (A := A) hFlow hFixed

section InverseSource

variable {R : Type*} [SeminormedRing R]

/-- Constant anomaly source generated by inverse-level chiral scale `ε`. -/
noncomputable def inverseEpsilonSource (a a_mp a_d : R) : ℝ → ℝ :=
  fun _ => epsilon a a_mp a_d

/--
If flow is driven by the inverse-level chiral anomaly source and is at fixed point,
the scalar curvature is exactly the chiral scale `ε`.
-/
theorem anomalyDriven_fixedpoint_eq_inverseEpsilon
    (flow : ScalarRicciFlow E)
    (a a_mp a_d : R)
    (hFlow : SatisfiesAnomalyDrivenKaehlerRicciFlow (E := E) flow
      (inverseEpsilonSource a a_mp a_d))
    (hFixed : ∀ s, scalarRicciBetaFunction (E := E) flow s = 0) :
    ∀ s, flow s = epsilon a a_mp a_d := by
  intro s
  simpa [inverseEpsilonSource] using
    (anomalyDriven_fixedpoint_tracks_source
      (E := E) (flow := flow) (A := inverseEpsilonSource a a_mp a_d) hFlow hFixed s)

end InverseSource
end AnomalyRicciFlow

end InfoGeometry.Research.ChiralEinsteinBridge
