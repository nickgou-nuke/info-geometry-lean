import Mathlib.Tactic
import InfoGeometry.External.Auto.AnomalousKMSFlow
import InfoGeometry.External.Auto.CuntzKTheoryPairing
import InfoGeometry.External.Auto.ZetaCoordinateSymmetry
import InfoGeometry.External.Auto.PrimonSuperThermodynamics
import InfoGeometry.External.Auto.ConnesSpectralAction

noncomputable section

namespace InfoGeometry.Canonical.UnifiedAnomalyArchitecture

open Complex

/--
Unified architecture statement matching the three-sector proof diagram:

Topological (K-theory) collapse + Connes–Chern pairing ⇒ anomaly annihilation,
Analysis (strict convexity + involution symmetry) ⇒ axis-lock at σ=1/2,
Algebra (CPT graded factors) ⇒ `Z_total = 1`.
-/
theorem unified_architecture_of_anomaly_proof
    (f : ℝ → ℝ)
    (hConvex : StrictConvexOn ℝ (Set.Ioo (0 : ℝ) 1) f)
    (hSymm : ∀ σ ∈ Set.Ioo (0 : ℝ) 1, f (1 - σ) = f σ)
    (σ : ℝ)
    (hσ : σ ∈ Set.Ioo (0 : ℝ) 1)
    (hσ_ne : σ ≠ InfoGeometry.Arithmetic.ZetaCoordinateSymmetry.criticalAxis)
    (H : Type*) [AddCommGroup H] [Module ℂ H]
    (C : AnomalousKMSFlow.ModularAnomalyContext H)
    (hFaith : AnomalousKMSFlow.TraceFaithful H C.tr)
    (S0 c : ℝ) (hc : 0 < c)
    {K1 : Type*} [AddCommGroup K1]
    (k : CuntzKTheoryPairing.TrivialK0Model) (x : K1)
    (hPair :
      AnomalousKMSFlow.anomalousIndex H C =
      (inferInstance : CuntzKTheoryPairing.ConnesChernPairing CuntzKTheoryPairing.TrivialK0Model K1).pair k x)
    (β : ℝ) (S : Finset ℕ)
    (hβ : 0 < β) (hS : ∀ p ∈ S, 1 < p) :
    C.δK = 0 ∧
      (ConnesSpectralAction.connesSpectralAction (H := H) C C.δK S0 c = S0) ∧
      (∀ δ : Module.End ℂ H,
        ConnesSpectralAction.connesSpectralAction (H := H) C δ S0 c =
          ConnesSpectralAction.connesSpectralAction (H := H) C C.δK S0 c ↔ δ = C.δK) ∧
      (∀ s, AnomalousKMSFlow.anomalousLineLeak (AnomalousKMSFlow.anomalousIndexLeakProfile H C) s = 0) ∧
      (f InfoGeometry.Arithmetic.ZetaCoordinateSymmetry.criticalAxis < f σ) ∧
      (PrimonSuperThermo.totalCPTPartition β S = 1) := by
  have hTop :
      C.δK = 0 ∧
      (∀ δ : Module.End ℂ H,
        ConnesSpectralAction.connesSpectralAction (H := H) C C.δK S0 c ≤
          ConnesSpectralAction.connesSpectralAction (H := H) C δ S0 c) ∧
      (ConnesSpectralAction.connesSpectralAction (H := H) C C.δK S0 c = S0) ∧
      (∀ δ : Module.End ℂ H,
        ConnesSpectralAction.connesSpectralAction (H := H) C δ S0 c =
          ConnesSpectralAction.connesSpectralAction (H := H) C C.δK S0 c ↔ δ = C.δK) ∧
      (∀ s, AnomalousKMSFlow.anomalousLineLeak (AnomalousKMSFlow.anomalousIndexLeakProfile H C) s = 0) :=
    CuntzKTheoryPairing.O2_pairing_triviality_yields_full_anomaly_collapse
      (H := H) C hFaith S0 c hc k x hPair
  rcases hTop with ⟨hδ, _hMin, hBase, hUniq, hLeak⟩
  have hAxis :
      f InfoGeometry.Arithmetic.ZetaCoordinateSymmetry.criticalAxis < f σ :=
    InfoGeometry.Arithmetic.ZetaCoordinateSymmetry.strictConvex_symmetric_midpoint_lt f hConvex hSymm σ hσ hσ_ne
  have hCPT : PrimonSuperThermo.totalCPTPartition β S = 1 :=
    PrimonSuperThermo.totalCPTPartition_is_one β S hβ hS
  exact ⟨hδ, hBase, hUniq, hLeak, hAxis, hCPT⟩

end InfoGeometry.Canonical.UnifiedAnomalyArchitecture
