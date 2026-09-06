import Mathlib
import proofs.AnomalousKMSFlow

noncomputable section

namespace ConnesSpectralAction

open Complex

variable (H : Type*) [AddCommGroup H] [Module ℂ H]

/--
A Connes/Chamseddine-style quadratic spectral profile with anomaly argument
written through a fixed trace on the modular anomaly context:

`S(δ) = S0 + c · ||tr(δ)||^2`.
-/
def connesSpectralAction
    (C : AnomalousKMSFlow.ModularAnomalyContext H)
    (δ : Module.End ℂ H) (S0 c : ℝ) : ℝ :=
  S0 + c * Complex.normSq (C.tr δ)

@[simp] theorem connesSpectralAction_zero (C : AnomalousKMSFlow.ModularAnomalyContext H)
    (S0 c : ℝ) :
    connesSpectralAction (H := H) C (0 : Module.End ℂ H) S0 c = S0 := by
  simp [connesSpectralAction, Complex.normSq_zero]

/-- Nonnegativity of `normSq` gives a lower bound by the anomaly-free action level. -/
theorem connesAction_ge_baseline (C : AnomalousKMSFlow.ModularAnomalyContext H)
    (S0 c : ℝ) (hc : 0 ≤ c) :
    ∀ δ : Module.End ℂ H, S0 ≤ connesSpectralAction (H := H) C δ S0 c := by
  intro δ
  have hterm : 0 ≤ c * Complex.normSq (C.tr δ) := by
    exact mul_nonneg hc (Complex.normSq_nonneg (C.tr δ))
  have h0 : connesSpectralAction (H := H) C δ S0 c = S0 + c * Complex.normSq (C.tr δ) := by
    rfl
  rw [h0]
  exact le_add_of_nonneg_right hterm

/-- With strictly positive coupling, the trace argument of the action is zero iff the action
  saturates the baseline `δ = 0`.
-/
theorem connesAction_eq_baseline_iff_trace_zero (C : AnomalousKMSFlow.ModularAnomalyContext H)
    (S0 c : ℝ) (hc : 0 < c) (δ : Module.End ℂ H) :
    connesSpectralAction (H := H) C δ S0 c = connesSpectralAction (H := H) C (0 : Module.End ℂ H) S0 c ↔
      C.tr δ = 0 := by
  constructor
  · intro h
    have hsq : c * Complex.normSq (C.tr δ) = 0 := by
      simpa [connesSpectralAction, connesSpectralAction_zero (H := H) C S0 c] using h
    have hnorm : Complex.normSq (C.tr δ) = 0 :=
      (mul_eq_zero.mp hsq).resolve_left (ne_of_gt hc)
    exact Complex.normSq_eq_zero.mp hnorm
  · intro htr
    simp [connesSpectralAction, htr, Complex.normSq_zero]

/-- If the context trace is faithful, this is equivalent to `δ = 0`. -/
theorem connesAction_eq_baseline_iff_zero
    (C : AnomalousKMSFlow.ModularAnomalyContext H)
    (hFaith : AnomalousKMSFlow.TraceFaithful H C.tr)
    (S0 c : ℝ) (hc : 0 < c) (δ : Module.End ℂ H) :
    connesSpectralAction (H := H) C δ S0 c = connesSpectralAction (H := H) C (0 : Module.End ℂ H) S0 c ↔
      δ = 0 := by
  constructor
  · intro h
    have htr : C.tr δ = 0 := (connesAction_eq_baseline_iff_trace_zero (H := H) C S0 c hc δ).1 h
    exact hFaith (by simpa [htr])
  · intro hδ
    subst hδ
    simp [connesSpectralAction_zero (H := H) C]

/-- Cross-cap trap forces anomaly mode `δK = 0`; therefore the spectral action is
minimized at this trap value.
-/
theorem crosscap_trap_reaches_minimum
    (C : AnomalousKMSFlow.ModularAnomalyContext H)
    (ε : Module.End ℂ H) (hε_sq : ε * ε = 1)
    (h_auto : ε * C.δK = C.δK * ε)
    (h_crosscap : ε * C.δK * ε = -C.δK)
    (S0 c : ℝ) (hc : 0 ≤ c) :
    (∀ δ : Module.End ℂ H, connesSpectralAction (H := H) C C.δK S0 c ≤ connesSpectralAction (H := H) C δ S0 c) ∧
      connesSpectralAction (H := H) C C.δK S0 c = S0 := by
  have hδ : C.δK = 0 :=
    (AnomalousKMSFlow.anomaly_trap_from_crosscap (H := H) C ε hε_sq h_auto h_crosscap).1
  have hbaseline : connesSpectralAction (H := H) C C.δK S0 c = S0 := by
    rw [hδ]
    simpa using (connesSpectralAction_zero (H := H) C S0 c)
  refine ⟨?_, hbaseline⟩
  intro δ
  rw [hbaseline]
  exact connesAction_ge_baseline (H := H) C S0 c hc δ

/-- With faithful trace and trap assumptions, the only minimizer is exactly the trap value. -/
theorem crosscap_trap_unique_minimizer
    (C : AnomalousKMSFlow.ModularAnomalyContext H)
    (hFaith : AnomalousKMSFlow.TraceFaithful H C.tr)
    (ε : Module.End ℂ H) (hε_sq : ε * ε = 1)
    (h_auto : ε * C.δK = C.δK * ε)
    (h_crosscap : ε * C.δK * ε = -C.δK)
    (S0 c : ℝ) (hc : 0 < c) :
    (∀ δ : Module.End ℂ H,
      connesSpectralAction (H := H) C δ S0 c = connesSpectralAction (H := H) C C.δK S0 c ↔ δ = C.δK) := by
  have hδ : C.δK = 0 :=
    (AnomalousKMSFlow.anomaly_trap_from_crosscap (H := H) C ε hε_sq h_auto h_crosscap).1
  intro δ
  constructor
  · intro hEq
    have htrace : C.tr δ = 0 := by
      have hEq' : connesSpectralAction (H := H) C δ S0 c =
          connesSpectralAction (H := H) C (0 : Module.End ℂ H) S0 c := by
        simpa [hδ] using hEq
      exact (connesAction_eq_baseline_iff_trace_zero (H := H) C S0 c hc δ).1 hEq'
    have hδop : δ = 0 := hFaith (by simpa [htrace])
    simpa [hδ] using hδop
  · intro h
    subst h
    simpa [hδ] using (connesSpectralAction_zero (H := H) C S0 c)

end ConnesSpectralAction
