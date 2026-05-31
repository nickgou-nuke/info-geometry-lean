import InfoGeometry.Canonical.RicciMongeAmpere
import Mathlib.Analysis.Calculus.Deriv.MeanValue

namespace InfoGeometry.Canonical.PerelmanW

open InfoGeometry.Canonical.RicciMongeAmpere

section Core

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/--
Perelman-style entropy functional scaffold along a scalar Ricci flow:
`W(Λ) = τ(Λ) * R(Λ) + f(Λ)`.
-/
def WFunctional
    (flow : ScalarRicciFlow E) (τ f : ℝ → ℝ) (scale : ℝ) : ℝ :=
  τ scale * flow scale + f scale

/-- Dissipation rate `dW/dΛ`. -/
noncomputable def WDissipation
    (flow : ScalarRicciFlow E) (τ f : ℝ → ℝ) (scale : ℝ) : ℝ :=
  deriv (fun s => WFunctional flow τ f s) scale

/--
Abstract law identifying the `W`-dissipation with a prescribed nonnegative source.
-/
def SatisfiesWLaw
    (flow : ScalarRicciFlow E) (τ f diss : ℝ → ℝ) : Prop :=
  ∀ s : ℝ, WDissipation flow τ f s = diss s

/-- Lemma `deriv_WFunctional_eq_of_True`. -/
lemma deriv_WFunctional_eq_of_True
    (flow : ScalarRicciFlow E) (τ f diss : ℝ → ℝ)
    (hLaw : SatisfiesWLaw flow τ f diss) (s : ℝ) :
    deriv (fun t => WFunctional flow τ f t) s = diss s := by
  simpa [WDissipation] using hLaw s

/--
Monotonicity of `W` from a nonnegative dissipation law.
-/
theorem WFunctional_monotone_of_nonneg_dissipation
    (flow : ScalarRicciFlow E) (τ f diss : ℝ → ℝ)
    (hDiff : Differentiable ℝ (fun t => WFunctional flow τ f t))
    (hLaw : SatisfiesWLaw flow τ f diss)
    (hNonneg : ∀ s : ℝ, 0 ≤ diss s) :
    Monotone (fun t => WFunctional flow τ f t) := by
  apply monotone_of_deriv_nonneg hDiff
  intro s
  rw [deriv_WFunctional_eq_of_True flow τ f diss hLaw s]
  exact hNonneg s

/--
Strict monotonicity of `W` from strictly positive dissipation law.
-/
private theorem WFunctional_strictMono_of_pos_dissipation
    (flow : ScalarRicciFlow E) (τ f diss : ℝ → ℝ)
    (hLaw : SatisfiesWLaw flow τ f diss)
    (hPos : ∀ s : ℝ, 0 < diss s) :
    StrictMono (fun t => WFunctional flow τ f t) := by
  apply strictMono_of_deriv_pos
  intro s
  rw [deriv_WFunctional_eq_of_True flow τ f diss hLaw s]
  exact hPos s

/--
Barrier-driven monotonicity:
if dissipation dominates a nonnegative barrier pointwise, `W` is monotone.
-/
private theorem WFunctional_monotone_of_lower_barrier
    (flow : ScalarRicciFlow E) (τ f diss barrier : ℝ → ℝ)
    (hDiff : Differentiable ℝ (fun t => WFunctional flow τ f t))
    (hLaw : SatisfiesWLaw flow τ f diss)
    (hLower : ∀ s : ℝ, barrier s ≤ diss s)
    (hBarrierNonneg : ∀ s : ℝ, 0 ≤ barrier s) :
    Monotone (fun t => WFunctional flow τ f t) := by
  refine WFunctional_monotone_of_nonneg_dissipation
    (flow := flow) (τ := τ) (f := f) (diss := diss) hDiff hLaw ?_
  intro s
  exact le_trans (hBarrierNonneg s) (hLower s)

/--
Barrier-driven strict monotonicity:
if dissipation dominates a strictly positive barrier pointwise, `W` is strictly monotone.
-/
private theorem WFunctional_strictMono_of_lower_pos_barrier
    (flow : ScalarRicciFlow E) (τ f diss barrier : ℝ → ℝ)
    (hLaw : SatisfiesWLaw flow τ f diss)
    (hLower : ∀ s : ℝ, barrier s ≤ diss s)
    (hBarrierPos : ∀ s : ℝ, 0 < barrier s) :
    StrictMono (fun t => WFunctional flow τ f t) := by
  refine WFunctional_strictMono_of_pos_dissipation
    (flow := flow) (τ := τ) (f := f) (diss := diss) hLaw ?_
  intro s
  exact lt_of_lt_of_le (hBarrierPos s) (hLower s)

end Core

end InfoGeometry.Canonical.PerelmanW
