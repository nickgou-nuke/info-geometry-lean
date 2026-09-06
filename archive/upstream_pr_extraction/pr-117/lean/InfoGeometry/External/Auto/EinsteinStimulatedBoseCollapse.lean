import Mathlib.Data.Real.Basic
import Mathlib.Topology.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Filter Topology

noncomputable section

variable (A B : ℝ)
variable (N : ℝ)

def N_g (ρ : ℝ) := N * (A + B * ρ) / (A + 2 * B * ρ)
def N_e (ρ : ℝ) := N * B * ρ / (A + 2 * B * ρ)

lemma detailed_balance_eq (ρ : ℝ) :
  N_g A B N ρ * B * ρ = N_e A B N ρ * (A + B * ρ) := by
  simp only [N_g, N_e]
  ring

theorem einstein_stimulated_bose_collapse 
  (hA : 0 < A) (hB : 0 < B) (hN : 0 < N) :
  Tendsto (fun ρ => N_g A B N ρ - N_e A B N ρ) atTop (𝓝 0) := by
  have H : ∀ ρ : ℝ, N_g A B N ρ - N_e A B N ρ = (N * A) / (A + 2 * B * ρ) := by
    intro ρ
    simp only [N_g, N_e]
    ring
  simp_rw [H]
  have h1 : Tendsto (fun ρ : ℝ => 2 * B * ρ) atTop atTop :=
    Tendsto.const_mul_atTop (by positivity) tendsto_id
  have h2 : Tendsto (fun ρ : ℝ => A) atTop (𝓝 A) := tendsto_const_nhds
  have h3 : Tendsto (fun ρ : ℝ => 2 * B * ρ + A) atTop atTop := Tendsto.atTop_add h1 h2
  have h4 : (fun ρ : ℝ => 2 * B * ρ + A) = (fun ρ : ℝ => A + 2 * B * ρ) := by
    ext x
    ring
  rw [h4] at h3
  have h5 : Tendsto (fun ρ : ℝ => (N * A) / (A + 2 * B * ρ)) atTop (𝓝 0) :=
    Tendsto.const_div_atTop h3 (N * A)
  exact h5

end
