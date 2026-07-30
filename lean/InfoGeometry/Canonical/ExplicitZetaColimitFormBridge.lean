import Mathlib.Tactic
import Mathlib.NumberTheory.LSeries.RiemannZeta
import InfoGeometry.Canonical.CategoricalRiemannInductiveColimitBridge

namespace InfoGeometry.Canonical.ExplicitZetaColimitFormBridge

open Complex

def primeCutoffSet (n : ℕ) : Finset ℕ :=
  (Finset.range (n + 1)).filter Nat.Prime

theorem mem_primeCutoffSet_is_prime (n : ℕ) {p : ℕ} (hp : p ∈ primeCutoffSet n) :
    Nat.Prime p := by
  unfold primeCutoffSet at hp
  exact (Finset.mem_filter.mp hp).2

noncomputable def finiteEulerCutoffProduct (n : ℕ) (s : ℂ) : ℂ :=
  ∏ p ∈ primeCutoffSet n, (1 - (p : ℂ) ^ (-s))⁻¹

theorem finite_euler_cutoff_product_ne_zero
    (n : ℕ) (s : ℂ) (h_non_one : ∀ p ∈ primeCutoffSet n, (p : ℂ) ^ (-s) ≠ 1) :
    finiteEulerCutoffProduct n s ≠ 0 := by
  unfold finiteEulerCutoffProduct
  rw [Finset.prod_ne_zero_iff]
  intro p hp
  apply inv_ne_zero
  intro h_sub
  apply h_non_one p hp
  calc
    (p : ℂ) ^ (-s) = 1 - (1 - (p : ℂ) ^ (-s)) := by ring
    _ = 1 - 0 := by rw [h_sub]
    _ = 1 := by ring

end InfoGeometry.Canonical.ExplicitZetaColimitFormBridge
