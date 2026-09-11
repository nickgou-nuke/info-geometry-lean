import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra

noncomputable section

namespace InfoGeometry.Canonical.KleinBottleSymmetry

open Complex
open scoped BigOperators

variable (H : Type*) [AddCommGroup H] [Module ℂ H]

/-- Abstract cross-cap forcing: conjugation by an involutive involution has both a
prescribed sign and an invariance sign, so the anomaly must vanish. -/
theorem conjugation_forced_anomaly_vanishes
    (ε : Module.End ℂ H) (δK : Module.End ℂ H)
    (h_automorphism : ε * δK * ε = δK)
    (h_crosscap : ε * δK * ε = -δK) : δK = 0 := by
  have h : δK = -δK := by
    calc
      δK = ε * δK * ε := h_automorphism.symm
      _ = -δK := h_crosscap
  ext x
  have hpoint : δK x = -δK x := by
    exact congrArg (fun T : Module.End ℂ H => T x) h
  have hsum : δK x + δK x = 0 :=
    (eq_neg_iff_add_eq_zero).mp hpoint
  have hzero : δK x = 0 := by
    have hmul : (2 : ℂ) • δK x = 0 := by
      simpa [two_smul] using hsum
    exact (smul_eq_zero.mp hmul).resolve_left (by norm_num)
  exact hzero

/-- The Klein-bottle cross-cap mechanism in the concrete 2x2 test sector.
If `δK` is both conjugation-invariant and cross-cap-odd under
`Γ := ε`, then it is forced to vanish. -/
theorem kleinBottle_anomaly_vanishes_from_crosscap
    (ε : Module.End ℂ (Fin 2 → ℂ)) (δK : Module.End ℂ (Fin 2 → ℂ))
    (h_automorphism : ε * δK * ε = δK)
    (h_crosscap : ε * δK * ε = -δK) : δK = 0 := by
  exact conjugation_forced_anomaly_vanishes (H := Fin 2 → ℂ) ε δK h_automorphism h_crosscap

end InfoGeometry.Canonical.KleinBottleSymmetry
