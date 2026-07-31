import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-coordinatebundle-atomic-integrability-logscale`. -/
theorem paper_conclusion_coordinatebundle_atomic_integrability_logscale
    (m n s LJ Delta shannon audit linear kolmogorov Cm CmDrop : ℕ)
    (hLJ : LJ = 2 ^ (m * (n - s)))
    (hDelta : Delta = LJ)
    (hShannon : shannon = Delta)
    (hAudit : audit = Delta)
    (hLinear : linear = Delta)
    (hKolmogorov : kolmogorov = Delta)
    (hCm : Cm = CmDrop + m * (n - s)) :
    Delta = 2 ^ (m * (n - s)) ∧
      shannon = 2 ^ (m * (n - s)) ∧
      audit = 2 ^ (m * (n - s)) ∧
      linear = 2 ^ (m * (n - s)) ∧
      kolmogorov = 2 ^ (m * (n - s)) ∧
      Cm = CmDrop + m * (n - s) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hDelta, hLJ]
  · rw [hShannon, hDelta, hLJ]
  · rw [hAudit, hDelta, hLJ]
  · rw [hLinear, hDelta, hLJ]
  · rw [hKolmogorov, hDelta, hLJ]
  · exact hCm

end Omega.Conclusion
