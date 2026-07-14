import Mathlib.Tactic
import InfoGeometry.External.Automath.Omega.POM.HankelNFShiftInvarianceAndPropagation

namespace Omega.Discussion

noncomputable section

/-- Paper-facing rigidity wrapper for syntax-independent Hankel recovery: if two normal-form
factorizations share the same visible `2 d_q` window, then they have the same witness block
`H₂`, the same transfer matrix, and therefore the same shifted Hankel blocks for every `m ≥ 2`.
    thm:discussion-hankel-syntax-independent-rigidity -/
theorem paper_discussion_hankel_syntax_independent_rigidity
    {d dq : ℕ}
    (hdq : 1 ≤ dq)
    (O₁ A₁ C₁ O₂ A₂ C₂ : Matrix (Fin d) (Fin d) ℝ)
    (hShift₁ :
      ∀ k, ((O₁ * A₁ ^ k * C₁)⁻¹ * (O₁ * A₁ ^ (k + 1) * C₁)) = C₁⁻¹ * A₁ * C₁)
    (hShift₂ :
      ∀ k, ((O₂ * A₂ ^ k * C₂)⁻¹ * (O₂ * A₂ ^ (k + 1) * C₂)) = C₂⁻¹ * A₂ * C₂)
    (hProp₁ :
      ∀ k₀ r, O₁ * A₁ ^ (k₀ + r) * C₁ = (O₁ * A₁ ^ k₀ * C₁) * (C₁⁻¹ * A₁ * C₁) ^ r)
    (hProp₂ :
      ∀ k₀ r, O₂ * A₂ ^ (k₀ + r) * C₂ = (O₂ * A₂ ^ k₀ * C₂) * (C₂⁻¹ * A₂ * C₂) ^ r)
    (hWindow : ∀ k ≤ 2 * dq, O₁ * A₁ ^ k * C₁ = O₂ * A₂ ^ k * C₂) :
    O₁ * A₁ ^ 2 * C₁ = O₂ * A₂ ^ 2 * C₂ ∧
      C₁⁻¹ * A₁ * C₁ = C₂⁻¹ * A₂ * C₂ ∧
      ∀ m, 2 ≤ m → O₁ * A₁ ^ m * C₁ = O₂ * A₂ ^ m * C₂ := by
  have hH0 : O₁ * A₁ ^ 0 * C₁ = O₂ * A₂ ^ 0 * C₂ := hWindow 0 (by omega)
  have hH1 : O₁ * A₁ ^ 1 * C₁ = O₂ * A₂ ^ 1 * C₂ := hWindow 1 (by omega)
  have hH2 : O₁ * A₁ ^ 2 * C₁ = O₂ * A₂ ^ 2 * C₂ := hWindow 2 (by omega)
  have hTransfer : C₁⁻¹ * A₁ * C₁ = C₂⁻¹ * A₂ * C₂ := by
    calc
      C₁⁻¹ * A₁ * C₁ = (O₁ * A₁ ^ 0 * C₁)⁻¹ * (O₁ * A₁ ^ (0 + 1) * C₁) := by
        symm
        simpa using hShift₁ 0
      _ = (O₂ * A₂ ^ 0 * C₂)⁻¹ * (O₂ * A₂ ^ (0 + 1) * C₂) := by
        rw [hH0, hH1]
      _ = C₂⁻¹ * A₂ * C₂ := by
        simpa using hShift₂ 0
  refine ⟨hH2, hTransfer, ?_⟩
  intro m hm
  calc
    O₁ * A₁ ^ m * C₁ = (O₁ * A₁ ^ 0 * C₁) * (C₁⁻¹ * A₁ * C₁) ^ m := by
      simpa using hProp₁ 0 m
    _ = (O₂ * A₂ ^ 0 * C₂) * (C₂⁻¹ * A₂ * C₂) ^ m := by
      rw [hH0, hTransfer]
    _ = O₂ * A₂ ^ m * C₂ := by
      simpa using (hProp₂ 0 m).symm

end

end Omega.Discussion
