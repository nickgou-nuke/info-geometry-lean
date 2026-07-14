import Mathlib

namespace Omega.Zeta

noncomputable section

/-- Closed form obtained by separating the `k = 1` pole term from the convergent Möbius tail. -/
def finitePartClosedForm (finitePart logC : ℝ) (mobiusLogZeta : ℕ → ℝ) : Prop :=
  finitePart = logC + ∑' k : ℕ, mobiusLogZeta (k + 2)

/-- Publication-facing finite-part closed form for the Abelian Möbius-zeta decomposition.
    prop:abel-finite-part-mobius-zeta -/
theorem paper_etds_abel_finite_part_mobius_zeta
    (finitePart logC : ℝ) (mobiusLogZeta : ℕ → ℝ)
    (hResidue : mobiusLogZeta 1 = logC)
    (hFinitePartSplit : finitePart = mobiusLogZeta 1 + ∑' k : ℕ, mobiusLogZeta (k + 2))
    (hTailSummable : Summable (fun k : ℕ => mobiusLogZeta (k + 2))) :
    finitePartClosedForm finitePart logC mobiusLogZeta := by
  calc
    finitePart = mobiusLogZeta 1 + ∑' k : ℕ, mobiusLogZeta (k + 2) := hFinitePartSplit
    _ = logC + ∑' k : ℕ, mobiusLogZeta (k + 2) := by rw [hResidue]

end
end Omega.Zeta
