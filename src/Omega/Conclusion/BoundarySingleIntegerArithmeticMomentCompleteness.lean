import Mathlib.Tactic
import Omega.SPG.BoundaryGodelMomentReadout

namespace Omega.Conclusion

/-- Symmetric-difference distance on finite monomial supports. -/
def finiteMomentSupportDistance
    (U V : Omega.SPG.FiniteMomentSupport) : ℝ :=
  (((U \ V).card + (V \ U).card : ℕ) : ℝ)

/-- Counting measure of a finite monomial support. -/
def finiteMomentSupportMeasure
    (U : Omega.SPG.FiniteMomentSupport) : ℝ := (U.card : ℝ)

/-- Counting measure is 1-Lipschitz for symmetric-difference distance. -/
theorem finiteMomentSupport_measure_lipschitz
    (U V : Omega.SPG.FiniteMomentSupport) :
    |finiteMomentSupportMeasure U - finiteMomentSupportMeasure V| ≤
      finiteMomentSupportDistance U V := by
  have hU :
      (((U \ V).card : ℕ) : ℝ) + (((U ∩ V).card : ℕ) : ℝ) =
        (U.card : ℝ) := by
    exact_mod_cast Finset.card_sdiff_add_card_inter U V
  have hV :
      (((V \ U).card : ℕ) : ℝ) + (((V ∩ U).card : ℕ) : ℝ) =
        (V.card : ℝ) := by
    exact_mod_cast Finset.card_sdiff_add_card_inter V U
  have hI : ((U ∩ V).card : ℝ) = ((V ∩ U).card : ℝ) := by
    simp [Finset.inter_comm]
  have hNonnegUV : (0 : ℝ) ≤ ((U \ V).card : ℝ) := Nat.cast_nonneg _
  have hNonnegVU : (0 : ℝ) ≤ ((V \ U).card : ℝ) := Nat.cast_nonneg _
  rw [finiteMomentSupportMeasure, finiteMomentSupportMeasure,
    finiteMomentSupportDistance, abs_le]
  rw [Nat.cast_add]
  constructor <;> linarith

/--
The finite support encoding and its full moment profile both recover the
support; its counting measure obeys the symmetric-difference bound.
This theorem concerns finite combinatorial supports only. It constructs no
geometric dyadic polycube, boundary operator, or analytic Stokes theorem.
-/
theorem finiteMomentSupport_code_moment_and_measure_recovery :
    Function.Injective
      (Omega.SPG.boundaryGodelCode : Omega.SPG.FiniteMomentSupport →
        Omega.SPG.BoundaryGodelCode) ∧
    (∀ U V : Omega.SPG.FiniteMomentSupport,
      (∀ α, Omega.SPG.monomialMoment α U = Omega.SPG.monomialMoment α V) → U = V) ∧
    (∀ U V : Omega.SPG.FiniteMomentSupport,
      |finiteMomentSupportMeasure U - finiteMomentSupportMeasure V| ≤
        finiteMomentSupportDistance U V) := by
  refine ⟨Omega.SPG.boundaryGodelCode_injective, ?_, finiteMomentSupport_measure_lipschitz⟩
  intro U V h
  exact Omega.SPG.monomialMoment_profile_injective h

end Omega.Conclusion
