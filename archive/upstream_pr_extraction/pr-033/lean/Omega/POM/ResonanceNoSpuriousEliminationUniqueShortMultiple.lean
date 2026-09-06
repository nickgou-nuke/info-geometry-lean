import Mathlib.Tactic
import Omega.POM.ResonanceHankelNullIntegralPrincipalization

namespace Omega.POM

/-- Padding of a short coefficient vector to length `n`. -/
def resonanceExtendShort (degreeGap n : ℕ) (Q : Fin degreeGap → ℤ) :
    Fin n → ℤ :=
  fun i => if h : i.1 < degreeGap then Q ⟨i.1, h⟩ else 0

/-- The coefficient vector `Q` is a valid short multiple when principalization places `B` in the
multiple module and the padded coefficients recover `B`. -/
def resonanceIsShortMultiple
    {degreeGap n : ℕ} (Bcoeffs : Fin n → ℤ)
    (multipleModule : Set (Fin n → ℤ)) (Q : Fin degreeGap → ℤ) : Prop :=
  Bcoeffs ∈ multipleModule ∧ resonanceExtendShort degreeGap n Q = Bcoeffs

/-- Paper conclusion: there is a unique short coefficient vector whose padded coefficients recover
`B`. -/
lemma resonanceExtendShort_injective
    (degreeGap n : ℕ) (hgap : degreeGap ≤ n) :
    Function.Injective (resonanceExtendShort degreeGap n) := by
  intro Q₁ Q₂ hQ
  ext i
  have hEval := congrArg (fun f => f ⟨i.1, lt_of_lt_of_le i.is_lt hgap⟩) hQ
  simpa [resonanceExtendShort, i.is_lt] using hEval


/-- Paper label: `cor:pom-resonance-no-spurious-elimination-unique-short-multiple`. -/
theorem paper_pom_resonance_no_spurious_elimination_unique_short_multiple
    {n : ℕ}
    (nullModeKernel squareKernel multipleModule : Set (Fin n → ℤ))
    (nullMode_eq_squareKernel : nullModeKernel = squareKernel)
    (squareKernel_subset_multipleModule : squareKernel ⊆ multipleModule)
    (multipleModule_subset_squareKernel : multipleModule ⊆ squareKernel)
    (degreeGap : ℕ) (hgap : degreeGap ≤ n)
    (Bcoeffs : Fin n → ℤ)
    (nullmodeCoeff : Bcoeffs ∈ nullModeKernel)
    (witness : Fin degreeGap → ℤ)
    (witness_eq_Bcoeffs :
      (fun i : Fin n =>
        if h : i.1 < degreeGap then witness ⟨i.1, h⟩ else 0) = Bcoeffs) :
    ∃! Q : Fin degreeGap → ℤ,
      resonanceIsShortMultiple Bcoeffs multipleModule Q := by
  have hPrincipal : nullModeKernel = multipleModule :=
    paper_pom_resonance_hankel_null_integral_principalization
      nullModeKernel squareKernel multipleModule nullMode_eq_squareKernel
      squareKernel_subset_multipleModule
      multipleModule_subset_squareKernel
  have hBmultiple : Bcoeffs ∈ multipleModule := by
    simpa [hPrincipal] using nullmodeCoeff
  refine ⟨witness, ?_, ?_⟩
  · exact ⟨hBmultiple, by simpa [resonanceIsShortMultiple, resonanceExtendShort] using witness_eq_Bcoeffs⟩
  · intro Q hQ
    exact resonanceExtendShort_injective degreeGap n hgap
      (hQ.2.trans witness_eq_Bcoeffs.symm)

end Omega.POM
