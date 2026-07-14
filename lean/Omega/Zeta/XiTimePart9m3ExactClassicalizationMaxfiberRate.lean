namespace Omega.Zeta

/-- Paper label: `cor:xi-time-part9m3-exact-classicalization-maxfiber-rate`. -/
theorem paper_xi_time_part9m3_exact_classicalization_maxfiber_rate
    (exactBudget asymptoticRate : Prop) (hExact : exactBudget) (hRate : asymptoticRate) :
    exactBudget ∧ asymptoticRate := by
  exact ⟨hExact, hRate⟩

end Omega.Zeta
