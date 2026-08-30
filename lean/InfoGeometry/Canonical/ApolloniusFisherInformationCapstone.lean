import InfoGeometry.Quantum.ApolloniusFisherInformation

namespace InfoGeometry.Canonical.ApolloniusFisherInformationCapstone

open InfoGeometry.Quantum.ApolloniusFisherInformation

set_option linter.unusedVariables false

theorem verification_capstone
    (st : ApolloniusState) (v : Fin 2 → ℝ) (hv : v ≠ 0)
    (t : ℝ) (ht : t ≠ 0) :
    (0 < apolloniusFisherQuadraticForm st v) ∧
      ((apolloniusFisherMatrix st).det =
        1 / ((st.sigma - 1 / 2) ^ 2 + st.t ^ 2) ^ 2) ∧
      (Real.log (apolloniusFisherMatrix st).det =
        -2 * Real.log ((st.sigma - 1 / 2) ^ 2 + st.t ^ 2)) ∧
      (let st_crit : ApolloniusState := ⟨1 / 2, t, by
         have h : (1 / 2 - 1 / 2 : ℝ) ^ 2 + t ^ 2 = t ^ 2 := by ring
         rw [h]
         exact sq_pos_of_ne_zero ht⟩
       apolloniusFisherMatrix st_crit 0 0 = 1 / t ^ 2) := by
  exact grand_apollonius_fisher_information_synthesis st v hv t ht

end InfoGeometry.Canonical.ApolloniusFisherInformationCapstone
