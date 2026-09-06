import Omega.TypedAddressBiaxialCompletion.ComputableCertificateTemplate
import Omega.TypedAddressBiaxialCompletion.VisibleNullDichotomy
import Omega.UnitCirclePhaseArithmetic.CompletePhaseBudgetOrthogonal
import Omega.UnitCirclePhaseArithmetic.CompletePhaseReadability

namespace Omega.UnitCirclePhaseArithmetic

/-- The unit-circle compiled criterion packages readable fibers, orthogonal threshold budgets, and
the finite offline witness branch for `NULL` outputs. -/
def unit_circle_complete_phase_compiled_criterion_statement : Prop :=
  ∀ {Addr Cert Section Piece ι : Type}
    (read : Addr → Option Cert) (F : Addr → Set Cert)
    (restrict : ι → Section → Piece) (a : Addr) (locals : ι → Piece)
    (legalReadout visibleBudgetPassed registerBudgetPassed modeBudgetPassed : Prop)
    (visible_required : legalReadout → visibleBudgetPassed)
    (register_required : legalReadout → registerBudgetPassed)
    (mode_required : legalReadout → modeBudgetPassed)
    (visible_failure_obstructs :
      registerBudgetPassed → modeBudgetPassed → ¬ visibleBudgetPassed → ¬ legalReadout)
    (register_failure_obstructs :
      visibleBudgetPassed → modeBudgetPassed → ¬ registerBudgetPassed → ¬ legalReadout)
    (mode_failure_obstructs :
      visibleBudgetPassed → registerBudgetPassed → ¬ modeBudgetPassed → ¬ legalReadout)
    (offsliceAssertion explicitModeAxis nullFailureWitness noThirdPath : Prop)
    (D : Omega.TypedAddressBiaxialCompletion.ComputableCertificateTemplateData),
      (∀ a, (read a).isSome ↔ (F a).Nonempty) →
      (∃ s : Section, ∀ i : ι, restrict i s = locals i) →
      Function.Injective (fun s : Section => fun i : ι => restrict i s) →
      (offsliceAssertion → explicitModeAxis ∨ nullFailureWitness) →
      (offsliceAssertion → noThirdPath) →
      ((read a ≠ none ↔ (F a).Nonempty) ∧ ∃! s : Section, ∀ i : ι, restrict i s = locals i) ∧
        ((legalReadout → visibleBudgetPassed ∧ registerBudgetPassed ∧ modeBudgetPassed) ∧
          ((registerBudgetPassed ∧ modeBudgetPassed ∧ ¬ visibleBudgetPassed) → ¬ legalReadout) ∧
          ((visibleBudgetPassed ∧ modeBudgetPassed ∧ ¬ registerBudgetPassed) → ¬ legalReadout) ∧
          ((visibleBudgetPassed ∧ registerBudgetPassed ∧ ¬ modeBudgetPassed) → ¬ legalReadout)) ∧
        (offsliceAssertion → (explicitModeAxis ∨ nullFailureWitness) ∧ noThirdPath) ∧
        D.compilesToOfflineVerifier

/-- The compiled reader criterion is the conjunction of the readability/fiber equivalence, budget
orthogonality, and the finite offline-witness branch. -/
theorem unit_circle_complete_phase_compiled_criterion_certified :
    unit_circle_complete_phase_compiled_criterion_statement := by
  intro Addr Cert Section Piece ι read F restrict a locals legalReadout visibleBudgetPassed
    registerBudgetPassed modeBudgetPassed visible_required register_required mode_required
    visible_failure_obstructs register_failure_obstructs mode_failure_obstructs offsliceAssertion
    explicitModeAxis nullFailureWitness noThirdPath D hcompat hGlue hinj hSplit hNoThird
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact paper_unit_circle_complete_phase_readable_iff_fiber read F restrict a locals hcompat hGlue hinj
  · exact paper_unit_circle_complete_phase_budget_orthogonal
      legalReadout visibleBudgetPassed registerBudgetPassed modeBudgetPassed
      visible_required register_required mode_required visible_failure_obstructs
      register_failure_obstructs mode_failure_obstructs
  · exact
      Omega.TypedAddressBiaxialCompletion.paper_typed_address_biaxial_completion_visible_null_dichotomy
        offsliceAssertion explicitModeAxis nullFailureWitness noThirdPath hSplit hNoThird
  · exact
      (Omega.TypedAddressBiaxialCompletion.paper_typed_address_biaxial_completion_computable_certificate_template
        D).2.2.2.2

/-- Paper label: `prop:unit-circle-complete-phase-compiled-criterion`. -/
def paper_unit_circle_complete_phase_compiled_criterion : Prop := by
  exact unit_circle_complete_phase_compiled_criterion_statement

end Omega.UnitCirclePhaseArithmetic
