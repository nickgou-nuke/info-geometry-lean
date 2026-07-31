namespace Omega.OperatorAlgebra

/-- The restricted-Bell dimension formula and the exponential-generating-function input yield
the even exponential generating function. -/
theorem paper_op_algebra_replication_centralizer_dimension_egf
    (orbitAlgebraDimensionInput exponentialGeneratingFunctionInput
      dimensionClosedForm evenExponentialGeneratingFunction : Prop)
    (orbitAlgebraDimensionInput_h : orbitAlgebraDimensionInput)
    (exponentialGeneratingFunctionInput_h : exponentialGeneratingFunctionInput)
    (deriveDimensionClosedForm :
      orbitAlgebraDimensionInput → dimensionClosedForm)
    (deriveEvenExponentialGeneratingFunction :
      dimensionClosedForm → exponentialGeneratingFunctionInput →
        evenExponentialGeneratingFunction) :
    dimensionClosedForm ∧ evenExponentialGeneratingFunction := by
  have hClosed : dimensionClosedForm :=
    deriveDimensionClosedForm orbitAlgebraDimensionInput_h
  exact ⟨hClosed,
    deriveEvenExponentialGeneratingFunction hClosed exponentialGeneratingFunctionInput_h⟩

end Omega.OperatorAlgebra
