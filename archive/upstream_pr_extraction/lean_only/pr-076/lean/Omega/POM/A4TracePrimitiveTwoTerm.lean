import Mathlib.Tactic

namespace Omega.POM

/-- Paper-facing wrapper for the `A₄` two-term trace/primitive-orbit expansion: the trace splits
into the Perron term, the unique negative real subleading term, and a `ρ₄`-controlled remainder;
substituting this into the Möbius primitive-orbit formula and bounding all `d ≥ 2` divisors by the
`r₄^(n/2)` barrier yields the primitive two-term expansion with alternating subleading sign.
    prop:pom-a4-trace-primitive-two-term -/
theorem paper_pom_a4_trace_primitive_two_term
    (tracePerronTerm negativeSubleadingEigenvalue rho4ControlledRemainder
      mobiusPrimitiveOrbitFormula divisorTermsBoundedBySqrtPerron
      primitiveOrbitTwoTermExpansion alternatingSubleadingSign : Prop)
    (tracePerronTerm_h : tracePerronTerm)
    (negativeSubleadingEigenvalue_h : negativeSubleadingEigenvalue)
    (rho4ControlledRemainder_h : rho4ControlledRemainder)
    (mobiusPrimitiveOrbitFormula_h : mobiusPrimitiveOrbitFormula)
    (deriveDivisorTermsBoundedBySqrtPerron :
      tracePerronTerm → rho4ControlledRemainder → mobiusPrimitiveOrbitFormula →
        divisorTermsBoundedBySqrtPerron)
    (derivePrimitiveOrbitTwoTermExpansion :
      tracePerronTerm → negativeSubleadingEigenvalue → rho4ControlledRemainder →
        mobiusPrimitiveOrbitFormula → divisorTermsBoundedBySqrtPerron →
        primitiveOrbitTwoTermExpansion)
    (deriveAlternatingSubleadingSign :
      negativeSubleadingEigenvalue → primitiveOrbitTwoTermExpansion →
        alternatingSubleadingSign) :
    tracePerronTerm ∧ negativeSubleadingEigenvalue ∧ rho4ControlledRemainder ∧
      mobiusPrimitiveOrbitFormula ∧ divisorTermsBoundedBySqrtPerron ∧
      primitiveOrbitTwoTermExpansion ∧ alternatingSubleadingSign := by
  have hDivisor : divisorTermsBoundedBySqrtPerron :=
    deriveDivisorTermsBoundedBySqrtPerron tracePerronTerm_h rho4ControlledRemainder_h
      mobiusPrimitiveOrbitFormula_h
  have hPrimitive : primitiveOrbitTwoTermExpansion :=
    derivePrimitiveOrbitTwoTermExpansion tracePerronTerm_h
      negativeSubleadingEigenvalue_h rho4ControlledRemainder_h
      mobiusPrimitiveOrbitFormula_h hDivisor
  exact ⟨tracePerronTerm_h, negativeSubleadingEigenvalue_h, rho4ControlledRemainder_h,
    mobiusPrimitiveOrbitFormula_h, hDivisor, hPrimitive,
    deriveAlternatingSubleadingSign negativeSubleadingEigenvalue_h hPrimitive⟩

end Omega.POM
