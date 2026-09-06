import InfoGeometry.Algebra.BaezF4H3Zorn
import InfoGeometry.Algebra.SplitAlbertInnerTraceSpan

/-!
# Trace-zero readout for the explicit split-Albert `F₄` basis

This owner records the pointwise trace statement for the explicit basis
provided by `BaezF4H3Zorn`.  It deliberately does not identify the span of
that basis with all of `H3ZornF4Derivations`; that generation theorem remains
a separate obligation.
-/

namespace InfoGeometry.Algebra

open H3Zorn

def f4BasisSpan : Submodule ℝ (Module.End ℝ (H3Zorn ℝ)) :=
  Submodule.span ℝ
    (Set.range (fun i : Fin 52 => (f4Basis i).1))

theorem f4Basis_linearTrace_zero (i : Fin 52) (x : H3Zorn ℝ) :
    linearTrace ((f4Basis i).1 x) = 0 := by
  fin_cases i <;>
    change linearTrace
      ((h3ZornJordanInnerDerivation _ _ : Module.End ℝ (H3Zorn ℝ)) x) = 0 <;>
    exact h3ZornJordanInnerDerivation_linearTrace_zero _ _ x

theorem f4BasisSpan_le_traceZero :
    f4BasisSpan ≤ h3ZornTraceZeroEndomorphisms := by
  intro D hD
  refine Submodule.span_induction
    (p := fun T _ => T ∈ h3ZornTraceZeroEndomorphisms)
    ?_ ?_ ?_ ?_ hD
  · rintro T ⟨i, rfl⟩
    exact f4Basis_linearTrace_zero i
  · exact h3ZornTraceZeroEndomorphisms.zero_mem
  · intro T U _ _ hT hU
    exact h3ZornTraceZeroEndomorphisms.add_mem hT hU
  · intro r T _ hT
    exact h3ZornTraceZeroEndomorphisms.smul_mem r hT

end InfoGeometry.Algebra
