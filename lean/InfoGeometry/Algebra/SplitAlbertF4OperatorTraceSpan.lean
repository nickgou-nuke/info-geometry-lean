import InfoGeometry.Algebra.SplitAlbertF4BasisTrace
import InfoGeometry.Algebra.SplitAlbertDerivationOperatorTrace

/-!
# Native operator-trace readout on the explicit split-Albert `F₄` span

This bridge transports the existing explicit `f4BasisSpan` inclusion into the
native finite-dimensional operator-trace theorem.  It does not claim that the
explicit span is all of `H3ZornF4Derivations`, nor does it identify the scalar
Jordan trace with the operator trace.
-/

namespace InfoGeometry.Algebra

open H3Zorn

theorem f4BasisSpan_jordanLmul_operatorTrace_zero
    {D : Module.End ℝ (H3Zorn ℝ)}
    (hD : D ∈ f4BasisSpan) (x : H3Zorn ℝ) :
    LinearMap.trace ℝ (H3Zorn ℝ)
      (jordanLmul (R := ℝ) (D x)) = 0 := by
  have hD' : D ∈ H3ZornF4Derivations := f4BasisSpan_le_F4Derivations hD
  exact h3ZornF4_derivation_jordanLmul_operatorTrace_zero ⟨D, hD'⟩ x

theorem f4BasisSpan_apply_one_eq_zero
    {D : Module.End ℝ (H3Zorn ℝ)}
    (hD : D ∈ f4BasisSpan) :
    D (1 : H3Zorn ℝ) = 0 := by
  have hD' : D ∈ H3ZornF4Derivations := f4BasisSpan_le_F4Derivations hD
  exact h3ZornF4_derivation_apply_one_eq_zero ⟨D, hD'⟩

end InfoGeometry.Algebra
