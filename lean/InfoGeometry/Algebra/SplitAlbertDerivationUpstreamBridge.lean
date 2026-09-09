import InfoGeometry.Algebra.SplitAlbertDerivationOperatorTrace
import InfoGeometry.Algebra.H3ZornCarrierBasis

/-! Compatibility bridge for the upstream universal split-Albert derivation
adapter.  The scalar identity relating operator trace to `linearTrace` is
intentionally not asserted here; it remains a separate basis computation. -/

noncomputable section
namespace InfoGeometry.Algebra

open H3Zorn

noncomputable def bundledF4Derivation
    (D : H3ZornF4Derivations) :
    NonAssocDerivation.derivations ℝ (H3Zorn ℝ) :=
  ⟨D.1, D.2⟩

@[simp] theorem bundledF4Derivation_coe (D : H3ZornF4Derivations) :
    (bundledF4Derivation D : Module.End ℝ (H3Zorn ℝ)) = D.1 := rfl

theorem bundledF4Derivation_operatorTrace_zero
    (D : H3ZornF4Derivations) (x : H3Zorn ℝ) :
    LinearMap.trace ℝ (H3Zorn ℝ)
      (jordanLmul (R := ℝ) (D.1 x)) = 0 := by
  simpa using h3Zorn_derivation_jordanLmul_operatorTrace_zero
    (bundledF4Derivation D) x

end InfoGeometry.Algebra
