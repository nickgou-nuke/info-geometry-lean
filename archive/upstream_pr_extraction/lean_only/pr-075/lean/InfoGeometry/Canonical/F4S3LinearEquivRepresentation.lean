import InfoGeometry.Algebra.F4Derivations
import InfoGeometry.Algebra.H3ZornTopologicalReadout

/-!
# The bundled linear representation of the Peirce `S₃` action

`S3Perm.comp` is oriented as “first `σ`, then `τ`”.  The multiplication on
`LinearEquiv` is ordinary function composition, so the native action is an
antihomomorphism into the automorphism group.  Equivalently, it is a genuine
monoid homomorphism into the opposite group.
-/

namespace InfoGeometry.Algebra

open H3Zorn

noncomputable section

abbrev S3LinearEquiv := H3Zorn ℝ ≃ₗ[ℝ] H3Zorn ℝ

/-- The `S₃` action as a bundled monoid homomorphism into the opposite
automorphism group. -/
def S3OnH3ZornLinearEquivOpHom : S3Perm →* MulOpposite S3LinearEquiv where
  toFun σ := MulOpposite.op (S3OnH3ZornLinearEquiv σ)
  map_one' := by
    apply MulOpposite.unop_injective
    apply LinearEquiv.ext
    intro X
    change S3OnH3Zorn S3Perm.id X = X
    rfl
  map_mul' σ τ := by
    apply MulOpposite.unop_injective
    apply LinearEquiv.ext
    intro X
    change S3OnH3Zorn (S3Perm.comp σ τ) X =
      S3OnH3Zorn τ (S3OnH3Zorn σ X)
    exact congrFun (S3OnH3Zorn_comp σ τ) X

@[simp] theorem S3OnH3ZornLinearEquivOpHom_apply (σ : S3Perm) :
    S3OnH3ZornLinearEquivOpHom σ =
      MulOpposite.op (S3OnH3ZornLinearEquiv σ) :=
  rfl

/-- In the ordinary automorphism group, the same law is anti-multiplicative. -/
theorem S3OnH3ZornLinearEquiv_antihom (σ τ : S3Perm) :
    S3OnH3ZornLinearEquiv (S3Perm.comp σ τ) =
      S3OnH3ZornLinearEquiv τ * S3OnH3ZornLinearEquiv σ := by
  apply LinearEquiv.ext
  intro X
  change S3OnH3Zorn (S3Perm.comp σ τ) X =
    S3OnH3Zorn τ (S3OnH3Zorn σ X)
  exact congrFun (S3OnH3Zorn_comp σ τ) X

end
end InfoGeometry.Algebra
