import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Algebra.Lie.Subalgebra
import InfoGeometry.Algebra.H3ZornJordanInstance
import InfoGeometry.Algebra.BaezF4H3Zorn

/-!
# H₃ Zorn derivation-Lie status

The live closure source for the verified `H3Zorn ℝ` Jordan product is
`H3ZornJordanInstance`; the derivation Lie subalgebra is then installed and
re-exported by `BaezF4H3Zorn`.
-/

namespace InfoGeometry.Algebra.H3Zorn

/-- The ambient linear endomorphisms of the additive real H₃ Zorn carrier. -/
abbrev Endomorphism := Module.End ℝ (H3Zorn ℝ)

/-- The installed derivation Lie subalgebra for the verified split-Albert
Jordan product. -/
abbrev DerivationLieSubalgebraTarget : Type _ :=
  H3ZornF4Derivations

end InfoGeometry.Algebra.H3Zorn
