import InfoGeometry.Canonical.SplitG2AlbertEntrywiseBridge

/-! Native compatibility surface for the upstream entrywise-lift path.

Only the statements owned by the current bridge are exported here.  In
particular, no Jordan-product preservation or injectivity is inferred merely
from entrywise action. -/
namespace InfoGeometry.Canonical.SplitG2AlbertEntrywiseLift

noncomputable section

open InfoGeometry.Algebra
open InfoGeometry.Algebra.H3Zorn
open InfoGeometry.Lie.CanonicalZornDerivation
open InfoGeometry.Canonical.SplitG2AlbertEntrywiseBridge

abbrev G2Der := canonicalZornDerivations
abbrev H3 := H3Zorn ℝ
abbrev EndH3 := Module.End ℝ H3

noncomputable abbrev liftG2End (D : G2Der) : EndH3 := lift D

theorem liftG2End_annihilates_diag₁ (D : G2Der) (X : H3) :
    (liftG2End D X).α₁ = 0 := by rfl

theorem liftG2End_annihilates_diag₂ (D : G2Der) (X : H3) :
    (liftG2End D X).α₂ = 0 := by rfl

theorem liftG2End_annihilates_diag₃ (D : G2Der) (X : H3) :
    (liftG2End D X).α₃ = 0 := by rfl

end
end InfoGeometry.Canonical.SplitG2AlbertEntrywiseLift
