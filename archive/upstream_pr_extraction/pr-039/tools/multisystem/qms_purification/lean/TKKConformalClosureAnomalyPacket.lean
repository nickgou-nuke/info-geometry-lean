import InfoGeometry.OperatorAlgebra.TKKConformalClosure

/-!
QMS isolated proof target for theorem-honest normalization of the TKK/anomaly
narrative.

Mathematical context:
- `L` is a real Lie algebra.
- `G : TKKThreeGrading L` supplies three explicit graded submodules:
  `gMinus`, `gZero`, and `gPlus`.
- The owner structure carries bracket laws:
  1. if `Xm Ym ∈ gMinus`, then `⁅Xm, Ym⁆ = 0`;
  2. if `Xp Yp ∈ gPlus`, then `⁅Xp, Yp⁆ = 0`;
  3. if `Xm ∈ gMinus` and `Xp ∈ gPlus`, then `⁅Xm, Xp⁆ ∈ gZero`.

Existing mathlib/literature context:
- Mathlib supplies the Lie bracket notation and submodule membership.
- Classical Tits--Kantor--Koecher/Kantor--Koecher--Tits constructions obtain
  graded Lie algebras from Jordan pairs/triples under explicit algebraic
  hypotheses. This file does not construct those hypotheses from Cl(1,1)
  atoms or tensor products.

QMS purification move:
- The valid finite theorem is a readback from the supplied graded-bracket laws.
- It does not assert continuum anomaly cancellation, fluid/JKO emergence, or
  Amplituhedron volume identities.
-/

namespace InfoGeometry.QMS.TKKConformalClosureAnomalyPacket

open InfoGeometry.OperatorAlgebra.TKKConformalClosure

variable {L : Type*} [AddCommGroup L] [Module ℝ L] [LieRing L] [LieAlgebra ℝ L]

/-- Same-arrow TKK brackets vanish and the mixed outer bracket lands in grade zero. -/
theorem same_arrow_and_mixed_grade_anomaly_packet
    (G : TKKThreeGrading L)
    {Xm Ym Xp Yp : L}
    (hXm : Xm ∈ G.gMinus) (hYm : Ym ∈ G.gMinus)
    (hXp : Xp ∈ G.gPlus) (hYp : Yp ∈ G.gPlus) :
    ⁅Xm, Ym⁆ = 0 ∧ ⁅Xp, Yp⁆ = 0 ∧ ⁅Xm, Xp⁆ ∈ G.gZero := by
  exact ⟨G.minus_minus_eq_zero hXm hYm,
    G.plus_plus_eq_zero hXp hYp,
    G.minus_plus_mem_zero hXm hXp⟩

end InfoGeometry.QMS.TKKConformalClosureAnomalyPacket
