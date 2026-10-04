import InfoGeometry.Algebra.BaezG2AlternativeDerivations

/-!
# Split-octonion derivations and the idempotent locus

The real split-octonion carrier is the concrete Kingdon/Zorn algebra. Its
Baez derivations satisfy the Leibniz rule. Consequently, at an idempotent,
their value satisfies the linearized idempotent equation. This is the precise
algebraic relation to Peirce geometry established here; no twistor action,
Dirac–Kähler operator, or exceptional Lie-group identification is asserted.
-/

namespace InfoGeometry.Canonical.SplitOctonionTwistorDiracKahler

open InfoGeometry.Canonical.ZornVectorMatrixExplicit.KingdonSplitOctonion

/-- A derivation evaluated at an idempotent lies in the tangent equation
`d = d*e + e*d` obtained by differentiating `e*e = e`. -/
theorem baezSplitDerivation_tangent_idempotent
    (x y e : AbstractKingdon) (he : e * e = e) :
    baezSplitDerivation x y e =
      baezSplitDerivation x y e * e + e * baezSplitDerivation x y e := by
  have h := (baezSplitDerivation x y).leibniz e e
  rw [he] at h
  exact h

end InfoGeometry.Canonical.SplitOctonionTwistorDiracKahler
