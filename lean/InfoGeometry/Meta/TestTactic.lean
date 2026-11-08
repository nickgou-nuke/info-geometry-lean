import InfoGeometry.Meta.DvorakTactics
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Meta

theorem test_aeply (P Q : Prop) : (P → Q) → P → Q := by
  intro h hp
  aeply h
  exact h hp

end InfoGeometry.Meta
