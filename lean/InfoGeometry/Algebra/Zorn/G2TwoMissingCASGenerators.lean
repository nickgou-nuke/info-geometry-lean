import InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem

namespace InfoGeometry.Algebra.Zorn.G2TwoMissingCASGenerators

open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem

/-! Coordinate formulas exported by the carrier-level CAS search for the two
generators which are not words in the existing Weyl/Levi owners. -/

def g₂ (X : SplitOctF2) : SplitOctF2 :=
  ⟨add2 (add2 X.b X.x2) X.y0,
    add2 (add2 X.a X.x2) X.y0,
    add2 (add2 X.a X.b) (add2 X.x1 X.x2) |> fun z => add2 z X.y2,
    add2 X.x2 X.y1,
    X.y0,
    X.x2,
    add2 X.x1 X.y0,
    add2 (add2 (add2 (add2 (add2 X.a X.b) X.x0) X.x2) X.y0) X.y1⟩

def g₄ (X : SplitOctF2) : SplitOctF2 :=
  ⟨add2 (add2 (add2 X.a X.x2) X.y0) X.y1,
    add2 (add2 (add2 X.b X.x2) X.y0) X.y1,
    add2 (add2 (add2 (add2 (add2 X.a X.b) X.x0) X.x1) X.x2) X.y1,
    add2 (add2 X.x1 X.x2) X.y0,
    X.x2,
    X.y0,
    add2 (add2 X.x2 X.y0) X.y1,
    add2 (add2 (add2 (add2 (add2 X.a X.b) X.x1) X.y0) X.y1) X.y2⟩

theorem g₂_add (X Y : SplitOctF2) :
    g₂ (add X Y) = add (g₂ X) (g₂ Y) := by
  rcases X with ⟨a, b, x0, x1, x2, y0, y1, y2⟩
  rcases Y with ⟨a', b', x0', x1', x2', y0', y1', y2'⟩
  ext <;> dsimp [g₂, add, add2]
  all_goals ac_rfl

theorem g₄_add (X Y : SplitOctF2) :
    g₄ (add X Y) = add (g₄ X) (g₄ Y) := by
  rcases X with ⟨a, b, x0, x1, x2, y0, y1, y2⟩
  rcases Y with ⟨a', b', x0', x1', x2', y0', y1', y2'⟩
  ext <;> dsimp [g₄, add, add2]
  all_goals ac_rfl

theorem g₂_involutive (X : SplitOctF2) : g₂ (g₂ X) = X := by
  rcases X with ⟨a, b, x0, x1, x2, y0, y1, y2⟩
  ext <;> dsimp [g₂, add2]
  all_goals ac_rfl

theorem g₄_involutive (X : SplitOctF2) : g₄ (g₄ X) = X := by
  rcases X with ⟨a, b, x0, x1, x2, y0, y1, y2⟩
  ext <;> dsimp [g₄, add2]
  all_goals ac_rfl

end InfoGeometry.Algebra.Zorn.G2TwoMissingCASGenerators
