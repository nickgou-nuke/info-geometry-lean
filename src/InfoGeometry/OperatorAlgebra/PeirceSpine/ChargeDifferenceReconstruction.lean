/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSpine.GolayLeechMOGSheetPoset

/-! Integral reconstruction identities for the odd charge-sector differences. -/

namespace InfoGeometry.OperatorAlgebra.PeirceSpine

variable {B : Type*} [Ring B]

theorem kantor_odd_charge_differences {P : B} (hP : P * P = P) (A C X : B) :
    (4 : ℤ) • kantorDelta1 P A C X - kantorDelta3 P A C X =
      (3 : ℤ) • (kantorGp1 P A X - kantorGm1 P C X) ∧
    kantorDelta3 P A C X - kantorDelta1 P A C X =
      (6 : ℤ) • (kantorGp2 P A X - kantorGm2 P C X) := by
  rcases kantorDelta_expansions hP A C with ⟨h₁, _, h₃, _⟩
  rw [h₁ X, h₃ X]
  constructor <;> module

/-- The charge-zero Kantor sector is recovered integrally from the total
operator and the second and fourth iterated charge commutators. -/
theorem kantor_charge_zero_reconstruction {P : B} (hP : P * P = P)
    (A C X : B) :
    (4 : ℤ) • kantorG0 P A C X =
      (4 : ℤ) • kantorTotal P A C X -
        (5 : ℤ) • kantorDelta2 P A C X + kantorDelta4 P A C X := by
  rcases kantorDelta_expansions hP A C with ⟨_, h₂, _, h₄⟩
  rw [h₂ X, h₄ X]
  unfold kantorTotal
  module

end InfoGeometry.OperatorAlgebra.PeirceSpine
