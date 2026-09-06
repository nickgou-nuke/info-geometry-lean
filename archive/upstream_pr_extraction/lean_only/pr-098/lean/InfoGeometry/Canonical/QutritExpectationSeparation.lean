import InfoGeometry.Canonical.QutritSU3AdjointDecomposition

/-!
# Expectation separation for the qutrit operator space

The nine trace pairings against the Gell--Mann family form a complete
observable readout of `M₃(ℂ)`.  This is a finite algebraic statement: it does
not identify an arbitrary physical state with these coordinates, nor does it
claim that a smaller selected set of observables is separating.
-/

noncomputable section

namespace InfoGeometry.Canonical.QutritExpectationSeparation

open Matrix
open InfoGeometry.Canonical.QutritGellMannOperatorBasis
open InfoGeometry.Canonical.QutritSU3AdjointDecomposition

abbrev QutritMatrix := Matrix (Fin 3) (Fin 3) ℂ

/-! ## The complete bilinear expectation readout -/

/-- The nine trace-bilinear expectations against the Gell--Mann family. -/
def expectationReadout : QutritMatrix →ₗ[ℂ] (Fin 9 → ℂ) :=
  { toFun := fun A r => Matrix.trace ((gellMannFamily r)ᴴ * A)
    map_add' := by
      intro A B
      funext r
      simp [Matrix.mul_add, Matrix.trace_add]
    map_smul' := by
      intro c A
      funext r
      simp [Matrix.mul_smul, Matrix.trace_smul] }

@[simp] theorem expectationReadout_apply (A : QutritMatrix) (r : Fin 9) :
    expectationReadout A r =
      Matrix.trace ((gellMannFamily r)ᴴ * A) := rfl

theorem expectationReadout_reconstruction (A : QutritMatrix) :
    ∑ r : Fin 9,
        ((gramWeight r)⁻¹ * expectationReadout A r) • gellMannFamily r = A := by
  simpa [expectationReadout] using gellMann_trace_reconstruction A

/-- The complete nine-channel expectation readout separates operators. -/
theorem expectationReadout_injective :
    Function.Injective expectationReadout := by
  intro A B h
  rw [← expectationReadout_reconstruction A, ← expectationReadout_reconstruction B]
  apply Finset.sum_congr rfl
  intro r hr
  rw [h]

theorem expectationReadout_eq_iff (A B : QutritMatrix) :
    expectationReadout A = expectationReadout B ↔ A = B := by
  constructor
  · exact fun h => expectationReadout_injective h
  · intro h
    rw [h]

end InfoGeometry.Canonical.QutritExpectationSeparation

end noncomputable section
