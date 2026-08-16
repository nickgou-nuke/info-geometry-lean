import Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal
import Mathlib.Tactic

/-!
# Operator Itakura--Saito and Araki relative entropy

This owner is stated on a genuine noncommutative C*-algebra.  A positive
linear functional is the state/readout, while `Delta` and `logDelta` remain
elements of the algebra; no diagonal matrix model or commuting spectral
assumption is introduced.

The theorem below is the algebraic cancellation behind the bounded
Itakura--Saito/Araki comparison.  It does not construct an unbounded
Tomita--Takesaki logarithm or assert that an arbitrary pair of algebra
elements is a relative modular operator.  Those analytic hypotheses belong to
the standard-form/modular owners.
-/

noncomputable section

open scoped ComplexOrder

namespace InfoGeometry.Canonical.ArakiItakuraSaitoEquivalence

variable {A : Type*} [CStarAlgebra A] [PartialOrder A]

/-! ## Native noncommutative operators and positive readout -/

/-- The operator-valued Itakura--Saito expression `Delta - log Delta - 1`. -/
def operatorItakuraSaito (Delta logDelta : A) : A :=
  Delta - logDelta - 1

/-- Araki's relative-entropy readout for a supplied logarithmic modular datum. -/
def arakiRelativeEntropy (phi : A →ₚ[ℂ] ℂ) (logDelta : A) : ℂ :=
  -phi logDelta

/-!
## The cancellation theorem on the noncommutative carrier

Only the normalization of the positive functional on `Delta` and on the unit
is used.  No commutation of `Delta` and `logDelta` is needed.
-/

theorem itakuraSaito_expectation_eq_araki
    (phi : A →ₚ[ℂ] ℂ) (Delta logDelta : A)
    (h_delta : phi Delta = phi 1) :
    phi (operatorItakuraSaito Delta logDelta) =
      arakiRelativeEntropy phi logDelta := by
  unfold operatorItakuraSaito arakiRelativeEntropy
  rw [map_sub, map_sub, h_delta]
  simp

/-- Normalized-state specialization of the cancellation theorem. -/
theorem itakuraSaito_expectation_eq_araki_of_state
    (phi : A →ₚ[ℂ] ℂ) (Delta logDelta : A)
    (h_phi_one : phi 1 = 1)
    (h_delta : phi Delta = 1) :
    phi (operatorItakuraSaito Delta logDelta) =
      arakiRelativeEntropy phi logDelta := by
  apply itakuraSaito_expectation_eq_araki phi Delta logDelta
  simpa [h_phi_one] using h_delta

/--
Scaling the modular element and shifting its logarithmic datum is still an
algebraic statement on the positive-functional readout.  It is deliberately
separate from any claim that `c • Delta` has logarithm
`logDelta + logc • 1`.
-/
theorem itakuraSaito_expectation_scale_shift
    (phi : A →ₚ[ℂ] ℂ) (Delta logDelta : A) (c logc : ℂ)
    (h_delta : phi Delta = phi 1) :
    phi (operatorItakuraSaito (c • Delta)
      (logDelta + logc • (1 : A))) =
      (c - logc - 1) * phi 1 +
        phi (operatorItakuraSaito Delta logDelta) := by
  unfold operatorItakuraSaito
  rw [map_sub, map_sub, map_add, map_smul, map_sub, map_sub]
  rw [h_delta]
  simp
  ring

end InfoGeometry.Canonical.ArakiItakuraSaitoEquivalence

end noncomputable section
