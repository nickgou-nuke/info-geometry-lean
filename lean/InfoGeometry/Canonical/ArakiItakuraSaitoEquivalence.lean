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

section Ring

variable {A : Type*} [Ring A]

/-- The operator-valued Itakura--Saito expression `Delta - log Delta - 1`. -/
def operatorItakuraSaito (Delta logDelta : A) : A :=
  Delta - logDelta - 1

/-- Centered form of the operatorial Itakura--Saito deviance. -/
theorem operatorItakuraSaito_eq_centered (Delta logDelta : A) :
    operatorItakuraSaito Delta logDelta = (Delta - 1) - logDelta := by
  unfold operatorItakuraSaito
  abel

/-- The complement of a relative modular element is its perturbation from the unit. -/
theorem relative_complement_eq_perturbation
    (Delta X : A) (hDelta : Delta = 1 + X) :
    Delta - 1 = X := by
  rw [hDelta]
  abel

/-- Centered Itakura--Saito form in a supplied perturbation coordinate. -/
theorem operatorItakuraSaito_eq_perturbation_sub_log
    (Delta logDelta X : A) (hDelta : Delta = 1 + X) :
    operatorItakuraSaito Delta logDelta = X - logDelta := by
  rw [operatorItakuraSaito_eq_centered,
    relative_complement_eq_perturbation Delta X hDelta]

/-- Explicit modular-Hamiltonian readout. -/
theorem operatorItakuraSaito_eq_delta_sub_one_add_hamiltonian
    (Delta logDelta K : A) (hK : logDelta = -K) :
    operatorItakuraSaito Delta logDelta = Delta - 1 + K := by
  unfold operatorItakuraSaito
  rw [hK]
  abel

end Ring

section CStar

variable {A : Type*} [CStarAlgebra A] [PartialOrder A]

/-- A normalized linear readout annihilates the relative complement. -/
theorem complement_expectation_eq_zero
    (phi : A →ₚ[ℂ] ℂ) (Delta : A)
    (hDelta : phi Delta = phi 1) :
    phi (Delta - 1) = 0 := by
  rw [map_sub, hDelta]
  simp

/-- Araki's relative-entropy readout for a supplied logarithmic modular datum. -/
def arakiRelativeEntropy (phi : A →ₚ[ℂ] ℂ) (logDelta : A) : ℂ :=
  -phi logDelta

/-- The cancellation theorem on the noncommutative carrier. -/
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

/-- Scaling the modular element and shifting its logarithmic datum. -/
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

end CStar

section HilbertSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The Hilbert space operator Itakura-Saito Divergence: Δ - log(Δ) - I -/
def operatorItakuraSaitoHilbert (Delta logDelta : H →L[ℂ] H) : H →L[ℂ] H :=
  Delta - logDelta - ContinuousLinearMap.id ℂ H

/-- The Hilbert space Araki Relative Entropy on a vacuum vector. -/
def arakiRelativeEntropyVector (logDelta : H →L[ℂ] H) (Ω : H) : ℂ :=
  - inner ℂ Ω (logDelta Ω)

/-- Vacuum vector expectation value collapse. -/
theorem itakuraSaito_vector_expectation_eq_araki
    (Delta logDelta : H →L[ℂ] H) (Ω : H)
    (h_delta_vacuum : inner ℂ Ω (Delta Ω) = 1)
    (h_norm_vacuum : inner ℂ Ω Ω = 1) :
    inner ℂ Ω (operatorItakuraSaitoHilbert Delta logDelta Ω) = arakiRelativeEntropyVector logDelta Ω := by
  unfold operatorItakuraSaitoHilbert arakiRelativeEntropyVector
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply]
  rw [inner_sub_right, inner_sub_right]
  rw [h_delta_vacuum, h_norm_vacuum]
  ring

end HilbertSpace

end InfoGeometry.Canonical.ArakiItakuraSaitoEquivalence
