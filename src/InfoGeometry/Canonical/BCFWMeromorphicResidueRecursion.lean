import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra

open scoped BigOperators

namespace InfoGeometry.Canonical

/--
A finite partial-fraction expression built from coefficients `c` and shifts
`z_star`. No distinctness or nonzero-pole conditions are imposed, so this
definition alone does not assert that the summands are a meromorphic function
with simple poles and analytic residues.
-/
noncomputable def algebraicAmplitude {I : Type*} [Fintype I]
    (c z_star : I → ℂ) (z : ℂ) : ℂ :=
  ∑ i, (c i) / (z - z_star i)

/-- The rational coefficient `c i / z_star i` used in the finite algebraic
identity below. It is not defined as an analytic residue. -/
noncomputable def algebraicResidueOverZ {I : Type*}
    (c z_star : I → ℂ) (i : I) : ℂ :=
  (c i) / (z_star i)

/-- Finite algebraic identity for the displayed partial-fraction expression.
This equality uses totalized complex division and makes no analytic residue
claim. -/
theorem algebraic_residue_identity {I : Type*} [Fintype I]
    (c z_star : I → ℂ) :
    algebraicAmplitude c z_star 0 = - ∑ i, algebraicResidueOverZ c z_star i := by
  dsimp [algebraicAmplitude, algebraicResidueOverZ]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have h_denom : 0 - z_star i = - z_star i := zero_sub (z_star i)
  rw [h_denom]
  rw [div_neg]

end InfoGeometry.Canonical
