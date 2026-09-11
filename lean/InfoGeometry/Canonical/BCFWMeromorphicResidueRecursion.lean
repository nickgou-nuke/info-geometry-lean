import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra

open scoped BigOperators

namespace InfoGeometry.Canonical

/--
A purely algebraic model of a meromorphic function with simple poles (e.g. a tree-level amplitude).
We represent the amplitude A(z) via its partial fraction decomposition:
  A(z) = ∑_i c_i / (z - z_i)
where `z_i` are the finite poles and `c_i` are the residues.
This is a finite partial-fraction model. It is not a theorem about analytic
continuation or a contour-residue recursion scheme.
-/
noncomputable def algebraicAmplitude {I : Type*} [Fintype I]
    (c z_star : I → ℂ) (z : ℂ) : ℂ :=
  ∑ i, (c i) / (z - z_star i)

/--
The algebraic residue of A(z)/z at the pole z_i.
For A(z) = c_i / (z - z_i) + ..., the function A(z)/z has residue (c_i / z_i) at z_i.
-/
noncomputable def algebraicResidueOverZ {I : Type*}
    (c z_star : I → ℂ) (i : I) : ℂ :=
  (c i) / (z_star i)

/--
Finite residue identity for the partial-fraction model.
For `A(z) = ∑_i c_i / (z - z_i)`, the value at `0` matches the negative
sum of the model residues of `A(z)/z`.
-/
theorem algebraic_residue_identity {I : Type*} [Fintype I]
    (c z_star : I → ℂ)
    (_h_poles_nonzero : ∀ i, z_star i ≠ 0) :
    algebraicAmplitude c z_star 0 = - ∑ i, algebraicResidueOverZ c z_star i := by
  dsimp [algebraicAmplitude, algebraicResidueOverZ]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have h_denom : 0 - z_star i = - z_star i := zero_sub (z_star i)
  rw [h_denom]
  rw [div_neg]

end InfoGeometry.Canonical
