import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Thermodynamics

/-!
# TAP finite algebra and a `2 × 2` degeneracy criterion

This module contains finite algebraic facts: symmetric couplings give zero
antisymmetric entropy-production readout, the TAP cavity mean is a definition,
and a real symmetric `2 × 2` discriminant vanishes exactly when the two diagonal
entries agree and the off-diagonal entry is zero.  It does not prove a GUE
universality theorem or a spacetime/arrow-of-time theorem.
-/

variable {n : Type*} [Fintype n] [DecidableEq n]

/--
The coupling matrix has a finite uniform entry bound.

Since `n` is finite this is the proof-facing condition needed by later
thermodynamic estimates, and it replaces the former vacuous `True` predicate.
-/
def CouplingMatrix (J : n → n → ℝ) : Prop :=
  ∃ C : ℝ, ∀ i j : n, |J i j| ≤ C

/-- A Hopfield-style finite network is represented here by symmetric weights. -/
class HopfieldNetwork (J : n → n → ℝ) where
  is_symmetric : ∀ i j, J i j = J j i
  equilibrium :
    ∀ i j, J i j - J j i = 0

/-- A finite asymmetric-weight packet.  This is only an algebraic asymmetry
condition, not a theorem about transformers or time. -/
class TransformerNetwork (J : n → n → ℝ) where
  is_asymmetric : ∃ i j, J i j ≠ J j i
  non_equilibrium :
    ∃ i j, J i j - J j i ≠ 0

/-- The Entropy Production rate σ_t in a Non-Equilibrium Spin System.
    σ_t = Σ (J_ij - J_ji) D_ij.
    For symmetric matrices, this is identically zero. -/
noncomputable def EntropyProduction (J : n → n → ℝ) (D : n → n → ℝ) : ℝ :=
  ∑ i, ∑ j, (J i j - J j i) * D i j

omit [DecidableEq n] in
/-- Symmetric weights give zero antisymmetric entropy-production readout. -/
theorem hopfield_zero_entropy (J : n → n → ℝ) [h : HopfieldNetwork J] (D : n → n → ℝ) :
  EntropyProduction J D = 0 := by
  unfold EntropyProduction
  apply Finset.sum_eq_zero
  intro i _
  apply Finset.sum_eq_zero
  intro j _
  have h_symm := h.is_symmetric i j
  rw [h_symm]
  ring

/-- 
The Thouless-Anderson-Palmer (TAP) Equation for the effective mean field `a_i`.
Includes the Onsager Correction `- V_i * m_i` to prevent a spin from interacting
with its own echo.
-/
noncomputable def TAPCavityMean (J : n → n → ℝ) (m : n → ℝ) (V : n → ℝ) (i : n) : ℝ :=
  (∑ j, J i j * m j) - V i * m i

/-- 
A 2x2 real symmetric matrix representing the local coupling or energy.
-/
def Symmetric2x2 (a b c : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  ![![a, b],
    ![b, c]]

/-- 
The discriminant of the characteristic polynomial of a 2x2 symmetric matrix.
Δ = (tr M)² - 4 * det M
-/
def Discriminant (a b c : ℝ) : ℝ :=
  (a + c)^2 - 4 * (a * c - b^2)

/-- 
Lemma: the discriminant simplifies to a sum of squares.
Δ = (a - c)² + 4b²
-/
lemma discriminant_is_sum_of_squares (a b c : ℝ) :
  Discriminant a b c = (a - c)^2 + 4 * b^2 := by
  unfold Discriminant
  ring

/-- 
Degeneracy criterion for the displayed real symmetric `2 × 2` matrix.
Its discriminant vanishes exactly when the diagonal entries agree and the
off-diagonal entry is zero.  This is a finite linear-algebra statement, not a
random-matrix universality theorem.
-/
theorem symmetric2x2_discriminant_zero_iff (a b c : ℝ) :
  Discriminant a b c = 0 ↔ a = c ∧ b = 0 := by
  rw [discriminant_is_sum_of_squares]
  constructor
  · intro h
    -- Sum of two non-negative squares is zero iff both are zero.
    have h1 : 0 ≤ (a - c)^2 := sq_nonneg (a - c)
    have h2 : 0 ≤ 4 * b^2 := by positivity
    have h3 : (a - c)^2 = 0 := by linarith
    have h4 : 4 * b^2 = 0 := by linarith
    constructor
    · exact sub_eq_zero.mp (sq_eq_zero_iff.mp h3)
    · exact sq_eq_zero_iff.mp (by linarith)
  · intro h
    rcases h with ⟨h_ac, h_b⟩
    rw [h_ac, h_b]
    ring

end InfoGeometry.Thermodynamics
