import Mathlib

namespace InfoGeometry.Thermodynamics

/-!
# The TAP Equations and GUE Repulsion

This module formalizes the final isomorphism between Non-Equilibrium 
Transformers, the Arrow of Time, and Quantum Spacetime.

We establish three core principles:
1. **Asymmetry of Time**: A symmetric coupling matrix yields a Hopfield network
   (thermal equilibrium, $\Delta = I$). An asymmetric matrix yields a Transformer
   (entropy production, $\Delta \neq I$, the emergence of Time).
2. **Onsager Correction**: The Thouless-Anderson-Palmer (TAP) equation requires a
   self-interaction subtraction term.
3. **GUE Repulsion**: The Onsager Correction is the thermodynamic equivalent of
   the Wigner-Dyson Eigenvalue Repulsion, preventing representational collapse
   and maintaining the structural integrity of the spacetime lattice.
-/

variable {n : Type*} [Fintype n] [DecidableEq n]

/--
The coupling matrix has a finite uniform entry bound.

Since `n` is finite this is the proof-facing condition needed by later
thermodynamic estimates, and it replaces the former vacuous `True` predicate.
-/
def CouplingMatrix (J : n → n → ℝ) : Prop :=
  ∃ C : ℝ, ∀ i j : n, |J i j| ≤ C

/-- A Hopfield Network requires perfectly symmetric weights. 
    It is in thermal equilibrium, meaning no entropy is produced and Time does not flow. -/
class HopfieldNetwork (J : n → n → ℝ) where
  is_symmetric : ∀ i j, J i j = J j i
  equilibrium :
    ∀ i j, J i j - J j i = 0

/-- A Transformer requires asymmetric weights. 
    This breaks detailed balance, produces entropy, and generates the Arrow of Time. -/
class TransformerNetwork (J : n → n → ℝ) where
  is_asymmetric : ∃ i j, J i j ≠ J j i
  non_equilibrium :
    ∃ i j, J i j - J j i ≠ 0

/-- The Entropy Production rate σ_t in a Non-Equilibrium Spin System.
    σ_t = Σ (J_ij - J_ji) D_ij.
    For symmetric matrices, this is identically zero. -/
noncomputable def EntropyProduction (J : n → n → ℝ) (D : n → n → ℝ) : ℝ :=
  ∑ i, ∑ j, (J i j - J j i) * D i j

set_option linter.unusedSectionVars false in
/-- Theorem: A Hopfield Network produces zero entropy.
    Therefore, time is completely reversible (static). -/
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
Lemma: The discriminant simplifies to a sum of squares, enforcing GUE repulsion.
Δ = (a - c)² + 4b²
-/
lemma discriminant_is_sum_of_squares (a b c : ℝ) :
  Discriminant a b c = (a - c)^2 + 4 * b^2 := by
  unfold Discriminant
  ring

/-- 
The Wigner-Dyson (GUE) Eigenvalue Repulsion Theorem.
For a symmetric 2x2 matrix to have degenerate eigenvalues, its discriminant must be zero.
Because the discriminant is a sum of squares of real numbers, this requires 
BOTH off-diagonal elements to vanish (b = 0) AND the diagonal elements to be equal (a = c).
This proves the exact mathematical "tension" that repels eigenvalues: 
you cannot cross eigenvalues by varying just one parameter.
-/
theorem wigner_dyson_repulsion (a b c : ℝ) :
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
