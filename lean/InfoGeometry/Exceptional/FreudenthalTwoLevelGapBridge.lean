import InfoGeometry.Exceptional.FreudenthalFiveGradedLieClosure
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Data.Real.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.Ring

noncomputable section

open Matrix InfoGeometry.Exceptional.Freudenthal

namespace InfoGeometry.Exceptional.Freudenthal

variable {J : Type*} [AddCommGroup J] [Module ℝ J]
variable (D : CubicJordanDatum J)

abbrev Mat2 := InfoGeometry.Algebra.FiniteSpin.Mat2R
abbrev Vec2 := Fin 2 → ℝ

/-!
# Native Freudenthal Mixed Bracket to Two-Level Spectral Gap Bridge

This module establishes the exact, kernel-checked bridge between:
1. **The Native Freudenthal 5-Graded Mixed Bracket**:
   $[\mathfrak{g}_{-1}, \mathfrak{g}_{+1}] \subseteq \mathfrak{g}_0$, where the grade $0$ scale component is $\omega(X, Y) \in \mathbb{R}$.
2. **The Explicit Symmetric Two-Level Hamiltonian**:
   $\mathcal{H}_{X, Y}(E_0) = \begin{pmatrix} E_0 & \omega(X, Y) \\ \omega(X, Y) & E_0 \end{pmatrix}$.
3. **Explicit Symmetric / Antisymmetric Eigenmodes**:
   $\mathcal{H}_{X, Y} |+\rangle = (E_0 + \omega(X, Y)) |+\rangle$,
   $\mathcal{H}_{X, Y} |-\rangle = (E_0 - \omega(X, Y)) |-\rangle$.
4. **Exact Two-Level Spectral Gap & Coherent Transfer Frequency**:
   Signed splitting $(E_0 + \omega) - (E_0 - \omega) = 2\omega(X, Y)$, with transition channel
   $P_{L \to R}(t) = \sin^2(\omega(X, Y) t) = \frac{1 - \cos(2\omega(X, Y) t)}{2}$.

All proofs in this module are complete with 0 `sorry`s and 0 axioms.
-/

/-! ### 1. Scale Extraction from the Native 5-Graded Mixed Bracket -/

/-- Scale extraction map $\Delta(X, Y) := \omega(X, Y)$. -/
def freudenthalScaleCoupling (X Y : FreudenthalCharge J) : ℝ :=
  FreudenthalCharge.symplecticForm D X Y

/-- **THE ZERO-SCALE PROJECTION THEOREM**:
    The grade 0 scale component of the native 5-graded bracket between $\operatorname{injChargeMinus}(D, X)$
    and $\operatorname{injChargePlus}(D, Y)$ is precisely $\omega(X, Y)$. -/
theorem mixed_bracket_scale_eq (X Y : FreudenthalCharge J) :
    (fiveGradedBracket D (injChargeMinus D X) (injChargePlus D Y)).zero_scale =
    freudenthalScaleCoupling D X Y := by
  dsimp [fiveGradedBracket, injChargeMinus, injChargePlus, freudenthalScaleCoupling]
  rw [symplecticForm_zero_left D 0]
  ring

/-! ### 2. The Symmetric Two-Level Hamiltonian Realization -/

/-- The 2-level symmetric Hamiltonian realized from the Freudenthal mixed bracket:
    $\mathcal{H}_{X, Y}(E_0) = \begin{pmatrix} E_0 & \omega(X, Y) \\ \omega(X, Y) & E_0 \end{pmatrix}$. -/
def freudenthalTwoLevelHamiltonian (E0 : ℝ) (X Y : FreudenthalCharge J) : Mat2 :=
  !![E0, freudenthalScaleCoupling D X Y; freudenthalScaleCoupling D X Y, E0]

/-- **THE SECULAR CHARACTERISTIC DETERMINANT THEOREM**:
    $\det(\mathcal{H}_{X, Y} - E I_2) = (E - (E_0 - \omega(X, Y)))(E - (E_0 + \omega(X, Y)))$. -/
theorem freudenthal_secular_roots (E0 E : ℝ) (X Y : FreudenthalCharge J) :
    det (freudenthalTwoLevelHamiltonian D E0 X Y - E • (1 : Mat2)) =
    (E - (E0 - freudenthalScaleCoupling D X Y)) *
    (E - (E0 + freudenthalScaleCoupling D X Y)) := by
  dsimp [freudenthalTwoLevelHamiltonian]
  simp [det_fin_two]
  ring

/-! ### 3. Explicit Eigenmodes & Signed Splitting -/

/-- The symmetric eigenmode $|+\rangle = (1, 1)$. -/
def eigenPlus : Vec2 := ![1, 1]

/-- The antisymmetric eigenmode $|-\rangle = (1, -1)$. -/
def eigenMinus : Vec2 := ![1, -1]

/-- **THE SYMMETRIC EIGENVALUE THEOREM**:
    $\mathcal{H}_{X, Y} |+\rangle = (E_0 + \omega(X, Y)) |+\rangle$. -/
theorem freudenthal_plus_eigenmode (E0 : ℝ) (X Y : FreudenthalCharge J) :
    mulVec (freudenthalTwoLevelHamiltonian D E0 X Y) eigenPlus =
    (E0 + freudenthalScaleCoupling D X Y) • eigenPlus := by
  dsimp [freudenthalTwoLevelHamiltonian, eigenPlus, mulVec]
  ext i
  fin_cases i <;> simp <;> ring

/-- **THE ANTISYMMETRIC EIGENVALUE THEOREM**:
    $\mathcal{H}_{X, Y} |-\rangle = (E_0 - \omega(X, Y)) |-\rangle$. -/
theorem freudenthal_minus_eigenmode (E0 : ℝ) (X Y : FreudenthalCharge J) :
    mulVec (freudenthalTwoLevelHamiltonian D E0 X Y) eigenMinus =
    (E0 - freudenthalScaleCoupling D X Y) • eigenMinus := by
  dsimp [freudenthalTwoLevelHamiltonian, eigenMinus, mulVec]
  ext i
  fin_cases i <;> simp <;> ring

/-- **THE SIGNED SPLITTING THEOREM**:
    $(E_0 + \omega(X, Y)) - (E_0 - \omega(X, Y)) = 2 \omega(X, Y)$. -/
theorem freudenthal_signed_splitting (E0 : ℝ) (X Y : FreudenthalCharge J) :
    (E0 + freudenthalScaleCoupling D X Y) -
    (E0 - freudenthalScaleCoupling D X Y) =
    2 * freudenthalScaleCoupling D X Y := by
  ring

/-! ### 4. The Transition Channel & Coherent Frequency -/

/-- Coherent transition probability between sectors: $P_{L \to R}(t) = \sin^2(\omega(X, Y) t)$. -/
def freudenthalTransitionProb (X Y : FreudenthalCharge J) (t : ℝ) : ℝ :=
  (Real.sin (freudenthalScaleCoupling D X Y * t)) ^ 2

/-- **THE DOUBLE-ANGLE IDENTITY THEOREM**:
    $P_{L \to R}(t) = \frac{1 - \cos(2\omega(X, Y) t)}{2}$, exhibiting angular frequency $2|\omega(X, Y)|$. -/
theorem freudenthal_transition_double_angle (X Y : FreudenthalCharge J) (t : ℝ) :
    freudenthalTransitionProb D X Y t =
    (1 - Real.cos (2 * freudenthalScaleCoupling D X Y * t)) / 2 := by
  dsimp [freudenthalTransitionProb]
  have h_cos : Real.cos (2 * (freudenthalScaleCoupling D X Y * t)) =
               1 - 2 * (Real.sin (freudenthalScaleCoupling D X Y * t)) ^ 2 := by
    have h_double := Real.cos_two_mul (freudenthalScaleCoupling D X Y * t)
    have h_sq : (Real.cos (freudenthalScaleCoupling D X Y * t)) ^ 2 =
                1 - (Real.sin (freudenthalScaleCoupling D X Y * t)) ^ 2 := by
      have h_pyth := Real.sin_sq_add_cos_sq (freudenthalScaleCoupling D X Y * t)
      linarith
    linarith
  have h_eq : 2 * freudenthalScaleCoupling D X Y * t =
              2 * (freudenthalScaleCoupling D X Y * t) := by ring
  rw [h_eq, h_cos]
  ring

/-! ### 5. Grand Freudenthal Two-Level Gap Synthesis -/

/--
🏆 **GRAND SYNTHESIS: Native Freudenthal Bracket to Two-Level Spectral Gap**

Unifies:
1. Exact zero-scale component extraction: $\pi_H([X_-, Y_+]) = \omega(X, Y)$.
2. Explicit symmetric/antisymmetric eigenmodes with eigenvalues $E_0 \pm \omega(X, Y)$.
3. Exact signed splitting: $\Delta E_{\text{signed}} = 2\omega(X, Y)$.
4. Coherent probability flow: $P(t) = \frac{1 - \cos(2\omega t)}{2}$.
-/
theorem grand_freudenthal_two_level_gap_synthesis
    (E0 E : ℝ) (X Y : FreudenthalCharge J) (t : ℝ) :
    ((fiveGradedBracket D (injChargeMinus D X) (injChargePlus D Y)).zero_scale =
     freudenthalScaleCoupling D X Y) ∧
    (det (freudenthalTwoLevelHamiltonian D E0 X Y - E • (1 : Mat2)) =
     (E - (E0 - freudenthalScaleCoupling D X Y)) *
     (E - (E0 + freudenthalScaleCoupling D X Y))) ∧
    (mulVec (freudenthalTwoLevelHamiltonian D E0 X Y) eigenPlus =
     (E0 + freudenthalScaleCoupling D X Y) • eigenPlus) ∧
    (mulVec (freudenthalTwoLevelHamiltonian D E0 X Y) eigenMinus =
     (E0 - freudenthalScaleCoupling D X Y) • eigenMinus) ∧
    ((E0 + freudenthalScaleCoupling D X Y) -
     (E0 - freudenthalScaleCoupling D X Y) =
     2 * freudenthalScaleCoupling D X Y) ∧
    (freudenthalTransitionProb D X Y t =
     (1 - Real.cos (2 * freudenthalScaleCoupling D X Y * t)) / 2) :=
  ⟨mixed_bracket_scale_eq D X Y,
   freudenthal_secular_roots D E0 E X Y,
   freudenthal_plus_eigenmode D E0 X Y,
   freudenthal_minus_eigenmode D E0 X Y,
   freudenthal_signed_splitting D E0 X Y,
   freudenthal_transition_double_angle D X Y t⟩

end InfoGeometry.Exceptional.Freudenthal
