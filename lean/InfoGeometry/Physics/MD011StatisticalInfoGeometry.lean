import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Physics.MD20250430070955FinitePartition

/-!
# Repaired MD 011: finite statistical and information geometry

Source: `github-nick:nickgou-nuke/MD`, file `011.md`.

Chapter 11 applies statistical mechanics and information geometry to matrix
spaces.  The text also discusses emergent spacetime, entropy arrows, optimal
transport, and Einstein equations; those are not finite algebraic theorems.
This owner extracts the finite socket:

* finite real ensemble means and covariance entries;
* covariance symmetry and variance self-covariance;
* diagonal quadratic Hamiltonian shadow;
* diagonal covariance/inverse-covariance matrix identity, the finite Fisher
  readout used by Gaussian mean families;
* a concrete two-atom finite Fisher/covariance Gram matrix with symmetric and
  nonnegative quadratic form;
* reuse of the existing finite partition normalization theorem.

No theorem here asserts Gaussian integrals, differentiability of `log Z`,
continuous Fisher geometry, Wasserstein geometry, entropy-arrow dynamics,
Lorentzian-signature emergence, or Einstein equations.
-/

noncomputable section

namespace InfoGeometry.Physics.MD011StatisticalInfoGeometry

set_option linter.unusedSimpArgs false

open BigOperators

/-- Finite weighted real mean of an observable. -/
def finiteMeanReal {ι : Type} [Fintype ι] (w : ι → ℝ) (O : ι → ℝ) : ℝ :=
  ∑ i, w i * O i

/-- Centered finite observable. -/
def centeredReal {ι : Type} [Fintype ι] (w : ι → ℝ) (O : ι → ℝ) (i : ι) : ℝ :=
  O i - finiteMeanReal w O

/-- Finite weighted covariance entry. -/
def finiteCovReal {ι : Type} [Fintype ι] (w : ι → ℝ) (O P : ι → ℝ) : ℝ :=
  ∑ i, w i * centeredReal w O i * centeredReal w P i

/-- Covariance is symmetric in the two observables. -/
theorem finiteCovReal_symmetric {ι : Type} [Fintype ι]
    (w : ι → ℝ) (O P : ι → ℝ) :
    finiteCovReal w O P = finiteCovReal w P O := by
  unfold finiteCovReal
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Variance is the self-covariance. -/
def finiteVarianceReal {ι : Type} [Fintype ι] (w : ι → ℝ) (O : ι → ℝ) : ℝ :=
  finiteCovReal w O O

/-- A constant observable has zero centered readout when weights sum to one. -/
theorem centeredReal_zero_of_constant {ι : Type} [Fintype ι]
    (w : ι → ℝ) (hwsum : ∑ i, w i = 1) (c : ℝ) (i : ι) :
    centeredReal w (fun _ => c) i = 0 := by
  unfold centeredReal finiteMeanReal
  rw [← Finset.sum_mul]
  rw [hwsum]
  ring

/-- A constant observable has zero covariance. -/
theorem finiteCovReal_zero_left_of_constant {ι : Type} [Fintype ι]
    (w : ι → ℝ) (hwsum : ∑ i, w i = 1) (c : ℝ) (P : ι → ℝ) :
    finiteCovReal w (fun _ => c) P = 0 := by
  simp [finiteCovReal, centeredReal_zero_of_constant (w := w) hwsum c]

/-- Two real coordinates for the finite Gaussian/Fisher shadow. -/
abbrev RVec2 := InfoGeometry.Algebra.FiniteSpin.Vec2R

/-- Euclidean dot product on two real coordinates. -/
def rdot (x y : RVec2) : ℝ :=
  ∑ i, x i * y i

/-- Center a two-coordinate sample by a mean vector. -/
def centeredVec2 (m z : RVec2) : RVec2 :=
  fun i => z i - m i

/-- Diagonal quadratic form with inverse-covariance/stiffness entries `k`. -/
def diagQuad (k : RVec2) (x : RVec2) : ℝ :=
  ∑ i, k i * x i * x i

/-- Finite quadratic Hamiltonian shadow for a diagonal Gaussian model. -/
def gaussianEnergyDiag (k m z : RVec2) : ℝ :=
  (1 / 2 : ℝ) * diagQuad k (centeredVec2 m z)

/-- Expanded two-coordinate diagonal quadratic Hamiltonian. -/
theorem gaussianEnergyDiag_expand (k m z : RVec2) :
    gaussianEnergyDiag k m z =
      (1 / 2 : ℝ) * (k 0 * (z 0 - m 0) ^ 2 + k 1 * (z 1 - m 1) ^ 2) := by
  simp [gaussianEnergyDiag, diagQuad, centeredVec2, Fin.sum_univ_two]
  ring

/-- Diagonal covariance matrix. -/
def diagonalCov (s : RVec2) : Matrix (Fin 2) (Fin 2) ℝ :=
  fun i j => if i = j then s i else 0

/-- Diagonal inverse-covariance/Fisher matrix. -/
def diagonalInvCov (k : RVec2) : Matrix (Fin 2) (Fin 2) ℝ :=
  fun i j => if i = j then k i else 0

/-- Diagonal inverse covariance times covariance is the identity under reciprocal gates. -/
theorem diagonalInvCov_mul_diagonalCov (s k : RVec2) (h : ∀ i, k i * s i = 1) :
    diagonalInvCov k * diagonalCov s = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diagonalInvCov, diagonalCov, Matrix.mul_apply, Fin.sum_univ_two, h]

/-- Diagonal covariance times inverse covariance is also the identity. -/
theorem diagonalCov_mul_diagonalInvCov (s k : RVec2) (h : ∀ i, s i * k i = 1) :
    diagonalCov s * diagonalInvCov k = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diagonalInvCov, diagonalCov, Matrix.mul_apply, Fin.sum_univ_two, h]

/-- Two-atom finite Fisher/covariance Gram matrix for two sufficient statistics. -/
def finiteFisherCov2Atom (w : Fin 2 → ℝ) (T : Fin 2 → Fin 2 → ℝ) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  fun a b => finiteCovReal w (T a) (T b)

/-- Linear combination of two sufficient statistics on a two-atom ensemble. -/
def linStat2Atom (u : RVec2) (T : Fin 2 → Fin 2 → ℝ) : Fin 2 → ℝ :=
  fun i => u 0 * T 0 i + u 1 * T 1 i

/-- The finite Fisher/covariance Gram matrix is symmetric. -/
theorem finiteFisherCov2Atom_symmetric (w : Fin 2 → ℝ) (T : Fin 2 → Fin 2 → ℝ) :
    (finiteFisherCov2Atom w T).transpose = finiteFisherCov2Atom w T := by
  ext a b
  simp [finiteFisherCov2Atom, finiteCovReal_symmetric]

/-- Centering commutes with a finite two-statistic linear combination. -/
theorem centered_linStat2Atom (w : Fin 2 → ℝ) (u : RVec2)
    (T : Fin 2 → Fin 2 → ℝ) (i : Fin 2) :
    centeredReal w (linStat2Atom u T) i =
      u 0 * centeredReal w (T 0) i + u 1 * centeredReal w (T 1) i := by
  fin_cases i <;>
    simp [centeredReal, finiteMeanReal, linStat2Atom, Fin.sum_univ_two]
    <;> ring

/-- A Fisher/covariance Gram quadratic form is the variance of the linear statistic. -/
theorem finiteFisherCov2Atom_quadratic_eq_variance
    (w : Fin 2 → ℝ) (u : RVec2) (T : Fin 2 → Fin 2 → ℝ) :
    (∑ a : Fin 2, ∑ b : Fin 2, u a * finiteFisherCov2Atom w T a b * u b) =
      finiteVarianceReal w (linStat2Atom u T) := by
  simp [finiteFisherCov2Atom, finiteVarianceReal, finiteCovReal, Fin.sum_univ_two,
    centered_linStat2Atom, linStat2Atom]
  ring

/-- Nonnegative weights make any finite variance nonnegative on the two-atom ensemble. -/
theorem finiteVarianceReal_nonneg_of_weights_fin2
    (w : Fin 2 → ℝ) (hw : ∀ i, 0 ≤ w i) (O : Fin 2 → ℝ) :
    0 ≤ finiteVarianceReal w O := by
  unfold finiteVarianceReal finiteCovReal
  exact Finset.sum_nonneg (fun i _ => by
    have hs : 0 ≤ centeredReal w O i * centeredReal w O i := mul_self_nonneg _
    simpa [mul_assoc] using mul_nonneg (hw i) hs)

/-- The two-atom Fisher/covariance Gram quadratic form is nonnegative. -/
theorem finiteFisherCov2Atom_quadratic_nonneg
    (w : Fin 2 → ℝ) (hw : ∀ i, 0 ≤ w i) (u : RVec2) (T : Fin 2 → Fin 2 → ℝ) :
    0 ≤ ∑ a : Fin 2, ∑ b : Fin 2, u a * finiteFisherCov2Atom w T a b * u b := by
  rw [finiteFisherCov2Atom_quadratic_eq_variance w u T]
  exact finiteVarianceReal_nonneg_of_weights_fin2 w hw (linStat2Atom u T)

end InfoGeometry.Physics.MD011StatisticalInfoGeometry

end noncomputable section
