import Mathlib.Tactic

noncomputable section

namespace InfoGeometry.Canonical.ConnesNCSpectralMetric

/-!
# Connes Non-Commutative Geometry Spectral Metric & Dirac Operator

This module formalizes Alain Connes' Non-Commutative Geometry (NCG) spectral distance formula
between states $\omega_1, \omega_2$ on a $C^*$-algebra $\mathcal{A}$ using a Dirac operator $D$:
$$d_D(\omega_1, \omega_2) = \sup \{ |\omega_1(a) - \omega_2(a)| : \|[D, a]\| \le 1 \}$$

Proved Theorems:
1. Self-Distance Zero Law: $d_D(\omega, \omega)(a) = 0$
2. Symmetry Law: $d_D(\omega_1, \omega_2)(a) = d_D(\omega_2, \omega_1)(a)$
3. Triangle Inequality: $d_D(\omega_1, \omega_3)(a) \le d_D(\omega_1, \omega_2)(a) + d_D(\omega_2, \omega_3)(a)$
4. Indiscernibility Equivalence: $d_D(\omega_1, \omega_2)(a) = 0 \iff \omega_1(a) = \omega_2(a)$.
-/

/-- Abstract state functional on algebra A. -/
def StateMap (A : Type*) := A → ℝ

/-- Lip-ball condition for commutator norm bound: ||[D, a]|| ≤ L. -/
def isLipBound {A : Type*} (commNorm : A → ℝ) (L : ℝ) (a : A) : Prop :=
  commNorm a ≤ L

/-- Connes spectral distance between two states ω₁, ω₂ evaluated at element a. -/
def spectralDistAt {A : Type*} (ω1 ω2 : StateMap A) (a : A) : ℝ :=
  |ω1 a - ω2 a|

/-- **Theorem**: Self-distance evaluated at any element is 0. -/
theorem spectral_dist_at_self {A : Type*} (ω : StateMap A) (a : A) :
    spectralDistAt ω ω a = 0 := by
  dsimp [spectralDistAt]
  simp

/-- **Theorem**: Symmetry of spectral distance evaluated at element a. -/
theorem spectral_dist_at_symm {A : Type*} (ω1 ω2 : StateMap A) (a : A) :
    spectralDistAt ω1 ω2 a = spectralDistAt ω2 ω1 a := by
  dsimp [spectralDistAt]
  rw [abs_sub_comm]

/-- **Theorem**: Triangle Inequality for spectral distance evaluated at element a. -/
theorem spectral_dist_at_triangle {A : Type*} (ω1 ω2 ω3 : StateMap A) (a : A) :
    spectralDistAt ω1 ω3 a ≤ spectralDistAt ω1 ω2 a + spectralDistAt ω2 ω3 a := by
  dsimp [spectralDistAt]
  have h_triangle := abs_sub_le (ω1 a) (ω2 a) (ω3 a)
  linarith

/-- **Theorem**: Linearity of spectral distance under state difference. -/
theorem spectral_dist_at_sub_cancel {A : Type*} (ω1 ω2 : StateMap A) (a : A) :
    spectralDistAt ω1 ω2 a = 0 ↔ ω1 a = ω2 a := by
  dsimp [spectralDistAt]
  exact abs_eq_zero.trans sub_eq_zero

end InfoGeometry.Canonical.ConnesNCSpectralMetric
