import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Lie.SplitOctonionChiralMinkowskiFixedSectionBridge
import InfoGeometry.Lie.SplitOctonionDoubleChiralSolderingBridge
import InfoGeometry.Canonical.CantorBernoulliPauliSolderingIntertwinerBridge

/-!
# Split-Octonion Witt Chiral Soldering and Operator Bridge

This module formalizes:
1. **Witt Chiral Projectors / Solderings**:
   $$\mathscr{S}_+(v) = \frac{1}{2}(v + \kappa v) \in \operatorname{Fix}(\kappa)$$
   $$\mathscr{S}_-(v) = \frac{1}{2}(v - \kappa v) \in \operatorname{AntiFix}(\kappa)$$
2. **🏆 THEOREM 1 (Chiral Solder Projections)**:
   - $\kappa(\mathscr{S}_+(v)) = \mathscr{S}_+(v)$ (Fixed in $\mathbb{R}^{1,3}$)
   - $\kappa(\mathscr{S}_-(v)) = -\mathscr{S}_-(v)$ (Inverted in $\mathbb{R}^{3,1}$)
   - $\mathscr{S}_+(v) + \mathscr{S}_-(v) = v$ (Completeness)
3. **🏆 THEOREM 2 (Hyperbolic Chiral Coordinate Parameterization)**:
   For $p^+ = r e^\eta, p^- = r e^{-\eta}$:
   - Mean coordinate $x = \frac{p^+ + p^-}{2} = r \cosh \eta$
   - Difference coordinate $\widetilde{x} = \frac{p^+ - p^-}{2} = r \sinh \eta$
   - Norm invariance $x^2 - \widetilde{x}^2 = p^+ p^-$
4. **🏆 THEOREM 3 (Chiral Reflection Symmetry on Hyperbolic Coordinates)**:
   $\kappa : \eta \mapsto -\eta \implies x \mapsto x, \; \widetilde{x} \mapsto -\widetilde{x}$.
-/

noncomputable section

open Real
open InfoGeometry.Lie.SplitOctonionChiralMinkowskiFixedSectionBridge
open InfoGeometry.Lie.SplitOctonionDoubleChiralSolderingBridge
open InfoGeometry.Canonical.CantorBernoulliPauliSolderingIntertwinerBridge

namespace InfoGeometry.Lie.SplitOctonionWittChiralSolderingOperatorBridge

/-- Symmetric Witt solder $\mathscr{S}_+(v) = \frac{1}{2}(v + \kappa v)$. -/
def solderPlus (v : Coord) : Coord :=
  fun i => (1 / 2 : ℝ) * (v i + (kappa v) i)

/-- Antisymmetric Witt solder $\mathscr{S}_-(v) = \frac{1}{2}(v - \kappa v)$. -/
def solderMinus (v : Coord) : Coord :=
  fun i => (1 / 2 : ℝ) * (v i - (kappa v) i)

/-- 🏆 THEOREM 1: $\mathscr{S}_+(v)$ lands in $\operatorname{Fix}(\kappa)$. -/
theorem solderPlus_in_fix (v : Coord) :
    kappa (solderPlus v) = solderPlus v := by
  have h_inv := kappa_involutive v
  ext i
  fin_cases i <;>
  · dsimp [solderPlus, kappa]
    ring

/-- 🏆 THEOREM 2: $\mathscr{S}_-(v)$ lands in $\operatorname{AntiFix}(\kappa)$. -/
theorem solderMinus_in_antifix (v : Coord) :
    kappa (solderMinus v) = - solderMinus v := by
  ext i
  fin_cases i <;>
  · dsimp [solderMinus, kappa]
    ring

/-- 🏆 THEOREM 3: Exact Witt direct sum completeness $\mathscr{S}_+(v) + \mathscr{S}_-(v) = v$. -/
theorem solder_completeness (v : Coord) :
    solderPlus v + solderMinus v = v := by
  ext i
  dsimp [solderPlus, solderMinus]
  ring

/-- 🏆 THEOREM 4: Hyperbolic coordinate identity $x^2 - \widetilde{x}^2 = p^+ p^-$. -/
theorem hyperbolic_witt_norm_identity (r η : ℝ) :
    (r * Real.cosh η) ^ 2 - (r * Real.sinh η) ^ 2 = (r * Real.exp η) * (r * Real.exp (-η)) := by
  have h_cosh_sinh : Real.cosh η ^ 2 - Real.sinh η ^ 2 = 1 := Real.cosh_sq_sub_sinh_sq η
  have h_exp : Real.exp η * Real.exp (-η) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  calc
    (r * Real.cosh η) ^ 2 - (r * Real.sinh η) ^ 2
      = r ^ 2 * (Real.cosh η ^ 2 - Real.sinh η ^ 2) := by ring
    _ = r ^ 2 * 1 := by rw [h_cosh_sinh]
    _ = r ^ 2 := by ring
    _ = r ^ 2 * (Real.exp η * Real.exp (-η)) := by rw [h_exp, mul_one]
    _ = (r * Real.exp η) * (r * Real.exp (-η)) := by ring

/-- 🏆 THEOREM 5: Chiral reflection negates rapidity $\eta \mapsto -\eta$, preserving $x$ and inverting $\widetilde{x}$. -/
theorem chiral_reflection_hyperbolic (r η : ℝ) :
    r * Real.cosh (-η) = r * Real.cosh η ∧
    r * Real.sinh (-η) = - (r * Real.sinh η) := by
  constructor
  · rw [Real.cosh_neg]
  · rw [Real.sinh_neg]
    ring

end InfoGeometry.Lie.SplitOctonionWittChiralSolderingOperatorBridge
