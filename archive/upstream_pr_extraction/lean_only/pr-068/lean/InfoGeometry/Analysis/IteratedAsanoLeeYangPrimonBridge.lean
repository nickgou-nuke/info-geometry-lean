import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic
import InfoGeometry.Analysis.AsanoUnitDiskContractionBridge
import InfoGeometry.Analysis.AsanoLeeYangCircleBridge
import InfoGeometry.Canonical.ColimitPartitionXiIdentificationBridge

/-!
# InfoGeometry.Analysis.IteratedAsanoLeeYangPrimonBridge

Conditional Iterated Asano-Lee-Yang Readouts and Finite Primon Lattice
Critical-Line Localization.

This module formalizes:
1. **Ferromagnetic Pair Invariant:**
   For coupling $J \ge 0$, the Boltzmann interaction factor determinant satisfies:
   $$AD - BC = e^{2J} - e^{-2J} \ge 0$$
   and $AD - BC > 0$ for $J > 0$.
2. **Inversion Symmetry Conditionally Forces a Root to the Unit Circle:**
   $$|z| \le 1 \wedge |z^{-1}| \le 1 \implies |z| = 1$$
3. **A Finite-Model Root Conditionally Maps to the Critical Line:**
   For every root $z_0 \neq -1$ of the ferromagnetic model on the unit circle $|z_0| = 1$,
   its canonical Cayley temperature preimage $s_0 = \frac{z_0}{1 + z_0}$ satisfies:
   $$\operatorname{Re}(s_0) = \frac{1}{2}$$
-/

noncomputable section

namespace InfoGeometry.Analysis.IteratedAsanoLeeYangPrimon

open Complex
open InfoGeometry.Analysis.AsanoUnitDiskContraction
open InfoGeometry.Analysis.AsanoLeeYangCircle
open InfoGeometry.Canonical.ColimitPartitionXiIdentification

/-- 2-spin Ferromagnetic Boltzmann Matrix Determinant:
    A = exp(J), B = exp(-J), C = exp(-J), D = exp(J) ==> AD - BC = 2 sinh(2J) -/
def isingPairDeterminant (J : ℝ) : ℝ :=
  Real.exp (2 * J) - Real.exp (- (2 * J))

/-- 🏆 THEOREM 1: Positivity of the Ferromagnetic Interaction Determinant:
    J > 0 ==> AD - BC > 0 -/
theorem isingPairDeterminant_pos (J : ℝ) (hJ : 0 < J) :
    0 < isingPairDeterminant J := by
  dsimp [isingPairDeterminant]
  have h2J : 0 < 2 * J := by linarith
  have h_neg : -(2 * J) < 2 * J := by linarith
  exact sub_pos.mpr (Real.exp_lt_exp.mpr h_neg)

/-- 🏆 THEOREM 2: Non-degeneracy of the Ferromagnetic Interaction for J > 0 -/
theorem isingPairDeterminant_ne_zero (J : ℝ) (hJ : 0 < J) :
    isingPairDeterminant J ≠ 0 :=
  ne_of_gt (isingPairDeterminant_pos J hJ)

/-- 🏆 THEOREM 3: Nonnegativity of the Ferromagnetic Interaction for J ≥ 0 -/
theorem isingPairDeterminant_nonneg (J : ℝ) (hJ : 0 ≤ J) :
    0 ≤ isingPairDeterminant J := by
  dsimp [isingPairDeterminant]
  have h_le : -(2 * J) ≤ 2 * J := by linarith
  exact sub_nonneg.mpr (Real.exp_le_exp.mpr h_le)

/-- 🏆 THEOREM 4: Conditional unit-circle localization for one root.
    The hypotheses are the two disk inequalities for a nonzero root; this
    theorem does not construct a partition polynomial or prove the required
    inversion/zero-free hypotheses for a concrete model. -/
theorem roots_on_unit_circle_of_inversion_symmetry
    {z : ℂ} (hz_ne : z ≠ 0)
    (h_disk : ‖z‖ ≤ 1)
    (h_inv_disk : ‖z⁻¹‖ ≤ 1) :
    ‖z‖ = 1 :=
  unitCircle_of_inversion_symmetric_roots hz_ne h_disk h_inv_disk

/-- 🏆 THEOREM 5: Cayley transport of a unit-circle point.
    A separate theorem must identify `z₀` as a root of a concrete finite
    primon partition before this coordinate statement becomes a root result. -/
theorem finite_primon_root_on_critical_line
    {z₀ : ℂ} (hz₀_circle : ‖z₀‖ = 1) (hz₀_ne : z₀ ≠ -1) :
    (riemannCayleyInverse z₀).re = 1 / 2 :=
  partition_root_on_unitCircle_to_critical_line hz₀_circle hz₀_ne

end InfoGeometry.Analysis.IteratedAsanoLeeYangPrimon
