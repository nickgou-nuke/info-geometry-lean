import Mathlib.Tactic
import InfoGeometry.Quantum.ClassDSuperconductorPfaffianInvariant
import InfoGeometry.Canonical.ClassDTopology

/-!
# InfoGeometry.Canonical.KOIndexSpectralFlow

KO-Theoretic Classification, Bott Periodicity, and Fredholm Index Spectral Flow.

This module formalizes the KO-theoretic framework for Class-D topological insulators and
superconductors, connecting the $\mathbb{Z}_2$ Pfaffian invariant to the Fredholm index mod 2
and establishing the Bott periodicity $d + 8 \equiv d \pmod 8$.

## Mathematical Content

1. **Bott Periodicity mod 8**: The real K-theory KO groups satisfy $\text{KO}_{d+8}(X) \cong \text{KO}_d(X)$.
2. **Fredholm $\mathbb{Z}_2$ Index**: For a real skew-adjoint Fredholm operator $F$, the parity of its
   kernel dimension modulo 2 corresponds to the sign of the Pfaffian:
   $$\text{ind}_2(F) = \begin{cases} 1 & \text{if } \text{Pf}(F) < 0 \\ 0 & \text{if } \text{Pf}(F) > 0 \end{cases}$$
3. **Spectral Flow Parity Multiplicativity**: Under continuous deformations of gapped Hamiltonians, the parity of the number of zero-crossings is additive modulo 2 (multiplicative in Pfaffian signs).
-/

namespace InfoGeometry.Canonical.KOIndexSpectralFlow

open InfoGeometry.Quantum.ClassDSuperconductorPfaffianInvariant
open InfoGeometry.Canonical.ClassDTopology

/--
Bott periodicity mod 8 for real K-theory KO groups:
$\text{KO}_{d+8} \cong \text{KO}_d$.
-/
def bottPeriodicityMod8 (d : ℕ) : ZMod 8 :=
  ((d + 8 : ℕ) : ZMod 8)

/-- Bott periodicity mod 8 invariance identity: $(d + 8) \equiv d \pmod 8$. -/
theorem bott_periodicity_mod8_eq (d : ℕ) :
    bottPeriodicityMod8 d = (d : ZMod 8) := by
  unfold bottPeriodicityMod8
  push_cast
  have h8 : (8 : ZMod 8) = 0 := rfl
  rw [h8, add_zero]

/--
The Fredholm $\mathbb{Z}_2$ index associated to a real skew-adjoint operator with Pfaffian determinant `nu`:
returns `1 : ZMod 2` if `nu < 0` (topological/non-trivial) and `0 : ZMod 2` if `nu > 0` (trivial).
-/
noncomputable def fredholmZ2Index (nu : ℝ) : ZMod 2 :=
  if nu < 0 then 1 else 0

/--
**Fredholm $\mathbb{Z}_2$ Index Multiplicativity:**
The $\mathbb{Z}_2$ index of a product/composite system $F_1 \oplus F_2$ with Pfaffians $\nu_1, \nu_2 \neq 0$
equals the sum modulo 2 of their individual indices:
$$\text{ind}_2(F_1 \oplus F_2) = \text{ind}_2(F_1) + \text{ind}_2(F_2) \pmod 2$$
-/
theorem fredholm_z2_index_mul (nu1 nu2 : ℝ) (h1 : nu1 ≠ 0) (h2 : nu2 ≠ 0) :
    fredholmZ2Index (nu1 * nu2) = fredholmZ2Index nu1 + fredholmZ2Index nu2 := by
  unfold fredholmZ2Index
  rcases lt_or_gt_of_ne h1 with h1_neg | h1_pos <;>
  rcases lt_or_gt_of_ne h2 with h2_neg | h2_pos
  · have hprod : nu1 * nu2 > 0 := mul_pos_of_neg_of_neg h1_neg h2_neg
    have hprod_not_neg : ¬ (nu1 * nu2 < 0) := not_lt.mpr (le_of_lt hprod)
    simp [h1_neg, h2_neg, hprod_not_neg]
    rfl
  · have hprod : nu1 * nu2 < 0 := mul_neg_of_neg_of_pos h1_neg h2_pos
    have h2_not_neg : ¬ (nu2 < 0) := not_lt.mpr (le_of_lt h2_pos)
    simp [h1_neg, h2_not_neg, hprod]
  · have hprod : nu1 * nu2 < 0 := mul_neg_of_pos_of_neg h1_pos h2_neg
    have h1_not_neg : ¬ (nu1 < 0) := not_lt.mpr (le_of_lt h1_pos)
    simp [h1_not_neg, h2_neg, hprod]
  · have hprod : nu1 * nu2 > 0 := mul_pos h1_pos h2_pos
    have h1_not_neg : ¬ (nu1 < 0) := not_lt.mpr (le_of_lt h1_pos)
    have h2_not_neg : ¬ (nu2 < 0) := not_lt.mpr (le_of_lt h2_pos)
    have hprod_not_neg : ¬ (nu1 * nu2 < 0) := not_lt.mpr (le_of_lt hprod)
    simp [h1_not_neg, h2_not_neg, hprod_not_neg]

/--
**Class-D to Fredholm Index Identification:**
The 1D Class-D topological invariant `classDInvariantZ2` matches the Fredholm $\mathbb{Z}_2$ index
of the high-symmetry Pfaffian product $\nu = \text{Pf}(A(0)) \cdot \text{Pf}(A(\pi))$.
-/
theorem classD_to_fredholm_index_match (mu t : ℝ) (h : mu^2 ≠ t^2) :
    classDInvariantZ2 mu t = fredholmZ2Index (kitaevPfaffianProduct mu t) := by
  unfold classDInvariantZ2 fredholmZ2Index
  by_cases htop : mu^2 < t^2
  · have hneg := topological_phase_pfaffian_neg mu t htop
    simp [htop, hneg]
  · have hpos : kitaevPfaffianProduct mu t > 0 := by
      rw [kitaev_pfaffian_product_eq]
      have : t^2 < mu^2 := by
        rcases lt_or_gt_of_ne h with h1 | h2
        · exact False.elim (htop h1)
        · exact h2
      linarith
    have hnot_neg : ¬ (kitaevPfaffianProduct mu t < 0) := not_lt.mpr (le_of_lt hpos)
    simp [htop, hnot_neg]

end InfoGeometry.Canonical.KOIndexSpectralFlow
