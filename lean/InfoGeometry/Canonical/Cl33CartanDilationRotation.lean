/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.MajoranaEightByEightJW

/-!
# The $\operatorname{Cl}(3,3)$ Cartan subalgebra: dilation vs. rotation

Splitting the joint "Tomita boost $+$ RoPE phase" flow into two commuting factors requires
picking rank-two generators with **the right sign pairing**, because the sign of a bivector's
square decides whether its exponential is a real dilation or a trigonometric rotation.

With the repo's split signature $\eta = (+1,-1,+1,-1,+1,-1)$:

* $K = \gamma_0\gamma_1$ pairs a **positive** generator with a **negative** one, so
  $K^2 = -\eta_0\eta_1 = +1$ and $\exp(\tau b K)$ is a genuine real dilation.
* $J = \gamma_2\gamma_4$ pairs two **same-sign** generators, so
  $J^2 = -\eta_2\eta_4 = -1$ and $\exp(\tau\omega J)$ is trigonometric — a rotation.
* $\gamma_2\gamma_3$ pairs $\eta_2=+1$ with $\eta_3=-1$, hence also squares to $+1$: it is a
  *second dilation*, **not** a rotation. This is the sign error these theorems exist to
  prevent.
* Disjoint supports commute, so $[K,J]=0$, which is what licenses
  $\exp(\tau b K)\exp(\tau\omega J) = \exp(\tau(bK+\omega J))$.

**Scope note.** Only the sign bookkeeping and the vanishing of the commutator are asserted. No
exponential is taken, no flow is claimed, and no $\operatorname{Cl}(3,3)\cong M_8(\mathbb{R})$
isomorphism is used or asserted (see `SplitOctonionClifford33Soldering`, which explicitly
disclaims it). The $\mathbb{M}^{1,3}$ complex-twistor picture — where a $J$ with $J^2=-\mathbb{I}$
is available for free — is **not** what is certified here; in split signature the rotation must
come from a *same-sign* pair.
-/

namespace InfoGeometry.Canonical.SplitOctonionClifford33Soldering

open InfoGeometry.Canonical.MajoranaEightByEightJW

open scoped Matrix

set_option maxHeartbeats 0

/-- Distinct Majorana generators anticommute: $\gamma_a\gamma_b = -\gamma_b\gamma_a$ for $a\ne b$. -/
theorem cl33Generator_swap (a b : Fin 6) (hab : a ≠ b) :
    majoranaGenR a * majoranaGenR b = -majoranaGenR b * majoranaGenR a := by
  have hs := majoranaGenR_pairwise_anticomm a b hab
  rw [ChakravalaGA.superBracket_fermionic] at hs
  rw [neg_mul]
  exact add_eq_zero_iff_eq_neg.mp hs

theorem cl33Dilation_sq : (majoranaGenR ⟨0, by decide⟩ * majoranaGenR ⟨1, by decide⟩) ^ 2
      = (1 : Matrix (Fin 8) (Fin 8) ℝ) := by
  rw [pow_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [majoranaGenR, majoranaGenZ, gamma1PlusZ, gamma1MinusZ,
      Matrix.mul_apply, Fin.sum_univ_eight]
theorem cl33Rotation_sq : (majoranaGenR ⟨2, by decide⟩ * majoranaGenR ⟨4, by decide⟩) ^ 2 = -1 := by
  rw [pow_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [majoranaGenR, majoranaGenZ, gamma2PlusZ, gamma3PlusZ,
      Matrix.mul_apply, Fin.sum_univ_eight]
theorem cl33MixedPair_is_dilation : (majoranaGenR ⟨2, by decide⟩ * majoranaGenR ⟨3, by decide⟩) ^ 2
      = (1 : Matrix (Fin 8) (Fin 8) ℝ) := by
  rw [pow_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [majoranaGenR, majoranaGenZ, gamma2PlusZ, gamma2MinusZ,
      Matrix.mul_apply, Fin.sum_univ_eight]

/-- **The Cartan commutator vanishes.** The dilation $K=\gamma_0\gamma_1$ and the rotation
$J=\gamma_2\gamma_4$ act on disjoint generator supports, so they commute. This is the
algebraic licence for factorising a joint flow into a boost part and a phase part. -/
theorem cl33Cartan_comm :
    (majoranaGenR ⟨0, by decide⟩ * majoranaGenR ⟨1, by decide⟩)
        * (majoranaGenR ⟨2, by decide⟩ * majoranaGenR ⟨4, by decide⟩)
      = (majoranaGenR ⟨2, by decide⟩ * majoranaGenR ⟨4, by decide⟩)
        * (majoranaGenR ⟨0, by decide⟩ * majoranaGenR ⟨1, by decide⟩) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [majoranaGenR, majoranaGenZ, gamma1PlusZ, gamma1MinusZ,
      gamma2PlusZ, gamma3PlusZ, Matrix.mul_apply, Fin.sum_univ_eight]

end InfoGeometry.Canonical.SplitOctonionClifford33Soldering
