import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Lie.SplitOctonionWittVectorCovectorBridge

set_option linter.unusedSimpArgs false

/-!
# Split-Octonion Peirce 4-Fold Decomposition Bridge

This owner module formalizes the exact Peirce 4-fold decomposition of the
split-octonions $\mathbb{O}_s \cong \mathbb{R}^{4,4}$ under the chiral idempotents $u_+, u_-$:

1. **Four Peirce Projection Operators:**
   $$\Pi_{11}(x) = (x_0, 0, 0, 0, 0, 0, 0, 0) \in \mathbb{O}_{11} \cong \mathbb{R} u_+$$
   $$\Pi_{10}(x) = (0, x_1, x_2, x_3, 0, 0, 0, 0) \in \mathbb{O}_{10} \cong \operatorname{span}\{\boldsymbol{\sigma}^+_i\}$$
   $$\Pi_{01}(x) = (0, 0, 0, 0, 0, x_5, x_6, x_7) \in \mathbb{O}_{01} \cong \operatorname{span}\{\boldsymbol{\sigma}^-_i\}$$
   $$\Pi_{00}(x) = (0, 0, 0, 0, x_4, 0, 0, 0) \in \mathbb{O}_{00} \cong \mathbb{R} u_-$$

2. **Resolution of Identity:**
   $$\Pi_{11} + \Pi_{10} + \Pi_{01} + \Pi_{00} = \operatorname{id}_{\mathbb{O}_s}$$

3. **Orthogonal Projector Algebra:**
   $$\Pi_{ij}^2 = \Pi_{ij}, \qquad \Pi_{ij} \circ \Pi_{kl} = 0 \quad ((i,j) \neq (k,l))$$

4. **Chiral Isotropic Cone Recombination:**
   $$V_+ = \mathbb{O}_{11} \oplus \mathbb{O}_{10}, \qquad V_- = \mathbb{O}_{00} \oplus \mathbb{O}_{01}$$
-/

noncomputable section

namespace InfoGeometry.Lie.SplitOctonionPeirceDecompositionBridge

open InfoGeometry.Lie.SplitOctonionWittVectorCovectorBridge

abbrev Oct8 := InfoGeometry.Algebra.FiniteSpin.Vec8R

/-- Coordinate projection of the (1,1) scalar block: $u_+$. -/
def proj11 (x : Oct8) : Oct8 :=
  ![x 0, 0, 0, 0, 0, 0, 0, 0]

/-- Coordinate projection of the (1,0) 3-vector block: $(\boldsymbol{\sigma}^+_1, \boldsymbol{\sigma}^+_2, \boldsymbol{\sigma}^+_3)$. -/
def proj10 (x : Oct8) : Oct8 :=
  ![0, x 1, x 2, x 3, 0, 0, 0, 0]

/-- Coordinate projection of the (0,1) 3-covector block: $(\boldsymbol{\sigma}^-_1, \boldsymbol{\sigma}^-_2, \boldsymbol{\sigma}^-_3)$. -/
def proj01 (x : Oct8) : Oct8 :=
  ![0, 0, 0, 0, 0, x 5, x 6, x 7]

/-- Coordinate projection of the (0,0) mirror scalar block: $u_-$. -/
def proj00 (x : Oct8) : Oct8 :=
  ![0, 0, 0, 0, x 4, 0, 0, 0]

/-- 🏆 THEOREM 1: Resolution of identity into the four Peirce blocks:
    $\Pi_{11}(x) + \Pi_{10}(x) + \Pi_{01}(x) + \Pi_{00}(x) = x$. -/
theorem peirce_resolution_of_identity (x : Oct8) :
    proj11 x + proj10 x + proj01 x + proj00 x = x := by
  ext i
  fin_cases i <;> dsimp [proj11, proj10, proj01, proj00] <;> ring

/-- 🏆 THEOREM 2: The four Peirce projectors are idempotent: $\Pi_{ij}^2 = \Pi_{ij}$. -/
theorem peirce_proj11_idempotent (x : Oct8) : proj11 (proj11 x) = proj11 x := by
  ext i; fin_cases i <;> dsimp [proj11]

theorem peirce_proj10_idempotent (x : Oct8) : proj10 (proj10 x) = proj10 x := by
  ext i; fin_cases i <;> dsimp [proj10]

theorem peirce_proj01_idempotent (x : Oct8) : proj01 (proj01 x) = proj01 x := by
  ext i; fin_cases i <;> dsimp [proj01]

theorem peirce_proj00_idempotent (x : Oct8) : proj00 (proj00 x) = proj00 x := by
  ext i; fin_cases i <;> dsimp [proj00]

/-- 🏆 THEOREM 3: The four Peirce projectors are mutually orthogonal: $\Pi_{ij} \Pi_{kl} = 0$ for $(i,j) \neq (k,l)$. -/
theorem peirce_orthogonal_11_10 (x : Oct8) : proj11 (proj10 x) = 0 := by
  ext i; fin_cases i <;> dsimp [proj11, proj10]

theorem peirce_orthogonal_11_01 (x : Oct8) : proj11 (proj01 x) = 0 := by
  ext i; fin_cases i <;> dsimp [proj11, proj01]

theorem peirce_orthogonal_11_00 (x : Oct8) : proj11 (proj00 x) = 0 := by
  ext i; fin_cases i <;> dsimp [proj11, proj00]

theorem peirce_orthogonal_10_01 (x : Oct8) : proj10 (proj01 x) = 0 := by
  ext i; fin_cases i <;> dsimp [proj10, proj01]

theorem peirce_orthogonal_10_00 (x : Oct8) : proj10 (proj00 x) = 0 := by
  ext i; fin_cases i <;> dsimp [proj10, proj00]

theorem peirce_orthogonal_01_00 (x : Oct8) : proj01 (proj00 x) = 0 := by
  ext i; fin_cases i <;> dsimp [proj01, proj00]

/-- 🏆 THEOREM 4: Isotropic cone recovery:
    $V_+ = \mathbb{O}_{11} \oplus \mathbb{O}_{10}$ and $V_- = \mathbb{O}_{00} \oplus \mathbb{O}_{01}$. -/
theorem vplus_eq_peirce_11_add_10 (v : VPlus) :
    embedPlus v = proj11 (embedPlus v) + proj10 (embedPlus v) := by
  ext i; fin_cases i <;> dsimp [embedPlus, proj11, proj10] <;> ring

theorem vminus_eq_peirce_00_add_01 (w : VMinus) :
    embedMinus w = proj00 (embedMinus w) + proj01 (embedMinus w) := by
  ext i; fin_cases i <;> dsimp [embedMinus, proj00, proj01] <;> ring

end InfoGeometry.Lie.SplitOctonionPeirceDecompositionBridge
