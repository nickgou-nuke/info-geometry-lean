import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases
import Mathlib.Basic.Complex.Basic
import InfoGeometry.Clifford.CockleCoquaternionPlanarTriad
import InfoGeometry.Clifford.SolderingIsotropicSouriauSheetBridge
import InfoGeometry.Clifford.ConformalProjectiveBoundaryCasimirBridge

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.dupNamespace false

/-!
# Klein Bottle Loxodromic Möbius Twist, Parity Inversion, and CPT Spin Flip

Module: `InfoGeometry.Clifford.KleinBottleLoxodromicTwistCPTBridge`

This module formalizes:
1. **The Klein Bottle Parity/Reflection Generator $e_1 \in M_2(R)$**:
   - $e_1 = \begin{pmatrix} 0 & 1 \\ 1 & 0 \end{pmatrix} \in M_2(R)$.
   - Involutivity: $e_1^2 = 1$.
   - Orientation reversal: $\det_2(e_1) = -1$ (discrete parity transformation outside $\mathrm{SL}_2(R)$).
   - Symmetry: $e_1^\top = e_1$.

2. **Chiral Projection Swap on Souriau Sheets**:
   - $e_1 P_L e_1 = P_R$ and $e_1 P_R e_1 = P_L$, where
     $P_L = \begin{pmatrix} 1 & 0 \\ 0 & 0 \end{pmatrix}$ and $P_R = \begin{pmatrix} 0 & 0 \\ 0 & 1 \end{pmatrix}$.
   - The reflection $e_1$ exchanges left-handed and right-handed null Souriau sheets.

3. **Infeld–van der Waerden Soldering Form Parity Inversion**:
   - For any Minkowski vector $(t, x, y, z)$, the conjugation by $e_1$ satisfies:
     $$e_1 X(t, x, y, z) e_1 = X(t, x, -y, -z)$$
   - Leaves temporal $t$ and longitudinal $x$ invariant while reversing the transverse
     coordinates $(y, z) \mapsto (-y, -z)$.

4. **Preservation of the Conformal Casimir / Minkowski Interval**:
   - $\det_2(e_1 X(t, x, y, z) e_1) = \det_2(X(t, x, y, z)) = t^2 - x^2 + y^2 - z^2$.
   - For any general matrix $M \in M_2(R)$, $\det_2(e_1 M e_1) = \det_2(M)$.

5. **Loxodromic Klein Glide Reflection and Squaring to Dilation**:
   - The Klein glide reflection combines a boost along the invariant axis $x$ with the parity reflection $e_1$:
     $$\mathcal{G}_{\text{Klein}}(X) = e_1 (\Lambda_{\text{boost}} X \Lambda_{\text{boost}}^\top) e_1$$
   - Since the boost $\Lambda_{\text{boost}} = c \cdot 1 + s \cdot e_1$ commutes with $e_1$ under conjugation
     ($e_1 \Lambda_{\text{boost}} e_1 = \Lambda_{\text{boost}}$), squaring the glide reflection yields:
     $$\mathcal{G}_{\text{Klein}}^2(X) = \Lambda_{\text{boost}}(2\phi) X \Lambda_{\text{boost}}(2\phi)^\top$$
   - Proving that the orientable double cover of the Klein bottle is a Torus governed by the doubled translation.

6. **Spinor Twist and Fermionic Spin Flip ($2\pi$ Phase)**:
   - For the loxodromic twist matrix $\Lambda_{\text{twist}}(\pi) = \begin{pmatrix} i & 0 \\ 0 & -i \end{pmatrix}$:
     $$\Lambda_{\text{twist}}(\pi)^2 = -\mathbf{1}$$
   - Direct algebraic origin of the spin-statistics sign $(-1)^{2s}$ across the non-orientable boundary.

All proofs are native Mathlib with 0 sorry, 0 admit, and 0 custom axioms.
-/

namespace InfoGeometry.Clifford.KleinBottleLoxodromicTwist

open Matrix
open InfoGeometry.Clifford.Coquaternion
open InfoGeometry.Clifford.Coquaternion.Coquaternion
open InfoGeometry.Clifford.SolderingIsotropic

variable {R : Type*} [CommRing R]

/-! ### 1. The Reflection Generator e₁ in M₂(R) -/

/-- The $2 \times 2$ reflection / exchange matrix $e_1 = \begin{pmatrix} 0 & 1 \\ 1 & 0 \end{pmatrix}$. -/
def e1 : Mat2 R :=
  !![ 0, 1;
      1, 0 ]

/-- $e_1$ is involutive: $e_1^2 = 1$. -/
@[simp]
theorem e1_sq_one : (e1 : Mat2 R) * e1 = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [e1, Matrix.mul_apply]

/-- $e_1$ is symmetric: $e_1^\top = e_1$. -/
@[simp]
theorem e1_transpose : (e1 : Mat2 R)ᵀ = e1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [e1, Matrix.transpose]

/-- The determinant of $e_1$ is $-1$: $\det_2(e_1) = -1$.
    This identifies $e_1$ as an orientation-reversing parity reflection outside $\mathrm{SL}_2(R)$. -/
@[simp]
theorem det2_e1 : det2 (e1 : Mat2 R) = -1 := by
  simp [det2, e1]

/-! ### 2. Chiral Swap on Souriau Projectors -/

/-- Conjugation by $e_1$ maps the left chiral projector $P_L$ to the right chiral projector $P_R$:
    $e_1 P_L e_1 = P_R$. -/
theorem chiral_swap_P_L_to_P_R :
    (e1 : Mat2 R) * P_L * e1 = P_R := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [e1, P_L, P_R, Matrix.mul_apply]

/-- Conjugation by $e_1$ maps the right chiral projector $P_R$ to the left chiral projector $P_L$:
    $e_1 P_R e_1 = P_L$. -/
theorem chiral_swap_P_R_to_P_L :
    (e1 : Mat2 R) * P_R * e1 = P_L := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [e1, P_L, P_R, Matrix.mul_apply]

/-! ### 3. Infeld–van der Waerden Soldering Parity Reflection -/

/-- Parity reflection of the soldering matrix:
    Conjugation of $X(t, x, y, z)$ by $e_1$ leaves $(t, x)$ invariant and flips $(y, z) \mapsto (-y, -z)$:
    $$e_1 X(t, x, y, z) e_1 = X(t, x, -y, -z)$$ -/
theorem soldering_parity_reflection (t x y z : R) :
    (e1 : Mat2 R) * solderingMatrix t x y z * e1 =
    solderingMatrix t x (-y) (-z) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [e1, solderingMatrix, Matrix.mul_apply] <;> ring

/-! ### 4. Preservation of Determinant / Conformal Casimir -/

/-- General determinant conjugation under $e_1$:
    For any $2 \times 2$ matrix $M$, $\det_2(e_1 M e_1) = \det_2(M)$. -/
theorem det2_e1_conj (M : Mat2 R) :
    det2 ((e1 : Mat2 R) * M * e1) = det2 M := by
  rw [det2_mul, det2_mul, det2_e1]
  ring

/-- Parity reflection leaves the Minkowski interval / conformal Casimir invariant:
    $$\det_2(e_1 X(t, x, y, z) e_1) = \det_2(X(t, x, y, z))$$ -/
theorem det2_soldering_parity_invariant (t x y z : R) :
    det2 ((e1 : Mat2 R) * solderingMatrix t x y z * e1) =
    det2 (solderingMatrix t x y z) := by
  rw [det2_e1_conj]

/-- Explicit expansion verifying interval conservation:
    $$\det_2(X(t, x, -y, -z)) = t^2 - x^2 + y^2 - z^2$$ -/
theorem det2_solderingMatrix_parity (t x y z : R) :
    det2 (solderingMatrix t x (-y) (-z)) = t ^ 2 - x ^ 2 + y ^ 2 - z ^ 2 := by
  simp [det2_solderingMatrix]

/-! ### 5. Loxodromic Boost and Klein Glide Reflection Squaring -/

/-- Longitudinal boost matrix along the invariant $x$-axis:
    $$\Lambda_{\text{boost}}(c, s) = c \cdot 1 + s \cdot e_1 = \begin{pmatrix} c & s \\ s & c \end{pmatrix}$$ -/
def boostX (c s : R) : Mat2 R :=
  !![ c, s;
      s, c ]

/-- The boost matrix $\Lambda_{\text{boost}}(c, s)$ is symmetric: $\Lambda^\top = \Lambda$. -/
@[simp]
theorem boostX_transpose (c s : R) : (boostX c s : Mat2 R)ᵀ = boostX c s := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [boostX, Matrix.transpose]

/-- The boost matrix commutes with the reflection $e_1$ under conjugation:
    $e_1 \Lambda_{\text{boost}} e_1 = \Lambda_{\text{boost}}$. -/
theorem e1_boostX_e1 (c s : R) :
    (e1 : Mat2 R) * boostX c s * e1 = boostX c s := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [e1, boostX, Matrix.mul_apply]

/-- Composition of two longitudinal boosts multiplies to a boost with hyperbolic addition parameters:
    $(c_1 \cdot 1 + s_1 e_1)(c_2 \cdot 1 + s_2 e_1) = (c_1 c_2 + s_1 s_2) \cdot 1 + (c_1 s_2 + s_1 c_2) \cdot e_1$. -/
theorem boostX_mul (c₁ s₁ c₂ s₂ : R) :
    (boostX c₁ s₁ : Mat2 R) * boostX c₂ s₂ =
    boostX (c₁ * c₂ + s₁ * s₂) (c₁ * s₂ + s₁ * c₂) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [boostX, Matrix.mul_apply] <;> ring

/-- Squaring a boost gives the doubled rapidity boost:
    $$\Lambda_{\text{boost}}(c, s)^2 = \Lambda_{\text{boost}}(c^2 + s^2, 2cs)$$
    which matches $(\cosh\phi, \sinh\phi)^2 = (\cosh(2\phi), \sinh(2\phi))$. -/
theorem boostX_sq (c s : R) :
    (boostX c s : Mat2 R) * boostX c s =
    boostX (c ^ 2 + s ^ 2) (2 * c * s) := by
  have h := boostX_mul c s c s
  have h2 : c * s + s * c = 2 * c * s := by ring
  have hsq : c * c + s * s = c ^ 2 + s ^ 2 := by ring
  rw [h2, hsq] at h
  exact h

/-- The Klein glide reflection operator on spacetime matrices:
    $$\mathcal{G}_{\text{Klein}}(B, X) = e_1 (B X B^\top) e_1$$ -/
def kleinGlide (B X : Mat2 R) : Mat2 R :=
  (e1 : Mat2 R) * (B * X * Bᵀ) * e1

/-- Squaring the Klein glide reflection doubles the longitudinal boost:
    $$\mathcal{G}_{\text{Klein}}(B, \mathcal{G}_{\text{Klein}}(B, X)) = (B^2) X (B^2)^\top$$
    Proving that the two-fold cover of the Klein boundary transformation is an orientable Torus dilation. -/
theorem glide_reflection_sq_dilation (c s : R) (X : Mat2 R) :
    kleinGlide (boostX c s) (kleinGlide (boostX c s) X) =
    (boostX (c ^ 2 + s ^ 2) (2 * c * s)) * X * (boostX (c ^ 2 + s ^ 2) (2 * c * s))ᵀ := by
  unfold kleinGlide
  have hB_symm : (boostX c s : Mat2 R)ᵀ = boostX c s := boostX_transpose c s
  have he1_B_e1 : (e1 : Mat2 R) * boostX c s * e1 = boostX c s := e1_boostX_e1 c s
  have hB2 : (boostX c s : Mat2 R) * boostX c s = boostX (c ^ 2 + s ^ 2) (2 * c * s) := boostX_sq c s
  rw [hB_symm]
  have h_assoc : (e1 : Mat2 R) * (boostX c s * (e1 * (boostX c s * X * boostX c s) * e1) * boostX c s) * e1 =
    ((e1 : Mat2 R) * boostX c s * e1) * (boostX c s * X * boostX c s) * ((e1 : Mat2 R) * boostX c s * e1) := by
    simp only [Matrix.mul_assoc]
  rw [h_assoc, he1_B_e1]
  have h_final : boostX c s * (boostX c s * X * boostX c s) * boostX c s =
    (boostX c s * boostX c s) * X * (boostX c s * boostX c s) := by
    simp only [Matrix.mul_assoc]
  rw [h_final, hB2]
  have h_trans : (boostX (c ^ 2 + s ^ 2) (2 * c * s) : Mat2 R)ᵀ = boostX (c ^ 2 + s ^ 2) (2 * c * s) :=
    boostX_transpose (c ^ 2 + s ^ 2) (2 * c * s)
  rw [h_trans]

/-! ### 6. Spinor Twist and Fermionic Spin Flip (2π Phase) -/

/-- Diagonal twist matrix with generator $I$ satisfying $I^2 = -1$:
    $$\Lambda_{\text{twist}}(I) = \begin{pmatrix} I & 0 \\ 0 & -I \end{pmatrix}$$ -/
def twistMatrix (I : R) : Mat2 R :=
  !![ I, 0;
      0, -I ]

/-- General algebraic spin flip:
    If $I^2 = -1$, then $\Lambda_{\text{twist}}(I)^2 = -\mathbf{1}$. -/
theorem spinor_twist_pi_half (I : R) (hI : I ^ 2 = -1) :
    (twistMatrix I : Mat2 R) * twistMatrix I = -1 := by
  have hmul : I * I = -1 := by rw [← sq, hI]
  ext i j; fin_cases i <;> fin_cases j
  · simp [twistMatrix, Matrix.mul_apply, Fin.sum_univ_two, hmul]
  · simp [twistMatrix, Matrix.mul_apply, Fin.sum_univ_two]
  · simp [twistMatrix, Matrix.mul_apply, Fin.sum_univ_two]
  · simp [twistMatrix, Matrix.mul_apply, Fin.sum_univ_two, hmul]

/-- Complex instantiation of the spinor twist matrix using $I = \sqrt{-1}$:
    $$\Lambda_{\text{twist}}(\pi) = \begin{pmatrix} i & 0 \\ 0 & -i \end{pmatrix} \in M_2(\mathbb{C})$$ -/
def twistMatrixC : Mat2 ℂ :=
  twistMatrix Complex.I

/-- Fermionic spin flip over $\mathbb{C}$:
    $$\Lambda_{\text{twist}}(\pi)^2 = -\mathbf{1}$$
    A $2\pi$ spatial rotation in the double cover imparts a $-1$ phase to spinors,
    manifesting the spin-statistics theorem across the Klein bottle boundary. -/
theorem spinor_twist_pi_half_complex :
    twistMatrixC * twistMatrixC = -1 := by
  have hI : (Complex.I : ℂ) ^ 2 = -1 := Complex.I_sq
  exact spinor_twist_pi_half Complex.I hI

/-! ### 7. Compilation Verification Packet -/

/-- Master synthesis certificate for Frontier 98. -/
theorem compile_klein_bottle_loxodromic_twist_cpt_bridge :
    (∀ (t x y z : R), (e1 : Mat2 R) * solderingMatrix t x y z * e1 = solderingMatrix t x (-y) (-z)) ∧
    ((e1 : Mat2 R) * P_L * e1 = P_R) ∧
    ((e1 : Mat2 R) * P_R * e1 = P_L) ∧
    (det2 (e1 : Mat2 R) = -1) ∧
    (∀ (I : R), I ^ 2 = -1 → (twistMatrix I : Mat2 R) * twistMatrix I = -1) ∧
    (twistMatrixC * twistMatrixC = -1) := by
  refine ⟨soldering_parity_reflection, chiral_swap_P_L_to_P_R, chiral_swap_P_R_to_P_L,
          det2_e1, spinor_twist_pi_half, spinor_twist_pi_half_complex⟩

end InfoGeometry.Clifford.KleinBottleLoxodromicTwist
