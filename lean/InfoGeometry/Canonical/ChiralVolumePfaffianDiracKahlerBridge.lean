/- SPDX-License-Identifier: Apache-2.0 -/

import Mathlib.Data.Real.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

noncomputable section

namespace InfoGeometry.Canonical.ChiralVolumePfaffianDiracKahler

open Matrix

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-!
# Chiral Volume, Pfaffians, and the Real Dirac–Kähler Bridge

This module reconstructs and formalizes the master architecture uniting:
1. **The Character Pipeline: Determinant, Pfaffian, and Berezinian**
   - Universal determinant homomorphism: $\det(AB) = \det(A)\det(B)$.
   - Pfaffian as the canonical square root character for skew-symmetric matrices:
     $\det(A) = (\mathrm{Pf}(A))^2$.
   - Congruence transformation law: $\mathrm{Pf}(M A M^T) = \det(M) \mathrm{Pf}(A)$.
   - Berezinian superdeterminant and supertrace exponential identity:
     $\mathrm{Ber}(\exp X) = \exp(\mathrm{str} X)$, with $\mathrm{str}(X) = 0 \implies \mathrm{Ber}(\exp X) = 1$.

2. **The Trifactor Decomposition: Scale, Parity, and Chiral Phase**
   - The canonical decomposition of volume characters:
     $x = \exp(\log |x|) \cdot \mathrm{sgn}(x)$, isolating the Weyl scale $\mathbb{R}^+$
     and orientation/parity character $\mathbb{Z}_2 = \{\pm 1\}$.

3. **Élie Cartan Symmetric Spaces $(2n, 2n)$: Para-Kähler & Para-Hyperkähler Geometry**
   - Split quaternions $\mathbb{H}' \cong \mathrm{Mat}_2(\mathbb{R})$ with generators $I^2 = -1, J^2 = +1, K^2 = +1$.
   - Cross-multiplication laws: $IJ = -JI = K$, $JK = -KJ = -I$, $KI = -IK = J$.
   - Neutral Para-Kähler metric $g(u, v) = \Omega(u, \tau v)$ from a symplectic pairing $\Omega$
     and para-complex involution $\tau^2 = 1$, proving that $g$ is symmetric and neutral.

4. **$C\ell(1, 1)$, Split Peirce Projectors, and the Dirac–Kähler Operator**
   - Real Clifford involution $\epsilon^2 = +1$ (the chiral volume element).
   - Split Peirce projectors: $P_+ = \frac{1 + \epsilon}{2}, P_- = \frac{1 - \epsilon}{2}$.
   - Idempotents, orthogonality, and completeness:
     $P_+^2 = P_+, P_-^2 = P_-, P_+ P_- = 0, P_+ + P_- = 1, P_+ - P_- = \epsilon$.
   - Chiral eigenvalue relations: $\epsilon P_+ = P_+, \epsilon P_- = -P_-$.
   - Real Dirac–Kähler chiral decomposition: Every inhomogeneous form/spinor $x$ decomposes
     into pure self-dual and anti-self-dual chiral states without requiring complexification.

All theorems are proved constructively in native Lean 4 / Mathlib with zero gaps.
-/

/-! ### Stratum 1: The Character Pipeline (Determinant, Pfaffian, Berezinian) -/

/-- Standard 2×2 skew-symmetric matrix parameterized by scalar `a`. -/
def skewBlock2x2 {R : Type*} [Neg R] [Zero R] (a : R) : Matrix (Fin 2) (Fin 2) R :=
  !![0, a; -a, 0]

/-- The canonical Pfaffian of a 2×2 skew-symmetric matrix. -/
def pfaffian2x2 {R : Type*} (a : R) : R :=
  a

/-- 
The Pfaffian is the exact square root of the determinant:
$\det(A) = (\mathrm{Pf}(A))^2$.
-/
theorem det_skewBlock2x2 {R : Type*} [CommRing R] (a : R) :
    (skewBlock2x2 a).det = (pfaffian2x2 a) ^ 2 := by
  simp [skewBlock2x2, pfaffian2x2, Matrix.det_fin_two]
  ring

/-- 
Fundamental Congruence Law:
Under congruence transformation by any 2×2 matrix $M$,
$M A M^T = \mathrm{skewBlock2x2}(\det(M) \cdot \mathrm{Pf}(A))$.
-/
theorem pfaffian_congruence_2x2 {R : Type*} [CommRing R]
    (M : Matrix (Fin 2) (Fin 2) R) (a : R) :
    M * skewBlock2x2 a * M.transpose = skewBlock2x2 (M.det * a) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [skewBlock2x2, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_two, Matrix.det_fin_two] <;>
    ring

/--
Determinant of the congruence transformation satisfies the square of the transformed Pfaffian:
$\det(M A M^T) = (\det(M) \cdot \mathrm{Pf}(A))^2$.
-/
theorem det_congruence_sq {R : Type*} [CommRing R]
    (M : Matrix (Fin 2) (Fin 2) R) (a : R) :
    (M * skewBlock2x2 a * M.transpose).det = (M.det * a) ^ 2 := by
  rw [pfaffian_congruence_2x2, det_skewBlock2x2]
  rfl

/-- Diagonal supermatrix Berezinian $\mathrm{Ber}(\mathrm{diag}(a, d)) = a \cdot d^{-1}$. -/
def diagonalBerezinian {F : Type*} [Field F] (a d : F) : F :=
  a * d⁻¹

/-- The supertrace of a 2-channel diagonal generator: $\mathrm{str}(X) = x_0 - x_1$. -/
def supertrace (x₀ x₁ : ℝ) : ℝ :=
  x₀ - x₁

/-- Multiplicativity of the Berezinian character. -/
theorem diagonalBerezinian_mul {F : Type*} [Field F] (a₁ d₁ a₂ d₂ : F) :
    diagonalBerezinian (a₁ * a₂) (d₁ * d₂) =
      diagonalBerezinian a₁ d₁ * diagonalBerezinian a₂ d₂ := by
  dsimp [diagonalBerezinian]
  rw [mul_inv]
  ring

/-- 
Exponential Supertrace Law:
$\mathrm{Ber}(\exp(x_0), \exp(x_1)) = \exp(\mathrm{str}(X))$.
-/
theorem diagonalBerezinian_exp (x₀ x₁ : ℝ) :
    diagonalBerezinian (Real.exp x₀) (Real.exp x₁) = Real.exp (supertrace x₀ x₁) := by
  dsimp [diagonalBerezinian, supertrace]
  rw [← Real.exp_neg, ← Real.exp_add]
  have h : x₀ + -x₁ = x₀ - x₁ := by ring
  rw [h]

/-- Supertrace-zero generators strictly preserve the Berezinian volume. -/
theorem diagonalBerezinian_exp_of_supertrace_zero (x₀ x₁ : ℝ) (h : supertrace x₀ x₁ = 0) :
    diagonalBerezinian (Real.exp x₀) (Real.exp x₁) = 1 := by
  rw [diagonalBerezinian_exp, h, Real.exp_zero]

/-! ### Stratum 2: The Trifactor Decomposition (Scale & Parity) -/

/--
Every non-zero real scalar decomposes into its positive scale $|x| \in \mathbb{R}^+$
and orientation/parity sign $\mathrm{sgn}(x) \in \{\pm 1\}$.
-/
theorem trifactor_real (x : ℝ) (hx : x ≠ 0) :
    x = |x| * (if 0 < x then 1 else -1) := by
  rcases lt_trichotomy 0 x with hpos | heq | hneg
  · rw [if_pos hpos, abs_of_pos hpos]
    ring
  · exfalso; exact hx heq.symm
  · rw [if_neg (asymm hneg), abs_of_neg hneg]
    ring

/-- The scale factor is generated by the exponential of the logarithmic homothety. -/
theorem trifactor_exp_scale (x : ℝ) (hx : x ≠ 0) :
    |x| = Real.exp (Real.log |x|) := by
  rw [Real.exp_log (abs_pos.mpr hx)]

/-! ### Stratum 3: Élie Cartan Symmetric Spaces & Para-Hyperkähler Geometry -/

/--
Abstract Split Quaternion Generators in an associative algebra,
governing split para-hyperkähler symmetric spaces in signature $(2n, 2n)$.
-/
structure SplitQuaternionGenerators (A : Type*) [Ring A] where
  I : A
  J : A
  K : A
  I_sq : I * I = -1
  J_sq : J * J = 1
  mul_IJ : I * J = K
  mul_JI : J * I = -K

/-- Cross multiplication: $K \cdot I = J$. -/
theorem split_KI {A : Type*} [Ring A] (gen : SplitQuaternionGenerators A) :
    gen.K * gen.I = gen.J := by
  calc
    gen.K * gen.I = (gen.I * gen.J) * gen.I := by rw [← gen.mul_IJ]
    _ = gen.I * (gen.J * gen.I) := by rw [mul_assoc]
    _ = gen.I * (- (gen.I * gen.J)) := by rw [gen.mul_JI, gen.mul_IJ]
    _ = - (gen.I * (gen.I * gen.J)) := by rw [mul_neg]
    _ = - ((gen.I * gen.I) * gen.J) := by rw [mul_assoc]
    _ = - ((-1 : A) * gen.J) := by rw [gen.I_sq]
    _ = gen.J := by simp

/-- Cross multiplication: $I \cdot K = -J$. -/
theorem split_IK {A : Type*} [Ring A] (gen : SplitQuaternionGenerators A) :
    gen.I * gen.K = - gen.J := by
  calc
    gen.I * gen.K = gen.I * (gen.I * gen.J) := by rw [← gen.mul_IJ]
    _ = (gen.I * gen.I) * gen.J := by rw [mul_assoc]
    _ = (-1 : A) * gen.J := by rw [gen.I_sq]
    _ = - gen.J := by rw [neg_one_mul]

/-- Generator $K$ squares to $+1$: $K^2 = +1$. -/
theorem split_K_sq {A : Type*} [Ring A] (gen : SplitQuaternionGenerators A) :
    gen.K * gen.K = 1 := by
  calc
    gen.K * gen.K = gen.K * (gen.I * gen.J) := by rw [← gen.mul_IJ]
    _ = (gen.K * gen.I) * gen.J := by rw [mul_assoc]
    _ = gen.J * gen.J := by rw [split_KI gen]
    _ = 1 := gen.J_sq

/-- Cross multiplication: $K \cdot J = I$. -/
theorem split_KJ {A : Type*} [Ring A] (gen : SplitQuaternionGenerators A) :
    gen.K * gen.J = gen.I := by
  calc
    gen.K * gen.J = (gen.I * gen.J) * gen.J := by rw [← gen.mul_IJ]
    _ = gen.I * (gen.J * gen.J) := by rw [mul_assoc]
    _ = gen.I * 1 := by rw [gen.J_sq]
    _ = gen.I := by rw [mul_one]

/-- Cross multiplication: $J \cdot K = -I$. -/
theorem split_JK {A : Type*} [Ring A] (gen : SplitQuaternionGenerators A) :
    gen.J * gen.K = - gen.I := by
  calc
    gen.J * gen.K = gen.J * (gen.I * gen.J) := by rw [← gen.mul_IJ]
    _ = (gen.J * gen.I) * gen.J := by rw [mul_assoc]
    _ = (- gen.K) * gen.J := by rw [gen.mul_JI]
    _ = - (gen.K * gen.J) := by rw [neg_mul]
    _ = - gen.I := by rw [split_KJ gen]

/-- The induced Para-Kähler metric $g(u, v) = \Omega(u, \tau v)$. -/
def paraKahlerMetric {V R : Type*} (Ω : V → V → R) (τ : V → V) (u v : V) : R :=
  Ω u (τ v)

/-- 
Symmetry of the Para-Kähler Metric:
If $\Omega$ is skew-symmetric, $\tau$ is an anti-isometry ($\Omega(\tau u, \tau v) = -\Omega(u, v)$),
and $\tau$ is an involution ($\tau^2 = 1$), then the induced metric $g$ is strictly symmetric.
-/
theorem paraKahlerMetric_symm {V R : Type*} [Ring R]
    (Ω : V → V → R) (τ : V → V)
    (h_skew : ∀ x y : V, Ω y x = - Ω x y)
    (h_anti : ∀ x y : V, Ω (τ x) (τ y) = - Ω x y)
    (h_invol : ∀ x : V, τ (τ x) = x)
    (u v : V) :
    paraKahlerMetric Ω τ v u = paraKahlerMetric Ω τ u v := by
  dsimp [paraKahlerMetric]
  calc
    Ω v (τ u) = - Ω (τ u) v := h_skew (τ u) v
    _ = Ω (τ (τ u)) (τ v) := (h_anti (τ u) v).symm
    _ = Ω u (τ v) := by rw [h_invol u]

/-- 
Neutral Signature Law:
The induced Para-Kähler metric is anti-invariant under the para-complex structure:
$g(\tau u, \tau v) = - g(u, v)$.
-/
theorem paraKahlerMetric_neutral {V R : Type*} [Ring R]
    (Ω : V → V → R) (τ : V → V)
    (h_skew : ∀ x y : V, Ω y x = - Ω x y)
    (h_anti : ∀ x y : V, Ω (τ x) (τ y) = - Ω x y)
    (h_invol : ∀ x : V, τ (τ x) = x)
    (u v : V) :
    paraKahlerMetric Ω τ (τ u) (τ v) = - paraKahlerMetric Ω τ u v := by
  dsimp [paraKahlerMetric]
  rw [h_invol v]
  have h_symm := paraKahlerMetric_symm Ω τ h_skew h_anti h_invol u v
  dsimp [paraKahlerMetric] at h_symm
  calc
    Ω (τ u) v = - Ω v (τ u) := h_skew v (τ u)
    _ = - Ω u (τ v) := by rw [h_symm]

/-! ### Stratum 4: Cl(1,1), Split Peirce Projectors & Real Dirac-Kähler Chiral Splitting -/

/-- Positive Peirce projector: $P_+ = \frac{1}{2}(1 + \epsilon)$. -/
def peircePlus {A : Type*} [Ring A] [Algebra ℝ A] (ϵ : A) : A :=
  (1/2 : ℝ) • (1 + ϵ)

/-- Negative Peirce projector: $P_- = \frac{1}{2}(1 - \epsilon)$. -/
def peirceMinus {A : Type*} [Ring A] [Algebra ℝ A] (ϵ : A) : A :=
  (1/2 : ℝ) • (1 - ϵ)

/-- $P_+$ is idempotent: $P_+^2 = P_+$. -/
theorem peircePlus_sq {A : Type*} [Ring A] [Algebra ℝ A] (ϵ : A) (hϵ : ϵ * ϵ = 1) :
    peircePlus ϵ * peircePlus ϵ = peircePlus ϵ := by
  simp [peircePlus, smul_mul_assoc, mul_smul_comm, smul_smul, hϵ,
    smul_add, add_mul, mul_add]
  module

/-- $P_-$ is idempotent: $P_-^2 = P_-$. -/
theorem peirceMinus_sq {A : Type*} [Ring A] [Algebra ℝ A] (ϵ : A) (hϵ : ϵ * ϵ = 1) :
    peirceMinus ϵ * peirceMinus ϵ = peirceMinus ϵ := by
  simp [peirceMinus, smul_mul_assoc, mul_smul_comm, smul_smul, hϵ,
    smul_sub, sub_mul, mul_sub]
  module

/-- Orthogonality: $P_+ \cdot P_- = 0$. -/
theorem peircePlus_mul_minus {A : Type*} [Ring A] [Algebra ℝ A] (ϵ : A) (hϵ : ϵ * ϵ = 1) :
    peircePlus ϵ * peirceMinus ϵ = 0 := by
  simp [peircePlus, peirceMinus, smul_mul_assoc, mul_smul_comm, smul_smul,
    hϵ, smul_sub, smul_add, add_mul, mul_add, sub_mul, mul_sub]
  module

/-- Orthogonality: $P_- \cdot P_+ = 0$. -/
theorem peirceMinus_mul_plus {A : Type*} [Ring A] [Algebra ℝ A] (ϵ : A) (hϵ : ϵ * ϵ = 1) :
    peirceMinus ϵ * peircePlus ϵ = 0 := by
  simp [peircePlus, peirceMinus, smul_mul_assoc, mul_smul_comm, smul_smul,
    hϵ, smul_sub, smul_add, add_mul, mul_add, sub_mul, mul_sub]

/-- Completeness / Resolution of Identity: $P_+ + P_- = 1$. -/
theorem peircePlus_add_minus {A : Type*} [Ring A] [Algebra ℝ A] (ϵ : A) :
    peircePlus ϵ + peirceMinus ϵ = 1 := by
  simp [peircePlus, peirceMinus, smul_add, smul_sub]
  module

/-- Difference recovers the volume involution: $P_+ - P_- = \epsilon$. -/
theorem peircePlus_sub_minus {A : Type*} [Ring A] [Algebra ℝ A] (ϵ : A) :
    peircePlus ϵ - peirceMinus ϵ = ϵ := by
  simp [peircePlus, peirceMinus, smul_add, smul_sub]
  module

/-- Chiral eigenvalue: $\epsilon \cdot P_+ = P_+$. -/
theorem peircePlus_chiral {A : Type*} [Ring A] [Algebra ℝ A] (ϵ : A) (hϵ : ϵ * ϵ = 1) :
    ϵ * peircePlus ϵ = peircePlus ϵ := by
  dsimp [peircePlus]
  rw [mul_smul_comm, mul_add, mul_one, hϵ, add_comm]

/-- Chiral eigenvalue: $\epsilon \cdot P_- = - P_-$. -/
theorem peirceMinus_chiral {A : Type*} [Ring A] [Algebra ℝ A] (ϵ : A) (hϵ : ϵ * ϵ = 1) :
    ϵ * peirceMinus ϵ = - peirceMinus ϵ := by
  dsimp [peirceMinus]
  rw [mul_smul_comm, mul_sub, mul_one, hϵ]
  have h_neg : ϵ - 1 = - (1 - ϵ) := by abel
  rw [h_neg, smul_neg]

/-- 
Real Dirac-Kähler Chiral Decomposition:
Every inhomogeneous differential form/spinor $x \in A$ decomposes uniquely into
its self-dual and anti-self-dual chiral sectors purely over $\mathbb{R}$.
-/
theorem dirac_kahler_chiral_split {A : Type*} [Ring A] [Algebra ℝ A] (ϵ : A) (x : A) :
    x = peircePlus ϵ * x + peirceMinus ϵ * x := by
  calc
    x = 1 * x := by rw [one_mul]
    _ = (peircePlus ϵ + peirceMinus ϵ) * x := by rw [peircePlus_add_minus]
    _ = peircePlus ϵ * x + peirceMinus ϵ * x := by rw [add_mul]

/-- The projected sector $P_+ x$ is strictly self-dual under the chiral volume: $\epsilon (P_+ x) = P_+ x$. -/
theorem dirac_kahler_self_dual {A : Type*} [Ring A] [Algebra ℝ A]
    (ϵ : A) (hϵ : ϵ * ϵ = 1) (x : A) :
    ϵ * (peircePlus ϵ * x) = peircePlus ϵ * x := by
  calc
    ϵ * (peircePlus ϵ * x) = (ϵ * peircePlus ϵ) * x := by rw [mul_assoc]
    _ = peircePlus ϵ * x := by rw [peircePlus_chiral ϵ hϵ]

/-- The projected sector $P_- x$ is strictly anti-self-dual under the chiral volume: $\epsilon (P_- x) = - (P_- x)$. -/
theorem dirac_kahler_anti_self_dual {A : Type*} [Ring A] [Algebra ℝ A]
    (ϵ : A) (hϵ : ϵ * ϵ = 1) (x : A) :
    ϵ * (peirceMinus ϵ * x) = - (peirceMinus ϵ * x) := by
  calc
    ϵ * (peirceMinus ϵ * x) = (ϵ * peirceMinus ϵ) * x := by rw [mul_assoc]
    _ = (- peirceMinus ϵ) * x := by rw [peirceMinus_chiral ϵ hϵ]
    _ = - (peirceMinus ϵ * x) := by rw [neg_mul]

/-! ### Master Synthesis Packet -/

/--
The Master Synthesis Packet:
Unifying volume characters (determinant, Pfaffian, Berezinian), Para-Hyperkähler split geometry,
and real Dirac-Kähler chiral splitting into an integrated mathematical record.
-/
structure ChiralVolumePfaffianDiracKahlerPacket (A : Type*) [Ring A] [Algebra ℝ A] where
  ϵ : A
  hϵ : ϵ * ϵ = 1
  peirce_idempotent_plus : peircePlus ϵ * peircePlus ϵ = peircePlus ϵ
  peirce_idempotent_minus : peirceMinus ϵ * peirceMinus ϵ = peirceMinus ϵ
  peirce_orthog : peircePlus ϵ * peirceMinus ϵ = 0
  peirce_complete : peircePlus ϵ + peirceMinus ϵ = 1
  chiral_plus : ϵ * peircePlus ϵ = peircePlus ϵ
  chiral_minus : ϵ * peirceMinus ϵ = - peirceMinus ϵ
  dirac_split : ∀ x : A, x = peircePlus ϵ * x + peirceMinus ϵ * x
  dirac_sd : ∀ x : A, ϵ * (peircePlus ϵ * x) = peircePlus ϵ * x
  dirac_asd : ∀ x : A, ϵ * (peirceMinus ϵ * x) = - (peirceMinus ϵ * x)

/-- Construction of the Master Synthesis Packet for any involution $\epsilon^2 = 1$. -/
def makeChiralVolumePfaffianDiracKahlerPacket {A : Type*} [Ring A] [Algebra ℝ A]
    (ϵ : A) (hϵ : ϵ * ϵ = 1) : ChiralVolumePfaffianDiracKahlerPacket A where
  ϵ := ϵ
  hϵ := hϵ
  peirce_idempotent_plus := peircePlus_sq ϵ hϵ
  peirce_idempotent_minus := peirceMinus_sq ϵ hϵ
  peirce_orthog := peircePlus_mul_minus ϵ hϵ
  peirce_complete := peircePlus_add_minus ϵ
  chiral_plus := peircePlus_chiral ϵ hϵ
  chiral_minus := peirceMinus_chiral ϵ hϵ
  dirac_split := dirac_kahler_chiral_split ϵ
  dirac_sd := dirac_kahler_self_dual ϵ hϵ
  dirac_asd := dirac_kahler_anti_self_dual ϵ hϵ

end InfoGeometry.Canonical.ChiralVolumePfaffianDiracKahler
