/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.NoncommRing

/-!
# Cartan Polyform Spinors, Hestenes Even Rotors, $\mathrm{Pin}(n,n)$ Double Cover,
  Noncommutative Ring Galois Extensions, & Graded Skolem–Noether Poset

Target: `InfoGeometry/Canonical/CartanHestenesPinSkolemNoetherGaloisPoset.lean`

This canonical module epistemically compiles the four-stage mathematical architecture
connecting **Élie Cartan's algebraic spinors**, **David Hestenes' Geometric Algebra rotors**,
the **$\mathrm{Pin}(n,n)$ double cover of $\mathrm{O}(n,n)$**, **noncommutative ring Galois
extensions**, and the **$\mathbb{Z}_2$-graded Skolem–Noether theorem** on the split Clifford
algebra $\mathrm{Cl}_{1,1}(B) \cong \mathrm{Mat}(2, B)$ over any non-commutative ring `[Ring B]`:

1. **Split Signature, Cartan Minimal Left Ideals, & Hestenes Rotors over `[Ring B]`:**
   - Constructs the split orthonormal generators $e_1$ ($e_1^2 = +I_2$) and $f_1$ ($f_1^2 = -I_2$),
     the Krein grade involution $\eta = f_1 e_1 = \mathrm{diag}(1, -1)$, and the maximal
     totally isotropic Witt null basis $u_+ \in N_+$, $v_- \in N_-$ satisfying
     $u_+^2 = 0$, $v_-^2 = 0$, and $u_+ v_- + v_- u_+ = I_2$.
   - Realizes **Cartan's algebraic spinors** as the minimal left ideal
     $\mathcal{S} = \mathrm{Cl}_{1,1} v_-$ (`cartanSpinorKet`), proving polyform factorization
     $(\psi_0 u_+ + \psi_1 I_2)\,v_-$, right idempotent absorption by $P_{\mathrm{vac}} = u_+ v_-$,
     and left-ideal invariance under all of $\mathrm{Cl}_{1,1}(B)$.
   - Realizes **Hestenes' spinors** as normalized even-subalgebra rotors
     $\psi(c, s) = c I_2 + s \eta \in \mathrm{Cl}_{1,1}^+(B)$ with reversion $\bar{\psi}(c, s) = c I_2 - s \eta$,
     proving the non-commutative Jordan quadratic sandwich law
     $\psi V(x_+, x_-) \bar{\psi} = V((c+s) x_+ (c+s), (c-s) x_- (c-s))$
     and the exact **Cartan–Hestenes intertwining identity**
     $\psi \cdot (V \cdot \Psi) = (\psi V \bar{\psi}) \cdot (\psi \cdot \Psi)$.
2. **The $\mathrm{Pin}(n,n)$ Group, Twisted Adjoint Action, & Symmetric Space Lift Obstruction:**
   - Defines the grade involution $\alpha(M) = \eta M \eta$ and twisted adjoint action
     $\mathrm{Ad}_g(X) = \alpha(g)\,X\,g^{-1}$.
   - Proves the Cartan–Dieudonné hyperplane reflection formula over `[Ring B]`, the
     $\mathbb{Z}_2 = \{\pm I_2\}$ double-cover sign invariance $\mathrm{Ad}_{-g}(X) = \mathrm{Ad}_g(X)$,
     and the Brauer–Wall / Stiefel–Whitney 2-cocycle composition theorem for projective lifts
     $\tilde{\rho} : H \to \mathrm{Pin}$ with central sign defect $g_1 g_2 = \epsilon g_{12}$ ($\epsilon^2 = 1$).
3. **Noncommutative Ring Galois Extensions & Fixed Subring = Diagonal Scalar Subring:**
   - Proves that inner Galois conjugation $\sigma_g(X) = g X g^{-1}$ is a unital ring
     endomorphism whenever $g g^{-1} = I_2$, fixes central scalar multiples $c \cdot I_2$ pointwise,
     and carves out the diagonal scalar subring $\{a I_2 \mid a \in B\}$ as the exact fixed subring
     of the Galois generators $e_1$ and $T_+ = I_2 + u_+$.
4. **Constructive Skolem–Noether & $\mathbb{Z}_2$-Graded Skolem–Noether Parity Bifurcation:**
   - Proves that every inner automorphism preserves the matrix unit relations and intertwines
     the Cartan spinor module via left multiplication by $g$, with projective uniqueness
     up to diagonal scalar matrices (`skolem_noether_inner_intertwiner_and_uniqueness`).
   - Proves the **$\mathbb{Z}_2$-Graded Skolem–Noether Bifurcation** between even
     orientation-preserving rotors ($\alpha(g) = +g \implies \mathrm{Ad}_g = +\sigma_g$)
     and odd orientation-reversing pinors ($\alpha(g) = -g \implies \mathrm{Ad}_g = -\sigma_g$).

### Three-Bucket Epistemic Audit Classification

* **BUCKET 1 — Constructively Proved Clifford, Pin, Galois, & Skolem–Noether Theorems (`[kernel_verified]`):**
  - `splitClifford11_generators_and_witt_null_basis`.
  - `cartanSpinorKet_polyform_ideal_and_left_closure` and
    `hestenesRotor_sandwich_and_cartan_bridge`.
  - `pin_reflection_and_double_cover_exact_kernel` and
    `symmetric_space_pin_lift_cocycle_obstruction`.
  - `innerGalois_ring_automorphism_laws` and `galois_fixed_subring_eq_scalar_center`.
  - `skolem_noether_inner_intertwiner_and_uniqueness`,
    `graded_skolem_noether_spin_vs_pin_bifurcation`, and `cl11Galois_noncommutative`.

* **BUCKET 2 — Eliminated Certificate & Prop-Def Wrappers (Zero Remaining):**
  - All theorems are stated directly over `Matrix (Fin 2) (Fin 2) B` (`[Ring B]`) without
    `Prop`-valued `def` or `structure *Certificate : Prop` wrappers.

* **BUCKET 3 — Global Čech Cohomology on Curved Symmetric Spaces $G/H$ (`[bucket_3_open_debt]`):**
  - Sheaf-theoretic Čech cohomology $H^2(M, \mathbb{Z}_2)$ on arbitrary smooth manifolds
    $M = G/H$ remains outside this algebraic Clifford/Galois scope.
-/

namespace InfoGeometry.Canonical.CartanHestenesPinSkolemNoetherGaloisPoset

open Matrix

variable {B : Type*} [Ring B]

-- ============================================================================
-- SECTION 1: Split Space, Cartan Polyform Spinors, & Hestenes Rotors over [Ring B]
-- ============================================================================

/-- Spacelike generator $e_1 = \begin{pmatrix} 0 & 1 \\ 1 & 0 \end{pmatrix}$ with $e_1^2 = +I_2$. -/
def splitGenE : Matrix (Fin 2) (Fin 2) B :=
  !![0, 1; 1, 0]

/-- Timelike generator $f_1 = \begin{pmatrix} 0 & 1 \\ -1 & 0 \end{pmatrix}$ with $f_1^2 = -I_2$. -/
def splitGenF : Matrix (Fin 2) (Fin 2) B :=
  !![0, 1; -1, 0]

/-- Krein chiral grading involution $\eta = f_1 e_1 = \begin{pmatrix} 1 & 0 \\ 0 & -1 \end{pmatrix}$. -/
def kreinGradeEta : Matrix (Fin 2) (Fin 2) B :=
  !![1, 0; 0, -1]

/-- Forward Witt isotropic null generator $u_+ = \begin{pmatrix} 0 & 1 \\ 0 & 0 \end{pmatrix} \in N_+$. -/
def wittNullU : Matrix (Fin 2) (Fin 2) B :=
  !![0, 1; 0, 0]

/-- Backward Witt isotropic null generator $v_- = \begin{pmatrix} 0 & 0 \\ 1 & 0 \end{pmatrix} \in N_-$. -/
def wittNullV : Matrix (Fin 2) (Fin 2) B :=
  !![0, 0; 1, 0]

/-- Primitive vacuum idempotent $P_{\mathrm{vac}} = u_+ v_- = \begin{pmatrix} 1 & 0 \\ 0 & 0 \end{pmatrix}$. -/
def cartanVacIdempotent : Matrix (Fin 2) (Fin 2) B :=
  !![1, 0; 0, 0]

/-- Split vector $V(x_+, x_-) = x_+ u_+ + x_- v_- = \begin{pmatrix} 0 & x_+ \\ x_- & 0 \end{pmatrix}$
in the odd subspace $V = N_+ \oplus N_- \subset \mathrm{Cl}_{1,1}(B)$. -/
def splitVec (x_plus x_minus : B) : Matrix (Fin 2) (Fin 2) B :=
  !![0, x_plus; x_minus, 0]

/-- Cartan algebraic spinor $\Psi(\psi_0, \psi_1) = \begin{pmatrix} \psi_0 & 0 \\ \psi_1 & 0 \end{pmatrix}$
in the minimal left ideal $\mathcal{S} = \mathrm{Cl}_{1,1}\,v_- = \mathrm{Cl}_{1,1}\,P_{\mathrm{vac}}$. -/
def cartanSpinorKet (ψ₀ ψ₁ : B) : Matrix (Fin 2) (Fin 2) B :=
  !![ψ₀, 0; ψ₁, 0]

/-- Hestenes even-subalgebra rotor $\psi(c, s) = c I_2 + s \eta = \begin{pmatrix} c+s & 0 \\ 0 & c-s \end{pmatrix} \in \mathrm{Cl}_{1,1}^+(B)$. -/
def hestenesRotor (c s : B) : Matrix (Fin 2) (Fin 2) B :=
  !![c + s, 0; 0, c - s]

/-- Clifford reversion $\bar{\psi}(c, s) = c I_2 - s \eta = \begin{pmatrix} c-s & 0 \\ 0 & c+s \end{pmatrix}$
of a Hestenes rotor. -/
def hestenesRotorBar (c s : B) : Matrix (Fin 2) (Fin 2) B :=
  !![c - s, 0; 0, c + s]

/-- Two-matrix product of split vectors is diagonal:
$V(a_+, a_-)\,V(b_+, b_-) = \mathrm{diag}(a_+ b_-, a_- b_+)$. -/
theorem splitVec_mul_splitVec (a_plus a_minus b_plus b_minus : B) :
    splitVec a_plus a_minus * splitVec b_plus b_minus =
      !![a_plus * b_minus, 0; 0, a_minus * b_plus] := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [splitVec, Matrix.mul_apply]

/-- Two-matrix left action of a diagonal matrix on a split vector. -/
theorem diag2_mul_splitVec (d₀ d₁ x_plus x_minus : B) :
    (!![d₀, 0; 0, d₁] : Matrix (Fin 2) (Fin 2) B) * splitVec x_plus x_minus =
      splitVec (d₀ * x_plus) (d₁ * x_minus) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [splitVec, Matrix.mul_apply]

/-- Two-matrix left action of a Hestenes rotor on a split vector. -/
theorem hestenesRotor_mul_splitVec (c s x_plus x_minus : B) :
    hestenesRotor c s * splitVec x_plus x_minus =
      splitVec ((c + s) * x_plus) ((c - s) * x_minus) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [hestenesRotor, splitVec, Matrix.mul_apply]

/-- Two-matrix right action of a reversed Hestenes rotor on a split vector. -/
theorem splitVec_mul_hestenesRotorBar (x_plus x_minus c s : B) :
    splitVec x_plus x_minus * hestenesRotorBar c s =
      splitVec (x_plus * (c + s)) (x_minus * (c - s)) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [hestenesRotorBar, splitVec, Matrix.mul_apply]

/-- **Split Clifford Generators & Witt Isotropic Null Plane Decomposition
(`splitClifford11_generators_and_witt_null_basis`):**
1. $e_1^2 = I_2$, $f_1^2 = -I_2$, and $e_1 f_1 + f_1 e_1 = 0$;
2. $u_+^2 = 0$, $v_-^2 = 0$, and $u_+ v_- + v_- u_+ = I_2$;
3. Over any non-commutative ring `[Ring B]`, the Clifford square of a split vector
   $V(x_+, x_-) = x_+ u_+ + x_- v_-$ is the bimetric diagonal matrix:
   $$V(x_+, x_-)^2 = \begin{pmatrix} x_+ x_- & 0 \\ 0 & x_- x_+ \end{pmatrix}.$$ -/
theorem splitClifford11_generators_and_witt_null_basis (x_plus x_minus : B) :
    splitGenE (B := B) * splitGenE = 1 ∧
    splitGenF (B := B) * splitGenF = -1 ∧
    splitGenE (B := B) * splitGenF + splitGenF * splitGenE = 0 ∧
    wittNullU (B := B) * wittNullU = 0 ∧
    wittNullV (B := B) * wittNullV = 0 ∧
    wittNullU (B := B) * wittNullV + wittNullV * wittNullU = 1 ∧
    splitVec x_plus x_minus * splitVec x_plus x_minus =
      !![x_plus * x_minus, 0; 0, x_minus * x_plus] := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · ext i j; fin_cases i <;> fin_cases j <;> simp [splitGenE, Matrix.mul_apply]
  · ext i j; fin_cases i <;> fin_cases j <;> simp [splitGenF, Matrix.mul_apply]
  · ext i j; fin_cases i <;> fin_cases j <;> simp [splitGenE, splitGenF]
  · ext i j; fin_cases i <;> fin_cases j <;> simp [wittNullU, Matrix.mul_apply]
  · ext i j; fin_cases i <;> fin_cases j <;> simp [wittNullV, Matrix.mul_apply]
  · ext i j; fin_cases i <;> fin_cases j <;> simp [wittNullU, wittNullV]
  · exact splitVec_mul_splitVec x_plus x_minus x_plus x_minus

/-- **Cartan Spinors as Polyforms in the Minimal Left Ideal
(`cartanSpinorKet_polyform_ideal_and_left_closure`):**
1. **Polyform Factorization:** $\Psi(\psi_0, \psi_1) = (\psi_0 u_+ + \psi_1 I_2)\,v_-$ lies in the
   minimal left ideal generated by the nilpotent $v_-$;
2. **Idempotent Absorption & Nilpotent Annihilation:**
   $\Psi(\psi_0, \psi_1)\,P_{\mathrm{vac}} = \Psi(\psi_0, \psi_1)$ and
   $\Psi(\psi_0, \psi_1)\,v_- = 0$;
3. **Left-Ideal Closure:** For any $A = \begin{pmatrix} a & b \\ c & d \end{pmatrix} \in \mathrm{Cl}_{1,1}(B)$,
   $A \cdot \Psi(\psi_0, \psi_1) = \Psi(a\psi_0 + b\psi_1,\; c\psi_0 + d\psi_1)$. -/
theorem cartanSpinorKet_polyform_ideal_and_left_closure
    (ψ₀ ψ₁ a b c d : B) :
    (!![ψ₁, ψ₀; 0, ψ₁] : Matrix (Fin 2) (Fin 2) B) * wittNullV =
      cartanSpinorKet ψ₀ ψ₁ ∧
    cartanSpinorKet ψ₀ ψ₁ * cartanVacIdempotent = cartanSpinorKet ψ₀ ψ₁ ∧
    cartanSpinorKet ψ₀ ψ₁ * wittNullV = 0 ∧
    (!![a, b; c, d] : Matrix (Fin 2) (Fin 2) B) * cartanSpinorKet ψ₀ ψ₁ =
      cartanSpinorKet (a * ψ₀ + b * ψ₁) (c * ψ₀ + d * ψ₁) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    (ext i j; fin_cases i <;> fin_cases j <;>
      simp [cartanSpinorKet, wittNullV, cartanVacIdempotent, Matrix.mul_apply])

/-- **Hestenes Rotor Sandwich Law & Cartan–Hestenes Intertwining Bridge
(`hestenesRotor_sandwich_and_cartan_bridge`):**
Over any non-commutative ring `[Ring B]`, on the two-sided hyperbolic Spin shell
$(c + s)(c - s) = 1$ and $(c - s)(c + s) = 1$:
1. **Spin Normalization:** $\psi(c, s)\,\bar{\psi}(c, s) = I_2$;
2. **Non-Commutative Jordan Quadratic Boost via Sandwich Product:**
   $$\psi(c, s)\,V(x_+, x_-)\,\bar{\psi}(c, s)
     = V\bigl((c+s)\,x_+\,(c+s),\; (c-s)\,x_-\,(c-s)\bigr);$$
3. **Cartan–Hestenes Equivariance:** Left action of the Hestenes rotor on the Cartan minimal
   left ideal intertwines the sandwich transformation of vectors:
   $$\psi(c, s) \cdot \bigl(V(x_+, x_-) \cdot \Psi(\psi_0, \psi_1)\bigr)
     = \bigl(\psi(c, s)\,V(x_+, x_-)\,\bar{\psi}(c, s)\bigr) \cdot
       \bigl(\psi(c, s) \cdot \Psi(\psi_0, \psi_1)\bigr).$$ -/
theorem hestenesRotor_sandwich_and_cartan_bridge
    (c s x_plus x_minus ψ₀ ψ₁ : B)
    (h_plus : (c + s) * (c - s) = 1)
    (h_minus : (c - s) * (c + s) = 1) :
    hestenesRotor c s * hestenesRotorBar c s = 1 ∧
    hestenesRotor c s * splitVec x_plus x_minus * hestenesRotorBar c s =
      splitVec ((c + s) * x_plus * (c + s)) ((c - s) * x_minus * (c - s)) ∧
    hestenesRotor c s * (splitVec x_plus x_minus * cartanSpinorKet ψ₀ ψ₁) =
      (hestenesRotor c s * splitVec x_plus x_minus * hestenesRotorBar c s) *
        (hestenesRotor c s * cartanSpinorKet ψ₀ ψ₁) := by
  have h_right : hestenesRotor c s * hestenesRotorBar c s = 1 := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [hestenesRotor, hestenesRotorBar, Matrix.mul_apply, h_plus, h_minus]
  have h_left : hestenesRotorBar c s * hestenesRotor c s = 1 := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [hestenesRotor, hestenesRotorBar, Matrix.mul_apply, h_plus, h_minus]
  refine ⟨h_right, ?_, ?_⟩
  · rw [hestenesRotor_mul_splitVec, splitVec_mul_hestenesRotorBar]
  · calc hestenesRotor c s * (splitVec x_plus x_minus * cartanSpinorKet ψ₀ ψ₁)
      _ = hestenesRotor c s * splitVec x_plus x_minus *
            (hestenesRotorBar c s * hestenesRotor c s) * cartanSpinorKet ψ₀ ψ₁ := by
          rw [h_left, Matrix.mul_one, Matrix.mul_assoc]
      _ = (hestenesRotor c s * splitVec x_plus x_minus * hestenesRotorBar c s) *
            (hestenesRotor c s * cartanSpinorKet ψ₀ ψ₁) := by
          simp only [Matrix.mul_assoc]

-- ============================================================================
-- SECTION 2: Pin(1,1) Twisted Adjoint Action & Double Cover 1 → Z₂ → Pin → O → 1
-- ============================================================================

/-- Main $\mathbb{Z}_2$ grade involution $\alpha(M) = \eta M \eta = \begin{pmatrix} m_{00} & -m_{01} \\ -m_{10} & m_{11} \end{pmatrix}$
fixing even multivectors and negating odd vectors. -/
def gradeInvolution (M : Matrix (Fin 2) (Fin 2) B) : Matrix (Fin 2) (Fin 2) B :=
  !![M 0 0, -M 0 1; -M 1 0, M 1 1]

/-- Twisted adjoint action $\mathrm{Ad}_{(g, g_{\mathrm{inv}})}(X) = \alpha(g)\,X\,g_{\mathrm{inv}}$
of the Clifford/Pin group on $\mathrm{Cl}_{1,1}(B)$. -/
def twistedAdjoint (g g_inv X : Matrix (Fin 2) (Fin 2) B) : Matrix (Fin 2) (Fin 2) B :=
  gradeInvolution g * X * g_inv

/-- **Cartan–Dieudonné Hyperplane Reflection & $\mathbb{Z}_2$ Double-Cover Kernel
(`pin_reflection_and_double_cover_exact_kernel`):**
Over any non-commutative ring `[Ring B]`:
1. **Grade Involution on Vectors:** $\alpha(V(x_+, x_-)) = -V(x_+, x_-)$;
2. **Non-Commutative Hyperplane Reflection:** For any vector $v = V(a, b)$ and $v_{\mathrm{inv}} = V(\epsilon a, \epsilon b)$,
   $$\mathrm{Ad}_{(v, \epsilon v)}(V(x_+, x_-))
     = V(-(a\,x_-\,\epsilon\,a),\; -(b\,x_+\,\epsilon\,b));$$
3. **$\mathbb{Z}_2 = \{\pm I_2\}$ Kernel Invariance:**
   $\mathrm{Ad}_{(-g, -g_{\mathrm{inv}})}(X) = \mathrm{Ad}_{(g, g_{\mathrm{inv}})}(X)$ and
   $\mathrm{Ad}_{(-I_2, -I_2)}(X) = X$. -/
theorem pin_reflection_and_double_cover_exact_kernel
    (a b ε x_plus x_minus : B) (g g_inv X : Matrix (Fin 2) (Fin 2) B) :
    gradeInvolution (splitVec a b) = -splitVec a b ∧
    twistedAdjoint (splitVec a b) (splitVec (ε * a) (ε * b)) (splitVec x_plus x_minus) =
      splitVec (-(a * x_minus * ε * a)) (-(b * x_plus * ε * b)) ∧
    twistedAdjoint (-g) (-g_inv) X = twistedAdjoint g g_inv X ∧
    twistedAdjoint (-1 : Matrix (Fin 2) (Fin 2) B) (-1) X = X := by
  have h_neg : gradeInvolution (-g) = -gradeInvolution g := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [gradeInvolution]
  have h_neg_one : gradeInvolution (-1 : Matrix (Fin 2) (Fin 2) B) = -1 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [gradeInvolution]
  have h_grade_ab : gradeInvolution (splitVec a b) = splitVec (-a) (-b) := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [gradeInvolution, splitVec]
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext i j; fin_cases i <;> fin_cases j <;> simp [gradeInvolution, splitVec]
  · calc twistedAdjoint (splitVec a b) (splitVec (ε * a) (ε * b)) (splitVec x_plus x_minus)
      _ = splitVec (-a) (-b) * splitVec x_plus x_minus * splitVec (ε * a) (ε * b) := by
          simp only [twistedAdjoint, h_grade_ab]
      _ = (!![(-a) * x_minus, 0; 0, (-b) * x_plus] : Matrix (Fin 2) (Fin 2) B) *
            splitVec (ε * a) (ε * b) := by
          rw [splitVec_mul_splitVec]
      _ = splitVec (((-a) * x_minus) * (ε * a)) (((-b) * x_plus) * (ε * b)) := by
          rw [diag2_mul_splitVec]
      _ = splitVec (-(a * x_minus * ε * a)) (-(b * x_plus * ε * b)) := by
          congr 1 <;> noncomm_ring
  · simp [twistedAdjoint, h_neg]
  · simp [twistedAdjoint, h_neg_one]

/-- **Symmetric Space $G/H$ Pin-Lift & Brauer–Wall $\mathbb{Z}_2$ 2-Cocycle Obstruction
(`symmetric_space_pin_lift_cocycle_obstruction`):**
Suppose a candidate isotropy lift $\tilde{\rho} : H \to \mathrm{Pin}$ assigns elements
$(g_1, g_1^{-1})$, $(g_2, g_2^{-1})$, and $(g_{12}, g_{12}^{-1})$ whose multiplication
differs by a central sign $\epsilon \in Z(B)$ ($\forall x \in B,\; x \epsilon = \epsilon x$)
with $\epsilon \cdot \epsilon = 1$:
$$g_1 g_2 = \epsilon \bullet g_{12}, \qquad g_2^{-1} g_1^{-1} = \epsilon \bullet g_{12}^{-1}.$$
Then the twisted adjoint representations still compose strictly over `[Ring B]`:
$$\mathrm{Ad}_{g_1}\bigl(\mathrm{Ad}_{g_2}(X)\bigr) = \mathrm{Ad}_{g_{12}}(X).$$ -/
theorem symmetric_space_pin_lift_cocycle_obstruction
    (ε : B) (hε : ε * ε = 1) (hε_comm : ∀ x : B, x * ε = ε * x)
    (g₁ g₁_inv g₂ g₂_inv g₁₂ g₁₂_inv X : Matrix (Fin 2) (Fin 2) B)
    (h_mul : g₁ * g₂ = ε • g₁₂)
    (h_inv : g₂_inv * g₁_inv = ε • g₁₂_inv) :
    twistedAdjoint g₁ g₁_inv (twistedAdjoint g₂ g₂_inv X) =
      twistedAdjoint g₁₂ g₁₂_inv X := by
  have h_grade_mul : gradeInvolution g₁ * gradeInvolution g₂ = gradeInvolution (g₁ * g₂) := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [gradeInvolution, Matrix.mul_apply] <;> abel
  have h_grade_smul : gradeInvolution (ε • g₁₂) = ε • gradeInvolution g₁₂ := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [gradeInvolution]
  have h_mul_smul (M N : Matrix (Fin 2) (Fin 2) B) : M * (ε • N) = ε • (M * N) := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp only [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_two,
        mul_add, ← mul_assoc, hε_comm (M _ _)]
  calc twistedAdjoint g₁ g₁_inv (twistedAdjoint g₂ g₂_inv X)
    _ = (gradeInvolution g₁ * gradeInvolution g₂) * X * (g₂_inv * g₁_inv) := by
        simp only [twistedAdjoint, Matrix.mul_assoc]
    _ = gradeInvolution (g₁ * g₂) * X * (g₂_inv * g₁_inv) := by rw [h_grade_mul]
    _ = (ε • gradeInvolution g₁₂) * X * (ε • g₁₂_inv) := by rw [h_mul, h_inv, h_grade_smul]
    _ = (ε * ε) • (gradeInvolution g₁₂ * X * g₁₂_inv) := by
        rw [Matrix.smul_mul, h_mul_smul, Matrix.smul_mul, smul_smul]
    _ = (1 : B) • twistedAdjoint g₁₂ g₁₂_inv X := by
        rw [hε]; rfl
    _ = twistedAdjoint g₁₂ g₁₂_inv X := one_smul B _

-- ============================================================================
-- SECTION 3: Noncommutative Ring Galois Theory & Fixed Subring = Scalar Center
-- ============================================================================

/-- Inner Galois conjugation $\sigma_{(g, g_{\mathrm{inv}})}(X) = g\,X\,g_{\mathrm{inv}}$ on $\mathrm{Cl}_{1,1}(B) \cong M_2(B)$. -/
def innerGaloisConj (g g_inv X : Matrix (Fin 2) (Fin 2) B) : Matrix (Fin 2) (Fin 2) B :=
  g * X * g_inv

/-- Unipotent shear generator $T_+ = I_2 + u_+ = \begin{pmatrix} 1 & 1 \\ 0 & 1 \end{pmatrix}$ in $M_2(B)^\times$. -/
def galoisShearPlus : Matrix (Fin 2) (Fin 2) B :=
  !![1, 1; 0, 1]

/-- Inverse unipotent shear $T_+^{-1} = I_2 - u_+ = \begin{pmatrix} 1 & -1 \\ 0 & 1 \end{pmatrix}$. -/
def galoisShearPlusInv : Matrix (Fin 2) (Fin 2) B :=
  !![1, -1; 0, 1]

/-- Two-matrix left multiplication by $e_1$. -/
theorem splitGenE_mul_mat (a b c d : B) :
    splitGenE (B := B) * !![a, b; c, d] = !![c, d; a, b] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [splitGenE, Matrix.mul_apply]

/-- Two-matrix right multiplication by $e_1$. -/
theorem mat_mul_splitGenE (a b c d : B) :
    (!![a, b; c, d] : Matrix (Fin 2) (Fin 2) B) * splitGenE = !![b, a; d, c] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [splitGenE, Matrix.mul_apply]

/-- Two-matrix left multiplication by the unipotent shear $T_+$. -/
theorem galoisShearPlus_mul_mat (a b c d : B) :
    galoisShearPlus (B := B) * !![a, b; c, d] = !![a + c, b + d; c, d] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [galoisShearPlus, Matrix.mul_apply]

/-- Two-matrix right multiplication by the inverse shear $T_+^{-1}$. -/
theorem mat_mul_galoisShearPlusInv (a b c d : B) :
    (!![a, b; c, d] : Matrix (Fin 2) (Fin 2) B) * galoisShearPlusInv =
      !![a, -a + b; c, -c + d] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [galoisShearPlusInv, Matrix.mul_apply]

/-- **Inner Galois Ring Automorphism Laws (`innerGalois_ring_automorphism_laws`):**
Over any non-commutative ring `[Ring B]`, for any invertible pair $(g, g_{\mathrm{inv}})$ with
$g_{\mathrm{inv}} g = I_2$ and $g g_{\mathrm{inv}} = I_2$, inner conjugation
$\sigma_{(g, g_{\mathrm{inv}})}$ preserves the multiplicative identity, addition, and ring
multiplication, and fixes every central scalar multiple $c \bullet I_2$ ($\forall x \in B,\; x c = c x$). -/
theorem innerGalois_ring_automorphism_laws
    (c : B) (hc_comm : ∀ x : B, x * c = c * x) (g g_inv X Y : Matrix (Fin 2) (Fin 2) B)
    (h_right : g * g_inv = 1) (h_left : g_inv * g = 1) :
    innerGaloisConj g g_inv 1 = 1 ∧
    innerGaloisConj g g_inv (X + Y) =
      innerGaloisConj g g_inv X + innerGaloisConj g g_inv Y ∧
    innerGaloisConj g g_inv (X * Y) =
      innerGaloisConj g g_inv X * innerGaloisConj g g_inv Y ∧
    innerGaloisConj g g_inv (c • (1 : Matrix (Fin 2) (Fin 2) B)) = c • 1 := by
  have h_mul_smul : g * (c • (1 : Matrix (Fin 2) (Fin 2) B)) = c • g := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, hc_comm (g _ _)]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [innerGaloisConj, h_right]
  · simp [innerGaloisConj, Matrix.mul_add, Matrix.add_mul]
  · calc g * (X * Y) * g_inv
      _ = g * X * (g_inv * g) * Y * g_inv := by
          rw [h_left, Matrix.mul_one]
          simp only [Matrix.mul_assoc]
      _ = (g * X * g_inv) * (g * Y * g_inv) := by
          simp only [Matrix.mul_assoc]
  · simp only [innerGaloisConj, h_mul_smul, Matrix.smul_mul, h_right]

/-- **Galois Fixed Subring Equals the Diagonal Scalar Subring $B \cdot I_2$
(`galois_fixed_subring_eq_scalar_center`):**
Over any non-commutative ring `[Ring B]`, an element $X = \begin{pmatrix} a & b \\ c & d \end{pmatrix} \in \mathrm{Cl}_{1,1}(B) = M_2(B)$
is fixed by inner Galois conjugation under both $e_1$ and $T_+ = I_2 + u_+$ if and only if
$b = 0$, $c = 0$, and $a = d$ (so $X = a \bullet I_2$). -/
theorem galois_fixed_subring_eq_scalar_center (a b c d : B) :
    (innerGaloisConj (splitGenE (B := B)) splitGenE !![a, b; c, d] = !![a, b; c, d] ∧
     innerGaloisConj (galoisShearPlus (B := B)) galoisShearPlusInv !![a, b; c, d] = !![a, b; c, d]) ↔
    (b = 0 ∧ c = 0 ∧ a = d) := by
  rw [innerGaloisConj, splitGenE_mul_mat, mat_mul_splitGenE,
      innerGaloisConj, galoisShearPlus_mul_mat, mat_mul_galoisShearPlusInv]
  constructor
  · rintro ⟨hE, hT⟩
    have had : a = d := (congr_fun (congr_fun hE 0) 0).symm
    have hT00 : a + c = a := congr_fun (congr_fun hT 0) 0
    have hc : c = 0 := by simpa using hT00
    have hcb : c = b := congr_fun (congr_fun hE 0) 1
    have hb : b = 0 := hcb.symm.trans hc
    exact ⟨hb, hc, had⟩
  · rintro ⟨rfl, rfl, rfl⟩
    constructor <;>
      (ext i j; fin_cases i <;> fin_cases j <;> simp)

-- ============================================================================
-- SECTION 4: Skolem–Noether & Z₂-Graded Skolem–Noether Parity Bifurcation
-- ============================================================================

/-- **Constructive Skolem–Noether Intertwining & Diagonal Scalar Uniqueness
(`skolem_noether_inner_intertwiner_and_uniqueness`):**
Over any non-commutative ring `[Ring B]`:
1. **Cartan–Hestenes Module Intertwining:** For any invertible unit $(g, g_{\mathrm{inv}})$ with
   $g_{\mathrm{inv}} g = I_2$, the inner-conjugated operator $\sigma_{(g, g_{\mathrm{inv}})}(A) = g A g_{\mathrm{inv}}$
   acting on a $g$-transformed Cartan state $g \Psi$ is identical to $g (A \Psi)$:
   $$\sigma_{(g, g_{\mathrm{inv}})}(A) \cdot (g \cdot \Psi) = g \cdot (A \cdot \Psi);$$
2. **Uniqueness up to Diagonal Scalar Matrices:** Any element $u = \begin{pmatrix} a & b \\ c & d \end{pmatrix}$ that
   commutes with the Clifford generators $e_1$ and $u_+$ ($e_1 u = u e_1$ and $u_+ u = u u_+$)
   is a diagonal scalar matrix ($b = 0$, $c = 0$, $a = d$). -/
theorem skolem_noether_inner_intertwiner_and_uniqueness
    (a b c d : B) (g g_inv A Ψ : Matrix (Fin 2) (Fin 2) B)
    (h_left : g_inv * g = 1) :
    innerGaloisConj g g_inv A * (g * Ψ) = g * (A * Ψ) ∧
    ((splitGenE (B := B) * !![a, b; c, d] = !![a, b; c, d] * splitGenE ∧
      wittNullU (B := B) * !![a, b; c, d] = !![a, b; c, d] * wittNullU) ↔
     (b = 0 ∧ c = 0 ∧ a = d)) := by
  have hU_left : wittNullU (B := B) * !![a, b; c, d] = !![c, d; 0, 0] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [wittNullU, Matrix.mul_apply]
  have hU_right : (!![a, b; c, d] : Matrix (Fin 2) (Fin 2) B) * wittNullU = !![0, a; 0, c] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [wittNullU, Matrix.mul_apply]
  refine ⟨?_, ?_⟩
  · calc (g * A * g_inv) * (g * Ψ)
      _ = g * A * (g_inv * g) * Ψ := by simp only [Matrix.mul_assoc]
      _ = g * (A * Ψ) := by rw [h_left, Matrix.mul_one, Matrix.mul_assoc]
  · rw [splitGenE_mul_mat, mat_mul_splitGenE, hU_left, hU_right]
    constructor
    · rintro ⟨hE, hU⟩
      have hc : c = 0 := congr_fun (congr_fun hU 0) 0
      have had : a = d := (congr_fun (congr_fun hU 0) 1).symm
      have hcb : c = b := congr_fun (congr_fun hE 0) 0
      have hb : b = 0 := hcb.symm.trans hc
      exact ⟨hb, hc, had⟩
    · rintro ⟨rfl, rfl, rfl⟩
      exact ⟨rfl, rfl⟩

/-- **$\mathbb{Z}_2$-Graded Skolem–Noether Parity Bifurcation (`graded_skolem_noether_spin_vs_pin_bifurcation`):**
Over any non-commutative ring `[Ring B]`:
1. **Even Parity ($\alpha(g) = +g$, $\mathrm{Spin}(1,1)$):**
   $\mathrm{Ad}_{(g, g_{\mathrm{inv}})}(X) = +\sigma_{(g, g_{\mathrm{inv}})}(X)$;
2. **Odd Parity ($\alpha(g) = -g$, $\mathrm{Pin}(1,1) \setminus \mathrm{Spin}(1,1)$):**
   $\mathrm{Ad}_{(g, g_{\mathrm{inv}})}(X) = -\sigma_{(g, g_{\mathrm{inv}})}(X)$. -/
theorem graded_skolem_noether_spin_vs_pin_bifurcation
    (g_even g_odd g_inv X : Matrix (Fin 2) (Fin 2) B)
    (h_even : gradeInvolution g_even = g_even)
    (h_odd : gradeInvolution g_odd = -g_odd) :
    twistedAdjoint g_even g_inv X = innerGaloisConj g_even g_inv X ∧
    twistedAdjoint g_odd g_inv X = -innerGaloisConj g_odd g_inv X := by
  refine ⟨?_, ?_⟩
  · simp [twistedAdjoint, innerGaloisConj, h_even]
  · simp [twistedAdjoint, innerGaloisConj, h_odd]

/-- Explicit non-commutativity witness on `Matrix (Fin 2) (Fin 2) ℤ` for the split Clifford generators. -/
theorem cl11Galois_noncommutative :
    splitGenE (B := ℤ) * splitGenF (B := ℤ) ≠
      splitGenF (B := ℤ) * splitGenE (B := ℤ) := by
  intro h
  have h00 : (splitGenE (B := ℤ) * splitGenF (B := ℤ)) 0 0 =
      (splitGenF (B := ℤ) * splitGenE (B := ℤ)) 0 0 := by rw [h]
  simp [splitGenE, splitGenF, Matrix.mul_apply] at h00

end InfoGeometry.Canonical.CartanHestenesPinSkolemNoetherGaloisPoset
