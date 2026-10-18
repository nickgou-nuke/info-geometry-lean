/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import InfoGeometry.Synthesis.Cl22RealDiracCarrier
import InfoGeometry.Synthesis.Cl22LightconeWeylBerezinGaugeBridge

/-!
# Shirokov's Normalized Clifford Trace, Involutions, and Matrix-Free Determinant/Inverse in $\mathrm{Cl}(1,1)$ and $\mathrm{Cl}(2,2)$

This module formalizes Shirokov's basis-free normalized Clifford trace
$\mathrm{Tr}_{\mathrm{Cl}}(U) = 2^{-\lfloor n/2 \rfloor}\operatorname{tr}(U) = \langle U \rangle_0$,
the three fundamental Clifford involutions (grade involution $\widehat{U}$, reversion $\widetilde{U}$,
and Clifford conjugation $\widetilde{\widehat{U}}$), and the matrix-free determinant and inverse
formulas in $\mathrm{Cl}(1,1) \cong M_2(\mathbb{R})$ ($n = 2$) and
$\mathrm{Cl}(2,2) \cong M_4(\mathbb{R})$ ($n = 4$):

1. **Section 1 — Shirokov's $n = 2$ Clifford Trace, Involutions $\widehat{U}, \widetilde{U}, \widetilde{\widehat{U}}$, and Matrix-Free Determinant/Inverse in $\mathrm{Cl}(1,1) \cong M_2(\mathbb{R})$**:
   - Defines the $2 \times 2$ real Clifford generators `cl11GenE0`, `cl11GenE1`, `cl11GenE01`,
     the general multivector `cl11Multivector u0 u1 u2 u12`, and Shirokov's normalized trace
     `cl11ShirokovTrace U = (1 / 2) * Matrix.trace U`.
   - Proves rank-$0$ scalar extraction `cl11ShirokovTrace_multivector`, cyclic trace symmetry
     `cl11ShirokovTrace_mul_comm`, and trace invariance under grade involution `cl11GradeInvol`,
     reversion `cl11Reversion`, and Clifford conjugation `cl11CliffordConj`
     (`cl11ShirokovTrace_invariance`).
   - Proves Shirokov's $n = 2$ matrix-free determinant identity `cl11_shirokov_det_formula`
     ($U \widetilde{\widehat{U}} = \det(U) \mathbf{1}_2$,
     $\det(U) = u_0^2 - u_1^2 + u_2^2 - u_{12}^2$) and the matrix-free two-sided inverse formula
     `cl11_shirokov_inverse_formula` ($U^{-1} = \det(U)^{-1} \widetilde{\widehat{U}}$).
2. **Section 2 — Shirokov's $n = 4$ Normalized Trace $\mathrm{Tr}_{\mathrm{Cl}}(U) = \frac{1}{4}\operatorname{tr}(U)$, Degree-$4$ Determinant Homogeneity, and Matrix-Free Inverse in $\mathrm{Cl}(2,2) \cong M_4(\mathbb{R})$**:
   - Defines `cl22ShirokovTrace U = (1 / 4) * Matrix.trace U` on $M_4(\mathbb{R})$ and proves
     rank-$0$ scalar extraction `cl22ShirokovTrace_weylScaledMultivector` and cyclic symmetry
     `cl22ShirokovTrace_mul_comm`.
   - Proves determinant multiplicativity `cl22_det_mul`, degree-$4$ scaling homogeneity
     `cl22_det_smul_degree_four` ($\det(\alpha U) = \alpha^4 \det(U)$), and the explicit
     matrix-free two-sided inverse `weylScaledSolderedVector_shirokov_inverse` for Weyl-scaled
     soldered lightcone vectors.
-/

set_option autoImplicit false

noncomputable section

open scoped Matrix
open Matrix
open InfoGeometry.Synthesis.Cl22RealDiracCarrier
open InfoGeometry.Synthesis.Cl22LightconeWeylBerezinGaugeBridge

namespace InfoGeometry.Synthesis.ShirokovCliffordTraceDetInverseBridge

/-!
## Section 1: Shirokov's $n = 2$ Clifford Trace, Involutions, and Matrix-Free Determinant/Inverse in $\mathrm{Cl}(1,1) \cong M_2(\mathbb{R})$
-/

/-- Timelike generator $e_0 = \begin{pmatrix} 0 & 1 \\ 1 & 0 \end{pmatrix} \in M_2(\mathbb{R})$
of $\mathrm{Cl}(1,1)$ ($e_0^2 = +\mathbf{1}_2$). -/
def cl11GenE0 : Matrix (Fin 2) (Fin 2) ℝ :=
  !![0, 1;
     1, 0]

/-- Spacelike generator $e_1 = \begin{pmatrix} 0 & 1 \\ -1 & 0 \end{pmatrix} \in M_2(\mathbb{R})$
of $\mathrm{Cl}(1,1)$ ($e_1^2 = -\mathbf{1}_2$). -/
def cl11GenE1 : Matrix (Fin 2) (Fin 2) ℝ :=
  !![ 0, 1;
     -1, 0]

/-- Bivector pseudoscalar $e_{01} = e_0 e_1 = \begin{pmatrix} -1 & 0 \\ 0 & 1 \end{pmatrix} \in M_2(\mathbb{R})$
of $\mathrm{Cl}(1,1)$ ($e_{01}^2 = +\mathbf{1}_2$). -/
def cl11GenE01 : Matrix (Fin 2) (Fin 2) ℝ :=
  cl11GenE0 * cl11GenE1

/-- Explicit non-commutativity witness for the $2 \times 2$ real Clifford carrier $M_2(\mathbb{R})$:
`cl11GenE0 * cl11GenE1 ≠ cl11GenE1 * cl11GenE0`. -/
theorem cl11GenE0_mul_cl11GenE1_ne_comm :
    cl11GenE0 * cl11GenE1 ≠ cl11GenE1 * cl11GenE0 := by
  intro h_comm
  have h00 : (cl11GenE0 * cl11GenE1) 0 0 = (cl11GenE1 * cl11GenE0) 0 0 :=
    congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 0) h_comm
  revert h00
  simp [cl11GenE0, cl11GenE1, Matrix.mul_apply, Fin.sum_univ_two]
  norm_num

/-- General 4-component multivector $U = u_0 \mathbf{1}_2 + u_1 e_0 + u_2 e_1 + u_{12} e_{01}$
in $\mathrm{Cl}(1,1) \cong M_2(\mathbb{R})$. -/
def cl11Multivector (u0 u1 u2 u12 : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  u0 • (1 : Matrix (Fin 2) (Fin 2) ℝ) +
    u1 • cl11GenE0 +
    u2 • cl11GenE1 +
    u12 • cl11GenE01

/-- Shirokov's normalized Clifford trace $\mathrm{Tr}_{\mathrm{Cl}}(U) = \frac{1}{2}\operatorname{tr}(U)$
for $n = 2$ ($2^{\lfloor 2/2 \rfloor} = 2$). -/
def cl11ShirokovTrace (U : Matrix (Fin 2) (Fin 2) ℝ) : ℝ :=
  (1 / 2 : ℝ) * Matrix.trace U

/-- The unnormalized matrix trace of `cl11Multivector u0 u1 u2 u12` equals `2 * u0`. -/
theorem cl11Multivector_trace_eq (u0 u1 u2 u12 : ℝ) :
    Matrix.trace (cl11Multivector u0 u1 u2 u12) = 2 * u0 := by
  have _ := (u0, u1, u2, u12)
  unfold cl11Multivector cl11GenE01 cl11GenE0 cl11GenE1
  simp [Matrix.trace, Matrix.diag, Fin.sum_univ_two]
  ring

/-- Shirokov's normalized trace extracts the exact rank-$0$ scalar component $\langle U \rangle_0 = u_0$
of any multivector $U \in \mathrm{Cl}(1,1)$, since $\operatorname{tr}(e_0) = \operatorname{tr}(e_1) = \operatorname{tr}(e_{01}) = 0$. -/
theorem cl11ShirokovTrace_multivector (u0 u1 u2 u12 : ℝ) :
    cl11ShirokovTrace (cl11Multivector u0 u1 u2 u12) = u0 := by
  have h_scale : (1 / 2 : ℝ) * (2 * u0) = u0 := by
    ring
  unfold cl11ShirokovTrace
  rw [cl11Multivector_trace_eq u0 u1 u2 u12]
  exact h_scale

/-- Cyclic symmetry of Shirokov's normalized Clifford trace on $M_2(\mathbb{R})$:
$\mathrm{Tr}_{\mathrm{Cl}}(U V) = \mathrm{Tr}_{\mathrm{Cl}}(V U)$. -/
theorem cl11ShirokovTrace_mul_comm (U V : Matrix (Fin 2) (Fin 2) ℝ) :
    cl11ShirokovTrace (U * V) = cl11ShirokovTrace (V * U) := by
  unfold cl11ShirokovTrace
  rw [Matrix.trace_mul_comm U V]

/-- Grade involution $\widehat{U} = \langle U \rangle_0 - \langle U \rangle_1 + \langle U \rangle_2$
in $\mathrm{Cl}(1,1)$, negating odd-grade vector components $(u_1, u_2) \mapsto (-u_1, -u_2)$. -/
def cl11GradeInvol (u0 u1 u2 u12 : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  cl11Multivector u0 (-u1) (-u2) u12

/-- Reversion $\widetilde{U} = \langle U \rangle_0 + \langle U \rangle_1 - \langle U \rangle_2$
in $\mathrm{Cl}(1,1)$, negating the rank-$2$ bivector component $u_{12} \mapsto -u_{12}$. -/
def cl11Reversion (u0 u1 u2 u12 : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  cl11Multivector u0 u1 u2 (-u12)

/-- Clifford conjugation $\widetilde{\widehat{U}} = \langle U \rangle_0 - \langle U \rangle_1 - \langle U \rangle_2$
in $\mathrm{Cl}(1,1)$, negating both rank-$1$ and rank-$2$ components. -/
def cl11CliffordConj (u0 u1 u2 u12 : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  cl11Multivector u0 (-u1) (-u2) (-u12)

/-- Shirokov's normalized trace is invariant under grade involution $\widehat{U}$,
reversion $\widetilde{U}$, and Clifford conjugation $\widetilde{\widehat{U}}$. -/
theorem cl11ShirokovTrace_invariance (u0 u1 u2 u12 : ℝ) :
    cl11ShirokovTrace (cl11GradeInvol u0 u1 u2 u12) = u0 ∧
    cl11ShirokovTrace (cl11Reversion u0 u1 u2 u12) = u0 ∧
    cl11ShirokovTrace (cl11CliffordConj u0 u1 u2 u12) = u0 := by
  refine ⟨?_, ?_, ?_⟩
  · unfold cl11GradeInvol
    exact cl11ShirokovTrace_multivector u0 (-u1) (-u2) u12
  · unfold cl11Reversion
    exact cl11ShirokovTrace_multivector u0 u1 u2 (-u12)
  · unfold cl11CliffordConj
    exact cl11ShirokovTrace_multivector u0 (-u1) (-u2) (-u12)

/-- The scalar Shirokov determinant polynomial
$\Delta(u_0, u_1, u_2, u_{12}) = u_0^2 - u_1^2 + u_2^2 - u_{12}^2$ for $\mathrm{Cl}(1,1)$. -/
def cl11DetScalar (u0 u1 u2 u12 : ℝ) : ℝ :=
  u0 ^ 2 - u1 ^ 2 + u2 ^ 2 - u12 ^ 2

/-- Left multiplication by the Clifford conjugate $\widetilde{\widehat{U}} U = \det(U) \mathbf{1}_2$. -/
theorem cl11_cliffordConj_mul_multivector (u0 u1 u2 u12 : ℝ) :
    cl11CliffordConj u0 u1 u2 u12 * cl11Multivector u0 u1 u2 u12 =
      cl11DetScalar u0 u1 u2 u12 • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  have _ := (u0, u1, u2, u12)
  ext i j
  fin_cases i <;> fin_cases j <;>
    (simp [cl11CliffordConj, cl11Multivector, cl11DetScalar, cl11GenE01, cl11GenE0, cl11GenE1,
      Matrix.mul_apply, Fin.sum_univ_two];
     ring)

/-- **Shirokov's $n = 2$ Matrix-Free Determinant Formula in $\mathrm{Cl}(1,1)$**:
For every multivector $U = u_0 \mathbf{1}_2 + u_1 e_0 + u_2 e_1 + u_{12} e_{01} \in \mathrm{Cl}(1,1)$,
the Clifford product $U \widetilde{\widehat{U}}$ is the scalar multiple
$(u_0^2 - u_1^2 + u_2^2 - u_{12}^2) \mathbf{1}_2$, and coincides identically with the matrix
determinant $\det(U)$. -/
theorem cl11_shirokov_det_formula (u0 u1 u2 u12 : ℝ) :
    cl11Multivector u0 u1 u2 u12 * cl11CliffordConj u0 u1 u2 u12 =
      cl11DetScalar u0 u1 u2 u12 • (1 : Matrix (Fin 2) (Fin 2) ℝ) ∧
    Matrix.det (cl11Multivector u0 u1 u2 u12) = cl11DetScalar u0 u1 u2 u12 := by
  refine ⟨?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      (simp [cl11CliffordConj, cl11Multivector, cl11DetScalar, cl11GenE01, cl11GenE0, cl11GenE1,
        Matrix.mul_apply, Fin.sum_univ_two];
       ring)
  · rw [Matrix.det_fin_two]
    simp [cl11Multivector, cl11DetScalar, cl11GenE01, cl11GenE0, cl11GenE1]
    ring

/-- **Shirokov's $n = 2$ Matrix-Free Inverse Formula in $\mathrm{Cl}(1,1)$**:
Whenever $\Delta = \mathrm{cl11DetScalar}(u_0, u_1, u_2, u_{12})$ has reciprocal `invDet`
($\Delta \cdot \mathrm{invDet} = 1$), the scaled Clifford conjugate
$U^{-1} = \mathrm{invDet} \cdot \widetilde{\widehat{U}}$ is the exact two-sided multiplicative
inverse of $U = \mathrm{cl11Multivector}(u_0, u_1, u_2, u_{12})$. -/
theorem cl11_shirokov_inverse_formula (u0 u1 u2 u12 invDet : ℝ)
    (h_inv : cl11DetScalar u0 u1 u2 u12 * invDet = 1) :
    cl11Multivector u0 u1 u2 u12 * (invDet • cl11CliffordConj u0 u1 u2 u12) =
      (1 : Matrix (Fin 2) (Fin 2) ℝ) ∧
    (invDet • cl11CliffordConj u0 u1 u2 u12) * cl11Multivector u0 u1 u2 u12 =
      (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  have h_comm : invDet * cl11DetScalar u0 u1 u2 u12 = 1 := by
    rw [mul_comm, h_inv]
  refine ⟨?_, ?_⟩
  · rw [Matrix.mul_smul, (cl11_shirokov_det_formula u0 u1 u2 u12).1,
        smul_smul, h_comm, one_smul]
  · rw [Matrix.smul_mul, cl11_cliffordConj_mul_multivector u0 u1 u2 u12,
        smul_smul, h_comm, one_smul]

/-!
## Section 2: Shirokov's $n = 4$ Normalized Trace, Degree-$4$ Determinant Homogeneity, and Matrix-Free Inverse in $\mathrm{Cl}(2,2) \cong M_4(\mathbb{R})$
-/

/-- Local alias of the real Dirac generator $e_0 \in M_4(\mathbb{R})$ for explicit $M_4(\mathbb{R})$
carrier typing. -/
def cl22E0 : Matrix (Fin 4) (Fin 4) ℝ := e0

/-- Local alias of the real Dirac generator $e_1 \in M_4(\mathbb{R})$ for explicit $M_4(\mathbb{R})$
carrier typing. -/
def cl22E1 : Matrix (Fin 4) (Fin 4) ℝ := e1

/-- Explicit non-commutativity witness on the $4 \times 4$ real Dirac carrier $M_4(\mathbb{R})$:
`cl22E0 * cl22E1 ≠ cl22E1 * cl22E0`. -/
theorem cl22E0_mul_cl22E1_ne_comm :
    cl22E0 * cl22E1 ≠ cl22E1 * cl22E0 :=
  e0_mul_e1_ne_comm

/-- Shirokov's normalized Clifford trace $\mathrm{Tr}_{\mathrm{Cl}}(U) = \frac{1}{4}\operatorname{tr}(U)$
for $n = 4$ ($2^{\lfloor 4/2 \rfloor} = 4$) on $\mathrm{Cl}(2,2) \cong M_4(\mathbb{R})$. -/
def cl22ShirokovTrace (U : Matrix (Fin 4) (Fin 4) ℝ) : ℝ :=
  (1 / 4 : ℝ) * Matrix.trace U

/-- Shirokov's $n = 4$ normalized trace extracts the exact rank-$0$ scalar coefficient $\alpha$
of any Weyl-scaled multivector `weylScaledMultivector alpha a b c d lam invLam`, independent of
the scale parameter $\lambda$ and the non-scalar amplitudes $(a, b, c, d)$. -/
theorem cl22ShirokovTrace_weylScaledMultivector (alpha a b c d lam invLam : ℝ) :
    cl22ShirokovTrace (weylScaledMultivector alpha a b c d lam invLam) = alpha := by
  have h_scale : (1 / 4 : ℝ) * (4 * alpha) = alpha := by
    ring
  unfold cl22ShirokovTrace
  rw [weylScaledMultivector_trace_eq alpha a b c d lam invLam]
  exact h_scale

/-- Cyclic symmetry of Shirokov's $n = 4$ normalized Clifford trace on $M_4(\mathbb{R})$:
$\mathrm{Tr}_{\mathrm{Cl}}(U V) = \mathrm{Tr}_{\mathrm{Cl}}(V U)$. -/
theorem cl22ShirokovTrace_mul_comm (U V : Matrix (Fin 4) (Fin 4) ℝ) :
    cl22ShirokovTrace (U * V) = cl22ShirokovTrace (V * U) := by
  unfold cl22ShirokovTrace
  rw [Matrix.trace_mul_comm U V]

/-- Multiplicativity of the $n = 4$ Clifford determinant on $\mathrm{Cl}(2,2) \cong M_4(\mathbb{R})$:
$\det(U V) = \det(U) \det(V)$. -/
theorem cl22_det_mul (U V : Matrix (Fin 4) (Fin 4) ℝ) :
    Matrix.det (U * V) = Matrix.det U * Matrix.det V :=
  Matrix.det_mul U V

/-- Degree-$4$ homogeneity of the Clifford determinant on $\mathrm{Cl}(2,2) \cong M_4(\mathbb{R})$:
$\det(\alpha U) = \alpha^4 \det(U)$ ($N = 2^{\lfloor 4/2 \rfloor} = 4$). -/
theorem cl22_det_smul_degree_four (alpha : ℝ) (U : Matrix (Fin 4) (Fin 4) ℝ) :
    Matrix.det (alpha • U) = alpha ^ 4 * Matrix.det U := by
  rw [Matrix.det_smul U alpha]
  simp

/-- **Shirokov's Matrix-Free Inverse Formula for Weyl-Scaled Soldered Lightcone Vectors in $\mathrm{Cl}(2,2)$**:
For any reciprocal scale pair $\lambda \cdot \lambda^{-1} = 1$ and any soldered lightcone vector
$X(\lambda) = (\lambda a) n_+^{(1)} + (\lambda^{-1} b) n_-^{(1)} + c e_3 \in M_4(\mathbb{R})$
whose conformal interval $q = 2 a b - c^2$ has reciprocal `invQ` ($q \cdot \mathrm{invQ} = 1$),
the scaled multivector $X(\lambda)^{-1} = \mathrm{invQ} \cdot X(\lambda)$ is the exact
two-sided multiplicative inverse of $X(\lambda)$. -/
theorem weylScaledSolderedVector_shirokov_inverse
    (a b c lam invLam invQ : ℝ)
    (h_recip : lam * invLam = 1)
    (h_inv : (2 * a * b - c ^ 2) * invQ = 1) :
    weylScaledSolderedVector a b c lam invLam *
        (invQ • weylScaledSolderedVector a b c lam invLam) =
      (1 : Matrix (Fin 4) (Fin 4) ℝ) ∧
    (invQ • weylScaledSolderedVector a b c lam invLam) *
        weylScaledSolderedVector a b c lam invLam =
      (1 : Matrix (Fin 4) (Fin 4) ℝ) := by
  have hsq := weylScaledSolderedVector_sq_invariant a b c lam invLam h_recip
  have h_comm : invQ * (2 * a * b - c ^ 2) = 1 := by
    rw [mul_comm, h_inv]
  refine ⟨?_, ?_⟩
  · rw [Matrix.mul_smul, hsq, smul_smul, h_comm, one_smul]
  · rw [Matrix.smul_mul, hsq, smul_smul, h_comm, one_smul]

end InfoGeometry.Synthesis.ShirokovCliffordTraceDetInverseBridge
