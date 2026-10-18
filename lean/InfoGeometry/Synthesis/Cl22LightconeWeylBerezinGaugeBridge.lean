/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import InfoGeometry.Synthesis.Cl22RealDiracCarrier
import InfoGeometry.NCG.BerezinianSuperdeterminant
import InfoGeometry.Supergeometry.BerezinianDecomposition

/-!
# $\mathrm{Cl}(2,2)$ Paracomplex-Lightcone Coordinate Transition, $\lambda \leftrightarrow \lambda^{-1}$ Dual $\mathrm{Cl}(1,1)$ Scaling, and Chiral Schur-Expression Weyl Invariance

This module formalizes the four-part mathematical synthesis connecting the doubled
real Dirac matrix realization satisfying the $\mathrm{Cl}(2,2)$ relations
to conformal dilaton scaling ($\lambda = e^\tau \leftrightarrow \lambda^{-1} = e^{-\tau}$) and
Weyl scaling identities:

1. **Section 1 (Paracomplex/Hypercomplex Duality & Coordinate Transition in $\mathrm{Cl}(2,2)$)**:
   - Establishes mutually inverse coordinate transitions between the standard 4-component
     bivector block $\mathcal{B}_{\mathrm{std}} = \{\mathbf{1}, \omega_1, J_{\mathrm{geom}}, \omega_1 J_{\mathrm{geom}}\}$
     and the Peircian lightcone socle $\mathcal{B}_{\mathrm{light}} = \{P_+^{(1)}, P_-^{(1)}, J_{\mathrm{geom}}, \omega_1 J_{\mathrm{geom}}\}$.
   - Proves that the cross-sheet complex twin $J_{\mathrm{geom}} = e_0 e_2$ anticommutes with
     the intra-sheet paracomplex unit $\omega_1 = e_0 e_1$ (`J_geom_anticomm_omega1`) and
     intertwines/swaps the incoming and outgoing Peircian projectors (`J_geom_intertwines_peircian_projectors`,
     `J_geom_conjugates_peircianPlus1_to_Minus1`).

2. **Section 2 (Scale Symmetry $\lambda \leftrightarrow 1/\lambda$: Duality Between $\mathrm{Cl}(1,1)$ and Inverse $\mathrm{Cl}(1,1)$)**:
   - Defines the Weyl-scaled lightcone Majorana modes $n_+^{(1)}(\lambda) = \lambda n_+^{(1)}$
     (incoming causal shell) and $n_-^{(1)}(\lambda) = \lambda^{-1} n_-^{(1)}$ (outgoing
     retrocausal shell), together with their logarithmic-time specializations
     $n_+^{(1)}(\tau) = e^\tau n_+^{(1)}$ and $n_-^{(1)}(\tau) = e^{-\tau} n_-^{(1)}$.
   - Proves nilpotency at all scales (`weylScaledMajorana_sq_zero`) and exact Weyl gauge
     invariance of the CAR Witt anticommutator:
     $$\{n_+^{(1)}(\lambda), n_-^{(1)}(\lambda)\} = 2 \cdot \mathbf{1}_4 \quad (\lambda \cdot \lambda^{-1} = 1), \qquad
       \{n_+^{(1)}(\tau), n_-^{(1)}(\tau)\} = 2 \cdot \mathbf{1}_4 \quad (\forall \tau \in \mathbb{R}).$$

3. **Section 3 (Separation of Trace and Conformal Determinant Under $\lambda \leftrightarrow \lambda^{-1}$ Scaling)**:
   - Proves that all non-identity $\mathrm{Cl}(2,2)$ generators ($n_+^{(1)}, n_-^{(1)}, \omega_1, J_{\mathrm{geom}}, \Omega, e_3$)
     are strictly traceless (`cl22_nontrivial_modes_traceless`), so the matrix trace of a
     Weyl-scaled multivector depends solely on the identity coefficient $\alpha$:
     $$\operatorname{Tr}(\alpha \mathbf{1}_4 + (\lambda a) n_+^{(1)} + (\lambda^{-1} b) n_-^{(1)} + c J_{\mathrm{geom}} + d \Omega)
       = \alpha \cdot \operatorname{Tr}(\mathbf{1}_4) = 4 \alpha.$$
   - Proves that the soldered lightcone operator
     $X(\lambda) = (\lambda a) n_+^{(1)} + (\lambda^{-1} b) n_-^{(1)} + c e_3 \in M_4(\mathbb{R})$
     squares to the $\lambda$-independent conformal interval $(2 a b - c^2) \mathbf{1}_4$
     (`weylScaledSolderedVector_sq_invariant`), and that the $2 \times 2$ lightcone Gram
     matrix $\begin{pmatrix} \lambda a & c \\ c & \lambda^{-1} b \end{pmatrix}$ has exact
     Weyl-invariant determinant $a b - c^2$ (`lightconeGramMatrix_det_weyl_invariant`).

4. **Section 4 (Chiral Schur Expression & Vanishing Weyl Scale Derivative)**:
   - Proves that for any $2 \times 2$ block matrix
     $T(\lambda) = \begin{pmatrix} A & \lambda \cdot B \\lambda^{-1} \cdot C & D \end{pmatrix}$
     whose blocks scale oppositely by $\lambda$ and $\lambda^{-1}$, the expression defined
     by berezinianSchur is independent of $\lambda$ (berezinianSchur_weyl_gauge_invariant
     and logTimeBerezinianSchur_eq_const), with zero derivative in logarithmic time $\tau$
     (deriv_logTimeBerezinianSchur_eq_zero). No inverse laws for invD or invDetD are assumed.
-/

set_option autoImplicit false

noncomputable section

open scoped Matrix
open Matrix
open InfoGeometry.Synthesis.Cl22RealDiracCarrier
open InfoGeometry.NCG

namespace InfoGeometry.Synthesis.Cl22LightconeWeylBerezinGaugeBridge

/-!
## Section 1: Paracomplex/Hypercomplex Duality and Basis Transition in $\mathrm{Cl}(2,2)$
-/

/-- Local alias of $J_{\mathrm{geom}} \in M_4(\mathbb{R})$ for explicit $M_4(\mathbb{R})$ carrier typing. -/
def diracJGeom : Matrix (Fin 4) (Fin 4) ℝ := J_geom

/-- Local alias of $\omega_1 \in M_4(\mathbb{R})$ for explicit $M_4(\mathbb{R})$ carrier typing. -/
def diracOmega1 : Matrix (Fin 4) (Fin 4) ℝ := omega1

/-- Explicit non-commutativity witness on the $4 \times 4$ real Dirac matrix carrier $M_4(\mathbb{R})$:
the cross-sheet complex structure $J_{\mathrm{geom}} = e_0 e_2$ and the intra-sheet paracomplex
unit $\omega_1 = e_0 e_1$ do not commute ($J_{\mathrm{geom}} \omega_1
eq \omega_1 J_{\mathrm{geom}}$). -/
theorem J_geom_mul_omega1_ne_comm :
    diracJGeom * diracOmega1 ≠ diracOmega1 * diracJGeom := by
  intro h_comm
  have h03 : (diracJGeom * diracOmega1) 0 3 = (diracOmega1 * diracJGeom) 0 3 :=
    congrArg (fun M : Matrix (Fin 4) (Fin 4) ℝ => M 0 3) h_comm
  revert h03
  rcases bivector_explicit_matrices with ⟨hw1, _, hJg, _⟩
  unfold diracJGeom diracOmega1
  rw [hw1, hJg]
  simp [Matrix.mul_apply, Fin.sum_univ_four]
  norm_num

/-- The cross-sheet complex twin $J_{\mathrm{geom}} = e_0 e_2$ ($J_{\mathrm{geom}}^2 = -I$)
strictly anticommutes with the intra-sheet paracomplex unit $\omega_1 = e_0 e_1$ ($\omega_1^2 = +I$):
$$J_{\mathrm{geom}} \omega_1 + \omega_1 J_{\mathrm{geom}} = 0 \quad \text{and} \quad
  J_{\mathrm{geom}} \omega_1 = -\omega_1 J_{\mathrm{geom}}.$$ -/
theorem J_geom_anticomm_omega1 :
    J_geom * omega1 + omega1 * J_geom = 0 ∧
    J_geom * omega1 = -(omega1 * J_geom) := by
  rcases bivector_explicit_matrices with ⟨hw1, _, hJg, _⟩
  rw [hw1, hJg]
  constructor <;>
    (ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_four])

/-- Standard 4-component multivector combination in $\mathcal{B}_{\mathrm{std}} = \{\mathbf{1}, \omega_1, J_{\mathrm{geom}}, \omega_1 J_{\mathrm{geom}}\}$. -/
def stdBivectorBlock (a b c d : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  a • (1 : Matrix (Fin 4) (Fin 4) ℝ) + b • omega1 + c • J_geom + d • (omega1 * J_geom)

/-- Lightcone Peircian 4-component combination in $\mathcal{B}_{\mathrm{light}} = \{P_+^{(1)}, P_-^{(1)}, J_{\mathrm{geom}}, \omega_1 J_{\mathrm{geom}}\}$. -/
def lightconePeircianBlock (uPlus uMinus c d : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  uPlus • peircianPlus1 + uMinus • peircianMinus1 + c • J_geom + d • (omega1 * J_geom)

/-- **Theorem 1.1 (Exact Basis Transition Between Standard Multivector Block and Lightcone Peircian Socle)**:
For any $(a, b, c, d) \in \mathbb{R}^4$, the standard multivector expansion equals the lightcone
Peircian expansion with incoming amplitude $u_+ = a + b$ and outgoing amplitude $u_- = a - b$:
$$a \mathbf{1} + b \omega_1 + c J_{\mathrm{geom}} + d (\omega_1 J_{\mathrm{geom}})
  = (a + b) P_+^{(1)} + (a - b) P_-^{(1)} + c J_{\mathrm{geom}} + d (\omega_1 J_{\mathrm{geom}}).$$ -/
theorem stdBivectorBlock_eq_lightconePeircianBlock (a b c d : ℝ) :
    stdBivectorBlock a b c d = lightconePeircianBlock (a + b) (a - b) c d := by
  rcases bivector_explicit_matrices with ⟨hw1, _, hJg, _⟩
  unfold stdBivectorBlock lightconePeircianBlock peircianPlus1 peircianMinus1
  rw [hw1, hJg]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp <;> ring

/-- Inverse basis transition recovering standard coordinates $a = \frac{1}{2}(u_+ + u_-)$ and
$b = \frac{1}{2}(u_+ - u_-)$ from lightcone Peircian coordinates $(u_+, u_-)$. -/
theorem lightconePeircianBlock_eq_stdBivectorBlock (uPlus uMinus c d : ℝ) :
    lightconePeircianBlock uPlus uMinus c d =
      stdBivectorBlock ((1 / 2 : ℝ) * (uPlus + uMinus)) ((1 / 2 : ℝ) * (uPlus - uMinus)) c d := by
  rw [stdBivectorBlock_eq_lightconePeircianBlock]
  have h_plus : (1 / 2 : ℝ) * (uPlus + uMinus) + (1 / 2 : ℝ) * (uPlus - uMinus) = uPlus := by ring
  have h_minus : (1 / 2 : ℝ) * (uPlus + uMinus) - (1 / 2 : ℝ) * (uPlus - uMinus) = uMinus := by ring
  rw [h_plus, h_minus]

/-- **Theorem 1.2 (Möbius Flip / Chiral Switch of Lightcone Projectors by the Complex Twin $J_{\mathrm{geom}}$)**:
Multiplication and conjugation by $J_{\mathrm{geom}}$ transmutes the incoming Peircian projector
$P_+^{(1)}$ into the outgoing Peircian projector $P_-^{(1)}$ and vice versa:
$$J_{\mathrm{geom}} P_+^{(1)} = P_-^{(1)} J_{\mathrm{geom}}, \quad
  J_{\mathrm{geom}} P_-^{(1)} = P_+^{(1)} J_{\mathrm{geom}}, \quad
  (-J_{\mathrm{geom}}) P_+^{(1)} J_{\mathrm{geom}} = P_-^{(1)}, \quad
  (-J_{\mathrm{geom}}) P_-^{(1)} J_{\mathrm{geom}} = P_+^{(1)}.$$ -/
theorem J_geom_intertwines_and_swaps_peircian_projectors :
    J_geom * peircianPlus1 = peircianMinus1 * J_geom ∧
    J_geom * peircianMinus1 = peircianPlus1 * J_geom ∧
    (-J_geom) * peircianPlus1 * J_geom = peircianMinus1 ∧
    (-J_geom) * peircianMinus1 * J_geom = peircianPlus1 := by
  have hJ_om : J_geom * omega1 = -(omega1 * J_geom) := J_geom_anticomm_omega1.2
  have hJ_sq : J_geom * J_geom = -(1 : Matrix (Fin 4) (Fin 4) ℝ) :=
    cl22_hypercomplex_and_geometric_i.2.2.1
  have h1 : J_geom * peircianPlus1 = peircianMinus1 * J_geom := by
    unfold peircianPlus1 peircianMinus1
    rw [Matrix.mul_smul, Matrix.smul_mul, mul_add, mul_one, sub_mul, one_mul, hJ_om, ← sub_eq_add_neg]
  have h2 : J_geom * peircianMinus1 = peircianPlus1 * J_geom := by
    unfold peircianPlus1 peircianMinus1
    rw [Matrix.mul_smul, Matrix.smul_mul, mul_sub, mul_one, add_mul, one_mul, hJ_om, sub_neg_eq_add]
  have h3 : (-J_geom) * peircianPlus1 * J_geom = peircianMinus1 := by
    rw [neg_mul, h1, neg_mul, mul_assoc, hJ_sq, mul_neg, mul_one, neg_neg]
  have h4 : (-J_geom) * peircianMinus1 * J_geom = peircianPlus1 := by
    rw [neg_mul, h2, neg_mul, mul_assoc, hJ_sq, mul_neg, mul_one, neg_neg]
  exact ⟨h1, h2, h3, h4⟩

/-!
## Section 2: Scale Symmetry $\lambda \leftrightarrow 1/\lambda$ and CAR Normalization
-/

/-- Weyl-scaled incoming (causal) Majorana null mode $n_+^{(1)}(\lambda) = \lambda \cdot n_+^{(1)}$. -/
def weylNPlus1 (lam : ℝ) : Matrix (Fin 4) (Fin 4) ℝ := lam • n_plus_1

/-- Weyl-scaled outgoing (retrocausal) Majorana null mode $n_-^{(1)}(\lambda^{-1}) = \lambda^{-1} \cdot n_-^{(1)}$. -/
def weylNMinus1 (invLam : ℝ) : Matrix (Fin 4) (Fin 4) ℝ := invLam • n_minus_1

/-- Weyl-scaled Sheet-2 incoming Majorana null mode $n_+^{(2)}(\lambda) = \lambda \cdot n_+^{(2)}$. -/
def weylNPlus2 (lam : ℝ) : Matrix (Fin 4) (Fin 4) ℝ := lam • n_plus_2

/-- Weyl-scaled Sheet-2 outgoing Majorana null mode $n_-^{(2)}(\lambda^{-1}) = \lambda^{-1} \cdot n_-^{(2)}$. -/
def weylNMinus2 (invLam : ℝ) : Matrix (Fin 4) (Fin 4) ℝ := invLam • n_minus_2

/-- **Theorem 2.1 (Scale-Invariant Nilpotency of Weyl-Scaled Majorana Modes)**:
For any scale parameters $\lambda, \mu \in \mathbb{R}$, all four scaled lightcone Majorana
operators remain strictly nilpotent of index 2. -/
theorem weylScaledMajorana_sq_zero (lam mu : ℝ) :
    weylNPlus1 lam * weylNPlus1 lam = 0 ∧
    weylNMinus1 mu * weylNMinus1 mu = 0 ∧
    weylNPlus2 lam * weylNPlus2 lam = 0 ∧
    weylNMinus2 mu * weylNMinus2 mu = 0 := by
  rcases majorana_nilpotency with ⟨h1, h2, h3, h4⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold weylNPlus1; rw [smul_mul_smul_comm, h1, smul_zero]
  · unfold weylNMinus1; rw [smul_mul_smul_comm, h2, smul_zero]
  · unfold weylNPlus2; rw [smul_mul_smul_comm, h3, smul_zero]
  · unfold weylNMinus2; rw [smul_mul_smul_comm, h4, smul_zero]

/-- **Theorem 2.2 (Weyl Gauge Invariance of the CAR Witt Anticommutator Under $\lambda \leftrightarrow \lambda^{-1}$)**:
For any reciprocal scale pair $(\lambda, \lambda^{-1})$ satisfying $\lambda \cdot \lambda^{-1} = 1$,
the causal expansion $\lambda n_+^{(a)}$ and retrocausal contraction $\lambda^{-1} n_-^{(a)}$
neutralize in the CAR anticommutator:
$$\{n_+^{(1)}(\lambda), n_-^{(1)}(\lambda^{-1})\} = 2 \cdot \mathbf{1}_4 \quad \text{and} \quad
  \{n_+^{(2)}(\lambda), n_-^{(2)}(\lambda^{-1})\} = 2 \cdot \mathbf{1}_4.$$ -/
theorem weylScaledMajorana_car_invariant (lam invLam : ℝ) (h_recip : lam * invLam = 1) :
    weylNPlus1 lam * weylNMinus1 invLam + weylNMinus1 invLam * weylNPlus1 lam =
      (2 : ℝ) • (1 : Matrix (Fin 4) (Fin 4) ℝ) ∧
    weylNPlus2 lam * weylNMinus2 invLam + weylNMinus2 invLam * weylNPlus2 lam =
      (2 : ℝ) • (1 : Matrix (Fin 4) (Fin 4) ℝ) := by
  rcases majorana_witt_anticommutation_relations with ⟨hw1, hw2, _, _⟩
  have h_comm : invLam * lam = 1 := by rw [mul_comm, h_recip]
  constructor
  · unfold weylNPlus1 weylNMinus1
    rw [smul_mul_smul_comm, smul_mul_smul_comm, h_recip, h_comm, one_smul, one_smul, hw1]
  · unfold weylNPlus2 weylNMinus2
    rw [smul_mul_smul_comm, smul_mul_smul_comm, h_recip, h_comm, one_smul, one_smul, hw2]

/-- Logarithmic-time incoming wavefront shell $n_+^{(1)}(\tau) = e^\tau n_+^{(1)}$. -/
def logTimeNPlus1 (tau : ℝ) : Matrix (Fin 4) (Fin 4) ℝ := weylNPlus1 (Real.exp tau)

/-- Logarithmic-time outgoing wavefront shell $n_-^{(1)}(\tau) = e^{-\tau} n_-^{(1)}$. -/
def logTimeNMinus1 (tau : ℝ) : Matrix (Fin 4) (Fin 4) ℝ := weylNMinus1 (Real.exp (-tau))

/-- **Theorem 2.3 (Exact Conformal CAR Invariance Along Logarithmic Time $\tau \in \mathbb{R}$)**:
Under $\lambda(\tau) = e^\tau$ and $\lambda(\tau)^{-1} = e^{-\tau}$, the CAR anticommutator
is constant for all $\tau \in \mathbb{R}$:
$$\{n_+^{(1)}(\tau), n_-^{(1)}(\tau)\} = 2 \cdot \mathbf{1}_4.$$ -/
theorem logTimeMajorana_car_invariant (tau : ℝ) :
    logTimeNPlus1 tau * logTimeNMinus1 tau + logTimeNMinus1 tau * logTimeNPlus1 tau =
      (2 : ℝ) • (1 : Matrix (Fin 4) (Fin 4) ℝ) := by
  unfold logTimeNPlus1 logTimeNMinus1
  have h_exp : Real.exp tau * Real.exp (-tau) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  exact (weylScaledMajorana_car_invariant (Real.exp tau) (Real.exp (-tau)) h_exp).1

/-!
## Section 3: Separation of Trace and Determinant Under $\lambda \leftrightarrow \lambda^{-1}$ Scaling
-/

/-- **Theorem 3.1 (Tracelessness of All Non-Identity $\mathrm{Cl}(2,2)$ Basis Modes)**:
The Majorana null modes $n_+^{(1)}, n_-^{(1)}$, the paracomplex bivector $\omega_1$,
the complex twin $J_{\mathrm{geom}}$, the volume pseudoscalar $\Omega$, and the
spacelike generator $e_3$ all have identically zero matrix trace. -/
theorem cl22_nontrivial_modes_traceless :
    Matrix.trace n_plus_1 = 0 ∧
    Matrix.trace n_minus_1 = 0 ∧
    Matrix.trace omega1 = 0 ∧
    Matrix.trace J_geom = 0 ∧
    Matrix.trace volumeOmega = 0 ∧
    Matrix.trace e3 = 0 := by
  rcases bivector_explicit_matrices with ⟨hw1, _, hJg, _⟩
  rw [volumeOmega_explicit, hw1, hJg]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (simp [n_plus_1, n_minus_1, e0, e1, e3, Matrix.trace, Matrix.diag, Fin.sum_univ_four])

/-- General Weyl-scaled multivector in $\mathrm{Cl}(2,2)$ combining identity, scaled lightcone
modes, complex structure $J_{\mathrm{geom}}$, and pseudoscalar $\Omega$. -/
def weylScaledMultivector (alpha a b c d lam invLam : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  alpha • (1 : Matrix (Fin 4) (Fin 4) ℝ) +
    (lam * a) • n_plus_1 +
    (invLam * b) • n_minus_1 +
    c • J_geom +
    d • volumeOmega

/-- **Theorem 3.2 (Trace Separation: Trace Depends Exclusively on the Identity Coefficient $\alpha$)**:
For any scale parameters $\lambda, \lambda^{-1}$ and amplitudes $a, b, c, d$,
$$\operatorname{Tr}(X(\alpha, a, b, c, d, \lambda, \lambda^{-1})) = \alpha \cdot \operatorname{Tr}(\mathbf{1}_4) = 4 \alpha.$$ -/
theorem weylScaledMultivector_trace_eq (alpha a b c d lam invLam : ℝ) :
    Matrix.trace (weylScaledMultivector alpha a b c d lam invLam) = 4 * alpha := by
  rcases cl22_nontrivial_modes_traceless with ⟨hn1, hn2, _, hJ, hOm, _⟩
  unfold weylScaledMultivector
  rw [Matrix.trace_add, Matrix.trace_add, Matrix.trace_add, Matrix.trace_add,
      Matrix.trace_smul, Matrix.trace_smul, Matrix.trace_smul, Matrix.trace_smul, Matrix.trace_smul,
      hn1, hn2, hJ, hOm]
  have h_one : Matrix.trace (1 : Matrix (Fin 4) (Fin 4) ℝ) = 4 := by
    simp [Matrix.trace, Matrix.diag]
  rw [h_one]
  ring

/-- Soldered Weyl-scaled vector $X_{\mathrm{solder}}(a, b, c, \lambda, \lambda^{-1}) = (\lambda a) n_+^{(1)} + (\lambda^{-1} b) n_-^{(1)} + c e_3 \in M_4(\mathbb{R})$. -/
def weylScaledSolderedVector (a b c lam invLam : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  (lam * a) • n_plus_1 + (invLam * b) • n_minus_1 + c • e3

/-- Anticommutation of the Sheet-1 Majorana modes $n_\pm^{(1)}$ with the Sheet-2 spacelike generator $e_3$. -/
theorem n_plus_minus_1_anticomm_e3 :
    n_plus_1 * e3 + e3 * n_plus_1 = 0 ∧
    n_minus_1 * e3 + e3 * n_minus_1 = 0 := by
  rcases cl22_anticommutation with ⟨_, _, he03, _, he13, _⟩
  have h_plus : (e0 + e1) * e3 + e3 * (e0 + e1) = 0 := by
    calc (e0 + e1) * e3 + e3 * (e0 + e1)
        = (e0 * e3 + e3 * e0) + (e1 * e3 + e3 * e1) := by noncomm_ring
      _ = 0 + 0 := by rw [he03, he13]
      _ = 0 := add_zero 0
  have h_minus : (e0 - e1) * e3 + e3 * (e0 - e1) = 0 := by
    calc (e0 - e1) * e3 + e3 * (e0 - e1)
        = (e0 * e3 + e3 * e0) - (e1 * e3 + e3 * e1) := by noncomm_ring
      _ = 0 - 0 := by rw [he03, he13]
      _ = 0 := sub_zero 0
  constructor
  · unfold n_plus_1
    rw [Matrix.smul_mul, Matrix.mul_smul, ← smul_add, h_plus, smul_zero]
  · unfold n_minus_1
    rw [Matrix.smul_mul, Matrix.mul_smul, ← smul_add, h_minus, smul_zero]

/-- **Theorem 3.3 (Weyl Gauge Invariance of the Soldered Clifford Interval in $M_4(\mathbb{R})$)**:
For any reciprocal scale pair $\lambda \cdot \lambda^{-1} = 1$, the square of the soldered
Weyl-scaled vector in $\mathrm{Cl}(2,2)$ neutralizes $\lambda$ and equals the conformal-projective
interval $(2 a b - c^2) \mathbf{1}_4$:
$$\big((\lambda a) n_+^{(1)} + (\lambda^{-1} b) n_-^{(1)} + c e_3\big)^2 = (2 a b - c^2) \cdot \mathbf{1}_4.$$ -/
theorem weylScaledSolderedVector_sq_invariant (a b c lam invLam : ℝ) (h_recip : lam * invLam = 1) :
    weylScaledSolderedVector a b c lam invLam * weylScaledSolderedVector a b c lam invLam =
      (2 * a * b - c ^ 2) • (1 : Matrix (Fin 4) (Fin 4) ℝ) := by
  rcases majorana_nilpotency with ⟨hn1_sq, hn2_sq, _, _⟩
  rcases majorana_witt_anticommutation_relations with ⟨hw1, _, _, _⟩
  rcases n_plus_minus_1_anticomm_e3 with ⟨h_n1_e3, h_n2_e3⟩
  have he3_sq : e3 * e3 = -(1 : Matrix (Fin 4) (Fin 4) ℝ) := cl22_metric_signatures.2.2.2
  have h_prod : (lam * a) * (invLam * b) = a * b := by
    calc (lam * a) * (invLam * b) = (lam * invLam) * (a * b) := by ring
      _ = 1 * (a * b) := by rw [h_recip]
      _ = a * b := one_mul (a * b)
  unfold weylScaledSolderedVector
  have h_expand :
      ((lam * a) • n_plus_1 + (invLam * b) • n_minus_1 + c • e3) *
        ((lam * a) • n_plus_1 + (invLam * b) • n_minus_1 + c • e3) =
      ((lam * a) * (lam * a)) • (n_plus_1 * n_plus_1) +
      ((invLam * b) * (invLam * b)) • (n_minus_1 * n_minus_1) +
      ((lam * a) * (invLam * b)) • (n_plus_1 * n_minus_1 + n_minus_1 * n_plus_1) +
      ((lam * a) * c) • (n_plus_1 * e3 + e3 * n_plus_1) +
      ((invLam * b) * c) • (n_minus_1 * e3 + e3 * n_minus_1) +
      (c ^ 2) • (e3 * e3) := by
    ext i j
    simp [Matrix.mul_apply, Fin.sum_univ_four]
    ring
  rw [h_expand, h_prod, hn1_sq, hn2_sq, hw1, h_n1_e3, h_n2_e3, he3_sq]
  ext i j; fin_cases i <;> fin_cases j <;> simp <;> ring

/-- A nonzero soldered interval gives an explicit two-sided inverse in the concrete
M₄(ℝ) representation: the candidate is the soldered vector divided by its scalar square.
This is a result for this parameterized vector family, not for arbitrary Clifford elements. -/
theorem weylScaledSolderedVector_has_two_sided_inverse
    (a b c lam invLam : ℝ) (h_recip : lam * invLam = 1)
    (h_interval : 2 * a * b - c ^ 2 ≠ 0) :
    ∃ Y : Matrix (Fin 4) (Fin 4) ℝ,
      Y * weylScaledSolderedVector a b c lam invLam = 1 ∧
      weylScaledSolderedVector a b c lam invLam * Y = 1 := by
  let X := weylScaledSolderedVector a b c lam invLam
  let q := 2 * a * b - c ^ 2
  have hsq : X * X = q • (1 : Matrix (Fin 4) (Fin 4) ℝ) := by
    dsimp [X, q]
    exact weylScaledSolderedVector_sq_invariant a b c lam invLam h_recip
  refine ⟨q⁻¹ • X, ?_, ?_⟩
  · calc
      (q⁻¹ • X) * X = q⁻¹ • (X * X) := by rw [Matrix.smul_mul]
      _ = q⁻¹ • (q • (1 : Matrix (Fin 4) (Fin 4) ℝ)) := by rw [hsq]
      _ = 1 := by rw [smul_smul, inv_mul_cancel₀ h_interval, one_smul]
  · calc
      X * (q⁻¹ • X) = q⁻¹ • (X * X) := by rw [Matrix.mul_smul]
      _ = q⁻¹ • (q • (1 : Matrix (Fin 4) (Fin 4) ℝ)) := by rw [hsq]
      _ = 1 := by rw [smul_smul, inv_mul_cancel₀ h_interval, one_smul]

/-- $2 \times 2$ lightcone Gram / soldered matrix $\begin{pmatrix} \lambda a & c \\ c & \lambda^{-1} b \end{pmatrix}$. -/
def lightconeGramMatrix (a b c lam invLam : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![lam * a, c; c, invLam * b]

/-- **Theorem 3.4 (Weyl Gauge Invariance of the $2 \times 2$ Lightcone Determinant $\det(X) = a b - c^2$)**:
For any reciprocal scale pair $\lambda \cdot \lambda^{-1} = 1$,
$$\det \begin{pmatrix} \lambda a & c \\ c & \lambda^{-1} b \end{pmatrix} = a b - c^2.$$ -/
theorem lightconeGramMatrix_det_weyl_invariant (a b c lam invLam : ℝ) (h_recip : lam * invLam = 1) :
    Matrix.det (lightconeGramMatrix a b c lam invLam) = a * b - c ^ 2 := by
  unfold lightconeGramMatrix
  rw [Matrix.det_fin_two_of]
  calc (lam * a) * (invLam * b) - c * c
      = (lam * invLam) * (a * b) - c ^ 2 := by ring
    _ = 1 * (a * b) - c ^ 2 := by rw [h_recip]
    _ = a * b - c ^ 2 := by ring

/-!
## Section 4: Chiral Schur Expression and Vanishing Weyl Scale Derivative
-/

/-- **Theorem 4.1 (Weyl Invariance of the Defined Schur Expression Under Opposite Block Scaling)**:
For any block matrix $T(\lambda) = \begin{pmatrix} A & \lambda \cdot B \\ \lambda^{-1} \cdot C & D \end{pmatrix}$
over $M_4(\mathbb{R})$ where the incoming odd block $B$ scales by $\lambda$ and the
outgoing block $C$ scales by $\lambda^{-1}$ ($\lambda \cdot \lambda^{-1} = 1$), the
defined Schur expression is invariant. No inverse law for invD or invDetD is assumed,
so this is an algebraic scaling identity for the defined expression, precisely the equality
stated in the Lean theorem below. -/
theorem berezinianSchur_weyl_gauge_invariant
    (A B C D invD : Matrix (Fin 4) (Fin 4) ℝ) (invDetD lam invLam : ℝ)
    (h_recip : lam * invLam = 1) :
    berezinianSchur A (lam • B) (invLam • C) D invD invDetD =
      berezinianSchur A B C D invD invDetD := by
  unfold berezinianSchur
  have h_comm : invLam * lam = 1 := by rw [mul_comm, h_recip]
  have h_schur : (lam • B) * invD * (invLam • C) = B * invD * C := by
    calc
      (lam • B) * invD * (invLam • C)
          = (lam • (B * invD)) * (invLam • C) := by rw [Matrix.smul_mul]
      _ = invLam • ((lam • (B * invD)) * C) := by rw [Matrix.mul_smul]
      _ = invLam • (lam • (B * invD * C)) := by rw [Matrix.smul_mul]
      _ = (invLam * lam) • (B * invD * C) := by rw [smul_smul]
      _ = B * invD * C := by rw [h_comm, one_smul]
  rw [h_schur]

/-- Logarithmic-time Weyl-scaled Schur expression
$\tau \mapsto$ the `berezinianSchur` expression with oppositely scaled blocks. -/
def logTimeBerezinianSchur
    (A B C D invD : Matrix (Fin 4) (Fin 4) ℝ) (invDetD : ℝ) (tau : ℝ) : ℝ :=
  berezinianSchur A (Real.exp tau • B) (Real.exp (-tau) • C) D invD invDetD

/-- **Theorem 4.2 (Logarithmic-Time Invariance of the Defined Schur Expression)**:
For all $\tau \in \mathbb{R}$, the corresponding defined expressions are equal. -/
theorem logTimeBerezinianSchur_eq_const
    (A B C D invD : Matrix (Fin 4) (Fin 4) ℝ) (invDetD : ℝ) (tau : ℝ) :
    logTimeBerezinianSchur A B C D invD invDetD tau =
      berezinianSchur A B C D invD invDetD := by
  unfold logTimeBerezinianSchur
  have h_exp : Real.exp tau * Real.exp (-tau) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  exact berezinianSchur_weyl_gauge_invariant A B C D invD invDetD (Real.exp tau) (Real.exp (-tau)) h_exp

/-- **Theorem 4.3 (Vanishing Derivative of the Defined Schur Expression)**:
The derivative of the Weyl-scaled defined expression with respect to logarithmic time
$\tau \in \mathbb{R}$ vanishes identically. -/
theorem deriv_logTimeBerezinianSchur_eq_zero
    (A B C D invD : Matrix (Fin 4) (Fin 4) ℝ) (invDetD : ℝ) (tau : ℝ) :
    deriv (logTimeBerezinianSchur A B C D invD invDetD) tau = 0 := by
  have h_fun : logTimeBerezinianSchur A B C D invD invDetD =
      fun _ : ℝ => berezinianSchur A B C D invD invDetD := by
    ext t
    exact logTimeBerezinianSchur_eq_const A B C D invD invDetD t
  rw [h_fun, deriv_const]

/-- **Theorem 4.4 (Scalar $(1|1)$ Formula Weyl Invariance)**:
For the scalar formula `InfoGeometry.Supergeometry.Berezinian.berezinian` with arbitrary `invD`,
scaling the upper-right odd entry $M_{01}$ by $\lambda$ and the lower-left odd entry $M_{10}$
by $\lambda^{-1}$ ($\lambda \cdot \lambda^{-1} = 1$) leaves the value of that defined formula invariant. -/
theorem berezinian_super_lu_weyl_invariant
    (a b c d invD lam invLam : ℝ) (h_recip : lam * invLam = 1) :
    InfoGeometry.Supergeometry.Berezinian.berezinian
      !![a, lam * b; invLam * c, d] invD =
    InfoGeometry.Supergeometry.Berezinian.berezinian
      !![a, b; c, d] invD := by
  unfold InfoGeometry.Supergeometry.Berezinian.berezinian
  simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  calc (a - (lam * b) * invD * (invLam * c)) * invD
      = (a - (lam * invLam) * (b * invD * c)) * invD := by ring
    _ = (a - 1 * (b * invD * c)) * invD := by rw [h_recip]
    _ = (a - b * invD * c) * invD := by ring

end InfoGeometry.Synthesis.Cl22LightconeWeylBerezinGaugeBridge
