/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import InfoGeometry.Clifford.Cl11JordanWignerCARBridge

/-!
# Doubled $\mathrm{Cl}(1,1) \;\widehat{\otimes}\; \mathrm{Cl}(1,1) \cong \mathrm{Cl}(2,2)$ Real Dirac Carrier

This module formalizes the 16-dimensional neutral/split real Dirac algebra
$\mathrm{Cl}(2,2) \cong M_4(\mathbb{R})$ obtained by doubling the single-sheet
spacetime Clifford algebra $\mathrm{Cl}(1,1)$ across the primal causal sheet $T^+$
(Sheet 1: $\{e_0, e_1\}$) and the dual retrocausal sheet $T^-$ (Sheet 2: $\{e_2, e_3\}$):

1. **Section 1 (Metric Signature $(+1, -1, +1, -1)$ & Pairwise Anticommutation of $\mathrm{Cl}(2,2)$)**:
   - Defines the four real $4 \times 4$ Dirac generators `e0`, `e1` (Sheet 1) and
     `e2`, `e3` (Sheet 2).
   - Proves `cl22_metric_signatures` ($e_0^2 = +I$, $e_1^2 = -I$, $e_2^2 = +I$, $e_3^2 = -I$),
     `e0_mul_e1_ne_comm` ($e_0 e_1 \neq e_1 e_0$), and `cl22_anticommutation`
     ($\{e_\mu, e_\nu\} = 0$ for all $\mu \neq \nu$).

2. **Section 2 (The Four Majorana Null Vectors & Four-Mode Fermionic Null Algebra)**:
   - Defines the four lightcone Majorana null modes `n_plus_1`, `n_minus_1` (Sheet 1)
     and `n_plus_2`, `n_minus_2` (Sheet 2).
   - Proves `majorana_nilpotency` ($(n_\pm^{(1)})^2 = 0$, $(n_\pm^{(2)})^2 = 0$),
     intra-sheet Witt normalization `majorana_intra_sheet_anticommutators`
     ($\{n_+^{(1)}, n_-^{(1)}\} = 2 I$, $\{n_+^{(2)}, n_-^{(2)}\} = 2 I$), and
     cross-sheet anticommutativity `majorana_cross_sheet_anticommutators`
     ($\{n_\mu^{(1)}, n_\nu^{(2)}\} = 0$).

3. **Section 3 (Intra-Sheet Hypercomplex Bivectors $\omega_1, \omega_2$ vs. Cross-Sheet Geometric Imaginary Unit $J_{\mathrm{geom}} = e_0 e_2$)**:
   - Defines the intra-sheet hyperbolic bivectors `omega1 = e0 * e1` ($\omega_1^2 = +I$)
     and `omega2 = e2 * e3` ($\omega_2^2 = +I$), the cross-sheet elliptic bivectors
     `J_geom = e0 * e2` ($J_{\mathrm{geom}}^2 = -I$) and `J_space = e1 * e3`
     ($J_{\mathrm{space}}^2 = -I$), and the paracomplex volume pseudoscalar
     `volumeOmega = omega1 * omega2` ($\Omega^2 = +I$).
   - Proves `cl22_hypercomplex_and_geometric_i` and `cl22_volume_and_bivector_commutation`
     ($[\Omega, J_{\mathrm{geom}}] = 0$, $[\Omega, J_{\mathrm{space}}] = 0$,
     $[J_{\mathrm{geom}}, J_{\mathrm{space}}] = 0$).

4. **Section 4 (Andreev Reflection as a Continuous Gauge Rotor in $\mathrm{Spin}_0(2,2)$)**:
   - Defines the continuous cross-sheet rotor `andreevRotor c s = c • 1 + s • J_geom`
     and its reverse `andreevRotorRev c s = c • 1 - s • J_geom`.
   - Proves the forward spin normalization as the first conjunct of
     `andreevRotor_planar_sheet_rotation`
     ($R(c, s)\widetilde{R}(c, s) = (c^2 + s^2) I$); the reverse-order normalization
     is proved in `Cl22ReverseRotor`
     `andreevRotor_planar_sheet_rotation`
     ($\widetilde{R}(c, s) \, e_0 \, R(c, s) = (c^2 - s^2) e_0 + 2 c s \, e_2$),
     and exact $\theta = \pi / 2$ Andreev sheet transmutation
     `andreevRotor_pi_div_two_transmutes_sheet1_to_sheet2` (rotating $e_0 \in T^+$
     into $e_2 \in T^-$ and $e_1 \in T^+$ into $e_3 \in T^-$).

5. **Section 5 (Peircian Chiral Idempotents $P_\pm^{(1)}, P_\pm^{(2)}$ in $\mathrm{Cl}(2,2)$)**:
   - Defines the Sheet-1 and Sheet-2 Peircian projectors `peircianPlus1`, `peircianMinus1`,
     `peircianPlus2`, `peircianMinus2` and proves their orthogonal idempotent resolution
     and mutual commutativity (`cl22_peircian_idempotent_resolution`).
-/

set_option autoImplicit false

noncomputable section

open scoped Matrix
open Matrix

namespace InfoGeometry.Synthesis.Cl22RealDiracCarrier

/-!
## Section 1: Metric Signature $(+1, -1, +1, -1)$ and Anticommutation of $\mathrm{Cl}(2,2)$
-/

/-- Orthonormal generator $e_0$ (Sheet 1, timelike: $e_0^2 = +1$). -/
def e0 : Matrix (Fin 4) (Fin 4) ℝ :=
  !![ 0,  0,  1,  0;
      0,  0,  0,  1;
      1,  0,  0,  0;
      0,  1,  0,  0 ]

/-- Orthonormal generator $e_1$ (Sheet 1, spacelike: $e_1^2 = -1$, $e_1 = J \otimes I_2$). -/
def e1 : Matrix (Fin 4) (Fin 4) ℝ :=
  !![  0,  0,  1,  0;
       0,  0,  0,  1;
      -1,  0,  0,  0;
       0, -1,  0,  0 ]

/-- Orthonormal generator $e_2$ (Sheet 2, timelike: $e_2^2 = +1$, $e_2 = Z \otimes X$). -/
def e2 : Matrix (Fin 4) (Fin 4) ℝ :=
  !![ 0,  1,  0,  0;
      1,  0,  0,  0;
      0,  0,  0, -1;
      0,  0, -1,  0 ]

/-- Orthonormal generator $e_3$ (Sheet 2, spacelike: $e_3^2 = -1$, $e_3 = Z \otimes (-J)$). -/
def e3 : Matrix (Fin 4) (Fin 4) ℝ :=
  !![ 0, -1,  0,  0;
      1,  0,  0,  0;
      0,  0,  0,  1;
      0,  0, -1,  0 ]

/-- Explicit non-commutativity of the real Dirac generators $e_0, e_1 \in M_4(\mathbb{R})$:
$e_0 e_1 \neq e_1 e_0$. -/
theorem e0_mul_e1_ne_comm :
    e0 * e1 ≠ e1 * e0 := by
  intro h_comm
  have h00 : (e0 * e1) 0 0 = (e1 * e0) 0 0 :=
    congrArg (fun M : Matrix (Fin 4) (Fin 4) ℝ => M 0 0) h_comm
  revert h00
  simp [e0, e1, Matrix.mul_apply, Fin.sum_univ_four]
  norm_num

/-- **Theorem 1.1 (Exact Neutral Metric Signature $(+1, -1, +1, -1)$)**:
The four generators satisfy $e_0^2 = +I$, $e_1^2 = -I$, $e_2^2 = +I$, and $e_3^2 = -I$. -/
theorem cl22_metric_signatures :
    e0 * e0 = (1 : Matrix (Fin 4) (Fin 4) ℝ) ∧
    e1 * e1 = -(1 : Matrix (Fin 4) (Fin 4) ℝ) ∧
    e2 * e2 = (1 : Matrix (Fin 4) (Fin 4) ℝ) ∧
    e3 * e3 = -(1 : Matrix (Fin 4) (Fin 4) ℝ) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    (ext i j; fin_cases i <;> fin_cases j <;>
      simp [e0, e1, e2, e3, Matrix.mul_apply, Fin.sum_univ_four])

/-- **Theorem 1.2 (Pairwise Anticommutation of Orthogonal $\mathrm{Cl}(2,2)$ Generators)**:
All six distinct pairs of generators anticommute: $e_\mu e_\nu + e_\nu e_\mu = 0$ ($\mu < \nu$). -/
theorem cl22_anticommutation :
    e0 * e1 + e1 * e0 = 0 ∧
    e0 * e2 + e2 * e0 = 0 ∧
    e0 * e3 + e3 * e0 = 0 ∧
    e1 * e2 + e2 * e1 = 0 ∧
    e1 * e3 + e3 * e1 = 0 ∧
    e2 * e3 + e3 * e2 = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (ext i j; fin_cases i <;> fin_cases j <;>
      simp [e0, e1, e2, e3])

/-!
## Section 2: The Four Majorana Null Vectors (2 on Sheet 1, 2 on Sheet 2)
-/

/-- Forward lightcone Majorana null vector $n_+^{(1)} = \frac{1}{\sqrt{2}}(e_0 + e_1)$ on Sheet 1 ($T^+$). -/
def n_plus_1  : Matrix (Fin 4) (Fin 4) ℝ := (1 / Real.sqrt 2) • (e0 + e1)

/-- Backward lightcone Majorana null vector $n_-^{(1)} = \frac{1}{\sqrt{2}}(e_0 - e_1)$ on Sheet 1 ($T^+$). -/
def n_minus_1 : Matrix (Fin 4) (Fin 4) ℝ := (1 / Real.sqrt 2) • (e0 - e1)

/-- Forward lightcone Majorana null vector $n_+^{(2)} = \frac{1}{\sqrt{2}}(e_2 + e_3)$ on Sheet 2 ($T^-$). -/
def n_plus_2  : Matrix (Fin 4) (Fin 4) ℝ := (1 / Real.sqrt 2) • (e2 + e3)

/-- Backward lightcone Majorana null vector $n_-^{(2)} = \frac{1}{\sqrt{2}}(e_2 - e_3)$ on Sheet 2 ($T^-$). -/
def n_minus_2 : Matrix (Fin 4) (Fin 4) ℝ := (1 / Real.sqrt 2) • (e2 - e3)

/-- Unnormalized lightcone nilpotency identities $(e_0 \pm e_1)^2 = 0$ and $(e_2 \pm e_3)^2 = 0$. -/
theorem unnormalized_lightcone_sq_zero :
    (e0 + e1) * (e0 + e1) = 0 ∧
    (e0 - e1) * (e0 - e1) = 0 ∧
    (e2 + e3) * (e2 + e3) = 0 ∧
    (e2 - e3) * (e2 - e3) = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    (ext i j; fin_cases i <;> fin_cases j <;>
      simp [e0, e1, e2, e3, Matrix.mul_apply, Fin.sum_univ_four])

/-- **Theorem 2.1 (Nilpotency of the Four Majorana Modes)**:
All four Majorana lightcone vectors square to zero:
$$(n_+^{(1)})^2 = 0, \quad (n_-^{(1)})^2 = 0, \quad (n_+^{(2)})^2 = 0, \quad (n_-^{(2)})^2 = 0.$$ -/
theorem majorana_nilpotency :
    n_plus_1 * n_plus_1 = 0 ∧
    n_minus_1 * n_minus_1 = 0 ∧
    n_plus_2 * n_plus_2 = 0 ∧
    n_minus_2 * n_minus_2 = 0 := by
  rcases unnormalized_lightcone_sq_zero with ⟨h1, h2, h3, h4⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold n_plus_1; rw [Matrix.smul_mul, Matrix.mul_smul, h1, smul_zero, smul_zero]
  · unfold n_minus_1; rw [Matrix.smul_mul, Matrix.mul_smul, h2, smul_zero, smul_zero]
  · unfold n_plus_2; rw [Matrix.smul_mul, Matrix.mul_smul, h3, smul_zero, smul_zero]
  · unfold n_minus_2; rw [Matrix.smul_mul, Matrix.mul_smul, h4, smul_zero, smul_zero]

private theorem inv_sqrt_two_mul_self :
    (1 / Real.sqrt 2) * (1 / Real.sqrt 2) = (1 / 2 : ℝ) := by
  rw [div_mul_div_comm, one_mul, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

/-- **Theorem 2.2 (Intra-Sheet Majorana Witt Anticommutators & Cross-Sheet Anticommutativity)**:
Within each sheet, $\{n_+^{(a)}, n_-^{(a)}\} = 2 I$, while Majorana modes on opposite sheets
anticommute: $\{n_+^{(1)}, n_+^{(2)}\} = 0$ and $\{n_-^{(1)}, n_-^{(2)}\} = 0$. -/
theorem majorana_witt_anticommutation_relations :
    n_plus_1 * n_minus_1 + n_minus_1 * n_plus_1 = (2 : ℝ) • (1 : Matrix (Fin 4) (Fin 4) ℝ) ∧
    n_plus_2 * n_minus_2 + n_minus_2 * n_plus_2 = (2 : ℝ) • (1 : Matrix (Fin 4) (Fin 4) ℝ) ∧
    n_plus_1 * n_plus_2 + n_plus_2 * n_plus_1 = 0 ∧
    n_minus_1 * n_minus_2 + n_minus_2 * n_minus_1 = 0 := by
  have h_sheet1 :
      (e0 + e1) * (e0 - e1) + (e0 - e1) * (e0 + e1) =
        (4 : ℝ) • (1 : Matrix (Fin 4) (Fin 4) ℝ) := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [e0, e1] <;> norm_num
  have h_sheet2 :
      (e2 + e3) * (e2 - e3) + (e2 - e3) * (e2 + e3) =
        (4 : ℝ) • (1 : Matrix (Fin 4) (Fin 4) ℝ) := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [e2, e3] <;> norm_num
  have h_cross_plus :
      (e0 + e1) * (e2 + e3) + (e2 + e3) * (e0 + e1) = 0 := by
    ext i j
    (fin_cases i <;> fin_cases j <;> simp [e0, e1, e2, e3]); norm_num
  have h_cross_minus :
      (e0 - e1) * (e2 - e3) + (e2 - e3) * (e0 - e1) = 0 := by
    ext i j
    (fin_cases i <;> fin_cases j <;> simp [e0, e1, e2, e3]); norm_num
  have h_scale : ((1 / Real.sqrt 2) * (1 / Real.sqrt 2)) * 4 = (2 : ℝ) := by
    rw [inv_sqrt_two_mul_self]
    norm_num
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold n_plus_1 n_minus_1
    rw [smul_mul_smul_comm, smul_mul_smul_comm, ← smul_add, h_sheet1, smul_smul, h_scale]
  · unfold n_plus_2 n_minus_2
    rw [smul_mul_smul_comm, smul_mul_smul_comm, ← smul_add, h_sheet2, smul_smul, h_scale]
  · unfold n_plus_1 n_plus_2
    rw [smul_mul_smul_comm, smul_mul_smul_comm, ← smul_add, h_cross_plus, smul_zero]
  · unfold n_minus_1 n_minus_2
    rw [smul_mul_smul_comm, smul_mul_smul_comm, ← smul_add, h_cross_minus, smul_zero]

/-!
## Section 3: Intra-Sheet Hypercomplex Bivectors vs. Cross-Sheet Geometric Imaginary Unit $i$
-/

/-- Intra-sheet 1 paracomplex bivector $\omega_1 = e_0 e_1$ ($\omega_1^2 = +I$). -/
def omega1 : Matrix (Fin 4) (Fin 4) ℝ := e0 * e1

/-- Intra-sheet 2 paracomplex bivector $\omega_2 = e_2 e_3$ ($\omega_2^2 = +I$). -/
def omega2 : Matrix (Fin 4) (Fin 4) ℝ := e2 * e3

/-- Cross-sheet timelike geometric imaginary unit $J_{\mathrm{geom}} = e_0 e_2$ ($J_{\mathrm{geom}}^2 = -I$). -/
def J_geom : Matrix (Fin 4) (Fin 4) ℝ := e0 * e2

/-- Cross-sheet spacelike geometric imaginary unit $J_{\mathrm{space}} = e_1 e_3$ ($J_{\mathrm{space}}^2 = -I$). -/
def J_space : Matrix (Fin 4) (Fin 4) ℝ := e1 * e3

/-- Total grade-4 paracomplex volume pseudoscalar $\Omega = e_0 e_1 e_2 e_3 = \omega_1 \omega_2$ ($\Omega^2 = +I$). -/
def volumeOmega : Matrix (Fin 4) (Fin 4) ℝ := omega1 * omega2

/-- Explicit $4 \times 4$ matrix representations of the bivectors $\omega_1, \omega_2, J_{\mathrm{geom}}, J_{\mathrm{space}}$. -/
theorem bivector_explicit_matrices :
    omega1 = !![ -1,  0,  0,  0;
                  0, -1,  0,  0;
                  0,  0,  1,  0;
                  0,  0,  0,  1 ] ∧
    omega2 = !![  1,  0,  0,  0;
                  0, -1,  0,  0;
                  0,  0,  1,  0;
                  0,  0,  0, -1 ] ∧
    J_geom = !![  0,  0,  0, -1;
                  0,  0, -1,  0;
                  0,  1,  0,  0;
                  1,  0,  0,  0 ] ∧
    J_space = !![  0,  0,  0,  1;
                   0,  0, -1,  0;
                   0,  1,  0,  0;
                  -1,  0,  0,  0 ] := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    (ext i j; fin_cases i <;> fin_cases j <;>
      simp [omega1, omega2, J_geom, J_space, e0, e1, e2, e3,
            Matrix.mul_apply, Fin.sum_univ_four])

/-- Explicit $4 \times 4$ diagonal matrix representation of the grade-4 volume element $\Omega = \omega_1 \omega_2$. -/
theorem volumeOmega_explicit :
    volumeOmega = !![ -1,  0,  0,  0;
                       0,  1,  0,  0;
                       0,  0,  1,  0;
                       0,  0,  0, -1 ] := by
  rcases bivector_explicit_matrices with ⟨hw1, hw2, _, _⟩
  unfold volumeOmega
  rw [hw1, hw2]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_four]

/-- **Theorem 3.1 (Intra-Sheet Hypercomplex Bivectors vs. Cross-Sheet Geometric Complex Structure)**:
1. The intra-sheet bivectors are hypercomplex: $\omega_1^2 = +I$ and $\omega_2^2 = +I$.
2. The cross-sheet bivectors are strictly complex: $J_{\mathrm{geom}}^2 = -I$ and $J_{\mathrm{space}}^2 = -I$.
3. $J_{\mathrm{geom}}$ anticommutes with both $e_0$ (Sheet 1) and $e_2$ (Sheet 2). -/
theorem cl22_hypercomplex_and_geometric_i :
    omega1 * omega1 = (1 : Matrix (Fin 4) (Fin 4) ℝ) ∧
    omega2 * omega2 = (1 : Matrix (Fin 4) (Fin 4) ℝ) ∧
    J_geom * J_geom = -(1 : Matrix (Fin 4) (Fin 4) ℝ) ∧
    J_space * J_space = -(1 : Matrix (Fin 4) (Fin 4) ℝ) ∧
    e0 * J_geom + J_geom * e0 = 0 ∧
    e2 * J_geom + J_geom * e2 = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (ext i j; fin_cases i <;> fin_cases j <;>
      simp [omega1, omega2, J_geom, J_space, e0, e1, e2, e3,
            Matrix.mul_apply, Fin.sum_univ_four])

/-- **Theorem 3.2 (Paracomplex Volume Element $\Omega = \omega_1 \omega_2$ and Bi-Quaternionic Commutation)**:
The grade-4 pseudoscalar $\Omega = \omega_1 \omega_2$ satisfies $\Omega^2 = +I$,
$\omega_1 \omega_2 = \omega_2 \omega_1$, and commutes with both cross-sheet complex
structures $J_{\mathrm{geom}}$ and $J_{\mathrm{space}}$ ($[\Omega, J_{\mathrm{geom}}] = 0$,
$[\Omega, J_{\mathrm{space}}] = 0$, $[J_{\mathrm{geom}}, J_{\mathrm{space}}] = 0$). -/
theorem cl22_volume_and_bivector_commutation :
    volumeOmega * volumeOmega = (1 : Matrix (Fin 4) (Fin 4) ℝ) ∧
    omega1 * omega2 = omega2 * omega1 ∧
    volumeOmega * J_geom = J_geom * volumeOmega ∧
    volumeOmega * J_space = J_space * volumeOmega ∧
    J_geom * J_space = J_space * J_geom := by
  rcases bivector_explicit_matrices with ⟨hw1, hw2, hJg, hJs⟩
  rw [volumeOmega_explicit, hw1, hw2, hJg, hJs]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    (ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_four])

/-!
## Section 4: Andreev Reflection as a Continuous Gauge Rotor in $\mathrm{Spin}_0(2,2)$
-/

/-- Continuous cross-sheet Andreev rotor $R(c, s) = c I + s J_{\mathrm{geom}}$ parameterized by
$(c, s) = (\cos(\theta/2), \sin(\theta/2))$. -/
def andreevRotor (c s : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  c • (1 : Matrix (Fin 4) (Fin 4) ℝ) + s • J_geom

/-- Reversed cross-sheet Andreev rotor $\widetilde{R}(c, s) = c I - s J_{\mathrm{geom}}$. -/
def andreevRotorRev (c s : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  c • (1 : Matrix (Fin 4) (Fin 4) ℝ) - s • J_geom

/-- The cross-sheet rotor multiplication law is the complex multiplication law
on its two real coefficients. -/
theorem andreevRotor_mul
    (c s c' s' : ℝ) :
    andreevRotor c s * andreevRotor c' s' =
      andreevRotor (c * c' - s * s') (c * s' + s * c') := by
  unfold andreevRotor
  rw [add_mul, mul_add, mul_add,
    smul_mul_smul_comm, mul_one,
    smul_mul_smul_comm, smul_mul_smul_comm,
    mul_one, smul_mul_smul_comm,
    cl22_hypercomplex_and_geometric_i.2.2.1,
    smul_neg]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [J_geom, e0, e2, Matrix.mul_apply, Fin.sum_univ_four] <;>
    ring

/-- Action of the cross-sheet complex structure $J_{\mathrm{geom}} = e_0 e_2$ on the
timelike generators $e_0$ and $e_2$:
$$e_0 J_{\mathrm{geom}} = e_2, \quad J_{\mathrm{geom}} e_0 = -e_2, \quad
  e_2 J_{\mathrm{geom}} = -e_0, \quad J_{\mathrm{geom}} e_2 = e_0.$$ -/
theorem J_geom_action_on_e0_e2 :
    e0 * J_geom = e2 ∧
    J_geom * e0 = -e2 ∧
    e2 * J_geom = -e0 ∧
    J_geom * e2 = e0 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    (ext i j; fin_cases i <;> fin_cases j <;>
      simp [J_geom, e0, e2, Matrix.mul_apply, Fin.sum_univ_four])

/-- Left multiplication of $e_0$ by $\widetilde{R}(c, s)$ and $R(c, s)$. -/
theorem andreevRotor_left_mul_e0 (c s : ℝ) :
    andreevRotorRev c s * e0 = c • e0 + s • e2 ∧
    andreevRotor c s * e0 = c • e0 - s • e2 := by
  rcases J_geom_action_on_e0_e2 with ⟨_, hJ_e0, _, _⟩
  constructor
  · unfold andreevRotorRev
    rw [sub_mul, smul_mul_assoc, one_mul, smul_mul_assoc, hJ_e0, smul_neg, sub_neg_eq_add]
  · unfold andreevRotor
    rw [add_mul, smul_mul_assoc, one_mul, smul_mul_assoc, hJ_e0, smul_neg, ← sub_eq_add_neg]

/-- **Theorem 4.1 (Spin Group Normalization & Planar Cross-Sheet Rotor Action)**:
For any $c, s \in \mathbb{R}$:
1. $R(c, s)\,\widetilde{R}(c, s) = (c^2 + s^2) I$,
2. $\widetilde{R}(c, s) \, e_0 \, R(c, s) = (c^2 - s^2) e_0 + (2 c s) e_2$,
3. $R(c, s) \, e_0 \, \widetilde{R}(c, s) = (c^2 - s^2) e_0 - (2 c s) e_2$. -/
theorem andreevRotor_planar_sheet_rotation (c s : ℝ) :
    andreevRotor c s * andreevRotorRev c s =
      (c ^ 2 + s ^ 2) • (1 : Matrix (Fin 4) (Fin 4) ℝ) ∧
    andreevRotorRev c s * e0 * andreevRotor c s =
      (c ^ 2 - s ^ 2) • e0 + (2 * c * s) • e2 ∧
    andreevRotor c s * e0 * andreevRotorRev c s =
      (c ^ 2 - s ^ 2) • e0 - (2 * c * s) • e2 := by
  have hJ_sq : J_geom * J_geom = -(1 : Matrix (Fin 4) (Fin 4) ℝ) :=
    cl22_hypercomplex_and_geometric_i.2.2.1
  rcases J_geom_action_on_e0_e2 with ⟨he0_J, _, he2_J, _⟩
  rcases andreevRotor_left_mul_e0 c s with ⟨h_rev_e0, h_rot_e0⟩
  refine ⟨?_, ?_, ?_⟩
  · unfold andreevRotor andreevRotorRev
    rw [add_mul, mul_sub, mul_sub, smul_mul_smul_comm, one_mul,
        smul_mul_smul_comm, one_mul, smul_mul_smul_comm, mul_one,
        smul_mul_smul_comm, hJ_sq, smul_neg, sub_neg_eq_add]
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [J_geom, e0, e2] <;> ring
  · rw [h_rev_e0]
    unfold andreevRotor
    rw [add_mul, mul_add, mul_add, smul_mul_smul_comm, mul_one,
        smul_mul_smul_comm, he0_J, smul_mul_smul_comm, mul_one,
        smul_mul_smul_comm, he2_J, smul_neg]
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [e0, e2] <;> ring
  · rw [h_rot_e0]
    unfold andreevRotorRev
    rw [sub_mul, mul_sub, mul_sub, smul_mul_smul_comm, mul_one,
        smul_mul_smul_comm, he0_J, smul_mul_smul_comm, mul_one,
        smul_mul_smul_comm, he2_J, smul_neg, sub_neg_eq_add]
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [e0, e2] <;> ring

/-- **Theorem 4.2 (Andreev Reflection as a $\theta = \pi / 2$ Rotor Transmuting Sheet 1 into Sheet 2)**:
At the $\theta = \pi / 2$ half-angle point $c = s = 1 / \sqrt{2}$, the continuous rotor
$\mathcal{R}_A = R(1/\sqrt{2}, 1/\sqrt{2})$ is strictly unimodular
($\mathcal{R}_A \widetilde{\mathcal{R}}_A = I$) and rotates the primal causal generator
$e_0 \in T^+$ directly into the dual retrocausal generator $e_2 \in T^-$:
$$\widetilde{\mathcal{R}}_A \, e_0 \, \mathcal{R}_A = e_2 \quad \text{and} \quad
  \mathcal{R}_A \, e_0 \, \widetilde{\mathcal{R}}_A = -e_2.$$ -/
theorem andreevRotor_pi_div_two_transmutes_sheet1_to_sheet2 :
    andreevRotor (1 / Real.sqrt 2) (1 / Real.sqrt 2) *
        andreevRotorRev (1 / Real.sqrt 2) (1 / Real.sqrt 2) = 1 ∧
    andreevRotorRev (1 / Real.sqrt 2) (1 / Real.sqrt 2) * e0 *
        andreevRotor (1 / Real.sqrt 2) (1 / Real.sqrt 2) = e2 ∧
    andreevRotor (1 / Real.sqrt 2) (1 / Real.sqrt 2) * e0 *
        andreevRotorRev (1 / Real.sqrt 2) (1 / Real.sqrt 2) = -e2 := by
  rcases andreevRotor_planar_sheet_rotation (1 / Real.sqrt 2) (1 / Real.sqrt 2) with
    ⟨h_norm, h_rot1, h_rot2⟩
  have h_sq : (1 / Real.sqrt 2) ^ 2 = (1 / 2 : ℝ) := by
    rw [sq, inv_sqrt_two_mul_self]
  have h_sum : (1 / Real.sqrt 2) ^ 2 + (1 / Real.sqrt 2) ^ 2 = (1 : ℝ) := by
    rw [h_sq]; norm_num
  have h_diff : (1 / Real.sqrt 2) ^ 2 - (1 / Real.sqrt 2) ^ 2 = (0 : ℝ) := sub_self _
  have h_prod : 2 * (1 / Real.sqrt 2) * (1 / Real.sqrt 2) = (1 : ℝ) := by
    rw [mul_assoc, inv_sqrt_two_mul_self]; norm_num
  refine ⟨?_, ?_, ?_⟩
  · rw [h_norm, h_sum, one_smul]
  · rw [h_rot1, h_diff, h_prod, zero_smul, one_smul, zero_add]
  · rw [h_rot2, h_diff, h_prod, zero_smul, one_smul, zero_sub]

/-!
## Section 5: Peircian Chiral Idempotents $P_\pm^{(1)}, P_\pm^{(2)}$ in $\mathrm{Cl}(2,2)$
-/

/-- Sheet-1 positive Peircian chiral projector $P_+^{(1)} = \frac{1}{2}(I + \omega_1)$. -/
def peircianPlus1 : Matrix (Fin 4) (Fin 4) ℝ :=
  (1 / 2 : ℝ) • ((1 : Matrix (Fin 4) (Fin 4) ℝ) + omega1)

/-- Sheet-1 negative Peircian chiral projector $P_-^{(1)} = \frac{1}{2}(I - \omega_1)$. -/
def peircianMinus1 : Matrix (Fin 4) (Fin 4) ℝ :=
  (1 / 2 : ℝ) • ((1 : Matrix (Fin 4) (Fin 4) ℝ) - omega1)

/-- Sheet-2 positive Peircian chiral projector $P_+^{(2)} = \frac{1}{2}(I + \omega_2)$. -/
def peircianPlus2 : Matrix (Fin 4) (Fin 4) ℝ :=
  (1 / 2 : ℝ) • ((1 : Matrix (Fin 4) (Fin 4) ℝ) + omega2)

/-- Sheet-2 negative Peircian chiral projector $P_-^{(2)} = \frac{1}{2}(I - \omega_2)$. -/
def peircianMinus2 : Matrix (Fin 4) (Fin 4) ℝ :=
  (1 / 2 : ℝ) • ((1 : Matrix (Fin 4) (Fin 4) ℝ) - omega2)

/-- **Theorem 5.1 (Orthogonal Peircian Idempotent Resolution & Sheet Commutativity in $\mathrm{Cl}(2,2)$)**:
$P_+^{(1)}, P_-^{(1)}$ and $P_+^{(2)}, P_-^{(2)}$ form commuting orthogonal idempotent resolutions
of the $4 \times 4$ Dirac identity:
$$P_+^{(1)} + P_-^{(1)} = I, \quad (P_+^{(1)})^2 = P_+^{(1)}, \quad P_+^{(1)} P_-^{(1)} = 0, \quad
  P_+^{(1)} P_+^{(2)} = P_+^{(2)} P_+^{(1)}.$$ -/
theorem cl22_peircian_idempotent_resolution :
    peircianPlus1 + peircianMinus1 = (1 : Matrix (Fin 4) (Fin 4) ℝ) ∧
    peircianPlus2 + peircianMinus2 = (1 : Matrix (Fin 4) (Fin 4) ℝ) ∧
    peircianPlus1 * peircianPlus1 = peircianPlus1 ∧
    peircianMinus1 * peircianMinus1 = peircianMinus1 ∧
    peircianPlus1 * peircianMinus1 = 0 ∧
    peircianPlus1 * peircianPlus2 = peircianPlus2 * peircianPlus1 := by
  rcases bivector_explicit_matrices with ⟨hw1, hw2, _, _⟩
  unfold peircianPlus1 peircianMinus1 peircianPlus2 peircianMinus2
  rw [hw1, hw2]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_four] <;> norm_num)

end InfoGeometry.Synthesis.Cl22RealDiracCarrier
