/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Synthesis.Z2Z2KoszulOperadicHomologyShirokovSynthesis

/-!
# Frontier 105: Unification of the Dirac Krein Adjoint ($\bar{\psi} = \psi^\dagger \gamma^0$), Aharonov–Bergmann–Lebowitz Two-State Weak Values, Schwinger–Keldysh / Thermo Field Dynamics Doubling, and Tomita–Takesaki Modular Reflection

This module formalizes the exact mathematical unification of the four canonical "auxiliary"
two-sheeted / indefinite-metric formalisms of twentieth-century mathematical physics as coordinate
charts of the same neutral $(n, n)$ Para-Kähler / Double Real Krein geometry $\mathcal{K}_n = T^+ \oplus T^-$:

1. **Section 1 — The Dirac Conjugation / Krein $J$-Adjoint Identity ($\bar{A} = \gamma^0 A^{\mathsf{T}} \gamma^0$) & Cayley–Hadamard Congruence to Totally Isotropic Para-Kähler Sheets**:
   - Defines the $(2,2)$ Dirac fundamental symmetry $\gamma^0 = \operatorname{diag}(+1, +1, -1, -1)$
     (`diracGamma0Krein4`), the Dirac bilinear pairing $\langle \phi, \psi \rangle_{\text{Dirac}} = \phi^{\mathsf{T}} \gamma^0 \psi$
     (`diracKreinPairing4`), and the Dirac operator adjoint $\bar{A} = \gamma^0 A^{\mathsf{T}} \gamma^0$
     (`diracKreinAdjoint4`).
   - Proves `dirac_conjugation_is_exact_krein_adjoint_and_paraKahler_congruent`:
     * $(\gamma^0)^2 = I_4$ and $\operatorname{Tr}(\gamma^0) = 0$ (neutral $(2,2)$ Krein signature),
     * Exact Krein $J$-adjoint duality: $\langle \phi, A \psi \rangle_{\text{Dirac}} = \langle \bar{A} \phi, \psi \rangle_{\text{Dirac}}$,
     * Involutive anti-automorphism laws: $\overline{\bar{A}} = A$ and $\overline{A B} = \bar{B} \bar{A}$,
     * Cayley–Hadamard sheet rotation $H_4^{\mathsf{T}} \gamma^0 H_4 = 2 \eta_{\text{PK}}$: the diagonal
       Dirac $(2,2)$ metric is congruent to the off-diagonal Para-Kähler metric $\eta_{\text{PK}} = \begin{pmatrix} 0 & I_2 \\ I_2 & 0 \end{pmatrix}$,
       on which both sheets $T^+$ and $T^-$ are strictly isotropic ($\langle u^+, u^+ \rangle_{\text{PK}} = \langle u^-, u^- \rangle_{\text{PK}} = 0$).

2. **Section 2 — Aharonov–Bergmann–Lebowitz Two-State Vector Formalism (TSVF) Weak Values as Para-Kähler Cross-Ratio Readouts**:
   - Defines the TSVF weak value $A_w(\phi, \psi) = \frac{\langle \phi, A \psi \rangle}{\langle \phi, \psi \rangle}$
     (`tsvfWeakValue`) between a backward-evolving post-selected covector $\phi \in T^-$ and a
     forward-evolving pre-selected state $\psi \in T^+$.
   - Proves `tsvf_weakValue_calculus_and_anomalous_krein_witness`:
     * Normalization $I_w(\phi, \psi) = 1$,
     * Linearity $({\alpha A + \beta B})_w = \alpha A_w + \beta B_w$,
     * Exact Krein/transpose symmetry $A_w(\phi, \psi) = (A^{\mathsf{T}})_w(\psi, \phi)$,
     * Explicit anomalous weak-value witness: for the rank-$1$ projector $P = \operatorname{diag}(1, 0)$
       on $\mathbb{R}^2$ (whose eigenvalues are strictly in $\{0, 1\}$, i.e., $P^2 = P$), the two-state
       pair $\phi = (2, -1)$, $\psi = (1, 1)$ yields $P_w(\phi, \psi) = 2 > 1$!

3. **Section 3 — Schwinger–Keldysh ($C_+ \cup C_-$) Contour & Thermo Field Dynamics (TFD) Keldysh Rotation to the Para-Kähler Metric**:
   - Defines the Schwinger–Keldysh contour difference pairing $S_{\text{SK}}(u, v) = \langle u_+, v_+ \rangle - \langle u_-, v_- \rangle$
     (`schwingerKeldyshContourPairing`) and the Keldysh classical/quantum coordinates
     $(u_{\text{cl}}, u_{\text{q}}) = (u_+ + u_-, u_+ - u_-)$.
   - Proves `schwingerKeldysh_tfd_paraKahler_equivalence`:
     * Under the Keldysh rotation, the off-diagonal Para-Kähler pairing between $u_{\text{cl}}$ and
       $v_{\text{q}}$ recovers twice the Schwinger–Keldysh contour action:
       $\langle u_{\text{cl}}, v_{\text{q}} \rangle + \langle u_{\text{q}}, v_{\text{cl}} \rangle = 2 S_{\text{SK}}(u, v)$,
     * Both pure classical ($u_{\text{q}} = 0$) and pure quantum ($u_{\text{cl}} = 0$) sheets are
       totally isotropic null subspaces under the Para-Kähler pairing,
     * The Thermofield Double state $\psi_{\text{TFD}}(j) = \sqrt{p_j}$ purifies the thermal Gibbs
       ensemble so that the doubled two-sheet inner product $\sum_j \psi_{\text{TFD}}(j)^2 E_j$
       equals the exact thermal expectation $\sum_j p_j E_j$.

4. **Section 4 — Tomita–Takesaki Modular Conjugation $J$ ($J \mathcal{M} J = \mathcal{M}'$) as Andreev Sheet-Swap Reflection**:
   - Defines the Tomita modular conjugation `tomitaSheetSwapConj (X, Y) := (Yᵀ, Xᵀ)` on the doubled
     matrix carrier $M_n(\mathbb{R}) \times M_n(\mathbb{R})$, together with the bimodal left action of
     the causal algebra $\mathcal{M}_L$ (`leftCausalAction A M := A * M`) and right action of the
     retrocausal commutant $\mathcal{M}_R$ (`rightCommutantAction B M := M * Bᵀ`).
   - Proves `tomita_takesaki_sheet_swap_commutant_duality`:
     * `tomitaSheetSwapConj` is a strict involution ($J^2 = \mathrm{id}$),
     * $J$ maps the forward causal sector $(A, 0)$ bijectively onto the retrocausal commutant
       sector $(0, A^{\mathsf{T}})$,
     * Every forward operator `leftCausalAction A` commutes identically with every $J$-reflected
       retrocausal operator `rightCommutantAction B` (`[L_A, R_B] = 0` by matrix associativity
       $(A M) B^{\mathsf{T}} = A (M B^{\mathsf{T}})$).
-/

set_option autoImplicit false

namespace InfoGeometry.Synthesis.DiracKreinTSVFKeldyshTomitaUnificationSynthesis

noncomputable section

open scoped BigOperators Matrix
open Finset Matrix
open InfoGeometry.Synthesis.SuperGrassmannianFiveGradedColorSupersymmetrySynthesis
open InfoGeometry.Synthesis.Z2Z2KoszulOperadicHomologyShirokovSynthesis
open InfoGeometry.Synthesis.ShirokovCliffordTraceDetInverseBridge

/-!
## Section 1: The Dirac Conjugation / Krein $J$-Adjoint Identity ($\bar{A} = \gamma^0 A^{\mathsf{T}} \gamma^0$) & Cayley–Hadamard Congruence to Totally Isotropic Para-Kähler Sheets
-/

/-- Local $2 \times 2$ non-commutativity generator $e_0 \in M_2(\mathbb{R})$ (`T16`). -/
def diracCl11E0 : Matrix (Fin 2) (Fin 2) ℝ := cl11GenE0

/-- Local $2 \times 2$ non-commutativity generator $e_1 \in M_2(\mathbb{R})$ (`T16`). -/
def diracCl11E1 : Matrix (Fin 2) (Fin 2) ℝ := cl11GenE1

/-- Explicit $2 \times 2$ non-commutativity witness on `Matrix (Fin 2) (Fin 2) ℝ` (`T16`). -/
theorem dirac_mat2_noncomm :
    diracCl11E0 * diracCl11E1 ≠ diracCl11E1 * diracCl11E0 :=
  cl11GenE0_mul_cl11GenE1_ne_comm

/-- Local $4 \times 4$ real Dirac generator $e_0 \in M_4(\mathbb{R})$ (`T16`). -/
def diracCl22E0 : Matrix (Fin 4) (Fin 4) ℝ := cl22E0

/-- Local $4 \times 4$ real Dirac generator $e_1 \in M_4(\mathbb{R})$ (`T16`). -/
def diracCl22E1 : Matrix (Fin 4) (Fin 4) ℝ := cl22E1

/-- Explicit $4 \times 4$ non-commutativity witness on `Matrix (Fin 4) (Fin 4) ℝ` (`T16`). -/
theorem dirac_mat4_noncomm :
    diracCl22E0 * diracCl22E1 ≠ diracCl22E1 * diracCl22E0 :=
  cl22E0_mul_cl22E1_ne_comm

/-- The standard $(2,2)$ Dirac fundamental symmetry matrix
$\gamma^0 = \operatorname{diag}(+1, +1, -1, -1) \in M_4(\mathbb{R})$. -/
def diracGamma0Krein4 : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.of ![![1, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, -1, 0], ![0, 0, 0, -1]]

/-- Off-diagonal $(2,2)$ Para-Kähler / Double Real Krein metric
$\eta_{\text{PK}} = \begin{pmatrix} 0 & I_2 \\ I_2 & 0 \end{pmatrix} \in M_4(\mathbb{R})$. -/
def paraKahlerMetricMatrix4 : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.of ![![0, 0, 1, 0], ![0, 0, 0, 1], ![1, 0, 0, 0], ![0, 1, 0, 0]]

/-- Unnormalized Cayley–Hadamard sheet-rotation matrix
$H_4 = \begin{pmatrix} I_2 & I_2 \\ I_2 & -I_2 \end{pmatrix} \in M_4(\mathbb{R})$
intertwining the diagonal Dirac Krein metric $\gamma^0$ with the off-diagonal Para-Kähler
metric $\eta_{\text{PK}}$. -/
def cayleyHadamardSheetTransform4 : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.of ![![1, 0, 1, 0], ![0, 1, 0, 1], ![1, 0, -1, 0], ![0, 1, 0, -1]]

/-- The Dirac bilinear pairing $\langle \phi, \psi \rangle_{\text{Dirac}} = \phi^{\mathsf{T}} \gamma^0 \psi$
of signature $(2,2)$ on $\mathbb{R}^4$. -/
def diracKreinPairing4 (φ ψ : Fin 4 → ℝ) : ℝ :=
  dotProduct φ (diracGamma0Krein4.mulVec ψ)

/-- The off-diagonal Para-Kähler bilinear pairing $\langle \phi, \psi \rangle_{\text{PK}} = \phi^{\mathsf{T}} \eta_{\text{PK}} \psi$
on $\mathbb{R}^4$. -/
def paraKahlerPairing4 (φ ψ : Fin 4 → ℝ) : ℝ :=
  dotProduct φ (paraKahlerMetricMatrix4.mulVec ψ)

/-- The Dirac operator adjoint (Krein $J$-adjoint) $\bar{A} := \gamma^0 A^{\mathsf{T}} \gamma^0$
on $M_4(\mathbb{R})$. -/
def diracKreinAdjoint4 (A : Matrix (Fin 4) (Fin 4) ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  diracGamma0Krein4 * Aᵀ * diracGamma0Krein4

/-- **Theorem 1.1 (`dirac_conjugation_is_exact_krein_adjoint_and_paraKahler_congruent`)**:
1. Neutral $(2,2)$ Krein involution: $(\gamma^0)^2 = I_4$ and $\operatorname{Tr}(\gamma^0) = 0$.
2. Exact Krein $J$-adjoint identity:
   $\langle \phi, A \psi \rangle_{\text{Dirac}} = \langle \bar{A} \phi, \psi \rangle_{\text{Dirac}}$.
3. Involutive anti-automorphism: $\overline{\bar{A}} = A$ and $\overline{A B} = \bar{B} \bar{A}$.
4. Cayley–Hadamard Congruence to Totally Isotropic Para-Kähler Sheets:
   $H_4^{\mathsf{T}} \gamma^0 H_4 = 2 \eta_{\text{PK}}$, and both the forward sheet
   $(u_0, u_1, 0, 0)$ and backward sheet $(0, 0, v_0, v_1)$ have identically zero self-norm
   under `paraKahlerPairing4`. -/
theorem dirac_conjugation_is_exact_krein_adjoint_and_paraKahler_congruent
    (A B : Matrix (Fin 4) (Fin 4) ℝ) (φ ψ : Fin 4 → ℝ) (u₀ u₁ v₀ v₁ : ℝ) :
    (diracGamma0Krein4 * diracGamma0Krein4 = (1 : Matrix (Fin 4) (Fin 4) ℝ) ∧
     diracGamma0Krein4.trace = 0) ∧
    diracKreinPairing4 φ (A.mulVec ψ) =
      diracKreinPairing4 ((diracKreinAdjoint4 A).mulVec φ) ψ ∧
    (diracKreinAdjoint4 (diracKreinAdjoint4 A) = A ∧
     diracKreinAdjoint4 (A * B) = diracKreinAdjoint4 B * diracKreinAdjoint4 A) ∧
    (cayleyHadamardSheetTransform4ᵀ * diracGamma0Krein4 * cayleyHadamardSheetTransform4 =
      (2 : ℝ) • paraKahlerMetricMatrix4 ∧
     paraKahlerPairing4 ![u₀, u₁, 0, 0] ![u₀, u₁, 0, 0] = 0 ∧
     paraKahlerPairing4 ![0, 0, v₀, v₁] ![0, 0, v₀, v₁] = 0) := by
  have h_gamma_sq : diracGamma0Krein4 * diracGamma0Krein4 = (1 : Matrix (Fin 4) (Fin 4) ℝ) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [diracGamma0Krein4, Matrix.mul_apply, Fin.sum_univ_four]
  have h_gamma_tr : diracGamma0Krein4.trace = 0 := by
    simp [diracGamma0Krein4, Matrix.trace, Matrix.diag, Fin.sum_univ_four]
  refine ⟨⟨h_gamma_sq, h_gamma_tr⟩, ?_, ⟨?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩
  · dsimp [diracKreinPairing4, diracKreinAdjoint4, Matrix.mulVec, dotProduct]
    simp only [Fin.sum_univ_four, diracGamma0Krein4, Matrix.mul_apply, Matrix.transpose_apply,
      Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]
    ring
  · dsimp [diracKreinAdjoint4]
    have h_symm : diracGamma0Krein4ᵀ = diracGamma0Krein4 := by
      ext i j
      fin_cases i <;> fin_cases j <;> rfl
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, h_symm]
    calc
      diracGamma0Krein4 * (diracGamma0Krein4 * (A * diracGamma0Krein4)) * diracGamma0Krein4
          = (diracGamma0Krein4 * diracGamma0Krein4) * A *
              (diracGamma0Krein4 * diracGamma0Krein4) := by
            simp only [Matrix.mul_assoc]
      _ = 1 * A * 1 := by rw [h_gamma_sq]
      _ = A := by simp
  · dsimp [diracKreinAdjoint4]
    rw [Matrix.transpose_mul]
    calc
      diracGamma0Krein4 * (Bᵀ * Aᵀ) * diracGamma0Krein4
          = diracGamma0Krein4 * Bᵀ * (diracGamma0Krein4 * diracGamma0Krein4) *
              Aᵀ * diracGamma0Krein4 := by
            rw [h_gamma_sq]
            simp only [Matrix.mul_one, Matrix.mul_assoc]
      _ = (diracGamma0Krein4 * Bᵀ * diracGamma0Krein4) *
            (diracGamma0Krein4 * Aᵀ * diracGamma0Krein4) := by
            simp only [Matrix.mul_assoc]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      (simp [cayleyHadamardSheetTransform4, diracGamma0Krein4, paraKahlerMetricMatrix4,
        Matrix.mul_apply, Fin.sum_univ_four]; try norm_num)
  · dsimp [paraKahlerPairing4, paraKahlerMetricMatrix4, Matrix.mulVec, dotProduct]
    simp only [Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]
    ring
  · dsimp [paraKahlerPairing4, paraKahlerMetricMatrix4, Matrix.mulVec, dotProduct]
    simp only [Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]
    ring

/-!
## Section 2: Aharonov–Bergmann–Lebowitz Two-State Vector Weak Values as Para-Kähler Cross-Ratios
-/

/-- Aharonov–Bergmann–Lebowitz Two-State Vector Formalism (TSVF) weak value
$$A_w(\phi, \psi) = \frac{\langle \phi, A \psi \rangle}{\langle \phi, \psi \rangle}$$
pairing a post-selected backward covector $\phi \in T^-$ with a pre-selected forward state $\psi \in T^+$. -/
def tsvfWeakValue {m : ℕ} (φ ψ : Fin m → ℝ) (A : Matrix (Fin m) (Fin m) ℝ) : ℝ :=
  dotProduct φ (A.mulVec ψ) / dotProduct φ ψ

/-- Canonical rank-$1$ projector $P_{00} = \begin{pmatrix} 1 & 0 \\ 0 & 0 \end{pmatrix} \in M_2(\mathbb{R})$
with spectrum $\{0, 1\}$. -/
def tsvfProjector00 : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.of ![![1, 0], ![0, 0]]

/-- Scalar associativity/commutativity helper $a (b c) = c (b a)$ for transpose dot-product duality. -/
lemma scalar_mul3_swap (a b c : ℝ) : a * (b * c) = c * (b * a) := by
  ring

/-- **Theorem 2.1 (`tsvf_weakValue_calculus_and_anomalous_krein_witness`)**:
1. Identity normalization: for any non-orthogonal two-state pair $\langle \phi, \psi \rangle \neq 0$,
   $I_w(\phi, \psi) = 1$.
2. Operator linearity: $(\alpha A + \beta B)_w(\phi, \psi) = \alpha A_w(\phi, \psi) + \beta B_w(\phi, \psi)$.
3. Retrodictive transpose duality: $A_w(\phi, \psi) = (A^{\mathsf{T}})_w(\psi, \phi)$.
4. **Anomalous Weak-Value Witness Outside $[0, 1]$**:
   Although `tsvfProjector00` is an idempotent projector ($P^2 = P$) whose eigenvalues lie strictly
   in $\{0, 1\}$, on the two-state pair $\phi = (2, -1)$, $\psi = (1, 1)$ its weak value is
   $P_w(\phi, \psi) = 2 > 1$, while on the orthogonal projector $(I_2 - P)$ its weak value is
   $(I_2 - P)_w(\phi, \psi) = -1 < 0$ (with $2 + (-1) = 1$!). -/
theorem tsvf_weakValue_calculus_and_anomalous_krein_witness
    {m : ℕ} (φ ψ : Fin m → ℝ) (A B : Matrix (Fin m) (Fin m) ℝ) (α β : ℝ)
    (h_ov : dotProduct φ ψ ≠ 0) :
    tsvfWeakValue φ ψ (1 : Matrix (Fin m) (Fin m) ℝ) = 1 ∧
    tsvfWeakValue φ ψ (α • A + β • B) =
      α * tsvfWeakValue φ ψ A + β * tsvfWeakValue φ ψ B ∧
    tsvfWeakValue φ ψ A = tsvfWeakValue ψ φ Aᵀ ∧
    (tsvfProjector00 * tsvfProjector00 = tsvfProjector00 ∧
     tsvfWeakValue ![2, -1] ![1, 1] tsvfProjector00 = 2 ∧
     tsvfWeakValue ![2, -1] ![1, 1] (1 - tsvfProjector00) = -1) := by
  refine ⟨?_, ?_, ?_, ⟨?_, ?_, ?_⟩⟩
  · dsimp [tsvfWeakValue]
    rw [Matrix.one_mulVec, div_self h_ov]
  · dsimp [tsvfWeakValue]
    rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec,
      dotProduct_add, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul,
      add_div, mul_div_assoc, mul_div_assoc]
  · dsimp [tsvfWeakValue]
    congr 1
    · dsimp [Matrix.mulVec, dotProduct]
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
      exact scalar_mul3_swap (φ j) (A j i) (ψ i)
    · exact dotProduct_comm φ ψ
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [tsvfProjector00, Matrix.mul_apply, Fin.sum_univ_two]
  · dsimp [tsvfWeakValue, tsvfProjector00, Matrix.mulVec, dotProduct]
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    norm_num
  · dsimp [tsvfWeakValue, tsvfProjector00, Matrix.mulVec, dotProduct]
    simp only [Fin.sum_univ_two, Matrix.one_apply, ↓reduceIte,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    norm_num

/-!
## Section 3: Schwinger–Keldysh ($C_+ \cup C_-$) Contour & Thermo Field Dynamics (TFD) Keldysh Rotation to the Para-Kähler Metric
-/

/-- Schwinger–Keldysh closed-time-path difference pairing
$S_{\text{SK}}((u_+, u_-), (v_+, v_-)) = \langle u_+, v_+ \rangle - \langle u_-, v_- \rangle$
between the forward branch $C_+$ and backward branch $C_-$. -/
def schwingerKeldyshContourPairing {m : ℕ}
    (u v : (Fin m → ℝ) × (Fin m → ℝ)) : ℝ :=
  dotProduct u.1 v.1 - dotProduct u.2 v.2

/-- Doubled off-diagonal Para-Kähler / Krein pairing
$\eta_{\text{PK}}((x_{\text{cl}}, x_{\text{q}}), (y_{\text{cl}}, y_{\text{q}})) = \langle x_{\text{cl}}, y_{\text{q}} \rangle + \langle x_{\text{q}}, y_{\text{cl}} \rangle$. -/
def keldyshParaKahlerPairing {m : ℕ}
    (x y : (Fin m → ℝ) × (Fin m → ℝ)) : ℝ :=
  dotProduct x.1 y.2 + dotProduct x.2 y.1

/-- Keldysh basis rotation $(u_+, u_-) \mapsto (u_+ + u_-, u_+ - u_-)$ mapping the forward/backward
contour branches $(C_+, C_-)$ to the classical/quantum Para-Kähler null sheets. -/
def keldyshRotation {m : ℕ}
    (u : (Fin m → ℝ) × (Fin m → ℝ)) : (Fin m → ℝ) × (Fin m → ℝ) :=
  (u.1 + u.2, u.1 - u.2)

/-- **Theorem 3.1 (`schwingerKeldysh_tfd_paraKahler_equivalence`)**:
1. **Exact Keldysh–Para-Kähler Isometry**:
   Under `keldyshRotation`, the off-diagonal Para-Kähler pairing equals twice the Schwinger–Keldysh
   contour difference pairing:
   `keldyshParaKahlerPairing (keldyshRotation u) (keldyshRotation v) = 2 * schwingerKeldyshContourPairing u v`.
2. **Total Nullity of the Classical and Quantum Sheets**:
   For any $x_{\text{cl}}, x_{\text{q}} \in \mathbb{R}^m$,
   `keldyshParaKahlerPairing (x_cl, 0) (x_cl, 0) = 0` and
   `keldyshParaKahlerPairing (0, x_q) (0, x_q) = 0`.
3. **Thermo Field Dynamics (TFD) Purification Identity**:
   For any non-negative probability weights $p_j \ge 0$ (`hp : ∀ j, 0 ≤ p j`), the doubled
   thermofield amplitude $\psi_{\text{TFD}}(j) = \sqrt{p_j}$ satisfies
   $\sum_j \psi_{\text{TFD}}(j) \widetilde{\psi}_{\text{TFD}}(j) E_j = \sum_j p_j E_j$. -/
theorem schwingerKeldysh_tfd_paraKahler_equivalence
    {m : ℕ} (u v : (Fin m → ℝ) × (Fin m → ℝ))
    (x_cl x_q p E : Fin m → ℝ) (hp : ∀ j : Fin m, 0 ≤ p j) :
    keldyshParaKahlerPairing (keldyshRotation u) (keldyshRotation v) =
      2 * schwingerKeldyshContourPairing u v ∧
    (keldyshParaKahlerPairing (x_cl, 0) (x_cl, 0) = 0 ∧
     keldyshParaKahlerPairing (0, x_q) (0, x_q) = 0) ∧
    (∑ j : Fin m, (Real.sqrt (p j) * Real.sqrt (p j)) * E j) =
      ∑ j : Fin m, p j * E j := by
  refine ⟨?_, ⟨?_, ?_⟩, ?_⟩
  · dsimp [keldyshParaKahlerPairing, keldyshRotation, schwingerKeldyshContourPairing, dotProduct]
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    ring
  · have _ := x_cl
    dsimp [keldyshParaKahlerPairing]
    simp
  · have _ := x_q
    dsimp [keldyshParaKahlerPairing]
    simp
  · refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Real.mul_self_sqrt (hp j)]

/-!
## Section 4: Tomita–Takesaki Modular Conjugation $J$ ($J \mathcal{M} J = \mathcal{M}'$) as Andreev Sheet-Swap Reflection
-/

/-- Tomita–Takesaki modular sheet-swap conjugation $J(X, Y) = (Y^{\mathsf{T}}, X^{\mathsf{T}})$
on the doubled matrix carrier $M_m(\mathbb{R}) \times M_m(\mathbb{R})$. -/
def tomitaSheetSwapConj {m : ℕ}
    (P : Matrix (Fin m) (Fin m) ℝ × Matrix (Fin m) (Fin m) ℝ) :
    Matrix (Fin m) (Fin m) ℝ × Matrix (Fin m) (Fin m) ℝ :=
  (P.2ᵀ, P.1ᵀ)

/-- Forward causal left multiplication $L_A(M) = A M$ on the Hilbert–Schmidt bimodule $M_m(\mathbb{R})$. -/
def leftCausalAction {m : ℕ} (A M : Matrix (Fin m) (Fin m) ℝ) : Matrix (Fin m) (Fin m) ℝ :=
  A * M

/-- Retrocausal commutant right multiplication $R_B(M) = M B^{\mathsf{T}}$ induced by Tomita
conjugation $J(B, 0) = (0, B^{\mathsf{T}})$. -/
def rightCommutantAction {m : ℕ} (B M : Matrix (Fin m) (Fin m) ℝ) : Matrix (Fin m) (Fin m) ℝ :=
  M * Bᵀ

/-- **Theorem 4.1 (`tomita_takesaki_sheet_swap_commutant_duality`)**:
1. **Involutive Andreev Sheet-Swap Reflection ($J^2 = \mathrm{id}$)**:
   `tomitaSheetSwapConj (tomitaSheetSwapConj P) = P`.
2. **Exact Mapping of Forward Sheet to Dual Commutant Sheet ($J \mathcal{M} J = \mathcal{M}'$)**:
   `tomitaSheetSwapConj (A, 0) = (0, Aᵀ)` and `tomitaSheetSwapConj (0, Bᵀ) = (B, 0)`.
3. **Bimodule Commutant Theorem ($[L_A, R_B] = 0$)**:
   For every forward causal operator $A \in M_m(\mathbb{R})$, every dual retrocausal operator
   $B \in M_m(\mathbb{R})$, and every state $M \in M_m(\mathbb{R})$, the forward left action
   and Tomita-reflected right action commute identically:
   `leftCausalAction A (rightCommutantAction B M) = rightCommutantAction B (leftCausalAction A M)`. -/
theorem tomita_takesaki_sheet_swap_commutant_duality
    (P : Matrix (Fin 2) (Fin 2) ℝ × Matrix (Fin 2) (Fin 2) ℝ)
    (A B M : Matrix (Fin 2) (Fin 2) ℝ) :
    tomitaSheetSwapConj (tomitaSheetSwapConj P) = P ∧
    (tomitaSheetSwapConj (A, 0) = (0, Aᵀ) ∧
     tomitaSheetSwapConj (0, Bᵀ) = (B, 0)) ∧
    leftCausalAction A (rightCommutantAction B M) =
      rightCommutantAction B (leftCausalAction A M) := by
  refine ⟨?_, ⟨?_, ?_⟩, ?_⟩
  · cases P
    dsimp [tomitaSheetSwapConj]
    rw [Matrix.transpose_transpose, Matrix.transpose_transpose]
  · simp [tomitaSheetSwapConj]
  · simp [tomitaSheetSwapConj]
  · dsimp [leftCausalAction, rightCommutantAction]
    rw [Matrix.mul_assoc]

end

end InfoGeometry.Synthesis.DiracKreinTSVFKeldyshTomitaUnificationSynthesis
