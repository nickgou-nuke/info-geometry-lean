/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Thermodynamics.UnruhTemperature
import InfoGeometry.Synthesis.LogarithmicTimeVacuumSurprisalSynthesis
import InfoGeometry.Synthesis.Cl22RealDiracCarrier
import InfoGeometry.Synthesis.Cl22LightconeWeylBerezinGaugeBridge
import InfoGeometry.Synthesis.G2Sl2SeventeenParameterProductActionBridge
import InfoGeometry.Synthesis.Cl55SuperGrassmannianKKTSynthesis
import InfoGeometry.Synthesis.Cl55TwistorSplitSedenionColorBridge
import InfoGeometry.Synthesis.Cl55TwistorLinearEquivAndOrderFourBridge

/-!
# Cuntz–Toeplitz Lightcone Projector Resolution in $\mathrm{Cl}(2,2)$, Unruh–Gibbs Modular Surprisal & Weyl–KKS Bridge, and $\mathrm{Cl}(5,5)$ Lepton–Quark Twistor Decomposition

This module synthesizes three cross-subsystem bridges across the doubled real Dirac algebra
$\mathrm{Cl}(2,2) \cong M_4(\mathbb{R})$, the Rindler–Unruh modular thermodynamics and
$\mathfrak{so}(2,1)$ Kirillov–Kostant–Souriau (KKS) pairing, and the 16-dimensional
$\mathrm{Cl}(5,5)$ split-twistor carrier `Twistor55 ℝ`:

1. **Section 1 — Cuntz–Toeplitz Orthogonal Projector Resolution on the Doubled $\mathrm{Cl}(2,2)$ Lightcone**:
   - Defines the normalized Sheet-1 lightcone chiral ladder projectors
     $P_+ = \frac{1}{2} n_+^{(1)} n_-^{(1)}$ and $P_- = \frac{1}{2} n_-^{(1)} n_+^{(1)}$ in
     `Matrix (Fin 4) (Fin 4) ℝ`, together with the $(2|2)$ supertrace `supertrace22` and
     the cross-sheet complex structure alias `interSheetComplexJ = J_geom`.
   - Proves `cuntz_toeplitz_doubled_dirac_master_bridge`: nilpotency $(n_\pm^{(1)})^2 = 0$,
     partition of unity $P_+ + P_- = I_4$, idempotency $P_\pm^2 = P_\pm$, mutual orthogonality
     $P_+ P_- = P_- P_+ = 0$, Peirce creation absorption $n_+^{(1)} P_- = P_+ n_+^{(1)} = n_+^{(1)}$,
     $J_{\mathrm{geom}}^2 = -I_4$, vanishing $(2|2)$ supertraces of $J_{\mathrm{geom}}$ and
     $J_{\mathrm{geom}}^2$, and ordinary matrix traces $\operatorname{Tr}(P_+) = \operatorname{Tr}(P_-) = 2$.

2. **Section 2 — Unruh–Gibbs Modular Surprisal First Law & Weyl-Soldered $\mathfrak{so}(2,1)$ KKS Bridge**:
   - Proves `unruh_gibbs_surprisal_first_law_bridge`, connecting `RindlerObserver`,
     `inverseTemperature`, and `unruhTemperature` from `InfoGeometry.Thermodynamics.UnruhTemperature`
     with `modularSurprisal`, `gibbsState`, and `first_law_of_entanglement_gibbs` from
     `InfoGeometry.Synthesis.LogarithmicTimeVacuumSurprisalSynthesis`.
   - Defines the $4 \times 4$ Weyl boost matrix `weylBoostMatrix`, conjugation operator
     `weylBoostConjugate`, and radial $\mathfrak{so}(2,1)$ KKS 2-form `logConformalKKSTwoForm`,
     and proves `unruh_weyl_soldered_kks_master_bridge`.

3. **Section 3 — $\mathrm{Cl}(5,5)$ Twistor Lepton–Quark Direct-Sum Decomposition & Single-Sheet Quadratic Reduction**:
   - Defines the doubled split-twistor projections `leptonSubspaceProj` and `quarkSubspaceProj`
     and complementary embeddings `embedPureLepton` and `embedPureQuark` on `Twistor55 ℝ`.
   - Proves `twistor55_lepton_quark_direct_sum_decomposition` (exact additive reconstruction,
     cross-sector orthogonality, and retraction laws) and `lepton_sector_klein_quadric_reduction`
     (together with `zornNorm_lepton_sector_reduction` on `ZornSplitOctonion ℝ`).
-/

set_option autoImplicit false
noncomputable section

namespace InfoGeometry.Synthesis.Frontier103CuntzLeptonQuarkUnruhKleinBridge

open BigOperators Finset Matrix
open InfoGeometry.Thermodynamics.UnruhTemperature
open InfoGeometry.Canonical.ZornSplitOctonionFin8Bridge
open InfoGeometry.Synthesis.LogarithmicTimeVacuumSurprisalSynthesis
open InfoGeometry.Synthesis.Cl22RealDiracCarrier
open InfoGeometry.Synthesis.Cl22LightconeWeylBerezinGaugeBridge
open InfoGeometry.Synthesis.G2Sl2SeventeenParameterProductActionBridge
open InfoGeometry.Synthesis.Cl55SuperGrassmannianKKTSynthesis
open InfoGeometry.Synthesis.Cl55TwistorSplitSedenionColorBridge
open InfoGeometry.Synthesis.Cl55TwistorLinearEquivAndOrderFourBridge

/-!
## Section 1: Cuntz–Toeplitz Lightcone Projector Resolution in $\mathrm{Cl}(2,2) \cong M_4(\mathbb{R})$
-/

/-- Explicit $4 \times 4$ non-commutativity witness on `Matrix (Fin 4) (Fin 4) ℝ`:
the Sheet-1 Dirac generators $e_0$ and $e_1$ do not commute ($e_0 e_1 \neq e_1 e_0$). -/
theorem cl22_dirac_carrier_noncomm :
    (e0 : Matrix (Fin 4) (Fin 4) ℝ) * e1 ≠ e1 * e0 :=
  e0_mul_e1_ne_comm

/-- Normalized forward lightcone Peirce projector
$P_+ := \frac{1}{2} n_+^{(1)} n_-^{(1)} \in M_4(\mathbb{R})$. -/
def P_plus : Matrix (Fin 4) (Fin 4) ℝ :=
  (1 / 2 : ℝ) • (n_plus_1 * n_minus_1)

/-- Normalized backward lightcone Peirce projector
$P_- := \frac{1}{2} n_-^{(1)} n_+^{(1)} \in M_4(\mathbb{R})$. -/
def P_minus : Matrix (Fin 4) (Fin 4) ℝ :=
  (1 / 2 : ℝ) • (n_minus_1 * n_plus_1)

/-- Cross-sheet geometric complex structure $J_{\mathrm{geom}} = e_0 e_2 \in M_4(\mathbb{R})$
satisfying $J_{\mathrm{geom}}^2 = -I_4$. -/
abbrev interSheetComplexJ : Matrix (Fin 4) (Fin 4) ℝ :=
  J_geom

/-- The $(2|2)$ graded supertrace on `Matrix (Fin 4) (Fin 4) ℝ`:
$\operatorname{Str}_{2|2}(M) = M_{0,0} + M_{1,1} - M_{2,2} - M_{3,3}$. -/
def supertrace22 (M : Matrix (Fin 4) (Fin 4) ℝ) : ℝ :=
  M 0 0 + M 1 1 - M 2 2 - M 3 3

/-- Helper identity `rcp_sqrt_two_sq`: $(\frac{1}{\sqrt{2}})^2 = \frac{1}{2}$ for evaluating lightcone products. -/
theorem rcp_sqrt_two_sq :
    (1 / Real.sqrt 2) * (1 / Real.sqrt 2) = (1 / 2 : ℝ) := by
  rw [div_mul_div_comm, one_mul, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

/-- Explicit $4 \times 4$ matrix representation of $P_+ = \operatorname{diag}(1, 1, 0, 0)$. -/
theorem P_plus_explicit :
    P_plus = !![ (1 : ℝ), 0, 0, 0;
                 0, 1, 0, 0;
                 0, 0, 0, 0;
                 0, 0, 0, 0 ] := by
  unfold P_plus n_plus_1 n_minus_1
  rw [smul_mul_smul_comm, rcp_sqrt_two_sq, smul_smul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [e0, e1] <;> norm_num

/-- Explicit $4 \times 4$ matrix representation of $P_- = \operatorname{diag}(0, 0, 1, 1)$. -/
theorem P_minus_explicit :
    P_minus = !![ (0 : ℝ), 0, 0, 0;
                  0, 0, 0, 0;
                  0, 0, 1, 0;
                  0, 0, 0, 1 ] := by
  unfold P_minus n_plus_1 n_minus_1
  rw [smul_mul_smul_comm, rcp_sqrt_two_sq, smul_smul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [e0, e1] <;> norm_num

/-- Cuntz–Toeplitz partition of unity $P_+ + P_- = I_4$ on the 4D real Dirac spinor carrier. -/
theorem P_plus_add_P_minus_eq_one :
    P_plus + P_minus = (1 : Matrix (Fin 4) (Fin 4) ℝ) := by
  unfold P_plus P_minus
  rw [← smul_add, majorana_witt_anticommutation_relations.1, smul_smul]
  norm_num

/-- Right annihilation of $n_+^{(1)}$ by $P_+$: $n_+^{(1)} P_+ = 0$. -/
theorem n_plus_1_mul_P_plus_eq_zero :
    n_plus_1 * P_plus = 0 := by
  unfold P_plus
  rw [Matrix.mul_smul, ← Matrix.mul_assoc, majorana_nilpotency.1, Matrix.zero_mul, smul_zero]

/-- Left annihilation of $n_+^{(1)}$ by $P_-$: $P_- n_+^{(1)} = 0$. -/
theorem P_minus_mul_n_plus_1_eq_zero :
    P_minus * n_plus_1 = 0 := by
  unfold P_minus
  rw [Matrix.smul_mul, Matrix.mul_assoc, majorana_nilpotency.1, Matrix.mul_zero, smul_zero]

/-- Peirce creation-mode absorption identities $n_+^{(1)} P_- = n_+^{(1)}$ and
$P_+ n_+^{(1)} = n_+^{(1)}$. -/
theorem n_plus_1_peirce_absorption :
    n_plus_1 * P_minus = n_plus_1 ∧
    P_plus * n_plus_1 = n_plus_1 := by
  have h_sum := P_plus_add_P_minus_eq_one
  constructor
  · calc n_plus_1 * P_minus
        = 0 + n_plus_1 * P_minus := (zero_add _).symm
      _ = n_plus_1 * P_plus + n_plus_1 * P_minus := by rw [n_plus_1_mul_P_plus_eq_zero]
      _ = n_plus_1 * (P_plus + P_minus) := (Matrix.mul_add _ _ _).symm
      _ = n_plus_1 * 1 := by rw [h_sum]
      _ = n_plus_1 := Matrix.mul_one _
  · calc P_plus * n_plus_1
        = P_plus * n_plus_1 + 0 := (add_zero _).symm
      _ = P_plus * n_plus_1 + P_minus * n_plus_1 := by rw [P_minus_mul_n_plus_1_eq_zero]
      _ = (P_plus + P_minus) * n_plus_1 := (Matrix.add_mul _ _ _).symm
      _ = 1 * n_plus_1 := by rw [h_sum]
      _ = n_plus_1 := Matrix.one_mul _

/-- Idempotency and mutual orthogonality of $P_+$ and $P_-$. -/
theorem P_plus_P_minus_idempotent_orthogonal :
    P_plus * P_plus = P_plus ∧
    P_minus * P_minus = P_minus ∧
    P_plus * P_minus = 0 ∧
    P_minus * P_plus = 0 := by
  rw [P_plus_explicit, P_minus_explicit]
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    (ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_four])

/-- Both lightcone Peirce projectors $P_+$ and $P_-$ have ordinary matrix trace $2$, while
the cross-sheet complex structure $J_{\mathrm{geom}}$ and its square $J_{\mathrm{geom}}^2 = -I_4$
have vanishing $(2|2)$ supertrace. -/
theorem P_plus_P_minus_trace_and_interSheetComplexJ_supertrace :
    Matrix.trace P_plus = 2 ∧
    Matrix.trace P_minus = 2 ∧
    supertrace22 interSheetComplexJ = 0 ∧
    supertrace22 (interSheetComplexJ * interSheetComplexJ) = 0 := by
  have hJ_sq : interSheetComplexJ * interSheetComplexJ = -(1 : Matrix (Fin 4) (Fin 4) ℝ) :=
    cl22_hypercomplex_and_geometric_i.2.2.1
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [P_plus_explicit]
    simp [Matrix.trace, Matrix.diag, Fin.sum_univ_four]
    norm_num
  · rw [P_minus_explicit]
    simp [Matrix.trace, Matrix.diag, Fin.sum_univ_four]
    norm_num
  · unfold interSheetComplexJ
    rw [bivector_explicit_matrices.2.2.1]
    simp [supertrace22]
  · rw [hJ_sq]
    simp [supertrace22]

/-- **Theorem 1.1 (Cuntz–Toeplitz Lightcone Projector Resolution & Doubled Dirac Master Bridge)**:
In the doubled real Dirac carrier $\mathrm{Cl}(2,2) \cong M_4(\mathbb{R})$:
1. The Sheet-1 lightcone Majorana generators $n_+^{(1)}, n_-^{(1)}$ are nilpotent
   ($(n_+^{(1)})^2 = 0$, $(n_-^{(1)})^2 = 0$).
2. The normalized chiral ladder projectors $P_+ = \frac{1}{2} n_+^{(1)} n_-^{(1)}$ and
   $P_- = \frac{1}{2} n_-^{(1)} n_+^{(1)}$ form a defect-free orthogonal idempotent resolution
   of the $4 \times 4$ identity ($P_+ + P_- = I_4$, $P_\pm^2 = P_\pm$, $P_+ P_- = P_- P_+ = 0$).
3. $n_+^{(1)}$ satisfies Peirce creation absorption $n_+^{(1)} P_- = n_+^{(1)}$ and
   $P_+ n_+^{(1)} = n_+^{(1)}$.
4. The cross-sheet complex structure $J = e_0 e_2$ satisfies $J^2 = -I_4$ with vanishing
   $(2|2)$ supertraces $\operatorname{Str}_{2|2}(J) = \operatorname{Str}_{2|2}(J^2) = 0$, while
   $\operatorname{Tr}(P_+) = \operatorname{Tr}(P_-) = 2$. -/
theorem cuntz_toeplitz_doubled_dirac_master_bridge :
    (n_plus_1 * n_plus_1 = 0 ∧ n_minus_1 * n_minus_1 = 0) ∧
    (P_plus + P_minus = (1 : Matrix (Fin 4) (Fin 4) ℝ)) ∧
    (P_plus * P_plus = P_plus ∧ P_minus * P_minus = P_minus) ∧
    (P_plus * P_minus = 0 ∧ P_minus * P_plus = 0) ∧
    (n_plus_1 * P_minus = n_plus_1 ∧ P_plus * n_plus_1 = n_plus_1) ∧
    (interSheetComplexJ * interSheetComplexJ = -(1 : Matrix (Fin 4) (Fin 4) ℝ) ∧
     supertrace22 interSheetComplexJ = 0 ∧
     supertrace22 (interSheetComplexJ * interSheetComplexJ) = 0 ∧
     Matrix.trace P_plus = 2 ∧
     Matrix.trace P_minus = 2) := by
  rcases majorana_nilpotency with ⟨hn1, hn2, _, _⟩
  rcases P_plus_P_minus_idempotent_orthogonal with ⟨hp2, hm2, hpm, hmp⟩
  rcases P_plus_P_minus_trace_and_interSheetComplexJ_supertrace with ⟨htp, htm, hstrJ, hstrJ2⟩
  exact ⟨⟨hn1, hn2⟩, P_plus_add_P_minus_eq_one, ⟨hp2, hm2⟩, ⟨hpm, hmp⟩,
    n_plus_1_peirce_absorption,
    ⟨cl22_hypercomplex_and_geometric_i.2.2.1, hstrJ, hstrJ2, htp, htm⟩⟩

/-!
## Section 2: Unruh–Gibbs Modular Surprisal First Law & Weyl-Soldered $\mathfrak{so}(2,1)$ KKS Bridge
-/

/-- Reciprocal identity $\beta(a) = \frac{1}{T_{\mathrm{U}}(a)}$ between `inverseTemperature`
and `unruhTemperature` for any `obs : RindlerObserver`. -/
theorem beta_eq_inv_unruhTemperature (obs : RindlerObserver) :
    inverseTemperature obs = 1 / unruhTemperature obs ∧
    unruhTemperature obs * inverseTemperature obs = 1 := by
  have h_T_ne : unruhTemperature obs ≠ 0 := ne_of_gt (unruhTemperature_pos obs)
  have h_inv : inverseTemperature obs = (unruhTemperature obs)⁻¹ := by
    unfold unruhTemperature
    rw [inv_inv]
  constructor
  · rw [h_inv, one_div]
  · rw [h_inv]
    exact mul_inv_cancel₀ h_T_ne

/-- **Theorem 2.1 (Unruh–Gibbs Modular Surprisal & First Law of Entanglement Bridge)**:
For any Rindler observer `obs : RindlerObserver`, finite energy spectrum $E : \mathrm{Fin}\, n \to \mathbb{R}$,
partition function $Z > 0$, and traceless entanglement perturbation $\delta\rho : \mathrm{Fin}\, n \to \mathbb{R}$
($\sum_i \delta\rho_i = 0$):
1. The modular surprisal of the Gibbs state at `inverseTemperature obs` equals both
   $\frac{2\pi}{a} E_i + \ln Z$ and $\frac{E_i}{T_{\mathrm{U}}(a)} + \ln Z$.
2. The First Law of Entanglement holds in both inverse-temperature and Unruh-temperature forms:
   $$\sum_{i} \delta\rho_i \, H_{\mathrm{mod}}(p_i)
     = \frac{2\pi}{a} \sum_{i} \delta\rho_i E_i
     = \frac{1}{T_{\mathrm{U}}(a)} \sum_{i} \delta\rho_i E_i.$$ -/
theorem unruh_gibbs_surprisal_first_law_bridge
    {n : ℕ} (obs : RindlerObserver) (Z : ℝ) (E deltaRho : Fin n → ℝ)
    (hZ : 0 < Z) (h_trace_zero : ∑ i : Fin n, deltaRho i = 0) (i : Fin n) :
    (modularSurprisal (gibbsState (inverseTemperature obs) Z E i) =
       ((2 * Real.pi) / obs.a) * E i + Real.log Z ∧
     modularSurprisal (gibbsState (inverseTemperature obs) Z E i) =
       E i / unruhTemperature obs + Real.log Z) ∧
    ((∑ j : Fin n, deltaRho j * modularSurprisal (gibbsState (inverseTemperature obs) Z E j)) =
       ((2 * Real.pi) / obs.a) * (∑ j : Fin n, deltaRho j * E j) ∧
     (∑ j : Fin n, deltaRho j * modularSurprisal (gibbsState (inverseTemperature obs) Z E j)) =
       (1 / unruhTemperature obs) * (∑ j : Fin n, deltaRho j * E j)) := by
  have h_surp := modularSurprisal_gibbsState (inverseTemperature obs) Z E hZ i
  have h_first := first_law_of_entanglement_gibbs (inverseTemperature obs) Z E deltaRho hZ h_trace_zero
  have h_beta := inverseTemperature_eq obs
  have h_inv_T := (beta_eq_inv_unruhTemperature obs).1
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · rw [h_surp, h_beta]
  · rw [h_surp, h_inv_T, one_div_mul_eq_div]
  · rw [h_first, h_beta]
  · rw [h_first, h_inv_T]

/-- $4 \times 4$ Weyl lightcone boost matrix in `Matrix (Fin 4) (Fin 4) ℝ` scaling the
upper-left $2 \times 2$ spinor block by $\lambda$ and the lower-right $2 \times 2$ block
by $\lambda \lambda^{-1}$. -/
def weylBoostMatrix (lam invLam : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![lam, 0, 0, 0;
     0, lam, 0, 0;
     0, 0, lam * invLam, 0;
     0, 0, 0, lam * invLam]

/-- Conjugation of a $4 \times 4$ real Dirac matrix $M \in M_4(\mathbb{R})$ by the Weyl
lightcone boost matrix `weylBoostMatrix lam invLam`. -/
def weylBoostConjugate (lam invLam : ℝ) (M : Matrix (Fin 4) (Fin 4) ℝ) :
    Matrix (Fin 4) (Fin 4) ℝ :=
  weylBoostMatrix lam invLam * M * weylBoostMatrix invLam lam

/-- Radial $\mathfrak{so}(2,1)$ Kirillov–Kostant–Souriau (KKS) alternating 2-form evaluated at
the radial Cartan basepoint $\mu(m) = (m, 0, 0) \in \mathbb{R}^{2,1}$ via `so21KKSForm` from
`InfoGeometry.Synthesis.G2Sl2SeventeenParameterProductActionBridge`. -/
def logConformalKKSTwoForm (m : ℝ) (ξ η : Fin 3 → ℝ) : ℝ :=
  so21KKSForm ![m, 0, 0] ξ η

/-- **Theorem 2.2 (Unruh Reciprocity, Weyl Lightcone Boost Conjugation, & $\mathfrak{so}(2,1)$ KKS Master Bridge)**:
For any Rindler observer `obs : RindlerObserver`, reciprocal Weyl scale parameters
$\lambda \cdot \lambda^{-1} = 1$, radial parameter $m \in \mathbb{R}$, and tangent vectors
$\xi, \eta \in \mathbb{R}^3$:
1. $T_{\mathrm{U}}(a) \cdot \beta(a) = 1$.
2. `weylBoostConjugate lam invLam` scales the forward Sheet-1 lightcone generator $e_0 + e_1$ by
   $\lambda$ and the backward generator $e_0 - e_1$ by $\lambda^{-1}$.
3. `weylBoostConjugate lam invLam` leaves the transverse Sheet-2 generators $e_2, e_3$ strictly invariant.
4. The $(2|2)$ supertrace of `weylBoostMatrix lam invLam * weylBoostMatrix invLam lam` vanishes.
5. `logConformalKKSTwoForm m` is alternating ($\omega_m(\xi, \eta) = -\omega_m(\eta, \xi)$) and
   annihilates the radial basepoint vector $(m, 0, 0)$ ($\omega_m((m, 0, 0), \eta) = 0$). -/
theorem unruh_weyl_soldered_kks_master_bridge
    (obs : RindlerObserver) (lam invLam : ℝ) (h_inv : lam * invLam = 1)
    (m : ℝ) (ξ η : Fin 3 → ℝ) :
    (unruhTemperature obs * inverseTemperature obs = 1) ∧
    (weylBoostConjugate lam invLam (e0 + e1) = lam • (e0 + e1) ∧
     weylBoostConjugate lam invLam (e0 - e1) = invLam • (e0 - e1)) ∧
    (weylBoostConjugate lam invLam e2 = e2 ∧
     weylBoostConjugate lam invLam e3 = e3) ∧
    (supertrace22 (weylBoostMatrix lam invLam * weylBoostMatrix invLam lam) = 0) ∧
    (logConformalKKSTwoForm m ξ η = -logConformalKKSTwoForm m η ξ ∧
     logConformalKKSTwoForm m ![m, 0, 0] η = 0) := by
  have h_inv_comm : invLam * lam = 1 := by rw [mul_comm, h_inv]
  refine ⟨(beta_eq_inv_unruhTemperature obs).2, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ⟨?_, ?_⟩⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [weylBoostConjugate, weylBoostMatrix, e0, e1, h_inv, h_inv_comm,
        Matrix.mul_apply, Fin.sum_univ_four]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [weylBoostConjugate, weylBoostMatrix, e0, e1, h_inv, h_inv_comm,
        Matrix.mul_apply, Fin.sum_univ_four, add_mul, mul_add]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [weylBoostConjugate, weylBoostMatrix, e2, h_inv, h_inv_comm,
        Matrix.mul_apply, Fin.sum_univ_four]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [weylBoostConjugate, weylBoostMatrix, e3, h_inv, h_inv_comm,
        Matrix.mul_apply, Fin.sum_univ_four]
  · simp [supertrace22, weylBoostMatrix, h_inv, h_inv_comm,
      Matrix.mul_apply, Fin.sum_univ_four]
  · exact so21KKSForm_skew ![m, 0, 0] ξ η
  · exact so21KKSForm_kernel_basepoint ![m, 0, 0] η

/-!
## Section 3: $\mathrm{Cl}(5,5)$ Twistor Lepton–Quark Direct-Sum Decomposition & Single-Sheet Quadratic Reduction
-/

/-- Projects a 16-component split twistor $Z = (\psi, \chi) \in \mathrm{Twistor55}\, \mathbb{R}$
onto its doubled 2-component colorless **Lepton** singlet sector
$(\mathbf{1} \oplus \mathbf{1})_{T^+} \oplus (\mathbf{1} \oplus \mathbf{1})_{T^-}$. -/
def leptonSubspaceProj (Z : Twistor55 ℝ) : (Fin 2 → ℝ) × (Fin 2 → ℝ) :=
  ((gunaydinGurseySplit Z.1).1, (gunaydinGurseySplit Z.2).1)

/-- Projects a 16-component split twistor $Z = (\psi, \chi) \in \mathrm{Twistor55}\, \mathbb{R}$
onto its doubled $3 \oplus 3 = 6$-component **Quark / Antiquark** color-triplet sector
$(\mathbf{3} \oplus \bar{\mathbf{3}})_{T^+} \oplus (\mathbf{3} \oplus \bar{\mathbf{3}})_{T^-}$. -/
def quarkSubspaceProj (Z : Twistor55 ℝ) :
    ((Fin 3 → ℝ) × (Fin 3 → ℝ)) × ((Fin 3 → ℝ) × (Fin 3 → ℝ)) :=
  ((gunaydinGurseySplit Z.1).2, (gunaydinGurseySplit Z.2).2)

/-- Embeds a pure lepton pair $L = (\ell_+, \ell_-) \in (\mathrm{Fin}\, 2 \to \mathbb{R})^2$ into
the 16-component split-twistor space `Twistor55 ℝ` with vanishing quark color components. -/
def embedPureLepton (L : (Fin 2 → ℝ) × (Fin 2 → ℝ)) : Twistor55 ℝ :=
  (gunaydinGurseyCombine (L.1, (0, 0)),
   gunaydinGurseyCombine (L.2, (0, 0)))

/-- Embeds a pure quark/antiquark color configuration
$Q = ((q_+, \bar{q}_+), (q_-, \bar{q}_-))$ into the 16-component split-twistor space
`Twistor55 ℝ` with vanishing lepton singlet components. -/
def embedPureQuark
    (Q : ((Fin 3 → ℝ) × (Fin 3 → ℝ)) × ((Fin 3 → ℝ) × (Fin 3 → ℝ))) : Twistor55 ℝ :=
  (gunaydinGurseyCombine (0, Q.1),
   gunaydinGurseyCombine (0, Q.2))

/-- **Theorem 3.1 ($\mathrm{Cl}(5,5)$ Split-Twistor Lepton–Quark Direct-Sum Decomposition)**:
1. Every split twistor $Z \in \mathrm{Twistor55}\, \mathbb{R}$ decomposes as the sum of its
   pure lepton and pure quark components:
   `embedPureLepton (leptonSubspaceProj Z) + embedPureQuark (quarkSubspaceProj Z) = Z`.
2. Cross-sector orthogonality of projections:
   `leptonSubspaceProj (embedPureQuark Q) = 0` and `quarkSubspaceProj (embedPureLepton L) = 0`.
3. Exact retraction identities:
   `leptonSubspaceProj (embedPureLepton L) = L` and `quarkSubspaceProj (embedPureQuark Q) = Q`. -/
theorem twistor55_lepton_quark_direct_sum_decomposition
    (Z : Twistor55 ℝ)
    (L : (Fin 2 → ℝ) × (Fin 2 → ℝ))
    (Q : ((Fin 3 → ℝ) × (Fin 3 → ℝ)) × ((Fin 3 → ℝ) × (Fin 3 → ℝ))) :
    (embedPureLepton (leptonSubspaceProj Z) + embedPureQuark (quarkSubspaceProj Z) = Z) ∧
    (leptonSubspaceProj (embedPureQuark Q) = 0 ∧
     quarkSubspaceProj (embedPureLepton L) = 0) ∧
    (leptonSubspaceProj (embedPureLepton L) = L ∧
     quarkSubspaceProj (embedPureQuark Q) = Q) := by
  refine ⟨?_, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · apply Prod.ext
    · ext i
      fin_cases i <;>
        simp [embedPureLepton, embedPureQuark, leptonSubspaceProj, quarkSubspaceProj,
          gunaydinGurseyCombine, gunaydinGurseySplit]
    · ext i
      fin_cases i <;>
        simp [embedPureLepton, embedPureQuark, leptonSubspaceProj, quarkSubspaceProj,
          gunaydinGurseyCombine, gunaydinGurseySplit]
  · apply Prod.ext <;>
      (ext i; fin_cases i <;>
        simp [leptonSubspaceProj, embedPureQuark, gunaydinGurseySplit, gunaydinGurseyCombine])
  · apply Prod.ext <;> apply Prod.ext <;>
      (ext i; fin_cases i <;>
        simp [quarkSubspaceProj, embedPureLepton, gunaydinGurseySplit, gunaydinGurseyCombine])
  · apply Prod.ext <;>
      (ext i; fin_cases i <;>
        simp [leptonSubspaceProj, embedPureLepton, gunaydinGurseySplit, gunaydinGurseyCombine])
  · apply Prod.ext <;> apply Prod.ext <;>
      (ext i; fin_cases i <;>
        simp [quarkSubspaceProj, embedPureQuark, gunaydinGurseySplit, gunaydinGurseyCombine])

/-- Split-signature quadratic form on a single 8D semi-spinor sheet `Fin 8 → ℝ` aligned with
the Günaydin–Gürsey splitting `gunaydinGurseySplit x = (![x 0, x 1], ![x 2, x 3, x 4], ![x 5, x 6, x 7])`,
pairing the hyperbolic lepton singlet coordinates `(x 0, x 1)` against the quark/antiquark
color-triplet coordinates `((x 2, x 3, x 4), (x 5, x 6, x 7))`. -/
def splitOctonionQuadraticForm (x : Fin 8 → ℝ) : ℝ :=
  2 * x 0 * x 1 - 2 * (x 2 * x 5 + x 3 * x 6 + x 4 * x 7)

/-- **Theorem 3.2 (Single-Sheet Lepton-Sector Quadratic Reduction in Günaydin–Gürsey Coordinates)**:
When the quark and antiquark color-triplet coordinates of $x \in \mathrm{Fin}\, 8 \to \mathbb{R}$
vanish (`(gunaydinGurseySplit x).2 = 0`), `splitOctonionQuadraticForm x` reduces exclusively to
the hyperbolic lepton singlet pairing `2 * x 0 * x 1`. -/
theorem lepton_sector_klein_quadric_reduction
    (x : Fin 8 → ℝ) (h_quark_zero : (gunaydinGurseySplit x).2 = 0) :
    splitOctonionQuadraticForm x = 2 * x 0 * x 1 := by
  have hx2 : x 2 = 0 := congrFun (congrArg Prod.fst h_quark_zero) 0
  have hx3 : x 3 = 0 := congrFun (congrArg Prod.fst h_quark_zero) 1
  have hx4 : x 4 = 0 := congrFun (congrArg Prod.fst h_quark_zero) 2
  have hx5 : x 5 = 0 := congrFun (congrArg Prod.snd h_quark_zero) 0
  have hx6 : x 6 = 0 := congrFun (congrArg Prod.snd h_quark_zero) 1
  have hx7 : x 7 = 0 := congrFun (congrArg Prod.snd h_quark_zero) 2
  unfold splitOctonionQuadraticForm
  rw [hx2, hx3, hx4, hx5, hx6, hx7]
  ring

/-- **Theorem 3.3 (Zorn Split-Octonion Norm Reduction on the Colorless Peircian Diagonal Sector)**:
For any Zorn split-octonion $z \in \mathrm{ZornSplitOctonion}\, \mathbb{R}$ whose off-diagonal
$\Lambda^1$ and $\Lambda^2$ color vectors vanish (`z.u = 0` and `z.v = 0`), the Zorn quadratic
norm `zornNorm z = z.a * z.b - vec3Dot z.u z.v` reduces to the hyperbolic Peircian diagonal
product `z.a * z.b`, which in the Fock chart `zornToFin8 z` equals `(zornToFin8 z) 0 * (zornToFin8 z) 7`. -/
theorem zornNorm_lepton_sector_reduction
    (z : ZornSplitOctonion ℝ) (hu : z.u = 0) (hv : z.v = 0) :
    zornNorm z = z.a * z.b ∧
    zornNorm z = (zornToFin8 z) 0 * (zornToFin8 z) 7 := by
  have h_norm : zornNorm z = z.a * z.b := by
    unfold zornNorm vec3Dot
    rw [hu, hv]
    simp
  refine ⟨h_norm, ?_⟩
  rw [h_norm]
  simp [zornToFin8]

end InfoGeometry.Synthesis.Frontier103CuntzLeptonQuarkUnruhKleinBridge
