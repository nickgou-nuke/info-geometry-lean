import Mathlib.Algebra.Ring.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Section 87: Nuclear Quasiphonon Krein-SUSY Intertwining & Soloviev Pairing Architecture

This module formalizes the exact algebraic bridge linking the nuclear many-body pairing sector
(Soloviev Quasiparticle-Phonon Nuclear Model / BCS pairing Hamiltonian) to the superconformal
$\mathfrak{osp}(1|2)$ Kantor Jordan pair architecture within an indefinite Krein space:

$$M_3(R) = \mathfrak{g}_{-2} \oplus \mathfrak{g}_{-1} \oplus \mathfrak{g}_0 \oplus \mathfrak{g}_1 \oplus \mathfrak{g}_2$$

### Key Architectural Results:
1. **Quasiphonon Ladder Operator Identification**:
   - Odd creation operators: $\alpha^\dagger = E_{01}$, $\beta^\dagger = E_{12}$ (Grade $+1$)
   - Odd annihilation operators: $\alpha = E_{10}$, $\beta = E_{21}$ (Grade $-1$)
   - Canonical anticommutation relations (CAR):
     $$\{\alpha, \alpha^\dagger\} = E_{11} + E_{00}, \qquad \{\beta, \beta^\dagger\} = E_{11} + E_{22}$$
2. **Soloviev Pairing Hamiltonian as an Inner Jordan Derivation**:
   - Inner derivation element:
     $$T_{\text{pair}} = [\alpha^\dagger, \alpha] - [\beta^\dagger, \beta] = E_{00} - 2E_{11} + E_{22} \in \mathfrak{g}_0$$
   - Commutation with the Cartan grading element $H = E_{00} - E_{22}$:
     $$[T_{\text{pair}}, H] = 0$$
   - Reconstruction of $H$ as the sum of spinor bilinears:
     $$H = [\alpha^\dagger, \alpha] + [\beta^\dagger, \beta]$$
3. **Krein Metric & Paracomplex Sheet-Swap Intertwining**:
   - Fundamental Krein metric $\eta = \operatorname{diag}(1, -1, 1)$, $\eta^2 = \mathbf{1}$
   - Paracomplex sheet-swap involution $J_{\text{sheet}}^2 = \mathbf{1}$
   - Andreev particle-hole reflection $\tau_1 = E_{02} + E_{20} = E + F$
   - Sheet-swap intertwining:
     $$J \tau_1 J = \tau_1, \qquad J H J = -H$$
4. **Krein Self-Adjointness**:
   An operator $A$ is $\eta$-self-adjoint if $A^\top \eta = \eta A$. Proved for:
   $$T_{\text{pair}}^\top \eta = \eta T_{\text{pair}}, \qquad H^\top \eta = \eta H, \qquad \tau_1^\top \eta = \eta \tau_1$$
   and consequently for the entire Soloviev pairing Hamiltonian:
   $$(H_{\text{pair}}(\varepsilon, \Delta))^\top \eta = \eta H_{\text{pair}}(\varepsilon, \Delta)$$
5. **Exact Bogoliubov-de Gennes Dispersion & Particle-Hole Intertwining**:
   $$(H_{\text{pair}}(\varepsilon, \Delta))^2 = (\varepsilon^2 + \Delta^2) H^2$$
   $$(H_{\text{pair}}(\varepsilon, \Delta))^3 = (\varepsilon^2 + \Delta^2) H_{\text{pair}}(\varepsilon, \Delta)$$
   $$J H_{\text{pair}}(\varepsilon, \Delta) J = H_{\text{pair}}(-\varepsilon, \Delta)$$
   $$\operatorname{STr}(H_{\text{pair}}(\varepsilon, \Delta)) = 0$$
6. **Master Compilation Theorem**:
   Rigorous verification of `compile_nuclear_quasiphonon_krein_susy` with 0 sorry, 0 admit, 0 custom axioms.
-/

namespace InfoGeometry.NuclearPhysics.NuclearQuasiphononKreinSUSY

open scoped Matrix BigOperators

variable {R : Type*} [CommRing R]

/-! ### Section 1: Canonical Matrix Basis and Operators in M₃(R) -/

/-- Elementary matrix units in $M_3(R)$. -/
def E (i j : Fin 3) : Matrix (Fin 3) (Fin 3) R :=
  Matrix.of fun r c => if r = i ∧ c = j then 1 else 0

/-- The Cartan grading element $H = E_{00} - E_{22} = \operatorname{diag}(1, 0, -1)$. -/
def H_gen (R : Type*) [CommRing R] : Matrix (Fin 3) (Fin 3) R :=
  E 0 0 - E 2 2

/-- Positive nilpotent generator $E = E_{02}$. -/
def E_gen (R : Type*) [CommRing R] : Matrix (Fin 3) (Fin 3) R :=
  E 0 2

/-- Negative nilpotent generator $F = E_{20}$. -/
def F_gen (R : Type*) [CommRing R] : Matrix (Fin 3) (Fin 3) R :=
  E 2 0

/-- Odd creation operator $\alpha^\dagger = E_{01}$ (Grade $+1$). -/
def alpha_dag (R : Type*) [CommRing R] : Matrix (Fin 3) (Fin 3) R := E 0 1

/-- Odd creation operator $\beta^\dagger = E_{12}$ (Grade $+1$). -/
def beta_dag (R : Type*) [CommRing R] : Matrix (Fin 3) (Fin 3) R := E 1 2

/-- Odd annihilation operator $\alpha = E_{10}$ (Grade $-1$). -/
def alpha (R : Type*) [CommRing R] : Matrix (Fin 3) (Fin 3) R := E 1 0

/-- Odd annihilation operator $\beta = E_{21}$ (Grade $-1$). -/
def beta (R : Type*) [CommRing R] : Matrix (Fin 3) (Fin 3) R := E 2 1

/-- Matrix Lie bracket (commutator): $[A, B] = AB - BA$. -/
def commutator (A B : Matrix (Fin 3) (Fin 3) R) : Matrix (Fin 3) (Fin 3) R :=
  A * B - B * A

/-- Matrix anticommutator: $\{A, B\} = AB + BA$. -/
def anticommutator (A B : Matrix (Fin 3) (Fin 3) R) : Matrix (Fin 3) (Fin 3) R :=
  A * B + B * A

/-- Graded supertrace on $M_3(R)$: $\operatorname{STr}(X) = X_{00} - X_{11} + X_{22}$. -/
def supertrace (X : Matrix (Fin 3) (Fin 3) R) : R :=
  X 0 0 - X 1 1 + X 2 2

/-! ### Section 2: Quasiphonon Ladder Operator Identification & CAR -/

/-- **Theorem**: Canonical anticommutation relation for $\alpha$:
    $\{\alpha, \alpha^\dagger\} = E_{11} + E_{00}$. -/
theorem car_alpha : anticommutator (alpha R) (alpha_dag R) = E 1 1 + E 0 0 := by
  unfold anticommutator alpha alpha_dag E
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.add_apply, Fin.sum_univ_three]

/-- **Theorem**: Canonical anticommutation relation for $\beta$:
    $\{\beta, \beta^\dagger\} = E_{11} + E_{22}$. -/
theorem car_beta : anticommutator (beta R) (beta_dag R) = E 1 1 + E 2 2 := by
  unfold anticommutator beta beta_dag E
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.add_apply, Fin.sum_univ_three]

/-! ### Section 3: Soloviev Pairing Hamiltonian as an Inner Derivation -/

/-- The Soloviev pairing inner derivation element:
    $T_{\text{pair}} = [\alpha^\dagger, \alpha] - [\beta^\dagger, \beta] \in \mathfrak{g}_0$. -/
def T_pair (R : Type*) [CommRing R] : Matrix (Fin 3) (Fin 3) R :=
  commutator (alpha_dag R) (alpha R) - commutator (beta_dag R) (beta R)

/-- **Theorem**: Explicit diagonal form of the pairing derivation:
    $T_{\text{pair}} = E_{00} - 2E_{11} + E_{22}$. -/
theorem T_pair_explicit :
    T_pair R = E 0 0 - 2 • (E 1 1) + E 2 2 := by
  unfold T_pair commutator alpha_dag alpha beta_dag beta E
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Fin.sum_univ_three] <;> ring

/-- **Theorem**: The pairing derivation commutes with the Cartan grading element:
    $[T_{\text{pair}}, H] = 0$. -/
theorem T_pair_comm_H :
    commutator (T_pair R) (H_gen R) = 0 := by
  rw [T_pair_explicit]
  unfold commutator H_gen E
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Fin.sum_univ_three] <;> ring

/-- **Theorem**: The Cartan element is the sum of the spinor bilinears:
    $H = [\alpha^\dagger, \alpha] + [\beta^\dagger, \beta]$. -/
theorem H_gen_as_sum :
    H_gen R = commutator (alpha_dag R) (alpha R) + commutator (beta_dag R) (beta R) := by
  unfold commutator alpha_dag alpha beta_dag beta H_gen E
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.add_apply, Matrix.sub_apply, Fin.sum_univ_three]

/-! ### Section 4: Krein Metric & Paracomplex Sheet-Swap Intertwining -/

/-- The fundamental Krein metric $\eta = \operatorname{diag}(1, -1, 1)$. -/
def eta_krein (R : Type*) [CommRing R] : Matrix (Fin 3) (Fin 3) R :=
  Matrix.of fun r c =>
    if r = c then
      if r = 0 ∨ r = 2 then 1 else -1
    else 0

/-- The paracomplex / Krein anti-diagonal sheet-swap involution $J_{\text{sheet}}$. -/
def J_sheet (R : Type*) [CommRing R] : Matrix (Fin 3) (Fin 3) R :=
  Matrix.of fun r c => if (r : ℕ) + (c : ℕ) = 2 then 1 else 0

/-- The Andreev particle-hole reflection generator $\tau_1 = E_{02} + E_{20} = E + F$. -/
def tau_1 (R : Type*) [CommRing R] : Matrix (Fin 3) (Fin 3) R :=
  E 0 2 + E 2 0

/-- **Theorem**: Involutive property of the sheet swap: $J_{\text{sheet}}^2 = \mathbf{1}$. -/
theorem J_sheet_sq : (J_sheet R) * (J_sheet R) = 1 := by
  unfold J_sheet
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three]

/-- **Theorem**: Involutive property of the Krein metric: $\eta^2 = \mathbf{1}$. -/
theorem eta_krein_sq : (eta_krein R) * (eta_krein R) = 1 := by
  unfold eta_krein
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three]

/-- **Theorem**: Andreev reflection is invariant under paracomplex sheet swap:
    $J_{\text{sheet}} \tau_1 J_{\text{sheet}} = \tau_1$. -/
theorem J_sheet_tau1_J_sheet :
    (J_sheet R) * (tau_1 R) * (J_sheet R) = tau_1 R := by
  unfold J_sheet tau_1 E
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.add_apply, Fin.sum_univ_three]

/-- **Theorem**: Cartan element inverts under paracomplex sheet swap:
    $J_{\text{sheet}} H J_{\text{sheet}} = -H$. -/
theorem J_sheet_inverts_H :
    (J_sheet R) * (H_gen R) * (J_sheet R) = - H_gen R := by
  unfold J_sheet H_gen E
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.neg_apply, Fin.sum_univ_three]

/-! ### Section 5: Krein Self-Adjointness -/

/-- **Theorem**: Krein self-adjointness of the pairing derivation:
    $T_{\text{pair}}^\top \eta = \eta T_{\text{pair}}$. -/
theorem T_pair_krein_self_adjoint :
    (T_pair R)ᵀ * (eta_krein R) = (eta_krein R) * (T_pair R) := by
  rw [T_pair_explicit]
  unfold eta_krein E
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.transpose_apply, Fin.sum_univ_three] <;> ring

/-- **Theorem**: Krein self-adjointness of the Cartan grading element:
    $H^\top \eta = \eta H$. -/
theorem H_gen_krein_self_adjoint :
    (H_gen R)ᵀ * (eta_krein R) = (eta_krein R) * (H_gen R) := by
  unfold H_gen eta_krein E
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.transpose_apply, Fin.sum_univ_three] <;> ring

/-- **Theorem**: Krein self-adjointness of the Andreev generator:
    $\tau_1^\top \eta = \eta \tau_1$. -/
theorem tau1_krein_self_adjoint :
    (tau_1 R)ᵀ * (eta_krein R) = (eta_krein R) * (tau_1 R) := by
  unfold tau_1 eta_krein E
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.add_apply, Matrix.transpose_apply, Fin.sum_univ_three]

/-! ### Section 6: Soloviev Pairing Hamiltonian & BdG Dispersion -/

/-- The Soloviev Quasispin Pairing Hamiltonian $H_{\text{pair}}(\varepsilon, \Delta) = \varepsilon H + \Delta \tau_1$. -/
def pairingHamiltonian (ε Δ : R) : Matrix (Fin 3) (Fin 3) R :=
  ε • (H_gen R) + Δ • (tau_1 R)

/-- **Theorem**: The entire Soloviev pairing Hamiltonian is Krein self-adjoint:
    $(H_{\text{pair}}(\varepsilon, \Delta))^\top \eta = \eta H_{\text{pair}}(\varepsilon, \Delta)$. -/
theorem pairing_krein_self_adjoint (ε Δ : R) :
    (pairingHamiltonian ε Δ)ᵀ * (eta_krein R) = (eta_krein R) * (pairingHamiltonian ε Δ) := by
  unfold pairingHamiltonian
  simp only [Matrix.transpose_add, Matrix.transpose_smul, Matrix.add_mul, Matrix.smul_mul,
             Matrix.mul_add, Matrix.mul_smul]
  rw [H_gen_krein_self_adjoint, tau1_krein_self_adjoint]

/-- **Theorem**: Paracomplex sheet-swap intertwining inverts single-particle energy:
    $J_{\text{sheet}} H_{\text{pair}}(\varepsilon, \Delta) J_{\text{sheet}} = H_{\text{pair}}(-\varepsilon, \Delta)$. -/
theorem pairing_sheet_swap_intertwine (ε Δ : R) :
    (J_sheet R) * (pairingHamiltonian ε Δ) * (J_sheet R) = pairingHamiltonian (-ε) Δ := by
  unfold pairingHamiltonian
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]
  rw [J_sheet_inverts_H, J_sheet_tau1_J_sheet]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.add_apply, Matrix.smul_apply, Matrix.neg_apply] <;> ring

/-- **Theorem**: Exact Bogoliubov-de Gennes dispersion squaring identity:
    $(H_{\text{pair}}(\varepsilon, \Delta))^2 = (\varepsilon^2 + \Delta^2) H^2$. -/
theorem pairing_hamiltonian_sq (ε Δ : R) :
    (pairingHamiltonian ε Δ) * (pairingHamiltonian ε Δ) =
      (ε ^ 2 + Δ ^ 2) • ((H_gen R) * (H_gen R)) := by
  unfold pairingHamiltonian H_gen tau_1 E
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Fin.sum_univ_three] <;> ring

/-- **Theorem**: Cubic minimal polynomial / quasiparticle characteristic equation:
    $(H_{\text{pair}}(\varepsilon, \Delta))^3 = (\varepsilon^2 + \Delta^2) H_{\text{pair}}(\varepsilon, \Delta)$. -/
theorem pairing_hamiltonian_cube (ε Δ : R) :
    (pairingHamiltonian ε Δ) * (pairingHamiltonian ε Δ) * (pairingHamiltonian ε Δ) =
      (ε ^ 2 + Δ ^ 2) • (pairingHamiltonian ε Δ) := by
  unfold pairingHamiltonian H_gen tau_1 E
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Fin.sum_univ_three] <;> ring

/-- **Theorem**: Vanishing supertrace of the Soloviev pairing Hamiltonian:
    $\operatorname{STr}(H_{\text{pair}}(\varepsilon, \Delta)) = 0$. -/
theorem pairing_supertrace (ε Δ : R) :
    supertrace (pairingHamiltonian ε Δ) = 0 := by
  dsimp [supertrace, pairingHamiltonian, H_gen, tau_1, E]
  simp

/-! ### Section 7: Master Certification & Conjunction Targets -/

/-- Master certificate structure packaging the full set of Nuclear Quasiphonon Krein SUSY theorems. -/
structure NuclearQuasiphononKreinSUSYCertificate : Prop where
  car_alpha_comm          : anticommutator (alpha R) (alpha_dag R) = E 1 1 + E 0 0
  car_beta_comm           : anticommutator (beta R) (beta_dag R) = E 1 1 + E 2 2
  T_pair_explicit_form    : T_pair R = E 0 0 - 2 • (E 1 1) + E 2 2
  T_pair_commutes_H       : commutator (T_pair R) (H_gen R) = 0
  H_as_bilinear_sum       : H_gen R = commutator (alpha_dag R) (alpha R) + commutator (beta_dag R) (beta R)
  J_is_involutive         : (J_sheet R) * (J_sheet R) = 1
  eta_is_involutive       : (eta_krein R) * (eta_krein R) = 1
  tau1_sheet_invariant    : (J_sheet R) * (tau_1 R) * (J_sheet R) = tau_1 R
  T_pair_krein_sa         : (T_pair R)ᵀ * (eta_krein R) = (eta_krein R) * (T_pair R)
  H_gen_krein_sa          : (H_gen R)ᵀ * (eta_krein R) = (eta_krein R) * (H_gen R)
  tau1_krein_sa           : (tau_1 R)ᵀ * (eta_krein R) = (eta_krein R) * (tau_1 R)
  pairing_krein_sa        : ∀ ε Δ : R, (pairingHamiltonian ε Δ)ᵀ * (eta_krein R) =
                              (eta_krein R) * (pairingHamiltonian ε Δ)
  pairing_intertwine      : ∀ ε Δ : R, (J_sheet R) * (pairingHamiltonian ε Δ) * (J_sheet R) =
                              pairingHamiltonian (-ε) Δ
  pairing_sq              : ∀ ε Δ : R, (pairingHamiltonian ε Δ) * (pairingHamiltonian ε Δ) =
                              (ε ^ 2 + Δ ^ 2) • ((H_gen R) * (H_gen R))
  pairing_cube            : ∀ ε Δ : R, (pairingHamiltonian ε Δ) * (pairingHamiltonian ε Δ) * (pairingHamiltonian ε Δ) =
                              (ε ^ 2 + Δ ^ 2) • (pairingHamiltonian ε Δ)
  pairing_str_zero        : ∀ ε Δ : R, supertrace (pairingHamiltonian ε Δ) = 0

/-- Master certificate instantiation. -/
theorem compile_nuclear_quasiphonon_krein_susy_cert :
    NuclearQuasiphononKreinSUSYCertificate (R := R) where
  car_alpha_comm          := car_alpha
  car_beta_comm           := car_beta
  T_pair_explicit_form    := T_pair_explicit
  T_pair_commutes_H       := T_pair_comm_H
  H_as_bilinear_sum       := H_gen_as_sum
  J_is_involutive         := J_sheet_sq
  eta_is_involutive       := eta_krein_sq
  tau1_sheet_invariant    := J_sheet_tau1_J_sheet
  T_pair_krein_sa         := T_pair_krein_self_adjoint
  H_gen_krein_sa          := H_gen_krein_self_adjoint
  tau1_krein_sa           := tau1_krein_self_adjoint
  pairing_krein_sa        := pairing_krein_self_adjoint
  pairing_intertwine      := pairing_sheet_swap_intertwine
  pairing_sq              := pairing_hamiltonian_sq
  pairing_cube            := pairing_hamiltonian_cube
  pairing_str_zero        := pairing_supertrace

/-- **Master Gate Target**: The exact 5-clause conjunction specified in the Operational Directive:
    `[T_pair, H] = 0 ∧ J² = 1 ∧ J τ₁ J = τ₁ ∧ T_pairᵀ η = η T_pair ∧ Hᵀ η = η H`. -/
theorem compile_nuclear_quasiphonon_krein_susy :
    (commutator (T_pair R) (H_gen R) = 0) ∧
    ((J_sheet R) * (J_sheet R) = 1) ∧
    ((J_sheet R) * (tau_1 R) * (J_sheet R) = tau_1 R) ∧
    ((T_pair R)ᵀ * (eta_krein R) = (eta_krein R) * (T_pair R)) ∧
    ((H_gen R)ᵀ * (eta_krein R) = (eta_krein R) * (H_gen R)) :=
  ⟨T_pair_comm_H, J_sheet_sq, J_sheet_tau1_J_sheet, T_pair_krein_self_adjoint, H_gen_krein_self_adjoint⟩

end InfoGeometry.NuclearPhysics.NuclearQuasiphononKreinSUSY
