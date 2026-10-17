/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Clifford.Cl11Matrix
import InfoGeometry.Clifford.Cl11TensorTower
import InfoGeometry.Clifford.Cl11JordanWignerCARBridge
import InfoGeometry.Canonical.Cl11TensorTowerLocalParity
import InfoGeometry.Canonical.Cl11TensorTowerGlobalParity
import InfoGeometry.Canonical.Cl11TensorTowerCrossSiteCAR
import InfoGeometry.Canonical.MajoranaEightByEightJW
import InfoGeometry.Canonical.MajoranaUHFJordanWignerInduction
import InfoGeometry.Canonical.SplitOctonionParaKahlerNullCone
import InfoGeometry.Canonical.SplitOctonionClifford33Soldering
import InfoGeometry.Canonical.SplitOctonionJordanWignerIntertwiner
import InfoGeometry.Synthesis.ThreeTraditionLineageConvergence

/-!
# Krein–$\operatorname{Cl}(1,1)$ Nilpotent-Kernel and Möbius-Quotient Synthesis

This module unifies the atomic $\operatorname{Cl}(1,1)$ matrix model, the inductive
$\operatorname{Cl}(1,1)^{\otimes n}$ Jordan–Wigner CAR tensor tower, the Krein
para-complex sheet projectors and off-diagonal quadratic pairing on
`ModularCPT.DoubledCarrier E`, the unoriented Möbius $\mathbb{Z}_2$ quotient
identifying primal and dual covector sheets, and finite $8 \times 8$ Zorn/Jordan–Wigner
matrix identities. The quotient is by the explicit Möbius twist, and the final
diagonal matrix is the vacuum-minus-top Peirce operator; neither is identified
here with a quotient by, or the full chiral-volume operator of, $\operatorname{Cl}(3,3)$.

## Main Results

1. **Section 1 ($\operatorname{Cl}(1,1)$ Atomic $2 \times 2$ Cell)**:
   - `cl11NilpotentPlus`, `cl11NilpotentMinus`, `cl11ChiralVolume`,
     `cl11VacProj`, and `cl11OccProj`.
   - Nilpotency (`cl11NilpotentPlus_sq_zero`, `cl11NilpotentMinus_sq_zero`),
     CAR anticommutator (`cl11Nilpotent_anticommutator_eq_one`),
     non-commutativity witness (`cl11NilpotentPlus_mul_cl11NilpotentMinus_ne_comm`),
     chiral volume anticommutation and involution (`cl11ChiralVolume_sq_eq_one`,
     `cl11ChiralVolume_anticomm_nilpotentPlus`,
     `cl11ChiralVolume_anticomm_nilpotentMinus`), and idempotent spectral/kernel
     absorptions (`cl11VacProj_add_cl11OccProj_eq_one`,
     `cl11VacProj_sub_cl11OccProj_eq_neg_chiralVolume`,
     `cl11NilpotentPlus_mul_cl11VacProj_zero`,
     `cl11NilpotentMinus_mul_cl11OccProj_zero`).
2. **Section 2 ($\operatorname{Cl}(1,1)^{\otimes n}$ Tensor Tower of Null Nilpotents)**:
   - Stage-uniform nilpotency (`jwCreation_sq_zero_all`, `jwAnnihilation_sq_zero_all`),
     uniform same-type anticommutativity (`jwCreation_anticomm_all`,
     `jwAnnihilation_anticomm_all`), and chiral parity conjugation negating every
     Jordan–Wigner ladder operator (`globalChirality_conj_jwCreation`,
     `globalChirality_conj_jwAnnihilation`).
3. **Section 3 (Krein Indefinite Metric & Para-Complex Kernel Sheets)**:
   - Isotropic vanishing on the spectral projectors and eigen-submodules
     (`kreinForm_paraProjectorPlus_self_zero`,
     `kreinForm_paraProjectorMinus_self_zero`,
     `kreinForm_self_eq_zero_of_mem_primalSheet`,
     `kreinForm_self_eq_zero_of_mem_covectorVacuumSheet`), and off-diagonal
     cross-sheet quadratic evaluation (`kreinForm_eq_offDiagonal_sheet_pairing_sum`,
     `kreinForm_eq_two_mul_offDiagonal_sheet_pairing`).
4. **Section 4 (Unoriented Möbius $\mathbb{Z}_2$ Quotient)**:
   - `mobiusOrbitRel`, `chiralMobiusSetoid`, `UnorientedMobiusQuotient`,
     well-definedness of `quotientKreinQuadratic`, and the sheet identification
     `primal_eq_covectorVacuum_in_unorientedMobiusQuotient`.
5. **Section 5 (Finite Zorn/Jordan–Wigner Vacuum–Top Matrix Identities)**:
   - Explicit action of `zornJWConjugator` swapping the vacuum and top Fock lines
     while fixing the $3 \oplus 3$ primal and dual vector sheets, the half-sum
     realization `zornVacuumTopPeirceOperator_eq_half_left_add_right`, and its
     sign reversal `zornJWConjugator_negates_zornVacuumTopPeirceOperator`.

## Scope Note

This file proves finite-dimensional and inductive matrix-stage algebraic identities,
linear-algebraic Krein sheet decompositions, and the setoid quotient on
`ModularCPT.DoubledCarrier E`. It does not claim analytic continuum limits or
infinite-dimensional operator-norm convergence beyond the inductive algebraic tower.
-/

set_option autoImplicit false

namespace InfoGeometry.Synthesis.Cl11ChiralVolumeNilpotentQuotientSynthesis

open scoped Matrix Kronecker
open Matrix
open InfoGeometry.Clifford
open InfoGeometry.Canonical
open InfoGeometry.SuperGrassmannian

/-!
## Section 1: The $\operatorname{Cl}(1,1)$ Atomic $2 \times 2$ Cell
-/

/-- The upper-triangular Witt creation nilpotent
$n_+ = \tfrac{1}{2}(e_1 + e_2) = \begin{pmatrix} 0 & 1 \\ 0 & 0 \end{pmatrix}$
in the atomic $\operatorname{Cl}(1,1)$ cell. -/
noncomputable def cl11NilpotentPlus : Matrix (Fin 2) (Fin 2) ℝ :=
  (1 / 2 : ℝ) • (Cl11Matrix.J1 + Cl11Matrix.Eminus)

/-- The lower-triangular Witt annihilation nilpotent
$n_- = \tfrac{1}{2}(e_1 - e_2) = \begin{pmatrix} 0 & 0 \\ 1 & 0 \end{pmatrix}$
in the atomic $\operatorname{Cl}(1,1)$ cell. -/
noncomputable def cl11NilpotentMinus : Matrix (Fin 2) (Fin 2) ℝ :=
  (1 / 2 : ℝ) • (Cl11Matrix.J1 - Cl11Matrix.Eminus)

/-- The chiral volume grading matrix
$\omega = e_1 e_2 = \begin{pmatrix} -1 & 0 \\ 0 & 1 \end{pmatrix} = -\operatorname{Eplus}$
in the atomic $\operatorname{Cl}(1,1)$ cell. -/
def cl11ChiralVolume : Matrix (Fin 2) (Fin 2) ℝ :=
  Cl11Matrix.J1 * Cl11Matrix.Eminus

/-- The top/vacuum rank-1 idempotent projector $P_+ = n_+ n_- = \begin{pmatrix} 1 & 0 \\ 0 & 0 \end{pmatrix}$. -/
noncomputable def cl11VacProj : Matrix (Fin 2) (Fin 2) ℝ :=
  cl11NilpotentPlus * cl11NilpotentMinus

/-- The bottom/occupied rank-1 idempotent projector $P_- = n_- n_+ = \begin{pmatrix} 0 & 0 \\ 0 & 1 \end{pmatrix}$. -/
noncomputable def cl11OccProj : Matrix (Fin 2) (Fin 2) ℝ :=
  cl11NilpotentMinus * cl11NilpotentPlus

/-- `cl11NilpotentPlus` agrees with `Cl11TensorTower.wittCreationBase`. -/
theorem cl11NilpotentPlus_eq_wittCreationBase :
    cl11NilpotentPlus = Cl11TensorTower.wittCreationBase := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [cl11NilpotentPlus, Cl11TensorTower.wittCreationBase,
      Cl11Matrix.J1, Cl11Matrix.Eminus]

/-- `cl11NilpotentMinus` agrees with `Cl11TensorTower.wittAnnihilationBase`. -/
theorem cl11NilpotentMinus_eq_wittAnnihilationBase :
    cl11NilpotentMinus = Cl11TensorTower.wittAnnihilationBase := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [cl11NilpotentMinus, Cl11TensorTower.wittAnnihilationBase,
      Cl11Matrix.J1, Cl11Matrix.Eminus]

/-- `cl11ChiralVolume` agrees with `Cl11TensorTower.gamma_chiral_base = -Cl11Matrix.Eplus`. -/
theorem cl11ChiralVolume_eq_gamma_chiral_base :
    cl11ChiralVolume = Cl11TensorTower.gamma_chiral_base := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [cl11ChiralVolume, Cl11TensorTower.gamma_chiral_base,
      Cl11TensorTower.gamma_0_base, Cl11TensorTower.gamma_1_base,
      Cl11Matrix.J1, Cl11Matrix.Eminus, Matrix.mul_apply, Fin.sum_univ_two]

/-- The Witt creation operator $n_+$ is nilpotent of order 2: $n_+^2 = 0$. -/
theorem cl11NilpotentPlus_sq_zero :
    cl11NilpotentPlus * cl11NilpotentPlus = 0 := by
  rw [cl11NilpotentPlus_eq_wittCreationBase]
  exact Cl11TensorTower.wittCreationBase_sq

/-- The Witt annihilation operator $n_-$ is nilpotent of order 2: $n_-^2 = 0$. -/
theorem cl11NilpotentMinus_sq_zero :
    cl11NilpotentMinus * cl11NilpotentMinus = 0 := by
  rw [cl11NilpotentMinus_eq_wittAnnihilationBase]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Cl11TensorTower.wittAnnihilationBase, Matrix.mul_apply, Fin.sum_univ_two]

/-- Canonical CAR anticommutator in the atomic $\operatorname{Cl}(1,1)$ cell:
$n_+ n_- + n_- n_+ = I_2$. -/
theorem cl11Nilpotent_anticommutator_eq_one :
    cl11NilpotentPlus * cl11NilpotentMinus +
      cl11NilpotentMinus * cl11NilpotentPlus = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [cl11NilpotentPlus, cl11NilpotentMinus,
      Cl11Matrix.J1, Cl11Matrix.Eminus, Matrix.mul_apply, Fin.sum_univ_two]

/-- Non-commutativity witness for the atomic Witt nilpotents:
$n_+ n_- \neq n_- n_+$. -/
theorem cl11NilpotentPlus_mul_cl11NilpotentMinus_ne_comm :
    cl11NilpotentPlus * cl11NilpotentMinus ≠
      cl11NilpotentMinus * cl11NilpotentPlus := by
  intro h_comm
  have h00 :
      (cl11NilpotentPlus * cl11NilpotentMinus) 0 0 =
        (cl11NilpotentMinus * cl11NilpotentPlus) 0 0 :=
    congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 0) h_comm
  revert h00
  norm_num [cl11NilpotentPlus, cl11NilpotentMinus,
    Cl11Matrix.J1, Cl11Matrix.Eminus, Matrix.mul_apply, Fin.sum_univ_two]

/-- The chiral volume operator $\omega = e_1 e_2$ is a grading involution: $\omega^2 = I_2$. -/
theorem cl11ChiralVolume_sq_eq_one :
    cl11ChiralVolume * cl11ChiralVolume = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [cl11ChiralVolume, Cl11Matrix.J1, Cl11Matrix.Eminus,
      Matrix.mul_apply, Fin.sum_univ_two]

/-- The chiral volume operator $\omega$ anticommutes with $n_+$:
$\omega n_+ + n_+ \omega = 0$. -/
theorem cl11ChiralVolume_anticomm_nilpotentPlus :
    cl11ChiralVolume * cl11NilpotentPlus +
      cl11NilpotentPlus * cl11ChiralVolume = 0 := by
  rw [cl11ChiralVolume_eq_gamma_chiral_base, cl11NilpotentPlus_eq_wittCreationBase]
  exact Cl11TensorTowerLocalParity.gamma_chiral_base_anticomm_wittCreation

/-- The chiral volume operator $\omega$ anticommutes with $n_-$:
$\omega n_- + n_- \omega = 0$. -/
theorem cl11ChiralVolume_anticomm_nilpotentMinus :
    cl11ChiralVolume * cl11NilpotentMinus +
      cl11NilpotentMinus * cl11ChiralVolume = 0 := by
  rw [cl11ChiralVolume_eq_gamma_chiral_base, cl11NilpotentMinus_eq_wittAnnihilationBase]
  exact Cl11TensorTowerLocalParity.gamma_chiral_base_anticomm_wittAnnihilation

/-- The vacuum projector $P_+ = n_+ n_-$ is idempotent: $P_+^2 = P_+$. -/
theorem cl11VacProj_sq :
    cl11VacProj * cl11VacProj = cl11VacProj := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [cl11VacProj, cl11NilpotentPlus, cl11NilpotentMinus,
      Cl11Matrix.J1, Cl11Matrix.Eminus, Matrix.mul_apply, Fin.sum_univ_two]

/-- The occupied projector $P_- = n_- n_+$ is idempotent: $P_-^2 = P_-$. -/
theorem cl11OccProj_sq :
    cl11OccProj * cl11OccProj = cl11OccProj := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [cl11OccProj, cl11NilpotentPlus, cl11NilpotentMinus,
      Cl11Matrix.J1, Cl11Matrix.Eminus, Matrix.mul_apply, Fin.sum_univ_two]

/-- Orthogonality of the complementary projectors: $P_+ P_- = 0$. -/
theorem cl11VacProj_mul_cl11OccProj_zero :
    cl11VacProj * cl11OccProj = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [cl11VacProj, cl11OccProj, cl11NilpotentPlus, cl11NilpotentMinus,
      Cl11Matrix.J1, Cl11Matrix.Eminus, Matrix.mul_apply, Fin.sum_univ_two]

/-- Orthogonality of the complementary projectors in reverse order: $P_- P_+ = 0$. -/
theorem cl11OccProj_mul_cl11VacProj_zero :
    cl11OccProj * cl11VacProj = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [cl11VacProj, cl11OccProj, cl11NilpotentPlus, cl11NilpotentMinus,
      Cl11Matrix.J1, Cl11Matrix.Eminus, Matrix.mul_apply, Fin.sum_univ_two]

/-- Resolution of the identity into vacuum and occupied projectors: $P_+ + P_- = I_2$. -/
theorem cl11VacProj_add_cl11OccProj_eq_one :
    cl11VacProj + cl11OccProj = 1 :=
  cl11Nilpotent_anticommutator_eq_one

/-- Spectral decomposition of the chiral volume grading:
$P_+ - P_- = -\omega = \operatorname{Eplus}$. -/
theorem cl11VacProj_sub_cl11OccProj_eq_neg_chiralVolume :
    cl11VacProj - cl11OccProj = -cl11ChiralVolume := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [cl11VacProj, cl11OccProj, cl11ChiralVolume,
      cl11NilpotentPlus, cl11NilpotentMinus,
      Cl11Matrix.J1, Cl11Matrix.Eminus, Matrix.mul_apply, Fin.sum_univ_two]

/-- Kernel absorption on the top/vacuum projector: $n_+ P_+ = 0$. -/
theorem cl11NilpotentPlus_mul_cl11VacProj_zero :
    cl11NilpotentPlus * cl11VacProj = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [cl11VacProj, cl11NilpotentPlus, cl11NilpotentMinus,
      Cl11Matrix.J1, Cl11Matrix.Eminus, Matrix.mul_apply, Fin.sum_univ_two]

/-- Kernel absorption on the bottom/occupied projector: $n_- P_- = 0$. -/
theorem cl11NilpotentMinus_mul_cl11OccProj_zero :
    cl11NilpotentMinus * cl11OccProj = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [cl11OccProj, cl11NilpotentPlus, cl11NilpotentMinus,
      Cl11Matrix.J1, Cl11Matrix.Eminus, Matrix.mul_apply, Fin.sum_univ_two]

/-!
## Section 2: The $\operatorname{Cl}(1,1)^{\otimes n}$ Tensor Tower of Null Nilpotents
-/

/-- Every Jordan–Wigner creation operator in the $\operatorname{Cl}(1,1)^{\otimes n}$
tensor tower is strictly nilpotent of order 2: $a_k^{\dagger 2} = 0$. -/
theorem jwCreation_sq_zero_all :
    ∀ (n : ℕ) (k : Fin n),
      Cl11TensorTower.jwCreation n k * Cl11TensorTower.jwCreation n k = 0
  | 0, k => Fin.elim0 k
  | n + 1, k => by
      by_cases h : (k : ℕ) < n
      · let k' : Fin n := ⟨k, h⟩
        have ih := jwCreation_sq_zero_all n k'
        simp [Cl11TensorTower.jwCreation, Cl11TensorTower.jwStringWithBase, h]
        change
          ((Cl11TensorTower.jwStringWithBase Cl11TensorTower.wittCreationBase n k') ⊗ₖ
              (1 : Matrix (Fin 2) (Fin 2) ℝ)) *
            ((Cl11TensorTower.jwStringWithBase Cl11TensorTower.wittCreationBase n k') ⊗ₖ
              (1 : Matrix (Fin 2) (Fin 2) ℝ)) = 0
        rw [← Matrix.mul_kronecker_mul]
        simpa [Cl11TensorTower.jwCreation] using
          congrArg (fun A : Cl11TensorTower.MatStage n =>
            A ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℝ)) ih
      · have hk : k = Fin.last n := Fin.eq_last_of_not_lt h
        subst k
        have hlast : (Fin.last n : Fin (n + 1)) = ⟨n, Nat.lt_succ_self n⟩ := rfl
        simpa [hlast] using Cl11JordanWignerCARBridge.jwCreation_last_sq n

/-- Every Jordan–Wigner annihilation operator in the $\operatorname{Cl}(1,1)^{\otimes n}$
tensor tower is strictly nilpotent of order 2: $a_k^2 = 0$. -/
theorem jwAnnihilation_sq_zero_all :
    ∀ (n : ℕ) (k : Fin n),
      Cl11TensorTower.jwAnnihilation n k * Cl11TensorTower.jwAnnihilation n k = 0
  | 0, k => Fin.elim0 k
  | n + 1, k => by
      by_cases h : (k : ℕ) < n
      · let k' : Fin n := ⟨k, h⟩
        have ih := jwAnnihilation_sq_zero_all n k'
        simp [Cl11TensorTower.jwAnnihilation, Cl11TensorTower.jwStringWithBase, h]
        change
          ((Cl11TensorTower.jwStringWithBase Cl11TensorTower.wittAnnihilationBase n k') ⊗ₖ
              (1 : Matrix (Fin 2) (Fin 2) ℝ)) *
            ((Cl11TensorTower.jwStringWithBase Cl11TensorTower.wittAnnihilationBase n k') ⊗ₖ
              (1 : Matrix (Fin 2) (Fin 2) ℝ)) = 0
        rw [← Matrix.mul_kronecker_mul]
        simpa [Cl11TensorTower.jwAnnihilation] using
          congrArg (fun A : Cl11TensorTower.MatStage n =>
            A ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℝ)) ih
      · have hk : k = Fin.last n := Fin.eq_last_of_not_lt h
        subst k
        have hlast : (Fin.last n : Fin (n + 1)) = ⟨n, Nat.lt_succ_self n⟩ := rfl
        simpa [hlast] using Cl11JordanWignerCARBridge.jwAnnihilation_last_sq n

/-- Uniform creation-creation anticommutativity $\{a_i^\dagger, a_j^\dagger\} = 0$
for all $i, j \in \operatorname{Fin} n$ (both same-site and cross-site). -/
theorem jwCreation_anticomm_all (n : ℕ) (i j : Fin n) :
    Cl11TensorTower.jwCreation n i * Cl11TensorTower.jwCreation n j +
      Cl11TensorTower.jwCreation n j * Cl11TensorTower.jwCreation n i = 0 := by
  by_cases hij : i = j
  · subst hij
    rw [jwCreation_sq_zero_all n i, add_zero]
  · exact Cl11TensorTowerCrossSiteCAR.creation_cross_site_anticommute n i j hij

/-- Uniform annihilation-annihilation anticommutativity $\{a_i, a_j\} = 0$
for all $i, j \in \operatorname{Fin} n$ (both same-site and cross-site). -/
theorem jwAnnihilation_anticomm_all (n : ℕ) (i j : Fin n) :
    Cl11TensorTower.jwAnnihilation n i * Cl11TensorTower.jwAnnihilation n j +
      Cl11TensorTower.jwAnnihilation n j * Cl11TensorTower.jwAnnihilation n i = 0 := by
  by_cases hij : i = j
  · subst hij
    rw [jwAnnihilation_sq_zero_all n i, add_zero]
  · exact Cl11TensorTowerCrossSiteCAR.annihilation_cross_site_anticommute n i j hij

/-- Conjugating any Jordan–Wigner creation operator $a_k^\dagger$ by the involutive
global chiral volume operator $\Gamma_n = \gamma_{\mathrm{chiral}}^{\otimes n}$ negates it:
$\Gamma_n a_k^\dagger \Gamma_n = -a_k^\dagger$. -/
theorem globalChirality_conj_jwCreation (n : ℕ) (k : Fin n) :
    Cl11TensorTower.globalChirality n *
      Cl11TensorTower.jwCreation n k *
      Cl11TensorTower.globalChirality n =
        -Cl11TensorTower.jwCreation n k := by
  have h_anti :
      Cl11TensorTower.globalChirality n * Cl11TensorTower.jwCreation n k =
        -(Cl11TensorTower.jwCreation n k * Cl11TensorTower.globalChirality n) :=
    eq_neg_of_add_eq_zero_left
      (Cl11TensorTowerGlobalParity.globalChirality_anticomm_jwCreation n k)
  calc
    Cl11TensorTower.globalChirality n *
        Cl11TensorTower.jwCreation n k *
        Cl11TensorTower.globalChirality n =
      -(Cl11TensorTower.jwCreation n k *
          (Cl11TensorTower.globalChirality n * Cl11TensorTower.globalChirality n)) := by
      rw [h_anti, neg_mul, Matrix.mul_assoc]
    _ = -Cl11TensorTower.jwCreation n k := by
      rw [InfoGeometry.Clifford.JordanWignerCAR.globalChirality_sq n, Matrix.mul_one]

/-- Conjugating any Jordan–Wigner annihilation operator $a_k$ by the involutive
global chiral volume operator $\Gamma_n = \gamma_{\mathrm{chiral}}^{\otimes n}$ negates it:
$\Gamma_n a_k \Gamma_n = -a_k$. -/
theorem globalChirality_conj_jwAnnihilation (n : ℕ) (k : Fin n) :
    Cl11TensorTower.globalChirality n *
      Cl11TensorTower.jwAnnihilation n k *
      Cl11TensorTower.globalChirality n =
        -Cl11TensorTower.jwAnnihilation n k := by
  have h_anti :
      Cl11TensorTower.globalChirality n * Cl11TensorTower.jwAnnihilation n k =
        -(Cl11TensorTower.jwAnnihilation n k * Cl11TensorTower.globalChirality n) :=
    eq_neg_of_add_eq_zero_left
      (Cl11TensorTowerGlobalParity.globalChirality_anticomm_jwAnnihilation n k)
  calc
    Cl11TensorTower.globalChirality n *
        Cl11TensorTower.jwAnnihilation n k *
        Cl11TensorTower.globalChirality n =
      -(Cl11TensorTower.jwAnnihilation n k *
          (Cl11TensorTower.globalChirality n * Cl11TensorTower.globalChirality n)) := by
      rw [h_anti, neg_mul, Matrix.mul_assoc]
    _ = -Cl11TensorTower.jwAnnihilation n k := by
      rw [InfoGeometry.Clifford.JordanWignerCAR.globalChirality_sq n, Matrix.mul_one]

/-!
## Section 3: Krein Indefinite Metric & Para-Complex Kernel Sheets
-/

section KreinSheets

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- Every vector projected onto the $+1$ primal sheet via `paraProjectorPlus K_op`
is strictly null (isotropic) with respect to the Krein bilinear form. -/
theorem kreinForm_paraProjectorPlus_self_zero
    (pairing : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (z : ModularCPT.DoubledCarrier E) :
    ModularCPT.kreinForm pairing
      (SuperGrassmannian.paraProjectorPlus (ModularCPT.K_op (E := E)) z)
      (SuperGrassmannian.paraProjectorPlus (ModularCPT.K_op (E := E)) z) = 0 := by
  rw [ThreeTraditionLineageConvergence.paraProjectorPlus_K_op_apply]
  simp [ModularCPT.kreinForm]

/-- Every vector projected onto the $-1$ covector vacuum sheet via `paraProjectorMinus K_op`
is strictly null (isotropic) with respect to the Krein bilinear form. -/
theorem kreinForm_paraProjectorMinus_self_zero
    (pairing : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (z : ModularCPT.DoubledCarrier E) :
    ModularCPT.kreinForm pairing
      (SuperGrassmannian.paraProjectorMinus (ModularCPT.K_op (E := E)) z)
      (SuperGrassmannian.paraProjectorMinus (ModularCPT.K_op (E := E)) z) = 0 := by
  rw [ThreeTraditionLineageConvergence.paraProjectorMinus_K_op_apply]
  simp [ModularCPT.kreinForm]

/-- Every state `z` belonging to the $+1$ primal eigen-sheet
`SuperGrassmannian.primalSheet (ModularCPT.K_op)` is isotropic under the Krein quadratic form:
`kreinForm pairing z z = 0`. -/
theorem kreinForm_self_eq_zero_of_mem_primalSheet
    (pairing : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (z : ModularCPT.DoubledCarrier E)
    (hz : z ∈ SuperGrassmannian.primalSheet (ModularCPT.K_op (E := E))) :
    ModularCPT.kreinForm pairing z z = 0 := by
  have hz_proj :
      SuperGrassmannian.paraProjectorPlus (ModularCPT.K_op (E := E)) z = z :=
    (SuperGrassmannian.mem_primalSheet_iff
      (ModularCPT.K_op (E := E)) ModularCPT.K_involutive z).mp hz
  rw [← hz_proj]
  exact kreinForm_paraProjectorPlus_self_zero pairing z

/-- Every state `z` belonging to the $-1$ covector vacuum eigen-sheet
`SuperGrassmannian.covectorVacuumSheet (ModularCPT.K_op)` is isotropic under the Krein
quadratic form: `kreinForm pairing z z = 0`. -/
theorem kreinForm_self_eq_zero_of_mem_covectorVacuumSheet
    (pairing : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (z : ModularCPT.DoubledCarrier E)
    (hz : z ∈ SuperGrassmannian.covectorVacuumSheet (ModularCPT.K_op (E := E))) :
    ModularCPT.kreinForm pairing z z = 0 := by
  have hz_proj :
      SuperGrassmannian.paraProjectorMinus (ModularCPT.K_op (E := E)) z = z :=
    (SuperGrassmannian.mem_covectorVacuumSheet_iff
      (ModularCPT.K_op (E := E)) ModularCPT.K_involutive z).mp hz
  rw [← hz_proj]
  exact kreinForm_paraProjectorMinus_self_zero pairing z

/-- Because both the $+1$ primal sheet and the $-1$ covector vacuum sheet are isotropic,
the Krein quadratic form `kreinForm pairing z z` reduces entirely to the sum of the two
off-diagonal cross-sheet pairings between `paraProjectorPlus K_op z` and
`paraProjectorMinus K_op z`. -/
theorem kreinForm_eq_offDiagonal_sheet_pairing_sum
    (pairing : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (z : ModularCPT.DoubledCarrier E) :
    ModularCPT.kreinForm pairing z z =
      ModularCPT.kreinForm pairing
        (SuperGrassmannian.paraProjectorPlus (ModularCPT.K_op (E := E)) z)
        (SuperGrassmannian.paraProjectorMinus (ModularCPT.K_op (E := E)) z) +
      ModularCPT.kreinForm pairing
        (SuperGrassmannian.paraProjectorMinus (ModularCPT.K_op (E := E)) z)
        (SuperGrassmannian.paraProjectorPlus (ModularCPT.K_op (E := E)) z) := by
  rw [ThreeTraditionLineageConvergence.paraProjectorPlus_K_op_apply,
    ThreeTraditionLineageConvergence.paraProjectorMinus_K_op_apply]
  simp [ModularCPT.kreinForm]

/-- For a symmetric bilinear pairing on $E$, the Krein quadratic form on
`ModularCPT.DoubledCarrier E` equals twice the single off-diagonal cross-sheet pairing
between `paraProjectorPlus K_op z` and `paraProjectorMinus K_op z`. -/
theorem kreinForm_eq_two_mul_offDiagonal_sheet_pairing
    (pairing : E →ₗ[ℝ] E →ₗ[ℝ] ℝ)
    (h_symm : ∀ x y : E, pairing x y = pairing y x)
    (z : ModularCPT.DoubledCarrier E) :
    ModularCPT.kreinForm pairing z z =
      2 * ModularCPT.kreinForm pairing
        (SuperGrassmannian.paraProjectorPlus (ModularCPT.K_op (E := E)) z)
        (SuperGrassmannian.paraProjectorMinus (ModularCPT.K_op (E := E)) z) := by
  rw [kreinForm_eq_offDiagonal_sheet_pairing_sum,
    ThreeTraditionLineageConvergence.paraProjectorPlus_K_op_apply,
    ThreeTraditionLineageConvergence.paraProjectorMinus_K_op_apply]
  simp only [ModularCPT.kreinForm, map_zero, add_zero, zero_add]
  rw [h_symm z.2 z.1, two_mul]

/-!
## Section 4: Unoriented Möbius $\mathbb{Z}_2$ Quotient
-/

/-- The $\mathbb{Z}_2$ orbit equivalence relation on `ModularCPT.DoubledCarrier E`
generated by the involutive Möbius twist $\tau(x, y) = (-y, -x)$. -/
def mobiusOrbitRel (E : Type*) [AddCommGroup E] [Module ℝ E]
    (z w : ModularCPT.DoubledCarrier E) : Prop :=
  z = w ∨ w = ModularCPT.moebiusTwist z

/-- Reflexivity of `mobiusOrbitRel`. -/
theorem mobiusOrbitRel_refl (z : ModularCPT.DoubledCarrier E) :
    mobiusOrbitRel E z z :=
  Or.inl rfl

/-- Symmetry of `mobiusOrbitRel`, following from `ModularCPT.moebiusTwist_involutive`. -/
theorem mobiusOrbitRel_symm {z w : ModularCPT.DoubledCarrier E}
    (hzw : mobiusOrbitRel E z w) :
    mobiusOrbitRel E w z := by
  rcases hzw with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr (ModularCPT.moebiusTwist_involutive z).symm

/-- Transitivity of `mobiusOrbitRel`, following from `ModularCPT.moebiusTwist_involutive`. -/
theorem mobiusOrbitRel_trans {u v w : ModularCPT.DoubledCarrier E}
    (huv : mobiusOrbitRel E u v) (hvw : mobiusOrbitRel E v w) :
    mobiusOrbitRel E u w := by
  rcases huv with rfl | rfl <;> rcases hvw with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr rfl
  · exact Or.inr rfl
  · exact Or.inl (ModularCPT.moebiusTwist_involutive u).symm

/-- The $\mathbb{Z}_2$ Möbius setoid on `ModularCPT.DoubledCarrier E`. -/
def chiralMobiusSetoid (E : Type*) [AddCommGroup E] [Module ℝ E] :
    Setoid (ModularCPT.DoubledCarrier E) where
  r := mobiusOrbitRel E
  iseqv := ⟨mobiusOrbitRel_refl, mobiusOrbitRel_symm, mobiusOrbitRel_trans⟩

/-- The unoriented Möbius quotient `(E × E) / ℤ₂` identifying each state `z` with
its Möbius-twisted partner `ModularCPT.moebiusTwist z = (-z.2, -z.1)`. -/
abbrev UnorientedMobiusQuotient (E : Type*) [AddCommGroup E] [Module ℝ E] : Type _ :=
  Quotient (chiralMobiusSetoid E)

/-- The Krein quadratic form `kreinForm pairing z z` is invariant along every
`mobiusOrbitRel` equivalence class. -/
theorem kreinForm_self_eq_of_mobiusOrbitRel
    (pairing : E →ₗ[ℝ] E →ₗ[ℝ] ℝ)
    {z w : ModularCPT.DoubledCarrier E}
    (hzw : mobiusOrbitRel E z w) :
    ModularCPT.kreinForm pairing z z = ModularCPT.kreinForm pairing w w := by
  rcases hzw with rfl | rfl
  · rfl
  · exact (ThreeTraditionLineageConvergence.kreinForm_moebiusTwist_invariant pairing z z).symm

/-- The Krein quadratic form descends well-definedly to the unoriented Möbius quotient. -/
def quotientKreinQuadratic
    (pairing : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) :
    UnorientedMobiusQuotient E → ℝ :=
  Quotient.lift (fun z => ModularCPT.kreinForm pairing z z)
    (fun _ _ hzw => kreinForm_self_eq_of_mobiusOrbitRel pairing hzw)

/-- In `UnorientedMobiusQuotient E`, every pure primal state `(v, 0)` in
`primalSheet K_op` is identified with the pure covector vacuum state `(0, -v)` in
`covectorVacuumSheet K_op`. -/
theorem primal_eq_covectorVacuum_in_unorientedMobiusQuotient (v : E) :
    (Quotient.mk (chiralMobiusSetoid E) (v, (0 : E)) : UnorientedMobiusQuotient E) =
      Quotient.mk (chiralMobiusSetoid E) ((0 : E), -v) := by
  apply Quotient.sound
  change mobiusOrbitRel E (v, (0 : E)) ((0 : E), -v)
  right
  rw [ModularCPT.moebiusTwist_apply]
  simp

end KreinSheets

/-!
## Section 5: Finite Zorn/Jordan–Wigner Vacuum–Top Peirce Identities
-/

/-- The Zorn Jordan–Wigner conjugator $P_{\mathrm{JW}}$ maps the vacuum idempotent
basis state $e_0 = a \leftrightarrow |000\rangle$ to the top Fock basis state
$e_7 = b \leftrightarrow |111\rangle$. -/
theorem zornJWConjugator_mulVec_vacuum_basis :
    SplitOctonionJordanWignerIntertwiner.zornJWConjugator.mulVec
      (Pi.single (0 : Fin 8) (1 : ℝ)) =
        Pi.single (7 : Fin 8) (1 : ℝ) := by
  ext i
  fin_cases i <;>
    norm_num [SplitOctonionJordanWignerIntertwiner.zornJWConjugator,
      Matrix.mulVec, dotProduct, Fin.sum_univ_eight, Pi.single_apply]

/-- The Zorn Jordan–Wigner conjugator $P_{\mathrm{JW}}$ maps the top Fock basis
state $e_7 = b \leftrightarrow |111\rangle$ back to the vacuum idempotent basis state
$e_0 = a \leftrightarrow |000\rangle$. -/
theorem zornJWConjugator_mulVec_top_basis :
    SplitOctonionJordanWignerIntertwiner.zornJWConjugator.mulVec
      (Pi.single (7 : Fin 8) (1 : ℝ)) =
        Pi.single (0 : Fin 8) (1 : ℝ) := by
  ext i
  fin_cases i <;>
    norm_num [SplitOctonionJordanWignerIntertwiner.zornJWConjugator,
      Matrix.mulVec, dotProduct, Fin.sum_univ_eight, Pi.single_apply]

/-- The Zorn Jordan–Wigner conjugator $P_{\mathrm{JW}}$ pointwise fixes every basis
vector $e_k$ ($k \in \{1, 2, 3, 4, 5, 6\}$) spanning the $3 \oplus 3$ primal and dual
vector sheets. -/
theorem zornJWConjugator_fixes_primal_and_dual_sheet_basis
    (k : Fin 8) (hk0 : k ≠ 0) (hk7 : k ≠ 7) :
    SplitOctonionJordanWignerIntertwiner.zornJWConjugator.mulVec
      (Pi.single k (1 : ℝ)) =
        Pi.single k (1 : ℝ) := by
  fin_cases k
  · exact False.elim (hk0 rfl)
  · ext i
    fin_cases i <;>
      norm_num [SplitOctonionJordanWignerIntertwiner.zornJWConjugator,
        Matrix.mulVec, dotProduct, Fin.sum_univ_eight, Pi.single_apply]
  · ext i
    fin_cases i <;>
      norm_num [SplitOctonionJordanWignerIntertwiner.zornJWConjugator,
        Matrix.mulVec, dotProduct, Fin.sum_univ_eight, Pi.single_apply]
  · ext i
    fin_cases i <;>
      norm_num [SplitOctonionJordanWignerIntertwiner.zornJWConjugator,
        Matrix.mulVec, dotProduct, Fin.sum_univ_eight, Pi.single_apply]
  · ext i
    fin_cases i <;>
      norm_num [SplitOctonionJordanWignerIntertwiner.zornJWConjugator,
        Matrix.mulVec, dotProduct, Fin.sum_univ_eight, Pi.single_apply]
  · ext i
    fin_cases i <;>
      norm_num [SplitOctonionJordanWignerIntertwiner.zornJWConjugator,
        Matrix.mulVec, dotProduct, Fin.sum_univ_eight, Pi.single_apply]
  · ext i
    fin_cases i <;>
      norm_num [SplitOctonionJordanWignerIntertwiner.zornJWConjugator,
        Matrix.mulVec, dotProduct, Fin.sum_univ_eight, Pi.single_apply]
  · exact False.elim (hk7 rfl)

set_option maxHeartbeats 0

/-- The $8 \times 8$ vacuum-minus-top Peirce operator
$\operatorname{diag}(1, 0, 0, 0, 0, 0, 0, -1)$ on the 8D Fock ket space, separating
the vacuum idempotent line $e_0$ and top Fock line $e_7$ from the
$3 \oplus 3$ primal and dual vector sheets. It is not the full chiral-volume
operator on the eight-dimensional spinor space. -/
def zornVacuumTopPeirceOperator : Matrix (Fin 8) (Fin 8) ℝ :=
  !![1, 0, 0, 0, 0, 0, 0,  0;
     0, 0, 0, 0, 0, 0, 0,  0;
     0, 0, 0, 0, 0, 0, 0,  0;
     0, 0, 0, 0, 0, 0, 0,  0;
     0, 0, 0, 0, 0, 0, 0,  0;
     0, 0, 0, 0, 0, 0, 0,  0;
     0, 0, 0, 0, 0, 0, 0,  0;
     0, 0, 0, 0, 0, 0, 0, -1]

/-- The half-sum $\tfrac{1}{2}(L_K + R_K)$ of the left
and right multiplication matrices of `SplitOctonionParaKahlerNullCone.zornParaGrading`
equals `zornVacuumTopPeirceOperator`. -/
theorem zornVacuumTopPeirceOperator_eq_half_left_add_right :
    (1 / 2 : ℝ) •
      (SplitOctonionClifford33Soldering.zornLeftActMatrix
          (SplitOctonionParaKahlerNullCone.zornParaGrading (R := ℝ)) +
        SplitOctonionClifford33Soldering.zornRightActMatrix
          (SplitOctonionParaKahlerNullCone.zornParaGrading (R := ℝ))) =
      zornVacuumTopPeirceOperator := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [zornVacuumTopPeirceOperator,
      SplitOctonionClifford33Soldering.zornLeftActMatrix,
      SplitOctonionClifford33Soldering.zornLeftActFin8,
      SplitOctonionClifford33Soldering.zornRightActMatrix,
      SplitOctonionClifford33Soldering.zornRightActFin8,
      SplitOctonionParaKahlerNullCone.zornParaGrading,
      ZornSplitOctonionFin8Bridge.fin8ToZorn,
      ZornSplitOctonionFin8Bridge.zornToFin8,
      ZornSplitOctonionFin8Bridge.zornMul,
      ZornSplitOctonionFin8Bridge.vec3Dot,
      ZornSplitOctonionFin8Bridge.vec3Cross,
      LinearMap.toMatrix_apply, Pi.basisFun_apply,
      Pi.basisFun_repr, Pi.single_apply]

/-- Conjugating `zornVacuumTopPeirceOperator = diag(1, 0, 0, 0, 0, 0, 0, -1)` by
`zornJWConjugator` negates it, witnessing the exchange of the vacuum and top Fock
lines. This is not a statement about full $\operatorname{Cl}(3,3)$ chirality. -/
theorem zornJWConjugator_negates_zornVacuumTopPeirceOperator :
    SplitOctonionJordanWignerIntertwiner.zornJWConjugator *
      zornVacuumTopPeirceOperator *
      SplitOctonionJordanWignerIntertwiner.zornJWConjugator =
        -zornVacuumTopPeirceOperator := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [SplitOctonionJordanWignerIntertwiner.zornJWConjugator,
      zornVacuumTopPeirceOperator, Matrix.mul_apply,
      Fin.sum_univ_eight]

end InfoGeometry.Synthesis.Cl11ChiralVolumeNilpotentQuotientSynthesis
