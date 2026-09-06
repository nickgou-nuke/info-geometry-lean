import Mathlib.Tactic
import InfoGeometry.Canonical.Cl11WittVacancyTensorFactorization

/-!
# Witt occupation and global chirality factorization

This owner proves the multiplicative parity statement on the native real
`Cl(1,1)` tensor tower.

For one Jordan--Wigner mode define the occupation projector

`N_i = e_i f_i`

and the local chirality factor

`K_i = 1 - 2 N_i`.

Because matrix multiplication is noncommutative, the total product is not
written as an unordered `Finset.prod`.  Instead `orderedModeChiralityProduct`
uses the canonical tensor-stage order: append one site, embed the previous
product by `A ↦ A ⊗ 1`, and multiply by the new last-site factor.  The main
theorem proves that this ordered product is exactly `globalChirality`.
-/

noncomputable section
set_option autoImplicit false

namespace InfoGeometry.Canonical.Cl11WittOccupationParityFactorization

open scoped Matrix Kronecker BigOperators
open Matrix
open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Clifford.TowerMatrix
open InfoGeometry.Clifford.JordanWignerCAR

/-- Local one-mode occupation projector `e f`. -/
def localOccupationProjector : Matrix (Fin 2) (Fin 2) ℝ :=
  wittCreationBase * wittAnnihilationBase

/-- The local occupation projector is the first coordinate projector. -/
theorem localOccupationProjector_eq :
    localOccupationProjector = !![(1 : ℝ), 0; 0, 0] := by
  rw [show localOccupationProjector =
      realEncodedWittCreationBase * realEncodedWittAnnihilationBase by
        simp [localOccupationProjector, realEncodedWittCreationBase_eq,
          realEncodedWittAnnihilationBase_eq]]
  exact realEncodedWittCreation_mul_annihilation

/-- Finite-stage occupation projector at one Jordan--Wigner site. -/
def occupationAt (n : ℕ) (k : Fin n) : MatStage n :=
  jwCreation n k * jwAnnihilation n k

/-- Tensor-coordinate realization of a one-site occupation projector. -/
noncomputable def occupationTensorAt : (n : ℕ) → Fin n → MatStage n
  | 0, k => Fin.elim0 k
  | n + 1, k =>
      if h : (k : ℕ) < n then
        occupationTensorAt n ⟨k, h⟩ ⊗ₖ
          (1 : Matrix (Fin 2) (Fin 2) ℝ)
      else
        (1 : MatStage n) ⊗ₖ localOccupationProjector

/-- A Jordan--Wigner occupation projector has no residual chirality string. -/
theorem occupationAt_eq_tensor :
    ∀ (n : ℕ) (k : Fin n), occupationAt n k = occupationTensorAt n k
  | 0, k => Fin.elim0 k
  | n + 1, k => by
      by_cases h : (k : ℕ) < n
      · let k' : Fin n := ⟨k, h⟩
        have ih := occupationAt_eq_tensor n k'
        simp only [occupationAt, jwCreation, jwAnnihilation,
          jwStringWithBase, dif_pos h, occupationTensorAt]
        rw [← Matrix.mul_kronecker_mul]
        simpa [occupationAt] using congrArg
          (fun A : MatStage n =>
            A ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℝ)) ih
      · have hk : k = Fin.last n := Fin.eq_last_of_not_lt h
        subst k
        have hlast : ¬ ((Fin.last n : Fin (n + 1)).val < n) := by simp
        simp only [occupationAt, jwCreation, jwAnnihilation,
          jwStringWithBase, occupationTensorAt, dif_neg hlast]
        change
          (globalChirality n ⊗ₖ wittCreationBase) *
              (globalChirality n ⊗ₖ wittAnnihilationBase) =
            (1 : MatStage n) ⊗ₖ localOccupationProjector
        rw [← Matrix.mul_kronecker_mul]
        rw [globalChirality_sq]
        rfl

/-- The last-site occupation projector is `1 ⊗ (e f)`. -/
theorem occupationAt_last (n : ℕ) :
    occupationAt (n + 1) (Fin.last n) =
      (1 : MatStage n) ⊗ₖ localOccupationProjector := by
  rw [occupationAt_eq_tensor]
  simp [occupationTensorAt]

/-- The local chirality factor `1 - 2 e f`. -/
def localChiralityFactor : Matrix (Fin 2) (Fin 2) ℝ :=
  (1 : Matrix (Fin 2) (Fin 2) ℝ) -
    (2 : ℝ) • localOccupationProjector

/-- The local occupation-parity factor is exactly the native chiral atom. -/
theorem localChiralityFactor_eq_gamma_chiral_base :
    localChiralityFactor = gamma_chiral_base := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [localChiralityFactor, localOccupationProjector,
      wittCreationBase, wittAnnihilationBase, gamma_chiral_base,
      gamma_0_base, gamma_1_base,
      InfoGeometry.Clifford.Cl11Matrix.J1,
      InfoGeometry.Clifford.Cl11Matrix.Eminus,
      Matrix.mul_apply, Fin.sum_univ_two]

/-- Sitewise chirality factor `K_i = 1 - 2 e_i f_i`. -/
def modeChiralityFactor (n : ℕ) (k : Fin n) : MatStage n :=
  (1 : MatStage n) - (2 : ℝ) • occupationAt n k

/-- At the newly appended site the mode factor is `1 ⊗ gamma_chiral_base`. -/
theorem modeChiralityFactor_last (n : ℕ) :
    modeChiralityFactor (n + 1) (Fin.last n) =
      (1 : MatStage n) ⊗ₖ gamma_chiral_base := by
  rw [modeChiralityFactor, occupationAt_last]
  calc
    (1 : MatStage (n + 1)) -
          (2 : ℝ) • ((1 : MatStage n) ⊗ₖ localOccupationProjector) =
        (1 : MatStage n) ⊗ₖ localChiralityFactor := by
          ext ⟨i, a⟩ ⟨j, b⟩
          by_cases hij : i = j <;> by_cases hab : a = b <;>
            simp [localChiralityFactor, hij, hab]
    _ = (1 : MatStage n) ⊗ₖ gamma_chiral_base := by
      rw [localChiralityFactor_eq_gamma_chiral_base]

/-- Canonical ordered product of the site chirality factors.

At the successor stage, the previous product is embedded as `A ⊗ 1` and the
new last-site factor is multiplied on the right. -/
noncomputable def orderedModeChiralityProduct : (n : ℕ) → MatStage n
  | 0 => 1
  | n + 1 =>
      matStageEmbed n (orderedModeChiralityProduct n) *
        modeChiralityFactor (n + 1) (Fin.last n)

/-- The ordered product of all local `1 - 2 e_i f_i` factors is exactly the
global tensor-tower chirality operator. -/
theorem orderedModeChiralityProduct_eq_globalChirality :
    ∀ n : ℕ, orderedModeChiralityProduct n = globalChirality n
  | 0 => rfl
  | n + 1 => by
      rw [orderedModeChiralityProduct,
        orderedModeChiralityProduct_eq_globalChirality n,
        modeChiralityFactor_last]
      change
        (globalChirality n ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℝ)) *
            ((1 : MatStage n) ⊗ₖ gamma_chiral_base) =
          globalChirality (n + 1)
      rw [← Matrix.mul_kronecker_mul]
      simp [globalChirality, kronPow]

/-- The ordered parity product is an involution at every finite stage. -/
theorem orderedModeChiralityProduct_sq (n : ℕ) :
    orderedModeChiralityProduct n * orderedModeChiralityProduct n =
      (1 : MatStage n) := by
  rw [orderedModeChiralityProduct_eq_globalChirality]
  exact globalChirality_sq n

end InfoGeometry.Canonical.Cl11WittOccupationParityFactorization
