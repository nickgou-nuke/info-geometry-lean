import InfoGeometry.Canonical.Cl11TensorTowerCrossSiteCAR
import InfoGeometry.Clifford.JordanWignerCAR

noncomputable section

set_option autoImplicit false

namespace InfoGeometry.Canonical.Cl55WittCAR

open scoped Matrix Kronecker
open Matrix
open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Clifford.TowerMatrix
open InfoGeometry.Clifford.JordanWignerCAR
open InfoGeometry.Canonical.Cl11TensorTowerCrossSiteCAR

/-- The five-mode real Witt creation operators in the native stage-5 tower. -/
abbrev creation (i : Fin 5) : MatStage 5 := jwCreation 5 i

/-- The five-mode real Witt annihilation operators in the native stage-5 tower. -/
abbrev annihilation (i : Fin 5) : MatStage 5 := jwAnnihilation 5 i

private theorem wittCreationBase_transpose :
    wittCreationBaseᵀ = wittAnnihilationBase := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    rfl

private theorem gamma_chiral_base_transpose :
    gamma_chiral_baseᵀ = gamma_chiral_base := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [gamma_chiral_base, gamma_0_base, gamma_1_base,
      InfoGeometry.Clifford.Cl11Matrix.J1,
      InfoGeometry.Clifford.Cl11Matrix.Eminus,
      Matrix.transpose_apply, Matrix.mul_apply, Fin.sum_univ_two]

private theorem jwStringWithBase_transpose
    (localMat : Matrix (Fin 2) (Fin 2) ℝ) :
    ∀ (n : ℕ) (k : Fin n),
      (jwStringWithBase localMat n k)ᵀ =
        jwStringWithBase localMatᵀ n k
  | 0, k => Fin.elim0 k
  | n + 1, k => by
      by_cases h : (k : ℕ) < n
      · simp only [jwStringWithBase, dif_pos h]
        rw [InfoGeometry.Clifford.TowerMatrix.transpose_kronecker]
        simp only [transpose_one]
        rw [jwStringWithBase_transpose localMat n ⟨k, h⟩]
      · simp only [jwStringWithBase, dif_neg h]
        rw [InfoGeometry.Clifford.TowerMatrix.transpose_kronecker]
        simp only [globalChirality]
        have hgc :
            (InfoGeometry.Clifford.TowerMatrix.kronPow gamma_chiral_base n)ᵀ =
              InfoGeometry.Clifford.TowerMatrix.kronPow gamma_chiral_base n := by
          simpa [InfoGeometry.Clifford.TowerMatrix.Jn] using
            (InfoGeometry.Clifford.TowerMatrix.Jn_transpose
              gamma_chiral_base gamma_chiral_base_transpose n)
        rw [hgc]

theorem globalChirality_transpose (n : ℕ) :
    (globalChirality n)ᵀ = globalChirality n := by
  unfold globalChirality
  have hgc :
      (InfoGeometry.Clifford.TowerMatrix.kronPow gamma_chiral_base n)ᵀ =
        InfoGeometry.Clifford.TowerMatrix.kronPow gamma_chiral_base n := by
    simpa [InfoGeometry.Clifford.TowerMatrix.Jn] using
      (InfoGeometry.Clifford.TowerMatrix.Jn_transpose
        gamma_chiral_base gamma_chiral_base_transpose n)
  exact hgc

theorem creation_transpose (i : Fin 5) :
    (creation i)ᵀ = annihilation i := by
  simpa [creation, annihilation, jwCreation, jwAnnihilation,
    wittCreationBase_transpose] using
    (jwStringWithBase_transpose wittCreationBase 5 i)

theorem creation_sq :
    ∀ (n : ℕ) (k : Fin n), jwCreation n k * jwCreation n k = 0
  | 0, k => Fin.elim0 k
  | n + 1, k => by
      by_cases h : (k : ℕ) < n
      · let k' : Fin n := ⟨k, h⟩
        have ih := creation_sq n k'
        have ih' :
            jwStringWithBase wittCreationBase n k' *
                jwStringWithBase wittCreationBase n k' = 0 := by
          simpa [jwCreation] using ih
        simp [jwCreation, jwStringWithBase, h]
        change
          ((jwStringWithBase wittCreationBase n k') ⊗ₖ
              (1 : Matrix (Fin 2) (Fin 2) ℝ)) *
              ((jwStringWithBase wittCreationBase n k') ⊗ₖ
                (1 : Matrix (Fin 2) (Fin 2) ℝ)) = 0
        rw [← Matrix.mul_kronecker_mul, ih']
        simp
      · have hk : k = Fin.last n := Fin.eq_last_of_not_lt h
        subst k
        simp [jwCreation, jwStringWithBase]
        change
          (kronPow gamma_chiral_base n ⊗ₖ wittCreationBase) *
              (kronPow gamma_chiral_base n ⊗ₖ wittCreationBase) = 0
        have hsq : kronPow gamma_chiral_base n * kronPow gamma_chiral_base n =
            (1 : MatStage n) := by
          simpa [globalChirality] using globalChirality_sq n
        rw [← Matrix.mul_kronecker_mul, hsq, wittCreationBase_sq]
        simp

theorem annihilation_sq :
    ∀ (n : ℕ) (k : Fin n), jwAnnihilation n k * jwAnnihilation n k = 0
  | 0, k => Fin.elim0 k
  | n + 1, k => by
      by_cases h : (k : ℕ) < n
      · let k' : Fin n := ⟨k, h⟩
        have ih := annihilation_sq n k'
        have ih' :
            jwStringWithBase wittAnnihilationBase n k' *
                jwStringWithBase wittAnnihilationBase n k' = 0 := by
          simpa [jwAnnihilation] using ih
        simp [jwAnnihilation, jwStringWithBase, h]
        change
          ((jwStringWithBase wittAnnihilationBase n k') ⊗ₖ
              (1 : Matrix (Fin 2) (Fin 2) ℝ)) *
              ((jwStringWithBase wittAnnihilationBase n k') ⊗ₖ
                (1 : Matrix (Fin 2) (Fin 2) ℝ)) = 0
        rw [← Matrix.mul_kronecker_mul, ih']
        simp
      · have hk : k = Fin.last n := Fin.eq_last_of_not_lt h
        subst k
        simp [jwAnnihilation, jwStringWithBase]
        change
          (kronPow gamma_chiral_base n ⊗ₖ wittAnnihilationBase) *
              (kronPow gamma_chiral_base n ⊗ₖ wittAnnihilationBase) = 0
        have hsq : kronPow gamma_chiral_base n * kronPow gamma_chiral_base n =
            (1 : MatStage n) := by
          simpa [globalChirality] using globalChirality_sq n
        rw [← Matrix.mul_kronecker_mul, hsq]
        have hbase : wittAnnihilationBase * wittAnnihilationBase = 0 := by
          ext i j
          fin_cases i <;> fin_cases j <;>
            norm_num [wittAnnihilationBase, Matrix.mul_apply, Fin.sum_univ_two]
        rw [hbase]
        simp

theorem same_site_car :
    ∀ (n : ℕ) (k : Fin n),
      jwCreation n k * jwAnnihilation n k +
        jwAnnihilation n k * jwCreation n k = 1
  | 0, k => Fin.elim0 k
  | n + 1, k => by
      by_cases h : (k : ℕ) < n
      · let k' : Fin n := ⟨k, h⟩
        have ih := same_site_car n k'
        simp [jwCreation, jwAnnihilation, jwStringWithBase, h]
        change
          ((jwStringWithBase wittCreationBase n k') ⊗ₖ
              (1 : Matrix (Fin 2) (Fin 2) ℝ)) *
              ((jwStringWithBase wittAnnihilationBase n k') ⊗ₖ
                (1 : Matrix (Fin 2) (Fin 2) ℝ)) +
            ((jwStringWithBase wittAnnihilationBase n k') ⊗ₖ
                (1 : Matrix (Fin 2) (Fin 2) ℝ)) *
              ((jwStringWithBase wittCreationBase n k') ⊗ₖ
                (1 : Matrix (Fin 2) (Fin 2) ℝ)) = 1
        rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
          ← Matrix.add_kronecker]
        simpa using congrArg (fun A : MatStage n => A ⊗ₖ
          (1 : Matrix (Fin 2) (Fin 2) ℝ)) ih
      · have hk : k = Fin.last n := Fin.eq_last_of_not_lt h
        subst k
        simp [jwCreation, jwAnnihilation, jwStringWithBase]
        change
          (kronPow gamma_chiral_base n ⊗ₖ wittCreationBase) *
              (kronPow gamma_chiral_base n ⊗ₖ wittAnnihilationBase) +
            (kronPow gamma_chiral_base n ⊗ₖ wittAnnihilationBase) *
              (kronPow gamma_chiral_base n ⊗ₖ wittCreationBase) = 1
        rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
          ← Matrix.kronecker_add]
        have hsq : kronPow gamma_chiral_base n * kronPow gamma_chiral_base n =
            (1 : MatStage n) := by
          simpa [globalChirality] using globalChirality_sq n
        rw [hsq]
        have hbase : wittCreationBase * wittAnnihilationBase +
            wittAnnihilationBase * wittCreationBase =
              (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
          rw [← realEncodedWittCreationBase_eq,
            ← realEncodedWittAnnihilationBase_eq]
          exact realEncodedWitt_anticomm
        rw [hbase]
        simp

theorem creation_cross_anticommute {i j : Fin 5} (hij : i ≠ j) :
    creation i * creation j + creation j * creation i = 0 := by
  exact creation_cross_site_anticommute 5 i j hij

theorem annihilation_cross_anticommute {i j : Fin 5} (hij : i ≠ j) :
    annihilation i * annihilation j + annihilation j * annihilation i = 0 := by
  exact annihilation_cross_site_anticommute 5 i j hij

theorem creation_annihilation_cross_anticommute {i j : Fin 5} (hij : i ≠ j) :
    creation i * annihilation j + annihilation j * creation i = 0 := by
  exact creation_annihilation_cross_site_anticommute 5 i j hij

theorem annihilation_creation_cross_anticommute {i j : Fin 5} (hij : i ≠ j) :
    annihilation i * creation j + creation j * annihilation i = 0 := by
  exact annihilation_creation_cross_site_anticommute 5 i j hij

theorem creation_same_site_sq (i : Fin 5) : creation i * creation i = 0 :=
  creation_sq 5 i

theorem annihilation_same_site_sq (i : Fin 5) : annihilation i * annihilation i = 0 :=
  annihilation_sq 5 i

theorem creation_annihilation_same_site (i : Fin 5) :
    creation i * annihilation i + annihilation i * creation i = 1 :=
  same_site_car 5 i

end InfoGeometry.Canonical.Cl55WittCAR
