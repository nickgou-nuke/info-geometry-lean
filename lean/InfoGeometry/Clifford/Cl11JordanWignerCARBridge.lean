import InfoGeometry.Clifford.Cl11TensorTower
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Clifford.JordanWignerCAR
import InfoGeometry.Canonical.Cl11TensorTowerCrossSiteCAR

set_option autoImplicit false

noncomputable section

open scoped TensorProduct DirectSum Matrix Kronecker

namespace InfoGeometry.Clifford.Cl11JordanWignerCARBridge

open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Clifford.JordanWignerCAR
open InfoGeometry.Clifford.JordanWignerBridge
open InfoGeometry.Canonical.Cl11TensorTowerCrossSiteCAR

theorem jwCreation_last_eq_jw_u_new (k : ℕ) :
    jwCreation (k + 1) ⟨k, Nat.lt_succ_self k⟩ = jw_u_new k := by
  simp [jwCreation, jw_u_new, jwStringWithBase_last, wittCreationBase,
    a_dagger_base]

theorem jwAnnihilation_last_eq_jw_v_new (k : ℕ) :
    jwAnnihilation (k + 1) ⟨k, Nat.lt_succ_self k⟩ = jw_v_new k := by
  simp [jwAnnihilation, jw_v_new, jwStringWithBase_last, wittAnnihilationBase,
    a_base]

theorem jwCreation_last_sq (k : ℕ) :
    jwCreation (k + 1) ⟨k, Nat.lt_succ_self k⟩ *
        jwCreation (k + 1) ⟨k, Nat.lt_succ_self k⟩ = 0 := by
  rw [jwCreation_last_eq_jw_u_new]
  exact jw_u_new_sq k

theorem jwAnnihilation_last_sq (k : ℕ) :
    jwAnnihilation (k + 1) ⟨k, Nat.lt_succ_self k⟩ *
        jwAnnihilation (k + 1) ⟨k, Nat.lt_succ_self k⟩ = 0 := by
  rw [jwAnnihilation_last_eq_jw_v_new]
  exact jw_v_new_sq k

theorem jwAnnihilation_last_creation_last_anticomm (k : ℕ) :
    jwAnnihilation (k + 1) ⟨k, Nat.lt_succ_self k⟩ *
        jwCreation (k + 1) ⟨k, Nat.lt_succ_self k⟩ +
      jwCreation (k + 1) ⟨k, Nat.lt_succ_self k⟩ *
        jwAnnihilation (k + 1) ⟨k, Nat.lt_succ_self k⟩ = 1 := by
  rw [jwAnnihilation_last_eq_jw_v_new, jwCreation_last_eq_jw_u_new]
  simpa [add_comm] using jw_uv_anticomm_new k

/-! The same-site CAR law is proved by the tensor-tower induction.  The
    cross-site part is owned separately by `Cl11TensorTowerCrossSiteCAR`; the
    present theorem supplies the missing diagonal case. -/

theorem jw_same_site_car :
    ∀ (n : ℕ) (k : Fin n),
      jwAnnihilation n k * jwCreation n k +
          jwCreation n k * jwAnnihilation n k = 1
  | 0, k => Fin.elim0 k
  | n + 1, k => by
      by_cases h : (k : ℕ) < n
      · let k' : Fin n := ⟨k, h⟩
        have ih := jw_same_site_car n k'
        simp [jwCreation, jwAnnihilation, jwStringWithBase, h]
        change
          ((jwStringWithBase wittAnnihilationBase n k') ⊗ₖ
              (1 : Matrix (Fin 2) (Fin 2) ℝ)) *
              ((jwStringWithBase wittCreationBase n k') ⊗ₖ
                (1 : Matrix (Fin 2) (Fin 2) ℝ)) +
            ((jwStringWithBase wittCreationBase n k') ⊗ₖ
              (1 : Matrix (Fin 2) (Fin 2) ℝ)) *
              ((jwStringWithBase wittAnnihilationBase n k') ⊗ₖ
                (1 : Matrix (Fin 2) (Fin 2) ℝ)) = 1
        rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
          ← Matrix.add_kronecker]
        simpa using congrArg (fun A : MatStage n => A ⊗ₖ
          (1 : Matrix (Fin 2) (Fin 2) ℝ)) ih
      · have hk : k = Fin.last n := Fin.eq_last_of_not_lt h
        subst k
        have hlast : (Fin.last n : Fin (n + 1)) =
            ⟨n, Nat.lt_succ_self n⟩ := rfl
        simpa [hlast] using
          jwAnnihilation_last_creation_last_anticomm n

theorem jwAnnihilation_creation_anticommutator
    (n : ℕ) (i j : Fin n) :
      jwAnnihilation n i * jwCreation n j +
          jwCreation n j * jwAnnihilation n i =
        if i = j then 1 else 0 := by
  by_cases hij : i = j
  · subst j
    simp [jw_same_site_car]
  · rw [if_neg hij]
    exact annihilation_creation_cross_site_anticommute n i j hij

end InfoGeometry.Clifford.Cl11JordanWignerCARBridge
