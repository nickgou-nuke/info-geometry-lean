import InfoGeometry.Clifford.Cl11JordanWignerCARBridge
import InfoGeometry.Canonical.GNSCARColimit
import InfoGeometry.Topology.FractalCantorFock
import InfoGeometry.Canonical.Cl11WittOccupationParityFactorization

/-!
# Native `Cl(1,1)` CAR pairs for the finite/Fock interface

This owner instantiates the repository's finite `RealCARPair` interface with
the native Jordan--Wigner operators and with their algebraic direct-limit
representatives.  It is deliberately an algebraic readout: it does not add a
completed Fock space, an `O₂`/CAR equivalence, or an analytic limit.
-/

noncomputable section

namespace InfoGeometry.Canonical.Cl11CARFockColimitBridge

open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Clifford.Cl11JordanWignerCARBridge
open InfoGeometry.Clifford.Cl11TensorTowerLimit
open InfoGeometry.Canonical.GNSCARColimit
open InfoGeometry.Topology.FractalCantorFock

/-- The native last-site Jordan--Wigner CAR pair at a finite stage. -/
def finiteLastCARPair (k : ℕ) :
    RealCARPair (MatStage (k + 1)) where
  annihilation := jwAnnihilation (k + 1) ⟨k, Nat.lt_succ_self k⟩
  creation := jwCreation (k + 1) ⟨k, Nat.lt_succ_self k⟩
  nilpotent_annihilation := jwAnnihilation_last_sq k
  nilpotent_creation := jwCreation_last_sq k
  car := jwAnnihilation_last_creation_last_anticomm k

@[simp] theorem finiteLastCARPair_annihilation (k : ℕ) :
    (finiteLastCARPair k).annihilation =
      jwAnnihilation (k + 1) ⟨k, Nat.lt_succ_self k⟩ := rfl

@[simp] theorem finiteLastCARPair_creation (k : ℕ) :
    (finiteLastCARPair k).creation =
      jwCreation (k + 1) ⟨k, Nat.lt_succ_self k⟩ := rfl

/-- The `k`th algebraic direct-limit Jordan--Wigner CAR pair. -/
def algebraicCARPair (k : ℕ) :
    RealCARPair InfoGeometry.Clifford.Cl11TensorTowerLimit.Limit where
  annihilation := limit_v k
  creation := limit_u k
  nilpotent_annihilation := limit_v_sq_zero k
  nilpotent_creation := limit_u_sq_zero k
  car := by
    rw [add_comm]
    exact limit_uv_anticomm k

@[simp] theorem algebraicCARPair_annihilation (k : ℕ) :
    (algebraicCARPair k).annihilation = limit_v k := rfl

@[simp] theorem algebraicCARPair_creation (k : ℕ) :
    (algebraicCARPair k).creation = limit_u k := rfl

theorem finiteLastCARPair_annihilation_to_colimit (k : ℕ) :
    ofStage (k + 1) (finiteLastCARPair k).annihilation =
      (algebraicCARPair k).annihilation := by
  rw [finiteLastCARPair_annihilation]
  rw [jwAnnihilation_last_eq_jw_v_new]
  rfl

theorem finiteLastCARPair_creation_to_colimit (k : ℕ) :
    ofStage (k + 1) (finiteLastCARPair k).creation =
      (algebraicCARPair k).creation := by
  rw [finiteLastCARPair_creation]
  rw [jwCreation_last_eq_jw_u_new]
  rfl

/-- The last-site occupation projector maps to the colimit creation-annihilation product. -/
theorem occupationAt_last_to_algebraic (k : ℕ) :
    ofStage (k + 1)
      (Cl11WittOccupationParityFactorization.occupationAt (k + 1) (Fin.last k)) =
      (algebraicCARPair k).creation * (algebraicCARPair k).annihilation := by
  change ofStage (k + 1)
    ((finiteLastCARPair k).creation * (finiteLastCARPair k).annihilation) = _
  rw [ofStage_mul, finiteLastCARPair_creation_to_colimit,
    finiteLastCARPair_annihilation_to_colimit]

/-- The last-site vacancy projector maps to the opposite colimit product. -/
theorem vacancyAt_last_to_algebraic (k : ℕ) :
    ofStage (k + 1)
      (Cl11WittVacancyTensorFactorization.vacancyAt (k + 1) (Fin.last k)) =
      (algebraicCARPair k).annihilation * (algebraicCARPair k).creation := by
  change ofStage (k + 1)
    ((finiteLastCARPair k).annihilation * (finiteLastCARPair k).creation) = _
  rw [ofStage_mul, finiteLastCARPair_annihilation_to_colimit,
    finiteLastCARPair_creation_to_colimit]

def finiteLastCARPair_colimitReadout (k : ℕ) :
    RealCARPair InfoGeometry.Clifford.Cl11TensorTowerLimit.Limit where
  annihilation := ofStage (k + 1) (finiteLastCARPair k).annihilation
  creation := ofStage (k + 1) (finiteLastCARPair k).creation
  nilpotent_annihilation := by
    rw [finiteLastCARPair_annihilation_to_colimit]
    exact (algebraicCARPair k).nilpotent_annihilation
  nilpotent_creation := by
    rw [finiteLastCARPair_creation_to_colimit]
    exact (algebraicCARPair k).nilpotent_creation
  car := by
    rw [finiteLastCARPair_annihilation_to_colimit,
      finiteLastCARPair_creation_to_colimit]
    exact (algebraicCARPair k).car

theorem finiteLastCARPair_colimitReadout_eq_algebraic (k : ℕ) :
    finiteLastCARPair_colimitReadout k = algebraicCARPair k := by
  cases h₁ : finiteLastCARPair_colimitReadout k with
  | mk a₁ c₁ ha₁ hc₁ hcar₁ =>
    cases h₂ : algebraicCARPair k with
    | mk a₂ c₂ ha₂ hc₂ hcar₂ =>
      cases h₁
      cases h₂
      congr 1
      · exact finiteLastCARPair_annihilation_to_colimit k
      · exact finiteLastCARPair_creation_to_colimit k

theorem algebraicCARPair_car (k : ℕ) :
    (algebraicCARPair k).annihilation *
          (algebraicCARPair k).creation +
        (algebraicCARPair k).creation *
          (algebraicCARPair k).annihilation = 1 :=
  (algebraicCARPair k).car

end InfoGeometry.Canonical.Cl11CARFockColimitBridge
