import InfoGeometry.Clifford.Cl11JordanWignerCARBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.CliffordCARGeneratorTopological

noncomputable section

namespace InfoGeometry.Canonical.Cl11JordanWignerCARColimitBridge

open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Clifford.Cl11JordanWignerCARBridge
open InfoGeometry.Clifford.Cl11TensorTowerLimit
open InfoGeometry.Canonical.CliffordCARGeneratorTopological

theorem algebraicCreationElement_last_sq (k : ℕ) :
    algebraicCreationElement (k + 1) ⟨k, Nat.lt_succ_self k⟩ *
        algebraicCreationElement (k + 1) ⟨k, Nat.lt_succ_self k⟩ = 0 := by
  unfold algebraicCreationElement
  rw [← (ofStage (k + 1)).map_mul, jwCreation_last_sq,
    (ofStage (k + 1)).map_zero]

theorem algebraicAnnihilationElement_last_sq (k : ℕ) :
    algebraicAnnihilationElement (k + 1) ⟨k, Nat.lt_succ_self k⟩ *
        algebraicAnnihilationElement (k + 1) ⟨k, Nat.lt_succ_self k⟩ = 0 := by
  unfold algebraicAnnihilationElement
  rw [← (ofStage (k + 1)).map_mul, jwAnnihilation_last_sq,
    (ofStage (k + 1)).map_zero]

theorem algebraicAnnihilationElement_last_creationElement_last_anticomm (k : ℕ) :
    algebraicAnnihilationElement (k + 1) ⟨k, Nat.lt_succ_self k⟩ *
        algebraicCreationElement (k + 1) ⟨k, Nat.lt_succ_self k⟩ +
      algebraicCreationElement (k + 1) ⟨k, Nat.lt_succ_self k⟩ *
        algebraicAnnihilationElement (k + 1) ⟨k, Nat.lt_succ_self k⟩ = 1 := by
  unfold algebraicAnnihilationElement algebraicCreationElement
  rw [← (ofStage (k + 1)).map_mul, ← (ofStage (k + 1)).map_mul,
    ← (ofStage (k + 1)).map_add,
    jwAnnihilation_last_creation_last_anticomm,
    (ofStage (k + 1)).map_one]

/-! The full finite indexed CAR law transports to the algebraic colimit at
    every common finite stage.  This is a representative-level readout, not
    a completed Fock-space assertion. -/

theorem algebraicAnnihilationElement_creationElement_anticommutator
    (n : ℕ) (i j : Fin n) :
    algebraicAnnihilationElement n i * algebraicCreationElement n j +
        algebraicCreationElement n j * algebraicAnnihilationElement n i =
      if i = j then 1 else 0 := by
  unfold algebraicAnnihilationElement algebraicCreationElement
  rw [← (ofStage n).map_mul, ← (ofStage n).map_mul,
    ← (ofStage n).map_add,
    InfoGeometry.Clifford.Cl11JordanWignerCARBridge.jwAnnihilation_creation_anticommutator]
  by_cases hij : i = j <;> simp [hij]

theorem algebraicCreationElement_cross_site_anticommute
    (n : ℕ) (i j : Fin n) (hij : i ≠ j) :
    algebraicCreationElement n i * algebraicCreationElement n j +
        algebraicCreationElement n j * algebraicCreationElement n i = 0 := by
  unfold algebraicCreationElement
  rw [← (ofStage n).map_mul, ← (ofStage n).map_mul,
    ← (ofStage n).map_add,
    InfoGeometry.Canonical.Cl11TensorTowerCrossSiteCAR.creation_cross_site_anticommute
      n i j hij,
    (ofStage n).map_zero]

theorem algebraicAnnihilationElement_cross_site_anticommute
    (n : ℕ) (i j : Fin n) (hij : i ≠ j) :
    algebraicAnnihilationElement n i * algebraicAnnihilationElement n j +
        algebraicAnnihilationElement n j * algebraicAnnihilationElement n i = 0 := by
  unfold algebraicAnnihilationElement
  rw [← (ofStage n).map_mul, ← (ofStage n).map_mul,
    ← (ofStage n).map_add,
    InfoGeometry.Canonical.Cl11TensorTowerCrossSiteCAR.annihilation_cross_site_anticommute
      n i j hij,
    (ofStage n).map_zero]

theorem algebraicCreationElement_annihilationElement_cross_site_anticommute
    (n : ℕ) (i j : Fin n) (hij : i ≠ j) :
    algebraicCreationElement n i * algebraicAnnihilationElement n j +
        algebraicAnnihilationElement n j * algebraicCreationElement n i = 0 := by
  unfold algebraicCreationElement algebraicAnnihilationElement
  rw [← (ofStage n).map_mul, ← (ofStage n).map_mul,
    ← (ofStage n).map_add,
    InfoGeometry.Canonical.Cl11TensorTowerCrossSiteCAR.creation_annihilation_cross_site_anticommute
      n i j hij,
    (ofStage n).map_zero]

theorem algebraicAnnihilationElement_creationElement_cross_site_anticommute
    (n : ℕ) (i j : Fin n) (hij : i ≠ j) :
    algebraicAnnihilationElement n i * algebraicCreationElement n j +
        algebraicCreationElement n j * algebraicAnnihilationElement n i = 0 := by
  unfold algebraicAnnihilationElement algebraicCreationElement
  rw [← (ofStage n).map_mul, ← (ofStage n).map_mul,
    ← (ofStage n).map_add,
    InfoGeometry.Canonical.Cl11TensorTowerCrossSiteCAR.annihilation_creation_cross_site_anticommute
      n i j hij,
    (ofStage n).map_zero]

end InfoGeometry.Canonical.Cl11JordanWignerCARColimitBridge
