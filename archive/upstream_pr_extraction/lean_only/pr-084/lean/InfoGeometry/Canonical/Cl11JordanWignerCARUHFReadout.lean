import InfoGeometry.Canonical.Cl11JordanWignerCARColimitBridge
import InfoGeometry.Canonical.Cl11CuntzCantorChiralFramework

noncomputable section

namespace InfoGeometry.Canonical.Cl11JordanWignerCARUHFReadout

open InfoGeometry.Canonical.Cl11JordanWignerCARColimitBridge
open InfoGeometry.Canonical.Cl11CuntzCantorChiralFramework
open InfoGeometry.Canonical.CliffordCARGeneratorTopological
open InfoGeometry.Canonical.Cl11CuntzCantorChiralFramework.CarrierEquivalenceReadout

theorem commonCarrierEquiv_creation_last_sq (k : ℕ) :
    commonCarrierEquiv
        (algebraicCreationElement (k + 1) ⟨k, Nat.lt_succ_self k⟩) *
      commonCarrierEquiv
        (algebraicCreationElement (k + 1) ⟨k, Nat.lt_succ_self k⟩) = 0 := by
  rw [← map_mul, algebraicCreationElement_last_sq, map_zero]

theorem commonCarrierEquiv_annihilation_last_sq (k : ℕ) :
    commonCarrierEquiv
        (algebraicAnnihilationElement (k + 1) ⟨k, Nat.lt_succ_self k⟩) *
      commonCarrierEquiv
        (algebraicAnnihilationElement (k + 1) ⟨k, Nat.lt_succ_self k⟩) = 0 := by
  rw [← map_mul, algebraicAnnihilationElement_last_sq, map_zero]

theorem commonCarrierEquiv_last_CAR (k : ℕ) :
    commonCarrierEquiv
        (algebraicAnnihilationElement (k + 1) ⟨k, Nat.lt_succ_self k⟩) *
        commonCarrierEquiv
          (algebraicCreationElement (k + 1) ⟨k, Nat.lt_succ_self k⟩) +
      commonCarrierEquiv
        (algebraicCreationElement (k + 1) ⟨k, Nat.lt_succ_self k⟩) *
        commonCarrierEquiv
          (algebraicAnnihilationElement (k + 1) ⟨k, Nat.lt_succ_self k⟩) = 1 := by
  rw [← map_mul, ← map_mul, ← map_add,
    algebraicAnnihilationElement_last_creationElement_last_anticomm,
    map_one]

/-! The full indexed CAR law is read out in the common UHF carrier. -/

theorem commonCarrierEquiv_creation_annihilation_anticommutator
    (n : ℕ) (i j : Fin n) :
    commonCarrierEquiv (algebraicAnnihilationElement n i) *
          commonCarrierEquiv (algebraicCreationElement n j) +
        commonCarrierEquiv (algebraicCreationElement n j) *
          commonCarrierEquiv (algebraicAnnihilationElement n i) =
      if i = j then 1 else 0 := by
  rw [← map_mul, ← map_mul, ← map_add,
    algebraicAnnihilationElement_creationElement_anticommutator]
  by_cases hij : i = j <;> simp [hij]

theorem commonCarrierEquiv_creation_cross_site_anticommute
    (n : ℕ) (i j : Fin n) (hij : i ≠ j) :
    commonCarrierEquiv (algebraicCreationElement n i) *
          commonCarrierEquiv (algebraicCreationElement n j) +
        commonCarrierEquiv (algebraicCreationElement n j) *
          commonCarrierEquiv (algebraicCreationElement n i) = 0 := by
  rw [← map_mul, ← map_mul, ← map_add,
    algebraicCreationElement_cross_site_anticommute n i j hij,
    map_zero]

theorem commonCarrierEquiv_annihilation_cross_site_anticommute
    (n : ℕ) (i j : Fin n) (hij : i ≠ j) :
    commonCarrierEquiv (algebraicAnnihilationElement n i) *
          commonCarrierEquiv (algebraicAnnihilationElement n j) +
        commonCarrierEquiv (algebraicAnnihilationElement n j) *
          commonCarrierEquiv (algebraicAnnihilationElement n i) = 0 := by
  rw [← map_mul, ← map_mul, ← map_add,
    algebraicAnnihilationElement_cross_site_anticommute n i j hij,
    map_zero]

theorem commonCarrierEquiv_creation_annihilation_cross_site_anticommute
    (n : ℕ) (i j : Fin n) (hij : i ≠ j) :
    commonCarrierEquiv (algebraicCreationElement n i) *
          commonCarrierEquiv (algebraicAnnihilationElement n j) +
        commonCarrierEquiv (algebraicAnnihilationElement n j) *
          commonCarrierEquiv (algebraicCreationElement n i) = 0 := by
  rw [← map_mul, ← map_mul, ← map_add,
    algebraicCreationElement_annihilationElement_cross_site_anticommute n i j hij,
    map_zero]

theorem commonCarrierEquiv_annihilation_creation_cross_site_anticommute
    (n : ℕ) (i j : Fin n) (hij : i ≠ j) :
    commonCarrierEquiv (algebraicAnnihilationElement n i) *
          commonCarrierEquiv (algebraicCreationElement n j) +
        commonCarrierEquiv (algebraicCreationElement n j) *
          commonCarrierEquiv (algebraicAnnihilationElement n i) = 0 := by
  rw [← map_mul, ← map_mul, ← map_add,
    algebraicAnnihilationElement_creationElement_cross_site_anticommute n i j hij,
    map_zero]

theorem commonCarrierEquiv_cross_site_CAR_profile
    (n : ℕ) (i j : Fin n) (hij : i ≠ j) :
    commonCarrierEquiv (algebraicCreationElement n i) *
          commonCarrierEquiv (algebraicCreationElement n j) +
        commonCarrierEquiv (algebraicCreationElement n j) *
          commonCarrierEquiv (algebraicCreationElement n i) = 0 ∧
      commonCarrierEquiv (algebraicAnnihilationElement n i) *
          commonCarrierEquiv (algebraicAnnihilationElement n j) +
        commonCarrierEquiv (algebraicAnnihilationElement n j) *
          commonCarrierEquiv (algebraicAnnihilationElement n i) = 0 ∧
      commonCarrierEquiv (algebraicCreationElement n i) *
          commonCarrierEquiv (algebraicAnnihilationElement n j) +
        commonCarrierEquiv (algebraicAnnihilationElement n j) *
          commonCarrierEquiv (algebraicCreationElement n i) = 0 ∧
      commonCarrierEquiv (algebraicAnnihilationElement n i) *
          commonCarrierEquiv (algebraicCreationElement n j) +
        commonCarrierEquiv (algebraicCreationElement n j) *
          commonCarrierEquiv (algebraicAnnihilationElement n i) = 0 := by
  exact ⟨commonCarrierEquiv_creation_cross_site_anticommute n i j hij,
    commonCarrierEquiv_annihilation_cross_site_anticommute n i j hij,
    commonCarrierEquiv_creation_annihilation_cross_site_anticommute n i j hij,
    commonCarrierEquiv_annihilation_creation_cross_site_anticommute n i j hij⟩

end InfoGeometry.Canonical.Cl11JordanWignerCARUHFReadout
