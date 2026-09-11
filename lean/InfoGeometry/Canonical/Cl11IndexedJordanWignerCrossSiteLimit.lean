import InfoGeometry.Canonical.Cl11TensorTowerCrossSiteCAR
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.Cl11IndexedJordanWignerDirectLimit

set_option autoImplicit false

namespace InfoGeometry.Canonical.Cl11IndexedJordanWignerCrossSiteLimit

noncomputable section

open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Clifford.Cl11TensorTowerLimit
open InfoGeometry.Canonical.Cl11TensorTowerCrossSiteCAR
open InfoGeometry.Canonical.Cl11IndexedJordanWignerDirectLimit

abbrev Limit := InfoGeometry.Clifford.Cl11TensorTowerLimit.Limit

theorem uImage_cross_site_anticommute
    (n : ℕ) (i j : Fin n) (hij : i ≠ j) :
    uImage i * uImage j + uImage j * uImage i = 0 := by
  rw [uImage, uImage]
  rw [← ofStage_mul, ← ofStage_mul, ← ofStage_add]
  simpa [u] using congrArg (ofStage n)
    (creation_cross_site_anticommute n i j hij)

theorem vImage_cross_site_anticommute
    (n : ℕ) (i j : Fin n) (hij : i ≠ j) :
    vImage i * vImage j + vImage j * vImage i = 0 := by
  rw [vImage, vImage]
  rw [← ofStage_mul, ← ofStage_mul, ← ofStage_add]
  simpa [v] using congrArg (ofStage n)
    (annihilation_cross_site_anticommute n i j hij)

theorem uImage_vImage_cross_site_anticommute
    (n : ℕ) (i j : Fin n) (hij : i ≠ j) :
    uImage i * vImage j + vImage j * uImage i = 0 := by
  rw [uImage, vImage]
  rw [← ofStage_mul, ← ofStage_mul, ← ofStage_add]
  simpa [u, v] using congrArg (ofStage n)
    (creation_annihilation_cross_site_anticommute n i j hij)

theorem vImage_uImage_cross_site_anticommute
    (n : ℕ) (i j : Fin n) (hij : i ≠ j) :
    vImage i * uImage j + uImage j * vImage i = 0 := by
  rw [vImage, uImage]
  rw [← ofStage_mul, ← ofStage_mul, ← ofStage_add]
  simpa [u, v] using congrArg (ofStage n)
    (annihilation_creation_cross_site_anticommute n i j hij)

theorem uImage_vImage_cross_site_CAR_profile
    (n : ℕ) (i j : Fin n) (hij : i ≠ j) :
    uImage i * uImage j + uImage j * uImage i = 0 ∧
      vImage i * vImage j + vImage j * vImage i = 0 ∧
      uImage i * vImage j + vImage j * uImage i = 0 ∧
      vImage i * uImage j + uImage j * vImage i = 0 := by
  exact ⟨uImage_cross_site_anticommute n i j hij,
    vImage_cross_site_anticommute n i j hij,
    uImage_vImage_cross_site_anticommute n i j hij,
    vImage_uImage_cross_site_anticommute n i j hij⟩

theorem cross_site_CAR_profile_representative_stable
    (n : ℕ) (i j : Fin n) (hij : i ≠ j) :
    (ofStage (n + 1) (u (n + 1) i.castSucc) *
        ofStage (n + 1) (u (n + 1) j.castSucc) +
      ofStage (n + 1) (u (n + 1) j.castSucc) *
        ofStage (n + 1) (u (n + 1) i.castSucc) = 0) ∧
      (ofStage (n + 1) (v (n + 1) i.castSucc) *
        ofStage (n + 1) (v (n + 1) j.castSucc) +
      ofStage (n + 1) (v (n + 1) j.castSucc) *
        ofStage (n + 1) (v (n + 1) i.castSucc) = 0) ∧
      (ofStage (n + 1) (u (n + 1) i.castSucc) *
        ofStage (n + 1) (v (n + 1) j.castSucc) +
      ofStage (n + 1) (v (n + 1) j.castSucc) *
        ofStage (n + 1) (u (n + 1) i.castSucc) = 0) ∧
      (ofStage (n + 1) (v (n + 1) i.castSucc) *
        ofStage (n + 1) (u (n + 1) j.castSucc) +
      ofStage (n + 1) (u (n + 1) j.castSucc) *
        ofStage (n + 1) (v (n + 1) i.castSucc) = 0) := by
  simpa [uImage_castSucc, vImage_castSucc] using
    uImage_vImage_cross_site_CAR_profile n i j hij

end

end InfoGeometry.Canonical.Cl11IndexedJordanWignerCrossSiteLimit
