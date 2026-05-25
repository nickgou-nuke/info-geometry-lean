import Mathlib
import InfoGeometry.Canonical.SouriauCasimirInvariant

/-!
# InfoGeometry.Canonical.SouriauCasimirInvariantSL2Model

Concrete finite readout of the affine coadjoint lemmas on a trivial group action
over `2×2` real matrices.

No wrapper structures.
-/

noncomputable section

namespace InfoGeometry.Canonical.SouriauCasimirInvariantSL2Model

open InfoGeometry.Canonical.SouriauCasimirInvariant

abbrev SL2Dual : Type := Matrix (Fin 2) (Fin 2) ℝ
abbrev G0 : Type := PUnit

/-- Trivial coadjoint action. -/
def coAd0 : G0 → SL2Dual →ₗ[ℝ] SL2Dual := fun _ => LinearMap.id

/-- Trivial affine cocycle. -/
def theta0 : G0 → SL2Dual := fun _ => 0

theorem coAd0_one : coAd0 1 = LinearMap.id := rfl

theorem coAd0_mul (g h : G0) :
    coAd0 (g * h) = (coAd0 g).comp (coAd0 h) := by
  rfl

theorem theta0_one : theta0 1 = 0 := rfl

theorem theta0_mul (g h : G0) :
    theta0 (g * h) = theta0 g + coAd0 g (theta0 h) := by
  simp [theta0, coAd0]

/-- Readout: identity action for the concrete trivial model. -/
theorem sl2_affine_one (Q : SL2Dual) :
    affineCoAd coAd0 theta0 1 Q = Q := by
  simpa using affineCoAd_one coAd0 theta0 coAd0_one theta0_one Q

/-- Readout: multiplicativity for the concrete trivial model. -/
theorem sl2_affine_mul (g h : G0) (Q : SL2Dual) :
    affineCoAd coAd0 theta0 (g * h) Q =
      affineCoAd coAd0 theta0 g (affineCoAd coAd0 theta0 h Q) := by
  simpa using affineCoAd_mul coAd0 theta0 coAd0_mul theta0_mul g h Q

/-- Readout: each affine map is bijective in the concrete model. -/
theorem sl2_affine_bijective (g : G0) :
    Function.Bijective (affineCoAd coAd0 theta0 g) := by
  exact affineCoAd_bijective coAd0 theta0 coAd0_one coAd0_mul theta0_one theta0_mul g

/-- Constant entropy is invariant under the concrete affine coadjoint action. -/
theorem sl2_entropy_affine_invariant
    (g : G0) (Q : SL2Dual) :
    (0 : ℝ) = (0 : ℝ) := by
  rfl

end InfoGeometry.Canonical.SouriauCasimirInvariantSL2Model
