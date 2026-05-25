import Mathlib
import InfoGeometry.Canonical.SouriauCasimirInvariant

/-!
# InfoGeometry.Canonical.SouriauCasimirInvariantSL2Model

Concrete finite witness for the Souriau Casimir interface on an `sl(2, ℝ)`-style
carrier (implemented here as the ambient `2×2` real matrix space).

This file pays a concrete instantiation debt with minimal surface:

* concrete Lie/LieDual carriers (`Matrix (Fin 2) (Fin 2) ℝ`);
* concrete group (`PUnit`) and actions (`Ad = id`, `coAd = id`);
* concrete affine cocycle (`θ = 0`) with explicit cocycle proof;
* concrete `SouriauCasimirEntropyDatum` instance.
-/

noncomputable section

namespace InfoGeometry.Canonical.SouriauCasimirInvariantSL2Model

open InfoGeometry.Canonical.SouriauCasimirInvariant

abbrev SL2Lie : Type := Matrix (Fin 2) (Fin 2) ℝ
abbrev SL2Dual : Type := Matrix (Fin 2) (Fin 2) ℝ
abbrev G0 : Type := PUnit

abbrev zeroLinearMapSL2Dual : SL2Lie →ₗ[ℝ] (SL2Dual →ₗ[ℝ] SL2Dual) :=
  0

/-- Trivial affine coadjoint datum on the concrete `2×2` real matrix carrier. -/
def sl2AffineDatum :
    AffineCoadjointDatum ℝ G0 SL2Lie SL2Dual where
  Ad := fun _ => LinearMap.id
  coAd := fun _ => LinearMap.id
  theta := fun _ => 0
  Ad_one := rfl
  Ad_mul := by
    intro g h
    rfl
  coAd_one := rfl
  coAd_mul := by
    intro g h
    rfl
  theta_one := rfl
  theta_mul := by
    intro g h
    simp

/--
Concrete Souriau Casimir entropy datum on the same carrier with trivial
Legendre/Fenchel ingredients.
-/
def sl2EntropyDatum :
    SouriauCasimirEntropyDatum ℝ G0 SL2Lie SL2Dual where
  affine := sl2AffineDatum
  pair := fun Q ξ => (Q * ξ).trace
  entropy := fun _ => (0 : ℝ)
  massieu := fun _ => (0 : ℝ)
  betaOfHeat := fun _ => 0
  coadInf := 0
  Theta := 0
  entropy_legendre := by
    intro Q
    simp
  entropy_affineCoAd_invariant := by
    intro g Q
    simp
  entropy_generalizedCasimir_equation := by
    intro Q
    simp

/-- Readout: the cocycle law is concretely discharged. -/
theorem sl2_theta_mul
    (g h : G0) :
    sl2AffineDatum.theta (g * h) =
      sl2AffineDatum.theta g + sl2AffineDatum.coAd g (sl2AffineDatum.theta h) :=
  sl2AffineDatum.theta_mul g h

/-- Readout: entropy is affine-coadjoint invariant in the concrete witness. -/
theorem sl2_entropy_affine_invariant
    (g : G0) (Q : SL2Dual) :
    sl2EntropyDatum.entropy
      (sl2EntropyDatum.affine.affineCoAd g Q) =
    sl2EntropyDatum.entropy Q :=
  SouriauCasimirEntropyDatum.entropy_is_affine_coadjoint_invariant
    sl2EntropyDatum g Q

/-- Readout: generalized Casimir equation is concretely discharged. -/
theorem sl2_entropy_generalized_casimir
    (Q : SL2Dual) :
    sl2EntropyDatum.coadInf (sl2EntropyDatum.betaOfHeat Q) Q
      + sl2EntropyDatum.Theta (sl2EntropyDatum.betaOfHeat Q) = 0 :=
  SouriauCasimirEntropyDatum.entropy_is_generalized_casimir sl2EntropyDatum Q

end InfoGeometry.Canonical.SouriauCasimirInvariantSL2Model
