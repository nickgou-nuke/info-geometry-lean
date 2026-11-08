/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.KitaevSpinorSolder

/-! Nonzero indefinite-selfadjoint nilpotents from actual fixed spinors.
The constant spinor witnesses that the construction is not vacuous. -/
noncomputable section
namespace InfoGeometry.Canonical.KitaevNullSolderWitness
open Matrix
open InfoGeometry.CliffordWeyl.SpinorBilinearSoldering
open KitaevConcreteBoundary KitaevBoundaryDiracPair KitaevSpinorSolder
open CARMajoranaFiniteBridge

theorem solder_ne_zero {n : Type*} [Fintype n] [DecidableEq n]
    (J : Matrix n n ℂ) (hJ : J * J = 1) (x y : n → ℂ)
    (hx : x ≠ 0) (hy : y ≠ 0) : solder J x y ≠ 0 := by
  intro hz
  have he := congrArg (fun M : Matrix n n ℂ => M * J) hz
  rw [solder_eq_vecMulVec_mul, mul_assoc, hJ, mul_one, zero_mul] at he
  exact vecMulVec_ne_zero hx (by simpa only [ne_eq, star_eq_zero] using hy) he

theorem fixed_nonzero_solder (x : (Fin 2 × Fin 2) → ℂ) (hx : x ≠ 0)
    (hfix : (leftEndpoint (by decide) twoSiteOperators) *ᵥ x = x) :
    solder twoSiteKreinData.eta x x ≠ 0 ∧
    solder twoSiteKreinData.eta x x * solder twoSiteKreinData.eta x x = 0 ∧
    twoSiteKreinData.diracAdjoint (solder twoSiteKreinData.eta x x) =
      solder twoSiteKreinData.eta x x :=
  ⟨solder_ne_zero _ twoSiteKreinData.2.1 x x hx hx,
    fixed_spinor_solder_sq_zero x hfix, diracAdjoint_solder twoSiteKreinData x x⟩

theorem constant_spinor_fixed :
    (leftEndpoint (by decide) twoSiteOperators) *ᵥ (fun _ => (1 : ℂ)) =
      (fun _ => (1 : ℂ)) := by
  ext i
  rcases i with ⟨i, j⟩
  fin_cases i <;> fin_cases j <;>
    norm_num [leftEndpoint, twoSiteOperators, twoSiteMajorana,
      InfoGeometry.MajoranaPfaffianNaturalClosure.majorana1,
      InfoGeometry.MajoranaPfaffianNaturalClosure.splitPos,
      Matrix.mulVec, dotProduct, Fin.sum_univ_two, Fintype.sum_prod_type,
      Matrix.kronecker_apply]

theorem constant_spinor_solder_witness :
    let S := solder twoSiteKreinData.eta (fun _ => (1 : ℂ)) (fun _ => (1 : ℂ))
    S ≠ 0 ∧ S * S = 0 ∧ twoSiteKreinData.diracAdjoint S = S := by
  apply fixed_nonzero_solder _ _ constant_spinor_fixed
  intro h
  have he := congrFun h ((0 : Fin 2), (0 : Fin 2))
  norm_num at he

end InfoGeometry.Canonical.KitaevNullSolderWitness
