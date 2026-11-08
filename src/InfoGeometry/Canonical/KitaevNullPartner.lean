/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.DiracNullPeirce
import InfoGeometry.Canonical.KitaevNullSolderWitness

/-! A closed normalized null pair for the constructed two-site Krein metric.
The partner is eta*x/4; the denominator is the computed positive square
of the constant vector, not an inverse of a null metric square. -/
noncomputable section
namespace InfoGeometry.Canonical.KitaevNullPartner
open Matrix KitaevConcreteBoundary SpinorialCore.Krein
open InfoGeometry.CliffordWeyl.SpinorBilinearSoldering
open KitaevNullSolderWitness DiracNullPeirce

def seed : (Fin 2 × Fin 2) → ℂ := fun _ => 1
def partner : (Fin 2 × Fin 2) → ℂ := (1/4 : ℂ) • (twoSiteKreinData.eta *ᵥ seed)

theorem seed_null : SpinorialCore.Krein.pairing twoSiteKreinData.eta seed seed = 0 :=
  KitaevSpinorReflection.fixed_spinor_is_null seed constant_spinor_fixed

theorem seed_partner : SpinorialCore.Krein.pairing twoSiteKreinData.eta seed partner = 1 := by
  have hp := positive_pairing_recovery twoSiteKreinData.eta twoSiteKreinData.2.1 seed seed
  have hn : star seed ⬝ᵥ seed = (4 : ℂ) := by
    norm_num [seed, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_two]
  unfold partner
  change (metricDual twoSiteKreinData.eta seed) ((1/4 : ℂ) • _) = 1
  rw [map_smul]
  change (1/4 : ℂ) * SpinorialCore.Krein.pairing twoSiteKreinData.eta seed
    (twoSiteKreinData.eta *ᵥ seed) = 1
  rw [hp, hn]
  norm_num

theorem partner_seed : SpinorialCore.Krein.pairing twoSiteKreinData.eta partner seed = 1 := by
  have hh : twoSiteKreinData.eta.IsHermitian := twoSiteKreinData.2.2.1
  have hf := hh.star_dotProduct_mulVec_comm seed partner
  change star (SpinorialCore.Krein.pairing twoSiteKreinData.eta seed partner) =
    SpinorialCore.Krein.pairing twoSiteKreinData.eta partner seed at hf
  simpa only [seed_partner, star_one] using hf.symm

theorem partner_null : SpinorialCore.Krein.pairing twoSiteKreinData.eta partner partner = 0 := by
  have hi : IsIsometry twoSiteKreinData.eta twoSiteKreinData.eta := by
    have hs : star twoSiteKreinData.eta = twoSiteKreinData.eta := twoSiteKreinData.2.2.1
    have hsq : twoSiteKreinData.eta * twoSiteKreinData.eta = 1 := twoSiteKreinData.2.1
    change star twoSiteKreinData.eta * twoSiteKreinData.eta * twoSiteKreinData.eta = _
    rw [hs, hsq, one_mul]
  unfold partner
  rw [pairing_scale, pairing_isometry _ _ hi, seed_null, mul_zero]

/-- Both nullity and cross-normalization are discharged by native vectors. -/
theorem native_reflexive_pair :
    let d := solder twoSiteKreinData.eta seed seed
    let b := solder twoSiteKreinData.eta partner partner
    d*d=0 ∧ b*b=0 ∧ d*b*d=d ∧ b*d*b=b :=
  ⟨null_solder_square _ _ seed_null, null_solder_square _ _ partner_null,
    solder_reflexive _ _ _ seed_partner partner_seed,
    solder_reflexive _ _ _ partner_seed seed_partner⟩

def nativeWeylUnit : CARMajoranaFiniteBridge.ChainOpˣ :=
  nullSolderWeylUnit _ seed partner seed_null partner_null seed_partner partner_seed

end InfoGeometry.Canonical.KitaevNullPartner
