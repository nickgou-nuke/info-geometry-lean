import InfoGeometry.External.Auto.ZornScalingFlow
import InfoGeometry.External.Auto.TitsBruhatBrillouinKlein

/-!
# Canonical Zorn sector exchange and the affine Klein glide

This module joins two independently verified algebraic layers:

* the canonical Zorn sector-exchange automorphism, which reverses the uniform
  scaling and determinant-one torus parameters;
* the existing rational affine glide, whose square is a longitudinal
  translation and which conjugates the transverse translation to its inverse.

The bridge deliberately does not claim that a quotient space, wallpaper
group, or physical CPT action has been constructed.  Such statements require a
chosen invariant lattice and an action bundling these two layers.
-/

noncomputable section

namespace ZornKleinGlideBridge

open InfoGeometry.External.Auto.ZornScalingFlow

/-! ## A paired Zorn/affine action -/

/-- A canonical Zorn element together with an affine homogeneous frame. -/
abbrev PairedState := Zorn × TitsBruhatBrillouinKlein.M3Q

/-- Sector exchange paired with the affine half-translation glide. -/
def pairedGlide (S : PairedState) : PairedState :=
  (sectorExchange S.1, TitsBruhatBrillouinKlein.F * S.2)

/-- The inverse paired glide. -/
def pairedGlideInv (S : PairedState) : PairedState :=
  (sectorExchange S.1, TitsBruhatBrillouinKlein.Finv * S.2)

/-- The full longitudinal translation on the affine component. -/
def pairedLongTranslation (S : PairedState) : PairedState :=
  (S.1, TitsBruhatBrillouinKlein.Tx * S.2)

/-- Torus evolution paired with transverse affine translation. -/
def pairedTransverse (p q : ℂˣ) (S : PairedState) : PairedState :=
  (torusFlow p q S.1, TitsBruhatBrillouinKlein.Ty * S.2)

/-- Parameter and affine inverse of the paired transverse evolution. -/
def pairedTransverseInv (p q : ℂˣ) (S : PairedState) : PairedState :=
  (torusFlow p⁻¹ q⁻¹ S.1, TitsBruhatBrillouinKlein.TyInv * S.2)

/-- The paired glide squares to the full longitudinal translation. -/
theorem pairedGlide_sq (S : PairedState) :
    pairedGlide (pairedGlide S) = pairedLongTranslation S := by
  apply Prod.ext
  · exact sectorExchange_involutive S.1
  · dsimp [pairedGlide, pairedLongTranslation]
    rw [← Matrix.mul_assoc, TitsBruhatBrillouinKlein.F_sq_eq_Tx]

/-- The displayed inverse is a right inverse of the paired glide. -/
theorem pairedGlide_mul_inv (S : PairedState) :
    pairedGlide (pairedGlideInv S) = S := by
  apply Prod.ext
  · exact sectorExchange_involutive S.1
  · dsimp [pairedGlide, pairedGlideInv]
    rw [← Matrix.mul_assoc, TitsBruhatBrillouinKlein.F_mul_Finv,
      Matrix.one_mul]

/-- The displayed inverse is also a left inverse of the paired glide. -/
theorem pairedGlideInv_mul (S : PairedState) :
    pairedGlideInv (pairedGlide S) = S := by
  have hFinvF :
      TitsBruhatBrillouinKlein.Finv * TitsBruhatBrillouinKlein.F =
        (1 : TitsBruhatBrillouinKlein.M3Q) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [TitsBruhatBrillouinKlein.Finv,
        TitsBruhatBrillouinKlein.F]
  apply Prod.ext
  · exact sectorExchange_involutive S.1
  · dsimp [pairedGlide, pairedGlideInv]
    rw [← Matrix.mul_assoc, hFinvF, Matrix.one_mul]

/--
The paired glide conjugates transverse torus/affine evolution to its inverse:
the Zorn parameters and the transverse translation are reversed together.
-/
theorem pairedGlide_conj_transverse (p q : ℂˣ) (S : PairedState) :
    pairedGlide (pairedTransverse p q (pairedGlideInv S)) =
      pairedTransverseInv p q S := by
  apply Prod.ext
  · dsimp [pairedGlide, pairedGlideInv, pairedTransverse, pairedTransverseInv]
    rw [sectorExchange_torusFlow, sectorExchange_involutive]
  · dsimp [pairedGlide, pairedGlideInv, pairedTransverse, pairedTransverseInv]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc,
      TitsBruhatBrillouinKlein.F_conj_Ty]

/--
The effective cyclotomic multiplier and affine Klein relations coexist in the
canonical bridge.  This is the precise finite statement proved here.
-/
theorem effective_cyclotomic_klein_relations
    (p : ℂˣ) (hp : (p : ℂ) ^ 6 = 1) :
    ((p : ℂ) ^ 2) ^ 3 = 1 ∧
    TitsBruhatBrillouinKlein.F * TitsBruhatBrillouinKlein.F =
      TitsBruhatBrillouinKlein.Tx ∧
    TitsBruhatBrillouinKlein.F * TitsBruhatBrillouinKlein.Ty *
        TitsBruhatBrillouinKlein.Finv =
      TitsBruhatBrillouinKlein.TyInv := by
  exact ⟨automorphic_zornScale_effective_cube_root p hp,
    TitsBruhatBrillouinKlein.F_sq_eq_Tx,
    TitsBruhatBrillouinKlein.F_conj_Ty⟩

end ZornKleinGlideBridge

end noncomputable section
