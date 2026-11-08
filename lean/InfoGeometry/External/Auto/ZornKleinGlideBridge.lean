import InfoGeometry.External.Auto.ZornScalingFlow
import InfoGeometry.Algebra.FiniteSpinAlgebra
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
The exact algebraic data available for a future affine Zorn/Klein action.  The
affine component reuses `TitsBruhatBrillouinKlein` verbatim.
-/
structure ZornKleinGlideData where
  sector_involutive : ∀ X : Zorn, sectorExchange (sectorExchange X) = X
  sector_norm : ∀ X : Zorn, zornNorm (sectorExchange X) = zornNorm X
  sector_mul : ∀ X Y : Zorn,
    sectorExchange (zornMul X Y) =
      zornMul (sectorExchange X) (sectorExchange Y)
  scale_reversal : ∀ (p : ℂˣ) (X : Zorn),
    sectorExchange (zornScale p X) = zornScale p⁻¹ (sectorExchange X)
  torus_reversal : ∀ (p q : ℂˣ) (X : Zorn),
    sectorExchange (torusFlow p q X) =
      torusFlow p⁻¹ q⁻¹ (sectorExchange X)
  affine_inverse :
    TitsBruhatBrillouinKlein.F * TitsBruhatBrillouinKlein.Finv =
      (1 : TitsBruhatBrillouinKlein.M3Q)
  glide_square :
    TitsBruhatBrillouinKlein.F * TitsBruhatBrillouinKlein.F =
      TitsBruhatBrillouinKlein.Tx
  klein_reversal :
    TitsBruhatBrillouinKlein.F * TitsBruhatBrillouinKlein.Ty *
        TitsBruhatBrillouinKlein.Finv =
      TitsBruhatBrillouinKlein.TyInv

/-- The canonical checked Zorn/Klein algebraic bridge data. -/
def canonicalZornKleinGlideData : ZornKleinGlideData where
  sector_involutive := sectorExchange_involutive
  sector_norm := sectorExchange_norm
  sector_mul := sectorExchange_zornMul
  scale_reversal := sectorExchange_zornScale
  torus_reversal := sectorExchange_torusFlow
  affine_inverse := TitsBruhatBrillouinKlein.F_mul_Finv
  glide_square := TitsBruhatBrillouinKlein.F_sq_eq_Tx
  klein_reversal := TitsBruhatBrillouinKlein.F_conj_Ty

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
    canonicalZornKleinGlideData.glide_square,
    canonicalZornKleinGlideData.klein_reversal⟩

end ZornKleinGlideBridge

end noncomputable section
