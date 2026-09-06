import proofs.AlgebraicCuntzQuotient
import proofs.PrimonCuntzTower
import proofs.ProjectiveWallpaperGaugePSA
import proofs.WallpaperHolographicSelectionRules

/-!
# Cuntz–p6m boundary conditions

Finite bridge between the prime-indexed Cuntz sectors and the hexagonal `p6m`
wallpaper data.

What is proved here is deliberately modest:

* the primon tower uses the finite prime entries `2, 3, 5`;
* the algebraic Cuntz carriers `O₂, O₃, O₅` exist as finite algebraic quotients;
* the wallpaper shadow distinguishes `pg` (glide/Klein) from `p6m` (hexagonal/color);
* the `p6m` layer has the projective counts `H² = 4`, `N = 16`.
-/

noncomputable section

namespace CuntzP6MBoundary

open AlgebraicCuntzQuotient

/-- The finite prime tower used as the lithographic resolution seed. -/
def primonPrimeTower : List ℕ := [2, 3, 5]

@[simp] theorem primonPrimeTower_length : primonPrimeTower.length = 3 := by
  simp [primonPrimeTower]

@[simp] theorem primonPrimeTower_has_2 : 2 ∈ primonPrimeTower := by decide
@[simp] theorem primonPrimeTower_has_3 : 3 ∈ primonPrimeTower := by decide
@[simp] theorem primonPrimeTower_has_5 : 5 ∈ primonPrimeTower := by decide

/-- Prime-indexed algebraic Cuntz carriers in the finite quotient model. -/
abbrev O2 := CuntzAlg ℂ (Fin 2)
abbrev O3 := CuntzAlg ℂ (Fin 3)
abbrev O5 := CuntzAlg ℂ (Fin 5)

/-- The three prime carriers are inhabited: each has at least the zero element. -/
theorem primon_cuntz_carriers_inhabited :
    Nonempty O2 ∧ Nonempty O3 ∧ Nonempty O5 := by
  exact ⟨⟨0⟩, ⟨0⟩, ⟨0⟩⟩

/-- The `p6m` projective cohomology exponent is four. -/
theorem p6m_H2Exponent :
    ProjectiveWallpaperGaugePSA.H2Exponent
        ProjectiveWallpaperGaugePSA.WallpaperGroup.p6m = 4 := by
  simpa using WallpaperHolographicSelectionRules.p6m_H2Exponent

/-- The `p6m` layer has sixteen non-equivalent projective symmetry actions. -/
theorem p6m_nonEquivalentPSACount :
    ProjectiveWallpaperGaugePSA.nonEquivalentPSACount
        ProjectiveWallpaperGaugePSA.WallpaperGroup.p6m = 16 := by
  simpa using WallpaperHolographicSelectionRules.p6m_nonEquivalentPSACount

/-- The glide and hexagonal wallpaper groups are distinct. -/
theorem pg_ne_p6m :
    ProjectiveWallpaperGaugePSA.WallpaperGroup.pg ≠
        ProjectiveWallpaperGaugePSA.WallpaperGroup.p6m := by
  exact WallpaperHolographicSelectionRules.pg_p6m_are_distinct

#check primonPrimeTower_length
#check primon_cuntz_carriers_inhabited

end CuntzP6MBoundary

end noncomputable section
