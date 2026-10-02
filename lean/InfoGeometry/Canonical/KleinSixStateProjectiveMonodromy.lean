import InfoGeometry.Canonical.KleinPresentedGroup
import InfoGeometry.Canonical.KleinSixStateBundle

/-!
# Concrete projective Klein representation on the six-state fibre

This file instantiates the abstract presented Klein group with the concrete
sheet--colour glide and triality matrices.  The matrices are reindexed from
`Fin 2 × Fin 3` to `Fin 6`; no choice of basis is hidden in the quotient.
-/

noncomputable section
namespace InfoGeometry.Canonical.KleinSixStateProjectiveMonodromy

open TwoSheetThreeColorWeyl
open KleinSixStateBundle
open ProjectiveUnitary6
open KleinPresentedGroup

abbrev sixEquiv : (Fin 2 × Fin 3) ≃ Fin 6 := finProdFinEquiv

def reindexSix : KleinSixStateBundle.Mat23C ≃ₐ[ℂ] Matrix (Fin 6) (Fin 6) ℂ :=
  Matrix.reindexAlgEquiv ℂ ℂ sixEquiv

@[simp] theorem reindexSix_conjTranspose (A : KleinSixStateBundle.Mat23C) :
    reindexSix (Matrix.conjTranspose A) =
      Matrix.conjTranspose (reindexSix A) := by
  ext i j
  rfl

theorem theta_conjTranspose :
    Matrix.conjTranspose theta = theta := by
  ext ⟨s, a⟩ ⟨t, b⟩
  fin_cases s <;> fin_cases a <;> fin_cases t <;> fin_cases b <;>
    simp [theta, sheetExchange, colorReflection,
      Matrix.conjTranspose, Matrix.kroneckerMap_apply]

theorem triality_conjTranspose :
    Matrix.conjTranspose triality = triality ^ 5 := by
  rw [triality_fifth_formula]
  ext ⟨s, a⟩ ⟨t, b⟩
  fin_cases s <;> fin_cases a <;> fin_cases t <;> fin_cases b <;>
    simp [triality, sheetParity, uPlus,
      uMinus, colorShift, Matrix.conjTranspose,
      Matrix.kroneckerMap_apply, pow_two]

theorem triality_mul_fifth : triality * triality ^ 5 = 1 := by
  have color_inverse : colorShift * colorShift ^ 2 = 1 := by
    simpa only [← pow_succ'] using colorShift_cubed
  rw [triality_fifth_formula, triality, kronecker_mul,
    sheetParity_sq, color_inverse]
  simp

def thetaU6 (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0) : U6 :=
  ⟨reindexSix theta, by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
      ← reindexSix_conjTranspose]
    rw [← map_mul, theta_conjTranspose, ← pow_two, theta_sq]
    exact map_one reindexSix⟩

def trialityU6 (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0) : U6 :=
  ⟨reindexSix triality, by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
      ← reindexSix_conjTranspose]
    rw [← map_mul, triality_conjTranspose, triality_mul_fifth]
    exact map_one reindexSix⟩

def centralSignU6 : U6 :=
  ⟨-(1 : Matrix (Fin 6) (Fin 6) ℂ), by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
    simp⟩

theorem centralSign_mem_center : centralSignU6 ∈ centerU6 := by
  rw [Subgroup.mem_center_iff]
  intro A
  apply Subtype.ext
  simp [centralSignU6]

theorem concrete_pin_relation (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0) :
    thetaU6 ω hω * trialityU6 ω hω * (thetaU6 ω hω)⁻¹ =
      centralSignU6 * (trialityU6 ω hω)⁻¹ := by
  apply Subtype.ext
  change reindexSix theta * reindexSix triality *
      ((thetaU6 ω hω)⁻¹ : U6).1 =
    (centralSignU6 : Matrix (Fin 6) (Fin 6) ℂ) *
      ((trialityU6 ω hω)⁻¹ : U6).1
  have hThetaInv :
      ((thetaU6 ω hω)⁻¹ : U6).1 = reindexSix theta := by
    have hu : (thetaU6 ω hω)⁻¹ = thetaU6 ω hω := by
      apply inv_eq_of_mul_eq_one_right
      apply Subtype.ext
      change reindexSix theta * reindexSix theta = 1
      rw [← map_mul, ← pow_two, theta_sq]
      exact map_one reindexSix
    exact congrArg Subtype.val hu
  have hTInv :
      ((trialityU6 ω hω)⁻¹ : U6).1 =
        reindexSix (triality ^ 5) := by
    have hu : (trialityU6 ω hω)⁻¹ = (trialityU6 ω hω) ^ 5 := by
      apply inv_eq_of_mul_eq_one_right
      apply Subtype.ext
      change reindexSix triality * reindexSix triality ^ 5 = 1
      rw [← map_pow, ← map_mul, triality_mul_fifth]
      exact map_one reindexSix
    simpa [trialityU6] using congrArg Subtype.val hu
  rw [hThetaInv, hTInv]
  change reindexSix theta * reindexSix triality * reindexSix theta =
    -(1 : Matrix (Fin 6) (Fin 6) ℂ) * reindexSix (triality ^ 5)
  rw [← map_mul, ← map_mul, theta_triality_theta]
  simp

/-- The concrete algebraic projective representation of the presented Klein
group on the six-state fibre. -/
def concreteKleinProjectiveRep (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0) :
    KleinPresentedGroup.KleinGroup →* PU6 :=
  kleinProjectiveRep (thetaU6 ω hω) (trialityU6 ω hω) centralSignU6
    centralSign_mem_center (concrete_pin_relation ω hω)

theorem concreteKleinProjectiveRep_generators
    (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0) :
    concreteKleinProjectiveRep ω hω (toKlein genA) = toPU6 (thetaU6 ω hω) ∧
    concreteKleinProjectiveRep ω hω (toKlein genB) = toPU6 (trialityU6 ω hω) := by
  exact klein_projective_rep_generators _ _ _ centralSign_mem_center
    (concrete_pin_relation ω hω)

end InfoGeometry.Canonical.KleinSixStateProjectiveMonodromy
end noncomputable section
