import proofs.KleinPresentedGroup
import proofs.KleinSixStateBundle

/-!
# Concrete projective Klein representation on the six-state fibre

This file instantiates the abstract presented Klein group with the concrete
sheet--colour glide and triality matrices.  The matrices are reindexed from
`Fin 2 × Fin 3` to `Fin 6`; no choice of basis is hidden in the quotient.
-/

noncomputable section
namespace KleinSixStateProjectiveMonodromy

open TwoSheetThreeColorWeyl
open KleinBottleSixfoldCyclotomic
open KleinSixStateBundle
open ProjectiveUnitary6
open KleinPresentedGroup

abbrev sixEquiv : (Fin 2 × Fin 3) ≃ Fin 6 := finProdFinEquiv

def reindexSix : M6C ≃ₐ[ℂ] Matrix (Fin 6) (Fin 6) ℂ :=
  Matrix.reindexAlgEquiv ℂ ℂ sixEquiv

@[simp] theorem reindexSix_conjTranspose (A : M6C) :
    reindexSix (Matrix.conjTranspose A) =
      Matrix.conjTranspose (reindexSix A) := by
  ext i j
  rfl

theorem theta_conjTranspose :
    Matrix.conjTranspose theta = theta := by
  ext ⟨s, a⟩ ⟨t, b⟩
  fin_cases s <;> fin_cases a <;> fin_cases t <;> fin_cases b <;>
    simp [theta, internalGlide, tensor, sheetFlip, colorReflection,
      Matrix.conjTranspose, Matrix.kroneckerMap_apply]

theorem triality_conjTranspose :
    Matrix.conjTranspose triality = triality ^ 5 := by
  rw [triality_fifth_formula]
  ext ⟨s, a⟩ ⟨t, b⟩
  fin_cases s <;> fin_cases a <;> fin_cases t <;> fin_cases b <;>
    simp [triality, sixfoldTriality, tensor, sheetGamma, sheetPlus,
      sheetMinus, colorShift, Matrix.conjTranspose,
      Matrix.kroneckerMap_apply, pow_two]

def thetaU6 (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0) : U6 :=
  ⟨reindexSix theta, by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
      ← reindexSix_conjTranspose]
    rw [← map_mul, theta_conjTranspose, theta_sq ω hω]
    exact map_one reindexSix⟩

def trialityU6 (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0) : U6 :=
  ⟨reindexSix triality, by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
      ← reindexSix_conjTranspose]
    rw [← map_mul, triality_conjTranspose, triality_mul_fifth ω hω]
    exact map_one reindexSix⟩

def centralSignU6 : U6 :=
  ⟨-(1 : Matrix (Fin 6) (Fin 6) ℂ), by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
    simp⟩

theorem centralSign_mem_center : centralSignU6 ∈ CenterU6 := by
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
      simp [thetaU6, ← map_mul, theta_sq ω hω]
    exact congrArg Subtype.val hu
  have hTInv :
      ((trialityU6 ω hω)⁻¹ : U6).1 =
        reindexSix (triality ^ 5) := by
    have hu : (trialityU6 ω hω)⁻¹ = (trialityU6 ω hω) ^ 5 := by
      apply inv_eq_of_mul_eq_one_right
      apply Subtype.ext
      change reindexSix triality * reindexSix triality ^ 5 = 1
      rw [← map_pow, ← map_mul, triality_mul_fifth ω hω]
      exact map_one reindexSix
    simpa [trialityU6] using congrArg Subtype.val hu
  rw [hThetaInv, hTInv]
  change reindexSix (theta * triality * theta) =
    -(1 : Matrix (Fin 6) (Fin 6) ℂ) * reindexSix (triality ^ 5)
  rw [theta_triality_theta ω hω]
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

end KleinSixStateProjectiveMonodromy
end noncomputable section
