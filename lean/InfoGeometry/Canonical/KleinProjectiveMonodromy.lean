import InfoGeometry.Canonical.KleinPresentedGroup
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.KleinSixStateBundle

/-!
# Concrete projective Klein representation on the six-state fibre

This file instantiates the abstract presented Klein group with the concrete
sheet--colour glide and triality matrices.  The matrices are reindexed from
`Fin 2 × Fin 3` to `Fin 6`; no choice of basis is hidden in the quotient.
-/

noncomputable section
namespace InfoGeometry.Canonical.KleinProjectiveMonodromy

open TwoSheetThreeColorWeyl
open KleinSixStateBundle
open ProjectiveUnitary6
open KleinPresentedGroup

abbrev sixEquiv : (Fin 2 × Fin 3) ≃ Fin 6 := finProdFinEquiv

def reindexSix : TwoSheetThreeColorWeyl.Mat23C ≃ₐ[ℂ] Matrix (Fin 6) (Fin 6) ℂ :=
  Matrix.reindexAlgEquiv ℂ ℂ sixEquiv

@[simp] theorem reindexSix_conjTranspose (A : TwoSheetThreeColorWeyl.Mat23C) :
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

def thetaU6 (ω : ℂ) (_hω : ω ^ 2 + ω + 1 = 0) : U6 :=
  ⟨reindexSix theta, by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
      ← reindexSix_conjTranspose]
    rw [← map_mul, theta_conjTranspose]
    have h2 : theta * theta = 1 := by
      calc
        theta * theta = theta ^ 2 := by simp [pow_two]
        _ = 1 := theta_sq
    rw [h2]
    exact map_one reindexSix⟩

def trialityU6 (ω : ℂ) (_hω : ω ^ 2 + ω + 1 = 0) : U6 :=
  ⟨reindexSix triality, by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
      ← reindexSix_conjTranspose]
    rw [← map_mul, triality_conjTranspose]
    have h6 : triality * triality ^ 5 = 1 := by
      calc
        triality * triality ^ 5 = triality ^ 6 := by rw [← pow_succ']
        _ = sixTriality ^ 6 := rfl
        _ = 1 := sixTriality_sixth
    rw [h6]
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
      have hmul : ((thetaU6 ω hω) * (thetaU6 ω hω)).1 = reindexSix theta * reindexSix theta := rfl
      rw [hmul, ← map_mul]
      have h2 : theta * theta = 1 := by
        calc
          theta * theta = theta ^ 2 := by simp [pow_two]
          _ = 1 := theta_sq
      rw [h2, map_one]
      rfl
    exact congrArg Subtype.val hu
  have hTInv :
      ((trialityU6 ω hω)⁻¹ : U6).1 =
        reindexSix (triality ^ 5) := by
    have hu : (trialityU6 ω hω)⁻¹ = (trialityU6 ω hω) ^ 5 := by
      apply inv_eq_of_mul_eq_one_right
      apply Subtype.ext
      have hmul : ((trialityU6 ω hω) * (trialityU6 ω hω) ^ 5).1 = reindexSix triality * reindexSix (triality ^ 5) := by
        simp [trialityU6, pow_succ]
      rw [hmul, ← map_mul]
      have h6 : triality * triality ^ 5 = 1 := by
        calc
          triality * triality ^ 5 = triality ^ 6 := by rw [← pow_succ']
          _ = sixTriality ^ 6 := rfl
          _ = 1 := sixTriality_sixth
      rw [h6, map_one]
      rfl
    have hpow : ((trialityU6 ω hω) ^ 5).1 = reindexSix (triality ^ 5) := by
      change (reindexSix triality) ^ 5 = reindexSix (triality ^ 5)
      rw [← map_pow]
    rw [hu, hpow]
  rw [hThetaInv, hTInv]
  change reindexSix (theta * triality * theta) =
    -(1 : Matrix (Fin 6) (Fin 6) ℂ) * reindexSix (triality ^ 5)
  rw [theta_triality_theta]
  simp

/-- The concrete algebraic projective representation of the presented Klein
group on the six-state fibre. -/
def concreteKleinProjectiveRep (ω : ℂ) (_hω : ω ^ 2 + ω + 1 = 0) :
    KleinGroup →* PU6 :=
  kleinProjectiveRep (thetaU6 ω _hω) (trialityU6 ω _hω) centralSignU6
    centralSign_mem_center (concrete_pin_relation ω _hω)

theorem concreteKleinProjectiveRep_generators
    (ω : ℂ) (_hω : ω ^ 2 + ω + 1 = 0) :
    concreteKleinProjectiveRep ω _hω (toKlein genA) = toPU6 (thetaU6 ω _hω) ∧
    concreteKleinProjectiveRep ω _hω (toKlein genB) = toPU6 (trialityU6 ω _hω) := by
  exact klein_projective_rep_generators _ _ _ centralSign_mem_center
    (concrete_pin_relation ω _hω)

end InfoGeometry.Canonical.KleinProjectiveMonodromy
end noncomputable section
