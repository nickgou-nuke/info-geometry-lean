import proofs.KleinVectorLiftObstruction
import proofs.KleinUniversalAffineAction
import proofs.KleinOperatorAlgebraBundleCore
import Mathlib.LinearAlgebra.Matrix.Hermitian

/-!
# Observable Klein equivariance

The concrete six-state Pin lifts act projectively on states, but their inner
action on the full matrix algebra is an honest action.  This file derives the
observable Klein relation, inverse covariance, Hermitian preservation, and
the affine Hamiltonian path relation from the two generator covariance laws.
-/

noncomputable section
namespace KleinEquivariantHamiltonian

open KleinBrillouinBase
open KleinSixStateProjectiveMonodromy KleinVectorLiftObstruction
open KleinUniversalAffineAction ProjectiveUnitary6
open KleinOperatorAlgebraAssociatedQuotient

abbrev Matrix6 := Matrix (Fin 6) (Fin 6) ℂ

/-- Inner action of a concrete unitary matrix on observables. -/
def adjointAction (U : U6) (A : Matrix6) : Matrix6 :=
  U.1 * A * (U⁻¹).1

@[simp] theorem adjointAction_one (A : Matrix6) :
    adjointAction 1 A = A := by
  simp [adjointAction]

theorem adjointAction_mul (U V : U6) (A : Matrix6) :
    adjointAction (U * V) A = adjointAction U (adjointAction V A) := by
  simp only [adjointAction, Matrix.UnitaryGroup.mul_val, mul_inv_rev,
    Matrix.UnitaryGroup.inv_val]
  noncomm_ring

theorem adjointAction_inv_left (U : U6) (A : Matrix6) :
    adjointAction U⁻¹ (adjointAction U A) = A := by
  rw [← adjointAction_mul]
  simp

theorem adjointAction_inv_right (U : U6) (A : Matrix6) :
    adjointAction U (adjointAction U⁻¹ A) = A := by
  rw [← adjointAction_mul]
  simp

theorem adjointAction_add (U : U6) (A B : Matrix6) :
    adjointAction U (A + B) = adjointAction U A + adjointAction U B := by
  simp [adjointAction, Matrix.mul_add, Matrix.add_mul]

theorem adjointAction_smul (U : U6) (c : ℂ) (A : Matrix6) :
    adjointAction U (c • A) = c • adjointAction U A := by
  simp [adjointAction]

theorem adjointAction_mul_observable (U : U6) (A B : Matrix6) :
    adjointAction U (A * B) = adjointAction U A * adjointAction U B := by
  simp only [adjointAction, Matrix.UnitaryGroup.inv_val]
  have hunit := Matrix.UnitaryGroup.star_mul_self U
  symm
  calc
    U.1 * A * star U.1 * (U.1 * B * star U.1) =
        U.1 * A * (star U.1 * U.1) * (B * star U.1) := by
      simp only [Matrix.mul_assoc]
    _ = U.1 * A * (B * star U.1) := by
      rw [hunit]
      simp
    _ = U.1 * (A * B) * star U.1 := by
      simp [Matrix.mul_assoc]

@[simp] theorem adjointAction_zero (U : U6) : adjointAction U 0 = 0 := by
  simp [adjointAction]

@[simp] theorem adjointAction_one_observable (U : U6) :
    adjointAction U 1 = 1 := by
  simp [adjointAction]

/-- Conjugation by `U` as a native complex algebra equivalence. -/
def adjointAlgEquiv (U : U6) : Matrix6 ≃ₐ[ℂ] Matrix6 where
  toFun := adjointAction U
  invFun := adjointAction U⁻¹
  left_inv := adjointAction_inv_left U
  right_inv := adjointAction_inv_right U
  map_add' := adjointAction_add U
  map_mul' := adjointAction_mul_observable U
  commutes' c := by
    rw [Algebra.algebraMap_eq_smul_one, adjointAction_smul,
      adjointAction_one_observable]

theorem adjointAlgEquiv_mul (U V : U6) :
    adjointAlgEquiv (U * V) = adjointAlgEquiv U * adjointAlgEquiv V := by
  apply AlgEquiv.ext
  intro A
  exact adjointAction_mul U V A

/-- The unitary group acts honestly on the observable algebra. -/
def adjointRepresentation : U6 →* (Matrix6 ≃ₐ[ℂ] Matrix6) where
  toFun := adjointAlgEquiv
  map_one' := by ext A; simp [adjointAlgEquiv]
  map_mul' := adjointAlgEquiv_mul

/-- The concrete central Pin sign is invisible on every observable. -/
@[simp] theorem centralSign_adjointAction (A : Matrix6) :
    adjointAction centralSignU6 A = A := by
  simp [adjointAction, centralSignU6]

/-- Multiplying a state lift by the central Pin sign leaves its observable
action unchanged. -/
theorem centralSign_mul_adjointAction (U : U6) (A : Matrix6) :
    adjointAction (centralSignU6 * U) A = adjointAction U A := by
  rw [adjointAction_mul, centralSign_adjointAction]

/-- A Pin-refined Klein relation becomes the ordinary Klein relation under
the adjoint action.  The inverse relation is not assumed independently. -/
theorem pin_adjoint_klein_relation (Theta T : U6)
    (hpin : Theta * T * Theta⁻¹ = centralSignU6 * T⁻¹)
    (A : Matrix6) :
    adjointAction Theta (adjointAction T (adjointAction Theta⁻¹ A)) =
      adjointAction T⁻¹ A := by
  rw [← adjointAction_mul, ← adjointAction_mul, hpin,
    centralSign_mul_adjointAction]

/-- Concrete observable Klein relation for the original projective six-state
generators. -/
theorem concrete_pin_adjoint_klein_relation (omega : ℂ)
    (homega : omega ^ 2 + omega + 1 = 0) (A : Matrix6) :
    adjointAction (thetaU6 omega homega)
        (adjointAction (trialityU6 omega homega)
          (adjointAction (thetaU6 omega homega)⁻¹ A)) =
      adjointAction (trialityU6 omega homega)⁻¹ A :=
  pin_adjoint_klein_relation _ _ (concrete_pin_relation omega homega) A

theorem thetaU6_inv_val (omega : ℂ)
    (homega : omega ^ 2 + omega + 1 = 0) :
    ((thetaU6 omega homega)⁻¹ : U6).1 = reindexSix KleinSixStateBundle.theta := by
  have hself : (thetaU6 omega homega)⁻¹ = thetaU6 omega homega := by
    apply inv_eq_of_mul_eq_one_right
    apply Subtype.ext
    simp [thetaU6, ← map_mul, KleinSixStateBundle.theta_sq omega homega]
  exact congrArg Subtype.val hself

/-- The new native unitary adjoint action is literally the already packaged
operator-bundle transition after the concrete six-coordinate reindexing. -/
theorem adjointAction_theta_reindex (omega : ℂ)
    (homega : omega ^ 2 + omega + 1 = 0)
    (A : KleinOperatorAlgebraAssociatedQuotient.Operator) :
    adjointAction (thetaU6 omega homega) (reindexSix A) =
      reindexSix (operatorGlide A) := by
  simp only [adjointAction, thetaU6_inv_val omega homega]
  change reindexSix KleinSixStateBundle.theta * reindexSix A *
      reindexSix KleinSixStateBundle.theta = reindexSix (operatorGlide A)
  rw [← map_mul, ← map_mul]
  rfl

/-- Generator covariance under an invertible base transformation implies
covariance under its inverse. -/
theorem covariance_inverse {K : Type*} (f fInv : K → K)
    (hf_right : Function.RightInverse fInv f)
    (U : U6) (H : K → Matrix6)
    (hcov : ∀ k, H (f k) = adjointAction U (H k)) (k : K) :
    H (fInv k) = adjointAction U⁻¹ (H k) := by
  apply (adjointAlgEquiv U).injective
  change adjointAction U (H (fInv k)) =
    adjointAction U (adjointAction U⁻¹ (H k))
  rw [show adjointAction U (H (fInv k)) = H k by
    rw [← hcov (fInv k), hf_right k]]
  exact (adjointAction_inv_right U (H k)).symm

theorem glide_inverse_covariance (omega : ℂ)
    (homega : omega ^ 2 + omega + 1 = 0)
    (H : Cover → Matrix6)
    (hglide : ∀ k, H (glide k) =
      adjointAction (thetaU6 omega homega) (H k)) (k : Cover) :
    H (glideInv k) =
      adjointAction (thetaU6 omega homega)⁻¹ (H k) :=
  covariance_inverse glide glideInv glide_right_inverse
    (thetaU6 omega homega) H hglide k

theorem ty_left_inverse (k : Cover) : tyInv (ty k) = k := by
  apply Prod.ext <;> simp [ty, tyInv]

theorem ty_right_inverse (k : Cover) : ty (tyInv k) = k := by
  apply Prod.ext <;> simp [ty, tyInv]

theorem translation_inverse_covariance (omega : ℂ)
    (homega : omega ^ 2 + omega + 1 = 0)
    (H : Cover → Matrix6)
    (htranslation : ∀ k, H (ty k) =
      adjointAction (trialityU6 omega homega) (H k)) (k : Cover) :
    H (tyInv k) =
      adjointAction (trialityU6 omega homega)⁻¹ (H k) :=
  covariance_inverse ty tyInv ty_right_inverse
    (trialityU6 omega homega) H htranslation k

/-- The two generator covariance equations force the Klein path relation for
the Hamiltonian field; inverse covariance is derived, not postulated. -/
theorem hamiltonian_klein_path_consistency (omega : ℂ)
    (homega : omega ^ 2 + omega + 1 = 0)
    (H : Cover → Matrix6)
    (htranslation : ∀ k, H (ty k) =
      adjointAction (trialityU6 omega homega) (H k)) (k : Cover) :
    adjointAction (thetaU6 omega homega)
        (adjointAction (trialityU6 omega homega)
          (adjointAction (thetaU6 omega homega)⁻¹ (H k))) =
      H (tyInv k) := by
  rw [concrete_pin_adjoint_klein_relation]
  exact (translation_inverse_covariance omega homega H htranslation k).symm

/-- The same consistency theorem expressed entirely as values of the field
along the two affine Klein paths. -/
theorem hamiltonian_affine_klein_relation (omega : ℂ)
    (homega : omega ^ 2 + omega + 1 = 0)
    (H : Cover → Matrix6)
    (hglide : ∀ k, H (glide k) =
      adjointAction (thetaU6 omega homega) (H k))
    (htranslation : ∀ k, H (ty k) =
      adjointAction (trialityU6 omega homega) (H k)) (k : Cover) :
    H (glide (ty (glideInv k))) = H (tyInv k) := by
  calc
    H (glide (ty (glideInv k))) =
        adjointAction (thetaU6 omega homega) (H (ty (glideInv k))) :=
      hglide _
    _ = adjointAction (thetaU6 omega homega)
        (adjointAction (trialityU6 omega homega) (H (glideInv k))) := by
      rw [htranslation]
    _ = adjointAction (thetaU6 omega homega)
        (adjointAction (trialityU6 omega homega)
          (adjointAction (thetaU6 omega homega)⁻¹ (H k))) := by
      rw [glide_inverse_covariance omega homega H hglide]
    _ = H (tyInv k) :=
      hamiltonian_klein_path_consistency omega homega H htranslation k

/-- Unitary inner action preserves Hermitian observables. -/
theorem adjointAction_preserves_hermitian (U : U6) {A : Matrix6}
    (hA : A.IsHermitian) : (adjointAction U A).IsHermitian := by
  unfold Matrix.IsHermitian at hA ⊢
  unfold adjointAction
  simp only [Matrix.conjTranspose_mul, Matrix.UnitaryGroup.inv_val,
    Matrix.star_eq_conjTranspose]
  rw [Matrix.conjTranspose_conjTranspose, hA]
  simp [Matrix.mul_assoc]

theorem adjointAction_continuous (U : U6) :
    Continuous (adjointAction U) := by
  exact (continuous_const.mul continuous_id).mul continuous_const

/-- A continuous Hermitian field remains a continuous Hermitian field after
any fixed unitary change of frame. -/
theorem continuous_hermitian_adjoint_field {K : Type*} [TopologicalSpace K]
    (U : U6) (H : K → Matrix6) (hcont : Continuous H)
    (hherm : ∀ k, (H k).IsHermitian) :
    Continuous (fun k ↦ adjointAction U (H k)) ∧
      ∀ k, (adjointAction U (H k)).IsHermitian := by
  exact ⟨(adjointAction_continuous U).comp hcont,
    fun k ↦ adjointAction_preserves_hermitian U (hherm k)⟩

/-- Observable-level capstone: the original projective generators give an
honest Klein action, preserve the Hermitian locus, and preserve continuity. -/
theorem observable_klein_capstone (omega : ℂ)
    (homega : omega ^ 2 + omega + 1 = 0)
    (H : Cover → Matrix6) (hcont : Continuous H)
    (hherm : ∀ k, (H k).IsHermitian)
    (hglide : ∀ k, H (glide k) =
      adjointAction (thetaU6 omega homega) (H k))
    (htranslation : ∀ k, H (ty k) =
      adjointAction (trialityU6 omega homega) (H k)) :
    (∀ A, adjointAction (thetaU6 omega homega)
        (adjointAction (trialityU6 omega homega)
          (adjointAction (thetaU6 omega homega)⁻¹ A)) =
      adjointAction (trialityU6 omega homega)⁻¹ A) ∧
    (∀ k, H (glide (ty (glideInv k))) = H (tyInv k)) ∧
    Continuous H ∧ (∀ k, (H k).IsHermitian) := by
  exact ⟨concrete_pin_adjoint_klein_relation omega homega,
    hamiltonian_affine_klein_relation omega homega H hglide htranslation,
    hcont, hherm⟩

end KleinEquivariantHamiltonian
end noncomputable section
