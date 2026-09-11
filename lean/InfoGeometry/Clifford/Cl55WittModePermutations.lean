import InfoGeometry.Clifford.Cl55WittOrthogonalReflections
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Clifford.Cl55WittReflectionSubgroup

namespace InfoGeometry.Clifford.Clifford55

noncomputable def modeReindex (σ : Equiv.Perm (Fin 5)) :
    (Fin 5 → ℝ) ≃ₗ[ℝ] (Fin 5 → ℝ) where
  toFun f i := f (σ.symm i)
  invFun f i := f (σ i)
  left_inv f := by
    funext i
    simp
  right_inv f := by
    funext i
    simp
  map_add' f g := by
    funext i
    simp
  map_smul' r f := by
    funext i
    simp

noncomputable def modePermutationLinearEquiv (σ : Equiv.Perm (Fin 5)) :
    V55 ≃ₗ[ℝ] V55 :=
  LinearEquiv.prodCongr (modeReindex σ) (modeReindex σ)

@[simp] theorem modePermutationLinearEquiv_apply
    (σ : Equiv.Perm (Fin 5)) (x : V55) :
    modePermutationLinearEquiv σ x =
      (fun i => x.1 (σ.symm i), fun i => x.2 (σ.symm i)) := rfl

theorem modePermutation_preserves_Q55
    (σ : Equiv.Perm (Fin 5)) (x : V55) :
    Q55 (modePermutationLinearEquiv σ x) = Q55 x := by
  simp only [Q55_apply, modePermutationLinearEquiv_apply]
  rw [show (∑ i, x.1 (σ.symm i) ^ 2) = ∑ i, x.1 i ^ 2 by
    exact Equiv.sum_comp σ.symm (fun i => x.1 i ^ 2)]
  rw [show (∑ i, x.2 (σ.symm i) ^ 2) = ∑ i, x.2 i ^ 2 by
    exact Equiv.sum_comp σ.symm (fun i => x.2 i ^ 2)]

noncomputable def modePermutationIsometry (σ : Equiv.Perm (Fin 5)) :
    Q55.IsometryEquiv Q55 where
  __ := modePermutationLinearEquiv σ
  map_app' := modePermutation_preserves_Q55 σ

@[simp] theorem modePermutationIsometry_apply
    (σ : Equiv.Perm (Fin 5)) (x : V55) :
    modePermutationIsometry σ x = modePermutationLinearEquiv σ x := rfl

noncomputable def modePermutationAlg (σ : Equiv.Perm (Fin 5)) :
    Cl55 ≃ₐ[ℝ] Cl55 :=
  CliffordAlgebra.equivOfIsometry (modePermutationIsometry σ)

theorem modePermutationAlg_apply_ι
    (σ : Equiv.Perm (Fin 5)) (x : V55) :
    modePermutationAlg σ (ι55 x) =
      ι55 (modePermutationLinearEquiv σ x) := by
  simp [modePermutationAlg]

theorem modePermutationLinearEquiv_symm (σ : Equiv.Perm (Fin 5)) :
    (modePermutationLinearEquiv σ).symm =
      modePermutationLinearEquiv σ.symm := by
  apply LinearEquiv.ext
  intro x
  apply Prod.ext <;> funext i
  · change x.1 (σ i) = x.1 ((σ.symm).symm i)
    simp
  · change x.2 (σ i) = x.2 ((σ.symm).symm i)
    simp

theorem modePermutationLinearEquiv_mul (σ τ : Equiv.Perm (Fin 5)) :
    modePermutationLinearEquiv (σ * τ) =
      modePermutationLinearEquiv σ * modePermutationLinearEquiv τ := by
  apply LinearEquiv.ext
  intro x
  apply Prod.ext <;> funext i
  · change x.1 ((σ * τ).symm i) = x.1 (τ.symm (σ.symm i))
    rw [Equiv.Perm.mul_def]
    rfl
  · change x.2 ((σ * τ).symm i) = x.2 (τ.symm (σ.symm i))
    rw [Equiv.Perm.mul_def]
    rfl

noncomputable def modePermutationOrthogonal
    (σ : Equiv.Perm (Fin 5)) : orthogonalGroup55 :=
  ⟨modePermutationLinearEquiv σ, modePermutation_preserves_Q55 σ⟩

theorem modePermutationOrthogonal_apply
    (σ : Equiv.Perm (Fin 5)) (x : V55) :
    (modePermutationOrthogonal σ : V55 ≃ₗ[ℝ] V55) x =
      modePermutationLinearEquiv σ x := rfl

noncomputable def modePermutationOrthogonalHom :
    Equiv.Perm (Fin 5) →* orthogonalGroup55 where
  toFun := modePermutationOrthogonal
  map_one' := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    rfl
  map_mul' σ τ := by
    apply Subtype.ext
    exact modePermutationLinearEquiv_mul σ τ

end InfoGeometry.Clifford.Clifford55
