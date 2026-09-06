import InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition

/-!
# Native calibrated reflections on the traceless Cartan plane

The two maps below are the simple short- and long-root reflections in the
native three-coordinate model.  Their restrictions preserve the traceless
Cartan plane and act on the already-defined short and long weight sets.
-/

noncomputable section

namespace InfoGeometry.Lie.CanonicalZornCartanRootReflections

open InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition
open InfoGeometry.Lie.SplitOctonionAxialCartanErlangen

def shortRepresentative : Fin 3 → ℝ := ![2 / 3, -(1 / 3), -(1 / 3)]

def longRepresentative : Fin 3 → ℝ := ![-1, 1, 0]

def euclideanNormSq (v : Fin 3 → ℝ) : ℝ := ∑ i : Fin 3, v i * v i

def euclideanInner (v w : Fin 3 → ℝ) : ℝ := ∑ i : Fin 3, v i * w i

def cartanPairing (v w : Fin 3 → ℝ) : ℝ :=
  2 * euclideanInner v w / euclideanNormSq v

theorem shortRepresentative_normSq :
    euclideanNormSq shortRepresentative = (2 / 3 : ℝ) := by
  simp [euclideanNormSq, shortRepresentative, Fin.sum_univ_three]
  norm_num

theorem longRepresentative_normSq :
    euclideanNormSq longRepresentative = (2 : ℝ) := by
  simp [euclideanNormSq, longRepresentative, Fin.sum_univ_three]
  norm_num

theorem short_long_inner :
    euclideanInner shortRepresentative longRepresentative = -1 := by
  simp [euclideanInner, shortRepresentative, longRepresentative, Fin.sum_univ_three]
  norm_num

theorem cartanPairing_short_long :
    cartanPairing shortRepresentative longRepresentative = -3 := by
  rw [cartanPairing, short_long_inner, shortRepresentative_normSq]
  norm_num

theorem cartanPairing_long_short :
    cartanPairing longRepresentative shortRepresentative = -1 := by
  simp [cartanPairing, euclideanInner, euclideanNormSq,
    shortRepresentative, longRepresentative, Fin.sum_univ_three]
  norm_num

def shortReflection : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ) where
  toFun x := ![
    (-1 / 3) * x 0 + (2 / 3) * x 1 + (2 / 3) * x 2,
    (2 / 3) * x 0 + (2 / 3) * x 1 + (-1 / 3) * x 2,
    (2 / 3) * x 0 + (-1 / 3) * x 1 + (2 / 3) * x 2]
  map_add' x y := by funext i; fin_cases i <;> simp <;> ring
  map_smul' a x := by funext i; fin_cases i <;> simp <;> ring

def longReflection : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ) where
  toFun x := ![x 1, x 0, x 2]
  map_add' x y := by funext i; fin_cases i <;> simp
  map_smul' a x := by funext i; fin_cases i <;> simp

theorem shortReflection_preserves_traceless (k : TracelessWeight) :
    ∑ i : Fin 3, shortReflection k.1 i = 0 := by
  have h : ∑ i : Fin 3, k.1 i = 0 := k.2
  have h' : k.1 0 + k.1 1 + k.1 2 = 0 := by
    simpa [Fin.sum_univ_three] using h
  rw [Fin.sum_univ_three]
  simp [shortReflection]
  linear_combination h'

theorem longReflection_preserves_traceless (k : TracelessWeight) :
    ∑ i : Fin 3, longReflection k.1 i = 0 := by
  have h : ∑ i : Fin 3, k.1 i = 0 := k.2
  have h' : k.1 0 + k.1 1 + k.1 2 = 0 := by
    simpa [Fin.sum_univ_three] using h
  rw [Fin.sum_univ_three]
  simp [longReflection]
  linear_combination h'

def shortReflectionOnCartan : TracelessWeight →ₗ[ℝ] TracelessWeight where
  toFun k := ⟨shortReflection k.1, shortReflection_preserves_traceless k⟩
  map_add' k l := by
    apply Subtype.ext
    funext i
    fin_cases i <;> simp [shortReflection] <;> ring
  map_smul' a k := by
    apply Subtype.ext
    funext i
    fin_cases i <;> simp [shortReflection]

def longReflectionOnCartan : TracelessWeight →ₗ[ℝ] TracelessWeight where
  toFun k := ⟨longReflection k.1, longReflection_preserves_traceless k⟩
  map_add' k l := by
    apply Subtype.ext
    funext i
    fin_cases i <;> simp [longReflection]
  map_smul' a k := by
    apply Subtype.ext
    funext i
    fin_cases i <;> simp [longReflection]

def weightPullback
    (s : TracelessWeight →ₗ[ℝ] TracelessWeight)
    (α : TracelessWeight →ₗ[ℝ] ℝ) : TracelessWeight →ₗ[ℝ] ℝ :=
  α.comp s

@[simp] theorem weightPullback_apply
    (s : TracelessWeight →ₗ[ℝ] TracelessWeight)
    (α : TracelessWeight →ₗ[ℝ] ℝ) (k : TracelessWeight) :
    weightPullback s α k = α (s k) := rfl

theorem weightPullback_neg
    (s : TracelessWeight →ₗ[ℝ] TracelessWeight)
    (α : TracelessWeight →ₗ[ℝ] ℝ) :
    weightPullback s (-α) = -weightPullback s α := by
  ext k
  simp [weightPullback]

theorem weightPullback_sub
    (s : TracelessWeight →ₗ[ℝ] TracelessWeight)
    (α β : TracelessWeight →ₗ[ℝ] ℝ) :
    weightPullback s (α - β) =
      weightPullback s α - weightPullback s β := by
  ext k
  simp [weightPullback]

theorem shortReflection_coordWeight (i : Fin 3) :
    weightPullback shortReflectionOnCartan (coordWeight i) =
      match i with
      | 0 => -coordWeight 0
      | 1 => -coordWeight 2
      | 2 => -coordWeight 1 := by
  fin_cases i <;>
    apply LinearMap.ext <;> intro k
  · have h : ∑ j : Fin 3, k.1 j = 0 := k.2
    rw [Fin.sum_univ_three] at h
    simp [weightPullback, shortReflectionOnCartan, shortReflection, coordWeight]
    linarith [h]
  · have h : ∑ j : Fin 3, k.1 j = 0 := k.2
    rw [Fin.sum_univ_three] at h
    simp [weightPullback, shortReflectionOnCartan, shortReflection, coordWeight]
    linarith [h]
  · have h : ∑ j : Fin 3, k.1 j = 0 := k.2
    rw [Fin.sum_univ_three] at h
    simp [weightPullback, shortReflectionOnCartan, shortReflection, coordWeight]
    linarith [h]

theorem longReflection_coordWeight (i : Fin 3) :
    weightPullback longReflectionOnCartan (coordWeight i) =
      match i with
      | 0 => coordWeight 1
      | 1 => coordWeight 0
      | 2 => coordWeight 2 := by
  fin_cases i <;>
    apply LinearMap.ext <;> intro k <;>
    simp [weightPullback, longReflectionOnCartan, longReflection, coordWeight]

theorem shortReflection_longSimpleWeight :
    weightPullback shortReflectionOnCartan (coordWeight 1 - coordWeight 0) =
      coordWeight 0 - coordWeight 2 := by
  apply LinearMap.ext
  intro k
  have h : ∑ j : Fin 3, k.1 j = 0 := k.2
  rw [Fin.sum_univ_three] at h
  simp [weightPullback, shortReflectionOnCartan, shortReflection, coordWeight]
  linarith [h]

theorem longReflection_shortSimpleWeight :
    weightPullback longReflectionOnCartan (coordWeight 0) = coordWeight 1 := by
  exact longReflection_coordWeight 0

private theorem neg_add_eq_sub (α β : TracelessWeight →ₗ[ℝ] ℝ) :
    -α + β = β - α := by
  ext k
  simp [sub_eq_add_neg]
  abel

private theorem neg_sub_neg_eq_sub (α β : TracelessWeight →ₗ[ℝ] ℝ) :
    (-α) - (-β) = β - α := by
  ext k
  simp [sub_eq_add_neg]
  abel

theorem shortReflection_mapsTo_shortRootWeights :
    Set.MapsTo (weightPullback shortReflectionOnCartan)
      shortRootWeights shortRootWeights := by
  intro α hα
  simp only [shortRootWeights, Set.mem_insert_iff, Set.mem_singleton_iff] at hα ⊢
  rcases hα with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [shortReflection_coordWeight]
    simp
  · rw [weightPullback_neg]
    rw [shortReflection_coordWeight]
    simp
  · rw [shortReflection_coordWeight]
    simp
  · rw [weightPullback_neg]
    rw [shortReflection_coordWeight]
    simp
  · rw [shortReflection_coordWeight]
    simp
  · rw [weightPullback_neg]
    rw [shortReflection_coordWeight]
    simp

theorem longReflection_mapsTo_shortRootWeights :
    Set.MapsTo (weightPullback longReflectionOnCartan)
      shortRootWeights shortRootWeights := by
  intro α hα
  simp only [shortRootWeights, Set.mem_insert_iff, Set.mem_singleton_iff] at hα ⊢
  rcases hα with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [longReflection_coordWeight]
    simp
  · rw [weightPullback_neg]
    rw [longReflection_coordWeight]
    simp
  · rw [longReflection_coordWeight]
    simp
  · rw [weightPullback_neg]
    rw [longReflection_coordWeight]
    simp
  · rw [longReflection_coordWeight]
    simp
  · rw [weightPullback_neg]
    rw [longReflection_coordWeight]
    simp

theorem shortReflection_mapsTo_longRootWeights :
    Set.MapsTo (weightPullback shortReflectionOnCartan)
      longRootWeights longRootWeights := by
  intro α hα
  simp only [longRootWeights, Set.mem_insert_iff, Set.mem_singleton_iff] at hα ⊢
  rcases hα with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [weightPullback_sub, shortReflection_coordWeight, shortReflection_coordWeight]
    simp only
    right; right; right; left
    exact neg_sub_neg_eq_sub _ _
  · rw [weightPullback_sub, shortReflection_coordWeight, shortReflection_coordWeight]
    simp only
    right; right; left
    exact neg_sub_neg_eq_sub _ _
  · rw [weightPullback_sub, shortReflection_coordWeight, shortReflection_coordWeight]
    simp only
    right; left
    exact neg_sub_neg_eq_sub _ _
  · rw [weightPullback_sub, shortReflection_coordWeight, shortReflection_coordWeight]
    simp only
    left
    exact neg_sub_neg_eq_sub _ _
  · rw [weightPullback_sub, shortReflection_coordWeight, shortReflection_coordWeight]
    simp only
    right; right; right; right; left
    exact neg_sub_neg_eq_sub _ _
  · rw [weightPullback_sub, shortReflection_coordWeight, shortReflection_coordWeight]
    simp only
    right; right; right; right; right
    exact neg_sub_neg_eq_sub _ _

theorem longReflection_mapsTo_longRootWeights :
    Set.MapsTo (weightPullback longReflectionOnCartan)
      longRootWeights longRootWeights := by
  intro α hα
  simp only [longRootWeights, Set.mem_insert_iff, Set.mem_singleton_iff] at hα ⊢
  rcases hα with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [weightPullback_sub, longReflection_coordWeight, longReflection_coordWeight]
    simp
  · rw [weightPullback_sub, longReflection_coordWeight, longReflection_coordWeight]
    simp
  · rw [weightPullback_sub, longReflection_coordWeight, longReflection_coordWeight]
    simp
  · rw [weightPullback_sub, longReflection_coordWeight, longReflection_coordWeight]
    simp
  · rw [weightPullback_sub, longReflection_coordWeight, longReflection_coordWeight]
    simp
  · rw [weightPullback_sub, longReflection_coordWeight, longReflection_coordWeight]
    simp

theorem shortReflection_mapsTo_allRootWeights :
    Set.MapsTo (weightPullback shortReflectionOnCartan)
      (shortRootWeights ∪ longRootWeights)
      (shortRootWeights ∪ longRootWeights) := by
  intro α hα
  rcases hα with hα | hα
  · exact Or.inl (shortReflection_mapsTo_shortRootWeights hα)
  · exact Or.inr (shortReflection_mapsTo_longRootWeights hα)

theorem longReflection_mapsTo_allRootWeights :
    Set.MapsTo (weightPullback longReflectionOnCartan)
      (shortRootWeights ∪ longRootWeights)
      (shortRootWeights ∪ longRootWeights) := by
  intro α hα
  rcases hα with hα | hα
  · exact Or.inl (longReflection_mapsTo_shortRootWeights hα)
  · exact Or.inr (longReflection_mapsTo_longRootWeights hα)

theorem shortReflection_sq :
    shortReflection.comp shortReflection = LinearMap.id := by
  ext x i
  fin_cases i <;>
    simp [shortReflection, LinearMap.comp_apply] <;>
    ring

theorem longReflection_sq :
    longReflection.comp longReflection = LinearMap.id := by
  ext x i
  fin_cases i <;>
    simp [longReflection, LinearMap.comp_apply]

theorem nativeCartanReflections_braid :
    (shortReflection.comp longReflection) ^ 3 =
      (longReflection.comp shortReflection) ^ 3 := by
  ext x i
  fin_cases i <;>
    simp [shortReflection, longReflection,
      LinearMap.comp_apply, pow_succ] <;>
    ring

theorem shortReflectionOnCartan_sq :
    shortReflectionOnCartan.comp shortReflectionOnCartan = LinearMap.id := by
  apply LinearMap.ext
  intro k
  apply Subtype.ext
  have h := congrArg (fun f : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ) => f k.1)
    shortReflection_sq
  simpa [shortReflectionOnCartan, LinearMap.comp_apply] using h

theorem longReflectionOnCartan_sq :
    longReflectionOnCartan.comp longReflectionOnCartan = LinearMap.id := by
  apply LinearMap.ext
  intro k
  apply Subtype.ext
  have h := congrArg (fun f : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ) => f k.1)
    longReflection_sq
  simpa [longReflectionOnCartan, LinearMap.comp_apply] using h

theorem nativeCartanReflectionsOnCartan_braid :
    (shortReflectionOnCartan.comp longReflectionOnCartan) ^ 3 =
      (longReflectionOnCartan.comp shortReflectionOnCartan) ^ 3 := by
  apply LinearMap.ext
  intro k
  apply Subtype.ext
  have h := congrArg (fun f : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ) => f k.1)
    nativeCartanReflections_braid
  simpa [shortReflectionOnCartan, longReflectionOnCartan,
    LinearMap.comp_apply, pow_succ] using h

theorem nativeCartanReflectionsOnCartan_order_six :
    (shortReflectionOnCartan.comp longReflectionOnCartan) ^ 6 = LinearMap.id := by
  apply LinearMap.ext
  intro k
  apply Subtype.ext
  ext i
  fin_cases i <;>
    simp [shortReflectionOnCartan, longReflectionOnCartan,
      shortReflection, longReflection, LinearMap.comp_apply, pow_succ] <;>
    ring

theorem shortReflection_image_allRootWeights :
    weightPullback shortReflectionOnCartan ''
        (shortRootWeights ∪ longRootWeights) =
      shortRootWeights ∪ longRootWeights := by
  apply Set.Subset.antisymm
  · exact shortReflection_mapsTo_allRootWeights.image_subset
  · intro α hα
    refine ⟨weightPullback shortReflectionOnCartan α,
      shortReflection_mapsTo_allRootWeights hα, ?_⟩
    ext k
    change α (shortReflectionOnCartan (shortReflectionOnCartan k)) = α k
    have hs := congrArg (fun f : TracelessWeight →ₗ[ℝ] TracelessWeight => f k)
      shortReflectionOnCartan_sq
    simpa [shortReflectionOnCartan, LinearMap.comp_apply] using congrArg α hs

theorem longReflection_image_allRootWeights :
    weightPullback longReflectionOnCartan ''
        (shortRootWeights ∪ longRootWeights) =
      shortRootWeights ∪ longRootWeights := by
  apply Set.Subset.antisymm
  · exact longReflection_mapsTo_allRootWeights.image_subset
  · intro α hα
    refine ⟨weightPullback longReflectionOnCartan α,
      longReflection_mapsTo_allRootWeights hα, ?_⟩
    ext k
    change α (longReflectionOnCartan (longReflectionOnCartan k)) = α k
    have hs := congrArg (fun f : TracelessWeight →ₗ[ℝ] TracelessWeight => f k)
      longReflectionOnCartan_sq
    simpa [longReflectionOnCartan, LinearMap.comp_apply] using congrArg α hs

end InfoGeometry.Lie.CanonicalZornCartanRootReflections
