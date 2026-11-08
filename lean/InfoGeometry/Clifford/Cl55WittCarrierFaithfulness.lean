import InfoGeometry.Clifford.Cl55WittReflectionPinBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Clifford.Clifford55

/-!
# Faithfulness of the split Witt coordinate carrier

The ten anisotropic Witt coordinate vectors determine every vector in
`V55`.  This is the uniqueness step needed when comparing orthogonal
actions by their values on the coordinate generators.
-/

theorem orthogonalGroup55_eq_one_of_fix_witt_coordinates
    (g : orthogonalGroup55)
    (he : ∀ i : Fin 5, (g : V55 ≃ₗ[ℝ] V55) (e_pos i) = e_pos i)
    (hf : ∀ i : Fin 5, (g : V55 ≃ₗ[ℝ] V55) (f_neg i) = f_neg i) :
    g = 1 := by
  apply Subtype.ext
  apply LinearEquiv.ext
  rintro ⟨x, y⟩
  have hx : (x, (0 : Fin 5 → ℝ)) =
      ∑ i : Fin 5, x i • e_pos i := by
    apply Prod.ext
    · funext j
      classical
      change x j =
        (LinearMap.fst ℝ (Fin 5 → ℝ) (Fin 5 → ℝ)
          (∑ i : Fin 5, x i • e_pos i)) j
      rw [map_sum]
      simp [e_pos]
    · change (0 : Fin 5 → ℝ) =
        LinearMap.snd ℝ (Fin 5 → ℝ) (Fin 5 → ℝ)
          (∑ i : Fin 5, x i • e_pos i)
      rw [map_sum]
      simp [e_pos]
  have hy : ((0 : Fin 5 → ℝ), y) =
      ∑ i : Fin 5, y i • f_neg i := by
    apply Prod.ext
    · change (0 : Fin 5 → ℝ) =
        LinearMap.fst ℝ (Fin 5 → ℝ) (Fin 5 → ℝ)
          (∑ i : Fin 5, y i • f_neg i)
      rw [map_sum]
      simp [f_neg]
    · funext j
      classical
      change y j =
        (LinearMap.snd ℝ (Fin 5 → ℝ) (Fin 5 → ℝ)
          (∑ i : Fin 5, y i • f_neg i)) j
      rw [map_sum]
      simp [f_neg]
  have hxy : (x, y) =
      (x, (0 : Fin 5 → ℝ)) + ((0 : Fin 5 → ℝ), y) := by
    apply Prod.ext <;> simp
  rw [hxy, map_add, hx, hy]
  simp only [map_sum, map_smul, he, hf]
  rfl

end InfoGeometry.Clifford.Clifford55
