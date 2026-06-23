noncomputable section
import Mathlib.CategoryTheory.Filtered.Basic
namespace Test
instance : IsFiltered ℕ where
  ⟨⟨0⟩,
    fun m n => ⟨max m n, by exact le_max_left _ _, by exact le_max_right _ _⟩,
    fun {m n} (f g : m → n) => ⟨n, 𝟙, by simp_all⟩⟩
end Test
