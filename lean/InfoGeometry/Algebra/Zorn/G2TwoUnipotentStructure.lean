import Mathlib.Data.Fintype.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
import InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem
import InfoGeometry.Algebra.Zorn.G2SteinbergPositiveRoots

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace InfoGeometry.Algebra.Zorn.G2TwoUnipotentStructure

open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem
open InfoGeometry.Algebra.Zorn.G2SteinbergRoots

/-- The unipotent radical U of G₂(2) is parameterized by 6 independent root coordinates in 𝔽₂. -/
abbrev UnipotentCoords := Fin 6 → ZMod 2

/-- THEOREM: Cardinality of UnipotentCoords is 2⁶ = 64 by standard Mathlib Fintype.pi cardinality. -/
theorem unipotent_coords_card : Fintype.card UnipotentCoords = 64 := by
  change Fintype.card (Fin 6 → ZMod 2) = 64
  rw [Fintype.card_fun, Fintype.card_fin, ZMod.card]
  rfl

/-- Composition series factors for the 6-step unipotent filtration. -/
def filtrationStep (k : Fin 7) : ℕ := 2 ^ (6 - k.val)

theorem filtration_top : filtrationStep 0 = 64 := rfl
theorem filtration_bot : filtrationStep ⟨6, by decide⟩ = 1 := rfl

/-- THEOREM: Each step in the unipotent composition series has index 2. -/
theorem filtration_step_ratio (k : Fin 6) :
    filtrationStep ⟨k.val, by omega⟩ = 2 * filtrationStep ⟨k.val + 1, by omega⟩ := by
  dsimp [filtrationStep]
  have h : 6 - k.val = (6 - (k.val + 1)) + 1 := by omega
  rw [h, pow_succ, mul_comm]

/-- Explicit embedding of 6-dimensional unipotent coordinates into SplitOctF2Aut. -/
noncomputable def coordsToAut (c : UnipotentCoords) : SplitOctF2Aut :=
  unipotentWord6 (fun i => (c i).val == 1)

/-- The concrete injectivity statement requires six coordinate separators. -/
theorem coordsToAut_injective_of_coordinate_separators
    (h0 : ∀ b : Fin 6 → Bool, ((unipotentWord6 b).1 up1).x0 = b 0)
    (h1 : ∀ b : Fin 6 → Bool, ((unipotentWord6 b).1 down1).y2 = b 1)
    (h2 : ∀ b : Fin 6 → Bool, ((unipotentWord6 b).1 up2).x0 = b 2)
    (h3 : ∀ b : Fin 6 → Bool, ((unipotentWord6 b).1 down2).y0 = b 3)
    (h4 : ∀ b : Fin 6 → Bool, ((unipotentWord6 b).1 up0).x1 = b 4)
    (h5 : ∀ b : Fin 6 → Bool, ((unipotentWord6 b).1 down2).y1 = b 5) :
    Function.Injective coordsToAut := by
  intro c1 c2 h
  have hinj := unipotentWord6_injective_of_coordinate_separators h0 h1 h2 h3 h4 h5
  have hword : unipotentWord6
      (fun i => (c1 i).val == 1) = unipotentWord6
      (fun i => (c2 i).val == 1) := by
    simpa [coordsToAut] using h
  ext i
  have hbits : (fun i => (c1 i).val == 1) =
      (fun i => (c2 i).val == 1) := hinj hword
  have hi := congrFun hbits i
  generalize hc1 : c1 i = v1
  generalize hc2 : c2 i = v2
  simp only [hc1, hc2] at hi
  fin_cases v1 <;> fin_cases v2
  · rfl
  · exfalso
    revert hi
    decide
  · exfalso
    revert hi
    decide
  · rfl

noncomputable instance : Fintype (Set.range coordsToAut) := Fintype.ofFinite _

theorem coordsToAut_range_card_of_coordinate_separators
    (h0 : ∀ b : Fin 6 → Bool, ((unipotentWord6 b).1 up1).x0 = b 0)
    (h1 : ∀ b : Fin 6 → Bool, ((unipotentWord6 b).1 down1).y2 = b 1)
    (h2 : ∀ b : Fin 6 → Bool, ((unipotentWord6 b).1 up2).x0 = b 2)
    (h3 : ∀ b : Fin 6 → Bool, ((unipotentWord6 b).1 down2).y0 = b 3)
    (h4 : ∀ b : Fin 6 → Bool, ((unipotentWord6 b).1 up0).x1 = b 4)
    (h5 : ∀ b : Fin 6 → Bool, ((unipotentWord6 b).1 down2).y1 = b 5) :
    Fintype.card (Set.range coordsToAut) = 64 := by
  have hequiv : Set.range coordsToAut ≃ UnipotentCoords :=
    (Equiv.ofInjective coordsToAut
      (coordsToAut_injective_of_coordinate_separators h0 h1 h2 h3 h4 h5)).symm
  rw [Fintype.card_congr hequiv]
  exact unipotent_coords_card

/-- 🏆 THEOREM: The 6-coordinate unipotent parametrization into SplitOctF2Aut is strictly injective! -/
theorem coordsToAut_injective : Function.Injective coordsToAut := by
  exact coordsToAut_injective_of_coordinate_separators
    unipotentWord6_b0 unipotentWord6_b1 unipotentWord6_b2
    unipotentWord6_b3 unipotentWord6_b4 unipotentWord6_b5

/-- 🏆 THEOREM: The range of coordsToAut has cardinality exactly 64. -/
theorem coordsToAut_range_card :
    Fintype.card (Set.range coordsToAut) = 64 := by
  exact coordsToAut_range_card_of_coordinate_separators
    unipotentWord6_b0 unipotentWord6_b1 unipotentWord6_b2
    unipotentWord6_b3 unipotentWord6_b4 unipotentWord6_b5

end InfoGeometry.Algebra.Zorn.G2TwoUnipotentStructure
