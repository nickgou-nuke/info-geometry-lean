import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.Algebra.Lie.Subalgebra
import Mathlib.Algebra.Lie.Basic

open CategoryTheory CategoryTheory.Limits

namespace InfoGeometry.Lie.E10

universe u
variable {𝕜 : Type u} [Field 𝕜] [CharZero 𝕜]
variable (e10 : Type u) [LieRing e10] [LieAlgebra 𝕜 e10]

/- A filtered system of submodules representing the finite root-height cutoffs of E_10. -/
variable (stage : ℕ → Submodule 𝕜 e10)
variable (h_mono : Monotone stage)

/- 
Scholium XLI: Finite stages of Kac-Moody algebras (like E_10) are Modules, not Lie Algebras.
The interaction (Lie Bracket) generally exceeds any finite root-height bound `N`.
Therefore, the geometric equivalence must be built by defining the Colimit in `ModuleCat` 
and subsequently transporting the continuous bracket backward from the ambient infinite envelope.
-/

/-- The categorical diagram of E_10 finite-mode stages in ModuleCat. -/
@[simps]
noncomputable def E10RootHeightDiagram : ℕ ⥤ ModuleCat 𝕜 where
  obj N := ModuleCat.of 𝕜 (stage N)
  map {N M} hNM := 
    let h_le : stage N ≤ stage M := h_mono (leOfHom hNM)
    ModuleCat.ofHom (Submodule.inclusion h_le)
  map_id N := by apply ModuleCat.hom_ext; apply LinearMap.ext; intro x; rfl
  map_comp {N M K} hNM hMK := by apply ModuleCat.hom_ext; apply LinearMap.ext; intro x; rfl

/-- The explicit continuous subspace representing the infinite limit of all finite-height modes. -/
def E10RootHeightUnion : Submodule 𝕜 e10 :=
  iSup stage

/-- The categorical colimit of the E_10 root-height finite stages. -/
noncomputable def E10RootHeightColimit : Type u :=
  ↑(colimit (E10RootHeightDiagram e10 stage h_mono))

/-- The cocone of direct physical inclusions from the finite stages into the explicit union. -/
noncomputable def E10UnionCocone : Cocone (E10RootHeightDiagram e10 stage h_mono) where
  pt := ModuleCat.of 𝕜 (E10RootHeightUnion e10 stage)
  ι := {
    app := fun N => 
      ModuleCat.ofHom (Submodule.inclusion (le_iSup stage N))
    naturality := fun N M hNM => by
      apply ModuleCat.hom_ext; apply LinearMap.ext; intro x; rfl
  }

/- 
To transport the Lie algebra structure onto the union, we must prove the directed supremum 
of finite modules is closed under the ambient bracket. 
-/
variable (h_bracket_closure : ∀ x y : E10RootHeightUnion e10 stage, 
  (⁅(x : e10), (y : e10)⁆) ∈ E10RootHeightUnion e10 stage)

/-- The infinite geometric limit promoted to a Lie Subalgebra. -/
def E10RootHeightUnionLieSubalgebra : LieSubalgebra 𝕜 e10 :=
  { E10RootHeightUnion e10 stage with
    lie_mem' := fun hx hy => h_bracket_closure ⟨_, hx⟩ ⟨_, hy⟩ }

end InfoGeometry.Lie.E10
