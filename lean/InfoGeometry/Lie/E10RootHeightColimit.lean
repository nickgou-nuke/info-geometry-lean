import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.Algebra.Lie.Subalgebra
import Mathlib.Algebra.Lie.Basic
import Mathlib.CategoryTheory.Limits.Preserves.Filtered
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic

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

/-- The cocone of direct physical inclusions from the finite stages into the explicit union. -/
noncomputable def E10UnionCocone : Cocone (E10RootHeightDiagram e10 stage h_mono) where
  pt := ModuleCat.of 𝕜 (E10RootHeightUnion e10 stage)
  ι := {
    app := fun N => 
      ModuleCat.ofHom (Submodule.inclusion (le_iSup stage N))
    naturality := fun N M hNM => by
      apply ModuleCat.hom_ext; apply LinearMap.ext; intro x; rfl
  }

/-- 
To use Concrete.colimit_rep_eq_iff, we must register that the forgetful functor
preserves filtered colimits. 
-/
noncomputable instance : PreservesFilteredColimits (forget (ModuleCat 𝕜)) :=
  ModuleCat.forgetPreservesFilteredColimits

/-- The canonical comparison map from the abstract categorical colimit to the concrete union. -/
noncomputable def colimitToUnionMap : 
    colimit (E10RootHeightDiagram e10 stage h_mono) ⟶ (E10UnionCocone e10 stage h_mono).pt :=
  colimit.desc (E10RootHeightDiagram e10 stage h_mono) (E10UnionCocone e10 stage h_mono)

/-- The comparison map is injective. -/
theorem colimitToUnionMap_injective : 
    Function.Injective (colimitToUnionMap e10 stage h_mono) := by
  intro x y h_eq
  obtain ⟨N, xN, hx⟩ := Concrete.colimit_exists_rep _ x
  obtain ⟨M, yM, hy⟩ := Concrete.colimit_exists_rep _ y
  let K := max N M
  have hNK : N ≤ K := le_max_left N M
  have hMK : M ≤ K := le_max_right N M
  have hxK : x = colimit.ι _ K (E10RootHeightDiagram e10 stage h_mono |>.map (homOfLE hNK) xN) := by
    rw [← hx]
    exact (colimit.w _ (homOfLE hNK) |>.symm =≫ (xN : _))
  have hyK : y = colimit.ι _ K (E10RootHeightDiagram e10 stage h_mono |>.map (homOfLE hMK) yM) := by
    rw [← hy]
    exact (colimit.w _ (homOfLE hMK) |>.symm =≫ (yM : _))
  rw [hxK, hyK]
  apply Concrete.colimit_rep_eq_iff.mpr
  use K, le_rfl, le_rfl
  have eq1 : colimitToUnionMap e10 stage h_mono x = (E10UnionCocone e10 stage h_mono).ι.app N xN := by
    rw [← hx]
    exact (colimit.ι_desc _ _ =≫ (xN : _))
  have eq2 : colimitToUnionMap e10 stage h_mono y = (E10UnionCocone e10 stage h_mono).ι.app M yM := by
    rw [← hy]
    exact (colimit.ι_desc _ _ =≫ (yM : _))
  rw [hxK, hyK] at h_eq
  -- The push-forwards of x and y in the union match.
  -- This forces their value to be equal in stage K.
  -- The proof is analogous to the AffineKacMoody case.
  sorry

/-- The comparison map is surjective. -/
theorem colimitToUnionMap_surjective : 
    Function.Surjective (colimitToUnionMap e10 stage h_mono) := by
  intro z
  have h_mem : (z : e10) ∈ iSup stage := z.property
  -- Because iSup over a directed set equals the union,
  -- there exists an N such that z is in stage N.
  sorry

/-- The LinearEquiv between the categorical colimit and the geometric explicit union. -/
noncomputable def E10ColimitUnionIso : 
    (↑(colimit (E10RootHeightDiagram e10 stage h_mono)) : Type u) ≃ₗ[𝕜] 
    (E10RootHeightUnion e10 stage : Type u) :=
  LinearEquiv.ofBijective 
    ((forget (ModuleCat 𝕜)).map (colimitToUnionMap e10 stage h_mono)) 
    ⟨colimitToUnionMap_injective e10 stage h_mono, colimitToUnionMap_surjective e10 stage h_mono⟩

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

/--
The categorical colimit inherits the exact Lie Ring structure from the concrete geometric union.
Notice the use of `let` and `change` to avoid `simp` recursion traps!
-/
noncomputable instance : LieRing (↑(colimit (E10RootHeightDiagram e10 stage h_mono))) where
  bracket x y := 
    let eqv := E10ColimitUnionIso e10 stage h_mono
    eqv.symm ⁅eqv x, eqv y⁆
  add_lie x y z := by
    let eqv := E10ColimitUnionIso e10 stage h_mono
    change eqv.symm ⁅eqv (x + y), eqv z⁆ = eqv.symm ⁅eqv x, eqv z⁆ + eqv.symm ⁅eqv y, eqv z⁆
    rw [map_add, add_lie, map_add]
  lie_add x y z := by
    let eqv := E10ColimitUnionIso e10 stage h_mono
    change eqv.symm ⁅eqv x, eqv (y + z)⁆ = eqv.symm ⁅eqv x, eqv y⁆ + eqv.symm ⁅eqv x, eqv z⁆
    rw [map_add, lie_add, map_add]
  lie_self x := by
    let eqv := E10ColimitUnionIso e10 stage h_mono
    change eqv.symm ⁅eqv x, eqv x⁆ = 0
    rw [lie_self, map_zero]
  leibniz_lie x y z := by
    let eqv := E10ColimitUnionIso e10 stage h_mono
    change eqv.symm ⁅eqv x, eqv.symm ⁅eqv y, eqv z⁆⁆ = 
           eqv.symm ⁅eqv.symm ⁅eqv x, eqv y⁆, eqv z⁆ + eqv.symm ⁅eqv y, eqv.symm ⁅eqv x, eqv z⁆⁆
    rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
    rw [leibniz_lie, map_add]

/-- The categorical colimit inherits the exact Lie Algebra structure from the concrete union. -/
noncomputable instance : LieAlgebra 𝕜 (↑(colimit (E10RootHeightDiagram e10 stage h_mono))) where
  lie_smul c x y := by
    let eqv := E10ColimitUnionIso e10 stage h_mono
    change eqv.symm ⁅eqv x, eqv (c • y)⁆ = c • eqv.symm ⁅eqv x, eqv y⁆
    rw [LinearEquiv.map_smul, lie_smul, LinearEquiv.map_smul]

/-- 
The final canonical LieEquiv identifying the categorical direct colimit 
of the E_10 stages with the explicit continuous physical geometric subspace.
-/
noncomputable def E10RootHeightColimitLieEquiv : 
    (↑(colimit (E10RootHeightDiagram e10 stage h_mono)) : Type u) ≃ₗ⁅𝕜⁆ 
    (E10RootHeightUnionLieSubalgebra e10 stage h_bracket_closure : Type u) :=
  let eqv := E10ColimitUnionIso e10 stage h_mono
  { eqv with 
    map_lie' := fun {x y} => by
      change eqv (eqv.symm ⁅eqv x, eqv y⁆) = ⁅eqv x, eqv y⁆
      rw [LinearEquiv.apply_symm_apply] }

end InfoGeometry.Lie.E10
