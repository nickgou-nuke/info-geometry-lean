import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Physics.ThreeColorSL3ZornAction

/-!
# Topological three-colour `SL₃` action on the Zorn carrier

The Zorn carrier is first given the product topology transported through its
coordinate equivalence.  On this topological carrier, the external `SL₃`
action on the colour coordinates is continuous because it is built from
finite-dimensional linear maps on `ℂ^3`.
-/

namespace InfoGeometry.Topology.ThreeColorSL3ZornActionTopological

open InfoGeometry.Physics.ThreeColorSL3ZornAction

noncomputable section

abbrev ZornCoords :=
  ℂ × ((Fin 3 → ℂ) × ((Fin 3 → ℂ) × ℂ))

/-- Coordinate equivalence for the three-colour Zorn carrier. -/
def zornCoordEquiv : Zorn ≃ ZornCoords where
  toFun X := (X.a, (X.u, (X.v, X.b)))
  invFun t :=
    { a := t.1
      u := t.2.1
      v := t.2.2.1
      b := t.2.2.2 }
  left_inv X := by
    cases X
    rfl
  right_inv t := by
    rcases t with ⟨a, u, v, b⟩
    rfl

instance zornTopologicalSpace : TopologicalSpace Zorn :=
  TopologicalSpace.induced zornCoordEquiv.toFun inferInstance

private theorem continuous_zornCoordEquiv :
    Continuous (zornCoordEquiv : Zorn ≃ ZornCoords) :=
  continuous_induced_dom

def zornCoordHomeomorph : Zorn ≃ₜ ZornCoords where
  toEquiv := zornCoordEquiv
  continuous_toFun := continuous_zornCoordEquiv
  continuous_invFun := by
    apply (continuous_induced_rng).2
    simpa [zornCoordEquiv, Function.comp_def] using
      (show Continuous (fun x : ZornCoords => x) by
        exact continuous_id)

@[simp] theorem zornCoordHomeomorph_apply (X : Zorn) :
    zornCoordHomeomorph X = zornCoordEquiv X := rfl

theorem continuous_zorn_a :
    Continuous (fun X : Zorn => X.a) :=
  continuous_zornCoordEquiv.fst

theorem continuous_zorn_u :
    Continuous (fun X : Zorn => X.u) :=
  continuous_zornCoordEquiv.snd.fst

theorem continuous_zorn_v :
    Continuous (fun X : Zorn => X.v) :=
  continuous_zornCoordEquiv.snd.snd.fst

theorem continuous_zorn_b :
    Continuous (fun X : Zorn => X.b) :=
  continuous_zornCoordEquiv.snd.snd.snd

/-- The external `SL₃` colour action is continuous on the coordinate topology. -/
theorem continuous_zornSL3Action
    (g : Matrix.SpecialLinearGroup (Fin 3) ℂ) :
    Continuous (zornSL3Action g) := by
  let fundamental : (Fin 3 → ℂ) →ₗ[ℂ] (Fin 3 → ℂ) :=
    { toFun := colourFundamentalAction g
      map_add' u v := by
        ext i
        simp [colourFundamentalAction, Matrix.mulVec_add]
      map_smul' c u := by
        ext i
        simp [colourFundamentalAction, Matrix.mulVec_smul] }
  let dual : (Fin 3 → ℂ) →ₗ[ℂ] (Fin 3 → ℂ) :=
    { toFun := colourDualAction g
      map_add' u v := by
        ext i
        simp [colourDualAction, Matrix.mulVec_add]
      map_smul' c u := by
        ext i
        simp [colourDualAction, Matrix.mulVec_smul] }
  have hfun : Continuous (fun X : Zorn => colourFundamentalAction g X.u) := by
    simpa [fundamental] using
      (LinearMap.continuous_of_finiteDimensional fundamental).comp continuous_zorn_u
  have hdu : Continuous (fun X : Zorn => colourDualAction g X.v) := by
    simpa [dual] using
      (LinearMap.continuous_of_finiteDimensional dual).comp continuous_zorn_v
  have hcoord : Continuous (fun X : Zorn => zornCoordEquiv (zornSL3Action g X)) := by
    simpa [zornCoordEquiv, zornSL3Action] using
      (continuous_zorn_a.prodMk (hfun.prodMk (hdu.prodMk continuous_zorn_b)))
  exact (continuous_induced_rng).2 hcoord

/-- The fundamental colour action is inverted by the action of `g⁻¹`. -/
@[simp] theorem colourFundamentalAction_inv
    (g : Matrix.SpecialLinearGroup (Fin 3) ℂ) (u : Fin 3 → ℂ) :
    colourFundamentalAction (g⁻¹) (colourFundamentalAction g u) = u := by
  have hmat :
      ((g : Matrix (Fin 3) (Fin 3) ℂ).adjugate *
        (g : Matrix (Fin 3) (Fin 3) ℂ)) = 1 := by
    simpa using (Matrix.adjugate_mul (g : Matrix (Fin 3) (Fin 3) ℂ))
  simp [colourFundamentalAction, Matrix.SpecialLinearGroup.coe_inv,
    Matrix.mulVec_mulVec, hmat, Matrix.one_mulVec]

/-- The fundamental colour action is also inverted on the other side. -/
@[simp] theorem colourFundamentalAction_inv_right
    (g : Matrix.SpecialLinearGroup (Fin 3) ℂ) (u : Fin 3 → ℂ) :
    colourFundamentalAction g (colourFundamentalAction g⁻¹ u) = u := by
  simpa using (colourFundamentalAction_inv (g := g⁻¹) u)

/-- The dual colour action is inverted by the action of `g⁻¹`. -/
@[simp] theorem colourDualAction_inv
    (g : Matrix.SpecialLinearGroup (Fin 3) ℂ) (v : Fin 3 → ℂ) :
    colourDualAction (g⁻¹) (colourDualAction g v) = v := by
  simp [colourDualAction, Matrix.SpecialLinearGroup.coe_inv,
    Matrix.adjugate_transpose, Matrix.mul_adjugate]

/-- The dual colour action is also inverted on the other side. -/
@[simp] theorem colourDualAction_inv_right
    (g : Matrix.SpecialLinearGroup (Fin 3) ℂ) (v : Fin 3 → ℂ) :
    colourDualAction g (colourDualAction g⁻¹ v) = v := by
  simpa using (colourDualAction_inv (g := g⁻¹) v)

/-- The external `SL₃` action is a homeomorphism with inverse given by `g⁻¹`. -/
noncomputable def zornSL3ActionHomeomorph
    (g : Matrix.SpecialLinearGroup (Fin 3) ℂ) :
    Zorn ≃ₜ Zorn where
  toFun := zornSL3Action g
  invFun := zornSL3Action g⁻¹
  left_inv := by
    intro X
    cases X
    simp [zornSL3Action]
  right_inv := by
    intro X
    cases X
    simp [zornSL3Action]
  continuous_toFun := continuous_zornSL3Action g
  continuous_invFun := continuous_zornSL3Action g⁻¹

@[simp] theorem zornSL3ActionHomeomorph_apply
    (g : Matrix.SpecialLinearGroup (Fin 3) ℂ) (X : Zorn) :
    zornSL3ActionHomeomorph g X = zornSL3Action g X :=
  rfl

@[simp] theorem zornSL3ActionHomeomorph_symm_apply
    (g : Matrix.SpecialLinearGroup (Fin 3) ℂ) (X : Zorn) :
    (zornSL3ActionHomeomorph g).symm X = zornSL3Action g⁻¹ X := by
  rfl

theorem zornSL3ActionHomeomorph_comp
    (g₁ g₂ : Matrix.SpecialLinearGroup (Fin 3) ℂ) :
    (zornSL3ActionHomeomorph g₁).trans (zornSL3ActionHomeomorph g₂) =
      zornSL3ActionHomeomorph (g₂ * g₁) := by
  apply Homeomorph.ext
  intro X
  change zornSL3Action g₂ (zornSL3Action g₁ X) =
    zornSL3Action (g₂ * g₁) X
  simpa [zornSL3ActionHomeomorph_apply] using
    congrFun (InfoGeometry.Physics.ThreeColorSL3ZornAction.zornSL3Action_comp g₁ g₂) X

theorem zornSL3ActionHomeomorph_comp_inv
    (g : Matrix.SpecialLinearGroup (Fin 3) ℂ) :
    (zornSL3ActionHomeomorph g).trans (zornSL3ActionHomeomorph g⁻¹) =
      Homeomorph.refl Zorn := by
  apply Homeomorph.ext
  intro X
  change zornSL3Action g⁻¹ (zornSL3Action g X) = X
  simpa [zornSL3ActionHomeomorph_apply, zornSL3ActionHomeomorph_symm_apply] using
    (zornSL3ActionHomeomorph g).symm_apply_apply X

theorem zornSL3ActionHomeomorph_inv_comp
    (g : Matrix.SpecialLinearGroup (Fin 3) ℂ) :
    (zornSL3ActionHomeomorph g⁻¹).trans (zornSL3ActionHomeomorph g) =
      Homeomorph.refl Zorn := by
  apply Homeomorph.ext
  intro X
  change zornSL3Action g (zornSL3Action g⁻¹ X) = X
  simpa [zornSL3ActionHomeomorph_apply, zornSL3ActionHomeomorph_symm_apply] using
    (zornSL3ActionHomeomorph g).apply_symm_apply X

theorem zornSL3Action_comp
    (g₁ g₂ : Matrix.SpecialLinearGroup (Fin 3) ℂ) :
    zornSL3Action g₂ ∘ zornSL3Action g₁ = zornSL3Action (g₂ * g₁) := by
  funext X
  apply InfoGeometry.Physics.SplitOctonionBraidSU3.zorn_ext
  · rfl
  · funext i
    simp [zornSL3Action, colourFundamentalAction, Matrix.mulVec_mulVec]
  · funext i
    simp [zornSL3Action, colourDualAction, Matrix.mulVec_mulVec,
      Matrix.transpose_mul]
  · rfl

end

end InfoGeometry.Topology.ThreeColorSL3ZornActionTopological
