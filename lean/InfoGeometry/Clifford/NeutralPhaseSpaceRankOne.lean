import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.LinearAlgebra.QuadraticForm.IsometryEquiv
import InfoGeometry.Clifford.NeutralPhaseSpaceCore
import InfoGeometry.Clifford.SplitQ11
import InfoGeometry.Meta.Architecture

/-!
# InfoGeometry.Clifford.NeutralPhaseSpaceRankOne

Rank-one anchor from the neutral phase-space owner to the existing split
`(1,1)` seed.

This file proves that the off-diagonal neutral form on `ℝ × ℝ*` is isometric to
the diagonal split form `splitQ11` on `ℝ × ℝ`, and lifts that isometry to the
Clifford algebra level.
-/

namespace NeutralPhaseSpaceRankOne

open InfoGeometry.Clifford.NeutralPhaseSpaceCore

/-- Projection `ℝ* → ℝ` by evaluation at `1`. -/
@[rep_depth krein]
noncomputable def dualRealProjection : Module.Dual ℝ ℝ →ₗ[ℝ] ℝ where
  toFun := fun ξ => ξ 1
  map_add' := by
    intro ξ η
    simp
  map_smul' := by
    intro r ξ
    simp

/-- Section `ℝ → ℝ*` sending `r` to the functional `x ↦ r * x`. -/
@[rep_depth krein]
noncomputable def dualRealSection : ℝ →ₗ[ℝ] Module.Dual ℝ ℝ where
  toFun := fun r =>
    { toFun := fun x => r * x
      map_add' := by
        intro x y
        ring
      map_smul' := by
        intro c x
        simp [smul_eq_mul]
        ring }
  map_add' := by
    intro r s
    apply LinearMap.ext
    intro y
    simp
    ring
  map_smul' := by
    intro c r
    apply LinearMap.ext
    intro y
    simp [smul_eq_mul]
    ring

@[rep_depth krein, simp] theorem dualRealProjection_section
    (r : ℝ) :
    dualRealProjection (dualRealSection r) = r := by
  simp [dualRealProjection, dualRealSection]

@[rep_depth krein, simp] theorem dualRealSection_projection
    (ξ : Module.Dual ℝ ℝ) :
    dualRealSection (dualRealProjection ξ) = ξ := by
  apply LinearMap.ext
  intro y
  calc
    dualRealSection (dualRealProjection ξ) y = (ξ 1) * y := by
      simp [dualRealSection, dualRealProjection]
    _ = ξ (y * 1) := by
      simp
    _ = ξ y := by
      rw [mul_one]

/-- Explicit linear equivalence `ℝ* ≃ₗ[ℝ] ℝ`. -/
@[rep_depth krein]
noncomputable def dualRealEquiv : Module.Dual ℝ ℝ ≃ₗ[ℝ] ℝ :=
  LinearEquiv.ofLinear
    dualRealProjection
    dualRealSection
    (by
      apply LinearMap.ext
      intro r
      exact dualRealProjection_section r)
    (by
      apply LinearMap.ext
      intro ξ
      exact dualRealSection_projection ξ)

/-- Hyperbolic-to-diagonal rank-one coordinate transform. -/
@[rep_depth krein]
noncomputable def hyperbolicToDiagonalEquiv :
    PhaseSpaceCarrier ℝ ≃ₗ[ℝ] (ℝ × ℝ) :=
  LinearEquiv.ofLinear
    { toFun := fun X =>
        let x := X.1
        let ξ := dualRealEquiv X.2
        (x + ξ / 2, x - ξ / 2)
      map_add' := by
        intro X Y
        ext <;> simp [sub_eq_add_neg] <;> ring
      map_smul' := by
        intro r X
        ext <;> simp [sub_eq_add_neg] <;> ring }
    { toFun := fun Y =>
        let u := Y.1
        let v := Y.2
        ((u + v) / 2, dualRealEquiv.symm (u - v))
      map_add' := by
        intro X Y
        refine Prod.ext ?_ ?_
        · simp [sub_eq_add_neg]
          ring
        · apply dualRealEquiv.injective
          simp [sub_eq_add_neg]
          ring
      map_smul' := by
        intro r Y
        refine Prod.ext ?_ ?_
        · simp [sub_eq_add_neg]
          ring
        · apply dualRealEquiv.injective
          simp [sub_eq_add_neg]
      }
    (by
      apply LinearMap.ext
      intro X
      rcases X with ⟨x, ξ⟩
      ext <;> simp [sub_eq_add_neg] <;> ring)
    (by
      apply LinearMap.ext
      intro Y
      rcases Y with ⟨u, v⟩
      refine Prod.ext ?_ ?_
      · simp [sub_eq_add_neg]
        ring
      · apply dualRealEquiv.injective
        simp [sub_eq_add_neg]
        ring)

/-- Rank-one isometry from the neutral phase-space form to the existing split seed. -/
@[rep_depth krein]
noncomputable def rankOneIsometry :
    (canonicalNeutralForm (E := ℝ)).IsometryEquiv InfoGeometry.Clifford.splitQ11 where
  __ := hyperbolicToDiagonalEquiv
  map_app' := by
    intro X
    rcases X with ⟨x, ξ⟩
    have hξ : ξ x = dualRealEquiv ξ * x := by
      have hfun := congrArg (fun f : Module.Dual ℝ ℝ => f x) (dualRealSection_projection ξ).symm
      simpa [dualRealEquiv, dualRealProjection, dualRealSection, mul_comm, mul_left_comm, mul_assoc]
        using hfun
    simp [hyperbolicToDiagonalEquiv, canonicalNeutralForm_apply,
      InfoGeometry.Clifford.splitQ11_apply, sub_eq_add_neg]
    rw [hξ]
    ring

@[rep_depth krein]
noncomputable def rankOneCliffordEquiv :
    NeutralPhaseClifford ℝ ≃ₐ[ℝ] CliffordAlgebra InfoGeometry.Clifford.splitQ11 :=
  CliffordAlgebra.equivOfIsometry rankOneIsometry

@[rep_depth krein, simp] theorem rankOneIsometry_apply
    (X : PhaseSpaceCarrier ℝ) :
    InfoGeometry.Clifford.splitQ11 (rankOneIsometry X)
      = canonicalNeutralForm (E := ℝ) X := by
  exact rankOneIsometry.map_app X

end NeutralPhaseSpaceRankOne
