import InfoGeometry.Clifford.ClNN
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Clifford.SplitQ11
import InfoGeometry.Quantum.RealSplitClifford
import InfoGeometry.Meta.Architecture

/-!
# InfoGeometry.Clifford.ClNNSpecialization

Rank-one specialization of the generic split `Cl(n,n)` owner surface back to the
existing `(1,1)` seed.

This file is deliberately narrow:
- identify `Carrier 1` with the concrete `(ℝ × ℝ)` seed,
- show the generic quadratic form reduces to `splitQ11`,
- show the normalized rank-one null modes reduce to the existing split-null
  seed vectors.

Authority note:

- this is a specialization of the split-tower owner from `ClNN`,
- it is not the corrected neutral phase-space rank-one anchor,
- the corrected owner-side rank-one bridge lives in `NeutralPhaseSpaceRankOne`.
-/

namespace InfoGeometry.Clifford.ClNNSpecialization

open InfoGeometry.Clifford.ClNN

/-- Projection from the rank-one recursive carrier to the concrete split seed. -/
@[rep_depth krein]
noncomputable def rankOneProjection : Carrier 1 →ₗ[ℝ] (ℝ × ℝ) :=
  LinearMap.fst ℝ (ℝ × ℝ) (Carrier 0)

/-- Section from the concrete split seed into the rank-one recursive carrier. -/
@[rep_depth krein]
noncomputable def rankOneSection : (ℝ × ℝ) →ₗ[ℝ] Carrier 1 where
  toFun := headPair 0
  map_add' := by
    intro x y
    simp [headPair]
  map_smul' := by
    intro r x
    simp [headPair]

@[rep_depth krein, simp] theorem rankOneProjection_section
    (x : ℝ × ℝ) :
    rankOneProjection (rankOneSection x) = x := by
  simp [rankOneProjection, rankOneSection, headPair]

@[rep_depth krein, simp] theorem rankOneSection_projection
    (u : Carrier 1) :
    rankOneSection (rankOneProjection u) = u := by
  rcases u with ⟨x, xs⟩
  have hxs : xs = (0 : Carrier 0) := Subsingleton.elim _ _
  simp [rankOneProjection, rankOneSection, headPair, hxs]

/-- Linear equivalence between the rank-one recursive carrier and the concrete
split `(1,1)` seed. -/
@[rep_depth krein]
noncomputable def rankOneEquiv : Carrier 1 ≃ₗ[ℝ] (ℝ × ℝ) :=
  LinearEquiv.ofLinear
    rankOneProjection
    rankOneSection
    (by
      apply LinearMap.ext
      intro x
      exact rankOneProjection_section x)
    (by
      apply LinearMap.ext
      intro u
      exact rankOneSection_projection u)

@[rep_depth krein, simp] theorem quad_rankOneSection
    (x : ℝ × ℝ) :
    Quad 1 (rankOneSection x) = InfoGeometry.Clifford.splitQ11 x := by
  simpa [rankOneSection, headPair] using quad_headPair 0 x

@[rep_depth krein, simp] theorem quad_rankOneEquiv_symm
    (x : ℝ × ℝ) :
    Quad 1 ((rankOneEquiv).symm x) = InfoGeometry.Clifford.splitQ11 x := by
  simpa [rankOneEquiv] using quad_rankOneSection x

@[rep_depth krein, simp] theorem rankOne_headNullMinus :
    (rankOneEquiv.symm ((1 / 2 : ℝ), (1 / 2 : ℝ))) = headNullMinus 0 := by
  rfl

@[rep_depth krein, simp] theorem rankOne_headNullPlus :
    (rankOneEquiv.symm ((1 / 2 : ℝ), (-(1 / 2 : ℝ)))) = headNullPlus 0 := by
  rfl

@[rep_depth krein, simp] theorem quad_rankOne_headNullMinus :
    Quad 1 (headNullMinus 0) = 0 := by
  simpa [rankOne_headNullMinus] using headNullMinus_isotropic 0

@[rep_depth krein, simp] theorem quad_rankOne_headNullPlus :
    Quad 1 (headNullPlus 0) = 0 := by
  simpa [rankOne_headNullPlus] using headNullPlus_isotropic 0

@[rep_depth krein, simp] theorem gamma_rankOne_headNullMinus_sq :
    gammaHeadNullMinus 0 * gammaHeadNullMinus 0 = 0 := by
  exact gammaHeadNullMinus_sq 0

@[rep_depth krein, simp] theorem gamma_rankOne_headNullPlus_sq :
    gammaHeadNullPlus 0 * gammaHeadNullPlus 0 = 0 := by
  exact gammaHeadNullPlus_sq 0

end InfoGeometry.Clifford.ClNNSpecialization
