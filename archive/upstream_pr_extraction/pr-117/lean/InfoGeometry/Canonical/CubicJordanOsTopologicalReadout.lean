import InfoGeometry.Algebra.CubicJordanOsExtensions

/-!
# Topological readouts for the native cubic Albert carrier

The native `CubicJordanOs.AlbertMatrix` currently has additive and coordinate
structure, but no Jordan product.  This owner therefore adds only the honest
finite-coordinate topology induced by its existing equivalence and proves
continuity of the coordinate and Peirce readouts.
-/

noncomputable section

namespace InfoGeometry.Algebra.CubicJordanOs

open InfoGeometry.OperatorAlgebra.SplitOctonions.Multiplication
open InfoGeometry.Algebra.CubicJordanOs.AlbertMatrix

instance splitOctTopologicalSpace : TopologicalSpace SplitOct :=
  TopologicalSpace.induced splitOctEquiv.toFun inferInstance

instance albertMatrixTopologicalSpace : TopologicalSpace AlbertMatrix :=
  TopologicalSpace.induced albertMatrixEquiv.toFun inferInstance

private theorem continuous_splitOctEquiv :
    Continuous (splitOctEquiv : SplitOct → ℤ × ℤ × ℤ × ℤ × ℤ × ℤ × ℤ × ℤ) :=
  continuous_induced_dom

noncomputable def splitOctHomeomorph :
    SplitOct ≃ₜ ℤ × ℤ × ℤ × ℤ × ℤ × ℤ × ℤ × ℤ where
  toEquiv := splitOctEquiv
  continuous_toFun := continuous_splitOctEquiv
  continuous_invFun := by
    apply (continuous_induced_rng).2
    have hcomp :
        splitOctEquiv.toFun ∘ splitOctEquiv.invFun =
          id := by
      funext t
      exact splitOctEquiv.apply_symm_apply t
    rw [hcomp]
    exact continuous_id

instance splitOctDiscreteTopology : DiscreteTopology SplitOct :=
  (splitOctHomeomorph).discreteTopology_iff.mpr inferInstance

theorem continuous_mulZ :
    Continuous (fun p : SplitOct × SplitOct => mulZ p.1 p.2) :=
  continuous_of_discreteTopology

theorem continuous_conjZ :
    Continuous (conjZ : SplitOct → SplitOct) :=
  continuous_of_discreteTopology

theorem continuous_splitOct_add :
    Continuous (fun p : SplitOct × SplitOct => p.1 + p.2) :=
  continuous_of_discreteTopology

private theorem continuous_albertMatrixEquiv :
    Continuous
      (albertMatrixEquiv :
        AlbertMatrix → ℝ × ℝ × ℝ × SplitOct × SplitOct × SplitOct) :=
  continuous_induced_dom

theorem continuous_albertMatrix_α₁ :
    Continuous (fun X : AlbertMatrix => X.α₁) := by
  simpa [albertMatrixEquiv] using continuous_albertMatrixEquiv.fst

theorem continuous_albertMatrix_α₂ :
    Continuous (fun X : AlbertMatrix => X.α₂) := by
  simpa [albertMatrixEquiv] using continuous_albertMatrixEquiv.snd.fst

theorem continuous_albertMatrix_α₃ :
    Continuous (fun X : AlbertMatrix => X.α₃) := by
  simpa [albertMatrixEquiv] using continuous_albertMatrixEquiv.snd.snd.fst

theorem continuous_albertMatrix_z₁ :
    Continuous (fun X : AlbertMatrix => X.z₁) := by
  simpa [albertMatrixEquiv] using continuous_albertMatrixEquiv.snd.snd.snd.fst

theorem continuous_albertMatrix_z₂ :
    Continuous (fun X : AlbertMatrix => X.z₂) := by
  simpa [albertMatrixEquiv] using continuous_albertMatrixEquiv.snd.snd.snd.snd.fst

theorem continuous_albertMatrix_z₃ :
    Continuous (fun X : AlbertMatrix => X.z₃) := by
  exact continuous_albertMatrixEquiv.snd.snd.snd.snd.snd

theorem continuous_peirceDecomposition_diag₁ :
    Continuous (fun X : AlbertMatrix => (peirceDecomposition X).diag₁) := by
  simpa using continuous_albertMatrix_α₁

theorem continuous_peirceDecomposition_diag₂ :
    Continuous (fun X : AlbertMatrix => (peirceDecomposition X).diag₂) := by
  simpa using continuous_albertMatrix_α₂

theorem continuous_peirceDecomposition_diag₃ :
    Continuous (fun X : AlbertMatrix => (peirceDecomposition X).diag₃) := by
  simpa using continuous_albertMatrix_α₃

theorem continuous_peirceDecomposition_off₂₃ :
    Continuous (fun X : AlbertMatrix => (peirceDecomposition X).off₂₃) := by
  simpa using continuous_albertMatrix_z₁

theorem continuous_peirceDecomposition_off₃₁ :
    Continuous (fun X : AlbertMatrix => (peirceDecomposition X).off₃₁) := by
  simpa using continuous_albertMatrix_z₂

theorem continuous_peirceDecomposition_off₁₂ :
    Continuous (fun X : AlbertMatrix => (peirceDecomposition X).off₁₂) := by
  simpa using continuous_albertMatrix_z₃

private theorem continuous_peirce_target11 :
    Continuous (fun X : AlbertMatrix =>
      (X.α₁, (0 : ℝ), (0 : ℝ), zeroZ, zeroZ, zeroZ)) := by
  exact continuous_albertMatrix_α₁.prodMk
    (continuous_const.prodMk
      (continuous_const.prodMk
        (continuous_const.prodMk
          (continuous_const.prodMk continuous_const))))

theorem continuous_peirceProj11 :
    Continuous (peirceProj11 : AlbertMatrix → AlbertMatrix) := by
  apply (continuous_induced_rng).2
  simpa [Function.comp_def, albertMatrixEquiv, peirceProj11] using
    continuous_peirce_target11

private theorem continuous_peirce_target22 :
    Continuous (fun X : AlbertMatrix =>
      ((0 : ℝ), X.α₂, (0 : ℝ), zeroZ, zeroZ, zeroZ)) := by
  exact continuous_const.prodMk
    (continuous_albertMatrix_α₂.prodMk
      (continuous_const.prodMk
        (continuous_const.prodMk
          (continuous_const.prodMk continuous_const))))

theorem continuous_peirceProj22 :
    Continuous (peirceProj22 : AlbertMatrix → AlbertMatrix) := by
  apply (continuous_induced_rng).2
  simpa [Function.comp_def, albertMatrixEquiv, peirceProj22] using
    continuous_peirce_target22

private theorem continuous_peirce_target33 :
    Continuous (fun X : AlbertMatrix =>
      ((0 : ℝ), (0 : ℝ), X.α₃, zeroZ, zeroZ, zeroZ)) := by
  exact continuous_const.prodMk
    (continuous_const.prodMk
      (continuous_albertMatrix_α₃.prodMk
        (continuous_const.prodMk
          (continuous_const.prodMk continuous_const))))

theorem continuous_peirceProj33 :
    Continuous (peirceProj33 : AlbertMatrix → AlbertMatrix) := by
  apply (continuous_induced_rng).2
  simpa [Function.comp_def, albertMatrixEquiv, peirceProj33] using
    continuous_peirce_target33

private theorem continuous_peirce_target23 :
    Continuous (fun X : AlbertMatrix =>
      ((0 : ℝ), (0 : ℝ), (0 : ℝ), X.z₁, zeroZ, zeroZ)) := by
  exact continuous_const.prodMk
    (continuous_const.prodMk
      (continuous_const.prodMk
        (continuous_albertMatrix_z₁.prodMk
          (continuous_const.prodMk continuous_const))))

theorem continuous_peirceProj23 :
    Continuous (peirceProj23 : AlbertMatrix → AlbertMatrix) := by
  apply (continuous_induced_rng).2
  simpa [Function.comp_def, albertMatrixEquiv, peirceProj23] using
    continuous_peirce_target23

private theorem continuous_peirce_target31 :
    Continuous (fun X : AlbertMatrix =>
      ((0 : ℝ), (0 : ℝ), (0 : ℝ), zeroZ, X.z₂, zeroZ)) := by
  exact continuous_const.prodMk
    (continuous_const.prodMk
      (continuous_const.prodMk
        (continuous_const.prodMk
          (continuous_albertMatrix_z₂.prodMk continuous_const))))

theorem continuous_peirceProj31 :
    Continuous (peirceProj31 : AlbertMatrix → AlbertMatrix) := by
  apply (continuous_induced_rng).2
  simpa [Function.comp_def, albertMatrixEquiv, peirceProj31] using
    continuous_peirce_target31

private theorem continuous_peirce_target12 :
    Continuous (fun X : AlbertMatrix =>
      ((0 : ℝ), (0 : ℝ), (0 : ℝ), zeroZ, zeroZ, X.z₃)) := by
  exact continuous_const.prodMk
    (continuous_const.prodMk
      (continuous_const.prodMk
        (continuous_const.prodMk
          (continuous_const.prodMk continuous_albertMatrix_z₃))))

theorem continuous_peirceProj12 :
    Continuous (peirceProj12 : AlbertMatrix → AlbertMatrix) := by
  apply (continuous_induced_rng).2
  simpa [Function.comp_def, albertMatrixEquiv, peirceProj12] using
    continuous_peirce_target12

theorem continuous_octTrace :
    Continuous (octTrace : SplitOct → ℝ) := by
  have ha : Continuous (fun Z : SplitOct => (Z.a : ℝ)) :=
    Int.cast_continuous.comp continuous_splitOctEquiv.fst
  have hb : Continuous (fun Z : SplitOct => (Z.b : ℝ)) :=
    Int.cast_continuous.comp continuous_splitOctEquiv.snd.fst
  simpa [octTrace] using ha.add hb

theorem continuous_traceBilin_left (Y : AlbertMatrix) :
    Continuous (fun X : AlbertMatrix => traceBilin X Y) := by
  have h₁ := continuous_albertMatrix_α₁.mul
    (continuous_const : Continuous (fun _ : AlbertMatrix => Y.α₁))
  have h₂ := continuous_albertMatrix_α₂.mul
    (continuous_const : Continuous (fun _ : AlbertMatrix => Y.α₂))
  have h₃ := continuous_albertMatrix_α₃.mul
    (continuous_const : Continuous (fun _ : AlbertMatrix => Y.α₃))
  have h₂₃ := (continuous_octTrace.comp continuous_albertMatrix_z₁).mul
    (continuous_const : Continuous (fun _ : AlbertMatrix => octTrace Y.z₁))
  have h₃₁ := (continuous_octTrace.comp continuous_albertMatrix_z₂).mul
    (continuous_const : Continuous (fun _ : AlbertMatrix => octTrace Y.z₂))
  have h₁₂ := (continuous_octTrace.comp continuous_albertMatrix_z₃).mul
    (continuous_const : Continuous (fun _ : AlbertMatrix => octTrace Y.z₃))
  simpa [traceBilin] using
    (((((h₁.add h₂).add h₃).add h₂₃).add h₃₁).add h₁₂)

theorem continuous_albertMatrix_add :
    Continuous (fun p : AlbertMatrix × AlbertMatrix => p.1 + p.2) := by
  have hα₁ := (continuous_albertMatrix_α₁.comp continuous_fst).add
    (continuous_albertMatrix_α₁.comp continuous_snd)
  have hα₂ := (continuous_albertMatrix_α₂.comp continuous_fst).add
    (continuous_albertMatrix_α₂.comp continuous_snd)
  have hα₃ := (continuous_albertMatrix_α₃.comp continuous_fst).add
    (continuous_albertMatrix_α₃.comp continuous_snd)
  have hz₁ := continuous_splitOct_add.comp
    ((continuous_albertMatrix_z₁.comp continuous_fst).prodMk
      (continuous_albertMatrix_z₁.comp continuous_snd))
  have hz₂ := continuous_splitOct_add.comp
    ((continuous_albertMatrix_z₂.comp continuous_fst).prodMk
      (continuous_albertMatrix_z₂.comp continuous_snd))
  have hz₃ := continuous_splitOct_add.comp
    ((continuous_albertMatrix_z₃.comp continuous_fst).prodMk
      (continuous_albertMatrix_z₃.comp continuous_snd))
  have hcoords := hα₁.prodMk (hα₂.prodMk (hα₃.prodMk
    (hz₁.prodMk (hz₂.prodMk hz₃))))
  apply (continuous_induced_rng).2
  simpa [Function.comp_def, albertMatrixEquiv] using hcoords

theorem continuous_traceBilin :
    Continuous (fun p : AlbertMatrix × AlbertMatrix => traceBilin p.1 p.2) := by
  have hα₁ : Continuous (fun p : AlbertMatrix × AlbertMatrix => p.1.α₁) :=
    continuous_albertMatrix_α₁.comp continuous_fst
  have hα₂ : Continuous (fun p : AlbertMatrix × AlbertMatrix => p.1.α₂) :=
    continuous_albertMatrix_α₂.comp continuous_fst
  have hα₃ : Continuous (fun p : AlbertMatrix × AlbertMatrix => p.1.α₃) :=
    continuous_albertMatrix_α₃.comp continuous_fst
  have kα₁ : Continuous (fun p : AlbertMatrix × AlbertMatrix => p.2.α₁) :=
    continuous_albertMatrix_α₁.comp continuous_snd
  have kα₂ : Continuous (fun p : AlbertMatrix × AlbertMatrix => p.2.α₂) :=
    continuous_albertMatrix_α₂.comp continuous_snd
  have kα₃ : Continuous (fun p : AlbertMatrix × AlbertMatrix => p.2.α₃) :=
    continuous_albertMatrix_α₃.comp continuous_snd
  have hz₁ : Continuous (fun p : AlbertMatrix × AlbertMatrix => octTrace p.1.z₁) :=
    continuous_octTrace.comp (continuous_albertMatrix_z₁.comp continuous_fst)
  have hz₂ : Continuous (fun p : AlbertMatrix × AlbertMatrix => octTrace p.1.z₂) :=
    continuous_octTrace.comp (continuous_albertMatrix_z₂.comp continuous_fst)
  have hz₃ : Continuous (fun p : AlbertMatrix × AlbertMatrix => octTrace p.1.z₃) :=
    continuous_octTrace.comp (continuous_albertMatrix_z₃.comp continuous_fst)
  have kz₁ : Continuous (fun p : AlbertMatrix × AlbertMatrix => octTrace p.2.z₁) :=
    continuous_octTrace.comp (continuous_albertMatrix_z₁.comp continuous_snd)
  have kz₂ : Continuous (fun p : AlbertMatrix × AlbertMatrix => octTrace p.2.z₂) :=
    continuous_octTrace.comp (continuous_albertMatrix_z₂.comp continuous_snd)
  have kz₃ : Continuous (fun p : AlbertMatrix × AlbertMatrix => octTrace p.2.z₃) :=
    continuous_octTrace.comp (continuous_albertMatrix_z₃.comp continuous_snd)
  have hsum12 := hα₁.mul kα₁
  have hsum123 := hsum12.add (hα₂.mul kα₂)
  have hsum1234 := hsum123.add (hα₃.mul kα₃)
  have hsum12345 := hsum1234.add (hz₁.mul kz₁)
  have hsum123456 := hsum12345.add (hz₂.mul kz₂)
  have hsum := hsum123456.add (hz₃.mul kz₃)
  simpa [traceBilin] using hsum

theorem continuous_detZ :
    Continuous (detZ : SplitOct → ℤ) := by
  have ha : Continuous (fun Z : SplitOct => Z.a) :=
    continuous_splitOctEquiv.fst
  have hb : Continuous (fun Z : SplitOct => Z.b) :=
    continuous_splitOctEquiv.snd.fst
  have hx₀ : Continuous (fun Z : SplitOct => Z.x0) :=
    continuous_splitOctEquiv.snd.snd.fst
  have hx₁ : Continuous (fun Z : SplitOct => Z.x1) :=
    continuous_splitOctEquiv.snd.snd.snd.fst
  have hx₂ : Continuous (fun Z : SplitOct => Z.x2) :=
    continuous_splitOctEquiv.snd.snd.snd.snd.fst
  have hy₀ : Continuous (fun Z : SplitOct => Z.y0) :=
    continuous_splitOctEquiv.snd.snd.snd.snd.snd.fst
  have hy₁ : Continuous (fun Z : SplitOct => Z.y1) :=
    continuous_splitOctEquiv.snd.snd.snd.snd.snd.snd.fst
  have hy₂ : Continuous (fun Z : SplitOct => Z.y2) :=
    continuous_splitOctEquiv.snd.snd.snd.snd.snd.snd.snd
  have hxy₀ := hx₀.mul hy₀
  have hxy₁ := hx₁.mul hy₁
  have hxy₂ := hx₂.mul hy₂
  have hinner := (hxy₀.add hxy₁).add hxy₂
  simpa [detZ] using (ha.mul hb).sub hinner

theorem continuous_detZ_real :
    Continuous (fun Z : SplitOct => (detZ Z : ℝ)) :=
  Int.cast_continuous.comp continuous_detZ

theorem continuous_normCubic :
    Continuous (normCubic : AlbertMatrix → ℝ) := by
  have hα₁ := continuous_albertMatrix_α₁
  have hα₂ := continuous_albertMatrix_α₂
  have hα₃ := continuous_albertMatrix_α₃
  have hz₁ := continuous_albertMatrix_z₁
  have hz₂ := continuous_albertMatrix_z₂
  have hz₃ := continuous_albertMatrix_z₃
  have hdet₁ := continuous_detZ_real.comp hz₁
  have hdet₂ := continuous_detZ_real.comp hz₂
  have hdet₃ := continuous_detZ_real.comp hz₃
  have hmul₁₂ := continuous_mulZ.comp (hz₁.prodMk hz₂)
  have hmul₁₂₃ := continuous_mulZ.comp (hmul₁₂.prodMk hz₃)
  have htriple := continuous_octTrace.comp hmul₁₂₃
  have hterm₁₂₃ := (hα₁.mul hα₂).mul hα₃
  have hterm₁ := hα₁.mul hdet₁
  have hterm₂ := hα₂.mul hdet₂
  have hterm₃ := hα₃.mul hdet₃
  have hsum₁ := hterm₁₂₃.add hterm₁
  have hsum₂ := hsum₁.add hterm₂
  have hsum₃ := hsum₂.add hterm₃
  simpa [normCubic] using hsum₃.sub htriple

end InfoGeometry.Algebra.CubicJordanOs
