import InfoGeometry.Algebra.F4Derivations

/-!
# Coordinate topology for the native H₃(Zorn) carrier

This owner installs the product topology transported by the existing
coordinate equivalences.  It proves only coordinate continuity here; no
continuity of the cubic norm or Jordan product is claimed without the
corresponding coordinate lemmas.
-/

noncomputable section

namespace InfoGeometry.Algebra

open H3Zorn

instance zornVectorMatrixRealTopologicalSpace :
    TopologicalSpace (ZornVectorMatrix ℝ) :=
  TopologicalSpace.induced ZornVectorMatrix.coordEquiv.toFun inferInstance

private theorem continuous_zornVectorMatrix_coordEquiv :
    Continuous
      (ZornVectorMatrix.coordEquiv :
        ZornVectorMatrix ℝ ≃
          (ℝ × (Fin 3 → ℝ) × (Fin 3 → ℝ) × ℝ)) :=
  continuous_induced_dom

def zornVectorMatrixRealHomeomorph :
    ZornVectorMatrix ℝ ≃ₜ
      (ℝ × (Fin 3 → ℝ) × (Fin 3 → ℝ) × ℝ) where
  toEquiv := ZornVectorMatrix.coordEquiv
  continuous_toFun := continuous_zornVectorMatrix_coordEquiv
  continuous_invFun := by
    apply (continuous_induced_rng).2
    simpa [ZornVectorMatrix.coordEquiv, Function.comp_def] using
      (show Continuous (fun x :
          ℝ × (Fin 3 → ℝ) × (Fin 3 → ℝ) × ℝ => x) by
        exact continuous_id)

instance zornVectorMatrixRealT2Space : T2Space (ZornVectorMatrix ℝ) :=
  zornVectorMatrixRealHomeomorph.symm.t2Space

instance zornVectorMatrixRealLocallyCompactSpace :
    LocallyCompactSpace (ZornVectorMatrix ℝ) := by
  exact (zornVectorMatrixRealHomeomorph.locallyCompactSpace_iff).mpr inferInstance

theorem secondCountableTopology_zornVectorMatrix
    [SecondCountableTopology ℝ]
    [SecondCountableTopology (Fin 3 → ℝ)] :
    SecondCountableTopology (ZornVectorMatrix ℝ) :=
  zornVectorMatrixRealHomeomorph.secondCountableTopology

theorem continuous_zornVectorMatrix_a :
    Continuous (fun X : ZornVectorMatrix ℝ => X.a) :=
  continuous_zornVectorMatrix_coordEquiv.fst

theorem continuous_zornVectorMatrix_b :
    Continuous (fun X : ZornVectorMatrix ℝ => X.b) :=
  continuous_zornVectorMatrix_coordEquiv.snd.snd.snd

theorem continuous_zornVectorMatrix_v (i : Fin 3) :
    Continuous (fun X : ZornVectorMatrix ℝ => X.v i) :=
  (continuous_apply i).comp continuous_zornVectorMatrix_coordEquiv.snd.fst

theorem continuous_zornVectorMatrix_w (i : Fin 3) :
    Continuous (fun X : ZornVectorMatrix ℝ => X.w i) :=
  (continuous_apply i).comp continuous_zornVectorMatrix_coordEquiv.snd.snd.fst

def h3ZornRealCoordEquiv :
    H3Zorn ℝ ≃
      (ℝ × ℝ × ℝ × ZornVectorMatrix ℝ ×
        ZornVectorMatrix ℝ × ZornVectorMatrix ℝ) where
  toFun X := (X.α₁, X.α₂, X.α₃, X.a, X.b, X.c)
  invFun t :=
    { α₁ := t.1
      α₂ := t.2.1
      α₃ := t.2.2.1
      a := t.2.2.2.1
      b := t.2.2.2.2.1
      c := t.2.2.2.2.2 }
  left_inv X := by
    cases X
    rfl
  right_inv t := by
    rcases t with ⟨α₁, α₂, α₃, a, b, c⟩
    rfl

instance h3ZornRealTopologicalSpace : TopologicalSpace (H3Zorn ℝ) :=
  TopologicalSpace.induced h3ZornRealCoordEquiv.toFun inferInstance

private theorem continuous_h3ZornRealCoordEquiv :
    Continuous
      (h3ZornRealCoordEquiv :
        H3Zorn ℝ ≃
          (ℝ × ℝ × ℝ × ZornVectorMatrix ℝ ×
            ZornVectorMatrix ℝ × ZornVectorMatrix ℝ)) :=
  continuous_induced_dom

def h3ZornRealHomeomorph :
    H3Zorn ℝ ≃ₜ
      (ℝ × ℝ × ℝ × ZornVectorMatrix ℝ ×
        ZornVectorMatrix ℝ × ZornVectorMatrix ℝ) where
  toEquiv := h3ZornRealCoordEquiv
  continuous_toFun := continuous_h3ZornRealCoordEquiv
  continuous_invFun := by
    apply (continuous_induced_rng).2
    simpa [h3ZornRealCoordEquiv, Function.comp_def] using
      (show Continuous (fun x :
          ℝ × ℝ × ℝ × ZornVectorMatrix ℝ ×
            ZornVectorMatrix ℝ × ZornVectorMatrix ℝ => x) by
        exact continuous_id)

instance h3ZornRealT2Space : T2Space (H3Zorn ℝ) :=
  h3ZornRealHomeomorph.symm.t2Space

instance h3ZornRealLocallyCompactSpace :
    LocallyCompactSpace (H3Zorn ℝ) := by
  exact (h3ZornRealHomeomorph.locallyCompactSpace_iff).mpr inferInstance

theorem secondCountableTopology_h3Zorn
    [SecondCountableTopology ℝ]
    [SecondCountableTopology (Fin 3 → ℝ)] :
    SecondCountableTopology (H3Zorn ℝ) := by
  letI : SecondCountableTopology (ZornVectorMatrix ℝ) :=
    secondCountableTopology_zornVectorMatrix
  exact h3ZornRealHomeomorph.secondCountableTopology

@[simp] theorem h3ZornRealHomeomorph_apply (X : H3Zorn ℝ) :
    h3ZornRealHomeomorph X = h3ZornRealCoordEquiv X := rfl

theorem isCompact_h3Zorn_coordinate_image {K : Set (H3Zorn ℝ)} :
    IsCompact (h3ZornRealHomeomorph '' K) ↔ IsCompact K :=
  h3ZornRealHomeomorph.isCompact_image

theorem continuous_h3Zorn_α₁ :
    Continuous (fun X : H3Zorn ℝ => X.α₁) :=
  continuous_h3ZornRealCoordEquiv.fst

theorem continuous_h3Zorn_α₂ :
    Continuous (fun X : H3Zorn ℝ => X.α₂) :=
  continuous_h3ZornRealCoordEquiv.snd.fst

theorem continuous_h3Zorn_α₃ :
    Continuous (fun X : H3Zorn ℝ => X.α₃) :=
  continuous_h3ZornRealCoordEquiv.snd.snd.fst

theorem continuous_h3Zorn_a :
    Continuous (fun X : H3Zorn ℝ => X.a) :=
  continuous_h3ZornRealCoordEquiv.snd.snd.snd.fst

theorem continuous_h3Zorn_b :
    Continuous (fun X : H3Zorn ℝ => X.b) :=
  continuous_h3ZornRealCoordEquiv.snd.snd.snd.snd.fst

theorem continuous_h3Zorn_c :
    Continuous (fun X : H3Zorn ℝ => X.c) :=
  continuous_h3ZornRealCoordEquiv.snd.snd.snd.snd.snd

theorem continuous_zornVectorMatrix_trace :
    Continuous (ZornVectorMatrix.trace : ZornVectorMatrix ℝ → ℝ) := by
  simpa [ZornVectorMatrix.trace] using
    continuous_zornVectorMatrix_a.add continuous_zornVectorMatrix_b

theorem continuous_zornVectorMatrix_norm :
    Continuous (ZornVectorMatrix.norm : ZornVectorMatrix ℝ → ℝ) := by
  have hv₀ := continuous_zornVectorMatrix_v (0 : Fin 3)
  have hv₁ := continuous_zornVectorMatrix_v (1 : Fin 3)
  have hv₂ := continuous_zornVectorMatrix_v (2 : Fin 3)
  have hw₀ := continuous_zornVectorMatrix_w (0 : Fin 3)
  have hw₁ := continuous_zornVectorMatrix_w (1 : Fin 3)
  have hw₂ := continuous_zornVectorMatrix_w (2 : Fin 3)
  have hdot : Continuous (fun X : ZornVectorMatrix ℝ =>
      X.v 0 * X.w 0 + X.v 1 * X.w 1 + X.v 2 * X.w 2) := by
    exact ((hv₀.mul hw₀).add (hv₁.mul hw₁)).add (hv₂.mul hw₂)
  change Continuous (fun X : ZornVectorMatrix ℝ =>
    X.a * X.b - ZornVec3.dot X.v X.w)
  simpa [ZornVec3.dot_eq_sum_coords] using
    (continuous_zornVectorMatrix_a.mul continuous_zornVectorMatrix_b).sub hdot

theorem continuous_zornVectorMatrix_mul_a :
    Continuous (fun p : ZornVectorMatrix ℝ × ZornVectorMatrix ℝ =>
      (ZornVectorMatrix.mul p.1 p.2).a) := by
  have hdot : Continuous (fun p : ZornVectorMatrix ℝ × ZornVectorMatrix ℝ =>
      ZornVec3.dot p.1.v p.2.w) := by
    have h₀ := ((continuous_zornVectorMatrix_v 0).comp continuous_fst).mul
      ((continuous_zornVectorMatrix_w 0).comp continuous_snd)
    have h₁ := ((continuous_zornVectorMatrix_v 1).comp continuous_fst).mul
      ((continuous_zornVectorMatrix_w 1).comp continuous_snd)
    have h₂ := ((continuous_zornVectorMatrix_v 2).comp continuous_fst).mul
      ((continuous_zornVectorMatrix_w 2).comp continuous_snd)
    simpa [ZornVec3.dot_eq_sum_coords] using (h₀.add h₁).add h₂
  simpa [ZornVectorMatrix.mul] using
    ((continuous_zornVectorMatrix_a.comp continuous_fst).mul
      (continuous_zornVectorMatrix_a.comp continuous_snd)).add hdot

theorem continuous_zornVectorMatrix_mul_b :
    Continuous (fun p : ZornVectorMatrix ℝ × ZornVectorMatrix ℝ =>
      (ZornVectorMatrix.mul p.1 p.2).b) := by
  have hdot : Continuous (fun p : ZornVectorMatrix ℝ × ZornVectorMatrix ℝ =>
      ZornVec3.dot p.1.w p.2.v) := by
    have h₀ := ((continuous_zornVectorMatrix_w 0).comp continuous_fst).mul
      ((continuous_zornVectorMatrix_v 0).comp continuous_snd)
    have h₁ := ((continuous_zornVectorMatrix_w 1).comp continuous_fst).mul
      ((continuous_zornVectorMatrix_v 1).comp continuous_snd)
    have h₂ := ((continuous_zornVectorMatrix_w 2).comp continuous_fst).mul
      ((continuous_zornVectorMatrix_v 2).comp continuous_snd)
    simpa [ZornVec3.dot_eq_sum_coords] using (h₀.add h₁).add h₂
  simpa [ZornVectorMatrix.mul] using
    hdot.add ((continuous_zornVectorMatrix_b.comp continuous_fst).mul
      (continuous_zornVectorMatrix_b.comp continuous_snd))

theorem continuous_zornVectorMatrix_mul_v (i : Fin 3) :
    Continuous (fun p : ZornVectorMatrix ℝ × ZornVectorMatrix ℝ =>
      (ZornVectorMatrix.mul p.1 p.2).v i) := by
  fin_cases i
  · simpa [ZornVectorMatrix.mul, ZornVec3.cross] using
      (((continuous_zornVectorMatrix_a.comp continuous_fst).mul
        ((continuous_zornVectorMatrix_v 0).comp continuous_snd)).add
        ((continuous_zornVectorMatrix_b.comp continuous_snd).mul
          ((continuous_zornVectorMatrix_v 0).comp continuous_fst))).sub
        (((continuous_zornVectorMatrix_w 1).comp continuous_fst).mul
          ((continuous_zornVectorMatrix_w 2).comp continuous_snd) |>.sub
          (((continuous_zornVectorMatrix_w 2).comp continuous_fst).mul
            ((continuous_zornVectorMatrix_w 1).comp continuous_snd)))
  · simpa [ZornVectorMatrix.mul, ZornVec3.cross] using
      (((continuous_zornVectorMatrix_a.comp continuous_fst).mul
        ((continuous_zornVectorMatrix_v 1).comp continuous_snd)).add
        ((continuous_zornVectorMatrix_b.comp continuous_snd).mul
          ((continuous_zornVectorMatrix_v 1).comp continuous_fst))).sub
        (((continuous_zornVectorMatrix_w 2).comp continuous_fst).mul
          ((continuous_zornVectorMatrix_w 0).comp continuous_snd) |>.sub
          (((continuous_zornVectorMatrix_w 0).comp continuous_fst).mul
            ((continuous_zornVectorMatrix_w 2).comp continuous_snd)))
  · simpa [ZornVectorMatrix.mul, ZornVec3.cross] using
      (((continuous_zornVectorMatrix_a.comp continuous_fst).mul
        ((continuous_zornVectorMatrix_v 2).comp continuous_snd)).add
        ((continuous_zornVectorMatrix_b.comp continuous_snd).mul
          ((continuous_zornVectorMatrix_v 2).comp continuous_fst))).sub
        (((continuous_zornVectorMatrix_w 0).comp continuous_fst).mul
          ((continuous_zornVectorMatrix_w 1).comp continuous_snd) |>.sub
          (((continuous_zornVectorMatrix_w 1).comp continuous_fst).mul
            ((continuous_zornVectorMatrix_w 0).comp continuous_snd)))

theorem continuous_zornVectorMatrix_mul_w (i : Fin 3) :
    Continuous (fun p : ZornVectorMatrix ℝ × ZornVectorMatrix ℝ =>
      (ZornVectorMatrix.mul p.1 p.2).w i) := by
  fin_cases i
  · simpa [ZornVectorMatrix.mul, ZornVec3.cross] using
      (((continuous_zornVectorMatrix_a.comp continuous_snd).mul
        ((continuous_zornVectorMatrix_w 0).comp continuous_fst)).add
        ((continuous_zornVectorMatrix_b.comp continuous_fst).mul
          ((continuous_zornVectorMatrix_w 0).comp continuous_snd))).add
        (((continuous_zornVectorMatrix_v 1).comp continuous_fst).mul
          ((continuous_zornVectorMatrix_v 2).comp continuous_snd) |>.sub
          (((continuous_zornVectorMatrix_v 2).comp continuous_fst).mul
            ((continuous_zornVectorMatrix_v 1).comp continuous_snd)))
  · simpa [ZornVectorMatrix.mul, ZornVec3.cross] using
      (((continuous_zornVectorMatrix_a.comp continuous_snd).mul
        ((continuous_zornVectorMatrix_w 1).comp continuous_fst)).add
        ((continuous_zornVectorMatrix_b.comp continuous_fst).mul
          ((continuous_zornVectorMatrix_w 1).comp continuous_snd))).add
        (((continuous_zornVectorMatrix_v 2).comp continuous_fst).mul
          ((continuous_zornVectorMatrix_v 0).comp continuous_snd) |>.sub
          (((continuous_zornVectorMatrix_v 0).comp continuous_fst).mul
            ((continuous_zornVectorMatrix_v 2).comp continuous_snd)))
  · simpa [ZornVectorMatrix.mul, ZornVec3.cross] using
      (((continuous_zornVectorMatrix_a.comp continuous_snd).mul
        ((continuous_zornVectorMatrix_w 2).comp continuous_fst)).add
        ((continuous_zornVectorMatrix_b.comp continuous_fst).mul
          ((continuous_zornVectorMatrix_w 2).comp continuous_snd))).add
        (((continuous_zornVectorMatrix_v 0).comp continuous_fst).mul
          ((continuous_zornVectorMatrix_v 1).comp continuous_snd) |>.sub
          (((continuous_zornVectorMatrix_v 1).comp continuous_fst).mul
            ((continuous_zornVectorMatrix_v 0).comp continuous_snd)))

theorem continuous_zornVectorMatrix_mul :
    Continuous
      (fun p : ZornVectorMatrix ℝ × ZornVectorMatrix ℝ =>
        ZornVectorMatrix.mul p.1 p.2) := by
  have hv : Continuous (fun p : ZornVectorMatrix ℝ × ZornVectorMatrix ℝ =>
      (ZornVectorMatrix.mul p.1 p.2).v) := by
    exact continuous_pi (fun i => continuous_zornVectorMatrix_mul_v i)
  have hw : Continuous (fun p : ZornVectorMatrix ℝ × ZornVectorMatrix ℝ =>
      (ZornVectorMatrix.mul p.1 p.2).w) := by
    exact continuous_pi (fun i => continuous_zornVectorMatrix_mul_w i)
  have htuple : Continuous (fun p : ZornVectorMatrix ℝ × ZornVectorMatrix ℝ =>
      ((ZornVectorMatrix.mul p.1 p.2).a,
        (ZornVectorMatrix.mul p.1 p.2).v,
        (ZornVectorMatrix.mul p.1 p.2).w,
        (ZornVectorMatrix.mul p.1 p.2).b)) := by
    exact continuous_zornVectorMatrix_mul_a.prodMk
      (hv.prodMk (hw.prodMk continuous_zornVectorMatrix_mul_b))
  apply (continuous_induced_rng).2
  simpa [ZornVectorMatrix.coordEquiv, Function.comp_def] using htuple

theorem continuous_zornVectorMatrix_conj :
    Continuous (ZornVectorMatrix.conj : ZornVectorMatrix ℝ → ZornVectorMatrix ℝ) := by
  have hv : Continuous (fun X : ZornVectorMatrix ℝ => fun i => -X.v i) := by
    exact continuous_pi (fun i => (continuous_zornVectorMatrix_v i).neg)
  have hw : Continuous (fun X : ZornVectorMatrix ℝ => fun i => -X.w i) := by
    exact continuous_pi (fun i => (continuous_zornVectorMatrix_w i).neg)
  apply (continuous_induced_rng).2
  simpa [ZornVectorMatrix.coordEquiv, ZornVectorMatrix.conj, Function.comp_def] using
    continuous_zornVectorMatrix_b.prodMk
      (hv.prodMk (hw.prodMk continuous_zornVectorMatrix_a))

theorem continuous_zornVectorMatrix_sub :
    Continuous
      (fun p : ZornVectorMatrix ℝ × ZornVectorMatrix ℝ =>
        ZornVectorMatrix.sub p.1 p.2) := by
  have ha := (continuous_zornVectorMatrix_a.comp continuous_fst).sub
    (continuous_zornVectorMatrix_a.comp continuous_snd)
  have hb := (continuous_zornVectorMatrix_b.comp continuous_fst).sub
    (continuous_zornVectorMatrix_b.comp continuous_snd)
  have hv : Continuous (fun p : ZornVectorMatrix ℝ × ZornVectorMatrix ℝ =>
      fun i => p.1.v i - p.2.v i) := by
    exact continuous_pi (fun i =>
      (continuous_zornVectorMatrix_v i).comp continuous_fst |>.sub
        ((continuous_zornVectorMatrix_v i).comp continuous_snd))
  have hw : Continuous (fun p : ZornVectorMatrix ℝ × ZornVectorMatrix ℝ =>
      fun i => p.1.w i - p.2.w i) := by
    exact continuous_pi (fun i =>
      (continuous_zornVectorMatrix_w i).comp continuous_fst |>.sub
        ((continuous_zornVectorMatrix_w i).comp continuous_snd))
  apply (continuous_induced_rng).2
  simpa [ZornVectorMatrix.coordEquiv, ZornVectorMatrix.sub,
    ZornVectorMatrix.add, ZornVectorMatrix.neg, Function.comp_def] using
    ha.prodMk (hv.prodMk (hw.prodMk hb))

theorem continuous_zornVectorMatrix_smul :
    Continuous
      (fun p : ℝ × ZornVectorMatrix ℝ =>
        ZornVectorMatrix.smul p.1 p.2) := by
  have ha := continuous_fst.mul (continuous_zornVectorMatrix_a.comp continuous_snd)
  have hb := continuous_fst.mul (continuous_zornVectorMatrix_b.comp continuous_snd)
  have hv : Continuous (fun p : ℝ × ZornVectorMatrix ℝ =>
      fun i => p.1 * p.2.v i) := by
    exact continuous_pi (fun i =>
      continuous_fst.mul ((continuous_zornVectorMatrix_v i).comp continuous_snd))
  have hw : Continuous (fun p : ℝ × ZornVectorMatrix ℝ =>
      fun i => p.1 * p.2.w i) := by
    exact continuous_pi (fun i =>
      continuous_fst.mul ((continuous_zornVectorMatrix_w i).comp continuous_snd))
  apply (continuous_induced_rng).2
  simpa [ZornVectorMatrix.coordEquiv, ZornVectorMatrix.smul, Function.comp_def] using
    ha.prodMk (hv.prodMk (hw.prodMk hb))

theorem continuous_zornVectorMatrix_neg :
    Continuous (ZornVectorMatrix.neg : ZornVectorMatrix ℝ → ZornVectorMatrix ℝ) := by
  have hv : Continuous (fun X : ZornVectorMatrix ℝ => fun i => -X.v i) := by
    exact continuous_pi (fun i => (continuous_zornVectorMatrix_v i).neg)
  have hw : Continuous (fun X : ZornVectorMatrix ℝ => fun i => -X.w i) := by
    exact continuous_pi (fun i => (continuous_zornVectorMatrix_w i).neg)
  apply (continuous_induced_rng).2
  simpa [ZornVectorMatrix.coordEquiv, ZornVectorMatrix.neg, Function.comp_def] using
    (continuous_zornVectorMatrix_a.neg).prodMk
      (hv.prodMk (hw.prodMk (continuous_zornVectorMatrix_b.neg)))

theorem continuous_zornVectorMatrix_add :
    Continuous
      (fun p : ZornVectorMatrix ℝ × ZornVectorMatrix ℝ =>
        ZornVectorMatrix.add p.1 p.2) := by
  have ha := (continuous_zornVectorMatrix_a.comp continuous_fst).add
    (continuous_zornVectorMatrix_a.comp continuous_snd)
  have hb := (continuous_zornVectorMatrix_b.comp continuous_fst).add
    (continuous_zornVectorMatrix_b.comp continuous_snd)
  have hv : Continuous (fun p : ZornVectorMatrix ℝ × ZornVectorMatrix ℝ =>
      fun i => p.1.v i + p.2.v i) := by
    exact continuous_pi (fun i =>
      (continuous_zornVectorMatrix_v i).comp continuous_fst |>.add
        ((continuous_zornVectorMatrix_v i).comp continuous_snd))
  have hw : Continuous (fun p : ZornVectorMatrix ℝ × ZornVectorMatrix ℝ =>
      fun i => p.1.w i + p.2.w i) := by
    exact continuous_pi (fun i =>
      (continuous_zornVectorMatrix_w i).comp continuous_fst |>.add
        ((continuous_zornVectorMatrix_w i).comp continuous_snd))
  apply (continuous_induced_rng).2
  simpa [ZornVectorMatrix.coordEquiv, ZornVectorMatrix.add, Function.comp_def] using
    ha.prodMk (hv.prodMk (hw.prodMk hb))

theorem continuous_h3Zorn_normCubic :
    Continuous (H3Zorn.normCubic : H3Zorn ℝ → ℝ) := by
  have hα₁ := continuous_h3Zorn_α₁
  have hα₂ := continuous_h3Zorn_α₂
  have hα₃ := continuous_h3Zorn_α₃
  have hnorm_a := continuous_zornVectorMatrix_norm.comp continuous_h3Zorn_a
  have hnorm_b := continuous_zornVectorMatrix_norm.comp continuous_h3Zorn_b
  have hnorm_c := continuous_zornVectorMatrix_norm.comp continuous_h3Zorn_c
  have hmul_ab := continuous_zornVectorMatrix_mul.comp
    (continuous_h3Zorn_a.prodMk continuous_h3Zorn_b)
  have hmul_abc := continuous_zornVectorMatrix_mul.comp
    (hmul_ab.prodMk continuous_h3Zorn_c)
  have htriple := continuous_zornVectorMatrix_trace.comp hmul_abc
  have hterm₁₂₃ := (hα₁.mul hα₂).mul hα₃
  have hterm₁ := hα₁.mul hnorm_b
  have hterm₂ := hα₂.mul hnorm_c
  have hterm₃ := hα₃.mul hnorm_a
  have hsum₁ := hterm₁₂₃.sub hterm₁
  have hsum₂ := hsum₁.sub hterm₂
  have hsum₃ := hsum₂.sub hterm₃
  simpa [H3Zorn.normCubic] using hsum₃.add htriple

theorem isClosed_graph_h3Zorn_normCubic :
    IsClosed
      {p : H3Zorn ℝ × ℝ | H3Zorn.normCubic p.1 = p.2} := by
  exact isClosed_eq
    (continuous_h3Zorn_normCubic.comp continuous_fst)
    continuous_snd

private theorem continuous_h3_six_tuple
    (f₁ f₂ f₃ : H3Zorn ℝ → ℝ)
    (g₁ g₂ g₃ : H3Zorn ℝ → ZornVectorMatrix ℝ)
    (hf₁ : Continuous f₁) (hf₂ : Continuous f₂) (hf₃ : Continuous f₃)
    (hg₁ : Continuous g₁) (hg₂ : Continuous g₂) (hg₃ : Continuous g₃) :
    Continuous (fun X => (f₁ X, f₂ X, f₃ X, g₁ X, g₂ X, g₃ X)) := by
  exact hf₁.prodMk (hf₂.prodMk (hf₃.prodMk (hg₁.prodMk (hg₂.prodMk hg₃))))

private theorem continuous_six_tuple {X : Type*} [TopologicalSpace X]
    (f₁ f₂ f₃ : X → ℝ)
    (g₁ g₂ g₃ : X → ZornVectorMatrix ℝ)
    (hf₁ : Continuous f₁) (hf₂ : Continuous f₂) (hf₃ : Continuous f₃)
    (hg₁ : Continuous g₁) (hg₂ : Continuous g₂) (hg₃ : Continuous g₃) :
    Continuous (fun X => (f₁ X, f₂ X, f₃ X, g₁ X, g₂ X, g₃ X)) := by
  exact hf₁.prodMk (hf₂.prodMk (hf₃.prodMk (hg₁.prodMk (hg₂.prodMk hg₃))))

theorem continuous_h3Zorn_add :
    Continuous (fun p : H3Zorn ℝ × H3Zorn ℝ => p.1 + p.2) := by
  have hfst : Continuous (fun p : H3Zorn ℝ × H3Zorn ℝ => p.1) := continuous_fst
  have hsnd : Continuous (fun p : H3Zorn ℝ × H3Zorn ℝ => p.2) := continuous_snd
  have ha := continuous_zornVectorMatrix_add.comp
    ((continuous_h3Zorn_a.comp hfst).prodMk (continuous_h3Zorn_a.comp hsnd))
  have hb := continuous_zornVectorMatrix_add.comp
    ((continuous_h3Zorn_b.comp hfst).prodMk (continuous_h3Zorn_b.comp hsnd))
  have hc := continuous_zornVectorMatrix_add.comp
    ((continuous_h3Zorn_c.comp hfst).prodMk (continuous_h3Zorn_c.comp hsnd))
  apply (continuous_induced_rng).2
  simpa [h3ZornRealCoordEquiv, H3Zorn.add_readback, Function.comp_def] using
    continuous_six_tuple
      (fun p : H3Zorn ℝ × H3Zorn ℝ => p.1.α₁ + p.2.α₁)
      (fun p : H3Zorn ℝ × H3Zorn ℝ => p.1.α₂ + p.2.α₂)
      (fun p : H3Zorn ℝ × H3Zorn ℝ => p.1.α₃ + p.2.α₃)
      (fun p : H3Zorn ℝ × H3Zorn ℝ => ZornVectorMatrix.add p.1.a p.2.a)
      (fun p : H3Zorn ℝ × H3Zorn ℝ => ZornVectorMatrix.add p.1.b p.2.b)
      (fun p : H3Zorn ℝ × H3Zorn ℝ => ZornVectorMatrix.add p.1.c p.2.c)
      ((continuous_h3Zorn_α₁.comp hfst).add (continuous_h3Zorn_α₁.comp hsnd))
      ((continuous_h3Zorn_α₂.comp hfst).add (continuous_h3Zorn_α₂.comp hsnd))
      ((continuous_h3Zorn_α₃.comp hfst).add (continuous_h3Zorn_α₃.comp hsnd))
      ha hb hc

theorem continuous_h3Zorn_neg :
    Continuous (fun X : H3Zorn ℝ => -X) := by
  apply (continuous_induced_rng).2
  simpa [h3ZornRealCoordEquiv, H3Zorn.neg_readback, Function.comp_def] using
    continuous_six_tuple
      (fun X : H3Zorn ℝ => -X.α₁)
      (fun X : H3Zorn ℝ => -X.α₂)
      (fun X : H3Zorn ℝ => -X.α₃)
      (fun X : H3Zorn ℝ => ZornVectorMatrix.neg X.a)
      (fun X : H3Zorn ℝ => ZornVectorMatrix.neg X.b)
      (fun X : H3Zorn ℝ => ZornVectorMatrix.neg X.c)
      continuous_h3Zorn_α₁.neg continuous_h3Zorn_α₂.neg continuous_h3Zorn_α₃.neg
      (continuous_zornVectorMatrix_neg.comp continuous_h3Zorn_a)
      (continuous_zornVectorMatrix_neg.comp continuous_h3Zorn_b)
      (continuous_zornVectorMatrix_neg.comp continuous_h3Zorn_c)

theorem continuous_h3Zorn_sub :
    Continuous (fun p : H3Zorn ℝ × H3Zorn ℝ => p.1 - p.2) := by
  simpa [sub_eq_add_neg, Function.comp_def] using
    continuous_h3Zorn_add.comp
      (continuous_fst.prodMk (continuous_h3Zorn_neg.comp continuous_snd))

theorem continuous_h3Zorn_smul :
    Continuous (fun p : ℝ × H3Zorn ℝ => p.1 • p.2) := by
  have hfst : Continuous (fun p : ℝ × H3Zorn ℝ => p.1) := continuous_fst
  have hsnd : Continuous (fun p : ℝ × H3Zorn ℝ => p.2) := continuous_snd
  have hA := continuous_h3Zorn_α₁.comp hsnd
  have hB := continuous_h3Zorn_α₂.comp hsnd
  have hC := continuous_h3Zorn_α₃.comp hsnd
  have ha := continuous_zornVectorMatrix_smul.comp
    (hfst.prodMk (continuous_h3Zorn_a.comp hsnd))
  have hb := continuous_zornVectorMatrix_smul.comp
    (hfst.prodMk (continuous_h3Zorn_b.comp hsnd))
  have hc := continuous_zornVectorMatrix_smul.comp
    (hfst.prodMk (continuous_h3Zorn_c.comp hsnd))
  apply (continuous_induced_rng).2
  simpa [h3ZornRealCoordEquiv, H3Zorn.smul_readback, Function.comp_def] using
    continuous_six_tuple
      (fun p : ℝ × H3Zorn ℝ => p.1 * p.2.α₁)
      (fun p : ℝ × H3Zorn ℝ => p.1 * p.2.α₂)
      (fun p : ℝ × H3Zorn ℝ => p.1 * p.2.α₃)
      (fun p : ℝ × H3Zorn ℝ => ZornVectorMatrix.smul p.1 p.2.a)
      (fun p : ℝ × H3Zorn ℝ => ZornVectorMatrix.smul p.1 p.2.b)
      (fun p : ℝ × H3Zorn ℝ => ZornVectorMatrix.smul p.1 p.2.c)
      (hfst.mul hA) (hfst.mul hB) (hfst.mul hC)
      ha hb hc

instance zornVectorMatrixRealTopologicalAddGroup :
    IsTopologicalAddGroup (ZornVectorMatrix ℝ) where
  continuous_add := continuous_zornVectorMatrix_add
  continuous_neg := continuous_zornVectorMatrix_neg

instance zornVectorMatrixRealContinuousSMul :
    ContinuousSMul ℝ (ZornVectorMatrix ℝ) where
  continuous_smul := continuous_zornVectorMatrix_smul

instance h3ZornRealTopologicalAddGroup :
    IsTopologicalAddGroup (H3Zorn ℝ) where
  continuous_add := continuous_h3Zorn_add
  continuous_neg := continuous_h3Zorn_neg

instance h3ZornRealContinuousSMul :
    ContinuousSMul ℝ (H3Zorn ℝ) where
  continuous_smul := continuous_h3Zorn_smul

theorem continuous_h3Zorn_adjointQuad :
    Continuous (H3Zorn.adjointQuad : H3Zorn ℝ → H3Zorn ℝ) := by
  have hα₁ := continuous_h3Zorn_α₁
  have hα₂ := continuous_h3Zorn_α₂
  have hα₃ := continuous_h3Zorn_α₃
  have ha := continuous_zornVectorMatrix_sub.comp
    ((continuous_zornVectorMatrix_mul.comp
        ((continuous_zornVectorMatrix_conj.comp continuous_h3Zorn_c).prodMk
          (continuous_zornVectorMatrix_conj.comp continuous_h3Zorn_b))).prodMk
      (continuous_zornVectorMatrix_smul.comp
        (hα₃.prodMk continuous_h3Zorn_a)))
  have hb := continuous_zornVectorMatrix_sub.comp
    ((continuous_zornVectorMatrix_mul.comp
        ((continuous_zornVectorMatrix_conj.comp continuous_h3Zorn_a).prodMk
          (continuous_zornVectorMatrix_conj.comp continuous_h3Zorn_c))).prodMk
      (continuous_zornVectorMatrix_smul.comp
        (hα₁.prodMk continuous_h3Zorn_b)))
  have hc := continuous_zornVectorMatrix_sub.comp
    ((continuous_zornVectorMatrix_mul.comp
        ((continuous_zornVectorMatrix_conj.comp continuous_h3Zorn_b).prodMk
          (continuous_zornVectorMatrix_conj.comp continuous_h3Zorn_a))).prodMk
      (continuous_zornVectorMatrix_smul.comp
        (hα₂.prodMk continuous_h3Zorn_c)))
  have hf₁ := (hα₂.mul hα₃).sub
    (continuous_zornVectorMatrix_norm.comp continuous_h3Zorn_b)
  have hf₂ := (hα₁.mul hα₃).sub
    (continuous_zornVectorMatrix_norm.comp continuous_h3Zorn_c)
  have hf₃ := (hα₁.mul hα₂).sub
    (continuous_zornVectorMatrix_norm.comp continuous_h3Zorn_a)
  apply (continuous_induced_rng).2
  simpa [H3Zorn.adjointQuad, h3ZornRealCoordEquiv, Function.comp_def] using
    continuous_h3_six_tuple
      (fun X => X.α₂ * X.α₃ - ZornVectorMatrix.norm X.b)
      (fun X => X.α₁ * X.α₃ - ZornVectorMatrix.norm X.c)
      (fun X => X.α₁ * X.α₂ - ZornVectorMatrix.norm X.a)
      (fun X => ZornVectorMatrix.sub
        (ZornVectorMatrix.mul (ZornVectorMatrix.conj X.c)
          (ZornVectorMatrix.conj X.b))
        (ZornVectorMatrix.smul X.α₃ X.a))
      (fun X => ZornVectorMatrix.sub
        (ZornVectorMatrix.mul (ZornVectorMatrix.conj X.a)
          (ZornVectorMatrix.conj X.c))
        (ZornVectorMatrix.smul X.α₁ X.b))
      (fun X => ZornVectorMatrix.sub
        (ZornVectorMatrix.mul (ZornVectorMatrix.conj X.b)
          (ZornVectorMatrix.conj X.a))
        (ZornVectorMatrix.smul X.α₂ X.c))
      hf₁ hf₂ hf₃ ha hb hc

theorem isClosed_graph_h3Zorn_adjointQuad :
    IsClosed
      {p : H3Zorn ℝ × H3Zorn ℝ | H3Zorn.adjointQuad p.1 = p.2} := by
  exact isClosed_eq
    ((continuous_h3Zorn_adjointQuad).comp continuous_fst)
    continuous_snd

theorem continuous_h3Zorn_traceBilin :
    Continuous (fun p : H3Zorn ℝ × H3Zorn ℝ =>
      H3Zorn.traceBilin p.1 p.2) := by
  have hfst : Continuous (fun p : H3Zorn ℝ × H3Zorn ℝ => p.1) := continuous_fst
  have hsnd : Continuous (fun p : H3Zorn ℝ × H3Zorn ℝ => p.2) := continuous_snd
  have hdiag₁ := (continuous_h3Zorn_α₁.comp hfst).mul
    (continuous_h3Zorn_α₁.comp hsnd)
  have hdiag₂ := (continuous_h3Zorn_α₂.comp hfst).mul
    (continuous_h3Zorn_α₂.comp hsnd)
  have hdiag₃ := (continuous_h3Zorn_α₃.comp hfst).mul
    (continuous_h3Zorn_α₃.comp hsnd)
  have hconj_a := continuous_zornVectorMatrix_conj.comp
    (continuous_h3Zorn_a.comp hsnd)
  have hconj_b := continuous_zornVectorMatrix_conj.comp
    (continuous_h3Zorn_b.comp hsnd)
  have hconj_c := continuous_zornVectorMatrix_conj.comp
    (continuous_h3Zorn_c.comp hsnd)
  have hmul_a := continuous_zornVectorMatrix_mul.comp
    ((continuous_h3Zorn_a.comp hfst).prodMk hconj_a)
  have hmul_b := continuous_zornVectorMatrix_mul.comp
    ((continuous_h3Zorn_b.comp hfst).prodMk hconj_b)
  have hmul_c := continuous_zornVectorMatrix_mul.comp
    ((continuous_h3Zorn_c.comp hfst).prodMk hconj_c)
  have htrace_a := continuous_zornVectorMatrix_trace.comp hmul_a
  have htrace_b := continuous_zornVectorMatrix_trace.comp hmul_b
  have htrace_c := continuous_zornVectorMatrix_trace.comp hmul_c
  simpa [H3Zorn.traceBilin] using
    (((((hdiag₁.add hdiag₂).add hdiag₃).add htrace_a).add htrace_b).add htrace_c)

theorem continuous_h3Zorn_crossProduct :
    Continuous (fun p : H3Zorn ℝ × H3Zorn ℝ =>
      H3Zorn.crossProduct p.1 p.2) := by
  have hfst : Continuous (fun p : H3Zorn ℝ × H3Zorn ℝ => p.1) := continuous_fst
  have hsnd : Continuous (fun p : H3Zorn ℝ × H3Zorn ℝ => p.2) := continuous_snd
  have hsum := continuous_h3Zorn_adjointQuad.comp continuous_h3Zorn_add
  have hx := continuous_h3Zorn_adjointQuad.comp hfst
  have hy := continuous_h3Zorn_adjointQuad.comp hsnd
  have hfirst := continuous_h3Zorn_sub.comp (hsum.prodMk hx)
  have hsecond := continuous_h3Zorn_sub.comp (hfirst.prodMk hy)
  simpa [H3Zorn.crossProduct, Function.comp_def] using hsecond

theorem continuous_h3Zorn_U :
    Continuous (fun p : H3Zorn ℝ × H3Zorn ℝ =>
      H3Zorn.U p.1 p.2) := by
  have hfst : Continuous (fun p : H3Zorn ℝ × H3Zorn ℝ => p.1) := continuous_fst
  have hsnd : Continuous (fun p : H3Zorn ℝ × H3Zorn ℝ => p.2) := continuous_snd
  have htrace := continuous_h3Zorn_traceBilin
  have hpair := htrace.comp (hfst.prodMk hsnd)
  have hsmul := continuous_h3Zorn_smul.comp (hpair.prodMk hfst)
  have hadj := continuous_h3Zorn_adjointQuad.comp hfst
  have hcross := continuous_h3Zorn_crossProduct.comp (hadj.prodMk hsnd)
  have hsub := continuous_h3Zorn_sub.comp (hsmul.prodMk hcross)
  simpa [H3Zorn.U, Function.comp_def] using hsub

theorem continuous_h3Zorn_T :
    Continuous
      (fun p : (H3Zorn ℝ × H3Zorn ℝ) × H3Zorn ℝ =>
        H3Zorn.T p.1.1 p.1.2 p.2) := by
  have hx : Continuous
      (fun p : (H3Zorn ℝ × H3Zorn ℝ) × H3Zorn ℝ => p.1.1) :=
    continuous_fst.comp continuous_fst
  have hy : Continuous
      (fun p : (H3Zorn ℝ × H3Zorn ℝ) × H3Zorn ℝ => p.1.2) :=
    continuous_snd.comp continuous_fst
  have hz : Continuous
      (fun p : (H3Zorn ℝ × H3Zorn ℝ) × H3Zorn ℝ => p.2) :=
    continuous_snd
  have hxz : Continuous
      (fun p : (H3Zorn ℝ × H3Zorn ℝ) × H3Zorn ℝ => p.1.1 + p.2) :=
    continuous_h3Zorn_add.comp (hx.prodMk hz)
  have hu₁ := continuous_h3Zorn_U.comp (hxz.prodMk hy)
  have hu₂ := continuous_h3Zorn_U.comp (hx.prodMk hy)
  have hu₃ := continuous_h3Zorn_U.comp (hz.prodMk hy)
  have hleft := continuous_h3Zorn_sub.comp (hu₁.prodMk hu₂)
  have hresult := continuous_h3Zorn_sub.comp (hleft.prodMk hu₃)
  simpa [H3Zorn.T, Function.comp_def] using hresult

theorem isClosed_graph_h3Zorn_traceBilin :
    IsClosed
      {p : (H3Zorn ℝ × H3Zorn ℝ) × ℝ |
        H3Zorn.traceBilin p.1.1 p.1.2 = p.2} := by
  exact isClosed_eq
    ((continuous_h3Zorn_traceBilin).comp continuous_fst)
    continuous_snd

theorem isClosed_graph_h3Zorn_crossProduct :
    IsClosed
      {p : (H3Zorn ℝ × H3Zorn ℝ) × H3Zorn ℝ |
        H3Zorn.crossProduct p.1.1 p.1.2 = p.2} := by
  exact isClosed_eq
    ((continuous_h3Zorn_crossProduct).comp continuous_fst)
    continuous_snd

theorem isClosed_graph_h3Zorn_U :
    IsClosed
      {p : (H3Zorn ℝ × H3Zorn ℝ) × H3Zorn ℝ |
        H3Zorn.U p.1.1 p.1.2 = p.2} := by
  exact isClosed_eq
    ((continuous_h3Zorn_U).comp continuous_fst)
    continuous_snd

theorem isClosed_graph_h3Zorn_T :
    IsClosed
      {p : ((H3Zorn ℝ × H3Zorn ℝ) × H3Zorn ℝ) × H3Zorn ℝ |
        H3Zorn.T p.1.1.1 p.1.1.2 p.1.2 = p.2} := by
  exact isClosed_eq
    ((continuous_h3Zorn_T).comp continuous_fst)
    continuous_snd

theorem continuous_h3Zorn_candidateJordanMul :
    Continuous (fun p : H3Zorn ℝ × H3Zorn ℝ =>
      candidateJordanMul p.1 p.2) := by
  have hfst : Continuous (fun p : H3Zorn ℝ × H3Zorn ℝ => p.1) := continuous_fst
  have hsnd : Continuous (fun p : H3Zorn ℝ × H3Zorn ℝ => p.2) := continuous_snd
  have hone : Continuous (fun _ : H3Zorn ℝ × H3Zorn ℝ => (1 : H3Zorn ℝ)) :=
    continuous_const
  have htriple : Continuous
      (fun p : H3Zorn ℝ × H3Zorn ℝ => ((p.1, (1 : H3Zorn ℝ)), p.2)) :=
    (hfst.prodMk hone).prodMk hsnd
  have hT := continuous_h3Zorn_T.comp htriple
  have hscalar : Continuous
      (fun _ : H3Zorn ℝ × H3Zorn ℝ => (1 / 2 : ℝ)) := continuous_const
  have hsmul := continuous_h3Zorn_smul.comp (hscalar.prodMk hT)
  simpa [candidateJordanMul, Function.comp_def] using hsmul

theorem continuous_h3Zorn_jordanMul :
    Continuous (fun p : H3Zorn ℝ × H3Zorn ℝ => p.1 * p.2) := by
  simpa only [candidateJordanMul_eq_mul] using
    continuous_h3Zorn_candidateJordanMul

theorem isClosed_graph_h3Zorn_jordanMul :
    IsClosed
      {p : (H3Zorn ℝ × H3Zorn ℝ) × H3Zorn ℝ |
        p.1.1 * p.1.2 = p.2} := by
  exact isClosed_eq
    ((continuous_h3Zorn_jordanMul).comp continuous_fst)
    continuous_snd

theorem continuous_S3OnH3Zorn (σ : S3Perm) :
    Continuous (S3OnH3Zorn σ : H3Zorn ℝ → H3Zorn ℝ) := by
  apply (continuous_induced_rng).2
  rcases σ with (_ | _ | _ | _ | _ | _)
  · simpa [S3OnH3Zorn, h3ZornRealCoordEquiv, h3zornFromPeirce,
      h3zornPeirce, S3OnH3ZornPeirce, Function.comp_def] using
      continuous_h3_six_tuple
        (fun X => X.α₁) (fun X => X.α₂) (fun X => X.α₃)
        (fun X => X.a) (fun X => X.b) (fun X => X.c)
        continuous_h3Zorn_α₁ continuous_h3Zorn_α₂ continuous_h3Zorn_α₃
        continuous_h3Zorn_a continuous_h3Zorn_b continuous_h3Zorn_c
  · simpa [S3OnH3Zorn, h3ZornRealCoordEquiv, h3zornFromPeirce,
      h3zornPeirce, S3OnH3ZornPeirce, Function.comp_def] using
      continuous_h3_six_tuple
        (fun X => X.α₂) (fun X => X.α₁) (fun X => X.α₃)
        (fun X => (X.a).conj) (fun X => (X.c).conj) (fun X => (X.b).conj)
        continuous_h3Zorn_α₂ continuous_h3Zorn_α₁ continuous_h3Zorn_α₃
        (continuous_zornVectorMatrix_conj.comp continuous_h3Zorn_a)
        (continuous_zornVectorMatrix_conj.comp continuous_h3Zorn_c)
        (continuous_zornVectorMatrix_conj.comp continuous_h3Zorn_b)
  · simpa [S3OnH3Zorn, h3ZornRealCoordEquiv, h3zornFromPeirce,
      h3zornPeirce, S3OnH3ZornPeirce, Function.comp_def] using
      continuous_h3_six_tuple
        (fun X => X.α₁) (fun X => X.α₃) (fun X => X.α₂)
        (fun X => (X.c).conj) (fun X => (X.b).conj) (fun X => (X.a).conj)
        continuous_h3Zorn_α₁ continuous_h3Zorn_α₃ continuous_h3Zorn_α₂
        (continuous_zornVectorMatrix_conj.comp continuous_h3Zorn_c)
        (continuous_zornVectorMatrix_conj.comp continuous_h3Zorn_b)
        (continuous_zornVectorMatrix_conj.comp continuous_h3Zorn_a)
  · simpa [S3OnH3Zorn, h3ZornRealCoordEquiv, h3zornFromPeirce,
      h3zornPeirce, S3OnH3ZornPeirce, Function.comp_def] using
      continuous_h3_six_tuple
        (fun X => X.α₃) (fun X => X.α₂) (fun X => X.α₁)
        (fun X => (X.b).conj) (fun X => (X.a).conj) (fun X => (X.c).conj)
        continuous_h3Zorn_α₃ continuous_h3Zorn_α₂ continuous_h3Zorn_α₁
        (continuous_zornVectorMatrix_conj.comp continuous_h3Zorn_b)
        (continuous_zornVectorMatrix_conj.comp continuous_h3Zorn_a)
        (continuous_zornVectorMatrix_conj.comp continuous_h3Zorn_c)
  · simpa [S3OnH3Zorn, h3ZornRealCoordEquiv, h3zornFromPeirce,
      h3zornPeirce, S3OnH3ZornPeirce, Function.comp_def] using
      continuous_h3_six_tuple
        (fun X => X.α₃) (fun X => X.α₁) (fun X => X.α₂)
        (fun X => X.c) (fun X => X.a) (fun X => X.b)
        continuous_h3Zorn_α₃ continuous_h3Zorn_α₁ continuous_h3Zorn_α₂
        continuous_h3Zorn_c continuous_h3Zorn_a continuous_h3Zorn_b
  · simpa [S3OnH3Zorn, h3ZornRealCoordEquiv, h3zornFromPeirce,
      h3zornPeirce, S3OnH3ZornPeirce, Function.comp_def] using
      continuous_h3_six_tuple
        (fun X => X.α₂) (fun X => X.α₃) (fun X => X.α₁)
        (fun X => X.b) (fun X => X.c) (fun X => X.a)
        continuous_h3Zorn_α₂ continuous_h3Zorn_α₃ continuous_h3Zorn_α₁
        continuous_h3Zorn_b continuous_h3Zorn_c continuous_h3Zorn_a

theorem isClosed_graph_S3OnH3Zorn (σ : S3Perm) :
    IsClosed
      {p : H3Zorn ℝ × H3Zorn ℝ | S3OnH3Zorn σ p.1 = p.2} := by
  exact isClosed_eq
    ((continuous_S3OnH3Zorn σ).comp continuous_fst)
    continuous_snd

theorem continuous_normCubic_after_S3 (σ : S3Perm) :
    Continuous (fun X : H3Zorn ℝ =>
      H3Zorn.normCubic (S3OnH3Zorn σ X)) :=
  continuous_h3Zorn_normCubic.comp (continuous_S3OnH3Zorn σ)

theorem isClosed_normCubic_level (r : ℝ) :
    IsClosed {X : H3Zorn ℝ | H3Zorn.normCubic X = r} := by
  change IsClosed (H3Zorn.normCubic ⁻¹' ({r} : Set ℝ))
  exact isClosed_singleton.preimage continuous_h3Zorn_normCubic

theorem isClosed_normCubic_after_S3_level (σ : S3Perm) (r : ℝ) :
    IsClosed {X : H3Zorn ℝ |
      H3Zorn.normCubic (S3OnH3Zorn σ X) = r} := by
  change IsClosed
    ((fun X : H3Zorn ℝ => H3Zorn.normCubic (S3OnH3Zorn σ X)) ⁻¹'
      ({r} : Set ℝ))
  exact isClosed_singleton.preimage (continuous_normCubic_after_S3 σ)

def S3OnH3ZornHomeomorph (σ : S3Perm) :
    H3Zorn ℝ ≃ₜ H3Zorn ℝ where
  toEquiv := (S3OnH3ZornLinearEquiv σ).toEquiv
  continuous_toFun := continuous_S3OnH3Zorn σ
  continuous_invFun := continuous_S3OnH3Zorn (S3Perm.inverse σ)

def S3OnH3ZornContinuousLinearEquiv (σ : S3Perm) :
    H3Zorn ℝ ≃L[ℝ] H3Zorn ℝ where
  toLinearEquiv := S3OnH3ZornLinearEquiv σ
  continuous_toFun := continuous_S3OnH3Zorn σ
  continuous_invFun := by
    change Continuous (S3OnH3Zorn (S3Perm.inverse σ))
    exact continuous_S3OnH3Zorn (S3Perm.inverse σ)

@[simp] theorem S3OnH3ZornContinuousLinearEquiv_apply
    (σ : S3Perm) (X : H3Zorn ℝ) :
    S3OnH3ZornContinuousLinearEquiv σ X = S3OnH3Zorn σ X := rfl

@[simp] theorem S3OnH3ZornHomeomorph_apply (σ : S3Perm) (X : H3Zorn ℝ) :
    S3OnH3ZornHomeomorph σ X = S3OnH3Zorn σ X := rfl

theorem isClosedMap_S3OnH3Zorn (σ : S3Perm) :
    IsClosedMap (S3OnH3ZornHomeomorph σ) :=
  (S3OnH3ZornHomeomorph σ).isClosedMap

theorem isClosed_S3OnH3Zorn_image (σ : S3Perm)
    {K : Set (H3Zorn ℝ)} (hK : IsClosed K) :
    IsClosed (S3OnH3ZornHomeomorph σ '' K) :=
  isClosedMap_S3OnH3Zorn σ K hK

theorem isClosed_S3OnH3Zorn_normCubic_level_image
    (σ : S3Perm) (r : ℝ) :
    IsClosed
      (S3OnH3ZornHomeomorph σ ''
        {X : H3Zorn ℝ | H3Zorn.normCubic X = r}) :=
  isClosed_S3OnH3Zorn_image σ (isClosed_normCubic_level r)

theorem isClosed_S3OnH3Zorn_preimage
    (σ : S3Perm) {K : Set (H3Zorn ℝ)} (hK : IsClosed K) :
    IsClosed ((S3OnH3ZornHomeomorph σ) ⁻¹' K) :=
  hK.preimage (S3OnH3ZornHomeomorph σ).continuous_toFun

theorem isClosed_S3OnH3Zorn_normCubic_level_preimage
    (σ : S3Perm) (r : ℝ) :
    IsClosed
      ((S3OnH3ZornHomeomorph σ) ⁻¹'
        {X : H3Zorn ℝ | H3Zorn.normCubic X = r}) :=
  isClosed_S3OnH3Zorn_preimage σ (isClosed_normCubic_level r)

theorem isOpenMap_S3OnH3Zorn (σ : S3Perm) :
    IsOpenMap (S3OnH3ZornHomeomorph σ) :=
  (S3OnH3ZornHomeomorph σ).isOpenMap

theorem isOpen_S3OnH3Zorn_image (σ : S3Perm)
    {U : Set (H3Zorn ℝ)} (hU : IsOpen U) :
    IsOpen (S3OnH3ZornHomeomorph σ '' U) :=
  isOpenMap_S3OnH3Zorn σ U hU

theorem isOpen_S3OnH3Zorn_preimage
    (σ : S3Perm) {U : Set (H3Zorn ℝ)} (hU : IsOpen U) :
    IsOpen ((S3OnH3ZornHomeomorph σ) ⁻¹' U) :=
  hU.preimage (S3OnH3ZornHomeomorph σ).continuous_toFun

theorem isCompact_S3OnH3Zorn_image (σ : S3Perm)
    {K : Set (H3Zorn ℝ)} (hK : IsCompact K) :
    IsCompact (S3OnH3ZornHomeomorph σ '' K) :=
  hK.image (S3OnH3ZornHomeomorph σ).continuous_toFun

theorem isCompact_S3OnH3Zorn_preimage
    (σ : S3Perm) {K : Set (H3Zorn ℝ)} (hK : IsCompact K) :
    IsCompact ((S3OnH3ZornHomeomorph σ) ⁻¹' K) :=
  (S3OnH3ZornHomeomorph σ).isCompact_preimage.mpr hK

theorem isClosed_normCubic_homeomorph_level (σ : S3Perm) (r : ℝ) :
    IsClosed {X : H3Zorn ℝ |
      H3Zorn.normCubic (S3OnH3ZornHomeomorph σ X) = r} := by
  change IsClosed
    ((fun X : H3Zorn ℝ =>
      H3Zorn.normCubic (S3OnH3ZornHomeomorph σ X)) ⁻¹' ({r} : Set ℝ))
  exact isClosed_singleton.preimage
    (continuous_h3Zorn_normCubic.comp
      (S3OnH3ZornHomeomorph σ).continuous_toFun)

theorem S3OnH3ZornHomeomorph_comp_closure (σ τ : S3Perm) :
    ∃ (ρ : S3Perm),
      S3OnH3ZornHomeomorph ρ =
        (S3OnH3ZornHomeomorph σ).trans (S3OnH3ZornHomeomorph τ) := by
  rcases S3OnH3Zorn_group_closure σ τ with ⟨ρ, hρ⟩
  refine ⟨ρ, ?_⟩
  apply Homeomorph.ext
  intro X
  change S3OnH3Zorn ρ X =
    S3OnH3Zorn τ (S3OnH3Zorn σ X)
  rw [hρ]
  rfl

/-! Finite S₃ orbits are the native topological finite-sector readout. -/

def S3Orbit (X : H3Zorn ℝ) : Set (H3Zorn ℝ) :=
  Set.range (fun σ : S3Perm => S3OnH3Zorn σ X)

instance s3PermGroup : Group S3Perm where
  mul := S3Perm.comp
  one := S3Perm.id
  inv := S3Perm.inverse
  mul_assoc := by
    intro a b c
    rcases a <;> rcases b <;> rcases c <;> rfl
  one_mul := by
    intro a
    rcases a <;> rfl
  mul_one := by
    intro a
    rcases a <;> rfl
  inv_mul_cancel := by
    intro a
    rcases a <;> rfl

@[simp] theorem s3Perm_mul_eq_comp (σ τ : S3Perm) :
    σ * τ = S3Perm.comp σ τ := rfl

@[simp] theorem s3Perm_inv_eq_inverse (σ : S3Perm) :
    σ⁻¹ = S3Perm.inverse σ := rfl

@[simp] theorem S3OnH3Zorn_mul_apply
    (σ τ : S3Perm) (X : H3Zorn ℝ) :
    S3OnH3Zorn (σ * τ) X =
      S3OnH3Zorn τ (S3OnH3Zorn σ X) := by
  rw [s3Perm_mul_eq_comp, congrArg (fun f => f X) (S3OnH3Zorn_comp σ τ)]
  rfl

theorem S3OnH3ZornHomeomorph_comp_mul (σ τ : S3Perm) :
    (S3OnH3ZornHomeomorph σ).trans (S3OnH3ZornHomeomorph τ) =
      S3OnH3ZornHomeomorph (σ * τ) := by
  apply Homeomorph.ext
  intro X
  change S3OnH3Zorn τ (S3OnH3Zorn σ X) =
    S3OnH3Zorn (σ * τ) X
  exact (S3OnH3Zorn_mul_apply σ τ X).symm

theorem S3OnH3ZornContinuousLinearEquiv_comp_mul (σ τ : S3Perm) :
    (S3OnH3ZornContinuousLinearEquiv σ).trans
        (S3OnH3ZornContinuousLinearEquiv τ) =
      S3OnH3ZornContinuousLinearEquiv (σ * τ) := by
  apply ContinuousLinearEquiv.ext
  apply funext
  intro X
  change S3OnH3Zorn τ (S3OnH3Zorn σ X) =
    S3OnH3Zorn (σ * τ) X
  exact (S3OnH3Zorn_mul_apply σ τ X).symm

@[simp] theorem S3OnH3ZornContinuousLinearEquiv_symm_apply
    (σ : S3Perm) (X : H3Zorn ℝ) :
    (S3OnH3ZornContinuousLinearEquiv σ).symm X =
      S3OnH3Zorn (σ⁻¹) X := rfl

theorem S3OnH3ZornContinuousLinearEquiv_symm (σ : S3Perm) :
    (S3OnH3ZornContinuousLinearEquiv σ).symm =
      S3OnH3ZornContinuousLinearEquiv (σ⁻¹) := by
  apply ContinuousLinearEquiv.ext
  apply funext
  intro X
  rfl

def s3PermIndex : S3Perm → Fin 6
  | S3Perm.id => 0
  | S3Perm.s12 => 1
  | S3Perm.s23 => 2
  | S3Perm.s31 => 3
  | S3Perm.s12_s23 => 4
  | S3Perm.s23_s12 => 5

theorem s3PermIndex_injective : Function.Injective s3PermIndex := by
  intro σ τ hστ
  rcases σ with _ | _ | _ | _ | _ | _ <;>
    rcases τ with _ | _ | _ | _ | _ | _ <;>
      simp [s3PermIndex] at hστ ⊢

instance s3PermFinite : Finite S3Perm :=
  Finite.of_injective s3PermIndex s3PermIndex_injective

instance s3PermTopologicalSpace : TopologicalSpace S3Perm := ⊥

instance s3PermDiscreteTopology : DiscreteTopology S3Perm :=
  ⟨rfl⟩

theorem continuous_S3OrbitMap (X : H3Zorn ℝ) :
    Continuous (fun σ : S3Perm => S3OnH3Zorn σ X) :=
  continuous_of_discreteTopology

theorem S3Orbit_eq_orbitMap_image (X : H3Zorn ℝ) :
    S3Orbit X =
      (fun σ : S3Perm => S3OnH3Zorn σ X) '' (Set.univ : Set S3Perm) := by
  ext Y
  constructor
  · rintro ⟨σ, rfl⟩
    exact ⟨σ, Set.mem_univ σ, rfl⟩
  · rintro ⟨σ, -, rfl⟩
    exact ⟨σ, rfl⟩

theorem isCompact_S3Orbit_image (X : H3Zorn ℝ) :
    IsCompact
      ((fun σ : S3Perm => S3OnH3Zorn σ X) '' (Set.univ : Set S3Perm)) :=
  Set.finite_univ.isCompact.image (continuous_S3OrbitMap X)

def s3OrbitMapContinuousMap (X : H3Zorn ℝ) :
    ContinuousMap S3Perm (H3Zorn ℝ) :=
  ContinuousMap.mk (fun σ : S3Perm => S3OnH3Zorn σ X)
    (continuous_S3OrbitMap X)

@[simp] theorem s3OrbitMapContinuousMap_apply
    (X : H3Zorn ℝ) (σ : S3Perm) :
    s3OrbitMapContinuousMap X σ = S3OnH3Zorn σ X := rfl

theorem s3OrbitMapContinuousMap_image_univ (X : H3Zorn ℝ) :
    s3OrbitMapContinuousMap X '' (Set.univ : Set S3Perm) = S3Orbit X := by
  simpa [s3OrbitMapContinuousMap] using
    (S3Orbit_eq_orbitMap_image X).symm

theorem isCompact_s3OrbitMapContinuousMap_image_univ (X : H3Zorn ℝ) :
    IsCompact
      (s3OrbitMapContinuousMap X '' (Set.univ : Set S3Perm)) := by
  exact Set.finite_univ.isCompact.image
    (s3OrbitMapContinuousMap X).continuous

theorem S3OnH3Zorn_mem_orbit (σ : S3Perm) (X : H3Zorn ℝ) :
    S3OnH3Zorn σ X ∈ S3Orbit X :=
  ⟨σ, rfl⟩

theorem finite_S3Orbit (X : H3Zorn ℝ) : (S3Orbit X).Finite := by
  let s₀ : Set (H3Zorn ℝ) := {S3OnH3Zorn S3Perm.id X}
  let s₁ : Set (H3Zorn ℝ) := {S3OnH3Zorn S3Perm.s12 X}
  let s₂ : Set (H3Zorn ℝ) := {S3OnH3Zorn S3Perm.s23 X}
  let s₃ : Set (H3Zorn ℝ) := {S3OnH3Zorn S3Perm.s31 X}
  let s₄ : Set (H3Zorn ℝ) := {S3OnH3Zorn S3Perm.s12_s23 X}
  let s₅ : Set (H3Zorn ℝ) := {S3OnH3Zorn S3Perm.s23_s12 X}
  have hs : (s₀ ∪ s₁ ∪ s₂ ∪ s₃ ∪ s₄ ∪ s₅).Finite := by
    simp [s₀, s₁, s₂, s₃, s₄, s₅]
  apply hs.subset
  intro Y hY
  rcases hY with ⟨σ, rfl⟩
  rcases σ with _ | _ | _ | _ | _ | _ <;>
    simp [s₀, s₁, s₂, s₃, s₄, s₅]

theorem isCompact_S3Orbit (X : H3Zorn ℝ) : IsCompact (S3Orbit X) :=
  (finite_S3Orbit X).isCompact

theorem isClosed_S3Orbit (X : H3Zorn ℝ) : IsClosed (S3Orbit X) :=
  (finite_S3Orbit X).isClosed

theorem S3Orbit_nonempty (X : H3Zorn ℝ) : (S3Orbit X).Nonempty :=
  ⟨S3OnH3Zorn S3Perm.id X, S3OnH3Zorn_mem_orbit S3Perm.id X⟩

def S3Saturation (K : Set (H3Zorn ℝ)) : Set (H3Zorn ℝ) :=
    S3OnH3ZornHomeomorph S3Perm.id '' K ∪
    S3OnH3ZornHomeomorph S3Perm.s12 '' K ∪
    S3OnH3ZornHomeomorph S3Perm.s23 '' K ∪
    S3OnH3ZornHomeomorph S3Perm.s31 '' K ∪
    S3OnH3ZornHomeomorph S3Perm.s12_s23 '' K ∪
    S3OnH3ZornHomeomorph S3Perm.s23_s12 '' K

theorem isCompact_S3Saturation {K : Set (H3Zorn ℝ)} (hK : IsCompact K) :
    IsCompact (S3Saturation K) := by
  have h₀ := isCompact_S3OnH3Zorn_image S3Perm.id hK
  have h₁ := isCompact_S3OnH3Zorn_image S3Perm.s12 hK
  have h₂ := isCompact_S3OnH3Zorn_image S3Perm.s23 hK
  have h₃ := isCompact_S3OnH3Zorn_image S3Perm.s31 hK
  have h₄ := isCompact_S3OnH3Zorn_image S3Perm.s12_s23 hK
  have h₅ := isCompact_S3OnH3Zorn_image S3Perm.s23_s12 hK
  simpa [S3Saturation] using
    (((((h₀.union h₁).union h₂).union h₃).union h₄).union h₅)

theorem S3OnH3Zorn_image_subset_S3Saturation
    (σ : S3Perm) {K : Set (H3Zorn ℝ)} :
    S3OnH3ZornHomeomorph σ '' K ⊆ S3Saturation K := by
  unfold S3Saturation
  rcases σ with _ | _ | _ | _ | _ | _
  <;> intro Y hY
  <;> simp only [Set.mem_union]
  <;> aesop

theorem S3Orbit_subset_S3Saturation_singleton (X : H3Zorn ℝ) :
    S3Orbit X ⊆ S3Saturation {X} := by
  intro Y hY
  rcases hY with ⟨σ, rfl⟩
  apply S3OnH3Zorn_image_subset_S3Saturation σ
  exact ⟨X, by simp⟩

theorem S3OnH3ZornHomeomorph_image_S3Saturation_subset
    (σ : S3Perm) (K : Set (H3Zorn ℝ)) :
    S3OnH3ZornHomeomorph σ '' S3Saturation K ⊆ S3Saturation K := by
  have hcomp : ∀ (τ : S3Perm) (X : H3Zorn ℝ), X ∈ K →
      S3OnH3ZornHomeomorph σ
        (S3OnH3ZornHomeomorph τ X) ∈ S3Saturation K := by
    intro τ X hX
    rcases S3OnH3Zorn_group_closure τ σ with ⟨ρ, hρ⟩
    have hρmem := S3OnH3Zorn_image_subset_S3Saturation ρ (K := K)
      ⟨X, hX, rfl⟩
    change S3OnH3Zorn ρ X ∈ S3Saturation K at hρmem
    change S3OnH3Zorn σ (S3OnH3Zorn τ X) ∈ S3Saturation K
    rw [hρ] at hρmem
    simpa [Function.comp_apply] using hρmem
  intro Y hY
  rcases hY with ⟨Z, hZ, rfl⟩
  unfold S3Saturation at hZ
  rcases hZ with hpre | h₅
  · rcases hpre with hpre | h₄
    · rcases hpre with hpre | h₃
      · rcases hpre with hpre | h₂
        · rcases hpre with h₀ | h₁
          · rcases h₀ with ⟨X, hX, rfl⟩
            exact hcomp S3Perm.id X hX
          · rcases h₁ with ⟨X, hX, rfl⟩
            exact hcomp S3Perm.s12 X hX
        · rcases h₂ with ⟨X, hX, rfl⟩
          exact hcomp S3Perm.s23 X hX
      · rcases h₃ with ⟨X, hX, rfl⟩
        exact hcomp S3Perm.s31 X hX
    · rcases h₄ with ⟨X, hX, rfl⟩
      exact hcomp S3Perm.s12_s23 X hX
  · rcases h₅ with ⟨X, hX, rfl⟩
    exact hcomp S3Perm.s23_s12 X hX

theorem S3OnH3ZornHomeomorph_image_S3Saturation_eq
    (σ : S3Perm) (K : Set (H3Zorn ℝ)) :
    S3OnH3ZornHomeomorph σ '' S3Saturation K = S3Saturation K := by
  apply Set.Subset.antisymm
  · exact S3OnH3ZornHomeomorph_image_S3Saturation_subset σ K
  · intro Y hY
    have hInv := S3OnH3ZornHomeomorph_image_S3Saturation_subset
      (S3Perm.inverse σ) K
      ⟨Y, hY, rfl⟩
    refine ⟨S3OnH3ZornHomeomorph (S3Perm.inverse σ) Y, hInv, ?_⟩
    simpa only [S3OnH3ZornHomeomorph_apply] using
      S3OnH3Zorn_inverse_right σ Y

theorem isClosed_S3Saturation_normCubic_level (r : ℝ) :
    IsClosed
      (S3Saturation {X : H3Zorn ℝ | H3Zorn.normCubic X = r}) := by
  let K : Set (H3Zorn ℝ) := {X : H3Zorn ℝ | H3Zorn.normCubic X = r}
  have h₀ := isClosed_S3OnH3Zorn_normCubic_level_image S3Perm.id r
  have h₁ := isClosed_S3OnH3Zorn_normCubic_level_image S3Perm.s12 r
  have h₂ := isClosed_S3OnH3Zorn_normCubic_level_image S3Perm.s23 r
  have h₃ := isClosed_S3OnH3Zorn_normCubic_level_image S3Perm.s31 r
  have h₄ := isClosed_S3OnH3Zorn_normCubic_level_image S3Perm.s12_s23 r
  have h₅ := isClosed_S3OnH3Zorn_normCubic_level_image S3Perm.s23_s12 r
  simpa [S3Saturation, K] using
    (((((h₀.union h₁).union h₂).union h₃).union h₄).union h₅)

theorem S3OnH3ZornHomeomorph_normCubic_level_saturation_eq
    (σ : S3Perm) (r : ℝ) :
    S3OnH3ZornHomeomorph σ ''
        S3Saturation {X : H3Zorn ℝ | H3Zorn.normCubic X = r} =
      S3Saturation {X : H3Zorn ℝ | H3Zorn.normCubic X = r} :=
  S3OnH3ZornHomeomorph_image_S3Saturation_eq σ
    {X : H3Zorn ℝ | H3Zorn.normCubic X = r}

theorem isClosed_S3Saturation {K : Set (H3Zorn ℝ)} (hK : IsClosed K) :
    IsClosed (S3Saturation K) := by
  have h₀ := isClosed_S3OnH3Zorn_image S3Perm.id hK
  have h₁ := isClosed_S3OnH3Zorn_image S3Perm.s12 hK
  have h₂ := isClosed_S3OnH3Zorn_image S3Perm.s23 hK
  have h₃ := isClosed_S3OnH3Zorn_image S3Perm.s31 hK
  have h₄ := isClosed_S3OnH3Zorn_image S3Perm.s12_s23 hK
  have h₅ := isClosed_S3OnH3Zorn_image S3Perm.s23_s12 hK
  simpa [S3Saturation] using
    (((((h₀.union h₁).union h₂).union h₃).union h₄).union h₅)

theorem isOpen_S3Saturation {U : Set (H3Zorn ℝ)} (hU : IsOpen U) :
    IsOpen (S3Saturation U) := by
  have h₀ := isOpen_S3OnH3Zorn_image S3Perm.id hU
  have h₁ := isOpen_S3OnH3Zorn_image S3Perm.s12 hU
  have h₂ := isOpen_S3OnH3Zorn_image S3Perm.s23 hU
  have h₃ := isOpen_S3OnH3Zorn_image S3Perm.s31 hU
  have h₄ := isOpen_S3OnH3Zorn_image S3Perm.s12_s23 hU
  have h₅ := isOpen_S3OnH3Zorn_image S3Perm.s23_s12 hU
  simpa [S3Saturation] using
    (((((h₀.union h₁).union h₂).union h₃).union h₄).union h₅)

theorem subset_S3Saturation (K : Set (H3Zorn ℝ)) :
    K ⊆ S3Saturation K := by
  intro X hX
  unfold S3Saturation
  simp only [Set.mem_union]
  have hId : S3OnH3Zorn S3Perm.id X = X := by
    change S3OnH3Zorn S3Perm.id X = X
    rfl
  aesop

theorem S3Saturation_mono {K L : Set (H3Zorn ℝ)} (hKL : K ⊆ L) :
    S3Saturation K ⊆ S3Saturation L := by
  unfold S3Saturation
  have h₀ :
      S3OnH3ZornHomeomorph S3Perm.id '' K ⊆
        S3OnH3ZornHomeomorph S3Perm.id '' L :=
    Set.image_mono hKL
  have h₁ :
      S3OnH3ZornHomeomorph S3Perm.s12 '' K ⊆
        S3OnH3ZornHomeomorph S3Perm.s12 '' L :=
    Set.image_mono hKL
  have h₂ :
      S3OnH3ZornHomeomorph S3Perm.s23 '' K ⊆
        S3OnH3ZornHomeomorph S3Perm.s23 '' L :=
    Set.image_mono hKL
  have h₃ :
      S3OnH3ZornHomeomorph S3Perm.s31 '' K ⊆
        S3OnH3ZornHomeomorph S3Perm.s31 '' L :=
    Set.image_mono hKL
  have h₄ :
      S3OnH3ZornHomeomorph S3Perm.s12_s23 '' K ⊆
        S3OnH3ZornHomeomorph S3Perm.s12_s23 '' L :=
    Set.image_mono hKL
  have h₅ :
      S3OnH3ZornHomeomorph S3Perm.s23_s12 '' K ⊆
        S3OnH3ZornHomeomorph S3Perm.s23_s12 '' L :=
    Set.image_mono hKL
  exact Set.union_subset_union
    (Set.union_subset_union
      (Set.union_subset_union
        (Set.union_subset_union
          (Set.union_subset_union h₀ h₁) h₂) h₃) h₄) h₅

theorem S3Saturation_empty : S3Saturation (∅ : Set (H3Zorn ℝ)) = ∅ := by
  simp [S3Saturation]

theorem S3Saturation_union (K L : Set (H3Zorn ℝ)) :
    S3Saturation (K ∪ L) = S3Saturation K ∪ S3Saturation L := by
  simp only [S3Saturation, Set.image_union]
  ac_rfl

theorem S3Saturation_idem (K : Set (H3Zorn ℝ)) :
    S3Saturation (S3Saturation K) = S3Saturation K := by
  apply Set.Subset.antisymm
  · have h₀ := S3OnH3ZornHomeomorph_image_S3Saturation_subset
      S3Perm.id K
    have h₁ := S3OnH3ZornHomeomorph_image_S3Saturation_subset
      S3Perm.s12 K
    have h₂ := S3OnH3ZornHomeomorph_image_S3Saturation_subset
      S3Perm.s23 K
    have h₃ := S3OnH3ZornHomeomorph_image_S3Saturation_subset
      S3Perm.s31 K
    have h₄ := S3OnH3ZornHomeomorph_image_S3Saturation_subset
      S3Perm.s12_s23 K
    have h₅ := S3OnH3ZornHomeomorph_image_S3Saturation_subset
      S3Perm.s23_s12 K
    simpa [S3Saturation] using Set.union_subset_union
      (Set.union_subset_union
        (Set.union_subset_union
          (Set.union_subset_union
            (Set.union_subset_union h₀ h₁) h₂) h₃) h₄) h₅
  · exact S3Saturation_mono (subset_S3Saturation K)

theorem S3Saturation_singleton_eq_orbit (X : H3Zorn ℝ) :
    S3Saturation {X} = S3Orbit X := by
  apply Set.Subset.antisymm
  · intro Y hY
    unfold S3Saturation at hY
    rcases hY with hpre | h₅
    · rcases hpre with hpre | h₄
      · rcases hpre with hpre | h₃
        · rcases hpre with hpre | h₂
          · rcases hpre with h₀ | h₁
            · rcases h₀ with ⟨Z, hZ, rfl⟩
              have hZX : Z = X := Set.mem_singleton_iff.mp hZ
              subst Z
              simpa only [S3OnH3ZornHomeomorph_apply] using
                S3OnH3Zorn_mem_orbit S3Perm.id X
            · rcases h₁ with ⟨Z, hZ, rfl⟩
              have hZX : Z = X := Set.mem_singleton_iff.mp hZ
              subst Z
              simpa only [S3OnH3ZornHomeomorph_apply] using
                S3OnH3Zorn_mem_orbit S3Perm.s12 X
          · rcases h₂ with ⟨Z, hZ, rfl⟩
            have hZX : Z = X := Set.mem_singleton_iff.mp hZ
            subst Z
            simpa only [S3OnH3ZornHomeomorph_apply] using
              S3OnH3Zorn_mem_orbit S3Perm.s23 X
        · rcases h₃ with ⟨Z, hZ, rfl⟩
          have hZX : Z = X := Set.mem_singleton_iff.mp hZ
          subst Z
          simpa only [S3OnH3ZornHomeomorph_apply] using
            S3OnH3Zorn_mem_orbit S3Perm.s31 X
      · rcases h₄ with ⟨Z, hZ, rfl⟩
        have hZX : Z = X := Set.mem_singleton_iff.mp hZ
        subst Z
        simpa only [S3OnH3ZornHomeomorph_apply] using
          S3OnH3Zorn_mem_orbit S3Perm.s12_s23 X
    · rcases h₅ with ⟨Z, hZ, rfl⟩
      have hZX : Z = X := Set.mem_singleton_iff.mp hZ
      subst Z
      simpa only [S3OnH3ZornHomeomorph_apply] using
        S3OnH3Zorn_mem_orbit S3Perm.s23_s12 X
  · exact S3Orbit_subset_S3Saturation_singleton X

theorem isCompact_S3Saturation_singleton (X : H3Zorn ℝ) :
    IsCompact (S3Saturation {X}) := by
  rw [S3Saturation_singleton_eq_orbit]
  exact isCompact_S3Orbit X

theorem isClosed_S3Saturation_singleton (X : H3Zorn ℝ) :
    IsClosed (S3Saturation {X}) := by
  rw [S3Saturation_singleton_eq_orbit]
  exact isClosed_S3Orbit X

theorem S3Saturation_singleton_nonempty (X : H3Zorn ℝ) :
    (S3Saturation {X}).Nonempty := by
  rw [S3Saturation_singleton_eq_orbit]
  exact S3Orbit_nonempty X

theorem S3OnH3ZornHomeomorph_image_orbit_eq
    (σ : S3Perm) (X : H3Zorn ℝ) :
    S3OnH3ZornHomeomorph σ '' S3Orbit X = S3Orbit X := by
  rw [← S3Saturation_singleton_eq_orbit X]
  exact S3OnH3ZornHomeomorph_image_S3Saturation_eq σ {X}

theorem S3OnH3ZornHomeomorph_preimage_orbit_eq
    (σ : S3Perm) (X : H3Zorn ℝ) :
    (S3OnH3ZornHomeomorph σ) ⁻¹' S3Orbit X = S3Orbit X := by
  apply Set.Subset.antisymm
  · intro Y hY
    change S3OnH3ZornHomeomorph σ Y ∈ S3Orbit X at hY
    have hImage :
        S3OnH3ZornHomeomorph σ '' S3Orbit X = S3Orbit X :=
      S3OnH3ZornHomeomorph_image_orbit_eq σ X
    have hY' :
        S3OnH3ZornHomeomorph σ Y ∈
          S3OnH3ZornHomeomorph σ '' S3Orbit X := by
      rw [hImage]
      exact hY
    rcases hY' with ⟨Z, hZ, hZY⟩
    have hZY' : Z = Y :=
      (S3OnH3ZornHomeomorph σ).injective hZY
    simpa [hZY'] using hZ
  · intro Y hY
    change S3OnH3ZornHomeomorph σ Y ∈ S3Orbit X
    rw [← S3OnH3ZornHomeomorph_image_orbit_eq σ X]
    exact ⟨Y, hY, rfl⟩

theorem isCompact_S3OnH3ZornHomeomorph_preimage_orbit
    (σ : S3Perm) (X : H3Zorn ℝ) :
    IsCompact ((S3OnH3ZornHomeomorph σ) ⁻¹' S3Orbit X) := by
  rw [S3OnH3ZornHomeomorph_preimage_orbit_eq σ X]
  exact isCompact_S3Orbit X

theorem isClosed_S3OnH3ZornHomeomorph_preimage_orbit
    (σ : S3Perm) (X : H3Zorn ℝ) :
    IsClosed ((S3OnH3ZornHomeomorph σ) ⁻¹' S3Orbit X) := by
  rw [S3OnH3ZornHomeomorph_preimage_orbit_eq σ X]
  exact isClosed_S3Orbit X

def h3ZornNormCubicContinuousMap :
    ContinuousMap (H3Zorn ℝ) ℝ :=
  ContinuousMap.mk H3Zorn.normCubic continuous_h3Zorn_normCubic

def h3ZornAdjointQuadContinuousMap :
    ContinuousMap (H3Zorn ℝ) (H3Zorn ℝ) :=
  ContinuousMap.mk H3Zorn.adjointQuad continuous_h3Zorn_adjointQuad

def h3ZornJordanMulContinuousMap :
    ContinuousMap (H3Zorn ℝ × H3Zorn ℝ) (H3Zorn ℝ) :=
  ContinuousMap.mk
    (fun p : H3Zorn ℝ × H3Zorn ℝ => p.1 * p.2)
    continuous_h3Zorn_jordanMul

def s3OnH3ZornContinuousMap (σ : S3Perm) :
    ContinuousMap (H3Zorn ℝ) (H3Zorn ℝ) :=
  ContinuousMap.mk (S3OnH3Zorn σ) (continuous_S3OnH3Zorn σ)

def h3ZornTraceBilinContinuousMap :
    ContinuousMap (H3Zorn ℝ × H3Zorn ℝ) ℝ :=
  ContinuousMap.mk
    (fun p : H3Zorn ℝ × H3Zorn ℝ => H3Zorn.traceBilin p.1 p.2)
    continuous_h3Zorn_traceBilin

def h3ZornCrossProductContinuousMap :
    ContinuousMap (H3Zorn ℝ × H3Zorn ℝ) (H3Zorn ℝ) :=
  ContinuousMap.mk
    (fun p : H3Zorn ℝ × H3Zorn ℝ => H3Zorn.crossProduct p.1 p.2)
    continuous_h3Zorn_crossProduct

def h3ZornUContinuousMap :
    ContinuousMap (H3Zorn ℝ × H3Zorn ℝ) (H3Zorn ℝ) :=
  ContinuousMap.mk
    (fun p : H3Zorn ℝ × H3Zorn ℝ => H3Zorn.U p.1 p.2)
    continuous_h3Zorn_U

def h3ZornTContinuousMap :
    ContinuousMap ((H3Zorn ℝ × H3Zorn ℝ) × H3Zorn ℝ) (H3Zorn ℝ) :=
  ContinuousMap.mk
    (fun p : (H3Zorn ℝ × H3Zorn ℝ) × H3Zorn ℝ =>
      H3Zorn.T p.1.1 p.1.2 p.2)
    continuous_h3Zorn_T

def normCubicAfterS3ContinuousMap (σ : S3Perm) :
    ContinuousMap (H3Zorn ℝ) ℝ :=
  h3ZornNormCubicContinuousMap.comp (s3OnH3ZornContinuousMap σ)

@[simp] theorem normCubicAfterS3ContinuousMap_apply
    (σ : S3Perm) (X : H3Zorn ℝ) :
    normCubicAfterS3ContinuousMap σ X =
      H3Zorn.normCubic (S3OnH3Zorn σ X) := by
  rfl

end InfoGeometry.Algebra
