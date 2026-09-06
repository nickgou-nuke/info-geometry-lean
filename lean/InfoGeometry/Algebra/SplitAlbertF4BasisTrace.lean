import InfoGeometry.Algebra.BaezF4H3Zorn
import InfoGeometry.Algebra.RealAlbertH3ZornCarrierAlignment
import InfoGeometry.Algebra.SplitAlbertInnerTraceSpan
import InfoGeometry.Canonical.QutritGellMannBasis

/-!
# Trace-zero readout for the explicit split-Albert `F₄` basis

This owner records the pointwise trace statement for the explicit basis
provided by `BaezF4H3Zorn`.  It deliberately does not identify the span of
that basis with all of `H3ZornF4Derivations`; that generation theorem remains
a separate obligation.
-/

namespace InfoGeometry.Algebra

open H3Zorn

def f4BasisSpan : Submodule ℝ (Module.End ℝ (H3Zorn ℝ)) :=
  Submodule.span ℝ
    (Set.range (fun i : Fin 52 => (f4Basis i).1))

theorem f4Basis_linearTrace_zero (i : Fin 52) (x : H3Zorn ℝ) :
    linearTrace ((f4Basis i).1 x) = 0 := by
  fin_cases i <;>
    change linearTrace
      ((h3ZornJordanInnerDerivation _ _ : Module.End ℝ (H3Zorn ℝ)) x) = 0 <;>
    exact h3ZornJordanInnerDerivation_linearTrace_zero _ _ x

theorem f4BasisSpan_le_traceZero :
    f4BasisSpan ≤ h3ZornTraceZeroEndomorphisms := by
  intro D hD
  refine Submodule.span_induction
    (p := fun T _ => T ∈ h3ZornTraceZeroEndomorphisms)
    ?_ ?_ ?_ ?_ hD
  · rintro T ⟨i, rfl⟩
    exact f4Basis_linearTrace_zero i
  · exact h3ZornTraceZeroEndomorphisms.zero_mem
  · intro T U _ _ hT hU
    exact h3ZornTraceZeroEndomorphisms.add_mem hT hU
  · intro r T _ hT
    exact h3ZornTraceZeroEndomorphisms.smul_mem r hT

theorem f4BasisSpan_le_F4Derivations :
    f4BasisSpan ≤ H3ZornF4Derivations := by
  intro D hD
  refine Submodule.span_induction
    (p := fun T _ => T ∈ H3ZornF4Derivations)
    ?_ ?_ ?_ ?_ hD
  · rintro T ⟨i, rfl⟩
    exact (f4Basis i).property
  · exact H3ZornF4Derivations.zero_mem
  · intro T U _ _ hT hU
    exact H3ZornF4Derivations.add_mem hT hU
  · intro r T _ hT
    exact H3ZornF4Derivations.smul_mem r hT

theorem f4BasisSpan_le_h3ZornInnerDerivationSpan :
    f4BasisSpan ≤ h3ZornInnerDerivationSpan := by
  intro D hD
  refine Submodule.span_induction
    (p := fun T _ => T ∈ h3ZornInnerDerivationSpan)
    ?_ ?_ ?_ ?_ hD
  · rintro T ⟨i, rfl⟩
    fin_cases i <;>
      exact Submodule.subset_span ⟨_, _, rfl⟩
  · exact h3ZornInnerDerivationSpan.zero_mem
  · intro T U _ _ hT hU
    exact h3ZornInnerDerivationSpan.add_mem hT hU
  · intro r T _ hT
    exact h3ZornInnerDerivationSpan.smul_mem r hT

/-! A finite separating-coordinate certificate is sufficient for linear
independence.  This is the reusable assembly lemma for the explicit F₄
readback table; it contains no dimension or generation assumption. -/
theorem linearIndependent_of_separating_coordinate
    {ι V : Type*} [Fintype ι] [AddCommGroup V] [Module ℝ V]
    (f : ι → V) (coord : ι → V →ₗ[ℝ] ℝ)
    (hdiag : ∀ i, coord i (f i) ≠ 0)
    (hoff : ∀ i j, i ≠ j → coord i (f j) = 0) :
    LinearIndependent ℝ f := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have hcoord := congrArg (coord i) hg
  simp only [map_sum, map_smul] at hcoord
  rw [Finset.sum_eq_single i] at hcoord
  rw [(coord i).map_zero] at hcoord
  simp only [smul_eq_mul] at hcoord
  rw [mul_eq_zero] at hcoord
  · rcases hcoord with hcoord | hcoord
    · exact hcoord
    · exact absurd hcoord (hdiag i)
  · intro j _ hj
    rw [hoff i j (Ne.symm hj), smul_zero]
  · simp

theorem f4Basis_zero_apply (x : H3Zorn ℝ) :
    ((f4Basis 0).1 : Module.End ℝ (H3Zorn ℝ)) x =
      ((h3ZornJordanInnerDerivation h3_diag₁ (h3_off₁₂ 0) :
        Module.End ℝ (H3Zorn ℝ)) x) := by
  rfl

theorem zorn_basis_a_readback (g : Fin 8 → ℝ)
    (hg : ∑ i, g i • zorn_basis i = 0) :
    g 0 = 0 := by
  have h := congrArg (fun X : ZornVectorMatrix ℝ => X.a) hg
  simpa [zorn_basis, ZornVectorMatrix.smul, ZornVectorMatrix.add,
    ZornVectorMatrix.zero, Fin.sum_univ_succ] using h

theorem zorn_basis_v0_readback (g : Fin 8 → ℝ)
    (hg : ∑ i, g i • zorn_basis i = 0) :
    g 1 = 0 := by
  have h := congrArg (fun X : ZornVectorMatrix ℝ => X.v 0) hg
  simpa [zorn_basis, ZornVectorMatrix.smul, ZornVectorMatrix.add,
    ZornVectorMatrix.zero, Fin.sum_univ_succ] using h

theorem zorn_basis_v1_readback (g : Fin 8 → ℝ)
    (hg : ∑ i, g i • zorn_basis i = 0) :
    g 2 = 0 := by
  have h := congrArg (fun X : ZornVectorMatrix ℝ => X.v 1) hg
  simpa [zorn_basis, ZornVectorMatrix.smul, ZornVectorMatrix.add,
    ZornVectorMatrix.zero, Fin.sum_univ_succ] using h

theorem zorn_basis_v2_readback (g : Fin 8 → ℝ)
    (hg : ∑ i, g i • zorn_basis i = 0) :
    g 3 = 0 := by
  have h := congrArg (fun X : ZornVectorMatrix ℝ => X.v 2) hg
  simpa [zorn_basis, ZornVectorMatrix.smul, ZornVectorMatrix.add,
    ZornVectorMatrix.zero, Fin.sum_univ_succ] using h

theorem zorn_basis_w0_readback (g : Fin 8 → ℝ)
    (hg : ∑ i, g i • zorn_basis i = 0) :
    g 4 = 0 := by
  have h := congrArg (fun X : ZornVectorMatrix ℝ => X.w 0) hg
  simpa [zorn_basis, ZornVectorMatrix.smul, ZornVectorMatrix.add,
    ZornVectorMatrix.zero, Fin.sum_univ_succ] using h

theorem zorn_basis_w1_readback (g : Fin 8 → ℝ)
    (hg : ∑ i, g i • zorn_basis i = 0) :
    g 5 = 0 := by
  have h := congrArg (fun X : ZornVectorMatrix ℝ => X.w 1) hg
  simpa [zorn_basis, ZornVectorMatrix.smul, ZornVectorMatrix.add,
    ZornVectorMatrix.zero, Fin.sum_univ_succ] using h

theorem zorn_basis_w2_readback (g : Fin 8 → ℝ)
    (hg : ∑ i, g i • zorn_basis i = 0) :
    g 6 = 0 := by
  have h := congrArg (fun X : ZornVectorMatrix ℝ => X.w 2) hg
  simpa [zorn_basis, ZornVectorMatrix.smul, ZornVectorMatrix.add,
    ZornVectorMatrix.zero, Fin.sum_univ_succ] using h

theorem zorn_basis_b_readback (g : Fin 8 → ℝ)
    (hg : ∑ i, g i • zorn_basis i = 0) :
    g 7 = 0 := by
  have h := congrArg (fun X : ZornVectorMatrix ℝ => X.b) hg
  simpa [zorn_basis, ZornVectorMatrix.smul, ZornVectorMatrix.add,
    ZornVectorMatrix.zero, Fin.sum_univ_succ] using h

theorem zorn_basis_linearIndependent :
    LinearIndependent ℝ (fun i : Fin 8 => zorn_basis i) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  fin_cases i
  · exact zorn_basis_a_readback g hg
  · exact zorn_basis_v0_readback g hg
  · exact zorn_basis_v1_readback g hg
  · exact zorn_basis_v2_readback g hg
  · exact zorn_basis_w0_readback g hg
  · exact zorn_basis_w1_readback g hg
  · exact zorn_basis_w2_readback g hg
  · exact zorn_basis_b_readback g hg

theorem zorn_basis_decomposition (X : ZornVectorMatrix ℝ) :
    (∑ i : Fin 8, (match i with
      | 0 => X.a
      | 1 => X.v 0
      | 2 => X.v 1
      | 3 => X.v 2
      | 4 => X.w 0
      | 5 => X.w 1
      | 6 => X.w 2
      | 7 => X.b) • zorn_basis i) = X := by
  apply ZornVectorMatrix.ext
  · simp [zorn_basis, ZornVectorMatrix.smul, ZornVectorMatrix.add,
      Fin.sum_univ_succ]
  · funext i
    fin_cases i <;>
      simp [zorn_basis, ZornVectorMatrix.smul, ZornVectorMatrix.add,
        Fin.sum_univ_succ]
  · funext i
    fin_cases i <;>
      simp [zorn_basis, ZornVectorMatrix.smul, ZornVectorMatrix.add,
        Fin.sum_univ_succ]
  · simp [zorn_basis, ZornVectorMatrix.smul, ZornVectorMatrix.add,
      Fin.sum_univ_succ]

theorem zorn_basis_span_eq_top :
    Submodule.span ℝ (Set.range (fun i : Fin 8 => zorn_basis i)) = ⊤ := by
  apply top_unique
  intro X _
  rw [← zorn_basis_decomposition X]
  apply Submodule.sum_mem
  intro i hi
  apply Submodule.smul_mem
  exact Submodule.subset_span ⟨i, rfl⟩

noncomputable def zornCoordinateBasis :
    Module.Basis (Fin 8) ℝ (ZornVectorMatrix ℝ) :=
  Module.Basis.mk zorn_basis_linearIndependent (by
    intro X _
    rw [← zorn_basis_decomposition X]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))

@[simp] theorem zornCoordinateBasis_apply (i : Fin 8) :
    zornCoordinateBasis i = zorn_basis i := by
  exact Module.Basis.mk_apply _ _ _

noncomputable def gellMannCoordinateBasis :
    Module.Basis (Fin 8) ℝ InfoGeometry.Quantum.Qutrit.tracelessHermitian :=
  Module.Basis.mk InfoGeometry.Quantum.Qutrit.gellMann_linearIndependent (by
    intro X _
    rw [← InfoGeometry.Quantum.Qutrit.gellMann_traceless_expansion X]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _
        (Submodule.subset_span ⟨i, rfl⟩))

@[simp] theorem gellMannCoordinateBasis_apply (i : Fin 8) :
    gellMannCoordinateBasis i = InfoGeometry.Quantum.Qutrit.gellMann i := by
  exact Module.Basis.mk_apply _ _ _

noncomputable def tracelessHermitianZornSoldering :
    InfoGeometry.Quantum.Qutrit.tracelessHermitian ≃ₗ[ℝ]
      ZornVectorMatrix ℝ :=
  gellMannCoordinateBasis.equiv zornCoordinateBasis (Equiv.refl (Fin 8))

@[simp] theorem tracelessHermitianZornSoldering_gellMann (i : Fin 8) :
    tracelessHermitianZornSoldering
      (gellMannCoordinateBasis i) = zornCoordinateBasis i := by
  exact Module.Basis.equiv_apply
    gellMannCoordinateBasis i zornCoordinateBasis (Equiv.refl (Fin 8))

@[simp] theorem tracelessHermitianZornSoldering_symm_zorn (i : Fin 8) :
    tracelessHermitianZornSoldering.symm (zornCoordinateBasis i) =
      gellMannCoordinateBasis i := by
  have h := congrArg tracelessHermitianZornSoldering.symm
    (tracelessHermitianZornSoldering_gellMann i)
  simpa using h.symm

theorem tracelessHermitianZornSoldering_symm_apply (X : ZornVectorMatrix ℝ) :
    tracelessHermitianZornSoldering.symm X =
      ∑ i, (zornCoordinateBasis.repr X) i • gellMannCoordinateBasis i := by
  have h := congrArg tracelessHermitianZornSoldering.symm
    (zornCoordinateBasis.sum_repr X)
  rw [map_sum] at h
  simp only [map_smul, tracelessHermitianZornSoldering_symm_zorn] at h
  simpa using h.symm

@[simp] theorem tracelessHermitianZornSoldering_symm_apply_apply
    (X : InfoGeometry.Quantum.Qutrit.tracelessHermitian) :
    tracelessHermitianZornSoldering.symm
        (tracelessHermitianZornSoldering X) = X := by
  exact tracelessHermitianZornSoldering.symm_apply_apply X

@[simp] theorem tracelessHermitianZornSoldering_apply_symm_apply
    (X : ZornVectorMatrix ℝ) :
    tracelessHermitianZornSoldering
        (tracelessHermitianZornSoldering.symm X) = X := by
  exact tracelessHermitianZornSoldering.apply_symm_apply X

noncomputable def peirceHalfAEmbedding
    (X : InfoGeometry.Quantum.Qutrit.tracelessHermitian) : H3Zorn ℝ :=
  { α₁ := 0
    α₂ := 0
    α₃ := 0
    a := tracelessHermitianZornSoldering X
    b := ZornVectorMatrix.zero
    c := ZornVectorMatrix.zero }

@[simp] theorem peirceHalfAEmbedding_a
    (X : InfoGeometry.Quantum.Qutrit.tracelessHermitian) :
    (peirceHalfAEmbedding X).a = tracelessHermitianZornSoldering X := rfl

@[simp] theorem peirceHalfAEmbedding_b
    (X : InfoGeometry.Quantum.Qutrit.tracelessHermitian) :
    (peirceHalfAEmbedding X).b = ZornVectorMatrix.zero := rfl

@[simp] theorem peirceHalfAEmbedding_c
    (X : InfoGeometry.Quantum.Qutrit.tracelessHermitian) :
    (peirceHalfAEmbedding X).c = ZornVectorMatrix.zero := rfl

theorem peirceHalfAEmbedding_injective :
    Function.Injective peirceHalfAEmbedding := by
  intro X Y hXY
  apply tracelessHermitianZornSoldering.injective
  exact congrArg H3Zorn.a hXY


noncomputable def peirceHalfBEmbedding
    (X : InfoGeometry.Quantum.Qutrit.tracelessHermitian) : H3Zorn ℝ :=
  { α₁ := 0
    α₂ := 0
    α₃ := 0
    a := ZornVectorMatrix.zero
    b := tracelessHermitianZornSoldering X
    c := ZornVectorMatrix.zero }

@[simp] theorem peirceHalfBEmbedding_b
    (X : InfoGeometry.Quantum.Qutrit.tracelessHermitian) :
    (peirceHalfBEmbedding X).b = tracelessHermitianZornSoldering X := rfl

@[simp] theorem peirceHalfBEmbedding_a
    (X : InfoGeometry.Quantum.Qutrit.tracelessHermitian) :
    (peirceHalfBEmbedding X).a = ZornVectorMatrix.zero := rfl

@[simp] theorem peirceHalfBEmbedding_c
    (X : InfoGeometry.Quantum.Qutrit.tracelessHermitian) :
    (peirceHalfBEmbedding X).c = ZornVectorMatrix.zero := rfl

theorem peirceHalfBEmbedding_injective :
    Function.Injective peirceHalfBEmbedding := by
  intro X Y hXY
  apply tracelessHermitianZornSoldering.injective
  exact congrArg H3Zorn.b hXY

noncomputable def peirceHalfCEmbedding
    (X : InfoGeometry.Quantum.Qutrit.tracelessHermitian) : H3Zorn ℝ :=
  { α₁ := 0
    α₂ := 0
    α₃ := 0
    a := ZornVectorMatrix.zero
    b := ZornVectorMatrix.zero
    c := tracelessHermitianZornSoldering X }

@[simp] theorem peirceHalfCEmbedding_c
    (X : InfoGeometry.Quantum.Qutrit.tracelessHermitian) :
    (peirceHalfCEmbedding X).c = tracelessHermitianZornSoldering X := rfl

@[simp] theorem peirceHalfCEmbedding_a
    (X : InfoGeometry.Quantum.Qutrit.tracelessHermitian) :
    (peirceHalfCEmbedding X).a = ZornVectorMatrix.zero := rfl

@[simp] theorem peirceHalfCEmbedding_b
    (X : InfoGeometry.Quantum.Qutrit.tracelessHermitian) :
    (peirceHalfCEmbedding X).b = ZornVectorMatrix.zero := rfl

theorem peirceHalfCEmbedding_injective :
    Function.Injective peirceHalfCEmbedding := by
  intro X Y hXY
  apply tracelessHermitianZornSoldering.injective
  exact congrArg H3Zorn.c hXY

@[simp] theorem zornVectorMatrix_add_a (X Y : ZornVectorMatrix ℝ) :
    (X + Y).a = X.a + Y.a := rfl

@[simp] theorem zornVectorMatrix_add_v (X Y : ZornVectorMatrix ℝ) :
    (X + Y).v = X.v + Y.v := rfl

@[simp] theorem zornVectorMatrix_add_w (X Y : ZornVectorMatrix ℝ) :
    (X + Y).w = X.w + Y.w := rfl

@[simp] theorem zornVectorMatrix_add_b (X Y : ZornVectorMatrix ℝ) :
    (X + Y).b = X.b + Y.b := rfl

@[simp] theorem h3Zorn_add_α₁ (X Y : H3Zorn ℝ) :
    (X + Y).α₁ = X.α₁ + Y.α₁ := rfl

@[simp] theorem h3Zorn_add_α₂ (X Y : H3Zorn ℝ) :
    (X + Y).α₂ = X.α₂ + Y.α₂ := rfl

@[simp] theorem h3Zorn_add_α₃ (X Y : H3Zorn ℝ) :
    (X + Y).α₃ = X.α₃ + Y.α₃ := rfl

@[simp] theorem h3Zorn_add_a (X Y : H3Zorn ℝ) :
    (X + Y).a = X.a + Y.a := rfl

@[simp] theorem h3Zorn_add_b (X Y : H3Zorn ℝ) :
    (X + Y).b = X.b + Y.b := rfl

@[simp] theorem h3Zorn_add_c (X Y : H3Zorn ℝ) :
    (X + Y).c = X.c + Y.c := rfl

theorem peirceHalfEmbedding_offDiagonal_readback
    (X Y Z : InfoGeometry.Quantum.Qutrit.tracelessHermitian) :
    (peirceHalfAEmbedding X + peirceHalfBEmbedding Y +
      peirceHalfCEmbedding Z).a = tracelessHermitianZornSoldering X ∧
    (peirceHalfAEmbedding X + peirceHalfBEmbedding Y +
      peirceHalfCEmbedding Z).b = tracelessHermitianZornSoldering Y ∧
    (peirceHalfAEmbedding X + peirceHalfBEmbedding Y +
      peirceHalfCEmbedding Z).c = tracelessHermitianZornSoldering Z := by
  constructor
  · rw [h3Zorn_add_a, h3Zorn_add_a, peirceHalfAEmbedding_a,
      peirceHalfBEmbedding_a, peirceHalfCEmbedding_a]
    simp [ZornVectorMatrix.add_zero]
  constructor
  · rw [h3Zorn_add_b, h3Zorn_add_b, peirceHalfAEmbedding_b,
      peirceHalfBEmbedding_b, peirceHalfCEmbedding_b]
    simp [ZornVectorMatrix.add_zero, ZornVectorMatrix.zero_add]
  · rw [h3Zorn_add_c, h3Zorn_add_c, peirceHalfAEmbedding_c,
      peirceHalfBEmbedding_c, peirceHalfCEmbedding_c]
    simp [ZornVectorMatrix.zero_add]

theorem peirceHalfEmbedding_unique
    (X Y Z X' Y' Z' : InfoGeometry.Quantum.Qutrit.tracelessHermitian)
    (h : peirceHalfAEmbedding X + peirceHalfBEmbedding Y +
      peirceHalfCEmbedding Z =
      peirceHalfAEmbedding X' + peirceHalfBEmbedding Y' +
      peirceHalfCEmbedding Z') :
    X = X' ∧ Y = Y' ∧ Z = Z' := by
  have ha := congrArg H3Zorn.a h
  have hb := congrArg H3Zorn.b h
  have hc := congrArg H3Zorn.c h
  have ha' : tracelessHermitianZornSoldering X =
      tracelessHermitianZornSoldering X' := by
    exact (peirceHalfEmbedding_offDiagonal_readback X Y Z).1.symm.trans
      (ha.trans (peirceHalfEmbedding_offDiagonal_readback X' Y' Z').1)
  have hb' : tracelessHermitianZornSoldering Y =
      tracelessHermitianZornSoldering Y' := by
    exact (peirceHalfEmbedding_offDiagonal_readback X Y Z).2.1.symm.trans
      (hb.trans (peirceHalfEmbedding_offDiagonal_readback X' Y' Z').2.1)
  have hc' : tracelessHermitianZornSoldering Z =
      tracelessHermitianZornSoldering Z' := by
    exact (peirceHalfEmbedding_offDiagonal_readback X Y Z).2.2.symm.trans
      (hc.trans (peirceHalfEmbedding_offDiagonal_readback X' Y' Z').2.2)
  exact ⟨tracelessHermitianZornSoldering.injective ha',
    tracelessHermitianZornSoldering.injective hb',
    tracelessHermitianZornSoldering.injective hc'⟩

noncomputable def peirceHalfEmbeddingSum :
    (InfoGeometry.Quantum.Qutrit.tracelessHermitian ×
      InfoGeometry.Quantum.Qutrit.tracelessHermitian ×
      InfoGeometry.Quantum.Qutrit.tracelessHermitian) → H3Zorn ℝ
  | (X, Y, Z) => peirceHalfAEmbedding X + peirceHalfBEmbedding Y +
      peirceHalfCEmbedding Z

theorem peirceHalfEmbeddingSum_injective :
    Function.Injective peirceHalfEmbeddingSum := by
  intro p q h
  rcases p with ⟨X, Y, Z⟩
  rcases q with ⟨X', Y', Z'⟩
  rcases peirceHalfEmbedding_unique X Y Z X' Y' Z' h with ⟨hX, hY, hZ⟩
  exact Prod.ext hX (Prod.ext hY hZ)

@[simp] theorem peirceHalfEmbeddingSum_apply
    (X Y Z : InfoGeometry.Quantum.Qutrit.tracelessHermitian) :
    peirceHalfEmbeddingSum (X, Y, Z) =
      peirceHalfAEmbedding X + peirceHalfBEmbedding Y +
        peirceHalfCEmbedding Z := rfl

theorem peirceHalfEmbeddingSum_surjective_offDiagonal
    (T : H3Zorn ℝ)
    (h₁ : T.α₁ = 0) (h₂ : T.α₂ = 0) (h₃ : T.α₃ = 0) :
    ∃ p, peirceHalfEmbeddingSum p = T := by
  let X := tracelessHermitianZornSoldering.symm T.a
  let Y := tracelessHermitianZornSoldering.symm T.b
  let Z := tracelessHermitianZornSoldering.symm T.c
  refine ⟨(X, Y, Z), ?_⟩
  apply H3Zorn.ext_h3
  · simp [peirceHalfEmbeddingSum, H3Zorn.instAdd, peirceHalfAEmbedding,
      peirceHalfBEmbedding, peirceHalfCEmbedding]
    exact h₁.symm
  · simp [peirceHalfEmbeddingSum, H3Zorn.instAdd, peirceHalfAEmbedding,
      peirceHalfBEmbedding, peirceHalfCEmbedding]
    exact h₂.symm
  · simp [peirceHalfEmbeddingSum, H3Zorn.instAdd, peirceHalfAEmbedding,
      peirceHalfBEmbedding, peirceHalfCEmbedding]
    exact h₃.symm
  · rw [peirceHalfEmbeddingSum_apply]
    rw [h3Zorn_add_a, h3Zorn_add_a, peirceHalfAEmbedding_a,
      peirceHalfBEmbedding_a, peirceHalfCEmbedding_a]
    have hX : tracelessHermitianZornSoldering X = T.a :=
      tracelessHermitianZornSoldering.apply_symm_apply T.a
    rw [hX]
    ext i <;> simp [ZornVectorMatrix.add, ZornVectorMatrix.zero]
  · rw [peirceHalfEmbeddingSum_apply]
    rw [h3Zorn_add_b, h3Zorn_add_b, peirceHalfAEmbedding_b,
      peirceHalfBEmbedding_b, peirceHalfCEmbedding_b]
    have hY : tracelessHermitianZornSoldering Y = T.b :=
      tracelessHermitianZornSoldering.apply_symm_apply T.b
    rw [hY]
    ext i <;> simp [ZornVectorMatrix.add, ZornVectorMatrix.zero]
  · rw [peirceHalfEmbeddingSum_apply]
    rw [h3Zorn_add_c, h3Zorn_add_c, peirceHalfAEmbedding_c,
      peirceHalfBEmbedding_c, peirceHalfCEmbedding_c]
    have hZ : tracelessHermitianZornSoldering Z = T.c :=
      tracelessHermitianZornSoldering.apply_symm_apply T.c
    rw [hZ]
    ext i <;> simp [ZornVectorMatrix.add, ZornVectorMatrix.zero]

noncomputable def peirceHalfARealAlbertEmbedding
    (X : InfoGeometry.Quantum.Qutrit.tracelessHermitian) : RealAlbertMatrix :=
  InfoGeometry.Algebra.RealAlbertH3ZornCarrierAlignment.equiv.symm (peirceHalfAEmbedding X)

noncomputable def peirceHalfBRealAlbertEmbedding
    (X : InfoGeometry.Quantum.Qutrit.tracelessHermitian) : RealAlbertMatrix :=
  InfoGeometry.Algebra.RealAlbertH3ZornCarrierAlignment.equiv.symm (peirceHalfBEmbedding X)

noncomputable def peirceHalfCRealAlbertEmbedding
    (X : InfoGeometry.Quantum.Qutrit.tracelessHermitian) : RealAlbertMatrix :=
  InfoGeometry.Algebra.RealAlbertH3ZornCarrierAlignment.equiv.symm (peirceHalfCEmbedding X)

@[simp] theorem peirceHalfARealAlbertEmbedding_toH3 (X) :
    InfoGeometry.Algebra.RealAlbertH3ZornCarrierAlignment.equiv
        (peirceHalfARealAlbertEmbedding X) = peirceHalfAEmbedding X := by
  exact InfoGeometry.Algebra.RealAlbertH3ZornCarrierAlignment.equiv.apply_symm_apply _

@[simp] theorem peirceHalfBRealAlbertEmbedding_toH3 (X) :
    InfoGeometry.Algebra.RealAlbertH3ZornCarrierAlignment.equiv
        (peirceHalfBRealAlbertEmbedding X) = peirceHalfBEmbedding X := by
  exact InfoGeometry.Algebra.RealAlbertH3ZornCarrierAlignment.equiv.apply_symm_apply _

@[simp] theorem peirceHalfCRealAlbertEmbedding_toH3 (X) :
    InfoGeometry.Algebra.RealAlbertH3ZornCarrierAlignment.equiv
        (peirceHalfCRealAlbertEmbedding X) = peirceHalfCEmbedding X := by
  exact InfoGeometry.Algebra.RealAlbertH3ZornCarrierAlignment.equiv.apply_symm_apply _

theorem peirceHalfARealAlbertEmbedding_injective :
    Function.Injective peirceHalfARealAlbertEmbedding := by
  intro X Y hXY
  apply peirceHalfAEmbedding_injective
  rw [← peirceHalfARealAlbertEmbedding_toH3 X,
    ← peirceHalfARealAlbertEmbedding_toH3 Y]
  exact congrArg InfoGeometry.Algebra.RealAlbertH3ZornCarrierAlignment.equiv hXY

theorem peirceHalfBRealAlbertEmbedding_injective :
    Function.Injective peirceHalfBRealAlbertEmbedding := by
  intro X Y hXY
  apply peirceHalfBEmbedding_injective
  rw [← peirceHalfBRealAlbertEmbedding_toH3 X,
    ← peirceHalfBRealAlbertEmbedding_toH3 Y]
  exact congrArg InfoGeometry.Algebra.RealAlbertH3ZornCarrierAlignment.equiv hXY

theorem peirceHalfCRealAlbertEmbedding_injective :
    Function.Injective peirceHalfCRealAlbertEmbedding := by
  intro X Y hXY
  apply peirceHalfCEmbedding_injective
  rw [← peirceHalfCRealAlbertEmbedding_toH3 X,
    ← peirceHalfCRealAlbertEmbedding_toH3 Y]
  exact congrArg InfoGeometry.Algebra.RealAlbertH3ZornCarrierAlignment.equiv hXY

theorem tracelessHermitianZornSoldering_apply (X :
    InfoGeometry.Quantum.Qutrit.tracelessHermitian) :
    tracelessHermitianZornSoldering X =
      ∑ i, (gellMannCoordinateBasis.repr X) i • zornCoordinateBasis i := by
  have h := congrArg tracelessHermitianZornSoldering
    (gellMannCoordinateBasis.sum_repr X)
  rw [map_sum] at h
  simp only [map_smul, tracelessHermitianZornSoldering_gellMann] at h
  simpa using h.symm

theorem f4Basis_one_apply (x : H3Zorn ℝ) :
    ((f4Basis 1).1 : Module.End ℝ (H3Zorn ℝ)) x =
      ((h3ZornJordanInnerDerivation h3_diag₁ (h3_off₁₂ 1) :
        Module.End ℝ (H3Zorn ℝ)) x) := by
  rfl

theorem f4Basis_zero_apply_explicit (x : H3Zorn ℝ) :
    ((f4Basis 0).1 : Module.End ℝ (H3Zorn ℝ)) x =
      h3_diag₁ * (h3_off₁₂ 0 * x) -
        h3_off₁₂ 0 * (h3_diag₁ * x) := by
  rw [f4Basis_zero_apply, h3ZornJordanInnerDerivation_apply]

theorem f4Basis_one_apply_explicit (x : H3Zorn ℝ) :
    ((f4Basis 1).1 : Module.End ℝ (H3Zorn ℝ)) x =
      h3_diag₁ * (h3_off₁₂ 1 * x) -
        h3_off₁₂ 1 * (h3_diag₁ * x) := by
  rw [f4Basis_one_apply, h3ZornJordanInnerDerivation_apply]

theorem f4Basis_two_apply (x : H3Zorn ℝ) :
    ((f4Basis 2).1 : Module.End ℝ (H3Zorn ℝ)) x =
      ((h3ZornJordanInnerDerivation h3_diag₁ (h3_off₁₂ 2) :
        Module.End ℝ (H3Zorn ℝ)) x) := by
  rfl

theorem f4Basis_three_apply (x : H3Zorn ℝ) :
    ((f4Basis 3).1 : Module.End ℝ (H3Zorn ℝ)) x =
      ((h3ZornJordanInnerDerivation h3_diag₁ (h3_off₁₂ 3) :
        Module.End ℝ (H3Zorn ℝ)) x) := by
  rfl

theorem f4Basis_two_apply_explicit (x : H3Zorn ℝ) :
    ((f4Basis 2).1 : Module.End ℝ (H3Zorn ℝ)) x =
      h3_diag₁ * (h3_off₁₂ 2 * x) -
        h3_off₁₂ 2 * (h3_diag₁ * x) := by
  rw [f4Basis_two_apply, h3ZornJordanInnerDerivation_apply]

theorem f4Basis_three_apply_explicit (x : H3Zorn ℝ) :
    ((f4Basis 3).1 : Module.End ℝ (H3Zorn ℝ)) x =
      h3_diag₁ * (h3_off₁₂ 3 * x) -
        h3_off₁₂ 3 * (h3_diag₁ * x) := by
  rw [f4Basis_three_apply, h3ZornJordanInnerDerivation_apply]

/-- Native 27-coordinate evaluator for the canonical `H3Zorn` carrier. -/
def h3ZornCoordinate (X : H3Zorn ℝ) : Fin 27 → ℝ :=
  ![X.α₁, X.α₂, X.α₃,
    X.a.a, X.a.v 0, X.a.v 1, X.a.v 2, X.a.w 0, X.a.w 1, X.a.w 2, X.a.b,
    X.b.a, X.b.v 0, X.b.v 1, X.b.v 2, X.b.w 0, X.b.w 1, X.b.w 2, X.b.b,
    X.c.a, X.c.v 0, X.c.v 1, X.c.v 2, X.c.w 0, X.c.w 1, X.c.w 2, X.c.b]

theorem h3ZornCoordinate_zero (i : Fin 27) :
    h3ZornCoordinate (0 : H3Zorn ℝ) i = 0 := by
  fin_cases i <;> rfl

/-- Coordinate evaluator for the action of an explicit `f4Basis` derivation on
an explicitly supplied family of 27 probes. -/
noncomputable def f4BasisCoordinateEntry (probes : Fin 27 → H3Zorn ℝ)
    (i : Fin 52) (r c : Fin 27) : ℝ :=
  h3ZornCoordinate ((f4Basis i).1 (probes r)) c

/-- The complete rational-coordinate row is obtained after a probe family has
been instantiated; this definition is the Lean-side certificate generator. -/
noncomputable def f4BasisCoordinateRow (probes : Fin 27 → H3Zorn ℝ)
    (i : Fin 52) : Fin 729 → ℝ :=
  fun k => f4BasisCoordinateEntry probes i
    ⟨k.val / 27, by omega⟩ ⟨k.val % 27, by omega⟩

@[simp] theorem f4BasisCoordinateRow_apply
    (probes : Fin 27 → H3Zorn ℝ) (i : Fin 52) (r c : Fin 27) :
    f4BasisCoordinateRow probes i ⟨27 * r.val + c.val, by omega⟩ =
      h3ZornCoordinate ((f4Basis i).1 (probes r)) c := by
  dsimp [f4BasisCoordinateRow, f4BasisCoordinateEntry]
  have hr : (⟨(27 * r.val + c.val) / 27, by omega⟩ : Fin 27) = r := by
    ext
    dsimp
    have hrlt := r.isLt
    have hclt := c.isLt
    omega
  have hc : (⟨(27 * r.val + c.val) % 27, by omega⟩ : Fin 27) = c := by
    ext
    dsimp
    have hrlt := r.isLt
    have hclt := c.isLt
    omega
  rw [hr, hc]

/-! ### Canonical finite probe basis for the 27-dimensional carrier

The order below is the same order used by `h3ZornCoordinate`: three diagonal
coordinates, followed by the eight coordinates of `a`, `b`, and `c`.  Thus the
action table below is a genuine finite evaluator, rather than a parameterized
readout depending on an unspecified family of probes.
-/

noncomputable def h3ZornProbe (j : Fin 27) : H3Zorn ℝ :=
  ![h3_diag₁, h3_diag₂, h3_diag₃,
    h3_off₁₂ 0, h3_off₁₂ 1, h3_off₁₂ 2, h3_off₁₂ 3,
    h3_off₁₂ 4, h3_off₁₂ 5, h3_off₁₂ 6, h3_off₁₂ 7,
    h3_off₂₃ 0, h3_off₂₃ 1, h3_off₂₃ 2, h3_off₂₃ 3,
    h3_off₂₃ 4, h3_off₂₃ 5, h3_off₂₃ 6, h3_off₂₃ 7,
    h3_off₃₁ 0, h3_off₃₁ 1, h3_off₃₁ 2, h3_off₃₁ 3,
    h3_off₃₁ 4, h3_off₃₁ 5, h3_off₃₁ 6, h3_off₃₁ 7] j

@[simp] theorem h3ZornProbe_coordinate_self (j : Fin 27) :
    h3ZornCoordinate (h3ZornProbe j) j = 1 := by
  fin_cases j <;> rfl

noncomputable def f4BasisActionCoordinate (i : Fin 52) (r c : Fin 27) : ℝ :=
  h3ZornCoordinate ((f4Basis i).1 (h3ZornProbe r)) c

noncomputable def f4BasisActionCoordinateRow (i : Fin 52) : Fin 729 → ℝ :=
  fun k => f4BasisActionCoordinate i
    ⟨k.val / 27, by omega⟩ ⟨k.val % 27, by omega⟩

@[simp] theorem f4BasisActionCoordinateRow_flatten (i : Fin 52)
    (r c : Fin 27) :
    f4BasisActionCoordinateRow i ⟨27 * r.val + c.val, by omega⟩ =
      f4BasisActionCoordinate i r c := by
  dsimp [f4BasisActionCoordinateRow]
  have hr : (⟨(27 * r.val + c.val) / 27, by omega⟩ : Fin 27) = r := by
    ext
    dsimp
    have hrlt := r.isLt
    have hclt := c.isLt
    omega
  have hc : (⟨(27 * r.val + c.val) % 27, by omega⟩ : Fin 27) = c := by
    ext
    dsimp
    have hrlt := r.isLt
    have hclt := c.isLt
    omega
  rw [hr, hc]

noncomputable def f4BasisActionCoordinateMatrix : Fin 52 → Fin 729 → ℝ :=
  f4BasisActionCoordinateRow

@[simp] theorem f4BasisActionCoordinateMatrix_apply (i : Fin 52)
    (r c : Fin 27) :
    f4BasisActionCoordinateMatrix i ⟨27 * r.val + c.val, by omega⟩ =
      h3ZornCoordinate ((f4Basis i).1 (h3ZornProbe r)) c := by
  exact f4BasisActionCoordinateRow_flatten i r c

theorem f4Basis_export_row (i : Fin 52) :
    ∃ a b : H3Zorn ℝ,
      (f4Basis i).1 =
        (h3ZornJordanInnerDerivation a b : Module.End ℝ (H3Zorn ℝ)) := by
  fin_cases i <;>
    exact ⟨_, _, rfl⟩

theorem f4Basis_export_row_apply (i : Fin 52) (x : H3Zorn ℝ) :
    ∃ a b : H3Zorn ℝ,
      ((f4Basis i).1 : Module.End ℝ (H3Zorn ℝ)) x =
        ((h3ZornJordanInnerDerivation a b : Module.End ℝ (H3Zorn ℝ)) x) := by
  rcases f4Basis_export_row i with ⟨a, b, h⟩
  exact ⟨a, b, congrArg (fun D : Module.End ℝ (H3Zorn ℝ) => D x) h⟩

end InfoGeometry.Algebra
