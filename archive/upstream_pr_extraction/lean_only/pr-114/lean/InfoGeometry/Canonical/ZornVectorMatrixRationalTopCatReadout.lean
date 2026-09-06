import Mathlib.Topology.Category.TopCat.Basic
import InfoGeometry.Algebra.ZornVectorMatrix
import InfoGeometry.Algebra.ZornDualLattice

/-!
# Rational topological readout for the native Zorn carrier

The algebraic owner already supplies `cartanCharge` on `ZornVectorMatrix ℚ`.
This file transports the product topology through its existing coordinate
equivalence and packages that same coordinate projection as a `TopCat` map.
No lattice, charge-spectrum, or maximal-order claim is introduced here.
-/

noncomputable section

namespace InfoGeometry.Canonical

open CategoryTheory
open InfoGeometry.Algebra

instance zornVectorMatrixRationalTopologicalSpace :
    TopologicalSpace (ZornVectorMatrix ℚ) :=
  TopologicalSpace.induced ZornVectorMatrix.coordEquiv.toFun inferInstance

private theorem continuous_zornVectorMatrix_rational_coordEquiv :
    Continuous
      (ZornVectorMatrix.coordEquiv :
        ZornVectorMatrix ℚ ≃
          (ℚ × (Fin 3 → ℚ) × (Fin 3 → ℚ) × ℚ)) :=
  continuous_induced_dom

theorem continuous_zornVectorMatrix_rational_a :
    Continuous (fun X : ZornVectorMatrix ℚ => X.a) :=
  continuous_zornVectorMatrix_rational_coordEquiv.fst

theorem continuous_zornVectorMatrix_rational_b :
    Continuous (fun X : ZornVectorMatrix ℚ => X.b) :=
  continuous_zornVectorMatrix_rational_coordEquiv.snd.snd.snd

theorem continuous_zornVectorMatrix_rational_v (i : Fin 3) :
    Continuous (fun X : ZornVectorMatrix ℚ => X.v i) :=
  (continuous_apply i).comp
    continuous_zornVectorMatrix_rational_coordEquiv.snd.fst

theorem continuous_zornVectorMatrix_rational_w (i : Fin 3) :
    Continuous (fun X : ZornVectorMatrix ℚ => X.w i) :=
  (continuous_apply i).comp
    continuous_zornVectorMatrix_rational_coordEquiv.snd.snd.fst

theorem continuous_zornVectorMatrix_rational_trace :
    Continuous (fun X : ZornVectorMatrix ℚ => ZornVectorMatrix.trace X) := by
  simpa [ZornVectorMatrix.trace] using
    continuous_zornVectorMatrix_rational_a.add
      continuous_zornVectorMatrix_rational_b

theorem continuous_zornVectorMatrix_rational_norm :
    Continuous (fun X : ZornVectorMatrix ℚ => ZornVectorMatrix.norm X) := by
  have hv₀ := continuous_zornVectorMatrix_rational_v (0 : Fin 3)
  have hv₁ := continuous_zornVectorMatrix_rational_v (1 : Fin 3)
  have hv₂ := continuous_zornVectorMatrix_rational_v (2 : Fin 3)
  have hw₀ := continuous_zornVectorMatrix_rational_w (0 : Fin 3)
  have hw₁ := continuous_zornVectorMatrix_rational_w (1 : Fin 3)
  have hw₂ := continuous_zornVectorMatrix_rational_w (2 : Fin 3)
  have hdot : Continuous (fun X : ZornVectorMatrix ℚ =>
      X.v 0 * X.w 0 + X.v 1 * X.w 1 + X.v 2 * X.w 2) := by
    exact ((hv₀.mul hw₀).add (hv₁.mul hw₁)).add (hv₂.mul hw₂)
  simpa [ZornVectorMatrix.norm, ZornVec3.dot_eq_sum_coords] using
    (continuous_zornVectorMatrix_rational_a.mul
      continuous_zornVectorMatrix_rational_b).sub hdot

def zornVectorMatrixRationalTraceTopCat :
    TopCat.of (ZornVectorMatrix ℚ) ⟶ TopCat.of ℚ :=
  TopCat.ofHom
    { toFun := ZornVectorMatrix.trace
      continuous_toFun := continuous_zornVectorMatrix_rational_trace }

def zornVectorMatrixRationalNormTopCat :
    TopCat.of (ZornVectorMatrix ℚ) ⟶ TopCat.of ℚ :=
  TopCat.ofHom
    { toFun := ZornVectorMatrix.norm
      continuous_toFun := continuous_zornVectorMatrix_rational_norm }

def zornVectorMatrixRationalNonIsotropic : Set (ZornVectorMatrix ℚ) :=
  {X | ZornVectorMatrix.norm X ≠ 0}

theorem isOpen_zornVectorMatrixRationalNonIsotropic :
    IsOpen zornVectorMatrixRationalNonIsotropic := by
  have hclosed : IsClosed {X : ZornVectorMatrix ℚ |
      ZornVectorMatrix.norm X = 0} :=
    isClosed_singleton.preimage continuous_zornVectorMatrix_rational_norm
  rw [show zornVectorMatrixRationalNonIsotropic =
      ({X : ZornVectorMatrix ℚ | ZornVectorMatrix.norm X = 0})ᶜ by
        ext X
        simp [zornVectorMatrixRationalNonIsotropic]]
  exact hclosed.isOpen_compl

theorem zornVectorMatrixRationalNonIsotropic_mul_mem
    (X Y : ZornVectorMatrix ℚ)
    (hX : X ∈ zornVectorMatrixRationalNonIsotropic)
    (hY : Y ∈ zornVectorMatrixRationalNonIsotropic) :
    ZornVectorMatrix.mul X Y ∈ zornVectorMatrixRationalNonIsotropic := by
  change ZornVectorMatrix.norm (ZornVectorMatrix.mul X Y) ≠ 0
  exact ZornVectorMatrix.norm_mul_ne_zero X Y hX hY

theorem zornVectorMatrixRationalNonIsotropic_inverseCandidate_mem
    (X : ZornVectorMatrix ℚ)
    (hX : X ∈ zornVectorMatrixRationalNonIsotropic) :
    ZornVectorMatrix.inverseCandidate X ∈
      zornVectorMatrixRationalNonIsotropic := by
  change ZornVectorMatrix.norm
      (ZornVectorMatrix.inverseCandidate X) ≠ 0
  exact ZornVectorMatrix.norm_inverseCandidate_ne_zero X hX

theorem continuous_zornVectorMatrix_rational_polar :
    Continuous (fun p : ZornVectorMatrix ℚ × ZornVectorMatrix ℚ =>
      ZornVectorMatrix.polar p.1 p.2) := by
  have hfst : Continuous (fun p : ZornVectorMatrix ℚ × ZornVectorMatrix ℚ => p.1) :=
    continuous_fst
  have hsnd : Continuous (fun p : ZornVectorMatrix ℚ × ZornVectorMatrix ℚ => p.2) :=
    continuous_snd
  have ha₁ := continuous_zornVectorMatrix_rational_a.comp hfst
  have ha₂ := continuous_zornVectorMatrix_rational_a.comp hsnd
  have hb₁ := continuous_zornVectorMatrix_rational_b.comp hfst
  have hb₂ := continuous_zornVectorMatrix_rational_b.comp hsnd
  have hv₁ := (continuous_zornVectorMatrix_rational_v (0 : Fin 3)).comp hfst
  have hv₂ := (continuous_zornVectorMatrix_rational_v (1 : Fin 3)).comp hfst
  have hv₃ := (continuous_zornVectorMatrix_rational_v (2 : Fin 3)).comp hfst
  have hw₁ := (continuous_zornVectorMatrix_rational_w (0 : Fin 3)).comp hfst
  have hw₂ := (continuous_zornVectorMatrix_rational_w (1 : Fin 3)).comp hfst
  have hw₃ := (continuous_zornVectorMatrix_rational_w (2 : Fin 3)).comp hfst
  have yv₁ := (continuous_zornVectorMatrix_rational_v (0 : Fin 3)).comp hsnd
  have yv₂ := (continuous_zornVectorMatrix_rational_v (1 : Fin 3)).comp hsnd
  have yv₃ := (continuous_zornVectorMatrix_rational_v (2 : Fin 3)).comp hsnd
  have yw₁ := (continuous_zornVectorMatrix_rational_w (0 : Fin 3)).comp hsnd
  have yw₂ := (continuous_zornVectorMatrix_rational_w (1 : Fin 3)).comp hsnd
  have yw₃ := (continuous_zornVectorMatrix_rational_w (2 : Fin 3)).comp hsnd
  have hdiag : Continuous (fun p : ZornVectorMatrix ℚ × ZornVectorMatrix ℚ =>
      p.1.a * p.2.b + p.2.a * p.1.b) :=
    (ha₁.mul hb₂).add (ha₂.mul hb₁)
  have hcross : Continuous (fun p : ZornVectorMatrix ℚ × ZornVectorMatrix ℚ =>
      p.1.v 0 * p.2.w 0 + p.1.v 1 * p.2.w 1 +
      p.1.v 2 * p.2.w 2 + p.2.v 0 * p.1.w 0 +
      p.2.v 1 * p.1.w 1 + p.2.v 2 * p.1.w 2) := by
    exact (((((hv₁.mul yw₁).add (hv₂.mul yw₂)).add (hv₃.mul yw₃)).add
      (yv₁.mul hw₁)).add (yv₂.mul hw₂)).add (yv₃.mul hw₃)
  simpa [ZornVectorMatrix.polar] using hdiag.sub hcross

def zornVectorMatrixRationalPolarTopCat :
    TopCat.of (ZornVectorMatrix ℚ × ZornVectorMatrix ℚ) ⟶ TopCat.of ℚ :=
  TopCat.ofHom
    { toFun := fun p => ZornVectorMatrix.polar p.1 p.2
      continuous_toFun := continuous_zornVectorMatrix_rational_polar }

theorem continuous_zornVectorMatrix_rational_polar_diagonal :
    Continuous (fun X : ZornVectorMatrix ℚ =>
      ZornVectorMatrix.polar X X) := by
  have hdiag : Continuous (fun X : ZornVectorMatrix ℚ => (X, X)) :=
    continuous_id.prodMk continuous_id
  exact continuous_zornVectorMatrix_rational_polar.comp hdiag

def zornVectorMatrixRationalPolarDiagonalTopCat :
    TopCat.of (ZornVectorMatrix ℚ) ⟶ TopCat.of ℚ :=
  TopCat.ofHom
    { toFun := fun X => ZornVectorMatrix.polar X X
      continuous_toFun := continuous_zornVectorMatrix_rational_polar_diagonal }

@[simp] theorem zornVectorMatrixRationalPolarDiagonalTopCat_apply
    (X : ZornVectorMatrix ℚ) :
    zornVectorMatrixRationalPolarDiagonalTopCat X =
      2 * ZornVectorMatrix.norm X := by
  change ZornVectorMatrix.polar X X = 2 * ZornVectorMatrix.norm X
  exact ZornVectorMatrix.polar_self X

theorem continuous_zornVectorMatrix_rational_conj :
    Continuous (fun X : ZornVectorMatrix ℚ => ZornVectorMatrix.conj X) := by
  have hv : Continuous (fun X : ZornVectorMatrix ℚ =>
      fun i => -X.v i) :=
    continuous_pi (fun i => (continuous_zornVectorMatrix_rational_v i).neg)
  have hw : Continuous (fun X : ZornVectorMatrix ℚ =>
      fun i => -X.w i) :=
    continuous_pi (fun i => (continuous_zornVectorMatrix_rational_w i).neg)
  apply (continuous_induced_rng).2
  simpa [ZornVectorMatrix.coordEquiv, ZornVectorMatrix.conj,
    Function.comp_def] using
    continuous_zornVectorMatrix_rational_b.prodMk
      (hv.prodMk (hw.prodMk continuous_zornVectorMatrix_rational_a))

def zornVectorMatrixRationalConjTopCat :
    TopCat.of (ZornVectorMatrix ℚ) ⟶ TopCat.of (ZornVectorMatrix ℚ) :=
  TopCat.ofHom
    { toFun := ZornVectorMatrix.conj
      continuous_toFun := continuous_zornVectorMatrix_rational_conj }

theorem continuous_zornVectorMatrix_rational_mul_a :
    Continuous (fun p : ZornVectorMatrix ℚ × ZornVectorMatrix ℚ =>
      (ZornVectorMatrix.mul p.1 p.2).a) := by
  have hfst : Continuous (fun p : ZornVectorMatrix ℚ × ZornVectorMatrix ℚ => p.1) :=
    continuous_fst
  have hsnd : Continuous (fun p : ZornVectorMatrix ℚ × ZornVectorMatrix ℚ => p.2) :=
    continuous_snd
  have hdot : Continuous (fun p : ZornVectorMatrix ℚ × ZornVectorMatrix ℚ =>
      p.1.v 0 * p.2.w 0 + p.1.v 1 * p.2.w 1 + p.1.v 2 * p.2.w 2) := by
    exact (((continuous_zornVectorMatrix_rational_v 0).comp hfst).mul
      ((continuous_zornVectorMatrix_rational_w 0).comp hsnd) |>.add
      (((continuous_zornVectorMatrix_rational_v 1).comp hfst).mul
        ((continuous_zornVectorMatrix_rational_w 1).comp hsnd))).add
      (((continuous_zornVectorMatrix_rational_v 2).comp hfst).mul
        ((continuous_zornVectorMatrix_rational_w 2).comp hsnd))
  simpa [ZornVectorMatrix.mul, ZornVec3.dot_eq_sum_coords] using
    ((continuous_zornVectorMatrix_rational_a.comp hfst).mul
      (continuous_zornVectorMatrix_rational_a.comp hsnd)).add hdot

theorem continuous_zornVectorMatrix_rational_mul_b :
    Continuous (fun p : ZornVectorMatrix ℚ × ZornVectorMatrix ℚ =>
      (ZornVectorMatrix.mul p.1 p.2).b) := by
  have hfst : Continuous (fun p : ZornVectorMatrix ℚ × ZornVectorMatrix ℚ => p.1) :=
    continuous_fst
  have hsnd : Continuous (fun p : ZornVectorMatrix ℚ × ZornVectorMatrix ℚ => p.2) :=
    continuous_snd
  have hdot : Continuous (fun p : ZornVectorMatrix ℚ × ZornVectorMatrix ℚ =>
      p.1.w 0 * p.2.v 0 + p.1.w 1 * p.2.v 1 + p.1.w 2 * p.2.v 2) := by
    exact (((continuous_zornVectorMatrix_rational_w 0).comp hfst).mul
      ((continuous_zornVectorMatrix_rational_v 0).comp hsnd) |>.add
      (((continuous_zornVectorMatrix_rational_w 1).comp hfst).mul
        ((continuous_zornVectorMatrix_rational_v 1).comp hsnd))).add
      (((continuous_zornVectorMatrix_rational_w 2).comp hfst).mul
        ((continuous_zornVectorMatrix_rational_v 2).comp hsnd))
  simpa [ZornVectorMatrix.mul, ZornVec3.dot_eq_sum_coords] using
    hdot.add ((continuous_zornVectorMatrix_rational_b.comp hfst).mul
      (continuous_zornVectorMatrix_rational_b.comp hsnd))

theorem continuous_zornVectorMatrix_rational_mul_v (i : Fin 3) :
    Continuous (fun p : ZornVectorMatrix ℚ × ZornVectorMatrix ℚ =>
      (ZornVectorMatrix.mul p.1 p.2).v i) := by
  have hfst : Continuous (fun p : ZornVectorMatrix ℚ × ZornVectorMatrix ℚ => p.1) :=
    continuous_fst
  have hsnd : Continuous (fun p : ZornVectorMatrix ℚ × ZornVectorMatrix ℚ => p.2) :=
    continuous_snd
  fin_cases i
  · simpa [ZornVectorMatrix.mul, ZornVec3.cross] using
      (((continuous_zornVectorMatrix_rational_a.comp hfst).mul
          ((continuous_zornVectorMatrix_rational_v 0).comp hsnd)).add
        ((continuous_zornVectorMatrix_rational_b.comp hsnd).mul
          ((continuous_zornVectorMatrix_rational_v 0).comp hfst))).sub
        (((continuous_zornVectorMatrix_rational_w 1).comp hfst).mul
          ((continuous_zornVectorMatrix_rational_w 2).comp hsnd) |>.sub
          (((continuous_zornVectorMatrix_rational_w 2).comp hfst).mul
            ((continuous_zornVectorMatrix_rational_w 1).comp hsnd)))
  · simpa [ZornVectorMatrix.mul, ZornVec3.cross] using
      (((continuous_zornVectorMatrix_rational_a.comp hfst).mul
          ((continuous_zornVectorMatrix_rational_v 1).comp hsnd)).add
        ((continuous_zornVectorMatrix_rational_b.comp hsnd).mul
          ((continuous_zornVectorMatrix_rational_v 1).comp hfst))).sub
        (((continuous_zornVectorMatrix_rational_w 2).comp hfst).mul
          ((continuous_zornVectorMatrix_rational_w 0).comp hsnd) |>.sub
          (((continuous_zornVectorMatrix_rational_w 0).comp hfst).mul
            ((continuous_zornVectorMatrix_rational_w 2).comp hsnd)))
  · simpa [ZornVectorMatrix.mul, ZornVec3.cross] using
      (((continuous_zornVectorMatrix_rational_a.comp hfst).mul
          ((continuous_zornVectorMatrix_rational_v 2).comp hsnd)).add
        ((continuous_zornVectorMatrix_rational_b.comp hsnd).mul
          ((continuous_zornVectorMatrix_rational_v 2).comp hfst))).sub
        (((continuous_zornVectorMatrix_rational_w 0).comp hfst).mul
          ((continuous_zornVectorMatrix_rational_w 1).comp hsnd) |>.sub
          (((continuous_zornVectorMatrix_rational_w 1).comp hfst).mul
            ((continuous_zornVectorMatrix_rational_w 0).comp hsnd)))

theorem continuous_zornVectorMatrix_rational_mul_w (i : Fin 3) :
    Continuous (fun p : ZornVectorMatrix ℚ × ZornVectorMatrix ℚ =>
      (ZornVectorMatrix.mul p.1 p.2).w i) := by
  have hfst : Continuous (fun p : ZornVectorMatrix ℚ × ZornVectorMatrix ℚ => p.1) :=
    continuous_fst
  have hsnd : Continuous (fun p : ZornVectorMatrix ℚ × ZornVectorMatrix ℚ => p.2) :=
    continuous_snd
  fin_cases i
  · simpa [ZornVectorMatrix.mul, ZornVec3.cross] using
      (((continuous_zornVectorMatrix_rational_a.comp hsnd).mul
          ((continuous_zornVectorMatrix_rational_w 0).comp hfst)).add
        ((continuous_zornVectorMatrix_rational_b.comp hfst).mul
          ((continuous_zornVectorMatrix_rational_w 0).comp hsnd))).add
        (((continuous_zornVectorMatrix_rational_v 1).comp hfst).mul
          ((continuous_zornVectorMatrix_rational_v 2).comp hsnd) |>.sub
          (((continuous_zornVectorMatrix_rational_v 2).comp hfst).mul
            ((continuous_zornVectorMatrix_rational_v 1).comp hsnd)))
  · simpa [ZornVectorMatrix.mul, ZornVec3.cross] using
      (((continuous_zornVectorMatrix_rational_a.comp hsnd).mul
          ((continuous_zornVectorMatrix_rational_w 1).comp hfst)).add
        ((continuous_zornVectorMatrix_rational_b.comp hfst).mul
          ((continuous_zornVectorMatrix_rational_w 1).comp hsnd))).add
        (((continuous_zornVectorMatrix_rational_v 2).comp hfst).mul
          ((continuous_zornVectorMatrix_rational_v 0).comp hsnd) |>.sub
          (((continuous_zornVectorMatrix_rational_v 0).comp hfst).mul
            ((continuous_zornVectorMatrix_rational_v 2).comp hsnd)))
  · simpa [ZornVectorMatrix.mul, ZornVec3.cross] using
      (((continuous_zornVectorMatrix_rational_a.comp hsnd).mul
          ((continuous_zornVectorMatrix_rational_w 2).comp hfst)).add
        ((continuous_zornVectorMatrix_rational_b.comp hfst).mul
          ((continuous_zornVectorMatrix_rational_w 2).comp hsnd))).add
        (((continuous_zornVectorMatrix_rational_v 0).comp hfst).mul
          ((continuous_zornVectorMatrix_rational_v 1).comp hsnd) |>.sub
          (((continuous_zornVectorMatrix_rational_v 1).comp hfst).mul
            ((continuous_zornVectorMatrix_rational_v 0).comp hsnd)))

theorem continuous_zornVectorMatrix_rational_mul :
    Continuous (fun p : ZornVectorMatrix ℚ × ZornVectorMatrix ℚ =>
      ZornVectorMatrix.mul p.1 p.2) := by
  apply (continuous_induced_rng).2
  have hv : Continuous (fun p : ZornVectorMatrix ℚ × ZornVectorMatrix ℚ =>
      fun i => (ZornVectorMatrix.mul p.1 p.2).v i) :=
    continuous_pi (fun i => continuous_zornVectorMatrix_rational_mul_v i)
  have hw : Continuous (fun p : ZornVectorMatrix ℚ × ZornVectorMatrix ℚ =>
      fun i => (ZornVectorMatrix.mul p.1 p.2).w i) :=
    continuous_pi (fun i => continuous_zornVectorMatrix_rational_mul_w i)
  simpa [ZornVectorMatrix.coordEquiv, Function.comp_def] using
    continuous_zornVectorMatrix_rational_mul_a.prodMk
      (hv.prodMk (hw.prodMk continuous_zornVectorMatrix_rational_mul_b))

def zornVectorMatrixRationalMulTopCat :
    TopCat.of (ZornVectorMatrix ℚ × ZornVectorMatrix ℚ) ⟶
      TopCat.of (ZornVectorMatrix ℚ) :=
  TopCat.ofHom
    { toFun := fun p => ZornVectorMatrix.mul p.1 p.2
      continuous_toFun := continuous_zornVectorMatrix_rational_mul }

theorem continuous_zornVectorMatrix_rational_smul :
    Continuous (fun p : ℚ × ZornVectorMatrix ℚ =>
      ZornVectorMatrix.smul p.1 p.2) := by
  apply continuous_induced_rng.2
  have ha : Continuous (fun p : ℚ × ZornVectorMatrix ℚ =>
      p.1 * p.2.a) :=
    continuous_fst.mul (continuous_zornVectorMatrix_rational_a.comp continuous_snd)
  have hb : Continuous (fun p : ℚ × ZornVectorMatrix ℚ =>
      p.1 * p.2.b) :=
    continuous_fst.mul (continuous_zornVectorMatrix_rational_b.comp continuous_snd)
  have hv : Continuous (fun p : ℚ × ZornVectorMatrix ℚ =>
      fun i => p.1 * p.2.v i) := by
    exact continuous_pi (fun i =>
      continuous_fst.mul
        ((continuous_zornVectorMatrix_rational_v i).comp continuous_snd))
  have hw : Continuous (fun p : ℚ × ZornVectorMatrix ℚ =>
      fun i => p.1 * p.2.w i) := by
    exact continuous_pi (fun i =>
      continuous_fst.mul
        ((continuous_zornVectorMatrix_rational_w i).comp continuous_snd))
  simpa [ZornVectorMatrix.coordEquiv, ZornVectorMatrix.smul,
    Function.comp_def] using ha.prodMk (hv.prodMk (hw.prodMk hb))

instance zornVectorMatrixRationalContinuousSMul :
    ContinuousSMul ℚ (ZornVectorMatrix ℚ) where
  continuous_smul := continuous_zornVectorMatrix_rational_smul

theorem continuousOn_zornVectorMatrixRational_inverseCandidate :
    ContinuousOn
      (fun X : ZornVectorMatrix ℚ => ZornVectorMatrix.inverseCandidate X)
      zornVectorMatrixRationalNonIsotropic := by
  have hnorm : ContinuousOn
      (fun X : ZornVectorMatrix ℚ => ZornVectorMatrix.norm X)
      zornVectorMatrixRationalNonIsotropic :=
    continuous_zornVectorMatrix_rational_norm.continuousOn
  have hinv : ContinuousOn
      (fun X : ZornVectorMatrix ℚ =>
        (ZornVectorMatrix.norm X)⁻¹)
      zornVectorMatrixRationalNonIsotropic :=
    hnorm.inv₀ (by
      intro X hX
      exact hX)
  simpa [ZornVectorMatrix.inverseCandidate] using
    hinv.smul continuous_zornVectorMatrix_rational_conj.continuousOn

def zornVectorMatrixRationalNonIsotropicSubtypeValTopCat :
    TopCat.of (↥zornVectorMatrixRationalNonIsotropic) ⟶
      TopCat.of (ZornVectorMatrix ℚ) :=
  TopCat.ofHom
    { toFun := Subtype.val
      continuous_toFun := continuous_subtype_val }

def zornVectorMatrixRationalInverseCandidateTopCat :
    TopCat.of (↥zornVectorMatrixRationalNonIsotropic) ⟶
      TopCat.of (ZornVectorMatrix ℚ) :=
  TopCat.ofHom
    { toFun := fun X => ZornVectorMatrix.inverseCandidate X.1
      continuous_toFun := by
        simpa [Set.restrict] using
          continuousOn_zornVectorMatrixRational_inverseCandidate.restrict }

@[simp] theorem zornVectorMatrixRationalInverseCandidateTopCat_apply
    (X : ↥zornVectorMatrixRationalNonIsotropic) :
    zornVectorMatrixRationalInverseCandidateTopCat X =
      ZornVectorMatrix.inverseCandidate X.1 := rfl

def zornVectorMatrixRationalInverseCandidateSelfTopCat :
    TopCat.of (↥zornVectorMatrixRationalNonIsotropic) ⟶
      TopCat.of (↥zornVectorMatrixRationalNonIsotropic) :=
  TopCat.ofHom
    { toFun := fun X =>
        ⟨ZornVectorMatrix.inverseCandidate X.1,
          zornVectorMatrixRationalNonIsotropic_inverseCandidate_mem X.1 X.2⟩
      continuous_toFun := by
        apply Continuous.subtype_mk
        · simpa [Set.restrict] using
            continuousOn_zornVectorMatrixRational_inverseCandidate.restrict }

@[simp] theorem zornVectorMatrixRationalInverseCandidateSelfTopCat_apply
    (X : ↥zornVectorMatrixRationalNonIsotropic) :
    zornVectorMatrixRationalInverseCandidateSelfTopCat X =
      ⟨ZornVectorMatrix.inverseCandidate X.1,
        zornVectorMatrixRationalNonIsotropic_inverseCandidate_mem X.1 X.2⟩ := rfl

theorem zornVectorMatrixRationalInverseCandidateSelfTopCat_involutive
    (X : ↥zornVectorMatrixRationalNonIsotropic) :
    zornVectorMatrixRationalInverseCandidateSelfTopCat
        (zornVectorMatrixRationalInverseCandidateSelfTopCat X) = X := by
  apply Subtype.ext
  exact ZornVectorMatrix.inverseCandidate_inverseCandidate X.1 X.2

def zornVectorMatrixRationalInverseCandidateTopCatIso :
    TopCat.of (↥zornVectorMatrixRationalNonIsotropic) ≅
      TopCat.of (↥zornVectorMatrixRationalNonIsotropic) where
  hom := zornVectorMatrixRationalInverseCandidateSelfTopCat
  inv := zornVectorMatrixRationalInverseCandidateSelfTopCat
  hom_inv_id := by
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro X
    exact zornVectorMatrixRationalInverseCandidateSelfTopCat_involutive X
  inv_hom_id := by
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro X
    exact zornVectorMatrixRationalInverseCandidateSelfTopCat_involutive X

def zornVectorMatrixRationalRightInversePairTopCat :
    TopCat.of (↥zornVectorMatrixRationalNonIsotropic) ⟶
      TopCat.of (ZornVectorMatrix ℚ × ZornVectorMatrix ℚ) :=
  TopCat.ofHom
    { toFun := fun X =>
        (X.1, ZornVectorMatrix.inverseCandidate X.1)
      continuous_toFun := by
        exact continuous_subtype_val.prodMk (by
          simpa [Set.restrict] using
            continuousOn_zornVectorMatrixRational_inverseCandidate.restrict) }

def zornVectorMatrixRationalLeftInversePairTopCat :
    TopCat.of (↥zornVectorMatrixRationalNonIsotropic) ⟶
      TopCat.of (ZornVectorMatrix ℚ × ZornVectorMatrix ℚ) :=
  TopCat.ofHom
    { toFun := fun X =>
        (ZornVectorMatrix.inverseCandidate X.1, X.1)
      continuous_toFun := by
        have hinv : Continuous (fun X : ↥zornVectorMatrixRationalNonIsotropic =>
            ZornVectorMatrix.inverseCandidate X.1) := by
          simpa [Set.restrict] using
            continuousOn_zornVectorMatrixRational_inverseCandidate.restrict
        exact hinv.prodMk continuous_subtype_val }

def zornVectorMatrixRationalOneTopCat :
    TopCat.of (↥zornVectorMatrixRationalNonIsotropic) ⟶
      TopCat.of (ZornVectorMatrix ℚ) :=
  TopCat.ofHom
    (ContinuousMap.const (↥zornVectorMatrixRationalNonIsotropic)
      (ZornVectorMatrix.one : ZornVectorMatrix ℚ))

theorem zornVectorMatrixRationalRightInversePairTopCat_comp_mul :
    zornVectorMatrixRationalRightInversePairTopCat ≫
        zornVectorMatrixRationalMulTopCat =
      zornVectorMatrixRationalOneTopCat := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro X
  rw [TopCat.comp_app]
  exact ZornVectorMatrix.mul_inverseCandidate X.1 X.2

theorem zornVectorMatrixRationalLeftInversePairTopCat_comp_mul :
    zornVectorMatrixRationalLeftInversePairTopCat ≫
        zornVectorMatrixRationalMulTopCat =
      zornVectorMatrixRationalOneTopCat := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro X
  rw [TopCat.comp_app]
  exact ZornVectorMatrix.inverseCandidate_mul X.1 X.2

def zornVectorMatrixRationalNonIsotropicMulTopCat :
    TopCat.of
        (↥zornVectorMatrixRationalNonIsotropic ×
          ↥zornVectorMatrixRationalNonIsotropic) ⟶
      TopCat.of (↥zornVectorMatrixRationalNonIsotropic) :=
  TopCat.ofHom
    { toFun := fun p =>
        ⟨ZornVectorMatrix.mul p.1.1 p.2.1,
          zornVectorMatrixRationalNonIsotropic_mul_mem
            p.1.1 p.2.1 p.1.2 p.2.2⟩
      continuous_toFun := by
        apply Continuous.subtype_mk
        exact continuous_zornVectorMatrix_rational_mul.comp
          ((continuous_subtype_val.comp continuous_fst).prodMk
            (continuous_subtype_val.comp continuous_snd)) }

@[simp] theorem zornVectorMatrixRationalNonIsotropicMulTopCat_apply
    (p : ↥zornVectorMatrixRationalNonIsotropic ×
      ↥zornVectorMatrixRationalNonIsotropic) :
    zornVectorMatrixRationalNonIsotropicMulTopCat p =
      ⟨ZornVectorMatrix.mul p.1.1 p.2.1,
        zornVectorMatrixRationalNonIsotropic_mul_mem
          p.1.1 p.2.1 p.1.2 p.2.2⟩ := rfl

def zornVectorMatrixRationalNonIsotropicScalarTopCat
    (r : ℚ) (hr : r ≠ 0) :
    TopCat.of (↥zornVectorMatrixRationalNonIsotropic) ⟶
      TopCat.of (↥zornVectorMatrixRationalNonIsotropic) :=
  TopCat.ofHom
    { toFun := fun X =>
        ⟨ZornVectorMatrix.smul r X.1,
          ZornVectorMatrix.norm_smul_ne_zero r X.1 hr X.2⟩
      continuous_toFun := by
        apply Continuous.subtype_mk
        have hconst : Continuous
            (fun _ : ↥zornVectorMatrixRationalNonIsotropic => r) :=
          continuous_const
        have hval : Continuous
            (fun X : ↥zornVectorMatrixRationalNonIsotropic => X.1) :=
          continuous_subtype_val
        exact hconst.smul hval }

@[simp] theorem zornVectorMatrixRationalNonIsotropicScalarTopCat_apply
    (r : ℚ) (hr : r ≠ 0)
    (X : ↥zornVectorMatrixRationalNonIsotropic) :
    zornVectorMatrixRationalNonIsotropicScalarTopCat r hr X =
      ⟨ZornVectorMatrix.smul r X.1,
        ZornVectorMatrix.norm_smul_ne_zero r X.1 hr X.2⟩ := rfl

theorem zornVectorMatrixRationalNonIsotropicScalarTopCat_comp
    (r s : ℚ) (hr : r ≠ 0) (hs : s ≠ 0) :
    zornVectorMatrixRationalNonIsotropicScalarTopCat
        (r * s) (mul_ne_zero hr hs) =
      zornVectorMatrixRationalNonIsotropicScalarTopCat r hr ≫
        zornVectorMatrixRationalNonIsotropicScalarTopCat s hs := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro X
  apply Subtype.ext
  change (r * s) • X.1 = s • (r • X.1)
  rw [smul_smul]
  ring

theorem zornVectorMatrixRationalNonIsotropicScalarTopCat_one :
    zornVectorMatrixRationalNonIsotropicScalarTopCat
        1 one_ne_zero = 𝟙 (TopCat.of (↥zornVectorMatrixRationalNonIsotropic)) := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro X
  apply Subtype.ext
  change (1 : ℚ) • X.1 = X.1
  simp

def zornVectorMatrixRationalNormProductTopCat :
    TopCat.of (ZornVectorMatrix ℚ × ZornVectorMatrix ℚ) ⟶ TopCat.of ℚ :=
  TopCat.ofHom
    { toFun := fun p => ZornVectorMatrix.norm p.1 * ZornVectorMatrix.norm p.2
      continuous_toFun := by
        exact (continuous_zornVectorMatrix_rational_norm.comp continuous_fst).mul
          (continuous_zornVectorMatrix_rational_norm.comp continuous_snd) }

theorem zornVectorMatrixRationalNormAfterMulTopCat_eq_normProductTopCat :
    zornVectorMatrixRationalMulTopCat ≫ zornVectorMatrixRationalNormTopCat =
      zornVectorMatrixRationalNormProductTopCat := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro p
  rw [TopCat.comp_app]
  exact ZornVectorMatrix.norm_mul p.1 p.2

def zornVectorMatrixRationalCartanChargeTopCat :
    TopCat.of (ZornVectorMatrix ℚ) ⟶ TopCat.of ℚ :=
  TopCat.ofHom
    { toFun := ZornVectorMatrix.cartanChargeFn
      continuous_toFun := by
        simpa [ZornVectorMatrix.cartanChargeFn] using
          continuous_zornVectorMatrix_rational_a }

@[simp] theorem zornVectorMatrixRationalCartanChargeTopCat_apply
    (X : ZornVectorMatrix ℚ) :
    zornVectorMatrixRationalCartanChargeTopCat X =
      ZornVectorMatrix.cartanCharge X := rfl

theorem zornVectorMatrixRationalCartanChargeTopCat_eq_projection :
    zornVectorMatrixRationalCartanChargeTopCat =
      TopCat.ofHom
        { toFun := fun X : ZornVectorMatrix ℚ => X.a
          continuous_toFun := continuous_zornVectorMatrix_rational_a } := by
  rfl

end InfoGeometry.Canonical
