/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.KK.KasparovCycle
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.KK.CompactOperatorBridge
import InfoGeometry.KK.DiracFredholmIndex
import Mathlib.Analysis.InnerProductSpace.TensorProduct

open scoped InnerProductSpace

namespace InfoGeometry.KK

open InfoGeometry.Krein

/-!
# Bounded Kasparov Product Interfaces

### Evidence Boundaries (`BUCKET 2` vs `BUCKET 3`)
- **`BUCKET 2`**: `FiniteTensorProduct.finiteDimTensorProduct` constructs a concrete
  finite-dimensional `B = ℝ` graded tensor product on `H₁ ⊗[ℝ] H₂` with phase
  `F₁₂ := (1 / Real.sqrt 2) • (X.F ⊗ 1 + Γ₁ ⊗ Y.F)` under the commuting
  fundamental-symmetry hypothesis `KreinGradedModule.IsEven (KreinSpace.jCLM (H := H₁))`.
- **`BUCKET 3`**: The general `KasparovProductData` target remains an interface
  alias over arbitrary `NormedRing B` because `ρ` in `RealSplitKreinKasparovCycle`
  is a second even algebra representation rather than a genuine right Hilbert/Krein
  `B`-module (`C*`-correspondence), and when `J₁` anticommutes with `Γ₁` (the
  `SplitDoubledSpace` convention), `F₁₂` fails `IsKreinSkewAdjoint` under `J₁ ⊗ J₂`
  (proved in `finiteDimTensorPhase_not_kreinSkewAdjoint_of_jCLM_isOdd`).
-/

/--
Interface target for the Kasparov product in the bounded layer.
This packages the output cycle while deferring concrete tensor-product analysis.
-/
abbrev KasparovProductData
    (A B C H₁ H₂ P : Type*)
    [NormedRing A] [NormedRing B] [NormedRing C]
    [NormedAlgebra ℝ A] [NormedAlgebra ℝ B] [NormedAlgebra ℝ C]
    [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁] [CompleteSpace H₁]
    [KreinSpace H₁] [KreinGradedModule H₁]
    [NormedAddCommGroup H₂] [InnerProductSpace ℝ H₂] [CompleteSpace H₂]
    [KreinSpace H₂] [KreinGradedModule H₂]
    [NormedAddCommGroup P] [InnerProductSpace ℝ P] [CompleteSpace P]
    [KreinSpace P] [KreinGradedModule P]
    (_X : KasparovCycle A B H₁)
    (_Y : KasparovCycle B C H₂) :=
  KasparovCycle A C P

namespace FiniteTensorProduct

open scoped TensorProduct

section Instances

variable {H₁ H₂ : Type*}
variable [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁] [CompleteSpace H₁]
variable [KreinSpace H₁] [KreinGradedModule H₁] [FiniteDimensional ℝ H₁]
variable [NormedAddCommGroup H₂] [InnerProductSpace ℝ H₂] [CompleteSpace H₂]
variable [KreinSpace H₂] [KreinGradedModule H₂] [FiniteDimensional ℝ H₂]

/-- Scoped Krein space structure on the finite-dimensional tensor product `H₁ ⊗[ℝ] H₂`
via `J₁ ⊗ J₂`. Registered at priority 1000 inside `FiniteTensorProduct`. -/
noncomputable scoped instance (priority := 1000) instKreinSpaceTensorProduct :
    KreinSpace (H₁ ⊗[ℝ] H₂) where
  J := TensorProduct.congrIsometry (KreinSpace.J (H := H₁)) (KreinSpace.J (H := H₂))
  J_invol x := by
    induction x using TensorProduct.inductionOn with
    | tmul u v =>
      simp [TensorProduct.congrIsometry_apply, KreinSpace.J_invol]
    | add x y hx hy =>
      rw [map_add, map_add, hx, hy]
  J_selfAdj x y := by
    induction x using TensorProduct.inductionOn generalizing y with
    | tmul u₁ v₁ =>
      induction y using TensorProduct.inductionOn with
      | tmul u₂ v₂ =>
        simp [TensorProduct.congrIsometry_apply, TensorProduct.inner_tmul,
          KreinSpace.J_selfAdj]
      | add y₁ y₂ hy₁ hy₂ =>
        rw [inner_add_right, map_add, inner_add_right, hy₁, hy₂]
    | add x₁ x₂ hx₁ hx₂ =>
      rw [inner_add_left, map_add, inner_add_left, hx₁, hx₂]

/-- Scoped graded Krein module structure on `H₁ ⊗[ℝ] H₂` via `Γ₁ ⊗ Γ₂`. -/
noncomputable scoped instance (priority := 1000) instKreinGradedModuleTensorProduct :
    KreinGradedModule (H₁ ⊗[ℝ] H₂) where
  grade := TensorProduct.congrIsometry
    (KreinGradedModule.grade (H := H₁)) (KreinGradedModule.grade (H := H₂))
  grade_invol x := by
    induction x using TensorProduct.inductionOn with
    | tmul u v =>
      simp [TensorProduct.congrIsometry_apply, KreinGradedModule.grade_invol]
    | add x y hx hy =>
      rw [map_add, map_add, hx, hy]
  grade_selfAdj x y := by
    induction x using TensorProduct.inductionOn generalizing y with
    | tmul u₁ v₁ =>
      induction y using TensorProduct.inductionOn with
      | tmul u₂ v₂ =>
        simp [TensorProduct.congrIsometry_apply, TensorProduct.inner_tmul,
          KreinGradedModule.grade_selfAdj]
      | add y₁ y₂ hy₁ hy₂ =>
        rw [inner_add_right, map_add, inner_add_right, hy₁, hy₂]
    | add x₁ x₂ hx₁ hx₂ =>
      rw [inner_add_left, map_add, inner_add_left, hx₁, hx₂]

omit [KreinGradedModule H₁] [KreinGradedModule H₂] in
private lemma jCLM_tensor_apply (u : H₁) (v : H₂) :
    KreinSpace.jCLM (H := H₁ ⊗[ℝ] H₂) (u ⊗ₜ[ℝ] v) =
      (KreinSpace.jCLM (H := H₁) u) ⊗ₜ[ℝ] (KreinSpace.jCLM (H := H₂) v) := rfl

private lemma gradeCLM_tensor_apply (u : H₁) (v : H₂) :
    KreinGradedModule.gradeCLM (H := H₁ ⊗[ℝ] H₂) (u ⊗ₜ[ℝ] v) =
      (KreinGradedModule.gradeCLM (H := H₁) u) ⊗ₜ[ℝ]
        (KreinGradedModule.gradeCLM (H := H₂) v) := rfl

omit [KreinGradedModule H₁] [KreinGradedModule H₂] in
private lemma kreinAdjoint_mapL (S : EndH H₁) (T : EndH H₂) :
    KreinSpace.kreinAdjoint (H := H₁ ⊗[ℝ] H₂) (TensorProduct.mapL S T) =
      TensorProduct.mapL
        (KreinSpace.kreinAdjoint (H := H₁) S)
        (KreinSpace.kreinAdjoint (H := H₂) T) := by
  apply ContinuousLinearMap.ext
  intro x
  induction x using TensorProduct.inductionOn with
  | tmul u v =>
    change KreinSpace.J ((ContinuousLinearMap.adjoint (TensorProduct.mapL S T))
        (KreinSpace.J (u ⊗ₜ[ℝ] v))) =
      TensorProduct.mapL
        (KreinSpace.kreinAdjoint (H := H₁) S)
        (KreinSpace.kreinAdjoint (H := H₂) T) (u ⊗ₜ[ℝ] v)
    rw [TensorProduct.adjoint_mapL]
    change KreinSpace.jCLM (H := H₁ ⊗[ℝ] H₂)
        ((TensorProduct.mapL (ContinuousLinearMap.adjoint S) (ContinuousLinearMap.adjoint T))
          (KreinSpace.jCLM (H := H₁ ⊗[ℝ] H₂) (u ⊗ₜ[ℝ] v))) =
      TensorProduct.mapL
        (KreinSpace.kreinAdjoint (H := H₁) S)
        (KreinSpace.kreinAdjoint (H := H₂) T) (u ⊗ₜ[ℝ] v)
    rw [jCLM_tensor_apply, TensorProduct.mapL_tmul, jCLM_tensor_apply, TensorProduct.mapL_tmul]
    rfl
  | add x y hx hy =>
    rw [map_add, map_add, hx, hy]

private lemma gradeConj_mapL (S : EndH H₁) (T : EndH H₂) :
    KreinGradedModule.gradeConj (H := H₁ ⊗[ℝ] H₂) (TensorProduct.mapL S T) =
      TensorProduct.mapL
        (KreinGradedModule.gradeConj (H := H₁) S)
        (KreinGradedModule.gradeConj (H := H₂) T) := by
  apply ContinuousLinearMap.ext
  intro x
  induction x using TensorProduct.inductionOn with
  | tmul u v =>
    simp only [KreinGradedModule.gradeConj, ContinuousLinearMap.comp_apply,
      TensorProduct.mapL_tmul]
    rw [gradeCLM_tensor_apply, TensorProduct.mapL_tmul, gradeCLM_tensor_apply]
  | add x y hx hy =>
    rw [map_add, map_add, hx, hy]

omit [CompleteSpace H₁] [KreinSpace H₁] [KreinGradedModule H₁] [FiniteDimensional ℝ H₁]
  [CompleteSpace H₂] [KreinSpace H₂] [KreinGradedModule H₂] [FiniteDimensional ℝ H₂] in
private lemma mapL_neg_left (S : EndH H₁) (T : EndH H₂) :
    TensorProduct.mapL (-S) T = -(TensorProduct.mapL S T) := by
  apply ContinuousLinearMap.ext
  intro x
  induction x using TensorProduct.inductionOn with
  | tmul u v =>
    change (-S u) ⊗ₜ[ℝ] T v = -((S u) ⊗ₜ[ℝ] T v)
    exact TensorProduct.neg_tmul _ _
  | add x y hx hy =>
    rw [map_add, map_add, hx, hy]

omit [CompleteSpace H₁] [KreinSpace H₁] [KreinGradedModule H₁] [FiniteDimensional ℝ H₁]
  [CompleteSpace H₂] [KreinSpace H₂] [KreinGradedModule H₂] [FiniteDimensional ℝ H₂] in
private lemma mapL_neg_right (S : EndH H₁) (T : EndH H₂) :
    TensorProduct.mapL S (-T) = -(TensorProduct.mapL S T) := by
  apply ContinuousLinearMap.ext
  intro x
  induction x using TensorProduct.inductionOn with
  | tmul u v =>
    change (S u) ⊗ₜ[ℝ] (-T v) = -((S u) ⊗ₜ[ℝ] T v)
    exact TensorProduct.tmul_neg _ _
  | add x y hx hy =>
    rw [map_add, map_add, hx, hy]

/-- Right-tensor algebra homomorphism `EndH H₁ →ₐ[ℝ] EndH (H₁ ⊗[ℝ] H₂)`. -/
noncomputable def rTensorAlgHom : EndH H₁ →ₐ[ℝ] EndH (H₁ ⊗[ℝ] H₂) where
  toFun T := T.rTensor H₂
  map_one' := ContinuousLinearMap.rTensor_one H₂
  map_mul' S T := ContinuousLinearMap.rTensor_mul H₂ S T
  map_zero' := ContinuousLinearMap.rTensor_zero H₂
  map_add' S T := ContinuousLinearMap.rTensor_add H₂ S T
  commutes' r := by
    apply ContinuousLinearMap.ext
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul u v =>
      simp [Algebra.algebraMap_eq_smul_one]
    | add x y hx hy =>
      rw [map_add, map_add, hx, hy]

/-- Left-tensor algebra homomorphism `EndH H₂ →ₐ[ℝ] EndH (H₁ ⊗[ℝ] H₂)`. -/
noncomputable def lTensorAlgHom : EndH H₂ →ₐ[ℝ] EndH (H₁ ⊗[ℝ] H₂) where
  toFun T := T.lTensor H₁
  map_one' := ContinuousLinearMap.lTensor_one H₁
  map_mul' S T := ContinuousLinearMap.lTensor_mul H₁ S T
  map_zero' := ContinuousLinearMap.lTensor_zero H₁
  map_add' S T := ContinuousLinearMap.lTensor_add H₁ S T
  commutes' r := by
    apply ContinuousLinearMap.ext
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul u v =>
      simp [Algebra.algebraMap_eq_smul_one]
    | add x y hx hy =>
      rw [map_add, map_add, hx, hy]

end Instances

section FiniteProduct

variable {A C H₁ H₂ : Type*}
variable [NormedRing A] [NormedRing C] [NormedAlgebra ℝ A] [NormedAlgebra ℝ C]
variable [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁] [CompleteSpace H₁]
variable [KreinSpace H₁] [KreinGradedModule H₁] [FiniteDimensional ℝ H₁]
variable [NormedAddCommGroup H₂] [InnerProductSpace ℝ H₂] [CompleteSpace H₂]
variable [KreinSpace H₂] [KreinGradedModule H₂] [FiniteDimensional ℝ H₂]

/-- Lift the split `Cl(1,1)` action from `H₁` onto `H₁ ⊗[ℝ] H₂`. -/
noncomputable def finiteDimTensorCl11Action
    (X : KasparovCycle A ℝ H₁) :
    InfoGeometry.Quantum.RealSplitCl11Action (H₁ ⊗[ℝ] H₂) where
  eps := X.cl11.eps.rTensor H₂
  J := X.cl11.J.rTensor H₂
  eps_sq := by
    rw [← ContinuousLinearMap.rTensor_comp, X.cl11.eps_sq, ContinuousLinearMap.rTensor_id]
  J_sq := by
    rw [← ContinuousLinearMap.rTensor_comp, X.cl11.J_sq, ContinuousLinearMap.rTensor_id]
  J_eps_anti := by
    rw [← ContinuousLinearMap.rTensor_comp, X.cl11.J_eps_anti, ContinuousLinearMap.rTensor_neg,
      ContinuousLinearMap.rTensor_comp]

/-- `BUCKET 2` graded tensor phase `(1 / √2) • (F₁ ⊗ 1 + Γ₁ ⊗ F₂)` on `H₁ ⊗[ℝ] H₂`. -/
noncomputable def finiteDimTensorPhase
    (X : KasparovCycle A ℝ H₁) (Y : KasparovCycle ℝ C H₂) :
    EndH (H₁ ⊗[ℝ] H₂) :=
  ((1 / Real.sqrt 2) : ℝ) •
    (X.F.rTensor H₂ + TensorProduct.mapL (KreinGradedModule.gradeCLM (H := H₁)) Y.F)

theorem finiteDimTensorPhase_isOdd
    (X : KasparovCycle A ℝ H₁) (Y : KasparovCycle ℝ C H₂) :
    KreinGradedModule.IsOdd (H := H₁ ⊗[ℝ] H₂) (finiteDimTensorPhase X Y) := by
  have h1 : KreinGradedModule.IsOdd (H := H₁ ⊗[ℝ] H₂) (X.F.rTensor H₂) := by
    unfold KreinGradedModule.IsOdd
    rw [ContinuousLinearMap.rTensor_eq_mapL, gradeConj_mapL, X.F_odd]
    have hId : KreinGradedModule.gradeConj (H := H₂) (ContinuousLinearMap.id ℝ H₂) =
        ContinuousLinearMap.id ℝ H₂ := by
      unfold KreinGradedModule.gradeConj
      ext x
      simp
    rw [hId, mapL_neg_left]
  have h2 : KreinGradedModule.IsOdd (H := H₁ ⊗[ℝ] H₂)
      (TensorProduct.mapL (KreinGradedModule.gradeCLM (H := H₁)) Y.F) := by
    unfold KreinGradedModule.IsOdd
    rw [gradeConj_mapL, Y.F_odd]
    have hGamma : KreinGradedModule.gradeConj (H := H₁) (KreinGradedModule.gradeCLM (H := H₁)) =
        KreinGradedModule.gradeCLM (H := H₁) := by
      unfold KreinGradedModule.gradeConj
      ext x
      simp
    rw [hGamma, mapL_neg_right]
  unfold KreinGradedModule.IsOdd
  ext z
  have h1z := congrArg (fun T : EndH (H₁ ⊗[ℝ] H₂) => T z) h1
  have h2z := congrArg (fun T : EndH (H₁ ⊗[ℝ] H₂) => T z) h2
  have h1z' :
      KreinGradedModule.gradeCLM (H := H₁ ⊗[ℝ] H₂)
          (X.F.rTensor H₂ (KreinGradedModule.gradeCLM (H := H₁ ⊗[ℝ] H₂) z)) =
        -(X.F.rTensor H₂ z) := h1z
  have h2z' :
      KreinGradedModule.gradeCLM (H := H₁ ⊗[ℝ] H₂)
          (TensorProduct.mapL (KreinGradedModule.gradeCLM (H := H₁)) Y.F
            (KreinGradedModule.gradeCLM (H := H₁ ⊗[ℝ] H₂) z)) =
        -(TensorProduct.mapL (KreinGradedModule.gradeCLM (H := H₁)) Y.F z) := h2z
  change KreinGradedModule.gradeCLM (H := H₁ ⊗[ℝ] H₂)
      (((1 / Real.sqrt 2 : ℝ) •
        (X.F.rTensor H₂ + TensorProduct.mapL (KreinGradedModule.gradeCLM (H := H₁)) Y.F))
        (KreinGradedModule.gradeCLM (H := H₁ ⊗[ℝ] H₂) z)) =
    -(((1 / Real.sqrt 2 : ℝ) •
        (X.F.rTensor H₂ + TensorProduct.mapL (KreinGradedModule.gradeCLM (H := H₁)) Y.F)) z)
  simp only [smul_apply, add_apply, map_smul, map_add, h1z', h2z', ← neg_add, smul_neg]

omit [FiniteDimensional ℝ H₁] in
private lemma kreinAdjoint_gradeCLM_of_isEven
    (hJ₁_even : KreinGradedModule.IsEven (H := H₁) (KreinSpace.jCLM (H := H₁))) :
    KreinSpace.kreinAdjoint (H := H₁) (KreinGradedModule.gradeCLM (H := H₁)) =
      KreinGradedModule.gradeCLM (H := H₁) := by
  have hGradeAdj :
      ContinuousLinearMap.adjoint (KreinGradedModule.gradeCLM (H := H₁)) =
        KreinGradedModule.gradeCLM (H := H₁) := by
    symm
    refine (ContinuousLinearMap.eq_adjoint_iff _ _).2 fun u v => ?_
    exact KreinGradedModule.grade_selfAdj (H := H₁) u v
  have hAnti :
      (KreinGradedModule.gradeCLM (H := H₁)).comp (KreinSpace.jCLM (H := H₁)) =
        (KreinSpace.jCLM (H := H₁)).comp (KreinGradedModule.gradeCLM (H := H₁)) := by
    have h := congrArg (fun T : EndH H₁ => T.comp (KreinGradedModule.gradeCLM (H := H₁))) hJ₁_even
    simpa [KreinGradedModule.gradeConj, ContinuousLinearMap.comp_assoc] using h
  apply ContinuousLinearMap.ext
  intro x
  rw [KreinSpace.kreinAdjoint_apply, hGradeAdj]
  have hstep : KreinGradedModule.gradeCLM (H := H₁) (KreinSpace.jCLM (H := H₁) x) =
      KreinSpace.jCLM (H := H₁) (KreinGradedModule.gradeCLM (H := H₁) x) :=
    congrArg (fun T : EndH H₁ => T x) hAnti
  change KreinSpace.jCLM (H := H₁)
      (KreinGradedModule.gradeCLM (H := H₁) (KreinSpace.jCLM (H := H₁) x)) =
    KreinGradedModule.gradeCLM (H := H₁) x
  rw [hstep]
  simpa using KreinSpace.J_invol (H := H₁) (KreinGradedModule.gradeCLM (H := H₁) x)

theorem finiteDimTensorPhase_isKreinSkewAdjoint
    (X : KasparovCycle A ℝ H₁) (Y : KasparovCycle ℝ C H₂)
    (hJ₁_even : KreinGradedModule.IsEven (H := H₁) (KreinSpace.jCLM (H := H₁))) :
    KreinSpace.IsKreinSkewAdjoint (H := H₁ ⊗[ℝ] H₂) (finiteDimTensorPhase X Y) := by
  have h1 : KreinSpace.IsKreinSkewAdjoint (H := H₁ ⊗[ℝ] H₂) (X.F.rTensor H₂) := by
    unfold KreinSpace.IsKreinSkewAdjoint
    rw [ContinuousLinearMap.rTensor_eq_mapL, kreinAdjoint_mapL, X.F_skewAdj,
      show KreinSpace.kreinAdjoint (H := H₂) (ContinuousLinearMap.id ℝ H₂) =
          ContinuousLinearMap.id ℝ H₂ from KreinSpace.kreinAdjoint_id,
      mapL_neg_left]
  have h2 : KreinSpace.IsKreinSkewAdjoint (H := H₁ ⊗[ℝ] H₂)
      (TensorProduct.mapL (KreinGradedModule.gradeCLM (H := H₁)) Y.F) := by
    unfold KreinSpace.IsKreinSkewAdjoint
    rw [kreinAdjoint_mapL, kreinAdjoint_gradeCLM_of_isEven hJ₁_even, Y.F_skewAdj,
      mapL_neg_right]
  rw [KreinSpace.isKreinSkewAdjoint_iff]
  have h1' := (KreinSpace.isKreinSkewAdjoint_iff (H := H₁ ⊗[ℝ] H₂) _).mp h1
  have h2' := (KreinSpace.isKreinSkewAdjoint_iff (H := H₁ ⊗[ℝ] H₂) _).mp h2
  intro u v
  change KreinSpace.kreinInner
      ((1 / Real.sqrt 2 : ℝ) •
        (X.F.rTensor H₂ u + TensorProduct.mapL (KreinGradedModule.gradeCLM (H := H₁)) Y.F u)) v +
    KreinSpace.kreinInner u
      ((1 / Real.sqrt 2 : ℝ) •
        (X.F.rTensor H₂ v + TensorProduct.mapL (KreinGradedModule.gradeCLM (H := H₁)) Y.F v)) = 0
  rw [KreinSpace.kreinInner_smul_left, KreinSpace.kreinInner_smul_right,
    KreinSpace.kreinInner_add_left, KreinSpace.kreinInner_add_right]
  have hsum :
      (KreinSpace.kreinInner (X.F.rTensor H₂ u) v +
        KreinSpace.kreinInner u (X.F.rTensor H₂ v)) +
      (KreinSpace.kreinInner (TensorProduct.mapL (KreinGradedModule.gradeCLM (H := H₁)) Y.F u) v +
        KreinSpace.kreinInner u (TensorProduct.mapL (KreinGradedModule.gradeCLM (H := H₁)) Y.F v)) =
      0 := by
    rw [h1' u v, h2' u v, add_zero]
  calc
    (1 / Real.sqrt 2 : ℝ) *
          (KreinSpace.kreinInner (X.F.rTensor H₂ u) v +
            KreinSpace.kreinInner (TensorProduct.mapL (KreinGradedModule.gradeCLM (H := H₁)) Y.F u) v) +
        (1 / Real.sqrt 2 : ℝ) *
          (KreinSpace.kreinInner u (X.F.rTensor H₂ v) +
            KreinSpace.kreinInner u (TensorProduct.mapL (KreinGradedModule.gradeCLM (H := H₁)) Y.F v))
        = (1 / Real.sqrt 2 : ℝ) *
            ((KreinSpace.kreinInner (X.F.rTensor H₂ u) v +
                KreinSpace.kreinInner u (X.F.rTensor H₂ v)) +
              (KreinSpace.kreinInner
                  (TensorProduct.mapL (KreinGradedModule.gradeCLM (H := H₁)) Y.F u) v +
                KreinSpace.kreinInner u
                  (TensorProduct.mapL (KreinGradedModule.gradeCLM (H := H₁)) Y.F v))) := by
          ring
    _ = 0 := by rw [hsum, mul_zero]

omit [FiniteDimensional ℝ H₁] [FiniteDimensional ℝ H₂] in
theorem finiteDimTensorPhase_sq_eq_one_of_sq_one
    (X : KasparovCycle A ℝ H₁) (Y : KasparovCycle ℝ C H₂)
    (hX : X.F * X.F = 1) (hY : Y.F * Y.F = 1) :
    finiteDimTensorPhase X Y * finiteDimTensorPhase X Y = 1 := by
  have hAnti : (KreinGradedModule.gradeCLM (H := H₁)).comp X.F +
      X.F.comp (KreinGradedModule.gradeCLM (H := H₁)) = 0 := by
    rw [X.dirac_anticommutes_chirality]
    simp
  have hCross :
      (X.F.rTensor H₂) * (TensorProduct.mapL (KreinGradedModule.gradeCLM (H := H₁)) Y.F) +
      (TensorProduct.mapL (KreinGradedModule.gradeCLM (H := H₁)) Y.F) * (X.F.rTensor H₂) = 0 := by
    apply ContinuousLinearMap.ext
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul u v =>
      simp only [add_apply, mul_apply_eq_comp,
        ContinuousLinearMap.rTensor_tmul, TensorProduct.mapL_tmul, zero_apply]
      have hu : X.F (KreinGradedModule.gradeCLM (H := H₁) u) +
          KreinGradedModule.gradeCLM (H := H₁) (X.F u) = 0 := by
        simpa [ContinuousLinearMap.comp_apply, add_comm] using
          congrArg (fun T : EndH H₁ => T u) hAnti
      calc
        X.F (KreinGradedModule.gradeCLM (H := H₁) u) ⊗ₜ[ℝ] Y.F v +
            KreinGradedModule.gradeCLM (H := H₁) (X.F u) ⊗ₜ[ℝ] Y.F v
            = (X.F (KreinGradedModule.gradeCLM (H := H₁) u) +
                KreinGradedModule.gradeCLM (H := H₁) (X.F u)) ⊗ₜ[ℝ] Y.F v := by
              rw [← TensorProduct.add_tmul]
        _ = (0 : H₁) ⊗ₜ[ℝ] Y.F v := by rw [hu]
        _ = 0 := TensorProduct.zero_tmul _ _
    | add z₁ z₂ hz₁ hz₂ =>
      rw [map_add, map_add, hz₁, hz₂]
  have hTerm1 : X.F.rTensor H₂ * X.F.rTensor H₂ = 1 := by
    rw [← ContinuousLinearMap.rTensor_mul, hX, ContinuousLinearMap.rTensor_one]
  have hTerm2 :
      TensorProduct.mapL (KreinGradedModule.gradeCLM (H := H₁)) Y.F *
        TensorProduct.mapL (KreinGradedModule.gradeCLM (H := H₁)) Y.F = 1 := by
    rw [← TensorProduct.mapL_mul,
      show KreinGradedModule.gradeCLM (H := H₁) * KreinGradedModule.gradeCLM (H := H₁) = 1 from
        KreinGradedModule.gradeCLM_comp_self (H := H₁),
      hY]
    exact TensorProduct.mapL_id_id
  have hSumSq :
      (X.F.rTensor H₂ + TensorProduct.mapL (KreinGradedModule.gradeCLM (H := H₁)) Y.F) *
        (X.F.rTensor H₂ + TensorProduct.mapL (KreinGradedModule.gradeCLM (H := H₁)) Y.F) =
      (2 : ℝ) • (1 : EndH (H₁ ⊗[ℝ] H₂)) := by
    calc
      (X.F.rTensor H₂ + TensorProduct.mapL (KreinGradedModule.gradeCLM (H := H₁)) Y.F) *
          (X.F.rTensor H₂ + TensorProduct.mapL (KreinGradedModule.gradeCLM (H := H₁)) Y.F)
          = X.F.rTensor H₂ * X.F.rTensor H₂ +
              (X.F.rTensor H₂ * TensorProduct.mapL (KreinGradedModule.gradeCLM (H := H₁)) Y.F +
                TensorProduct.mapL (KreinGradedModule.gradeCLM (H := H₁)) Y.F * X.F.rTensor H₂) +
              TensorProduct.mapL (KreinGradedModule.gradeCLM (H := H₁)) Y.F *
                TensorProduct.mapL (KreinGradedModule.gradeCLM (H := H₁)) Y.F := by
            noncomm_ring
      _ = 1 + 0 + 1 := by rw [hTerm1, hCross, hTerm2]
      _ = (2 : ℝ) • (1 : EndH (H₁ ⊗[ℝ] H₂)) := by
            ext z; simp [two_smul]
  have hc : (1 / Real.sqrt 2 * (1 / Real.sqrt 2)) * (2 : ℝ) = 1 := by
    have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
    field_simp
    nlinarith [h2]
  apply ContinuousLinearMap.ext
  intro z
  change finiteDimTensorPhase X Y (finiteDimTensorPhase X Y z) = z
  let S := X.F.rTensor H₂ + TensorProduct.mapL (KreinGradedModule.gradeCLM (H := H₁)) Y.F
  have hSS : S (S z) = (2 : ℝ) • z := by
    simpa [S, mul_apply_eq_comp] using congrArg (fun T : EndH (H₁ ⊗[ℝ] H₂) => T z) hSumSq
  change ((1 / Real.sqrt 2 : ℝ) • S) (((1 / Real.sqrt 2 : ℝ) • S) z) = z
  simp only [smul_apply, map_smul, hSS, smul_smul]
  rw [show (1 / Real.sqrt 2 : ℝ) * ((1 / Real.sqrt 2 : ℝ) * 2) = 1 by nlinarith [hc], one_smul]

/--
`BUCKET 2` finite-dimensional `B = ℝ` graded tensor product packaging
`KasparovProductData A ℝ C H₁ H₂ (H₁ ⊗[ℝ] H₂) X Y` under the commuting
fundamental-symmetry hypothesis `IsEven (KreinSpace.jCLM (H := H₁))`.
-/
noncomputable def finiteDimTensorProduct
    (X : KasparovCycle A ℝ H₁) (Y : KasparovCycle ℝ C H₂)
    (hJ₁_even : KreinGradedModule.IsEven (H := H₁) (KreinSpace.jCLM (H := H₁))) :
    KasparovProductData A ℝ C H₁ H₂ (H₁ ⊗[ℝ] H₂) X Y where
  cl11 := finiteDimTensorCl11Action X
  π := rTensorAlgHom.comp X.π
  ρ := lTensorAlgHom.comp Y.ρ
  π_even := fun a => by
    unfold KreinGradedModule.IsEven
    change KreinGradedModule.gradeConj (H := H₁ ⊗[ℝ] H₂) ((X.π a).rTensor H₂) =
      (X.π a).rTensor H₂
    rw [ContinuousLinearMap.rTensor_eq_mapL, gradeConj_mapL, X.π_even a]
    have hId : KreinGradedModule.gradeConj (H := H₂) (ContinuousLinearMap.id ℝ H₂) =
        ContinuousLinearMap.id ℝ H₂ := by
      unfold KreinGradedModule.gradeConj
      ext x
      simp
    rw [hId]
  ρ_even := fun c => by
    unfold KreinGradedModule.IsEven
    change KreinGradedModule.gradeConj (H := H₁ ⊗[ℝ] H₂) ((Y.ρ c).lTensor H₁) =
      (Y.ρ c).lTensor H₁
    rw [ContinuousLinearMap.lTensor_eq_mapL, gradeConj_mapL, Y.ρ_even c]
    have hId : KreinGradedModule.gradeConj (H := H₁) (ContinuousLinearMap.id ℝ H₁) =
        ContinuousLinearMap.id ℝ H₁ := by
      unfold KreinGradedModule.gradeConj
      ext x
      simp
    rw [hId]
  F := finiteDimTensorPhase X Y
  F_odd := finiteDimTensorPhase_isOdd X Y
  F_skewAdj := finiteDimTensorPhase_isKreinSkewAdjoint X Y hJ₁_even
  F_sq_one_compact := isCompactEnd_of_finiteDimensional (H := H₁ ⊗[ℝ] H₂) _
  comm_compact := fun _ => isCompactEnd_of_finiteDimensional (H := H₁ ⊗[ℝ] H₂) _
  superComm_eps_compact := isCompactEnd_of_finiteDimensional (H := H₁ ⊗[ℝ] H₂) _
  superComm_J_compact := isCompactEnd_of_finiteDimensional (H := H₁ ⊗[ℝ] H₂) _

/--
`BUCKET 3` sign-obstruction theorem: when `J₁` anticommutes with `Γ₁`
(`IsOdd (KreinSpace.jCLM (H := H₁))`, as in `SplitDoubledSpace E` / `DoubledSpace E`),
the naive graded tensor phase `F₁₂ = (1/√2)(F₁ ⊗ 1 + Γ₁ ⊗ F₂)` flips the Krein adjoint
sign on `Γ₁ ⊗ F₂` to `+Γ₁ ⊗ F₂` and therefore fails `IsKreinSkewAdjoint` under `J₁ ⊗ J₂`
whenever `Y.F ≠ 0` and `[Nontrivial H₁]`.
-/
theorem finiteDimTensorPhase_not_kreinSkewAdjoint_of_jCLM_isOdd
    [Nontrivial H₁]
    (X : KasparovCycle A ℝ H₁) (Y : KasparovCycle ℝ C H₂)
    (hJ₁_odd : KreinGradedModule.IsOdd (H := H₁) (KreinSpace.jCLM (H := H₁)))
    (hYF : Y.F ≠ 0) :
    ¬ KreinSpace.IsKreinSkewAdjoint (H := H₁ ⊗[ℝ] H₂) (finiteDimTensorPhase X Y) := by
  have hGradeAdj :
      ContinuousLinearMap.adjoint (KreinGradedModule.gradeCLM (H := H₁)) =
        KreinGradedModule.gradeCLM (H := H₁) := by
    symm
    refine (ContinuousLinearMap.eq_adjoint_iff _ _).2 fun u v => ?_
    exact KreinGradedModule.grade_selfAdj (H := H₁) u v
  have hKreinGamma :
      KreinSpace.kreinAdjoint (H := H₁) (KreinGradedModule.gradeCLM (H := H₁)) =
        -(KreinGradedModule.gradeCLM (H := H₁)) := by
    have hAnti :
        (KreinGradedModule.gradeCLM (H := H₁)).comp (KreinSpace.jCLM (H := H₁)) =
          -((KreinSpace.jCLM (H := H₁)).comp (KreinGradedModule.gradeCLM (H := H₁))) := by
      have h := congrArg (fun T : EndH H₁ => T.comp (KreinGradedModule.gradeCLM (H := H₁))) hJ₁_odd
      simpa [KreinGradedModule.gradeConj, ContinuousLinearMap.comp_assoc] using h
    apply ContinuousLinearMap.ext
    intro x
    rw [KreinSpace.kreinAdjoint_apply, hGradeAdj]
    have hstep : KreinGradedModule.gradeCLM (H := H₁) (KreinSpace.jCLM (H := H₁) x) =
        -(KreinSpace.jCLM (H := H₁) (KreinGradedModule.gradeCLM (H := H₁) x)) :=
      congrArg (fun T : EndH H₁ => T x) hAnti
    change KreinSpace.jCLM (H := H₁)
        (KreinGradedModule.gradeCLM (H := H₁) (KreinSpace.jCLM (H := H₁) x)) =
      -(KreinGradedModule.gradeCLM (H := H₁) x)
    rw [hstep, map_neg]
    simpa using congrArg Neg.neg
      (KreinSpace.J_invol (H := H₁) (KreinGradedModule.gradeCLM (H := H₁) x))
  have h1 : KreinSpace.kreinAdjoint (H := H₁ ⊗[ℝ] H₂) (X.F.rTensor H₂) =
      -(X.F.rTensor H₂) := by
    rw [ContinuousLinearMap.rTensor_eq_mapL, kreinAdjoint_mapL, X.F_skewAdj,
      show KreinSpace.kreinAdjoint (H := H₂) (ContinuousLinearMap.id ℝ H₂) =
          ContinuousLinearMap.id ℝ H₂ from KreinSpace.kreinAdjoint_id,
      mapL_neg_left]
  have h2 : KreinSpace.kreinAdjoint (H := H₁ ⊗[ℝ] H₂)
      (TensorProduct.mapL (KreinGradedModule.gradeCLM (H := H₁)) Y.F) =
      TensorProduct.mapL (KreinGradedModule.gradeCLM (H := H₁)) Y.F := by
    rw [kreinAdjoint_mapL, hKreinGamma, Y.F_skewAdj, mapL_neg_left,
      mapL_neg_right, neg_neg]
  intro hSkew
  have hSkew' := (KreinSpace.isKreinSkewAdjoint_iff (H := H₁ ⊗[ℝ] H₂) _).mp hSkew
  have h1' := (KreinSpace.isKreinSkewAdjoint_iff (H := H₁ ⊗[ℝ] H₂) _).mp h1
  have hInnerEq : ∀ u v : H₁ ⊗[ℝ] H₂,
      KreinSpace.kreinInner
        (TensorProduct.mapL (KreinGradedModule.gradeCLM (H := H₁)) Y.F u) v = 0 := by
    intro u v
    have huv := hSkew' u v
    change KreinSpace.kreinInner
        ((1 / Real.sqrt 2 : ℝ) •
          (X.F.rTensor H₂ u + TensorProduct.mapL (KreinGradedModule.gradeCLM (H := H₁)) Y.F u)) v +
      KreinSpace.kreinInner u
        ((1 / Real.sqrt 2 : ℝ) •
          (X.F.rTensor H₂ v + TensorProduct.mapL (KreinGradedModule.gradeCLM (H := H₁)) Y.F v)) = 0
      at huv
    rw [KreinSpace.kreinInner_smul_left, KreinSpace.kreinInner_smul_right,
      KreinSpace.kreinInner_add_left, KreinSpace.kreinInner_add_right] at huv
    have h2' :
        KreinSpace.kreinInner u
            (TensorProduct.mapL (KreinGradedModule.gradeCLM (H := H₁)) Y.F v) =
          KreinSpace.kreinInner
            (TensorProduct.mapL (KreinGradedModule.gradeCLM (H := H₁)) Y.F u) v := by
      rw [KreinSpace.kreinInner_kreinAdjoint, h2]
    have hc : (1 / Real.sqrt 2 : ℝ) ≠ 0 := by positivity
    have hfact :
        (1 / Real.sqrt 2 : ℝ) *
          ((KreinSpace.kreinInner (X.F.rTensor H₂ u) v +
              KreinSpace.kreinInner u (X.F.rTensor H₂ v)) +
            (KreinSpace.kreinInner
                (TensorProduct.mapL (KreinGradedModule.gradeCLM (H := H₁)) Y.F u) v +
              KreinSpace.kreinInner u
                (TensorProduct.mapL (KreinGradedModule.gradeCLM (H := H₁)) Y.F v))) = 0 := by
      linarith [huv]
    have hadd :
        (KreinSpace.kreinInner (X.F.rTensor H₂ u) v +
          KreinSpace.kreinInner u (X.F.rTensor H₂ v)) +
        (KreinSpace.kreinInner
            (TensorProduct.mapL (KreinGradedModule.gradeCLM (H := H₁)) Y.F u) v +
          KreinSpace.kreinInner u
            (TensorProduct.mapL (KreinGradedModule.gradeCLM (H := H₁)) Y.F v)) = 0 :=
      (mul_eq_zero.mp hfact).resolve_left hc
    rw [h1' u v, zero_add, h2'] at hadd
    linarith
  have hMapZero : TensorProduct.mapL (KreinGradedModule.gradeCLM (H := H₁)) Y.F = 0 := by
    apply ContinuousLinearMap.ext
    intro u
    apply KreinSpace.J.injective
    apply ext_inner_right ℝ
    intro v
    have h0 := hInnerEq u v
    simpa [KreinSpace.kreinInner_def] using h0
  obtain ⟨v₁, hv₁⟩ := exists_ne (0 : H₁)
  have hv₂ : ∃ v₂ : H₂, Y.F v₂ ≠ 0 := by
    by_contra hAll
    push Not at hAll
    exact hYF (ContinuousLinearMap.ext hAll)
  rcases hv₂ with ⟨v₂, hv₂⟩
  have hG₁ : KreinGradedModule.gradeCLM (H := H₁) v₁ ≠ 0 := by
    intro h0
    have h1' := congrArg (KreinGradedModule.gradeCLM (H := H₁)) h0
    simp [KreinGradedModule.grade_invol] at h1'
    exact hv₁ h1'
  have hTmulZero : (KreinGradedModule.gradeCLM (H := H₁) v₁) ⊗ₜ[ℝ] (Y.F v₂) = 0 := by
    have := congrArg (fun T : EndH (H₁ ⊗[ℝ] H₂) => T (v₁ ⊗ₜ[ℝ] v₂)) hMapZero
    simpa [TensorProduct.mapL_tmul] using this
  have hInnerPos :
      0 < inner (𝕜 := ℝ)
        ((KreinGradedModule.gradeCLM (H := H₁) v₁) ⊗ₜ[ℝ] (Y.F v₂))
        ((KreinGradedModule.gradeCLM (H := H₁) v₁) ⊗ₜ[ℝ] (Y.F v₂)) := by
    rw [TensorProduct.inner_tmul]
    exact mul_pos (real_inner_self_pos.mpr hG₁) (real_inner_self_pos.mpr hv₂)
  rw [hTmulZero, inner_zero_left] at hInnerPos
  exact lt_irrefl 0 hInnerPos

end FiniteProduct

end FiniteTensorProduct

end InfoGeometry.KK
