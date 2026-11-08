/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.LinearAlgebra.Matrix.Bilinear
import InfoGeometry.Algebra.FiniteProjectiveModuleGrothendieck
import InfoGeometry.QuantumContext.MarkovGroupInversePetzSupport

/-!
# Markov group-inverse splitting in projective-module K₀

This module transports the complementary idempotents of a finite Markov group
inverse to actual finitely generated projective modules. Its K₀ group is the
repository's projective-module `K₀(ℝ)`, formed from ranges in the column
observable module `ι → ℝ`. The operators are represented by full matrices;
this is not a claim about `K₀` of the noncommutative matrix algebra.
-/

noncomputable section

namespace InfoGeometry.QuantumContext.MarkovProjectiveK0Bridge

open InfoGeometry.Algebra.FiniteProjectiveModuleGrothendieck
open InfoGeometry.Canonical.HartwigSouriauFrameDrazin
open InfoGeometry.QuantumContext.MarkovDrazin

local instance : AddCommGroup (K0 ℝ) := by
  change AddCommGroup (Grothendieck (ProjectiveModuleClass ℝ))
  infer_instance

variable {ι : Type} [Fintype ι] [DecidableEq ι]

abbrev Observable := ι → ℝ

/-- The range idempotent induced by the Markov Laplacian and its group inverse. -/
def markovRangeEnd (P G : Matrix ι ι ℝ) : Module.End ℝ (Observable (ι := ι)) :=
  Matrix.toLin' (markovRangeIdempotent P G)

/-- The Markov Laplacian acting on column observables. -/
def markovLaplacianEnd (P : Matrix ι ι ℝ) : Module.End ℝ (Observable (ι := ι)) :=
  Matrix.toLin' (1 - P)

/-- The complementary stationary endomorphism. -/
def markovKernelEnd (P G : Matrix ι ι ℝ) : Module.End ℝ (Observable (ι := ι)) :=
  1 - markovRangeEnd P G

theorem markovRangeEnd_idempotent (P G : Matrix ι ι ℝ)
    (hG : IsGroupInverse (1 - P) G) :
    markovRangeEnd P G * markovRangeEnd P G = markovRangeEnd P G := by
  simpa [markovRangeEnd, Matrix.toLin'_mul, Module.End.mul_eq_comp] using
    congrArg (fun A : Matrix ι ι ℝ => Matrix.toLin' A)
      (markovRangeIdempotent_idempotent P G hG)

theorem markovKernelEnd_idempotent (P G : Matrix ι ι ℝ)
    (hG : IsGroupInverse (1 - P) G) :
    markovKernelEnd P G * markovKernelEnd P G = markovKernelEnd P G := by
  have he := markovRangeEnd_idempotent P G hG
  dsimp [markovKernelEnd]
  simp [sub_mul, mul_sub, he]

theorem markovRangeEnd_mul_kernelEnd (P G : Matrix ι ι ℝ)
    (hG : IsGroupInverse (1 - P) G) :
    markovRangeEnd P G * markovKernelEnd P G = 0 := by
  have he := markovRangeEnd_idempotent P G hG
  dsimp [markovKernelEnd]
  simp [mul_sub, he]

private theorem matrixGroupInverse_toLin
    (P G : Matrix ι ι ℝ) (hG : IsGroupInverse (1 - P) G) :
    IsGroupInverse (markovLaplacianEnd P) (Matrix.toLin' G) := by
  constructor
  · simpa [markovLaplacianEnd, Matrix.toLin'_mul, Module.End.mul_eq_comp] using
      congrArg (fun A : Matrix ι ι ℝ => Matrix.toLin' A) hG.1
  constructor
  · simpa [markovLaplacianEnd, Matrix.toLin'_mul, Module.End.mul_eq_comp] using
      congrArg (fun A : Matrix ι ι ℝ => Matrix.toLin' A) hG.2.1
  · simpa [markovLaplacianEnd, Matrix.toLin'_mul, Module.End.mul_eq_comp] using
      congrArg (fun A : Matrix ι ι ℝ => Matrix.toLin' A) hG.2.2

/-- A nonidentity transition matrix has a nonzero Laplacian action on column
observables. -/
theorem markovLaplacianEnd_ne_zero_of_matrix_ne_one
    (P : Matrix ι ι ℝ) (hP : P ≠ 1) : markovLaplacianEnd P ≠ 0 := by
  intro hzero
  have hmatrix : 1 - P = 0 := by
    apply Matrix.toLin'.injective
    simpa [markovLaplacianEnd] using hzero
  exact hP (sub_eq_zero.mp hmatrix).symm

/-- The first idempotent's range is exactly the range of the Markov
Laplacian on column observables. -/
theorem markovRangeEnd_range_eq_laplacian
    (P G : Matrix ι ι ℝ) (hG : IsGroupInverse (1 - P) G) :
    LinearMap.range (markovRangeEnd P G) = (markovLaplacianEnd P).range := by
  have hLift := matrixGroupInverse_toLin P G hG
  simpa [markovRangeEnd, markovRangeIdempotent, markovLaplacianEnd,
    Matrix.toLin'_mul, Module.End.mul_eq_comp] using
    InfoGeometry.QuantumContext.MarkovDrazin.groupInverse_regularProjector_range
      (markovLaplacianEnd P) (Matrix.toLin' G) hLift

/-- The complementary idempotent's range is exactly the Markov Laplacian
kernel on column observables. -/
theorem markovKernelEnd_range_eq_laplacian_kernel
    (P G : Matrix ι ι ℝ) (hG : IsGroupInverse (1 - P) G) :
    LinearMap.range (markovKernelEnd P G) = (markovLaplacianEnd P).ker := by
  have hLift := matrixGroupInverse_toLin P G hG
  have hComplement : markovKernelEnd P G =
      InfoGeometry.Canonical.Drazin.IsDrazinInverse.complementaryProjection
        (markovLaplacianEnd P) (Matrix.toLin' G) := by
    simp [markovKernelEnd, markovRangeEnd, markovRangeIdempotent,
      markovLaplacianEnd,
      InfoGeometry.Canonical.Drazin.IsDrazinInverse.complementaryProjection,
      InfoGeometry.Canonical.Drazin.IsDrazinInverse.projection,
      Matrix.toLin'_mul, Module.End.mul_eq_comp]
  rw [hComplement]
  simpa [InfoGeometry.Canonical.Drazin.IsDrazinInverse.drazinCore] using
    InfoGeometry.Canonical.Drazin.IsDrazinInverse.complementaryProjection_range_eq_drazinCore
      hLift.toDrazin

theorem markovKernelEnd_mul_rangeEnd (P G : Matrix ι ι ℝ)
    (hG : IsGroupInverse (1 - P) G) :
    markovKernelEnd P G * markovRangeEnd P G = 0 := by
  have he := markovRangeEnd_idempotent P G hG
  dsimp [markovKernelEnd]
  simp [sub_mul, he]

private def rangeInjection (e : Module.End ℝ (Observable (ι := ι))) :
    LinearMap.range e →ₗ[ℝ] Observable (ι := ι) :=
  (LinearMap.range e).subtype

private def rangeProjection (e : Module.End ℝ (Observable (ι := ι)))
    (_he : e * e = e) :
    Observable (ι := ι) →ₗ[ℝ] LinearMap.range e where
  toFun x := ⟨e x, ⟨x, rfl⟩⟩
  map_add' x y := by
    apply Subtype.ext
    simp
  map_smul' c x := by
    apply Subtype.ext
    simp

omit [Fintype ι] [DecidableEq ι] in
private theorem rangeProjection_subtype (e : Module.End ℝ (Observable (ι := ι)))
    (he : e * e = e) :
    (rangeProjection e he).comp (rangeInjection e) = LinearMap.id := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  have hx : e x.1 = x.1 := by
    obtain ⟨y, hy⟩ := x.2
    calc
      e x.1 = e (e y) := by rw [hy]
      _ = x.1 := by
        have hy' : e (e y) = e y := by
          have h := congrArg (fun f : Module.End ℝ (Observable (ι := ι)) => f y) he
          simpa [Module.End.mul_eq_comp] using h
        rw [hy']
        exact hy
  exact hx

omit [DecidableEq ι] in
private theorem range_is_projective (e : Module.End ℝ (Observable (ι := ι)))
    (he : e * e = e) : Module.Projective ℝ (LinearMap.range e) := by
  let i := rangeInjection e
  let r := rangeProjection e he
  have hri : r.comp i = LinearMap.id := rangeProjection_subtype e he
  exact @Module.Projective.of_split ℝ _ (LinearMap.range e) _ _
    (Observable (ι := ι)) _ _ Module.Projective.of_free i r hri

omit [DecidableEq ι] in
private theorem range_is_finite (e : Module.End ℝ (Observable (ι := ι))) :
    Module.Finite ℝ (LinearMap.range e) := by
  infer_instance

/-- A finite-projective package for the range of an idempotent endomorphism. -/
private def rangeProjectiveModule (e : Module.End ℝ (Observable (ι := ι)))
    (he : e * e = e) : FiniteProjectiveModule ℝ :=
  ⟨ModuleCat.of ℝ (LinearMap.range e), range_is_finite e,
    range_is_projective e he⟩

omit [Fintype ι] [DecidableEq ι] in
private theorem idempotent_range_fixes
    (e : Module.End ℝ (Observable (ι := ι))) (he : e * e = e)
    (x : LinearMap.range e) : e x.1 = x.1 := by
  obtain ⟨y, hy⟩ := x.2
  calc
    e x.1 = e (e y) := by rw [hy]
    _ = x.1 := by
      have h := congrArg (fun f : Module.End ℝ (Observable (ι := ι)) => f y) he
      have h' : e (e y) = e y := by
        simpa [Module.End.mul_eq_comp] using h
      rw [h']
      exact hy

omit [Fintype ι] [DecidableEq ι] in
private theorem orthogonal_range_annihilates
    (e f : Module.End ℝ (Observable (ι := ι))) (hef : e * f = 0)
    (x : LinearMap.range f) : e x.1 = 0 := by
  obtain ⟨y, hy⟩ := x.2
  calc
    e x.1 = e (f y) := by rw [hy]
    _ = 0 := by
      have h := congrArg (fun g : Module.End ℝ (Observable (ι := ι)) => g y) hef
      simpa [Module.End.mul_eq_comp] using h

/-- The pair of range projections is a linear equivalence with the observable
space; the inverse adds the two components. -/
private def splitRangesEquiv
    (e f : Module.End ℝ (Observable (ι := ι)))
    (he : e * e = e) (hf : f * f = f)
    (hef : e * f = 0) (hfe : f * e = 0)
    (hsum : e + f = 1) :
    Observable (ι := ι) ≃ₗ[ℝ] (LinearMap.range e × LinearMap.range f) where
  toFun x := (⟨e x, ⟨x, rfl⟩⟩, ⟨f x, ⟨x, rfl⟩⟩)
  invFun z := z.1.1 + z.2.1
  left_inv x := by
    have h := congrArg (fun g : Module.End ℝ (Observable (ι := ι)) => g x) hsum
    simpa using h
  right_inv z := by
    apply Prod.ext
    · apply Subtype.ext
      change e (z.1.1 + z.2.1) = z.1.1
      rw [map_add, idempotent_range_fixes e he z.1,
        orthogonal_range_annihilates e f hef z.2, add_zero]
    · apply Subtype.ext
      change f (z.1.1 + z.2.1) = z.2.1
      rw [map_add, orthogonal_range_annihilates f e hfe z.1,
        idempotent_range_fixes f hf z.2, zero_add]
  map_add' x y := by
    apply Prod.ext <;> apply Subtype.ext <;> simp
  map_smul' c x := by
    apply Prod.ext <;> apply Subtype.ext <;> simp

omit [DecidableEq ι] in
private theorem projectiveRangesClassAdd_eq_observable
    (e f : Module.End ℝ (Observable (ι := ι)))
    (he : e * e = e) (hf : f * f = f)
    (hef : e * f = 0) (hfe : f * e = 0)
    (hsum : e + f = 1) :
    Quotient.mk (moduleIsoSetoid ℝ) (directSum ℝ
        (rangeProjectiveModule e he) (rangeProjectiveModule f hf)) =
      Quotient.mk (moduleIsoSetoid ℝ)
        (⟨ModuleCat.of ℝ (Observable (ι := ι)), inferInstance,
          Module.Projective.of_free⟩ : FiniteProjectiveModule ℝ) := by
  apply Quotient.sound
  exact ⟨(splitRangesEquiv e f he hf hef hfe hsum).symm.toModuleIso⟩

/-- The complementary group-inverse idempotents sum to the class of the
observable module in the repository's actual projective-module `K₀(ℝ)`. -/
theorem markovProjectiveK0_split
    (P G : Matrix ι ι ℝ) (hG : IsGroupInverse (1 - P) G) :
    k0Class ℝ (rangeProjectiveModule
        (markovRangeEnd P G) (markovRangeEnd_idempotent P G hG)) +
      k0Class ℝ (rangeProjectiveModule
        (markovKernelEnd P G) (markovKernelEnd_idempotent P G hG)) =
      k0Class ℝ
        (⟨ModuleCat.of ℝ (Observable (ι := ι)), inferInstance,
          Module.Projective.of_free⟩ : FiniteProjectiveModule ℝ) := by
  let e := markovRangeEnd P G
  let f := markovKernelEnd P G
  let he := markovRangeEnd_idempotent P G hG
  let hf := markovKernelEnd_idempotent P G hG
  have hef : e * f = 0 := markovRangeEnd_mul_kernelEnd P G hG
  have hfe : f * e = 0 := markovKernelEnd_mul_rangeEnd P G hG
  have hsum : e + f = 1 := by dsimp [e, f, markovKernelEnd]; noncomm_ring
  have hclass := projectiveRangesClassAdd_eq_observable e f he hf hef hfe hsum
  let cE : ProjectiveModuleClass ℝ :=
    Quotient.mk (moduleIsoSetoid ℝ) (rangeProjectiveModule e he)
  let cF : ProjectiveModuleClass ℝ :=
    Quotient.mk (moduleIsoSetoid ℝ) (rangeProjectiveModule f hf)
  let cV : ProjectiveModuleClass ℝ :=
    Quotient.mk (moduleIsoSetoid ℝ)
      (⟨ModuleCat.of ℝ (Observable (ι := ι)), inferInstance,
        Module.Projective.of_free⟩ : FiniteProjectiveModule ℝ)
  have hclassAdd : cE + cF = cV := by
    change classAdd ℝ
      (Quotient.mk (moduleIsoSetoid ℝ) (rangeProjectiveModule e he))
      (Quotient.mk (moduleIsoSetoid ℝ) (rangeProjectiveModule f hf)) =
      Quotient.mk (moduleIsoSetoid ℝ)
        (⟨ModuleCat.of ℝ (Observable (ι := ι)), inferInstance,
          Module.Projective.of_free⟩ : FiniteProjectiveModule ℝ)
    unfold classAdd
    rw [Quotient.map₂_mk]
    exact hclass
  change grothendieckMap (ProjectiveModuleClass ℝ) cE +
      grothendieckMap (ProjectiveModuleClass ℝ) cF =
    grothendieckMap (ProjectiveModuleClass ℝ) cV
  calc
    _ = grothendieckMap (ProjectiveModuleClass ℝ) (cE + cF) :=
      ((grothendieckMap (ProjectiveModuleClass ℝ)).map_add cE cF).symm
    _ = grothendieckMap (ProjectiveModuleClass ℝ) cV :=
      congrArg (grothendieckMap (ProjectiveModuleClass ℝ)) hclassAdd

/-- Every nonidentity finite row-stochastic operator has a nonzero Laplacian
and a matrix group inverse whose range/kernel projective modules split the
actual projective-module `K₀(ℝ)` class of the column observable space. -/
theorem exists_nontrivial_rowStochastic_markovProjectiveK0_split
    [Nontrivial ι] (P : Matrix ι ι ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ ι) (hP_ne_one : P ≠ 1) :
    ∃ G : Matrix ι ι ℝ,
      ∃ hG : IsGroupInverse (1 - P) G,
        k0Class ℝ (rangeProjectiveModule
          (markovRangeEnd P G) (markovRangeEnd_idempotent P G hG)) +
          k0Class ℝ (rangeProjectiveModule
            (markovKernelEnd P G) (markovKernelEnd_idempotent P G hG)) =
          k0Class ℝ
            (⟨ModuleCat.of ℝ (Observable (ι := ι)), inferInstance,
              Module.Projective.of_free⟩ : FiniteProjectiveModule ℝ) ∧
        markovLaplacianEnd P ≠ 0 := by
  obtain ⟨G, hG⟩ := exists_stochastic_markovRangeIdempotent P hP
  exact ⟨G, hG, markovProjectiveK0_split P G hG,
    markovLaplacianEnd_ne_zero_of_matrix_ne_one P hP_ne_one⟩

end InfoGeometry.QuantumContext.MarkovProjectiveK0Bridge

end
