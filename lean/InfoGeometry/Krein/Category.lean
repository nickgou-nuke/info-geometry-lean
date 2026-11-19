/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.CategoryTheory.Category.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Krein.KreinSpace
import InfoGeometry.Krein.DoubledSpace
import InfoGeometry.Krein.Clifford
import InfoGeometry.Quantum.RealKCategory

/-!
# Category of Bundled Real Krein Spaces

This module defines the categorical structure for real Krein spaces:
- `RealKreinSpace`: A bundled object containing the carrier Hilbert space and its fundamental symmetry.
- `Category RealKreinSpace`: Morphisms are continuous linear maps preserving the Krein inner product.
- Honest boundary theorems showing `J² = +Id` alone does not give an intrinsic `K² = -Id`.
- `doubledToRealKVect` and `doubledToComplex`: Functorial doubling from `RealKreinSpace` into
  `RealKVect` and `ModuleCat ℂ`.
- `RealKreinGradedSpace`: Graded Krein spaces with anticommuting `(J, Γ)`, giving an intrinsic
  `K := Γ ∘ J` with `K² = -Id` and functors `toRealKVect`, `toComplex`, plus the
  `HilbertDoubled` isomorphism to `doubledToRealKVect`.
-/

universe u

open CategoryTheory
open scoped InnerProductSpace

namespace InfoGeometry.Krein

open InfoGeometry.Quantum.RealKCategory

/-- Bundled object for the category of real Krein spaces. -/
structure RealKreinSpace where
  H : Type u
  [instN : NormedAddCommGroup H]
  [instI : InnerProductSpace ℝ H]
  [instC : CompleteSpace H]
  [instK : KreinSpace H]

attribute [instance] RealKreinSpace.instN RealKreinSpace.instI RealKreinSpace.instC RealKreinSpace.instK

namespace RealKreinSpace

/-- Morphisms in the category of Krein spaces. -/
noncomputable def Hom (X Y : RealKreinSpace.{u}) := KreinHom X.H Y.H

lemma Hom.ext {X Y : RealKreinSpace.{u}} {f g : Hom X Y} (h : f.hom = g.hom) : f = g := by
  cases f
  cases g
  cases h
  rfl

noncomputable instance : Category RealKreinSpace.{u} where
  Hom X Y := Hom X Y
  id X :=
    { hom := ContinuousLinearMap.id ℝ X.H
      isometric := by intro u v; simp [KreinSpace.kreinInner_def] }
  comp {X Y Z} f g :=
    { hom := g.hom.comp f.hom
      isometric := fun u v => by
        rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, g.isometric, f.isometric] }

@[simp] lemma hom_id (X : RealKreinSpace.{u}) :
    (𝟙 X : X ⟶ X).hom = ContinuousLinearMap.id ℝ X.H := rfl

@[simp] lemma hom_comp {X Y Z : RealKreinSpace.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).hom = g.hom.comp f.hom := rfl

/-! ### Honest Boundary: `J² = +Id` Alone Does Not Yield `K² = -Id` -/

/-- On any nontrivial real Krein space, the fundamental symmetry squares to `+Id`, never `-Id`. -/
theorem jCLM_sq_ne_neg_id (H : Type*)
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [KreinSpace H]
    [Nontrivial H] :
    (KreinSpace.jCLM (H := H)).comp (KreinSpace.jCLM (H := H)) ≠
      -(ContinuousLinearMap.id ℝ H) := by
  intro h
  rcases exists_ne (0 : H) with ⟨x, hx⟩
  have h1 : (KreinSpace.jCLM (H := H)).comp (KreinSpace.jCLM (H := H)) x =
      ContinuousLinearMap.id ℝ H x := by
    rw [KreinSpace.jCLM_comp_self]
  have h2 : (KreinSpace.jCLM (H := H)).comp (KreinSpace.jCLM (H := H)) x =
      (-(ContinuousLinearMap.id ℝ H)) x :=
    congrArg (fun T : H →L[ℝ] H => T x) h
  have hneg : x = -x := by
    simpa using h1.symm.trans h2
  have htwo : (2 : ℝ) • x = 0 := by
    have hadd : x + x = 0 := eq_neg_iff_add_eq_zero.mp hneg
    simpa [two_smul] using hadd
  exact hx ((smul_eq_zero.mp htwo).resolve_left (by norm_num))

/-- The 1-dimensional real line `ℝ` (equipped with `instKreinSpaceOfHilbert`) admits no `RealKVect`
operator `K : ℝ →ₗ[ℝ] ℝ` satisfying `K² = -Id`. -/
theorem no_realKVect_on_real_line :
    ¬ ∃ K : ℝ →ₗ[ℝ] ℝ, K.comp K = -(LinearMap.id : ℝ →ₗ[ℝ] ℝ) := by
  rintro ⟨K, hK⟩
  have h1 : K (K 1) = -1 := by
    have hpt := congrArg (fun T : ℝ →ₗ[ℝ] ℝ => T 1) hK
    simpa using hpt
  have hlin : K (K 1) = K 1 * K 1 := by
    calc
      K (K 1) = K (K 1 • (1 : ℝ)) := by simp [smul_eq_mul]
      _ = K 1 • K 1 := K.map_smul (K 1) 1
      _ = K 1 * K 1 := smul_eq_mul _ _
  have hsq : K 1 * K 1 = -1 := hlin.symm.trans h1
  have hnonneg : 0 ≤ K 1 * K 1 := mul_self_nonneg (K 1)
  have hneg : K 1 * K 1 < 0 := by
    rw [hsq]
    norm_num
  exact absurd hneg (not_lt.mpr hnonneg)

/-! ### Functorial Doubling Bridge: `RealKreinSpace ⥤ RealKVect ⥤ ModuleCat ℂ` -/

/-- Componentwise continuous linear lift of a Krein morphism to `DoubledSpace`. -/
noncomputable def doubledMap {X Y : RealKreinSpace.{u}} (f : X ⟶ Y) :
    DoubledSpace X.H →L[ℝ] DoubledSpace Y.H where
  toFun u := WithLp.toLp (2 : ENNReal) (f.hom (WithLp.fst u), f.hom (WithLp.snd u))
  map_add' u v := by
    simp only [WithLp.add_fst, WithLp.add_snd, map_add]
    simpa using (WithLp.toLp_add (p := (2 : ENNReal))
      (x := (f.hom (WithLp.fst u), f.hom (WithLp.snd u)))
      (y := (f.hom (WithLp.fst v), f.hom (WithLp.snd v))))
  map_smul' c u := by
    simp only [WithLp.smul_fst, WithLp.smul_snd, map_smul, RingHom.id_apply]
    simpa using (WithLp.toLp_smul (p := (2 : ENNReal)) (c := c)
      (x := (f.hom (WithLp.fst u), f.hom (WithLp.snd u))))
  cont := by
    exact (WithLp.prod_continuous_toLp (p := (2 : ENNReal)) (α := Y.H) (β := Y.H)).comp
      ((f.hom.continuous.comp
        (WithLp.continuous_fst (p := (2 : ENNReal)) (α := X.H) (β := X.H))).prodMk
       (f.hom.continuous.comp
        (WithLp.continuous_snd (p := (2 : ENNReal)) (α := X.H) (β := X.H))))

@[simp] lemma doubledMap_apply {X Y : RealKreinSpace.{u}} (f : X ⟶ Y) (u : DoubledSpace X.H) :
    doubledMap f u = WithLp.toLp (2 : ENNReal) (f.hom (WithLp.fst u), f.hom (WithLp.snd u)) := rfl

lemma doubledMap_id (X : RealKreinSpace.{u}) :
    doubledMap (𝟙 X) = ContinuousLinearMap.id ℝ (DoubledSpace X.H) := by
  apply ContinuousLinearMap.ext
  intro u
  apply DoubledSpace.ext <;> simp

lemma doubledMap_comp {X Y Z : RealKreinSpace.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    doubledMap (f ≫ g) = (doubledMap g).comp (doubledMap f) := by
  apply ContinuousLinearMap.ext
  intro u
  apply DoubledSpace.ext <;> simp

lemma doubledMap_comp_complex_i {X Y : RealKreinSpace.{u}} (f : X ⟶ Y) :
    (doubledMap f).comp (complex_i (E := X.H)) =
      (complex_i (E := Y.H)).comp (doubledMap f) := by
  apply ContinuousLinearMap.ext
  intro u
  apply DoubledSpace.ext <;> simp [complex_i_apply]

end RealKreinSpace

/-- Doubling functor sending a real Krein space `X` to `(DoubledSpace X.H, complex_i)` in `RealKVect`. -/
noncomputable def doubledToRealKVect : RealKreinSpace.{u} ⥤ RealKVect.{u} where
  obj X :=
    { V := DoubledSpace X.H
      K := (complex_i (E := X.H)).toLinearMap
      K_sq := congrArg ContinuousLinearMap.toLinearMap (complex_i_sq X.H) }
  map {X Y} f :=
    { hom := (RealKreinSpace.doubledMap f).toLinearMap
      comm := congrArg ContinuousLinearMap.toLinearMap
        (RealKreinSpace.doubledMap_comp_complex_i f) }
  map_id X := by
    apply RealKVect.Hom.ext
    exact congrArg ContinuousLinearMap.toLinearMap (RealKreinSpace.doubledMap_id X)
  map_comp {X Y Z} f g := by
    apply RealKVect.Hom.ext
    exact congrArg ContinuousLinearMap.toLinearMap (RealKreinSpace.doubledMap_comp f g)

/-- Composite functor from `RealKreinSpace` through doubling into `ModuleCat ℂ`. -/
noncomputable def doubledToComplex : RealKreinSpace.{u} ⥤ ModuleCat.{u} ℂ :=
  doubledToRealKVect ⋙ RealKVect.realKToComplex

/-! ### Intrinsic Graded Krein Category: `RealKreinGradedSpace ⥤ RealKVect` -/

/-- A real Krein space equipped with an anticommuting grading involution `Γ` (`J Γ = -Γ J`),
yielding an intrinsic square-minus-one axis `K := Γ ∘ J`. -/
structure RealKreinGradedSpace extends RealKreinSpace.{u} where
  [instG : KreinGradedModule H]
  J_grade_anticomm :
    (KreinSpace.jCLM (H := H)).comp (KreinGradedModule.gradeCLM (H := H)) =
      -((KreinGradedModule.gradeCLM (H := H)).comp (KreinSpace.jCLM (H := H)))

attribute [instance] RealKreinGradedSpace.instG

namespace RealKreinGradedSpace

/-- Morphisms in `RealKreinGradedSpace`: Krein isometries intertwining both `J` and `Γ`. -/
structure Hom (X Y : RealKreinGradedSpace.{u}) extends KreinHom X.H Y.H where
  comm_J : hom.comp (KreinSpace.jCLM (H := X.H)) =
    (KreinSpace.jCLM (H := Y.H)).comp hom
  comm_grade : hom.comp (KreinGradedModule.gradeCLM (H := X.H)) =
    (KreinGradedModule.gradeCLM (H := Y.H)).comp hom

lemma Hom.ext {X Y : RealKreinGradedSpace.{u}} {f g : Hom X Y} (h : f.hom = g.hom) :
    f = g := by
  cases f with
  | mk kf hJ hG =>
    cases g with
    | mk kg hJ' hG' =>
      cases kf
      cases kg
      dsimp at h
      cases h
      rfl

noncomputable instance : Category RealKreinGradedSpace.{u} where
  Hom X Y := Hom X Y
  id X :=
    { hom := ContinuousLinearMap.id ℝ X.H
      isometric := by intro u v; simp [KreinSpace.kreinInner_def]
      comm_J := by ext x; rfl
      comm_grade := by ext x; rfl }
  comp {X Y Z} f g :=
    { hom := g.hom.comp f.hom
      isometric := fun u v => by
        rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, g.isometric, f.isometric]
      comm_J := by
        rw [ContinuousLinearMap.comp_assoc, f.comm_J, ← ContinuousLinearMap.comp_assoc,
          g.comm_J, ContinuousLinearMap.comp_assoc]
      comm_grade := by
        rw [ContinuousLinearMap.comp_assoc, f.comm_grade, ← ContinuousLinearMap.comp_assoc,
          g.comm_grade, ContinuousLinearMap.comp_assoc] }

@[simp] lemma hom_id (X : RealKreinGradedSpace.{u}) :
    (𝟙 X : X ⟶ X).hom = ContinuousLinearMap.id ℝ X.H := rfl

@[simp] lemma hom_comp {X Y Z : RealKreinGradedSpace.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).hom = g.hom.comp f.hom := rfl

/-- The intrinsic complex axis `K := Γ ∘ J` on a graded Krein space with `J Γ = -Γ J`. -/
noncomputable def K (X : RealKreinGradedSpace.{u}) : X.H →L[ℝ] X.H :=
  (KreinGradedModule.gradeCLM (H := X.H)).comp (KreinSpace.jCLM (H := X.H))

lemma K_sq (X : RealKreinGradedSpace.{u}) :
    (X.K).comp X.K = -(ContinuousLinearMap.id ℝ X.H) := by
  unfold K
  calc
    ((KreinGradedModule.gradeCLM (H := X.H)).comp (KreinSpace.jCLM (H := X.H))).comp
        ((KreinGradedModule.gradeCLM (H := X.H)).comp (KreinSpace.jCLM (H := X.H)))
        = (KreinGradedModule.gradeCLM (H := X.H)).comp
            (((KreinSpace.jCLM (H := X.H)).comp (KreinGradedModule.gradeCLM (H := X.H))).comp
              (KreinSpace.jCLM (H := X.H))) := by
          simp only [ContinuousLinearMap.comp_assoc]
    _ = (KreinGradedModule.gradeCLM (H := X.H)).comp
          ((-((KreinGradedModule.gradeCLM (H := X.H)).comp (KreinSpace.jCLM (H := X.H)))).comp
            (KreinSpace.jCLM (H := X.H))) := by
          rw [X.J_grade_anticomm]
    _ = -(((KreinGradedModule.gradeCLM (H := X.H)).comp (KreinGradedModule.gradeCLM (H := X.H))).comp
          ((KreinSpace.jCLM (H := X.H)).comp (KreinSpace.jCLM (H := X.H)))) := by
          simp only [ContinuousLinearMap.neg_comp, ContinuousLinearMap.comp_neg,
            ContinuousLinearMap.comp_assoc]
    _ = -(ContinuousLinearMap.id ℝ X.H) := by
          rw [KreinGradedModule.gradeCLM_comp_self, KreinSpace.jCLM_comp_self,
            ContinuousLinearMap.id_comp]

/-- Forgetful functor from `RealKreinGradedSpace` to `RealKreinSpace`. -/
noncomputable def forgetToRealKreinSpace : RealKreinGradedSpace.{u} ⥤ RealKreinSpace.{u} where
  obj X := X.toRealKreinSpace
  map {_ _} f := f.toKreinHom
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Canonical functor `RealKreinGradedSpace ⥤ RealKVect` induced by `K := Γ ∘ J`. -/
noncomputable def toRealKVect : RealKreinGradedSpace.{u} ⥤ RealKVect.{u} where
  obj X :=
    { V := X.H
      K := X.K.toLinearMap
      K_sq := congrArg ContinuousLinearMap.toLinearMap (K_sq X) }
  map {X Y} f :=
    { hom := f.hom.toLinearMap
      comm := congrArg ContinuousLinearMap.toLinearMap
        (show f.hom.comp X.K = Y.K.comp f.hom from by
          unfold RealKreinGradedSpace.K
          rw [← ContinuousLinearMap.comp_assoc, f.comm_grade, ContinuousLinearMap.comp_assoc,
            f.comm_J, ← ContinuousLinearMap.comp_assoc]) }
  map_id _ := by
    apply RealKVect.Hom.ext
    rfl
  map_comp _ _ := by
    apply RealKVect.Hom.ext
    rfl

/-- Composite functor from `RealKreinGradedSpace` into `ModuleCat ℂ`. -/
noncomputable def toComplex : RealKreinGradedSpace.{u} ⥤ ModuleCat.{u} ℂ :=
  toRealKVect ⋙ RealKVect.realKToComplex

/-- Canonical `HilbertDoubled X.H` object in `RealKreinGradedSpace`. -/
noncomputable def hilbertDoubledGraded (X : RealKreinSpace.{u}) : RealKreinGradedSpace.{u} where
  H := HilbertDoubled X.H
  instN := inferInstance
  instI := inferInstance
  instC := inferInstance
  instK := inferInstance
  instG := instKreinGradedModuleHilbertDoubled (E := X.H)
  J_grade_anticomm := by
    rw [gradeCLM_eq_hilbertSwapCLM]
    exact (neg_eq_iff_eq_neg.mpr (hilbertSwap_comp_jCLM (E := X.H))).symm

/-- Natural `RealKVect` isomorphism identifying `toRealKVect (hilbertDoubledGraded X)` with
`doubledToRealKVect X`. -/
noncomputable def hilbertDoubledToRealKVectIso (X : RealKreinSpace.{u}) :
    toRealKVect.obj (hilbertDoubledGraded X) ≅ doubledToRealKVect.obj X where
  hom :=
    { hom := (HilbertDoubled.toDoubledContinuousLinearEquiv (E := X.H)).toContinuousLinearMap.toLinearMap
      comm := by
        apply LinearMap.ext
        intro u
        dsimp [toRealKVect, hilbertDoubledGraded, doubledToRealKVect, RealKreinGradedSpace.K]
        exact toDoubled_hilbertComplexI_apply (E := X.H) u }
  inv :=
    { hom := (HilbertDoubled.ofDoubledContinuousLinearEquiv (E := X.H)).toContinuousLinearMap.toLinearMap
      comm := by
        apply LinearMap.ext
        intro u
        apply (HilbertDoubled.toDoubledContinuousLinearEquiv (E := X.H)).injective
        dsimp [toRealKVect, hilbertDoubledGraded, doubledToRealKVect, RealKreinGradedSpace.K]
        exact (toDoubled_hilbertComplexI_apply (E := X.H)
          (HilbertDoubled.ofDoubledContinuousLinearEquiv (E := X.H) u)).symm }
  hom_inv_id := by
    apply RealKVect.Hom.ext
    apply LinearMap.ext
    intro u
    rfl
  inv_hom_id := by
    apply RealKVect.Hom.ext
    apply LinearMap.ext
    intro u
    rfl

end RealKreinGradedSpace

end InfoGeometry.Krein
