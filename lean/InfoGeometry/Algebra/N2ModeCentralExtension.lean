import InfoGeometry.External.Virasoro.CentralExtension
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.External.Virasoro.HeisenbergAlgebra

/-!
# N=2 mode central extension

External-Virasoro-style algebraic pipeline for the central part of an
infinite-mode N=2 closure:

```text
mode labels → finitely supported abelian mode algebra → basis generators
→ explicit alternating 2-cocycle → `LieTwoCocycle.CentralExtension`
→ generator bracket theorem → central-extension readback
```

This is an algebraic direct-sum/cocycle construction, not an analytic limit or
Sugawara representation theorem.
-/

namespace InfoGeometry.Algebra.N2ModeCentralExtension

open Module
open VirasoroProject

universe u

/-- Basis labels for the algebraic N=2 mode skeleton. -/
inductive N2ModeLabel (ι : Type u) : Type u
  | q : ι → N2ModeLabel ι
  | r : ι → N2ModeLabel ι
  | h : ι → N2ModeLabel ι
  deriving DecidableEq

/-- The finitely supported N=2 mode base algebra. -/
abbrev N2ModeBase (ι : Type u) (𝕜 : Type u) [CommRing 𝕜] :=
  AbelianLieAlgebraOn (N2ModeLabel ι) 𝕜

namespace N2ModeBase

variable {ι : Type u} (𝕜 : Type u) [CommRing 𝕜]

/-- The `Qᵢ` basis generator in the base direct-sum algebra. -/
noncomputable def qgen (i : ι) : N2ModeBase ι 𝕜 :=
  AbelianLieAlgebraOn.jgen 𝕜 (N2ModeLabel.q i)

/-- The `Rᵢ` basis generator in the base direct-sum algebra. -/
noncomputable def rgen (i : ι) : N2ModeBase ι 𝕜 :=
  AbelianLieAlgebraOn.jgen 𝕜 (N2ModeLabel.r i)

/-- The structural even `Hᵢ` basis generator in the base direct-sum algebra. -/
noncomputable def hgen (i : ι) : N2ModeBase ι 𝕜 :=
  AbelianLieAlgebraOn.jgen 𝕜 (N2ModeLabel.h i)

@[simp] theorem lie_qgen_rgen [Field 𝕜] (i j : ι) :
    ⁅qgen 𝕜 i, rgen 𝕜 j⁆ = 0 := by
  rfl

end N2ModeBase

namespace N2ModeCocycle

variable {ι : Type u} [DecidableEq ι]
variable (𝕜 : Type u) [Field 𝕜]

/-- The alternating N=2 central cocycle on basis labels. -/
def labelCocycle : N2ModeLabel ι → N2ModeLabel ι → 𝕜
  | N2ModeLabel.q i, N2ModeLabel.r j => if i = j then 1 else 0
  | N2ModeLabel.r i, N2ModeLabel.q j => if i = j then -1 else 0
  | _, _ => 0

@[simp] theorem labelCocycle_q_r (i j : ι) :
    labelCocycle 𝕜 (N2ModeLabel.q i) (N2ModeLabel.r j) =
      if i = j then 1 else 0 := rfl

@[simp] theorem labelCocycle_r_q (i j : ι) :
    labelCocycle 𝕜 (N2ModeLabel.r i) (N2ModeLabel.q j) =
      if i = j then -1 else 0 := rfl

@[simp] theorem labelCocycle_self (a : N2ModeLabel ι) :
    labelCocycle 𝕜 a a = 0 := by
  cases a <;> simp [labelCocycle]

/-- The label cocycle is skew. -/
theorem labelCocycle_eq_neg_flip :
    labelCocycle 𝕜 = fun a b : N2ModeLabel ι => - labelCocycle 𝕜 b a := by
  funext a b
  cases a with
  | q i =>
      cases b with
      | q j => simp [labelCocycle]
      | r j =>
          by_cases h : i = j
          · simp [labelCocycle, h]
          · simp [labelCocycle, h, Ne.symm h]
      | h j => simp [labelCocycle]
  | r i =>
      cases b with
      | q j =>
          by_cases h : i = j
          · simp [labelCocycle, h]
          · simp [labelCocycle, h, Ne.symm h]
      | r j => simp [labelCocycle]
      | h j => simp [labelCocycle]
  | h i =>
      cases b <;> simp [labelCocycle]

/-- Bilinear extension of the N=2 label cocycle to the finite-support mode algebra. -/
noncomputable def bilin :
    N2ModeBase ι 𝕜 →ₗ[𝕜] N2ModeBase ι 𝕜 →ₗ[𝕜] 𝕜 :=
  (AbelianLieAlgebraOn.jgen (ι := N2ModeLabel ι) 𝕜).constr 𝕜 <| fun a =>
    (AbelianLieAlgebraOn.jgen (ι := N2ModeLabel ι) 𝕜).constr 𝕜 <| fun b => labelCocycle 𝕜 a b

@[simp] theorem bilin_apply_jgen_jgen (a b : N2ModeLabel ι) :
    bilin 𝕜
      (AbelianLieAlgebraOn.jgen (ι := N2ModeLabel ι) 𝕜 a)
      (AbelianLieAlgebraOn.jgen (ι := N2ModeLabel ι) 𝕜 b) =
      labelCocycle 𝕜 a b := by
  simp [bilin]

/-- Skewness of the bilinear N=2 cocycle. -/
theorem bilin_eq_neg_flip :
    (bilin (ι := ι) 𝕜 :
      N2ModeBase ι 𝕜 →ₗ[𝕜] N2ModeBase ι 𝕜 →ₗ[𝕜] 𝕜) =
        -(bilin (ι := ι) 𝕜).flip := by
  apply LinearMap.ext_basis
    (AbelianLieAlgebraOn.jgen (ι := N2ModeLabel ι) 𝕜)
    (AbelianLieAlgebraOn.jgen (ι := N2ModeLabel ι) 𝕜)
  intro a b
  calc
    ((bilin 𝕜) ((AbelianLieAlgebraOn.jgen 𝕜) a))
        ((AbelianLieAlgebraOn.jgen 𝕜) b)
        = labelCocycle 𝕜 a b := by
          simp [bilin]
    _ = - labelCocycle 𝕜 b a := by
          exact congrFun (congrFun (labelCocycle_eq_neg_flip (ι := ι) 𝕜) a) b
    _ = ((-(bilin 𝕜).flip) ((AbelianLieAlgebraOn.jgen 𝕜) a))
        ((AbelianLieAlgebraOn.jgen 𝕜) b) := by
          simp [bilin]

variable [CharZero 𝕜]

/-- The N=2 Lie-algebra 2-cocycle defining the central extension. -/
noncomputable def cocycle : LieTwoCocycle 𝕜 (N2ModeBase ι 𝕜) 𝕜 where
  toBilin := bilin 𝕜
  self' X := by
    apply self_eq_neg.mp
    simpa only [LinearMap.neg_apply, LinearMap.coe_mk, AddHom.coe_mk]
      using LinearMap.congr_fun₂ (bilin_eq_neg_flip 𝕜) X X
  leibniz' X Y Z := by
    simp only [AbelianLieAlgebraOn.lie_def, map_zero, LinearMap.zero_apply,
      (lie_skew X Z).symm, neg_zero, add_zero]

@[simp] theorem cocycle_qgen_rgen (i j : ι) :
    cocycle 𝕜 (N2ModeBase.qgen 𝕜 i) (N2ModeBase.rgen 𝕜 j) =
      if i = j then 1 else 0 := by
  change bilin 𝕜 (N2ModeBase.qgen 𝕜 i) (N2ModeBase.rgen 𝕜 j) =
    if i = j then 1 else 0
  simp [N2ModeBase.qgen, N2ModeBase.rgen]

@[simp] theorem cocycle_rgen_qgen (i j : ι) :
    cocycle 𝕜 (N2ModeBase.rgen 𝕜 i) (N2ModeBase.qgen 𝕜 j) =
      if i = j then -1 else 0 := by
  change bilin 𝕜 (N2ModeBase.rgen 𝕜 i) (N2ModeBase.qgen 𝕜 j) =
    if i = j then -1 else 0
  simp [N2ModeBase.rgen, N2ModeBase.qgen]

@[simp] theorem cocycle_hgen_qgen (i j : ι) :
    cocycle 𝕜 (N2ModeBase.hgen 𝕜 i) (N2ModeBase.qgen 𝕜 j) = 0 := by
  change bilin 𝕜 (N2ModeBase.hgen 𝕜 i) (N2ModeBase.qgen 𝕜 j) = 0
  simp [N2ModeBase.hgen, N2ModeBase.qgen, bilin, labelCocycle]

end N2ModeCocycle

variable {ι : Type u} [DecidableEq ι]
variable (𝕜 : Type u) [Field 𝕜] [CharZero 𝕜]

/-- The N=2 central extension of the finitely supported mode base. -/
abbrev N2CentralExt (ι : Type u) [DecidableEq ι] (𝕜 : Type u) [Field 𝕜] [CharZero 𝕜] :=
  (N2ModeCocycle.cocycle (ι := ι) 𝕜).CentralExtension

namespace N2CentralExt

/-- Lift a base element to the central extension with zero central coordinate. -/
noncomputable def ofBase (X : N2ModeBase ι 𝕜) : N2CentralExt ι 𝕜 :=
  ⟨X, 0⟩

/-- The central generator. -/
noncomputable def zgen : N2CentralExt ι 𝕜 :=
  ⟨0, 1⟩

/-- The central generator, named in the Virasoro style. -/
noncomputable def cgen : N2CentralExt ι 𝕜 :=
  zgen 𝕜

/-- Lifted `Qᵢ` generator. -/
noncomputable def qgen (i : ι) : N2CentralExt ι 𝕜 :=
  ofBase 𝕜 (N2ModeBase.qgen 𝕜 i)

/-- Lifted `Rᵢ` generator. -/
noncomputable def rgen (i : ι) : N2CentralExt ι 𝕜 :=
  ofBase 𝕜 (N2ModeBase.rgen 𝕜 i)

/-- Lifted structural even `Hᵢ` generator. -/
noncomputable def hgen (i : ι) : N2CentralExt ι 𝕜 :=
  ofBase 𝕜 (N2ModeBase.hgen 𝕜 i)

@[simp] theorem zgen_eq : zgen (ι := ι) 𝕜 = ⟨0, 1⟩ := rfl
@[simp] theorem cgen_eq : cgen (ι := ι) 𝕜 = ⟨0, 1⟩ := rfl
@[simp] theorem qgen_eq (i : ι) : qgen 𝕜 i = ⟨N2ModeBase.qgen 𝕜 i, 0⟩ := rfl
@[simp] theorem rgen_eq (i : ι) : rgen 𝕜 i = ⟨N2ModeBase.rgen 𝕜 i, 0⟩ := rfl
@[simp] theorem hgen_eq (i : ι) : hgen 𝕜 i = ⟨N2ModeBase.hgen 𝕜 i, 0⟩ := rfl

/-- The central generator commutes on the left. -/
@[simp] theorem zgen_lie (X : N2CentralExt ι 𝕜) :
    ⁅zgen (ι := ι) 𝕜, X⁆ = 0 := by
  ext <;> simp [zgen, LieTwoCocycle.CentralExtension.lie_def]

/-- The central generator commutes on the right. -/
@[simp] theorem lie_zgen (X : N2CentralExt ι 𝕜) :
    ⁅X, zgen (ι := ι) 𝕜⁆ = 0 := by
  ext <;> simp [zgen, LieTwoCocycle.CentralExtension.lie_def]

/-- The Virasoro-named central generator commutes on the left. -/
@[simp] theorem cgen_lie (X : N2CentralExt ι 𝕜) :
    ⁅cgen (ι := ι) 𝕜, X⁆ = 0 := by
  simpa [cgen] using zgen_lie (ι := ι) (𝕜 := 𝕜) X

/-- The Virasoro-named central generator commutes on the right. -/
@[simp] theorem lie_cgen (X : N2CentralExt ι 𝕜) :
    ⁅X, cgen (ι := ι) 𝕜⁆ = 0 := by
  simpa [cgen] using lie_zgen (ι := ι) (𝕜 := 𝕜) X

/-- Generator bracket: the `Qᵢ,Rⱼ` bracket is the resonant central mode. -/
@[simp] theorem qgen_lie_rgen (i j : ι) :
    ⁅qgen 𝕜 i, rgen 𝕜 j⁆ =
      if i = j then zgen (ι := ι) 𝕜 else 0 := by
  by_cases h : i = j
  · subst h
    ext <;> simp [qgen, rgen, zgen, ofBase, LieTwoCocycle.CentralExtension.lie_def]
  · ext <;> simp [qgen, rgen, ofBase, LieTwoCocycle.CentralExtension.lie_def, h]

/-- Central-extension readback for arbitrary finite-support mode combinations. -/
theorem bracket_readback (X Y : N2CentralExt ι 𝕜) :
    ⁅X, Y⁆ =
      ⟨⁅X.fst, Y.fst⁆,
        N2ModeCocycle.cocycle (ι := ι) 𝕜 X.fst Y.fst⟩ := by
  rfl

/-- The central component of a bracket is exactly the N=2 cocycle. -/
theorem bracket_central_component_eq_cocycle
    (X Y : N2CentralExt ι 𝕜) :
    ⁅X, Y⁆.snd =
      N2ModeCocycle.cocycle (ι := ι) 𝕜 X.fst Y.fst := by
  rfl

end N2CentralExt

end InfoGeometry.Algebra.N2ModeCentralExtension
