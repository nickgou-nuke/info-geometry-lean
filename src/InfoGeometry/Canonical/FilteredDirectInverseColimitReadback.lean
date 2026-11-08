/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Canonical.FilteredDirectInverseColimit
import InfoGeometry.Categorical.Holonomy

/-!
# Projective-Limit Dual Readback of Filtered Direct Colimits in `ModuleCat`

This module formalizes the exact categorical duality between filtered direct colimits of
`R`-modules and projective inverse limits of stage dual modules `A i →ₗ[R] R` over `Iᵒᵖ`:
- `IsDualInverseFamily`: contravariant compatibility of stage linear functionals;
- `dualModuleDiagram : Opposite I ⥤ ModuleCat.{u} R`;
- `projectiveLimitEquivDualInverseFamily`: equivalence between the categorical projective limit
  `limit (dualModuleDiagram sys)` and compatible dual families;
- `dualInverseFamilyEquivColimitFunctional`: equivalence between compatible dual families and
  linear functionals on `colimit (Native.moduleDiagram sys)`;
- `projectiveLimitDualColimitFunctionalEquiv`: composite equivalence
  `limit (dualModuleDiagram sys) ≃ (colimit (Native.moduleDiagram sys) →ₗ[R] R)`.

### Audit Classification (BUCKET 1 / BUCKET 2 / BUCKET 3)
- **BUCKET 1 (Genuine Constructive Theorems)**:
  - `dualInverseTransition_comp_cocone`, `dualInverseFamilyCocone`
  - `dualModuleDiagram`, `dualInverseFamilyToProjectiveCone`,
    `dualInverseFamilyToProjectiveLimit`, `dualInverseFamilyToProjectiveLimit_stage`
  - `projectiveLimitToDualInverseFamily`, `projectiveLimitEquivDualInverseFamily`
  - `dualInverseFamilyColimitMap`, `dualInverseFamilyColimitMap_stage`,
    `dualInverseFamilyColimitMap_unique`
  - `colimitFunctionalStageFamily`, `colimitFunctionalStageFamily_isDualInverseFamily`,
    `dualInverseFamilyEquivColimitFunctional`, `dualInverseFamilyEquivColimitFunctional_apply_stage`,
    `dualInverseFamily_projective_inductive_stage_agree`,
    `projectiveLimitDualColimitFunctionalEquiv`, `projectiveLimitDualColimitFunctionalEquiv_stage`
- **BUCKET 2 (Honest Numeric/Finite Certificates)**: None (all results are polymorphic over `R` and `I`).
- **BUCKET 3 (Eliminated Debt)**: `0` `sorry`, `0` `admit`, `0` wrapper structures.
-/

noncomputable section

universe u

namespace FilteredColimit.InductiveCocone

open CategoryTheory CategoryTheory.Limits

variable {R : Type u} [CommRing R]
variable {I : Type u} [Preorder I]
variable {A : I → Type u} [∀ i, AddCommGroup (A i)] [∀ i, Module R (A i)]
variable {sys : DirectInductiveSystem R I A}
variable {A_inf : Type u} [AddCommGroup A_inf] [Module R A_inf]
variable (cocone : InductiveCocone R sys A_inf)

/-- A functional on the cocone target restricts to a compatible inverse family
of stage functionals. -/
theorem dualInverseTransition_comp_cocone
    (phi_inf : A_inf →ₗ[R] R) {i j : I} (hij : i ≤ j) :
    dualInverseTransition sys hij (phi_inf.comp (cocone.psi j)) =
      phi_inf.comp (cocone.psi i) := by
  ext x
  change phi_inf (cocone.psi j (sys.f hij x)) = phi_inf (cocone.psi i x)
  rw [cocone.cocone_eval_comm hij x]

/-- The compatibility predicate for a family of functionals on the stages.
Such a family is an element of the inverse system dual to `sys`. -/
abbrev IsDualInverseFamily
    (phi : ∀ i : I, A i →ₗ[R] R) : Prop :=
  ∀ {i j : I} (hij : i ≤ j),
    dualInverseTransition sys hij (phi j) = phi i

/-- A compatible inverse family of stage functionals is a linear cocone over
the original direct system. -/
def dualInverseFamilyCocone
    (phi : ∀ i : I, A i →ₗ[R] R)
    (hphi : IsDualInverseFamily (sys := sys) phi) :
    InductiveCocone R sys R :=
  InductiveCocone.mk phi (by
    intro i j hij
    ext x
    change phi j (sys.f hij x) = phi i x
    exact LinearMap.congr_fun (hphi hij) x)

/-- The inverse system of dual stage modules, promoted to a categorical
diagram on the opposite index category. -/
abbrev dualModuleDiagram (sys : DirectInductiveSystem R I A) :
    Opposite I ⥤ ModuleCat.{u} R where
  obj i := ModuleCat.of R (A i.unop →ₗ[R] R)
  map f := ModuleCat.ofHom (dualInverseTransition sys (leOfHom f.unop))
  map_id i := by
    ext phi x
    exact congrArg phi (LinearMap.congr_fun (sys.f_id i.unop) x)
  map_comp f g := by
    ext phi x
    exact LinearMap.congr_fun
      (dual_inverse_comp sys (leOfHom g.unop) (leOfHom f.unop) phi).symm x

/-- A compatible inverse family is a categorical cone over `dualModuleDiagram`
with vertex the scalar module. -/
abbrev dualInverseFamilyToProjectiveCone
    (phi : ∀ i : I, A i →ₗ[R] R)
    (hphi : IsDualInverseFamily (sys := sys) phi) :
    CategoryTheory.Limits.Cone (dualModuleDiagram sys) where
  pt := ModuleCat.of R R
  π :=
    { app := fun i => ModuleCat.ofHom
        (LinearMap.smulRight (1 : R →ₗ[R] R) (phi i.unop))
      naturality := by
        intro i j f
        ext x
        simpa [dualModuleDiagram, dualInverseTransition] using
          (LinearMap.congr_fun (hphi (leOfHom f.unop)) x).symm }

/-- The categorical projective limit receives the universal map from a
compatible dual family. -/
noncomputable def dualInverseFamilyToProjectiveLimit
    (phi : ∀ i : I, A i →ₗ[R] R)
    (hphi : IsDualInverseFamily (sys := sys) phi) :
    ModuleCat.of R R ⟶ CategoryTheory.Limits.limit
      (dualModuleDiagram sys) :=
  CategoryTheory.Limits.limit.lift (dualModuleDiagram sys)
    (dualInverseFamilyToProjectiveCone (sys := sys) phi hphi)

/-- Projection of the lifted inverse family recovers its stage functional
after evaluation at the scalar unit. -/
@[simp] theorem dualInverseFamilyToProjectiveLimit_stage
    (phi : ∀ i : I, A i →ₗ[R] R)
    (hphi : IsDualInverseFamily (sys := sys) phi) (i : I) (x : A i) :
    ((dualInverseFamilyToProjectiveLimit (sys := sys) phi hphi ≫
      CategoryTheory.Limits.limit.π (dualModuleDiagram sys)
        (Opposite.op i)).hom (1 : R)) x = phi i x := by
  have h := CategoryTheory.Limits.limit.lift_π
    (dualInverseFamilyToProjectiveCone (sys := sys) phi hphi) (Opposite.op i)
  have h1 :
      ((dualInverseFamilyToProjectiveLimit (sys := sys) phi hphi ≫
        CategoryTheory.Limits.limit.π (dualModuleDiagram sys)
          (Opposite.op i)).hom (1 : R)) x =
        ((1 : R) • phi i) x :=
    congrArg (fun f : ModuleCat.of R R ⟶
      (dualModuleDiagram sys).obj (Opposite.op i) =>
        (f.hom (1 : R)) x) h
  exact h1.trans (one_smul R (phi i x))

/-- Read a point of the categorical projective limit as its compatible family
of stage functionals. -/
def projectiveLimitToDualInverseFamily
    (z : ((CategoryTheory.Limits.limit (dualModuleDiagram sys) : ModuleCat R) : Type u)) :
    {phi : ∀ i : I, A i →ₗ[R] R //
      IsDualInverseFamily (sys := sys) phi} := by
  refine ⟨fun i => (CategoryTheory.Limits.limit.π
    (dualModuleDiagram sys) (Opposite.op i)).hom z, ?_⟩
  intro i j hij
  ext x
  have hw := CategoryTheory.Limits.limit.w
    (dualModuleDiagram sys) (CategoryTheory.homOfLE hij).op
  have hEval := congrArg (fun f => f.hom z) hw
  change ((dualInverseTransition sys hij)
      ((CategoryTheory.Limits.limit.π (dualModuleDiagram sys)
        (Opposite.op j)).hom z)) x =
    ((CategoryTheory.Limits.limit.π (dualModuleDiagram sys)
      (Opposite.op i)).hom z) x
  exact congrArg (fun f => f x) hEval

/-- The native categorical projective limit is equivalent, as a carrier, to
the compatible inverse families of stage functionals. The equivalence uses
the canonical limit projections and the universal cone lift. -/
noncomputable def projectiveLimitEquivDualInverseFamily :
    ((CategoryTheory.Limits.limit (dualModuleDiagram sys) : ModuleCat R) : Type u) ≃
      {phi : ∀ i : I, A i →ₗ[R] R //
        IsDualInverseFamily (sys := sys) phi} where
  toFun := projectiveLimitToDualInverseFamily (sys := sys)
  invFun s :=
    (dualInverseFamilyToProjectiveLimit (sys := sys) s.1 s.2).hom 1
  left_inv z := by
    let phi := projectiveLimitToDualInverseFamily (sys := sys) z
    let lift := dualInverseFamilyToProjectiveLimit
      (sys := sys) phi.1 phi.2
    have hmaps :
        ModuleCat.ofHom (LinearMap.smulRight (1 : R →ₗ[R] R) z) = lift := by
      apply CategoryTheory.Limits.limit.hom_ext
      intro i
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro r
      apply LinearMap.ext
      intro x
      have h := CategoryTheory.Limits.limit.lift_π
        (dualInverseFamilyToProjectiveCone
          (sys := sys) phi.1 phi.2) i
      have hEval := congrArg (fun f => f.hom r x) h
      have hLift :
          ((CategoryTheory.Limits.limit.π (dualModuleDiagram sys) i).hom
            (lift.hom r)) x = r • phi.1 i.unop x := by
        simpa [lift, dualInverseFamilyToProjectiveLimit,
          dualInverseFamilyToProjectiveCone, LinearMap.smulRight_apply,
          one_smul] using hEval
      change (CategoryTheory.Limits.limit.π (dualModuleDiagram sys) i).hom
          ((r • z)) x =
        ((CategoryTheory.Limits.limit.π (dualModuleDiagram sys) i).hom
          (lift.hom r)) x
      rw [map_smul]
      change r • ((CategoryTheory.Limits.limit.π
          (dualModuleDiagram sys) i).hom z) x =
        ((CategoryTheory.Limits.limit.π (dualModuleDiagram sys) i).hom
          (lift.hom r)) x
      rw [show ((CategoryTheory.Limits.limit.π
        (dualModuleDiagram sys) i).hom z) = phi.1 i.unop from rfl, hLift]
    have hAtOne := congrArg (fun f => f.hom 1) hmaps
    simpa [lift, phi, dualInverseFamilyToProjectiveLimit,
      LinearMap.smulRight_apply, one_smul] using hAtOne.symm
  right_inv s := by
    apply Subtype.ext
    funext i
    ext x
    exact dualInverseFamilyToProjectiveLimit_stage
      (sys := sys) s.1 s.2 i x

/-- Descend an inverse-compatible family of stage functionals through the
native `ModuleCat` colimit. This is the converse to
`dualInverseTransition_comp_cocone`. -/
noncomputable def dualInverseFamilyColimitMap
    (phi : ∀ i : I, A i →ₗ[R] R)
    (hphi : IsDualInverseFamily (sys := sys) phi) :
    CategoryTheory.Limits.colimit (Native.moduleDiagram sys) ⟶
      ModuleCat.of R R := by
  exact Native.descendModuleCocone sys
    (dualInverseFamilyCocone (sys := sys) phi hphi)

/-- The map induced by an inverse family evaluates on every canonical stage
inclusion as the original stage functional. -/
@[simp] theorem dualInverseFamilyColimitMap_stage
    (phi : ∀ i : I, A i →ₗ[R] R)
    (hphi : IsDualInverseFamily (sys := sys) phi) (i : I) (x : A i) :
    (dualInverseFamilyColimitMap (sys := sys) phi hphi).hom
      ((CategoryTheory.Limits.colimit.ι (Native.moduleDiagram sys) i).hom x) =
        phi i x := by
  have h := Native.moduleColimit_desc_stage sys
    (dualInverseFamilyCocone (sys := sys) phi hphi) i
  exact congrArg (fun f => f x) h

/-- A linear readout on the categorical colimit is determined by its inverse
family of stage restrictions. -/
theorem dualInverseFamilyColimitMap_unique
    (phi : ∀ i : I, A i →ₗ[R] R)
    (hphi : IsDualInverseFamily (sys := sys) phi)
    (g : CategoryTheory.Limits.colimit (Native.moduleDiagram sys) ⟶
      ModuleCat.of R R)
    (hg : ∀ i x,
      g.hom ((CategoryTheory.Limits.colimit.ι (Native.moduleDiagram sys) i).hom x) =
        phi i x) :
    g = dualInverseFamilyColimitMap (sys := sys) phi hphi := by
  apply CategoryTheory.Limits.colimit.hom_ext
  intro i
  ext x
  change g.hom ((CategoryTheory.Limits.colimit.ι
      (Native.moduleDiagram sys) i).hom x) =
    (dualInverseFamilyColimitMap (sys := sys) phi hphi).hom
      ((CategoryTheory.Limits.colimit.ι (Native.moduleDiagram sys) i).hom x)
  rw [hg i x, dualInverseFamilyColimitMap_stage (sys := sys) phi hphi i x]

/-- Restrict a linear functional on the categorical colimit to each stage.
The resulting family is compatible with the dual inverse transitions. -/
def colimitFunctionalStageFamily
    (g : InfoGeometry.Categorical.Holonomy.ModuleInductiveLimit R
      (Native.moduleDiagram sys) →ₗ[R] R) :
    ∀ i : I, A i →ₗ[R] R :=
  fun i => g.comp (CategoryTheory.Limits.colimit.ι
    (Native.moduleDiagram sys) i).hom

/-- Every colimit linear functional restricts to a compatible dual inverse family across stages. -/
theorem colimitFunctionalStageFamily_isDualInverseFamily
    (g : InfoGeometry.Categorical.Holonomy.ModuleInductiveLimit R
      (Native.moduleDiagram sys) →ₗ[R] R) :
    IsDualInverseFamily (sys := sys) (colimitFunctionalStageFamily
      (sys := sys) g) := by
  intro i j hij
  ext x
  change g ((CategoryTheory.Limits.colimit.ι
      (Native.moduleDiagram sys) j).hom (sys.f hij x)) =
    g ((CategoryTheory.Limits.colimit.ι
      (Native.moduleDiagram sys) i).hom x)
  have h := CategoryTheory.Limits.colimit.w_assoc
    (Native.moduleDiagram sys) (CategoryTheory.homOfLE hij)
    (ModuleCat.ofHom g)
  exact congrArg (fun f : (Native.moduleDiagram sys).obj i ⟶
    ModuleCat.of R R => f.hom x) h

/-- Inverse-compatible functionals on the stages are exactly the linear
functionals on the categorical `ModuleCat` colimit. This is the concrete
inverse-system form of the colimit state duality: the forward map descends the
family through the colimit, and the inverse map restricts a global functional
to every canonical stage injection. -/
noncomputable def dualInverseFamilyEquivColimitFunctional :
    {phi : ∀ i : I, A i →ₗ[R] R //
      IsDualInverseFamily (sys := sys) phi} ≃
        (InfoGeometry.Categorical.Holonomy.ModuleInductiveLimit R
          (Native.moduleDiagram sys) →ₗ[R] R) where
  toFun s := (dualInverseFamilyColimitMap (sys := sys) s.1 s.2).hom
  invFun g :=
    ⟨colimitFunctionalStageFamily (sys := sys) g,
      colimitFunctionalStageFamily_isDualInverseFamily (sys := sys) g⟩
  left_inv s := by
    apply Subtype.ext
    funext i
    ext x
    exact dualInverseFamilyColimitMap_stage
      (sys := sys) s.1 s.2 i x
  right_inv g := by
    have h := dualInverseFamilyColimitMap_unique (sys := sys)
      (colimitFunctionalStageFamily (sys := sys) g)
      (colimitFunctionalStageFamily_isDualInverseFamily (sys := sys) g)
      (ModuleCat.ofHom g) (by
        intro i x
        rfl)
    exact (congrArg ModuleCat.Hom.hom h).symm

/-- Evaluating the colimit functional associated to an inverse family `s` on the `i`-th stage
inclusion recovers `s.1 i x`. -/
@[simp] theorem dualInverseFamilyEquivColimitFunctional_apply_stage
    (s : {phi : ∀ i : I, A i →ₗ[R] R //
      IsDualInverseFamily (sys := sys) phi}) (i : I) (x : A i) :
    (dualInverseFamilyEquivColimitFunctional (sys := sys) s)
      ((CategoryTheory.Limits.colimit.ι
        (Native.moduleDiagram sys) i).hom x) = s.1 i x := by
  have h := dualInverseFamilyColimitMap_stage (sys := sys) s.1 s.2 i x
  exact h

/-- The projective-limit cone and inductive-colimit descent are two
categorical realizations of the same compatible inverse family: at every
stage, both readouts evaluate to `phi i x`. -/
theorem dualInverseFamily_projective_inductive_stage_agree
    (phi : ∀ i : I, A i →ₗ[R] R)
    (hphi : IsDualInverseFamily (sys := sys) phi) (i : I) (x : A i) :
    ((dualInverseFamilyToProjectiveLimit (sys := sys) phi hphi ≫
      CategoryTheory.Limits.limit.π (dualModuleDiagram sys)
        (Opposite.op i)).hom (1 : R)) x =
      (dualInverseFamilyColimitMap (sys := sys) phi hphi).hom
        ((CategoryTheory.Limits.colimit.ι (Native.moduleDiagram sys) i).hom x) := by
  rw [dualInverseFamilyToProjectiveLimit_stage (sys := sys) phi hphi i x,
    dualInverseFamilyColimitMap_stage (sys := sys) phi hphi i x]

/-- The native categorical projective limit of the dual stages is equivalent
to the linear dual of the native categorical colimit. This is the composite
of recovering the compatible inverse family from its limit projections and
descending that family through the colimit cocone. -/
noncomputable def projectiveLimitDualColimitFunctionalEquiv :
    ((CategoryTheory.Limits.limit (dualModuleDiagram sys) : ModuleCat R) : Type u) ≃
      (InfoGeometry.Categorical.Holonomy.ModuleInductiveLimit R
        (Native.moduleDiagram sys) →ₗ[R] R) :=
  (projectiveLimitEquivDualInverseFamily (sys := sys)).trans
    (dualInverseFamilyEquivColimitFunctional (sys := sys))

/-- The composed native limit/colimit duality reads each stage by the
corresponding projective-limit projection. -/
@[simp] theorem projectiveLimitDualColimitFunctionalEquiv_stage
    (z : ((CategoryTheory.Limits.limit (dualModuleDiagram sys) : ModuleCat R) : Type u))
    (i : I) (x : A i) :
    (projectiveLimitDualColimitFunctionalEquiv (sys := sys) z)
      ((CategoryTheory.Limits.colimit.ι
        (Native.moduleDiagram sys) i).hom x) =
      ((CategoryTheory.Limits.limit.π
        (dualModuleDiagram sys) (Opposite.op i)).hom z) x := by
  simp [projectiveLimitDualColimitFunctionalEquiv,
    projectiveLimitEquivDualInverseFamily,
    projectiveLimitToDualInverseFamily,
    dualInverseFamilyEquivColimitFunctional_apply_stage]

end FilteredColimit.InductiveCocone
