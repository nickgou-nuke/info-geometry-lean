/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.Module.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Order.Directed
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import InfoGeometry.Categorical.FilteredDirectLimitOwner
import InfoGeometry.Categorical.StateSpaceColimitCommutativity

set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false

noncomputable section

namespace FilteredColimit

/-- Directed Filtered Inductive System of Modules over a Directed Set (I, ≤). -/
structure DirectInductiveSystem (R : Type*) [Ring R] (I : Type*) [Preorder I] (A : I → Type*) [∀ i, AddCommGroup (A i)] [∀ i, Module R (A i)] where
  f : ∀ {i j : I}, i ≤ j → (A i →ₗ[R] A j)
  f_id : ∀ (i : I), f (le_refl i) = LinearMap.id
  f_comp : ∀ {i j k : I} (hij : i ≤ j) (hjk : j ≤ k), (f hjk).comp (f hij) = f (le_trans hij hjk)

/-- Cocone over a Direct Inductive System targeting a Module A_inf. -/
structure InductiveCocone (R : Type*) [Ring R] {I : Type*} [Preorder I] {A : I → Type*} [∀ i, AddCommGroup (A i)] [∀ i, Module R (A i)] (sys : DirectInductiveSystem R I A) (A_inf : Type*) [AddCommGroup A_inf] [Module R A_inf] where
  psi : ∀ i : I, A i →ₗ[R] A_inf
  psi_comm : ∀ {i j : I} (hij : i ≤ j), (psi j).comp (sys.f hij) = psi i

namespace InductiveCocone

variable {R : Type*} [Ring R] {I : Type*} [Preorder I] {A : I → Type*} [∀ i, AddCommGroup (A i)] [∀ i, Module R (A i)]
variable {sys : DirectInductiveSystem R I A} {A_inf : Type*} [AddCommGroup A_inf] [Module R A_inf]
variable (cocone : InductiveCocone R sys A_inf)

/-- **Theorem**: Direct Inductive Colimit Cocone Commutativity:
    For any transition map f_{i, j} (i ≤ j) and element x ∈ A_i,
    evaluating the cocone target map at stage j on f_{i, j}(x) equals evaluation at stage i:
    ψ_j (f_{i, j}(x)) = ψ_i (x). -/
theorem cocone_eval_comm {i j : I} (hij : i ≤ j) (x : A i) :
    cocone.psi j (sys.f hij x) = cocone.psi i x := by
  have h_comp := cocone.psi_comm hij
  exact LinearMap.congr_fun h_comp x

/-- **Theorem**: Direct Inductive Colimit Functional Trace Commutativity:
    For any linear evaluation functional φ_inf : A_inf →ₗ[R] R on the colimit space,
    evaluating φ_inf on ψ_j (f_{i, j}(x)) equals evaluation on ψ_i (x). -/
theorem colimit_functional_trace_comm (phi_inf : A_inf →ₗ[R] R) {i j : I} (hij : i ≤ j) (x : A i) :
    phi_inf (cocone.psi j (sys.f hij x)) = phi_inf (cocone.psi i x) := by
  rw [cocone.cocone_eval_comm hij x]

/-- Inverse / Projective System of Dual Functional Spaces A_i* = A i →ₗ[R] R. -/
def dualInverseTransition (sys : DirectInductiveSystem R I A) {i j : I} (hij : i ≤ j) : (A j →ₗ[R] R) →+ (A i →ₗ[R] R) where
  toFun phi_j := phi_j.comp (sys.f hij)
  map_zero' := rfl
  map_add' phi1 phi2 := rfl

/-- **Theorem**: Dual Inverse System Composition Property:
    g_{i, h} ∘ g_{j, i} = g_{j, h} for dual functionals. -/
theorem dual_inverse_comp (sys : DirectInductiveSystem R I A) {i j k : I} (hij : i ≤ j) (hjk : j ≤ k) (phi_k : A k →ₗ[R] R) :
    dualInverseTransition sys hij (dualInverseTransition sys hjk phi_k) = dualInverseTransition sys (le_trans hij hjk) phi_k := by
  dsimp [dualInverseTransition]
  ext x
  dsimp
  have h_comp := sys.f_comp hij hjk
  have h_eval := LinearMap.congr_fun h_comp x
  dsimp at h_eval
  rw [h_eval]

/-- **Theorem**: Filtered Direct Colimit State Duality Pairings:
    The pairing <ψ_i(x), φ_inf> on the colimit equals the local stage pairing <x, φ_i>
    where φ_i = φ_inf ∘ ψ_i. -/
theorem colimit_duality_pairing (phi_inf : A_inf →ₗ[R] R) (i : I) (x : A i) :
    phi_inf (cocone.psi i x) = (phi_inf.comp (cocone.psi i)) x := rfl

/-- A family of stage functionals is compatible with the inverse system dual
to `sys` when every later functional restricts to the earlier one. -/
def IsDualInverseFamily (sys : DirectInductiveSystem R I A)
    (phi : ∀ i : I, A i →ₗ[R] R) : Prop :=
  ∀ {i j : I} (hij : i ≤ j), dualInverseTransition sys hij (phi j) = phi i

end InductiveCocone

/-!
## Native categorical realization

The elementary presentation above is now connected to the actual Mathlib
category of `R`-modules.  The definitions below do not model a limit by a
chosen target: they construct the corresponding `ModuleCat` diagram and use
Mathlib's `colimit` and `limit` universal properties.  In particular, the
filtered and projective directions remain distinct.
-/

namespace Native

open CategoryTheory
open CategoryTheory.Limits

universe u

variable {R : Type u} [Ring R]
variable {I : Type u} [Preorder I]
variable {A : I → Type u} [∀ i, AddCommGroup (A i)] [∀ i, Module R (A i)]
variable {A_inf : Type u} [AddCommGroup A_inf] [Module R A_inf]

/-- The `ModuleCat` diagram induced by a genuine linear direct system. -/
def moduleDiagram (sys : DirectInductiveSystem R I A) : I ⥤ ModuleCat.{u} R where
  obj i := ModuleCat.of R (A i)
  map f := ModuleCat.ofHom (sys.f (leOfHom f))
  map_id i := by
    ext x
    exact LinearMap.congr_fun (sys.f_id i) x
  map_comp f g := by
    ext x
    exact LinearMap.congr_fun
      (sys.f_comp (leOfHom f) (leOfHom g)).symm x

/-- A linear cocone is promoted to a categorical cocone over `moduleDiagram`. -/
def moduleCocone
    (sys : DirectInductiveSystem R I A)
    (cocone : InductiveCocone R sys (A_inf := A_inf))
    :
    Cocone (moduleDiagram sys) where
  pt := ModuleCat.of R A_inf
  ι :=
    { app := fun i => ModuleCat.ofHom (cocone.psi i)
      naturality := by
        intro i j f
        ext x
        exact LinearMap.congr_fun
          (cocone.psi_comm (leOfHom f)) x }

/-- The universal map from the native filtered colimit to a cocone target. -/
noncomputable def descendModuleCocone
    (sys : DirectInductiveSystem R I A)
    (cocone : InductiveCocone R sys (A_inf := A_inf)) :
    colimit (moduleDiagram sys) ⟶ ModuleCat.of R A_inf :=
  colimit.desc (moduleDiagram sys) (moduleCocone sys cocone)

/-- The native colimit map agrees with every original stage map. -/
@[reassoc]
theorem moduleColimit_desc_stage
    (sys : DirectInductiveSystem R I A)
    (cocone : InductiveCocone R sys (A_inf := A_inf)) (i : I) :
    colimit.ι (moduleDiagram sys) i ≫ descendModuleCocone sys cocone =
      (moduleCocone sys cocone).ι.app i := by
  exact colimit.ι_desc (moduleCocone sys cocone) i

variable {K : Type u} [Category.{u} K]

/-! The inverse direction is the actual projective limit of a `ModuleCat`
diagram, not merely the composition law of precomposition maps. -/

noncomputable abbrev projectiveModuleLimit (G : K ⥤ ModuleCat.{u} R) : ModuleCat.{u} R :=
  limit G

noncomputable def projectiveLimitProjection
    (G : K ⥤ ModuleCat.{u} R) (k : K) :
    projectiveModuleLimit (R := R) G ⟶ G.obj k :=
  limit.π G k

noncomputable def liftProjectiveModuleLimit
    (G : K ⥤ ModuleCat.{u} R) (t : Cone G) :
    t.pt ⟶ projectiveModuleLimit (R := R) G :=
  limit.lift G t

@[reassoc]
theorem lift_projectiveLimit_projection
    (G : K ⥤ ModuleCat.{u} R) (t : Cone G) (k : K) :
    liftProjectiveModuleLimit G t ≫ projectiveLimitProjection G k =
      t.π.app k := by
  exact limit.lift_π t k

variable {J : Type u} [Category.{u} J] [IsFiltered J]
variable {L : Type u} [Category.{u} L] [FinCategory L]

/-! Filtered colimits and finite inverse limits are connected by Mathlib's
preservation theorem, rather than by a finite or diagonal surrogate. -/

noncomputable def filteredColimitFiniteLimitIso
    (F : L ⥤ J ⥤ ModuleCat.{u} R) :
    colimit (limit F) ≅ limit (colimit F.flip) := by
  exact InfoGeometry.Categorical.Holonomy.colimit_limit_iso R F

end Native

/-! The dual family, its genuine `ModuleCat` inverse diagram, and the induced
map out of the forward colimit. -/

namespace InductiveCocone

open CategoryTheory
open CategoryTheory.Limits

variable {R : Type u} [CommRing R]
variable {I : Type u} [Preorder I]
variable {A : I → Type u} [∀ i, AddCommGroup (A i)] [∀ i, Module R (A i)]

/-- The projective `ModuleCat` diagram obtained by dualizing a direct system. -/
def dualModuleDiagram (sys : DirectInductiveSystem R I A) : Iᵒᵖ ⥤ ModuleCat.{u} R where
  obj i := ModuleCat.of R (A (Opposite.unop i) →ₗ[R] R)
  map f := ModuleCat.ofHom {
    toFun := dualInverseTransition sys (leOfHom f.unop)
    map_add' := by intro phi psi; ext x; rfl
    map_smul' := by intro r phi; ext x; rfl }
  map_id i := by
    ext phi x
    change phi (sys.f (le_refl (Opposite.unop i)) x) = phi x
    rw [sys.f_id]
    rfl
  map_comp f g := by
    apply ModuleCat.hom_ext
    ext phi x
    change phi (sys.f (leOfHom (f ≫ g).unop) x) =
      phi (sys.f (leOfHom f.unop) (sys.f (leOfHom g.unop) x))
    have hcomp : sys.f (leOfHom (f ≫ g).unop) =
        sys.f (le_trans (leOfHom g.unop) (leOfHom f.unop)) := by
      congr 1
    rw [hcomp]
    exact congrArg phi
      (congrArg (fun F => F x)
        (sys.f_comp (leOfHom g.unop) (leOfHom f.unop)).symm)

/-- Compatible stage functionals are exactly the sections of the underlying
`Type` diagram of `dualModuleDiagram`. -/
noncomputable def dualInverseFamilyEquivSections
    (sys : DirectInductiveSystem R I A) :
    { phi : ∀ i : I, A i →ₗ[R] R // IsDualInverseFamily sys phi } ≃
      (dualModuleDiagram sys ⋙ forget (ModuleCat.{u} R)).sections where
  toFun s :=
    ⟨fun i => s.val (Opposite.unop i), by
      intro i j f
      change dualInverseTransition sys (leOfHom f.unop) (s.val (Opposite.unop i)) =
        s.val (Opposite.unop j)
      exact s.property (leOfHom f.unop)⟩
  invFun s :=
    ⟨fun i => s.val (Opposite.op i), by
      intro i j hij
      apply LinearMap.ext
      intro x
      let f : Opposite.op j ⟶ Opposite.op i := (homOfLE hij).op
      have h := s.property f
      change dualInverseTransition sys (leOfHom f.unop) (s.val (Opposite.op j)) =
        s.val (Opposite.op i) at h
      have hle : leOfHom f.unop = hij := Subsingleton.elim _ _
      rw [hle] at h
      exact congrArg (fun phi => phi x) h⟩
  left_inv s := by
    apply Subtype.ext
    rfl
  right_inv s := by
    apply Subtype.ext
    rfl

/-- The carrier of the actual `ModuleCat` projective limit is equivalent to
the compatible inverse family of stage functionals. This is obtained by
forgetting the `ModuleCat` limit, applying the `Type` limit/sections
equivalence, and identifying sections with compatible families. -/
noncomputable def projectiveLimitEquivDualInverseFamily
    (sys : DirectInductiveSystem R I A) :
    ((limit (dualModuleDiagram sys) : ModuleCat R) : Type u) ≃
      { phi : ∀ i : I, A i →ₗ[R] R // IsDualInverseFamily sys phi } := by
  let F := dualModuleDiagram sys
  let H := F ⋙ forget (ModuleCat.{u} R)
  let e := preservesLimitIso (forget (ModuleCat.{u} R)) F
  let e₁ : ((limit F : ModuleCat R) : Type u) ≃ limit H :=
    { toFun := fun x => e.hom x
      invFun := fun x => e.inv x
      left_inv := by
        intro x
        simpa using congrArg (fun f => f x) (Iso.hom_inv_id e)
      right_inv := by
        intro x
        simpa using congrArg (fun f => f x) (Iso.inv_hom_id e) }
  exact e₁.trans ((Types.limitEquivSections H).trans
    (dualInverseFamilyEquivSections sys).symm)

/-- Evaluation of a compatible family obtained from the actual projective
`ModuleCat` limit is the corresponding categorical projection. -/
@[simp] theorem projectiveLimitEquivDualInverseFamily_apply
    (sys : DirectInductiveSystem R I A)
    (z : ((limit (dualModuleDiagram sys) : ModuleCat R) : Type u)) (i : I) :
    (projectiveLimitEquivDualInverseFamily sys z).val i =
      (limit.π (dualModuleDiagram sys) (Opposite.op i)).hom z := by
  let F := dualModuleDiagram sys
  let H := F ⋙ forget (ModuleCat.{u} R)
  let e := preservesLimitIso (forget (ModuleCat.{u} R)) F
  let e₁ : ((limit F : ModuleCat R) : Type u) ≃ limit H :=
    { toFun := fun x => e.hom x
      invFun := fun x => e.inv x
      left_inv := by intro x; simpa using congrArg (fun f => f x) (Iso.hom_inv_id e)
      right_inv := by intro x; simpa using congrArg (fun f => f x) (Iso.inv_hom_id e) }
  change (((e₁.trans ((Types.limitEquivSections H).trans
    (dualInverseFamilyEquivSections sys).symm)) z).val i) = _
  rw [Equiv.trans_apply, Equiv.trans_apply]
  change ((Types.limitEquivSections H) (e₁ z)).val (Opposite.op i) = _
  rw [Types.limitEquivSections_apply]
  exact congrArg (fun f => f z) (preservesLimitIso_hom_π
    (G := forget (ModuleCat.{u} R)) (F := F) (Opposite.op i))

/-- The scalar-linear map into the actual projective limit determined by a
compatible family of stage functionals. Its cone legs send `r` to the scalar
multiple `r • phi i`. -/
noncomputable def dualInverseFamilyToProjectiveLimit
    {sys : DirectInductiveSystem R I A}
    (phi : ∀ i : I, A i →ₗ[R] R)
    (hphi : IsDualInverseFamily sys phi) :
    ModuleCat.of R R ⟶ limit (dualModuleDiagram sys) := by
  let legs : (Functor.const (Iᵒᵖ)).obj (ModuleCat.of R R) ⟶
      dualModuleDiagram sys :=
      { app := fun i => ModuleCat.ofHom {
          toFun := fun r => r • phi (Opposite.unop i)
          map_add' := by intro r s; ext x; simp [add_mul]
          map_smul' := by intro r s; ext x; simp [mul_assoc] }
        naturality := by
          intro i j f
          apply ModuleCat.hom_ext
          apply LinearMap.ext
          intro r
          let r' : R := r
          have h := congrArg (fun q : A (Opposite.unop j) →ₗ[R] R => r' • q)
            (hphi (leOfHom f.unop))
          change r' • phi (Opposite.unop j) =
            dualInverseTransition sys (leOfHom f.unop) (r' • phi (Opposite.unop i))
          exact h.symm }
  exact limit.lift (dualModuleDiagram sys) ⟨ModuleCat.of R R, legs⟩

/-- The stage functional obtained by evaluating the scalar-to-limit morphism
at `1` and then projecting to stage `i`. -/
noncomputable def dualInverseFamilyToProjectiveLimitStageFunctional
    {sys : DirectInductiveSystem R I A}
    (phi : ∀ i : I, A i →ₗ[R] R)
    (hphi : IsDualInverseFamily sys phi) (i : I) : A i →ₗ[R] R :=
  (dualInverseFamilyToProjectiveLimit (sys := sys) phi hphi ≫
    limit.π (dualModuleDiagram sys) (Opposite.op i)).hom (1 : R)

/-- The scalar-to-limit morphism followed by a stage projection recovers the
compatible functional at scalar `1`. -/
@[simp] theorem dualInverseFamilyToProjectiveLimit_stage
    {sys : DirectInductiveSystem R I A}
    (phi : ∀ i : I, A i →ₗ[R] R)
    (hphi : IsDualInverseFamily sys phi) (i : I) (x : A i) :
    dualInverseFamilyToProjectiveLimitStageFunctional (sys := sys) phi hphi i x = phi i x := by
  simp only [dualInverseFamilyToProjectiveLimitStageFunctional,
    dualInverseFamilyToProjectiveLimit, limit.lift_π]
  change ((1 : R) • phi i) x = phi i x
  simp

variable {A_inf : Type u} [AddCommGroup A_inf] [Module R A_inf]

/-- Descend a compatible family of stage functionals to the native filtered
colimit. This is the universal map of the actual `ModuleCat` colimit. -/
noncomputable def dualInverseFamilyColimitMap
    (sys : DirectInductiveSystem R I A)
    (phi : ∀ i : I, A i →ₗ[R] R)
    (hphi : IsDualInverseFamily sys phi) :
    colimit (Native.moduleDiagram sys) ⟶ ModuleCat.of R R := by
  let c : InductiveCocone R sys (A_inf := R) :=
    InductiveCocone.mk phi (by
      intro i j hij
      exact LinearMap.ext fun x => congrArg (fun f => f x) (hphi hij))
  exact Native.descendModuleCocone sys c

/-- The descended functional agrees with `phi` on each colimit stage. -/
@[simp] theorem dualInverseFamilyColimitMap_stage
    (sys : DirectInductiveSystem R I A)
    (phi : ∀ i : I, A i →ₗ[R] R)
    (hphi : IsDualInverseFamily sys phi) (i : I) (x : A i) :
    (dualInverseFamilyColimitMap sys phi hphi).hom
      ((colimit.ι (Native.moduleDiagram sys) i).hom x) = phi i x := by
  let c : InductiveCocone R sys (A_inf := R) :=
    InductiveCocone.mk phi (by
      intro i j hij
      exact LinearMap.ext fun x => congrArg (fun f => f x) (hphi hij))
  have h := Native.moduleColimit_desc_stage sys c i
  exact congrArg (fun f => f x) h

end InductiveCocone

end FilteredColimit
