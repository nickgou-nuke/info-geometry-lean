import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Order.Directed
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import InfoGeometry.Categorical.Holonomy

set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false

noncomputable section

namespace FilteredColimit

/-- Directed Filtered Inductive System of Modules over a Directed Set (I, ≤). -/
structure DirectInductiveSystem (R : Type*) [CommRing R] (I : Type*) [Preorder I] (A : I → Type*) [∀ i, AddCommGroup (A i)] [∀ i, Module R (A i)] where
  f : ∀ {i j : I}, i ≤ j → (A i →ₗ[R] A j)
  f_id : ∀ (i : I), f (le_refl i) = LinearMap.id
  f_comp : ∀ {i j k : I} (hij : i ≤ j) (hjk : j ≤ k), (f hjk).comp (f hij) = f (le_trans hij hjk)

/-- Cocone over a Direct Inductive System targeting a Module A_inf. -/
abbrev InductiveCocone (R : Type*) [CommRing R] {I : Type*} [Preorder I]
    {A : I → Type*} [∀ i, AddCommGroup (A i)] [∀ i, Module R (A i)]
    (sys : DirectInductiveSystem R I A) (A_inf : Type*)
    [AddCommGroup A_inf] [Module R A_inf] : Type _ :=
  {psi : ∀ i : I, A i →ₗ[R] A_inf //
    ∀ {i j : I} (hij : i ≤ j), (psi j).comp (sys.f hij) = psi i}

namespace InductiveCocone

variable {R : Type*} [CommRing R] {I : Type*} [Preorder I] {A : I → Type*} [∀ i, AddCommGroup (A i)] [∀ i, Module R (A i)]
variable {sys : DirectInductiveSystem R I A} {A_inf : Type*} [AddCommGroup A_inf] [Module R A_inf]
variable (cocone : InductiveCocone R sys A_inf)

abbrev psi (cocone : InductiveCocone R sys A_inf) (i : I) :
    A i →ₗ[R] A_inf := cocone.1 i

abbrev psi_comm (cocone : InductiveCocone R sys A_inf)
    {i j : I} (hij : i ≤ j) :
    (cocone.psi j).comp (sys.f hij) = cocone.psi i := by
  change (cocone.1 j).comp (sys.f hij) = cocone.1 i
  exact cocone.2 hij

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
def dualInverseTransition (sys : DirectInductiveSystem R I A) {i j : I} (hij : i ≤ j) : (A j →ₗ[R] R) →ₗ[R] (A i →ₗ[R] R) where
  toFun phi_j := phi_j.comp (sys.f hij)
  map_add' phi1 phi2 := rfl
  map_smul' c phi := rfl

/-- The dual transition along an identity arrow is the identity map. -/
theorem dual_inverse_id
    (sys : DirectInductiveSystem R I A) (i : I)
    (phi_i : A i →ₗ[R] R) :
    dualInverseTransition sys (le_refl i) phi_i = phi_i := by
  dsimp [dualInverseTransition]
  rw [sys.f_id]
  rfl

/-- The dual transition along an identity arrow is the identity linear map. -/
theorem dual_inverse_id_map
    (sys : DirectInductiveSystem R I A) (i : I) :
    dualInverseTransition sys (le_refl i) = LinearMap.id := by
  apply LinearMap.ext
  intro phi
  simpa using dual_inverse_id sys i phi

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

/-- The dual transition maps satisfy the inverse-system composition law as a
    linear-map equality. -/
theorem dual_inverse_comp_map
    (sys : DirectInductiveSystem R I A) {i j k : I}
    (hij : i ≤ j) (hjk : j ≤ k) :
    (dualInverseTransition sys hij).comp
        (dualInverseTransition sys hjk) =
      dualInverseTransition sys (le_trans hij hjk) := by
  apply LinearMap.ext
  intro phi
  simpa using dual_inverse_comp sys hij hjk phi

/-- **Theorem**: Filtered Direct Colimit State Duality Pairings:
    The pairing <ψ_i(x), φ_inf> on the colimit equals the local stage pairing <x, φ_i>
    where φ_i = φ_inf ∘ ψ_i. -/
theorem colimit_duality_pairing (phi_inf : A_inf →ₗ[R] R) (i : I) (x : A i) :
    phi_inf (cocone.psi i x) = (phi_inf.comp (cocone.psi i)) x := rfl

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

variable {R : Type u} [CommRing R]
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

/-! The descended map is uniquely determined by its finite-stage readouts. -/
theorem descendModuleCocone_unique
    (sys : DirectInductiveSystem R I A)
    (cocone : InductiveCocone R sys (A_inf := A_inf))
    (g : colimit (moduleDiagram sys) ⟶ ModuleCat.of R A_inf)
    (hg : ∀ i,
      colimit.ι (moduleDiagram sys) i ≫ g =
        (moduleCocone sys cocone).ι.app i) :
    g = descendModuleCocone sys cocone := by
  apply colimit.hom_ext
  intro i
  rw [moduleColimit_desc_stage sys cocone i]
  exact hg i

variable {K : Type u} [Category.{u} K]

/-! The inverse direction is the actual projective limit of a `ModuleCat`
diagram, not merely the composition law of precomposition maps. -/

noncomputable abbrev projectiveModuleLimit (G : K ⥤ ModuleCat.{u} R) : ModuleCat.{u} R :=
  CategoryTheory.Limits.limit G

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
    colimit (CategoryTheory.Limits.limit F) ≅ limit (CategoryTheory.Limits.colimit F.flip) := by
  exact InfoGeometry.Categorical.Holonomy.colimit_limit_iso R F

end Native

end FilteredColimit
