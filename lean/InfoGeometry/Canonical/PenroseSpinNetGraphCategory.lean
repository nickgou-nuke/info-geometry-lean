import Mathlib.CategoryTheory.PathCategory.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.FinitePenrosePatchCategory
import InfoGeometry.Causal.ProofGraphExteriorCalculus

/-!
# Penrose spin-net graph/category foundation

This file adds the discrete graph/path-category layer beneath the finite Penrose
patch tower and colimit files.

BUCKET 1: CLOSED FINITE THEOREMS
- a finite patch determines a subtype of vertices carrying the inherited poset;
- the inherited preorder category gives a quiver/path category on patch vertices;
- every path in the patch graph composes to a single order arrow;
- path endpoints determine forward-cone membership, Penrose incidence, and state
  transport;
- patch inclusions induce functors on vertex categories and on path categories.

BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT PREMISES
- all incidence/state-transport readouts depend only on the primitive
  `SpinNet` data already carried by `DiscretePenroseSpinNet`.

BUCKET 3: OPEN CLOSURE DEBT
- no concrete Penrose tiling substitution system;
- no AF/C⋆ completion;
- no twistor field equation or K-theoretic classification theorem.
-/

namespace InfoGeometry.Canonical.PenroseSpinNetGraphCategory

open CategoryTheory
open InfoGeometry.Canonical.DiscretePenroseSpinNet
open InfoGeometry.Canonical.FinitePenrosePatchCategory
open InfoGeometry.Causal.ProofGraphExteriorCalculus

universe u v

section PatchVertices

variable {α : Type u}
variable [PartialOrder α]

/-- The vertex set of a finite Penrose patch. -/
abbrev PatchVertex (P : FinitePatch (α := α)) : Type u :=
  {a // a ∈ P.carrier}

instance (P : FinitePatch (α := α)) : PartialOrder (PatchVertex (α := α) P) :=
  inferInstance

@[simp] theorem patchVertex_val_le_iff
    {P : FinitePatch (α := α)} {a b : PatchVertex (α := α) P} :
    a ≤ b ↔ a.1 ≤ b.1 :=
  Iff.rfl

omit [PartialOrder α] in
@[simp] theorem patchVertex_mem_carrier
    {P : FinitePatch (α := α)} (a : PatchVertex (α := α) P) :
    a.1 ∈ P.carrier :=
  a.2

/-- Inclusion of patch vertices into the ambient event preorder category. -/
def patchVertexInclusion
    (P : FinitePatch (α := α)) : PatchVertex (α := α) P ⥤ α where
  obj a := a.1
  map {X Y} f := homOfLE (show X.1 ≤ Y.1 from leOfHom f)

end PatchVertices

section PatchPaths

variable {α : Type u}
variable [PartialOrder α]
variable {𝕜 T D : Type u}
variable [CommRing 𝕜]
variable [AddCommGroup T] [Module 𝕜 T]
variable [AddCommGroup D] [Module 𝕜 D]
variable (S : SpinNet α 𝕜 T D)

/-- The state diagram restricted to the vertices of a finite patch. -/
def patchStateDiagram
    (P : FinitePatch (α := α)) : PatchVertex (α := α) P ⥤ Type v :=
  patchVertexInclusion (α := α) P ⋙ S.stateDiagram

/-- The induced state functor on the path category of a finite patch graph. -/
def patchPathStateDiagram
    (P : FinitePatch (α := α)) : CategoryTheory.Paths (PatchVertex (α := α) P) ⥤ Type v :=
  CategoryTheory.Paths.lift (patchStateDiagram (α := α) (𝕜 := 𝕜) (T := T) (D := D) S P).toPrefunctor

/--
Any path in the finite patch graph composes to a single order arrow, hence gives
an inequality between its endpoints.
-/
theorem patchPath_le
    {P : FinitePatch (α := α)} {a b : CategoryTheory.Paths (PatchVertex (α := α) P)}
    (p : a ⟶ b) :
    a.1 ≤ b.1 := by
  exact leOfHom ((CategoryTheory.pathComposition (PatchVertex (α := α) P)).map p)

/-- The target of a patch path lies in the forward cone of the source event inside the patch. -/
theorem patchPath_target_mem_forwardConeIn
    {P : FinitePatch (α := α)}
    {a b : CategoryTheory.Paths (PatchVertex (α := α) P)}
    (p : a ⟶ b) :
    b.1 ∈ forwardConeIn (α := α) P a.1 := by
  exact ⟨b.2, patchPath_le (α := α) p⟩

/-- The source of a patch path lies in the backward cone of the target event inside the patch. -/
theorem patchPath_source_mem_backwardConeIn
    {P : FinitePatch (α := α)}
    {a b : CategoryTheory.Paths (PatchVertex (α := α) P)}
    (p : a ⟶ b) :
    a.1 ∈ backwardConeIn (α := α) P b.1 := by
  exact ⟨a.2, patchPath_le (α := α) p⟩

/-- Every patch path carries Penrose incidence from its source to its target. -/
theorem incidence_of_patchPath
    {P : FinitePatch (α := α)}
    {a b : CategoryTheory.Paths (PatchVertex (α := α) P)}
    (p : a ⟶ b) :
    S.twistorIncidence.Incidence (S.dualAt a.1) (S.twistorAt b.1) :=
  incidence_of_le S (patchPath_le (α := α) p)

/--
State transport along a patch path is exactly the state-diagram map of the
composed order arrow.
-/
def patchPathTransport
    {P : FinitePatch (α := α)}
    {a b : CategoryTheory.Paths (PatchVertex (α := α) P)}
    (p : a ⟶ b) :
    (patchStateDiagram (α := α) (𝕜 := 𝕜) (T := T) (D := D) S P).obj a →
      (patchStateDiagram (α := α) (𝕜 := 𝕜) (T := T) (D := D) S P).obj b :=
  (patchStateDiagram (α := α) (𝕜 := 𝕜) (T := T) (D := D) S P).map
    ((CategoryTheory.pathComposition (PatchVertex (α := α) P)).map p)

@[simp] theorem patchPathTransport_nil
    {P : FinitePatch (α := α)}
    (a : CategoryTheory.Paths (PatchVertex (α := α) P))
    (x : (patchStateDiagram (α := α) (𝕜 := 𝕜) (T := T) (D := D) S P).obj a) :
    patchPathTransport (α := α) (𝕜 := 𝕜) (T := T) (D := D) S (𝟙 a) x = x := by
  simp [patchPathTransport]

@[simp] theorem patchPathTransport_cons
    {P : FinitePatch (α := α)}
    {a b c : CategoryTheory.Paths (PatchVertex (α := α) P)}
    (p : a ⟶ b) (q : b ⟶ c)
    (x : (patchStateDiagram (α := α) (𝕜 := 𝕜) (T := T) (D := D) S P).obj a) :
    patchPathTransport (α := α) (𝕜 := 𝕜) (T := T) (D := D) S (p ≫ q) x =
      patchPathTransport (α := α) (𝕜 := 𝕜) (T := T) (D := D) S q
        (patchPathTransport (α := α) (𝕜 := 𝕜) (T := T) (D := D) S p x) := by
  simpa [patchPathTransport] using
    congrFun
      ((patchStateDiagram (α := α) (𝕜 := 𝕜) (T := T) (D := D) S P).map_comp
        ((CategoryTheory.pathComposition (PatchVertex (α := α) P)).map p)
        ((CategoryTheory.pathComposition (PatchVertex (α := α) P)).map q))
      x

/-- Directed proof graph obtained by forgetting only the order relation on a patch. -/
noncomputable def patchDirectedProofGraph
    (P : FinitePatch (α := α)) : DirectedProofGraph (PatchVertex (α := α) P) where
  edge := (· ≤ ·)
  decEdge := Classical.decRel _

/-- The discrete gradient on the patch graph evaluates to endpoint difference along any path. -/
theorem patchGrad_apply_of_path
    (P : FinitePatch (α := α))
    (f : PatchVertex (α := α) P → ℝ)
    {a b : CategoryTheory.Paths (PatchVertex (α := α) P)}
    (p : a ⟶ b) :
    grad (patchDirectedProofGraph (α := α) P) f a b = f b - f a := by
  apply grad_apply_of_edge
  exact patchPath_le (α := α) p

end PatchPaths

section PatchInclusions

variable {α : Type u}
variable [PartialOrder α]

/-- Vertex map induced by inclusion of finite patches. -/
def mapPatchVertex
    {P Q : FinitePatch (α := α)} (f : P ⟶ Q) :
    PatchVertex (α := α) P → PatchVertex (α := α) Q
  | ⟨a, ha⟩ => ⟨a, f.down ha⟩

omit [PartialOrder α] in
@[simp] theorem mapPatchVertex_val
    {P Q : FinitePatch (α := α)} (f : P ⟶ Q)
    (a : PatchVertex (α := α) P) :
    (mapPatchVertex (α := α) f a).1 = a.1 :=
  rfl

/-- Inclusion of finite patches as a functor on patch-vertex preorder categories. -/
def patchInclusionFunctor
    {P Q : FinitePatch (α := α)} (f : P ⟶ Q) :
    PatchVertex (α := α) P ⥤ PatchVertex (α := α) Q where
  obj := mapPatchVertex (α := α) f
  map {X Y} g := homOfLE (show mapPatchVertex (α := α) f X ≤ mapPatchVertex (α := α) f Y from leOfHom g)

@[simp] theorem patchInclusionFunctor_obj
    {P Q : FinitePatch (α := α)} (f : P ⟶ Q)
    (a : PatchVertex (α := α) P) :
    (patchInclusionFunctor (α := α) f).obj a = mapPatchVertex (α := α) f a :=
  rfl

/-- Inclusion of finite patches lifts to a functor on path categories. -/
def patchPathInclusionFunctor
    {P Q : FinitePatch (α := α)} (f : P ⟶ Q) :
    CategoryTheory.Paths (PatchVertex (α := α) P) ⥤
      CategoryTheory.Paths (PatchVertex (α := α) Q) :=
  CategoryTheory.Paths.lift
    ((patchInclusionFunctor (α := α) f).toPrefunctor ⋙q
      CategoryTheory.Paths.of (PatchVertex (α := α) Q))

/-- A mapped patch path has the same underlying order relation between endpoints. -/
theorem patchPathInclusion_preserves_le
    {P Q : FinitePatch (α := α)} (f : P ⟶ Q)
    {a b : CategoryTheory.Paths (PatchVertex (α := α) P)}
    (p : a ⟶ b) :
    (mapPatchVertex (α := α) f a).1 ≤ (mapPatchVertex (α := α) f b).1 := by
  exact patchPath_le (α := α) ((patchPathInclusionFunctor (α := α) f).map p)

end PatchInclusions

end InfoGeometry.Canonical.PenroseSpinNetGraphCategory
