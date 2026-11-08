import InfoGeometry.Canonical.PenroseSpinNetGraphCategory
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.FinitePenrosePatchColimit

/-!
# Penrose spin-net path/category to colimit bridge

This file extends the finite Penrose path-category layer upward in two directions:

BUCKET 1: CLOSED FINITE/COLIMIT BRIDGES
- explicit cocones on patch path categories from chosen apex paths and legs;
- conditional universal-property packaging for such cocones;
- path-endpoint local states obtained by transporting a state along a finite path;
- theorem-honest readout of those path-endpoint local states into the existing
  sequential colimit interface of `FinitePenrosePatchColimit`.

BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT PREMISES
- colimit/universal claims for path cocones require explicit desc/factorization
  data and uniqueness premises supplied by the caller;
- limit readouts still depend on the caller-supplied cocone/readout maps and
  compatible finite predicates from `FinitePenrosePatchColimit`.

BUCKET 3: OPEN CLOSURE DEBT
- no concrete Penrose tiling substitution system;
- no concrete AF/C⋆ colimit;
- no twistor/K-theoretic classification theorem.
-/

namespace InfoGeometry.Canonical.PenroseSpinNetPathColimitBridge

open CategoryTheory
open CategoryTheory.Limits
open InfoGeometry.Canonical.FinitePenrosePatchCategory
open InfoGeometry.Canonical.FinitePenrosePatchTower
open InfoGeometry.Canonical.PenroseSpinNetGraphCategory
open InfoGeometry.Canonical.FinitePenrosePatchColimit
open InfoGeometry.Canonical.InductiveColimitBridge

universe u v w

section PathCocones

variable {α : Type u}
variable [PartialOrder α]
variable {J : Type v} [Category J]

/--
An explicit cocone on the path category of a finite patch, built from chosen legs
into a chosen apex path-object.
-/
def pathCoconeOfLegs
    (P : FinitePatch (α := α))
    (F : J ⥤ CategoryTheory.Paths (PatchVertex (α := α) P))
    {apex : CategoryTheory.Paths (PatchVertex (α := α) P)}
    (legs : ∀ j, F.obj j ⟶ apex)
    (hnat : ∀ {i j : J} (f : i ⟶ j), F.map f ≫ legs j = legs i) :
    Cocone F where
  pt := apex
  ι :=
    { app := legs
      naturality := by
        intro i j f
        simpa using hnat f }

/--
If every competing cocone admits an explicit factorization through a chosen path
cocone, and that factorization is unique, then the chosen cocone is colimiting.
-/
def pathCoconeIsColimitOfExplicitDesc
    (P : FinitePatch (α := α))
    (F : J ⥤ CategoryTheory.Paths (PatchVertex (α := α) P))
    (c : Cocone F)
    (desc : ∀ s : Cocone F, c.pt ⟶ s.pt)
    (fac : ∀ s : Cocone F, ∀ j : J, c.ι.app j ≫ desc s = s.ι.app j)
    (uniq : ∀ (s : Cocone F) (m : c.pt ⟶ s.pt),
      (∀ j : J, c.ι.app j ≫ m = s.ι.app j) → m = desc s) :
    IsColimit c where
  desc := desc
  fac := by
    intro s j
    exact fac s j
  uniq := by
    intro s m hm
    exact uniq s m hm

end PathCocones

section PathColimit

variable {α : Type u} {𝕜 T D : Type u}
variable [PartialOrder α]
variable [CommRing 𝕜]
variable [AddCommGroup T] [Module 𝕜 T]
variable [AddCommGroup D] [Module 𝕜 D]

variable {S : InfoGeometry.Canonical.DiscretePenroseSpinNet.SpinNet α 𝕜 T D}

/--
Transport a state along a finite patch path and package the target as a patch
local state.
-/
def pathEndpointLocalState
    (P : FinitePatch (α := α))
    {a b : CategoryTheory.Paths (PatchVertex (α := α) P)}
    (p : a ⟶ b)
    (x : (patchStateDiagram (α := α) (𝕜 := 𝕜) (T := T) (D := D) S P).obj a) :
    localState (α := α) S P :=
  ⟨b, patchPathTransport (α := α) (𝕜 := 𝕜) (T := T) (D := D) S p x⟩

@[simp] theorem pathEndpointLocalState_event
    {P : FinitePatch (α := α)}
    {a b : CategoryTheory.Paths (PatchVertex (α := α) P)}
    (p : a ⟶ b)
    (x : (patchStateDiagram (α := α) (𝕜 := 𝕜) (T := T) (D := D) S P).obj a) :
    (pathEndpointLocalState (α := α) (𝕜 := 𝕜) (T := T) (D := D) (S := S) P p x).1 = b :=
  rfl

@[simp] theorem mapLocalState_pathEndpointLocalState
    {P Q : FinitePatch (α := α)}
    (f : P ⟶ Q)
    {a b : CategoryTheory.Paths (PatchVertex (α := α) P)}
    (p : a ⟶ b)
    (x : (patchStateDiagram (α := α) (𝕜 := 𝕜) (T := T) (D := D) S P).obj a) :
    mapLocalState (α := α) S f
        (pathEndpointLocalState (α := α) (𝕜 := 𝕜) (T := T) (D := D) (S := S) P p x) =
      pathEndpointLocalState (α := α) (𝕜 := 𝕜) (T := T) (D := D) (S := S) Q
        ((patchPathInclusionFunctor (α := α) f).map p) x := by
  rfl

/--
Finite predicate asserting that a patch-local state is realized as a path endpoint
whose event lies in the forward cone of its source.
-/
def pathEndpointForwardConeProperty
    (P : FinitePatch (α := α)) :
    localState (α := α) S P → Prop
  | ⟨b, _⟩ =>
      ∃ (a : CategoryTheory.Paths (PatchVertex (α := α) P)) (_p : a ⟶ b),
        b.1 ∈ forwardConeIn (α := α) P a.1

/--
Finite predicate asserting that a patch-local state is realized as a path endpoint
whose source lies in the backward cone of its target.
-/
def pathEndpointBackwardConeProperty
    (P : FinitePatch (α := α)) :
    localState (α := α) S P → Prop
  | ⟨b, _⟩ =>
      ∃ (a : CategoryTheory.Paths (PatchVertex (α := α) P)) (_p : a ⟶ b),
        a.1 ∈ backwardConeIn (α := α) P b.1

/--
Finite predicate asserting that a patch-local state is realized as a path endpoint
with the corresponding Penrose twistor incidence from source to target.
-/
def pathEndpointIncidenceProperty
    (P : FinitePatch (α := α)) :
    localState (α := α) S P → Prop
  | ⟨b, _⟩ =>
      ∃ (a : CategoryTheory.Paths (PatchVertex (α := α) P)) (_p : a ⟶ b),
        S.twistorIncidence.Incidence (S.dualAt a.1) (S.twistorAt b.1)

 theorem pathEndpointForwardConeProperty_of_path
    {P : FinitePatch (α := α)}
    {a b : CategoryTheory.Paths (PatchVertex (α := α) P)}
    (p : a ⟶ b)
    (x : (patchStateDiagram (α := α) (𝕜 := 𝕜) (T := T) (D := D) S P).obj a) :
    pathEndpointForwardConeProperty (α := α) (𝕜 := 𝕜) (T := T) (D := D) (S := S) P
      (pathEndpointLocalState (α := α) (𝕜 := 𝕜) (T := T) (D := D) (S := S) P p x) := by
  refine ⟨a, p, ?_⟩
  exact patchPath_target_mem_forwardConeIn (α := α) (p := p)

 theorem pathEndpointBackwardConeProperty_of_path
    {P : FinitePatch (α := α)}
    {a b : CategoryTheory.Paths (PatchVertex (α := α) P)}
    (p : a ⟶ b)
    (x : (patchStateDiagram (α := α) (𝕜 := 𝕜) (T := T) (D := D) S P).obj a) :
    pathEndpointBackwardConeProperty (α := α) (𝕜 := 𝕜) (T := T) (D := D) (S := S) P
      (pathEndpointLocalState (α := α) (𝕜 := 𝕜) (T := T) (D := D) (S := S) P p x) := by
  refine ⟨a, p, ?_⟩
  exact patchPath_source_mem_backwardConeIn (α := α) (p := p)

 theorem pathEndpointIncidenceProperty_of_path
    {P : FinitePatch (α := α)}
    {a b : CategoryTheory.Paths (PatchVertex (α := α) P)}
    (p : a ⟶ b)
    (x : (patchStateDiagram (α := α) (𝕜 := 𝕜) (T := T) (D := D) S P).obj a) :
    pathEndpointIncidenceProperty (α := α) (𝕜 := 𝕜) (T := T) (D := D) (S := S) P
      (pathEndpointLocalState (α := α) (𝕜 := 𝕜) (T := T) (D := D) (S := S) P p x) := by
  refine ⟨a, p, ?_⟩
  simpa [pathEndpointLocalState] using
    incidence_of_patchPath (S := S) p

/--
A path-endpoint local state at a finite stage reads out to any supplied colimit
predicate through the existing local-state colimit bridge.
-/
theorem pathEndpoint_property_to_colimit
    (Twr : PatchTower S)
    (Limit : Type v)
    (toLimit : ∀ n, localState (α := α) S (Twr.stage n) → Limit)
    (cone_comm : ∀ (n : ℕ) (x : localState (α := α) S (Twr.stage n)),
      toLimit (n + 1) (mapLocalState (α := α) S (PLift.up (Twr.bond n)) x) =
        toLimit n x)
    (Pstate : ∀ n : ℕ, localState (α := α) S (Twr.stage n) → Prop)
    (Pinf : Limit → Prop)
    (hread :
      (localStateSequentialSystem (α := α) (S := S) Twr Limit toLimit cone_comm).LimitReadout Pstate Pinf)
    (n : ℕ)
    {a b : CategoryTheory.Paths (PatchVertex (α := α) (Twr.stage n))}
    (p : a ⟶ b)
    (x : (patchStateDiagram (α := α) (𝕜 := 𝕜) (T := T) (D := D) S (Twr.stage n)).obj a)
    (hx : Pstate n
      (pathEndpointLocalState (α := α) (𝕜 := 𝕜) (T := T) (D := D) (S := S) (Twr.stage n) p x)) :
    Pinf
      (toLimit n
        (pathEndpointLocalState (α := α) (𝕜 := 𝕜) (T := T) (D := D) (S := S) (Twr.stage n) p x)) :=
  localState_property_to_colimit
    (α := α) (S := S) Twr Limit toLimit cone_comm Pstate Pinf hread n
    (pathEndpointLocalState (α := α) (𝕜 := 𝕜) (T := T) (D := D) (S := S) (Twr.stage n) p x) hx

/--
A compatible path-endpoint theorem may be transported up the patch tower before
being read at the same colimit point.
-/
theorem transported_pathEndpoint_property_to_same_limit
    (Twr : PatchTower S)
    (Limit : Type v)
    (toLimit : ∀ n, localState (α := α) S (Twr.stage n) → Limit)
    (cone_comm : ∀ (n : ℕ) (x : localState (α := α) S (Twr.stage n)),
      toLimit (n + 1) (mapLocalState (α := α) S (PLift.up (Twr.bond n)) x) =
        toLimit n x)
    (Pstate : ∀ n : ℕ, localState (α := α) S (Twr.stage n) → Prop)
    (Pinf : Limit → Prop)
    (hP :
      (localStateSequentialSystem (α := α) (S := S) Twr Limit toLimit cone_comm).CompatibleProperty Pstate)
    (hread :
      (localStateSequentialSystem (α := α) (S := S) Twr Limit toLimit cone_comm).LimitReadout Pstate Pinf)
    (n m : ℕ)
    {a b : CategoryTheory.Paths (PatchVertex (α := α) (Twr.stage n))}
    (p : a ⟶ b)
    (x : (patchStateDiagram (α := α) (𝕜 := 𝕜) (T := T) (D := D) S (Twr.stage n)).obj a)
    (hx : Pstate n
      (pathEndpointLocalState (α := α) (𝕜 := 𝕜) (T := T) (D := D) (S := S) (Twr.stage n) p x)) :
    Pinf
      (toLimit (n + m)
        ((localStateSequentialSystem (α := α) (S := S) Twr Limit toLimit cone_comm).bondSeq n m
          (pathEndpointLocalState (α := α) (𝕜 := 𝕜) (T := T) (D := D) (S := S) (Twr.stage n) p x))) :=
  transported_localState_property_to_same_limit
    (α := α) (S := S) Twr Limit toLimit cone_comm Pstate Pinf hP hread n m
    (pathEndpointLocalState (α := α) (𝕜 := 𝕜) (T := T) (D := D) (S := S) (Twr.stage n) p x) hx

/--
The transported path-endpoint local state determines the same colimit point as
its original finite-stage representative.
-/
theorem transported_pathEndpoint_limit_eq
    (Twr : PatchTower S)
    (Limit : Type v)
    (toLimit : ∀ n, localState (α := α) S (Twr.stage n) → Limit)
    (cone_comm : ∀ (n : ℕ) (x : localState (α := α) S (Twr.stage n)),
      toLimit (n + 1) (mapLocalState (α := α) S (PLift.up (Twr.bond n)) x) =
        toLimit n x)
    (n m : ℕ)
    {a b : CategoryTheory.Paths (PatchVertex (α := α) (Twr.stage n))}
    (p : a ⟶ b)
    (x : (patchStateDiagram (α := α) (𝕜 := 𝕜) (T := T) (D := D) S (Twr.stage n)).obj a) :
    toLimit (n + m)
        ((localStateSequentialSystem (α := α) (S := S) Twr Limit toLimit cone_comm).bondSeq n m
          (pathEndpointLocalState (α := α) (𝕜 := 𝕜) (T := T) (D := D) (S := S) (Twr.stage n) p x)) =
      toLimit n
        (pathEndpointLocalState (α := α) (𝕜 := 𝕜) (T := T) (D := D) (S := S) (Twr.stage n) p x) :=
  transported_localState_limit_eq
    (α := α) (S := S) Twr Limit toLimit cone_comm n m
    (pathEndpointLocalState (α := α) (𝕜 := 𝕜) (T := T) (D := D) (S := S) (Twr.stage n) p x)

/--
Finite proof-graph witness extracted from a path endpoint: source, target, and the
underlying order edge in the patch proof graph.
-/
structure PathEndpointGraphData
    (P : FinitePatch (α := α)) where
  source : PatchVertex (α := α) P
  target : PatchVertex (α := α) P
  hle : source ≤ target

/-- Map finite proof-graph endpoint data along a patch inclusion. -/
def mapPathEndpointGraphData
    {P Q : FinitePatch (α := α)} (f : P ⟶ Q) :
    PathEndpointGraphData (α := α) P → PathEndpointGraphData (α := α) Q
  | ⟨source, target, hle⟩ =>
      ⟨mapPatchVertex (α := α) f source, mapPatchVertex (α := α) f target, hle⟩

@[simp] theorem mapPathEndpointGraphData_source
    {P Q : FinitePatch (α := α)} (f : P ⟶ Q)
    (y : PathEndpointGraphData (α := α) P) :
    (mapPathEndpointGraphData (α := α) f y).source = mapPatchVertex (α := α) f y.source := by
  cases y
  rfl

@[simp] theorem mapPathEndpointGraphData_target
    {P Q : FinitePatch (α := α)} (f : P ⟶ Q)
    (y : PathEndpointGraphData (α := α) P) :
    (mapPathEndpointGraphData (α := α) f y).target = mapPatchVertex (α := α) f y.target := by
  cases y
  rfl

/-- The canonical proof-graph witness carried by a finite patch path. -/
def pathEndpointGraphWitness
    (P : FinitePatch (α := α))
    {a b : CategoryTheory.Paths (PatchVertex (α := α) P)}
    (p : a ⟶ b) :
    PathEndpointGraphData (α := α) P :=
  ⟨a, b, patchPath_le (α := α) p⟩

@[simp] theorem pathEndpointGraphWitness_source
    {P : FinitePatch (α := α)}
    {a b : CategoryTheory.Paths (PatchVertex (α := α) P)}
    (p : a ⟶ b) :
    (pathEndpointGraphWitness (α := α) P p).source = a :=
  rfl

@[simp] theorem pathEndpointGraphWitness_target
    {P : FinitePatch (α := α)}
    {a b : CategoryTheory.Paths (PatchVertex (α := α) P)}
    (p : a ⟶ b) :
    (pathEndpointGraphWitness (α := α) P p).target = b :=
  rfl

/-- Endpoint equality relating a path-endpoint local state to its proof-graph witness. -/
def pathEndpointGraphEquivAt
    (P : FinitePatch (α := α)) :
    localState (α := α) S P → PathEndpointGraphData (α := α) P → Prop
  | x, y => x.1 = y.target

theorem pathEndpointGraphEquivAt_of_path
    {P : FinitePatch (α := α)}
    {a b : CategoryTheory.Paths (PatchVertex (α := α) P)}
    (p : a ⟶ b)
    (x : (patchStateDiagram (α := α) (𝕜 := 𝕜) (T := T) (D := D) S P).obj a) :
    pathEndpointGraphEquivAt (α := α) (𝕜 := 𝕜) (T := T) (D := D) (S := S) P
      (pathEndpointLocalState (α := α) (𝕜 := 𝕜) (T := T) (D := D) (S := S) P p x)
      (pathEndpointGraphWitness (α := α) P p) := by
  rfl

theorem pathEndpointGraphEquivAt_compat
    {P Q : FinitePatch (α := α)}
    (f : P ⟶ Q)
    (x : localState (α := α) S P)
    (y : PathEndpointGraphData (α := α) P)
    (hxy : pathEndpointGraphEquivAt (α := α) (𝕜 := 𝕜) (T := T) (D := D) (S := S) P x y) :
    pathEndpointGraphEquivAt (α := α) (𝕜 := 𝕜) (T := T) (D := D) (S := S) Q
      (mapLocalState (α := α) S f x)
      (mapPathEndpointGraphData (α := α) f y) := by
  cases x with
  | mk xv xs =>
      cases y with
      | mk source target hle =>
          change mapPatchVertex (α := α) f xv = mapPatchVertex (α := α) f target
          exact congrArg (mapPatchVertex (α := α) f) hxy

/-- Forward-cone readout on finite proof-graph endpoint data. -/
def pathEndpointGraphForwardConeProperty
    (P : FinitePatch (α := α)) :
    PathEndpointGraphData (α := α) P → Prop
  | y => y.target.1 ∈ forwardConeIn (α := α) P y.source.1

/-- Backward-cone readout on finite proof-graph endpoint data. -/
def pathEndpointGraphBackwardConeProperty
    (P : FinitePatch (α := α)) :
    PathEndpointGraphData (α := α) P → Prop
  | y => y.source.1 ∈ backwardConeIn (α := α) P y.target.1

/-- Incidence readout on finite proof-graph endpoint data. -/
def pathEndpointGraphIncidenceProperty
    (P : FinitePatch (α := α)) :
    PathEndpointGraphData (α := α) P → Prop
  | y => S.twistorIncidence.Incidence (S.dualAt y.source.1) (S.twistorAt y.target.1)

/-- Gradient endpoint readout on finite proof-graph endpoint data. -/
def pathEndpointGraphGradReadout
    (P : FinitePatch (α := α))
    (f : PatchVertex (α := α) P → ℝ) :
    PathEndpointGraphData (α := α) P → Prop
  | y =>
      InfoGeometry.Causal.ProofGraphExteriorCalculus.grad
        (patchDirectedProofGraph (α := α) P) f y.source y.target =
          f y.target - f y.source

theorem pathEndpointGraphForwardConeProperty_of_witness
    {P : FinitePatch (α := α)}
    {a b : CategoryTheory.Paths (PatchVertex (α := α) P)}
    (p : a ⟶ b) :
    pathEndpointGraphForwardConeProperty (P := P)
      (pathEndpointGraphWitness (α := α) P p) := by
  exact patchPath_target_mem_forwardConeIn (α := α) (p := p)

theorem pathEndpointGraphBackwardConeProperty_of_witness
    {P : FinitePatch (α := α)}
    {a b : CategoryTheory.Paths (PatchVertex (α := α) P)}
    (p : a ⟶ b) :
    pathEndpointGraphBackwardConeProperty (P := P)
      (pathEndpointGraphWitness (α := α) P p) := by
  exact patchPath_source_mem_backwardConeIn (α := α) (p := p)

theorem pathEndpointGraphIncidenceProperty_of_witness
    {P : FinitePatch (α := α)}
    {a b : CategoryTheory.Paths (PatchVertex (α := α) P)}
    (p : a ⟶ b) :
    pathEndpointGraphIncidenceProperty (S := S) (P := P)
      (pathEndpointGraphWitness (α := α) P p) := by
  exact incidence_of_patchPath (S := S) p

theorem pathEndpointGraphGradReadout_of_witness
    {P : FinitePatch (α := α)}
    (f : PatchVertex (α := α) P → ℝ)
    {a b : CategoryTheory.Paths (PatchVertex (α := α) P)}
    (p : a ⟶ b) :
    pathEndpointGraphGradReadout (P := P) f
      (pathEndpointGraphWitness (α := α) P p) := by
  exact patchGrad_apply_of_path (α := α) (P := P) (f := f) p

/--
Comparison tower between path-endpoint local states and finite proof-graph witness
states on the same patch tower.
-/
def pathEndpointGraphComparisonTower
    (Twr : PatchTower S)
    (LeftLimit : Type v)
    (left_toLimit : ∀ n, localState (α := α) S (Twr.stage n) → LeftLimit)
    (left_cone_comm : ∀ (n : ℕ) (x : localState (α := α) S (Twr.stage n)),
      left_toLimit (n + 1) (mapLocalState (α := α) S (PLift.up (Twr.bond n)) x) =
        left_toLimit n x)
    (RightLimit : Type u)
    (right_toLimit : ∀ n, PathEndpointGraphData (α := α) (Twr.stage n) → RightLimit)
    (right_cone_comm : ∀ (n : ℕ) (y : PathEndpointGraphData (α := α) (Twr.stage n)),
      right_toLimit (n + 1) (mapPathEndpointGraphData (α := α) (PLift.up (Twr.bond n)) y) = right_toLimit n y)
    (limitEquiv : LeftLimit → RightLimit → Prop)
    (limit_readout : ∀ (n : ℕ) (x : localState (α := α) S (Twr.stage n))
        (y : PathEndpointGraphData (α := α) (Twr.stage n)),
      pathEndpointGraphEquivAt (α := α) (𝕜 := 𝕜) (T := T) (D := D) (S := S) (Twr.stage n) x y →
        limitEquiv (left_toLimit n x) (right_toLimit n y)) :
    CompatibleFiniteEquivalenceTower :=
  patchLocalStateComparisonTower (α := α) (S := S) Twr LeftLimit left_toLimit left_cone_comm
    (fun n => PathEndpointGraphData (α := α) (Twr.stage n)) RightLimit
    (fun n => mapPathEndpointGraphData (α := α) (PLift.up (Twr.bond n)))
    right_toLimit right_cone_comm
    (fun n => pathEndpointGraphEquivAt (α := α) (𝕜 := 𝕜) (T := T) (D := D) (S := S) (Twr.stage n))
    (fun n x y => pathEndpointGraphEquivAt_compat (α := α) (𝕜 := 𝕜) (T := T) (D := D) (S := S)
      (PLift.up (Twr.bond n)) x y)
    limitEquiv limit_readout

theorem pathEndpointGraph_equiv_to_colimit
    (Twr : PatchTower S)
    (LeftLimit : Type v)
    (left_toLimit : ∀ n, localState (α := α) S (Twr.stage n) → LeftLimit)
    (left_cone_comm : ∀ (n : ℕ) (x : localState (α := α) S (Twr.stage n)),
      left_toLimit (n + 1) (mapLocalState (α := α) S (PLift.up (Twr.bond n)) x) =
        left_toLimit n x)
    (RightLimit : Type u)
    (right_toLimit : ∀ n, PathEndpointGraphData (α := α) (Twr.stage n) → RightLimit)
    (right_cone_comm : ∀ (n : ℕ) (y : PathEndpointGraphData (α := α) (Twr.stage n)),
      right_toLimit (n + 1) (mapPathEndpointGraphData (α := α) (PLift.up (Twr.bond n)) y) = right_toLimit n y)
    (limitEquiv : LeftLimit → RightLimit → Prop)
    (limit_readout : ∀ (n : ℕ) (x : localState (α := α) S (Twr.stage n))
        (y : PathEndpointGraphData (α := α) (Twr.stage n)),
      pathEndpointGraphEquivAt (α := α) (𝕜 := 𝕜) (T := T) (D := D) (S := S) (Twr.stage n) x y →
        limitEquiv (left_toLimit n x) (right_toLimit n y))
    (n : ℕ)
    (x : localState (α := α) S (Twr.stage n))
    (y : PathEndpointGraphData (α := α) (Twr.stage n))
    (hxy : pathEndpointGraphEquivAt (α := α) (𝕜 := 𝕜) (T := T) (D := D) (S := S) (Twr.stage n) x y) :
    limitEquiv (left_toLimit n x) (right_toLimit n y) :=
  patchLocalState_equiv_to_colimit
    (α := α) (S := S) Twr LeftLimit left_toLimit left_cone_comm
    (fun n => PathEndpointGraphData (α := α) (Twr.stage n)) RightLimit
    (fun n => mapPathEndpointGraphData (α := α) (PLift.up (Twr.bond n)))
    right_toLimit right_cone_comm
    (fun n => pathEndpointGraphEquivAt (α := α) (𝕜 := 𝕜) (T := T) (D := D) (S := S) (Twr.stage n))
    (fun n x y => pathEndpointGraphEquivAt_compat (α := α) (𝕜 := 𝕜) (T := T) (D := D) (S := S)
      (PLift.up (Twr.bond n)) x y)
    limitEquiv limit_readout n x y hxy

theorem transported_pathEndpointGraph_equiv_to_colimit
    (Twr : PatchTower S)
    (LeftLimit : Type v)
    (left_toLimit : ∀ n, localState (α := α) S (Twr.stage n) → LeftLimit)
    (left_cone_comm : ∀ (n : ℕ) (x : localState (α := α) S (Twr.stage n)),
      left_toLimit (n + 1) (mapLocalState (α := α) S (PLift.up (Twr.bond n)) x) =
        left_toLimit n x)
    (RightLimit : Type u)
    (right_toLimit : ∀ n, PathEndpointGraphData (α := α) (Twr.stage n) → RightLimit)
    (right_cone_comm : ∀ (n : ℕ) (y : PathEndpointGraphData (α := α) (Twr.stage n)),
      right_toLimit (n + 1) (mapPathEndpointGraphData (α := α) (PLift.up (Twr.bond n)) y) = right_toLimit n y)
    (limitEquiv : LeftLimit → RightLimit → Prop)
    (limit_readout : ∀ (n : ℕ) (x : localState (α := α) S (Twr.stage n))
        (y : PathEndpointGraphData (α := α) (Twr.stage n)),
      pathEndpointGraphEquivAt (α := α) (𝕜 := 𝕜) (T := T) (D := D) (S := S) (Twr.stage n) x y →
        limitEquiv (left_toLimit n x) (right_toLimit n y))
    (n m : ℕ)
    (x : localState (α := α) S (Twr.stage n))
    (y : PathEndpointGraphData (α := α) (Twr.stage n))
    (hxy : pathEndpointGraphEquivAt (α := α) (𝕜 := 𝕜) (T := T) (D := D) (S := S) (Twr.stage n) x y) :
    limitEquiv
      (left_toLimit (n + m)
        ((localStateSequentialSystem (α := α) (S := S) Twr LeftLimit left_toLimit left_cone_comm).bondSeq n m x))
      (right_toLimit (n + m)
        ((pathEndpointGraphComparisonTower (α := α) (𝕜 := 𝕜) (T := T) (D := D) (S := S)
          Twr LeftLimit left_toLimit left_cone_comm RightLimit right_toLimit right_cone_comm
          limitEquiv limit_readout).Right.bondSeq n m y)) :=
  transported_patchLocalState_equiv_to_colimit
    (α := α) (S := S) Twr LeftLimit left_toLimit left_cone_comm
    (fun n => PathEndpointGraphData (α := α) (Twr.stage n)) RightLimit
    (fun n => mapPathEndpointGraphData (α := α) (PLift.up (Twr.bond n)))
    right_toLimit right_cone_comm
    (fun n => pathEndpointGraphEquivAt (α := α) (𝕜 := 𝕜) (T := T) (D := D) (S := S) (Twr.stage n))
    (fun n x y => pathEndpointGraphEquivAt_compat (α := α) (𝕜 := 𝕜) (T := T) (D := D) (S := S)
      (PLift.up (Twr.bond n)) x y)
    limitEquiv limit_readout n m x y hxy

theorem pathEndpoint_forwardCone_to_colimit
    (Twr : PatchTower S)
    (Limit : Type v)
    (toLimit : ∀ n, localState (α := α) S (Twr.stage n) → Limit)
    (cone_comm : ∀ (n : ℕ) (x : localState (α := α) S (Twr.stage n)),
      toLimit (n + 1) (mapLocalState (α := α) S (PLift.up (Twr.bond n)) x) =
        toLimit n x)
    (Pinf : Limit → Prop)
    (hread :
      (localStateSequentialSystem (α := α) (S := S) Twr Limit toLimit cone_comm).LimitReadout
        (fun n => pathEndpointForwardConeProperty (α := α) (𝕜 := 𝕜) (T := T) (D := D) (S := S) (Twr.stage n))
        Pinf)
    (n : ℕ)
    {a b : CategoryTheory.Paths (PatchVertex (α := α) (Twr.stage n))}
    (p : a ⟶ b)
    (x : (patchStateDiagram (α := α) (𝕜 := 𝕜) (T := T) (D := D) S (Twr.stage n)).obj a) :
    Pinf
      (toLimit n
        (pathEndpointLocalState (α := α) (𝕜 := 𝕜) (T := T) (D := D) (S := S) (Twr.stage n) p x)) :=
  pathEndpoint_property_to_colimit
    (α := α) (𝕜 := 𝕜) (T := T) (D := D) (S := S) Twr Limit toLimit cone_comm
    (fun n => pathEndpointForwardConeProperty (α := α) (𝕜 := 𝕜) (T := T) (D := D) (S := S) (Twr.stage n))
    Pinf hread n p x
    (pathEndpointForwardConeProperty_of_path (α := α) (𝕜 := 𝕜) (T := T) (D := D) (S := S) p x)

theorem pathEndpoint_backwardCone_to_colimit
    (Twr : PatchTower S)
    (Limit : Type v)
    (toLimit : ∀ n, localState (α := α) S (Twr.stage n) → Limit)
    (cone_comm : ∀ (n : ℕ) (x : localState (α := α) S (Twr.stage n)),
      toLimit (n + 1) (mapLocalState (α := α) S (PLift.up (Twr.bond n)) x) =
        toLimit n x)
    (Pinf : Limit → Prop)
    (hread :
      (localStateSequentialSystem (α := α) (S := S) Twr Limit toLimit cone_comm).LimitReadout
        (fun n => pathEndpointBackwardConeProperty (α := α) (𝕜 := 𝕜) (T := T) (D := D) (S := S) (Twr.stage n))
        Pinf)
    (n : ℕ)
    {a b : CategoryTheory.Paths (PatchVertex (α := α) (Twr.stage n))}
    (p : a ⟶ b)
    (x : (patchStateDiagram (α := α) (𝕜 := 𝕜) (T := T) (D := D) S (Twr.stage n)).obj a) :
    Pinf
      (toLimit n
        (pathEndpointLocalState (α := α) (𝕜 := 𝕜) (T := T) (D := D) (S := S) (Twr.stage n) p x)) :=
  pathEndpoint_property_to_colimit
    (α := α) (𝕜 := 𝕜) (T := T) (D := D) (S := S) Twr Limit toLimit cone_comm
    (fun n => pathEndpointBackwardConeProperty (α := α) (𝕜 := 𝕜) (T := T) (D := D) (S := S) (Twr.stage n))
    Pinf hread n p x
    (pathEndpointBackwardConeProperty_of_path (α := α) (𝕜 := 𝕜) (T := T) (D := D) (S := S) p x)

theorem pathEndpoint_incidence_to_colimit
    (Twr : PatchTower S)
    (Limit : Type v)
    (toLimit : ∀ n, localState (α := α) S (Twr.stage n) → Limit)
    (cone_comm : ∀ (n : ℕ) (x : localState (α := α) S (Twr.stage n)),
      toLimit (n + 1) (mapLocalState (α := α) S (PLift.up (Twr.bond n)) x) =
        toLimit n x)
    (Pinf : Limit → Prop)
    (hread :
      (localStateSequentialSystem (α := α) (S := S) Twr Limit toLimit cone_comm).LimitReadout
        (fun n => pathEndpointIncidenceProperty (α := α) (𝕜 := 𝕜) (T := T) (D := D) (S := S) (Twr.stage n))
        Pinf)
    (n : ℕ)
    {a b : CategoryTheory.Paths (PatchVertex (α := α) (Twr.stage n))}
    (p : a ⟶ b)
    (x : (patchStateDiagram (α := α) (𝕜 := 𝕜) (T := T) (D := D) S (Twr.stage n)).obj a) :
    Pinf
      (toLimit n
        (pathEndpointLocalState (α := α) (𝕜 := 𝕜) (T := T) (D := D) (S := S) (Twr.stage n) p x)) :=
  pathEndpoint_property_to_colimit
    (α := α) (𝕜 := 𝕜) (T := T) (D := D) (S := S) Twr Limit toLimit cone_comm
    (fun n => pathEndpointIncidenceProperty (α := α) (𝕜 := 𝕜) (T := T) (D := D) (S := S) (Twr.stage n))
    Pinf hread n p x
    (pathEndpointIncidenceProperty_of_path (α := α) (𝕜 := 𝕜) (T := T) (D := D) (S := S) p x)

theorem transported_pathEndpoint_forwardCone_to_same_limit
    (Twr : PatchTower S)
    (Limit : Type v)
    (toLimit : ∀ n, localState (α := α) S (Twr.stage n) → Limit)
    (cone_comm : ∀ (n : ℕ) (x : localState (α := α) S (Twr.stage n)),
      toLimit (n + 1) (mapLocalState (α := α) S (PLift.up (Twr.bond n)) x) =
        toLimit n x)
    (Pinf : Limit → Prop)
    (hP :
      (localStateSequentialSystem (α := α) (S := S) Twr Limit toLimit cone_comm).CompatibleProperty
        (fun n => pathEndpointForwardConeProperty (α := α) (𝕜 := 𝕜) (T := T) (D := D) (S := S) (Twr.stage n)))
    (hread :
      (localStateSequentialSystem (α := α) (S := S) Twr Limit toLimit cone_comm).LimitReadout
        (fun n => pathEndpointForwardConeProperty (α := α) (𝕜 := 𝕜) (T := T) (D := D) (S := S) (Twr.stage n))
        Pinf)
    (n m : ℕ)
    {a b : CategoryTheory.Paths (PatchVertex (α := α) (Twr.stage n))}
    (p : a ⟶ b)
    (x : (patchStateDiagram (α := α) (𝕜 := 𝕜) (T := T) (D := D) S (Twr.stage n)).obj a) :
    Pinf
      (toLimit (n + m)
        ((localStateSequentialSystem (α := α) (S := S) Twr Limit toLimit cone_comm).bondSeq n m
          (pathEndpointLocalState (α := α) (𝕜 := 𝕜) (T := T) (D := D) (S := S) (Twr.stage n) p x))) :=
  transported_pathEndpoint_property_to_same_limit
    (α := α) (𝕜 := 𝕜) (T := T) (D := D) (S := S) Twr Limit toLimit cone_comm
    (fun n => pathEndpointForwardConeProperty (α := α) (𝕜 := 𝕜) (T := T) (D := D) (S := S) (Twr.stage n))
    Pinf hP hread n m p x
    (pathEndpointForwardConeProperty_of_path (α := α) (𝕜 := 𝕜) (T := T) (D := D) (S := S) p x)

theorem transported_pathEndpoint_backwardCone_to_same_limit
    (Twr : PatchTower S)
    (Limit : Type v)
    (toLimit : ∀ n, localState (α := α) S (Twr.stage n) → Limit)
    (cone_comm : ∀ (n : ℕ) (x : localState (α := α) S (Twr.stage n)),
      toLimit (n + 1) (mapLocalState (α := α) S (PLift.up (Twr.bond n)) x) =
        toLimit n x)
    (Pinf : Limit → Prop)
    (hP :
      (localStateSequentialSystem (α := α) (S := S) Twr Limit toLimit cone_comm).CompatibleProperty
        (fun n => pathEndpointBackwardConeProperty (α := α) (𝕜 := 𝕜) (T := T) (D := D) (S := S) (Twr.stage n)))
    (hread :
      (localStateSequentialSystem (α := α) (S := S) Twr Limit toLimit cone_comm).LimitReadout
        (fun n => pathEndpointBackwardConeProperty (α := α) (𝕜 := 𝕜) (T := T) (D := D) (S := S) (Twr.stage n))
        Pinf)
    (n m : ℕ)
    {a b : CategoryTheory.Paths (PatchVertex (α := α) (Twr.stage n))}
    (p : a ⟶ b)
    (x : (patchStateDiagram (α := α) (𝕜 := 𝕜) (T := T) (D := D) S (Twr.stage n)).obj a) :
    Pinf
      (toLimit (n + m)
        ((localStateSequentialSystem (α := α) (S := S) Twr Limit toLimit cone_comm).bondSeq n m
          (pathEndpointLocalState (α := α) (𝕜 := 𝕜) (T := T) (D := D) (S := S) (Twr.stage n) p x))) :=
  transported_pathEndpoint_property_to_same_limit
    (α := α) (𝕜 := 𝕜) (T := T) (D := D) (S := S) Twr Limit toLimit cone_comm
    (fun n => pathEndpointBackwardConeProperty (α := α) (𝕜 := 𝕜) (T := T) (D := D) (S := S) (Twr.stage n))
    Pinf hP hread n m p x
    (pathEndpointBackwardConeProperty_of_path (α := α) (𝕜 := 𝕜) (T := T) (D := D) (S := S) p x)

theorem transported_pathEndpoint_incidence_to_same_limit
    (Twr : PatchTower S)
    (Limit : Type v)
    (toLimit : ∀ n, localState (α := α) S (Twr.stage n) → Limit)
    (cone_comm : ∀ (n : ℕ) (x : localState (α := α) S (Twr.stage n)),
      toLimit (n + 1) (mapLocalState (α := α) S (PLift.up (Twr.bond n)) x) =
        toLimit n x)
    (Pinf : Limit → Prop)
    (hP :
      (localStateSequentialSystem (α := α) (S := S) Twr Limit toLimit cone_comm).CompatibleProperty
        (fun n => pathEndpointIncidenceProperty (α := α) (𝕜 := 𝕜) (T := T) (D := D) (S := S) (Twr.stage n)))
    (hread :
      (localStateSequentialSystem (α := α) (S := S) Twr Limit toLimit cone_comm).LimitReadout
        (fun n => pathEndpointIncidenceProperty (α := α) (𝕜 := 𝕜) (T := T) (D := D) (S := S) (Twr.stage n))
        Pinf)
    (n m : ℕ)
    {a b : CategoryTheory.Paths (PatchVertex (α := α) (Twr.stage n))}
    (p : a ⟶ b)
    (x : (patchStateDiagram (α := α) (𝕜 := 𝕜) (T := T) (D := D) S (Twr.stage n)).obj a) :
    Pinf
      (toLimit (n + m)
        ((localStateSequentialSystem (α := α) (S := S) Twr Limit toLimit cone_comm).bondSeq n m
          (pathEndpointLocalState (α := α) (𝕜 := 𝕜) (T := T) (D := D) (S := S) (Twr.stage n) p x))) :=
  transported_pathEndpoint_property_to_same_limit
    (α := α) (𝕜 := 𝕜) (T := T) (D := D) (S := S) Twr Limit toLimit cone_comm
    (fun n => pathEndpointIncidenceProperty (α := α) (𝕜 := 𝕜) (T := T) (D := D) (S := S) (Twr.stage n))
    Pinf hP hread n m p x
    (pathEndpointIncidenceProperty_of_path (α := α) (𝕜 := 𝕜) (T := T) (D := D) (S := S) p x)

/--
A pathwise finite comparison tower read through the existing patch-local-state
colimit comparison interface.
-/
def pathEndpointComparisonTower
    (Twr : PatchTower S)
    (LeftLimit : Type v)
    (left_toLimit : ∀ n, localState (α := α) S (Twr.stage n) → LeftLimit)
    (left_cone_comm : ∀ (n : ℕ) (x : localState (α := α) S (Twr.stage n)),
      left_toLimit (n + 1) (mapLocalState (α := α) S (PLift.up (Twr.bond n)) x) =
        left_toLimit n x)
    (RightStage : ℕ → Type w)
    (RightLimit : Type w)
    (right_bond : ∀ n, RightStage n → RightStage (n + 1))
    (right_toLimit : ∀ n, RightStage n → RightLimit)
    (right_cone_comm : ∀ (n : ℕ) (y : RightStage n),
      right_toLimit (n + 1) (right_bond n y) = right_toLimit n y)
    (equivAt : ∀ n : ℕ, localState (α := α) S (Twr.stage n) → RightStage n → Prop)
    (equiv_compat : ∀ (n : ℕ) (x : localState (α := α) S (Twr.stage n)) (y : RightStage n),
      equivAt n x y →
        equivAt (n + 1) (mapLocalState (α := α) S (PLift.up (Twr.bond n)) x) (right_bond n y))
    (limitEquiv : LeftLimit → RightLimit → Prop)
    (limit_readout : ∀ (n : ℕ) (x : localState (α := α) S (Twr.stage n)) (y : RightStage n),
      equivAt n x y → limitEquiv (left_toLimit n x) (right_toLimit n y)) :
    CompatibleFiniteEquivalenceTower :=
  patchLocalStateComparisonTower (α := α) (S := S) Twr LeftLimit left_toLimit left_cone_comm
    RightStage RightLimit right_bond right_toLimit right_cone_comm
    equivAt equiv_compat limitEquiv limit_readout

/-- A path-endpoint finite comparison has the supplied colimit readout. -/
theorem pathEndpoint_equiv_to_colimit
    (Twr : PatchTower S)
    (LeftLimit : Type v)
    (left_toLimit : ∀ n, localState (α := α) S (Twr.stage n) → LeftLimit)
    (left_cone_comm : ∀ (n : ℕ) (x : localState (α := α) S (Twr.stage n)),
      left_toLimit (n + 1) (mapLocalState (α := α) S (PLift.up (Twr.bond n)) x) =
        left_toLimit n x)
    (RightStage : ℕ → Type w)
    (RightLimit : Type w)
    (right_bond : ∀ n, RightStage n → RightStage (n + 1))
    (right_toLimit : ∀ n, RightStage n → RightLimit)
    (right_cone_comm : ∀ (n : ℕ) (y : RightStage n),
      right_toLimit (n + 1) (right_bond n y) = right_toLimit n y)
    (equivAt : ∀ n : ℕ, localState (α := α) S (Twr.stage n) → RightStage n → Prop)
    (equiv_compat : ∀ (n : ℕ) (x : localState (α := α) S (Twr.stage n)) (y : RightStage n),
      equivAt n x y →
        equivAt (n + 1) (mapLocalState (α := α) S (PLift.up (Twr.bond n)) x) (right_bond n y))
    (limitEquiv : LeftLimit → RightLimit → Prop)
    (limit_readout : ∀ (n : ℕ) (x : localState (α := α) S (Twr.stage n)) (y : RightStage n),
      equivAt n x y → limitEquiv (left_toLimit n x) (right_toLimit n y))
    (n : ℕ) (x : localState (α := α) S (Twr.stage n)) (y : RightStage n)
    (hxy : equivAt n x y) :
    limitEquiv (left_toLimit n x) (right_toLimit n y) :=
  patchLocalState_equiv_to_colimit
    (α := α) (S := S) Twr LeftLimit left_toLimit left_cone_comm
    RightStage RightLimit right_bond right_toLimit right_cone_comm
    equivAt equiv_compat limitEquiv limit_readout n x y hxy

/--
A path-endpoint finite comparison remains valid after any finite number of tower
bonding steps before taking the colimit readout.
-/
theorem transported_pathEndpoint_equiv_to_colimit
    (Twr : PatchTower S)
    (LeftLimit : Type v)
    (left_toLimit : ∀ n, localState (α := α) S (Twr.stage n) → LeftLimit)
    (left_cone_comm : ∀ (n : ℕ) (x : localState (α := α) S (Twr.stage n)),
      left_toLimit (n + 1) (mapLocalState (α := α) S (PLift.up (Twr.bond n)) x) =
        left_toLimit n x)
    (RightStage : ℕ → Type w)
    (RightLimit : Type w)
    (right_bond : ∀ n, RightStage n → RightStage (n + 1))
    (right_toLimit : ∀ n, RightStage n → RightLimit)
    (right_cone_comm : ∀ (n : ℕ) (y : RightStage n),
      right_toLimit (n + 1) (right_bond n y) = right_toLimit n y)
    (equivAt : ∀ n : ℕ, localState (α := α) S (Twr.stage n) → RightStage n → Prop)
    (equiv_compat : ∀ (n : ℕ) (x : localState (α := α) S (Twr.stage n)) (y : RightStage n),
      equivAt n x y →
        equivAt (n + 1) (mapLocalState (α := α) S (PLift.up (Twr.bond n)) x) (right_bond n y))
    (limitEquiv : LeftLimit → RightLimit → Prop)
    (limit_readout : ∀ (n : ℕ) (x : localState (α := α) S (Twr.stage n)) (y : RightStage n),
      equivAt n x y → limitEquiv (left_toLimit n x) (right_toLimit n y))
    (n m : ℕ) (x : localState (α := α) S (Twr.stage n)) (y : RightStage n)
    (hxy : equivAt n x y) :
    limitEquiv
      (left_toLimit (n + m)
        ((localStateSequentialSystem (α := α) (S := S) Twr LeftLimit left_toLimit left_cone_comm).bondSeq n m x))
      (right_toLimit (n + m)
        ((pathEndpointComparisonTower (α := α) (S := S) Twr LeftLimit left_toLimit left_cone_comm
          RightStage RightLimit right_bond right_toLimit right_cone_comm
          equivAt equiv_compat limitEquiv limit_readout).Right.bondSeq n m y)) :=
  CompatibleFiniteEquivalenceTower.transported_equiv_to_same_colimit
    (pathEndpointComparisonTower (α := α) (S := S) Twr LeftLimit left_toLimit left_cone_comm
      RightStage RightLimit right_bond right_toLimit right_cone_comm
      equivAt equiv_compat limitEquiv limit_readout)
    n m x y hxy

end PathColimit

end InfoGeometry.Canonical.PenroseSpinNetPathColimitBridge
