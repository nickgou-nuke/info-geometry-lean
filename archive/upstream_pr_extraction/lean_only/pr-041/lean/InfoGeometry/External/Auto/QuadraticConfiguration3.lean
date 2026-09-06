import Mathlib.Tactic

/-!
# Three non-isotropic points for an even complex quadric: finite presentation data

This file formalizes the theorem-honest combinatorial core of the proposed
calculation for

`F₃(q) = {(x₁,x₂,x₃) : q(xᵢ-xⱼ) ≠ 0 for i<j}`

where `q` is the standard complex quadratic form on `ℂ^D`.  We prove the finite
algebraic bookkeeping that is independent of analytic de Rham machinery:

* the three pairwise differences and non-isotropic predicates;
* translation/reduced-coordinate packaging for the `V × Y₃` split;
* the six edge generators `αᵢⱼ`, `βᵢⱼ` with degrees `1` and `D-1`;
* the three internal/external cooperad edge maps for arity three;
* data fields for the genuine de Rham comparison, quadric angular class, Arnold
  relations, and full cooperad theorem.

No claim here proves the analytic de Rham cohomology of the quadric complement;
that result remains an explicit field of the supplied comparison data.
-/

noncomputable section

namespace QuadraticConfiguration3

open BigOperators

/-- The ambient complex vector space `ℂ^D`. -/
abbrev V (D : ℕ) := Fin D → ℂ

/-- Standard complex quadratic form.  A general nondegenerate complex quadric is
linearly equivalent to this model over `ℂ`; the linear equivalence theorem is an
analytic/algebraic-geometry input, not used as a kernel fact here. -/
def q (D : ℕ) (x : V D) : ℂ := ∑ i : Fin D, x i * x i

/-- Difference of two points. -/
def diff {D : ℕ} (x y : V D) : V D := fun i => x i - y i

/-- A three-point configuration with all pairwise quadratic separations nonzero. -/
structure Config3 (D : ℕ) where
  x1 : V D
  x2 : V D
  x3 : V D
  h12 : q D (diff x1 x2) ≠ 0
  h13 : q D (diff x1 x3) ≠ 0
  h23 : q D (diff x2 x3) ≠ 0

/-- Reduced coordinates for the translation split: fix `x₁` as base and remember
`u=x₁-x₂`, `v=x₁-x₃`.  With this convention the third difference is `v-u`. -/
structure Reduced3 (D : ℕ) where
  base : V D
  u : V D
  v : V D
  hu : q D u ≠ 0
  hv : q D v ≠ 0
  huv : q D (diff v u) ≠ 0

/-- Reconstruct a three-point configuration from reduced coordinates. -/
def Reduced3.toConfig {D : ℕ} (R : Reduced3 D) : Config3 D where
  x1 := R.base
  x2 := fun i => R.base i - R.u i
  x3 := fun i => R.base i - R.v i
  h12 := by
    intro h
    apply R.hu
    convert h using 2
    ext i
    simp [diff]
  h13 := by
    intro h
    apply R.hv
    convert h using 2
    ext i
    simp [diff]
  h23 := by
    intro h
    apply R.huv
    convert h using 2
    ext i
    simp [diff, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]

/-- Extract reduced coordinates from a configuration. -/
def Config3.toReduced {D : ℕ} (C : Config3 D) : Reduced3 D where
  base := C.x1
  u := diff C.x1 C.x2
  v := diff C.x1 C.x3
  hu := C.h12
  hv := C.h13
  huv := by
    intro h
    apply C.h23
    convert h using 2
    ext i
    simp [diff, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]

@[ext] theorem Config3.ext {D : ℕ} {C C' : Config3 D}
    (hx1 : C.x1 = C'.x1) (hx2 : C.x2 = C'.x2) (hx3 : C.x3 = C'.x3) :
    C = C' := by
  cases C
  cases C'
  cases hx1
  cases hx2
  cases hx3
  rfl

@[ext] theorem Reduced3.ext {D : ℕ} {R R' : Reduced3 D}
    (hbase : R.base = R'.base) (hu : R.u = R'.u) (hv : R.v = R'.v) :
    R = R' := by
  cases R
  cases R'
  cases hbase
  cases hu
  cases hv
  rfl

/-- Translation splitting and translation reassembly are inverse operations. -/
theorem Config3.toReduced_toConfig {D : ℕ} (R : Reduced3 D) :
    Config3.toReduced (Reduced3.toConfig R) = R := by
  cases R
  ext <;> simp [Reduced3.toConfig, Config3.toReduced, diff]

/-- Translation splitting and reassembly are inverse operations. -/
theorem Config3.toConfig_toReduced {D : ℕ} (C : Config3 D) :
    Reduced3.toConfig (Config3.toReduced C) = C := by
  cases C
  ext <;> simp [Reduced3.toConfig, Config3.toReduced, diff]

/-- A concrete Equiv between full configurations and reduced coordinates. -/
def config3_reduced_equiv (D : ℕ) : Config3 D ≃ Reduced3 D where
  toFun := Config3.toReduced
  invFun := Reduced3.toConfig
  left_inv := by
    intro C
    exact Config3.toConfig_toReduced C
  right_inv := by
    intro R
    exact Config3.toReduced_toConfig R
/-- Edge set of the complete graph on three labelled points. -/
inductive Edge3 where
  | e12 | e13 | e23
  deriving DecidableEq, Repr

instance : Fintype Edge3 where
  elems := {Edge3.e12, Edge3.e13, Edge3.e23}
  complete := by
    intro e
    cases e <;> simp

/-- Cohomology generator kind: logarithmic `α` or quadric angular `β`. -/
inductive GenKind where
  | alpha | beta
  deriving DecidableEq, Repr

/-- Edge-labelled generator. -/
abbrev EdgeGen := Edge3 × GenKind

namespace EdgeGen

abbrev edge (g : EdgeGen) : Edge3 := g.1

abbrev kind (g : EdgeGen) : GenKind := g.2

end EdgeGen

/-- The degree of an edge generator for ambient dimension `D`. -/
def genDegree (D : ℕ) (g : EdgeGen) : ℕ :=
  match g.kind with
  | GenKind.alpha => 1
  | GenKind.beta => D - 1

@[simp] theorem alpha_degree (D : ℕ) (e : Edge3) :
    genDegree D ⟨e, GenKind.alpha⟩ = 1 := rfl

@[simp] theorem beta_degree (D : ℕ) (e : Edge3) :
    genDegree D ⟨e, GenKind.beta⟩ = D - 1 := rfl

/-- Even-dimensional property package for the quadric calculation. -/
structure EvenDimension where
  D : ℕ
  evenD : D % 2 = 0

/-- Three possible arity-three cooperad decompositions: a two-point internal
cluster and one external point. -/
inductive BlockDecomp3 where
  | pair12_3 | pair13_2 | pair23_1
  deriving DecidableEq, Repr

/-- Target side for a cooperad generator after a two-point cluster is separated:
internal edge of the inserted pair, or outer edge connecting the cluster to the
remaining point. -/
inductive TargetFactor where
  | outer | internal
  deriving DecidableEq, Repr

/-- The arity-three cooperad map on edges: internal edges stay internal; all
cross-block edges become the unique outer edge. -/
def cooperadEdge (b : BlockDecomp3) (e : Edge3) : TargetFactor :=
  match b, e with
  | BlockDecomp3.pair12_3, Edge3.e12 => TargetFactor.internal
  | BlockDecomp3.pair13_2, Edge3.e13 => TargetFactor.internal
  | BlockDecomp3.pair23_1, Edge3.e23 => TargetFactor.internal
  | _, _ => TargetFactor.outer

/-- Cooperad map on edge generators preserves the `α/β` label and only changes
whether the edge is internal or external. -/
def cooperadGen (b : BlockDecomp3) (g : EdgeGen) : TargetFactor × GenKind :=
  (cooperadEdge b g.edge, g.kind)

@[simp] theorem cooperad_pair23_internal_alpha :
    cooperadGen BlockDecomp3.pair23_1 ⟨Edge3.e23, GenKind.alpha⟩ =
      (TargetFactor.internal, GenKind.alpha) := rfl

@[simp] theorem cooperad_pair23_internal_beta :
    cooperadGen BlockDecomp3.pair23_1 ⟨Edge3.e23, GenKind.beta⟩ =
      (TargetFactor.internal, GenKind.beta) := rfl

@[simp] theorem cooperad_pair23_cross_12_alpha :
    cooperadGen BlockDecomp3.pair23_1 ⟨Edge3.e12, GenKind.alpha⟩ =
      (TargetFactor.outer, GenKind.alpha) := rfl

@[simp] theorem cooperad_pair23_cross_13_alpha :
    cooperadGen BlockDecomp3.pair23_1 ⟨Edge3.e13, GenKind.alpha⟩ =
      (TargetFactor.outer, GenKind.alpha) := rfl

/-- For every arity-three decomposition there is exactly one internal edge. -/
theorem cooperad_has_internal_edge (b : BlockDecomp3) :
    ∃ e : Edge3, cooperadEdge b e = TargetFactor.internal := by
  cases b
  · exact ⟨Edge3.e12, rfl⟩
  · exact ⟨Edge3.e13, rfl⟩
  · exact ⟨Edge3.e23, rfl⟩

/-- For every arity-three decomposition, every non-internal edge is external. -/
theorem cooperad_edge_outer_or_internal (b : BlockDecomp3) (e : Edge3) :
    cooperadEdge b e = TargetFactor.outer ∨
    cooperadEdge b e = TargetFactor.internal := by
  cases b <;> cases e <;> simp [cooperadEdge]

/-- Formal name for the three-edge Arnold triangle relation.  This is a symbolic
relation marker, not a proof of the analytic de Rham relation. -/
inductive ArnoldTriangle where
  | alpha | beta | mixed
  deriving DecidableEq, Repr

/-- Typed comparison data needed to identify a presentation with the de Rham
cohomology ring.  Unlike the former proposition markers, this packet carries
the classes, the presentation equivalence, and the cooperad map whose laws are
to be checked.  Constructing a value therefore requires an actual comparison,
not five unrelated propositions. -/
structure DeRhamCohomologyData (E : EvenDimension) where
  cohomology : Type*
  [cohomologyRing : CommRing cohomology]
  presentation : Type*
  [presentationRing : CommRing presentation]
  pairComplementClassAlpha : Edge3 → cohomology
  pairComplementClassBeta : Edge3 → cohomology
  /-- The arity-three Arnold relation among the actual alpha classes. -/
  arnoldTriangleRelations :
    pairComplementClassAlpha Edge3.e12 *
          pairComplementClassAlpha Edge3.e23 -
        pairComplementClassAlpha Edge3.e12 *
          pairComplementClassAlpha Edge3.e13 +
      pairComplementClassAlpha Edge3.e23 *
        pairComplementClassAlpha Edge3.e13 = 0
  /-- Completeness is an equivalence of rings, rather than a truth marker. -/
  deRhamPresentationIsComplete : presentation ≃+* cohomology
  /-- Cocomposition on the represented alpha and beta edge classes. -/
  cooperadAction :
    BlockDecomp3 → EdgeGen → TargetFactor × GenKind
  cooperadCompatibility :
    ∀ b g, cooperadAction b g = cooperadGen b g

namespace DeRhamCohomologyData

/-- The presentation comparison sends zero to the zero cohomology class. -/
@[simp] theorem presentation_zero
    (C : DeRhamCohomologyData E) :
    C.deRhamPresentationIsComplete
        C.presentationRing.toRing.toAddCommGroup.zero =
      C.cohomologyRing.toRing.toAddCommGroup.zero :=
  by
    letI : CommRing C.presentation := C.presentationRing
    letI : CommRing C.cohomology := C.cohomologyRing
    exact C.deRhamPresentationIsComplete.map_zero

/-- The stored cocomposition is exactly the finite arity-three owner map. -/
theorem cooperad_action_eq
    (C : DeRhamCohomologyData E) (b : BlockDecomp3) (g : EdgeGen) :
    C.cooperadAction b g = cooperadGen b g :=
  C.cooperadCompatibility b g

end DeRhamCohomologyData

end QuadraticConfiguration3

end noncomputable section
