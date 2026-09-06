import Mathlib.Tactic
import InfoGeometry.Cartan.Involution
import InfoGeometry.Lie.G2RollingBall
import InfoGeometry.Topology.MobiusGeometry
import InfoGeometry.Twistor.Incidence
import InfoGeometry.Twistor.PenroseTwistor

/-!
# Rolling spinors, Möbius triples, twistors, and null-incidence gluing

This module is the theorem-safe glue layer suggested by the Baez--Huerta
rolling-ball picture and the repository's existing Möbius, twistor, Cartan, and
split-octonion incidence files.

It proves only structural facts that are genuinely available in native Lean:

* incidence-preserving maps compose and pull back cochains;
* doubled/tripled `CP¹` carriers carry the diagonal Möbius action and project
  to the Riemann sphere as expected;
* a Möbius transform fixing the projected image of three distinct `CP¹` points
  is pointwise the identity on the Riemann sphere, reusing the Möbius owner;
* Cartan involutions give left/right projectors for doubled carriers;
* null-subalgebra automorphisms preserve null incidence;
* twistor incidence directly implies null separation by the twistor owner
  theorem.

The file intentionally does **not** claim the full theorem that the radius-`3`
rolling distribution, Penrose twistor geometry, amplituhedron forms, or `G₂`
classification are equivalent.  No placeholder bridge property is introduced
for that missing theorem.
-/

noncomputable section

namespace InfoGeometry.Twistor.RollingSpinorMobiusBridge

/-! ## Abstract incidence geometry and functorial glue -/

/-- A minimal incidence geometry with points, lines, and an incidence relation. -/
structure IncidenceGeometry where
  Point : Type*
  Line : Type*
  Inc : Point → Line → Prop

namespace IncidenceGeometry

/-- Incidence-preserving map between incidence geometries. -/
structure Hom (G H : IncidenceGeometry) where
  pointMap : G.Point → H.Point
  lineMap : G.Line → H.Line
  preserves_incidence' : ∀ {p : G.Point} {ℓ : G.Line}, G.Inc p ℓ → H.Inc (pointMap p) (lineMap ℓ)

namespace Hom

variable {G H K : IncidenceGeometry}

/-- Identity incidence homomorphism. -/
def id (G : IncidenceGeometry) : Hom G G where
  pointMap := fun p => p
  lineMap := fun ℓ => ℓ
  preserves_incidence' := by intro p ℓ h; exact h

/-- Composition of incidence homomorphisms. -/
def comp (g : Hom H K) (f : Hom G H) : Hom G K where
  pointMap := g.pointMap ∘ f.pointMap
  lineMap := g.lineMap ∘ f.lineMap
  preserves_incidence' := by
    intro p ℓ h
    exact g.preserves_incidence' (f.preserves_incidence' h)

@[simp] theorem id_pointMap (G : IncidenceGeometry) (p : G.Point) :
    (id G).pointMap p = p := rfl

@[simp] theorem id_lineMap (G : IncidenceGeometry) (ℓ : G.Line) :
    (id G).lineMap ℓ = ℓ := rfl

@[simp] theorem comp_pointMap (g : Hom H K) (f : Hom G H) (p : G.Point) :
    (g.comp f).pointMap p = g.pointMap (f.pointMap p) := rfl

@[simp] theorem comp_lineMap (g : Hom H K) (f : Hom G H) (ℓ : G.Line) :
    (g.comp f).lineMap ℓ = g.lineMap (f.lineMap ℓ) := rfl

/-- Extensionality for incidence homomorphisms. -/
theorem ext {f g : Hom G H} (hp : f.pointMap = g.pointMap) (hl : f.lineMap = g.lineMap) :
    f = g := by
  cases f
  cases g
  simp only at hp hl
  cases hp
  cases hl
  congr

@[simp] theorem comp_id (f : Hom G H) : (id H).comp f = f := by
  apply ext <;> rfl

@[simp] theorem id_comp (f : Hom G H) : f.comp (id G) = f := by
  apply ext <;> rfl

@[simp] theorem comp_assoc (h : Hom K L) (g : Hom H K) (f : Hom G H) :
    (h.comp g).comp f = h.comp (g.comp f) := by
  apply ext <;> rfl

/-- Point cochains on an incidence geometry.  This is the finite/combinatorial
shadow of later de Rham or Cech data; no de Rham theorem is asserted here. -/
abbrev PointCochain (G : IncidenceGeometry) (R : Type*) := G.Point → R

/-- Line cochains on an incidence geometry. -/
abbrev LineCochain (G : IncidenceGeometry) (R : Type*) := G.Line → R

/-- Pull back point cochains along an incidence homomorphism. -/
def pullbackPointCochain (f : Hom G H) {R : Type*} (c : PointCochain H R) :
    PointCochain G R :=
  c ∘ f.pointMap

/-- Pull back line cochains along an incidence homomorphism. -/
def pullbackLineCochain (f : Hom G H) {R : Type*} (c : LineCochain H R) :
    LineCochain G R :=
  c ∘ f.lineMap

@[simp] theorem pullbackPointCochain_apply (f : Hom G H) {R : Type*}
    (c : PointCochain H R) (p : G.Point) :
    f.pullbackPointCochain c p = c (f.pointMap p) := rfl

@[simp] theorem pullbackLineCochain_apply (f : Hom G H) {R : Type*}
    (c : LineCochain H R) (ℓ : G.Line) :
    f.pullbackLineCochain c ℓ = c (f.lineMap ℓ) := rfl

@[simp] theorem pullbackPointCochain_id {R : Type*} (c : PointCochain G R) :
    (id G).pullbackPointCochain c = c := by
  rfl

@[simp] theorem pullbackLineCochain_id {R : Type*} (c : LineCochain G R) :
    (id G).pullbackLineCochain c = c := by
  rfl

@[simp] theorem pullbackPointCochain_comp (g : Hom H K) (f : Hom G H)
    {R : Type*} (c : PointCochain K R) :
    (g.comp f).pullbackPointCochain c = f.pullbackPointCochain (g.pullbackPointCochain c) :=
  rfl

@[simp] theorem pullbackLineCochain_comp (g : Hom H K) (f : Hom G H)
    {R : Type*} (c : LineCochain K R) :
    (g.comp f).pullbackLineCochain c = f.pullbackLineCochain (g.pullbackLineCochain c) :=
  rfl

/-- The incidence-edge coboundary of a point cochain and a line cochain.  This
is the graph-level shadow of a Cech/de Rham gluing defect. -/
def incidenceCoboundary {C : Type*} [Sub C]
    (α : PointCochain G C) (β : LineCochain G C) (p : G.Point) (ℓ : G.Line) : C :=
  β ℓ - α p

@[simp] theorem pullback_incidenceCoboundary {C : Type*} [Sub C]
    (f : Hom G H) (α : PointCochain H C) (β : LineCochain H C)
    (p : G.Point) (ℓ : G.Line) :
    incidenceCoboundary (f.pullbackPointCochain α) (f.pullbackLineCochain β) p ℓ =
      incidenceCoboundary α β (f.pointMap p) (f.lineMap ℓ) :=
  rfl

/-- A point cochain and a line cochain are compatible when they agree on every
incident point-line pair. -/
def Compatible {C : Type*} (α : PointCochain G C) (β : LineCochain G C) : Prop :=
  ∀ {p : G.Point} {ℓ : G.Line}, G.Inc p ℓ → α p = β ℓ

/-- Incidence-compatible cochains pull back to incidence-compatible cochains. -/
theorem compatible_pullback {C : Type*} (f : Hom G H)
    {α : PointCochain H C} {β : LineCochain H C}
    (h : Compatible α β) :
    Compatible (f.pullbackPointCochain α) (f.pullbackLineCochain β) := by
  intro p ℓ hpℓ
  exact h (f.preserves_incidence' hpℓ)

/-- Compatibility makes the incidence-edge coboundary vanish on every incident
point-line pair. -/
theorem incidenceCoboundary_eq_zero_of_compatible {C : Type*} [AddGroup C]
    {α : PointCochain G C} {β : LineCochain G C}
    (h : Compatible α β) {p : G.Point} {ℓ : G.Line} (hpℓ : G.Inc p ℓ) :
    incidenceCoboundary α β p ℓ = 0 := by
  simp [incidenceCoboundary, h hpℓ]

/-- For additive cochains, compatibility is equivalent to vanishing incidence
coboundary on incident point-line pairs. -/
theorem compatible_iff_incidenceCoboundary_eq_zero {C : Type*} [AddGroup C]
    (α : PointCochain G C) (β : LineCochain G C) :
    Compatible α β ↔
      ∀ {p : G.Point} {ℓ : G.Line}, G.Inc p ℓ → incidenceCoboundary α β p ℓ = 0 := by
  constructor
  · intro h p ℓ hpℓ
    exact incidenceCoboundary_eq_zero_of_compatible h hpℓ
  · intro h p ℓ hpℓ
    have hz := h hpℓ
    have hβα : β ℓ = α p := sub_eq_zero.mp hz
    exact hβα.symm

end Hom

/-- Pull back an incidence geometry along point and line cover maps.  Incidence
on the cover means incidence after projection to the base. -/
def pullbackCover (G : IncidenceGeometry) (CoverPoint CoverLine : Type*)
    (πP : CoverPoint → G.Point) (πL : CoverLine → G.Line) : IncidenceGeometry where
  Point := CoverPoint
  Line := CoverLine
  Inc p ℓ := G.Inc (πP p) (πL ℓ)

/-- Projection from a pulled-back cover geometry to its base incidence geometry. -/
def coverProjectionHom (G : IncidenceGeometry) (CoverPoint CoverLine : Type*)
    (πP : CoverPoint → G.Point) (πL : CoverLine → G.Line) :
    Hom (pullbackCover G CoverPoint CoverLine πP πL) G where
  pointMap := πP
  lineMap := πL
  preserves_incidence' := by intro p ℓ h; exact h

@[simp] theorem pullbackCover_inc (G : IncidenceGeometry) (CoverPoint CoverLine : Type*)
    (πP : CoverPoint → G.Point) (πL : CoverLine → G.Line)
    (p : CoverPoint) (ℓ : CoverLine) :
    (pullbackCover G CoverPoint CoverLine πP πL).Inc p ℓ ↔ G.Inc (πP p) (πL ℓ) :=
  Iff.rfl

/-! ## Incidence actions and braid/monodromy-safe transport -/

/-- A monoid action on an incidence geometry by incidence endomorphisms.

This is the theorem-safe abstraction behind later braid/monodromy examples:
each generator or word acts by a proved incidence homomorphism, and the action
laws are stated only as composition laws for those homomorphisms. -/
structure EndAction (Γ : Type*) [Monoid Γ] (G : IncidenceGeometry) where
  toHom : Γ → Hom G G
  map_one : toHom 1 = Hom.id G
  map_mul : ∀ a b : Γ, toHom (a * b) = (toHom a).comp (toHom b)

namespace EndAction

variable {Γ : Type*} [Monoid Γ] {G : IncidenceGeometry}

@[simp] theorem toHom_one (ρ : EndAction Γ G) :
    ρ.toHom 1 = Hom.id G :=
  ρ.map_one

@[simp] theorem toHom_mul (ρ : EndAction Γ G) (a b : Γ) :
    ρ.toHom (a * b) = (ρ.toHom a).comp (ρ.toHom b) :=
  ρ.map_mul a b

/-- Point action induced by an incidence endomorphism action. -/
def pointAct (ρ : EndAction Γ G) (γ : Γ) (p : G.Point) : G.Point :=
  (ρ.toHom γ).pointMap p

/-- Line action induced by an incidence endomorphism action. -/
def lineAct (ρ : EndAction Γ G) (γ : Γ) (ℓ : G.Line) : G.Line :=
  (ρ.toHom γ).lineMap ℓ

@[simp] theorem pointAct_one (ρ : EndAction Γ G) (p : G.Point) :
    ρ.pointAct 1 p = p := by
  simp [pointAct]

@[simp] theorem lineAct_one (ρ : EndAction Γ G) (ℓ : G.Line) :
    ρ.lineAct 1 ℓ = ℓ := by
  simp [lineAct]

@[simp] theorem pointAct_mul (ρ : EndAction Γ G) (a b : Γ) (p : G.Point) :
    ρ.pointAct (a * b) p = ρ.pointAct a (ρ.pointAct b p) := by
  simp [pointAct]

@[simp] theorem lineAct_mul (ρ : EndAction Γ G) (a b : Γ) (ℓ : G.Line) :
    ρ.lineAct (a * b) ℓ = ρ.lineAct a (ρ.lineAct b ℓ) := by
  simp [lineAct]

/-- Every word in an incidence action preserves incidence. -/
theorem preserves_incidence (ρ : EndAction Γ G) (γ : Γ)
    {p : G.Point} {ℓ : G.Line} (hpℓ : G.Inc p ℓ) :
    G.Inc (ρ.pointAct γ p) (ρ.lineAct γ ℓ) :=
  (ρ.toHom γ).preserves_incidence' hpℓ

/-- Pull back point cochains along one action element. -/
def pullbackPointCochain (ρ : EndAction Γ G) (γ : Γ) {C : Type*}
    (c : Hom.PointCochain G C) : Hom.PointCochain G C :=
  (ρ.toHom γ).pullbackPointCochain c

/-- Pull back line cochains along one action element. -/
def pullbackLineCochain (ρ : EndAction Γ G) (γ : Γ) {C : Type*}
    (c : Hom.LineCochain G C) : Hom.LineCochain G C :=
  (ρ.toHom γ).pullbackLineCochain c

@[simp] theorem pullbackPointCochain_apply (ρ : EndAction Γ G) (γ : Γ) {C : Type*}
    (c : Hom.PointCochain G C) (p : G.Point) :
    ρ.pullbackPointCochain γ c p = c (ρ.pointAct γ p) :=
  rfl

@[simp] theorem pullbackLineCochain_apply (ρ : EndAction Γ G) (γ : Γ) {C : Type*}
    (c : Hom.LineCochain G C) (ℓ : G.Line) :
    ρ.pullbackLineCochain γ c ℓ = c (ρ.lineAct γ ℓ) :=
  rfl

/-- Incidence-compatible cochains remain compatible under any action element. -/
theorem compatible_pullback (ρ : EndAction Γ G) (γ : Γ) {C : Type*}
    {α : Hom.PointCochain G C} {β : Hom.LineCochain G C}
    (h : Hom.Compatible α β) :
    Hom.Compatible (ρ.pullbackPointCochain γ α) (ρ.pullbackLineCochain γ β) :=
  Hom.compatible_pullback (ρ.toHom γ) h

/-- Coboundaries pull back by evaluating at the transformed point and line. -/
theorem pullback_incidenceCoboundary (ρ : EndAction Γ G) (γ : Γ)
    {C : Type*} [Sub C] (α : Hom.PointCochain G C) (β : Hom.LineCochain G C)
    (p : G.Point) (ℓ : G.Line) :
    Hom.incidenceCoboundary (ρ.pullbackPointCochain γ α)
      (ρ.pullbackLineCochain γ β) p ℓ =
        Hom.incidenceCoboundary α β (ρ.pointAct γ p) (ρ.lineAct γ ℓ) :=
  rfl

@[simp] theorem pointAct_inv_mul {Γ : Type*} [Group Γ] {G : IncidenceGeometry}
    (ρ : EndAction Γ G) (γ : Γ) (p : G.Point) :
    ρ.pointAct γ⁻¹ (ρ.pointAct γ p) = p := by
  rw [← pointAct_mul]
  simp

@[simp] theorem pointAct_mul_inv {Γ : Type*} [Group Γ] {G : IncidenceGeometry}
    (ρ : EndAction Γ G) (γ : Γ) (p : G.Point) :
    ρ.pointAct γ (ρ.pointAct γ⁻¹ p) = p := by
  rw [← pointAct_mul]
  simp

@[simp] theorem lineAct_inv_mul {Γ : Type*} [Group Γ] {G : IncidenceGeometry}
    (ρ : EndAction Γ G) (γ : Γ) (ℓ : G.Line) :
    ρ.lineAct γ⁻¹ (ρ.lineAct γ ℓ) = ℓ := by
  rw [← lineAct_mul]
  simp

@[simp] theorem lineAct_mul_inv {Γ : Type*} [Group Γ] {G : IncidenceGeometry}
    (ρ : EndAction Γ G) (γ : Γ) (ℓ : G.Line) :
    ρ.lineAct γ (ρ.lineAct γ⁻¹ ℓ) = ℓ := by
  rw [← lineAct_mul]
  simp

end EndAction

/-- Semantic alias for a braid-group or braid-monoid action once the chosen
braid carrier is supplied.  The abstraction intentionally requires only proved
incidence endomorphism action laws; it does not assert any specific anyon model. -/
abbrev BraidActionOnIncidence (B : Type*) [Monoid B] (G : IncidenceGeometry) :=
  EndAction B G

/-- Equality incidence on a type.  This is the minimal projective-label shadow
used below for finite-state examples. -/
def equalityIncidence (X : Type*) : IncidenceGeometry where
  Point := X
  Line := X
  Inc x y := x = y

/-- A permutation acts on equality incidence by the same permutation on points
and lines. -/
def permEqualityHom {X : Type*} (σ : Equiv.Perm X) :
    Hom (equalityIncidence X) (equalityIncidence X) where
  pointMap := σ
  lineMap := σ
  preserves_incidence' := by
    intro x y h
    exact congrArg σ h

@[simp] theorem permEqualityHom_pointMap {X : Type*} (σ : Equiv.Perm X) (x : X) :
    (permEqualityHom σ).pointMap x = σ x :=
  rfl

@[simp] theorem permEqualityHom_lineMap {X : Type*} (σ : Equiv.Perm X) (x : X) :
    (permEqualityHom σ).lineMap x = σ x :=
  rfl

@[simp] theorem permEqualityHom_one {X : Type*} :
    permEqualityHom (1 : Equiv.Perm X) = Hom.id (equalityIncidence X) := by
  apply Hom.ext <;> rfl

@[simp] theorem permEqualityHom_mul {X : Type*} (σ τ : Equiv.Perm X) :
    permEqualityHom (σ * τ) = (permEqualityHom σ).comp (permEqualityHom τ) := by
  apply Hom.ext <;> rfl

/-- A monoid representation by permutations acts on equality incidence.  This is
the small theorem-safe kernel of many braid-representation examples. -/
def permEqualityAction {Γ X : Type*} [Monoid Γ] (ρ : Γ →* Equiv.Perm X) :
    EndAction Γ (equalityIncidence X) where
  toHom γ := permEqualityHom (ρ γ)
  map_one := by simp
  map_mul := by
    intro a b
    rw [map_mul]
    exact permEqualityHom_mul (ρ a) (ρ b)

/-- The three-label equality-incidence carrier underlying a qutrit computational
basis.  This is only the finite label shadow, not the full projective space
`CP²`. -/
abbrev qutritLabelIncidence : IncidenceGeometry :=
  equalityIncidence (Fin 3)

/-- Any braid/monodromy representation into permutations of three labels gives a
qutrit-label incidence action.  No Fibonacci-anyon universality or fusion-rule
classification is asserted here. -/
def qutritLabelBraidAction {B : Type*} [Monoid B] (ρ : B →* Equiv.Perm (Fin 3)) :
    BraidActionOnIncidence B qutritLabelIncidence :=
  permEqualityAction ρ

/-- Readout: every braid word in a permutation representation preserves qutrit
label incidence. -/
theorem qutritLabelBraidAction_preserves_incidence {B : Type*} [Monoid B]
    (ρ : B →* Equiv.Perm (Fin 3)) (b : B) {i j : Fin 3}
    (hij : qutritLabelIncidence.Inc i j) :
    qutritLabelIncidence.Inc ((qutritLabelBraidAction ρ).pointAct b i)
      ((qutritLabelBraidAction ρ).lineAct b j) :=
  EndAction.preserves_incidence (qutritLabelBraidAction ρ) b hij

/-- Readout: qutrit-label cochain compatibility pulls back along any braid word
represented by a permutation of the three labels. -/
theorem qutritLabelBraidAction_compatible_pullback {B C : Type*} [Monoid B]
    (ρ : B →* Equiv.Perm (Fin 3)) (b : B)
    {α : Hom.PointCochain qutritLabelIncidence C}
    {β : Hom.LineCochain qutritLabelIncidence C}
    (h : Hom.Compatible α β) :
    Hom.Compatible ((qutritLabelBraidAction ρ).pullbackPointCochain b α)
      ((qutritLabelBraidAction ρ).pullbackLineCochain b β) :=
  EndAction.compatible_pullback (qutritLabelBraidAction ρ) b h

end IncidenceGeometry

/-! ## Doubled and tripled `CP¹` carriers with diagonal Möbius action -/

/-- Doubled spinor/Riemann-sphere carrier: left and right `CP¹` sectors. -/
abbrev DoubledCP1 : Type := InfoGeometry.CP1 × InfoGeometry.CP1

/-- Tripled `CP¹` carrier, used for three-point Möbius frames. -/
abbrev TripledCP1 : Type := InfoGeometry.CP1 × InfoGeometry.CP1 × InfoGeometry.CP1

/-- Diagonal Möbius action on the doubled `CP¹` carrier. -/
def mobiusDiagonal₂ (M : InfoGeometry.MobiusTransform) (p : DoubledCP1) : DoubledCP1 :=
  (M.actCP1 p.1, M.actCP1 p.2)

/-- Diagonal Möbius action on a tripled `CP¹` carrier. -/
def mobiusDiagonal₃ (M : InfoGeometry.MobiusTransform) (p : TripledCP1) : TripledCP1 :=
  (M.actCP1 p.1, M.actCP1 p.2.1, M.actCP1 p.2.2)

@[simp] theorem mobiusDiagonal₂_left (M : InfoGeometry.MobiusTransform) (p : DoubledCP1) :
    (mobiusDiagonal₂ M p).1 = M.actCP1 p.1 := rfl

@[simp] theorem mobiusDiagonal₂_right (M : InfoGeometry.MobiusTransform) (p : DoubledCP1) :
    (mobiusDiagonal₂ M p).2 = M.actCP1 p.2 := rfl

@[simp] theorem mobiusDiagonal₃_first (M : InfoGeometry.MobiusTransform) (p : TripledCP1) :
    (mobiusDiagonal₃ M p).1 = M.actCP1 p.1 := rfl

@[simp] theorem mobiusDiagonal₃_second (M : InfoGeometry.MobiusTransform) (p : TripledCP1) :
    (mobiusDiagonal₃ M p).2.1 = M.actCP1 p.2.1 := rfl

@[simp] theorem mobiusDiagonal₃_third (M : InfoGeometry.MobiusTransform) (p : TripledCP1) :
    (mobiusDiagonal₃ M p).2.2 = M.actCP1 p.2.2 := rfl

/-- Incidence geometry of the `CP¹ → RiemannSphere` projection.  A `CP¹` point
is incident with exactly its projected Riemann-sphere point. -/
def cp1ProjectionIncidence : IncidenceGeometry where
  Point := InfoGeometry.CP1
  Line := InfoGeometry.RiemannSphere
  Inc p z := p.toRiemannSphere = z

/-- Equality incidence on the Riemann sphere. -/
def riemannSphereEqualityIncidence : IncidenceGeometry where
  Point := InfoGeometry.RiemannSphere
  Line := InfoGeometry.RiemannSphere
  Inc z w := z = w

/-- Projection from `CP¹` incidence to equality incidence on the Riemann sphere. -/
def cp1ProjectionHom :
    IncidenceGeometry.Hom cp1ProjectionIncidence riemannSphereEqualityIncidence where
  pointMap := InfoGeometry.CP1.toRiemannSphere
  lineMap := id
  preserves_incidence' := by intro p z hpz; exact hpz

@[simp] theorem cp1ProjectionHom_pointMap (p : InfoGeometry.CP1) :
    cp1ProjectionHom.pointMap p = p.toRiemannSphere := rfl

@[simp] theorem cp1ProjectionHom_lineMap (z : InfoGeometry.RiemannSphere) :
    cp1ProjectionHom.lineMap z = z := rfl

/-- Same-fiber relation for the projection `CP¹ → RiemannSphere`. -/
def SameCP1Projection (p q : InfoGeometry.CP1) : Prop :=
  p.toRiemannSphere = q.toRiemannSphere

@[simp] theorem sameCP1Projection_refl (p : InfoGeometry.CP1) : SameCP1Projection p p :=
  rfl

@[simp] theorem cp1ProjectionIncidence_iff (p : InfoGeometry.CP1)
    (z : InfoGeometry.RiemannSphere) :
    cp1ProjectionIncidence.Inc p z ↔ p.toRiemannSphere = z :=
  Iff.rfl

/-- Same projection is equality after applying the projection incidence hom's
point map. -/
theorem sameCP1Projection_iff_pointMap_eq (p q : InfoGeometry.CP1) :
    SameCP1Projection p q ↔ cp1ProjectionHom.pointMap p = cp1ProjectionHom.pointMap q :=
  Iff.rfl

/-- Every Möbius transformation acts as an incidence endomorphism of the
`CP¹ → RiemannSphere` projection geometry. -/
def mobiusCP1ProjectionHom (M : InfoGeometry.MobiusTransform) :
    IncidenceGeometry.Hom cp1ProjectionIncidence cp1ProjectionIncidence where
  pointMap := M.actCP1
  lineMap := M.eval
  preserves_incidence' := by
    intro p z hpz
    rw [← hpz]
    exact InfoGeometry.mobius_action_correspondence M p

/-- Möbius action preserves fibers of `CP¹ → RiemannSphere`. -/
theorem mobius_preserves_sameCP1Projection
    (M : InfoGeometry.MobiusTransform) {p q : InfoGeometry.CP1}
    (h : SameCP1Projection p q) :
    SameCP1Projection (M.actCP1 p) (M.actCP1 q) := by
  unfold SameCP1Projection at h ⊢
  rw [InfoGeometry.mobius_action_correspondence M p,
    InfoGeometry.mobius_action_correspondence M q, h]

/-- Incidence geometry of the doubled `CP¹` projection. -/
def doubledCP1ProjectionIncidence : IncidenceGeometry where
  Point := DoubledCP1
  Line := InfoGeometry.RiemannSphere × InfoGeometry.RiemannSphere
  Inc p z := p.1.toRiemannSphere = z.1 ∧ p.2.toRiemannSphere = z.2

/-- Projection from doubled `CP¹` incidence to equality incidence on pairs of
Riemann-sphere points. -/
def doubledRiemannSphereEqualityIncidence : IncidenceGeometry where
  Point := InfoGeometry.RiemannSphere × InfoGeometry.RiemannSphere
  Line := InfoGeometry.RiemannSphere × InfoGeometry.RiemannSphere
  Inc z w := z = w

/-- Projection homomorphism from doubled `CP¹` incidence to pair equality incidence. -/
def doubledCP1ProjectionHom :
    IncidenceGeometry.Hom doubledCP1ProjectionIncidence doubledRiemannSphereEqualityIncidence where
  pointMap := fun p => (p.1.toRiemannSphere, p.2.toRiemannSphere)
  lineMap := id
  preserves_incidence' := by
    intro p z hpz
    exact Prod.ext hpz.1 hpz.2

/-- Same-fiber relation for doubled `CP¹`. -/
def SameDoubledCP1Projection (p q : DoubledCP1) : Prop :=
  p.1.toRiemannSphere = q.1.toRiemannSphere ∧ p.2.toRiemannSphere = q.2.toRiemannSphere

@[simp] theorem sameDoubledCP1Projection_refl (p : DoubledCP1) :
    SameDoubledCP1Projection p p :=
  ⟨rfl, rfl⟩

@[simp] theorem doubledCP1ProjectionIncidence_iff (p : DoubledCP1)
    (z : InfoGeometry.RiemannSphere × InfoGeometry.RiemannSphere) :
    doubledCP1ProjectionIncidence.Inc p z ↔
      p.1.toRiemannSphere = z.1 ∧ p.2.toRiemannSphere = z.2 :=
  Iff.rfl

/-- Same doubled projection is equality after applying the doubled projection
hom's point map. -/
theorem sameDoubledCP1Projection_iff_pointMap_eq (p q : DoubledCP1) :
    SameDoubledCP1Projection p q ↔
      doubledCP1ProjectionHom.pointMap p = doubledCP1ProjectionHom.pointMap q := by
  constructor
  · intro h
    exact Prod.ext h.1 h.2
  · intro h
    exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩

/-- Diagonal Möbius action is an incidence endomorphism of doubled projected
`CP¹`. -/
def mobiusDoubledCP1ProjectionHom (M : InfoGeometry.MobiusTransform) :
    IncidenceGeometry.Hom doubledCP1ProjectionIncidence doubledCP1ProjectionIncidence where
  pointMap := mobiusDiagonal₂ M
  lineMap := fun z => (M.eval z.1, M.eval z.2)
  preserves_incidence' := by
    intro p z hpz
    constructor
    · dsimp [mobiusDiagonal₂]
      rw [InfoGeometry.mobius_action_correspondence M p.1, hpz.1]
    · dsimp [mobiusDiagonal₂]
      rw [InfoGeometry.mobius_action_correspondence M p.2, hpz.2]

/-- Diagonal Möbius action preserves fibers of doubled `CP¹ → RiemannSphere²`. -/
theorem mobius_preserves_sameDoubledCP1Projection
    (M : InfoGeometry.MobiusTransform) {p q : DoubledCP1}
    (h : SameDoubledCP1Projection p q) :
    SameDoubledCP1Projection (mobiusDiagonal₂ M p) (mobiusDiagonal₂ M q) := by
  constructor
  · exact mobius_preserves_sameCP1Projection M h.1
  · exact mobius_preserves_sameCP1Projection M h.2

/-- Incidence geometry of the tripled `CP¹` projection. -/
def tripledCP1ProjectionIncidence : IncidenceGeometry where
  Point := TripledCP1
  Line := InfoGeometry.RiemannSphere × InfoGeometry.RiemannSphere × InfoGeometry.RiemannSphere
  Inc p z := p.1.toRiemannSphere = z.1 ∧
    p.2.1.toRiemannSphere = z.2.1 ∧ p.2.2.toRiemannSphere = z.2.2

/-- Equality incidence on triples of Riemann-sphere points. -/
def tripledRiemannSphereEqualityIncidence : IncidenceGeometry where
  Point := InfoGeometry.RiemannSphere × InfoGeometry.RiemannSphere × InfoGeometry.RiemannSphere
  Line := InfoGeometry.RiemannSphere × InfoGeometry.RiemannSphere × InfoGeometry.RiemannSphere
  Inc z w := z = w

/-- Projection homomorphism from tripled `CP¹` incidence to triple equality incidence. -/
def tripledCP1ProjectionHom :
    IncidenceGeometry.Hom tripledCP1ProjectionIncidence tripledRiemannSphereEqualityIncidence where
  pointMap := fun p => (p.1.toRiemannSphere, p.2.1.toRiemannSphere, p.2.2.toRiemannSphere)
  lineMap := id
  preserves_incidence' := by
    intro p z hpz
    exact Prod.ext hpz.1 (Prod.ext hpz.2.1 hpz.2.2)

/-- Same-fiber relation for tripled `CP¹`. -/
def SameTripledCP1Projection (p q : TripledCP1) : Prop :=
  p.1.toRiemannSphere = q.1.toRiemannSphere ∧
    p.2.1.toRiemannSphere = q.2.1.toRiemannSphere ∧
      p.2.2.toRiemannSphere = q.2.2.toRiemannSphere

@[simp] theorem sameTripledCP1Projection_refl (p : TripledCP1) :
    SameTripledCP1Projection p p :=
  ⟨rfl, rfl, rfl⟩

@[simp] theorem tripledCP1ProjectionIncidence_iff (p : TripledCP1)
    (z : InfoGeometry.RiemannSphere × InfoGeometry.RiemannSphere × InfoGeometry.RiemannSphere) :
    tripledCP1ProjectionIncidence.Inc p z ↔
      p.1.toRiemannSphere = z.1 ∧
        p.2.1.toRiemannSphere = z.2.1 ∧ p.2.2.toRiemannSphere = z.2.2 :=
  Iff.rfl

/-- Same tripled projection is equality after applying the tripled projection
hom's point map. -/
theorem sameTripledCP1Projection_iff_pointMap_eq (p q : TripledCP1) :
    SameTripledCP1Projection p q ↔
      tripledCP1ProjectionHom.pointMap p = tripledCP1ProjectionHom.pointMap q := by
  constructor
  · intro h
    exact Prod.ext h.1 (Prod.ext h.2.1 h.2.2)
  · intro h
    exact ⟨congrArg Prod.fst h, congrArg (fun z => z.2.1) h, congrArg (fun z => z.2.2) h⟩

/-- Diagonal Möbius action is an incidence endomorphism of tripled projected
`CP¹`. -/
def mobiusTripledCP1ProjectionHom (M : InfoGeometry.MobiusTransform) :
    IncidenceGeometry.Hom tripledCP1ProjectionIncidence tripledCP1ProjectionIncidence where
  pointMap := mobiusDiagonal₃ M
  lineMap := fun z => (M.eval z.1, M.eval z.2.1, M.eval z.2.2)
  preserves_incidence' := by
    intro p z hpz
    constructor
    · dsimp [mobiusDiagonal₃]
      rw [InfoGeometry.mobius_action_correspondence M p.1, hpz.1]
    · constructor
      · dsimp [mobiusDiagonal₃]
        rw [InfoGeometry.mobius_action_correspondence M p.2.1, hpz.2.1]
      · dsimp [mobiusDiagonal₃]
        rw [InfoGeometry.mobius_action_correspondence M p.2.2, hpz.2.2]

/-- Diagonal Möbius action preserves fibers of tripled `CP¹ → RiemannSphere³`. -/
theorem mobius_preserves_sameTripledCP1Projection
    (M : InfoGeometry.MobiusTransform) {p q : TripledCP1}
    (h : SameTripledCP1Projection p q) :
    SameTripledCP1Projection (mobiusDiagonal₃ M p) (mobiusDiagonal₃ M q) := by
  constructor
  · exact mobius_preserves_sameCP1Projection M h.1
  · constructor
    · exact mobius_preserves_sameCP1Projection M h.2.1
    · exact mobius_preserves_sameCP1Projection M h.2.2

@[simp] theorem mobiusCP1ProjectionHom_pointMap
    (M : InfoGeometry.MobiusTransform) (p : InfoGeometry.CP1) :
    (mobiusCP1ProjectionHom M).pointMap p = M.actCP1 p := rfl

@[simp] theorem mobiusCP1ProjectionHom_lineMap
    (M : InfoGeometry.MobiusTransform) (z : InfoGeometry.RiemannSphere) :
    (mobiusCP1ProjectionHom M).lineMap z = M.eval z := rfl

/-- A projected `CP¹` incidence edge is sent to a projected `CP¹` incidence edge. -/
theorem cp1ProjectionIncidence_after_mobius
    (M : InfoGeometry.MobiusTransform) (p : InfoGeometry.CP1) :
    cp1ProjectionIncidence.Inc ((mobiusCP1ProjectionHom M).pointMap p)
      ((mobiusCP1ProjectionHom M).lineMap p.toRiemannSphere) :=
  (mobiusCP1ProjectionHom M).preserves_incidence' rfl

@[simp] theorem mobiusDoubledCP1ProjectionHom_pointMap
    (M : InfoGeometry.MobiusTransform) (p : DoubledCP1) :
    (mobiusDoubledCP1ProjectionHom M).pointMap p = mobiusDiagonal₂ M p := rfl

@[simp] theorem mobiusDoubledCP1ProjectionHom_lineMap
    (M : InfoGeometry.MobiusTransform)
    (z : InfoGeometry.RiemannSphere × InfoGeometry.RiemannSphere) :
    (mobiusDoubledCP1ProjectionHom M).lineMap z = (M.eval z.1, M.eval z.2) := rfl

/-- A doubled projected `CP¹` incidence edge is preserved by diagonal Möbius action. -/
theorem doubledCP1ProjectionIncidence_after_mobius
    (M : InfoGeometry.MobiusTransform) (p : DoubledCP1) :
    doubledCP1ProjectionIncidence.Inc ((mobiusDoubledCP1ProjectionHom M).pointMap p)
      ((mobiusDoubledCP1ProjectionHom M).lineMap
        (p.1.toRiemannSphere, p.2.toRiemannSphere)) :=
  (mobiusDoubledCP1ProjectionHom M).preserves_incidence' ⟨rfl, rfl⟩

@[simp] theorem mobiusTripledCP1ProjectionHom_pointMap
    (M : InfoGeometry.MobiusTransform) (p : TripledCP1) :
    (mobiusTripledCP1ProjectionHom M).pointMap p = mobiusDiagonal₃ M p := rfl

@[simp] theorem mobiusTripledCP1ProjectionHom_lineMap
    (M : InfoGeometry.MobiusTransform)
    (z : InfoGeometry.RiemannSphere × InfoGeometry.RiemannSphere × InfoGeometry.RiemannSphere) :
    (mobiusTripledCP1ProjectionHom M).lineMap z = (M.eval z.1, M.eval z.2.1, M.eval z.2.2) := rfl

/-- A tripled projected `CP¹` incidence edge is preserved by diagonal Möbius action. -/
theorem tripledCP1ProjectionIncidence_after_mobius
    (M : InfoGeometry.MobiusTransform) (p : TripledCP1) :
    tripledCP1ProjectionIncidence.Inc ((mobiusTripledCP1ProjectionHom M).pointMap p)
      ((mobiusTripledCP1ProjectionHom M).lineMap
        (p.1.toRiemannSphere, p.2.1.toRiemannSphere, p.2.2.toRiemannSphere)) :=
  (mobiusTripledCP1ProjectionHom M).preserves_incidence' ⟨rfl, rfl, rfl⟩

/-- Compatible cochains on projected `CP¹` incidence pull back along Möbius action. -/
theorem cp1Projection_compatible_pullback
    (M : InfoGeometry.MobiusTransform) {C : Type*}
    {α : IncidenceGeometry.Hom.PointCochain cp1ProjectionIncidence C}
    {β : IncidenceGeometry.Hom.LineCochain cp1ProjectionIncidence C}
    (h : IncidenceGeometry.Hom.Compatible α β) :
    IncidenceGeometry.Hom.Compatible
      ((mobiusCP1ProjectionHom M).pullbackPointCochain α)
      ((mobiusCP1ProjectionHom M).pullbackLineCochain β) :=
  IncidenceGeometry.Hom.compatible_pullback (mobiusCP1ProjectionHom M) h

/-- Compatible cochains on doubled projected `CP¹` incidence pull back along the
diagonal Möbius action. -/
theorem doubledCP1Projection_compatible_pullback
    (M : InfoGeometry.MobiusTransform) {C : Type*}
    {α : IncidenceGeometry.Hom.PointCochain doubledCP1ProjectionIncidence C}
    {β : IncidenceGeometry.Hom.LineCochain doubledCP1ProjectionIncidence C}
    (h : IncidenceGeometry.Hom.Compatible α β) :
    IncidenceGeometry.Hom.Compatible
      ((mobiusDoubledCP1ProjectionHom M).pullbackPointCochain α)
      ((mobiusDoubledCP1ProjectionHom M).pullbackLineCochain β) :=
  IncidenceGeometry.Hom.compatible_pullback (mobiusDoubledCP1ProjectionHom M) h

/-- Compatible cochains on tripled projected `CP¹` incidence pull back along the
diagonal Möbius action. -/
theorem tripledCP1Projection_compatible_pullback
    (M : InfoGeometry.MobiusTransform) {C : Type*}
    {α : IncidenceGeometry.Hom.PointCochain tripledCP1ProjectionIncidence C}
    {β : IncidenceGeometry.Hom.LineCochain tripledCP1ProjectionIncidence C}
    (h : IncidenceGeometry.Hom.Compatible α β) :
    IncidenceGeometry.Hom.Compatible
      ((mobiusTripledCP1ProjectionHom M).pullbackPointCochain α)
      ((mobiusTripledCP1ProjectionHom M).pullbackLineCochain β) :=
  IncidenceGeometry.Hom.compatible_pullback (mobiusTripledCP1ProjectionHom M) h

/-- Pullback of the incidence coboundary along the projected `CP¹` Möbius action. -/
theorem cp1Projection_pullback_incidenceCoboundary
    (M : InfoGeometry.MobiusTransform) {C : Type*} [Sub C]
    (α : IncidenceGeometry.Hom.PointCochain cp1ProjectionIncidence C)
    (β : IncidenceGeometry.Hom.LineCochain cp1ProjectionIncidence C)
    (p : InfoGeometry.CP1) (z : InfoGeometry.RiemannSphere) :
    IncidenceGeometry.Hom.incidenceCoboundary
      ((mobiusCP1ProjectionHom M).pullbackPointCochain α)
      ((mobiusCP1ProjectionHom M).pullbackLineCochain β) p z =
        IncidenceGeometry.Hom.incidenceCoboundary α β (M.actCP1 p) (M.eval z) :=
  rfl

/-- Left projection of the doubled diagonal action agrees with the Möbius action
on the Riemann sphere. -/
theorem mobiusDiagonal₂_left_toRiemannSphere
    (M : InfoGeometry.MobiusTransform) (p : DoubledCP1) :
    (mobiusDiagonal₂ M p).1.toRiemannSphere = M.eval p.1.toRiemannSphere := by
  exact InfoGeometry.mobius_action_correspondence M p.1

/-- Right projection of the doubled diagonal action agrees with the Möbius action
on the Riemann sphere. -/
theorem mobiusDiagonal₂_right_toRiemannSphere
    (M : InfoGeometry.MobiusTransform) (p : DoubledCP1) :
    (mobiusDiagonal₂ M p).2.toRiemannSphere = M.eval p.2.toRiemannSphere := by
  exact InfoGeometry.mobius_action_correspondence M p.2

/-- First projection of the tripled diagonal action. -/
theorem mobiusDiagonal₃_first_toRiemannSphere
    (M : InfoGeometry.MobiusTransform) (p : TripledCP1) :
    (mobiusDiagonal₃ M p).1.toRiemannSphere = M.eval p.1.toRiemannSphere := by
  exact InfoGeometry.mobius_action_correspondence M p.1

/-- Second projection of the tripled diagonal action. -/
theorem mobiusDiagonal₃_second_toRiemannSphere
    (M : InfoGeometry.MobiusTransform) (p : TripledCP1) :
    (mobiusDiagonal₃ M p).2.1.toRiemannSphere = M.eval p.2.1.toRiemannSphere := by
  exact InfoGeometry.mobius_action_correspondence M p.2.1

/-- Third projection of the tripled diagonal action. -/
theorem mobiusDiagonal₃_third_toRiemannSphere
    (M : InfoGeometry.MobiusTransform) (p : TripledCP1) :
    (mobiusDiagonal₃ M p).2.2.toRiemannSphere = M.eval p.2.2.toRiemannSphere := by
  exact InfoGeometry.mobius_action_correspondence M p.2.2

/-- If a Möbius transformation fixes the Riemann-sphere projections of three
distinct `CP¹` points, then it is the identity on the Riemann sphere. -/
theorem mobius_identity_of_fixed_projected_cp1_triple
    (M : InfoGeometry.MobiusTransform) (p₁ p₂ p₃ : InfoGeometry.CP1)
    (h12 : p₁.toRiemannSphere ≠ p₂.toRiemannSphere)
    (h23 : p₂.toRiemannSphere ≠ p₃.toRiemannSphere)
    (h13 : p₁.toRiemannSphere ≠ p₃.toRiemannSphere)
    (h₁ : (M.actCP1 p₁).toRiemannSphere = p₁.toRiemannSphere)
    (h₂ : (M.actCP1 p₂).toRiemannSphere = p₂.toRiemannSphere)
    (h₃ : (M.actCP1 p₃).toRiemannSphere = p₃.toRiemannSphere) :
    ∀ z : InfoGeometry.RiemannSphere, M.eval z = z := by
  apply InfoGeometry.three_fixed_points_implies_identity M
    p₁.toRiemannSphere p₂.toRiemannSphere p₃.toRiemannSphere h12 h23 h13
  · simpa [InfoGeometry.MobiusTransform.is_fixed_point,
      InfoGeometry.mobius_action_correspondence M p₁] using h₁
  · simpa [InfoGeometry.MobiusTransform.is_fixed_point,
      InfoGeometry.mobius_action_correspondence M p₂] using h₂
  · simpa [InfoGeometry.MobiusTransform.is_fixed_point,
      InfoGeometry.mobius_action_correspondence M p₃] using h₃

/-- Three fixed projected `CP¹` points force the line part of the projected
`CP¹` incidence endomorphism to be the identity. -/
theorem mobiusCP1ProjectionHom_lineMap_eq_id_of_fixed_projected_cp1_triple
    (M : InfoGeometry.MobiusTransform) (p₁ p₂ p₃ : InfoGeometry.CP1)
    (h12 : p₁.toRiemannSphere ≠ p₂.toRiemannSphere)
    (h23 : p₂.toRiemannSphere ≠ p₃.toRiemannSphere)
    (h13 : p₁.toRiemannSphere ≠ p₃.toRiemannSphere)
    (h₁ : (M.actCP1 p₁).toRiemannSphere = p₁.toRiemannSphere)
    (h₂ : (M.actCP1 p₂).toRiemannSphere = p₂.toRiemannSphere)
    (h₃ : (M.actCP1 p₃).toRiemannSphere = p₃.toRiemannSphere) :
    (mobiusCP1ProjectionHom M).lineMap = id := by
  funext z
  exact mobius_identity_of_fixed_projected_cp1_triple M p₁ p₂ p₃ h12 h23 h13 h₁ h₂ h₃ z

/-- The doubled projected incidence endomorphism also has identity line map when
its underlying Möbius transform fixes three projected `CP¹` points. -/
theorem mobiusDoubledCP1ProjectionHom_lineMap_eq_id_of_fixed_projected_cp1_triple
    (M : InfoGeometry.MobiusTransform) (p₁ p₂ p₃ : InfoGeometry.CP1)
    (h12 : p₁.toRiemannSphere ≠ p₂.toRiemannSphere)
    (h23 : p₂.toRiemannSphere ≠ p₃.toRiemannSphere)
    (h13 : p₁.toRiemannSphere ≠ p₃.toRiemannSphere)
    (h₁ : (M.actCP1 p₁).toRiemannSphere = p₁.toRiemannSphere)
    (h₂ : (M.actCP1 p₂).toRiemannSphere = p₂.toRiemannSphere)
    (h₃ : (M.actCP1 p₃).toRiemannSphere = p₃.toRiemannSphere) :
    (mobiusDoubledCP1ProjectionHom M).lineMap = id := by
  funext z
  apply Prod.ext
  · exact mobius_identity_of_fixed_projected_cp1_triple M p₁ p₂ p₃ h12 h23 h13 h₁ h₂ h₃ z.1
  · exact mobius_identity_of_fixed_projected_cp1_triple M p₁ p₂ p₃ h12 h23 h13 h₁ h₂ h₃ z.2

/-- The tripled projected incidence endomorphism also has identity line map when
its underlying Möbius transform fixes three projected `CP¹` points. -/
theorem mobiusTripledCP1ProjectionHom_lineMap_eq_id_of_fixed_projected_cp1_triple
    (M : InfoGeometry.MobiusTransform) (p₁ p₂ p₃ : InfoGeometry.CP1)
    (h12 : p₁.toRiemannSphere ≠ p₂.toRiemannSphere)
    (h23 : p₂.toRiemannSphere ≠ p₃.toRiemannSphere)
    (h13 : p₁.toRiemannSphere ≠ p₃.toRiemannSphere)
    (h₁ : (M.actCP1 p₁).toRiemannSphere = p₁.toRiemannSphere)
    (h₂ : (M.actCP1 p₂).toRiemannSphere = p₂.toRiemannSphere)
    (h₃ : (M.actCP1 p₃).toRiemannSphere = p₃.toRiemannSphere) :
    (mobiusTripledCP1ProjectionHom M).lineMap = id := by
  funext z
  apply Prod.ext
  · exact mobius_identity_of_fixed_projected_cp1_triple M p₁ p₂ p₃ h12 h23 h13 h₁ h₂ h₃ z.1
  · apply Prod.ext
    · exact mobius_identity_of_fixed_projected_cp1_triple M p₁ p₂ p₃ h12 h23 h13 h₁ h₂ h₃ z.2.1
    · exact mobius_identity_of_fixed_projected_cp1_triple M p₁ p₂ p₃ h12 h23 h13 h₁ h₂ h₃ z.2.2

/-- Line cochains on the Riemann-sphere projection are unchanged by pullback
when the Möbius transform fixes three projected `CP¹` points. -/
theorem pullbackLineCochain_mobiusCP1ProjectionHom_eq_self_of_fixed_projected_cp1_triple
    (M : InfoGeometry.MobiusTransform) (p₁ p₂ p₃ : InfoGeometry.CP1)
    (h12 : p₁.toRiemannSphere ≠ p₂.toRiemannSphere)
    (h23 : p₂.toRiemannSphere ≠ p₃.toRiemannSphere)
    (h13 : p₁.toRiemannSphere ≠ p₃.toRiemannSphere)
    (h₁ : (M.actCP1 p₁).toRiemannSphere = p₁.toRiemannSphere)
    (h₂ : (M.actCP1 p₂).toRiemannSphere = p₂.toRiemannSphere)
    (h₃ : (M.actCP1 p₃).toRiemannSphere = p₃.toRiemannSphere)
    {C : Type*} (c : IncidenceGeometry.Hom.LineCochain cp1ProjectionIncidence C) :
    (mobiusCP1ProjectionHom M).pullbackLineCochain c = c := by
  funext z
  simp [IncidenceGeometry.Hom.pullbackLineCochain,
    mobius_identity_of_fixed_projected_cp1_triple M p₁ p₂ p₃ h12 h23 h13 h₁ h₂ h₃ z]

/-- Line cochains on doubled projected incidence are unchanged by pullback when
three projected `CP¹` points force the underlying Möbius line action to be the
identity. -/
theorem pullbackLineCochain_mobiusDoubledCP1ProjectionHom_eq_self_of_fixed_projected_cp1_triple
    (M : InfoGeometry.MobiusTransform) (p₁ p₂ p₃ : InfoGeometry.CP1)
    (h12 : p₁.toRiemannSphere ≠ p₂.toRiemannSphere)
    (h23 : p₂.toRiemannSphere ≠ p₃.toRiemannSphere)
    (h13 : p₁.toRiemannSphere ≠ p₃.toRiemannSphere)
    (h₁ : (M.actCP1 p₁).toRiemannSphere = p₁.toRiemannSphere)
    (h₂ : (M.actCP1 p₂).toRiemannSphere = p₂.toRiemannSphere)
    (h₃ : (M.actCP1 p₃).toRiemannSphere = p₃.toRiemannSphere)
    {C : Type*} (c : IncidenceGeometry.Hom.LineCochain doubledCP1ProjectionIncidence C) :
    (mobiusDoubledCP1ProjectionHom M).pullbackLineCochain c = c := by
  funext z
  simp [IncidenceGeometry.Hom.pullbackLineCochain,
    mobius_identity_of_fixed_projected_cp1_triple M p₁ p₂ p₃ h12 h23 h13 h₁ h₂ h₃ z.1,
    mobius_identity_of_fixed_projected_cp1_triple M p₁ p₂ p₃ h12 h23 h13 h₁ h₂ h₃ z.2]

/-- Line cochains on tripled projected incidence are unchanged by pullback when
three projected `CP¹` points force the underlying Möbius line action to be the
identity. -/
theorem pullbackLineCochain_mobiusTripledCP1ProjectionHom_eq_self_of_fixed_projected_cp1_triple
    (M : InfoGeometry.MobiusTransform) (p₁ p₂ p₃ : InfoGeometry.CP1)
    (h12 : p₁.toRiemannSphere ≠ p₂.toRiemannSphere)
    (h23 : p₂.toRiemannSphere ≠ p₃.toRiemannSphere)
    (h13 : p₁.toRiemannSphere ≠ p₃.toRiemannSphere)
    (h₁ : (M.actCP1 p₁).toRiemannSphere = p₁.toRiemannSphere)
    (h₂ : (M.actCP1 p₂).toRiemannSphere = p₂.toRiemannSphere)
    (h₃ : (M.actCP1 p₃).toRiemannSphere = p₃.toRiemannSphere)
    {C : Type*} (c : IncidenceGeometry.Hom.LineCochain tripledCP1ProjectionIncidence C) :
    (mobiusTripledCP1ProjectionHom M).pullbackLineCochain c = c := by
  funext z
  simp [IncidenceGeometry.Hom.pullbackLineCochain,
    mobius_identity_of_fixed_projected_cp1_triple M p₁ p₂ p₃ h12 h23 h13 h₁ h₂ h₃ z.1,
    mobius_identity_of_fixed_projected_cp1_triple M p₁ p₂ p₃ h12 h23 h13 h₁ h₂ h₃ z.2.1,
    mobius_identity_of_fixed_projected_cp1_triple M p₁ p₂ p₃ h12 h23 h13 h₁ h₂ h₃ z.2.2]

/-! ## Left/right Cartan--Peirce projector glue -/

/-- A Cartan involution packages the left/right projectors used as a theorem-safe
Peirce-style decomposition of a doubled carrier. -/
structure CartanProjectorPair (𝕜 E : Type*) [Field 𝕜] [Invertible (2 : 𝕜)]
    [AddCommGroup E] [Module 𝕜 E] where
  theta : Module.End 𝕜 E
  theta_sq : InfoGeometry.Cartan.IsCartanInvolution theta

namespace CartanProjectorPair

variable {𝕜 E : Type*} [Field 𝕜] [Invertible (2 : 𝕜)] [AddCommGroup E] [Module 𝕜 E]

/-- Left/plus projector from the Cartan owner. -/
abbrev left (D : CartanProjectorPair 𝕜 E) : Module.End 𝕜 E :=
  InfoGeometry.Cartan.Pplus D.theta

/-- Right/minus projector from the Cartan owner. -/
abbrev right (D : CartanProjectorPair 𝕜 E) : Module.End 𝕜 E :=
  InfoGeometry.Cartan.Pminus D.theta

@[simp] theorem left_idempotent (D : CartanProjectorPair 𝕜 E) :
    D.left * D.left = D.left :=
  InfoGeometry.Cartan.Pplus_idempotent D.theta D.theta_sq

@[simp] theorem right_idempotent (D : CartanProjectorPair 𝕜 E) :
    D.right * D.right = D.right :=
  InfoGeometry.Cartan.Pminus_idempotent D.theta D.theta_sq

@[simp] theorem left_right_orthogonal (D : CartanProjectorPair 𝕜 E) :
    D.left * D.right = 0 :=
  InfoGeometry.Cartan.Pplus_comp_Pminus D.theta D.theta_sq

@[simp] theorem right_left_orthogonal (D : CartanProjectorPair 𝕜 E) :
    D.right * D.left = 0 :=
  InfoGeometry.Cartan.Pminus_comp_Pplus D.theta D.theta_sq

@[simp] theorem left_add_right (D : CartanProjectorPair 𝕜 E) :
    D.left + D.right = 1 :=
  InfoGeometry.Cartan.Pplus_add_Pminus_eq_id D.theta

/-- Every vector decomposes into left and right projected parts. -/
theorem decompose (D : CartanProjectorPair 𝕜 E) (x : E) :
    x = D.left x + D.right x :=
  InfoGeometry.Cartan.decompose D.theta D.theta_sq x

end CartanProjectorPair

/-! ## Concrete doubled-carrier Peirce/Cartan split -/

/-- The sign involution on a doubled carrier: `+1` on the first sector and `-1`
on the second. -/
def doubledSignInvolution (𝕜 E : Type*) [Field 𝕜] [AddCommGroup E] [Module 𝕜 E] :
    Module.End 𝕜 (E × E) where
  toFun x := (x.1, -x.2)
  map_add' x y := by
    ext
    · simp
    · simp
      abel
  map_smul' r x := by ext <;> simp

/-- The doubled sign map is a Cartan involution. -/
theorem doubledSignInvolution_sq (𝕜 E : Type*) [Field 𝕜] [AddCommGroup E] [Module 𝕜 E] :
    InfoGeometry.Cartan.IsCartanInvolution (doubledSignInvolution 𝕜 E) := by
  ext x <;> simp [doubledSignInvolution]

/-- The canonical left/right projector glue on a doubled carrier. -/
def doubledLeftRightProjectors (𝕜 E : Type*) [Field 𝕜] [Invertible (2 : 𝕜)]
    [AddCommGroup E] [Module 𝕜 E] : CartanProjectorPair 𝕜 (E × E) where
  theta := doubledSignInvolution 𝕜 E
  theta_sq := doubledSignInvolution_sq 𝕜 E

private theorem inv_two_smul_add_inv_two_smul {𝕜 E : Type*} [Field 𝕜] [Invertible (2 : 𝕜)]
    [AddCommGroup E] [Module 𝕜 E] (x : E) :
    (2 : 𝕜)⁻¹ • x + (2 : 𝕜)⁻¹ • x = x := by
  rw [← two_smul 𝕜 ((2 : 𝕜)⁻¹ • x), smul_smul]
  have h2 : (2 : 𝕜) ≠ 0 := isUnit_iff_ne_zero.mp (isUnit_of_invertible (2 : 𝕜))
  rw [mul_inv_cancel₀ h2, one_smul]

/-- The left projector on the doubled sign decomposition keeps the first sector. -/
theorem doubledLeftRightProjectors_left_apply {𝕜 E : Type*} [Field 𝕜] [Invertible (2 : 𝕜)]
    [AddCommGroup E] [Module 𝕜 E] (x : E × E) :
    (doubledLeftRightProjectors 𝕜 E).left x = (x.1, 0) := by
  ext
  · simp [doubledLeftRightProjectors, CartanProjectorPair.left,
      InfoGeometry.Cartan.Pplus, doubledSignInvolution]
    exact inv_two_smul_add_inv_two_smul x.1
  · simp [doubledLeftRightProjectors, CartanProjectorPair.left,
      InfoGeometry.Cartan.Pplus, doubledSignInvolution]

/-- The right projector on the doubled sign decomposition keeps the second sector. -/
theorem doubledLeftRightProjectors_right_apply {𝕜 E : Type*} [Field 𝕜] [Invertible (2 : 𝕜)]
    [AddCommGroup E] [Module 𝕜 E] (x : E × E) :
    (doubledLeftRightProjectors 𝕜 E).right x = (0, x.2) := by
  ext
  · simp [doubledLeftRightProjectors, CartanProjectorPair.right,
      InfoGeometry.Cartan.Pminus, doubledSignInvolution]
  · simp [doubledLeftRightProjectors, CartanProjectorPair.right,
      InfoGeometry.Cartan.Pminus, doubledSignInvolution]
    exact inv_two_smul_add_inv_two_smul x.2

/-- The doubled carrier is the sum of its left and right projected sectors. -/
theorem doubledLeftRightProjectors_decompose {𝕜 E : Type*} [Field 𝕜] [Invertible (2 : 𝕜)]
    [AddCommGroup E] [Module 𝕜 E] (x : E × E) :
    x = (doubledLeftRightProjectors 𝕜 E).left x + (doubledLeftRightProjectors 𝕜 E).right x :=
  CartanProjectorPair.decompose (doubledLeftRightProjectors 𝕜 E) x

/-! ## Rolling-null-subalgebra to twistor incidence glue -/

open InfoGeometry.Lie.G2RollingBall
open InfoGeometry.Twistor.Incidence
open InfoGeometry.Clifford.Soldering

variable {A : Type*} [AddCommGroup A] [Module ℝ A] [Mul A] [Zero A]

/-- The rolling/null-subalgebra incidence geometry attached to a quadratic
readout `Q`.  Points and lines are both represented by null subalgebras; rank
predicates can be layered on top when independently proved. -/
def nullSubalgebraIncidence (Q : A → ℝ) : IncidenceGeometry where
  Point := NullSubalgebra (A := A) Q
  Line := NullSubalgebra (A := A) Q
  Inc := NullIncident

/-- The finite twistor incidence geometry already owned by `Twistor.Incidence`:
twistors are points and soldered spacetime vectors are lines/planes of
incidence. -/
def twistorIncidenceGeometry : IncidenceGeometry where
  Point := Twistor
  Line := Vec22
  Inc := Incident

/-- A quadratic-multiplicative automorphism acts as an incidence endomorphism of
the null-subalgebra geometry. -/
def QuadraticMulAut.nullIncidenceHom {Q : A → ℝ} (g : QuadraticMulAut (A := A) Q) :
    IncidenceGeometry.Hom (nullSubalgebraIncidence (A := A) Q)
      (nullSubalgebraIncidence (A := A) Q) where
  pointMap := g.mapNullSubalgebra
  lineMap := g.mapNullSubalgebra
  preserves_incidence' := by
    intro P L h
    exact g.preserves_null_incidence h

/-! ## Proven incidence propagation lemmas, with no new bridge hypotheses -/

variable {Q : A → ℝ}

/-- A quadratic-multiplicative automorphism preserves null-subalgebra incidence.
This is the direct owner theorem from the rolling/null-subalgebra layer, exposed
without inventing an extra gluing property. -/
theorem quadraticMulAut_preserves_null_incidence
    (g : QuadraticMulAut (A := A) Q)
    {P L : NullSubalgebra (A := A) Q}
    (h : NullIncident P L) :
    NullIncident (g.mapNullSubalgebra P) (g.mapNullSubalgebra L) :=
  g.preserves_null_incidence h

/-- The incidence-hom formulation of the preceding theorem. -/
theorem nullIncidenceHom_preserves
    (g : QuadraticMulAut (A := A) Q)
    {P L : NullSubalgebra (A := A) Q}
    (h : (nullSubalgebraIncidence (A := A) Q).Inc P L) :
    (nullSubalgebraIncidence (A := A) Q).Inc
      ((QuadraticMulAut.nullIncidenceHom g).pointMap P)
      ((QuadraticMulAut.nullIncidenceHom g).lineMap L) :=
  (QuadraticMulAut.nullIncidenceHom g).preserves_incidence' h

/-- Compatible point/line cochains on the null-subalgebra incidence geometry
remain compatible after a quadratic-multiplicative automorphism.  This is a
finite incidence-cochain statement, not a de Rham computation. -/
theorem null_incidence_compatible_pullback_by_quadraticMulAut
    (g : QuadraticMulAut (A := A) Q) {C : Type*}
    {α : IncidenceGeometry.Hom.PointCochain (nullSubalgebraIncidence (A := A) Q) C}
    {β : IncidenceGeometry.Hom.LineCochain (nullSubalgebraIncidence (A := A) Q) C}
    (h : IncidenceGeometry.Hom.Compatible α β) :
    IncidenceGeometry.Hom.Compatible
      ((QuadraticMulAut.nullIncidenceHom g).pullbackPointCochain α)
      ((QuadraticMulAut.nullIncidenceHom g).pullbackLineCochain β) :=
  IncidenceGeometry.Hom.compatible_pullback (QuadraticMulAut.nullIncidenceHom g) h

/-- Twistor incidence as an incidence-geometry statement implies the existing
finite null-separation theorem. -/
theorem twistor_incident_points_null_separated
    (Z : Twistor) (X Y : Vec22)
    (hX : twistorIncidenceGeometry.Inc Z X) (hY : twistorIncidenceGeometry.Inc Z Y)
    (hπ : Z.2 ≠ 0) :
    q22 (X - Y) = 0 :=
  incident_points_null_separated Z X Y hX hY hπ

/-- If two lines of the twistor incidence geometry are incident with the same
nonzero-primary-spinor twistor point, then their spacetime representatives are
null-separated. -/
theorem twistor_common_point_null_separation
    {Z : Twistor} {X Y : Vec22}
    (hX : twistorIncidenceGeometry.Inc Z X)
    (hY : twistorIncidenceGeometry.Inc Z Y)
    (hπ : Z.2 ≠ 0) :
    q22 (X - Y) = 0 :=
  twistor_incident_points_null_separated Z X Y hX hY hπ

/-- Compatible point/line cochains on twistor incidence pull back along any
incidence homomorphism into twistor incidence.  This is the honest functorial
cochain glue available without proving a global rolling/twistor equivalence. -/
theorem twistor_compatible_pullback
    {G : IncidenceGeometry} (f : IncidenceGeometry.Hom G twistorIncidenceGeometry)
    {C : Type*}
    {α : IncidenceGeometry.Hom.PointCochain twistorIncidenceGeometry C}
    {β : IncidenceGeometry.Hom.LineCochain twistorIncidenceGeometry C}
    (h : IncidenceGeometry.Hom.Compatible α β) :
    IncidenceGeometry.Hom.Compatible
      (f.pullbackPointCochain α) (f.pullbackLineCochain β) :=
  IncidenceGeometry.Hom.compatible_pullback f h

end InfoGeometry.Twistor.RollingSpinorMobiusBridge
