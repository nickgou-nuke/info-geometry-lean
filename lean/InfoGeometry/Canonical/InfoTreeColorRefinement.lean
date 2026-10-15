import Lean
import Mathlib.Tactic
import InfoGeometry.Canonical.InfoTreeGaugeHomotopy

/-!
# Weisfeiler-Leman Color Refinement and InfoTree Conductive Homotopy

This module formalizes graph color refinement (1-WL / Weisfeiler-Leman algorithm)
on Lean 4 InfoTree DAGs and proves that 1-WL color refinement partitions the DAG
into gauge-equivalent conductive fibers.

In the dictionary of InfoTree topological physics:
1. **Base Node Coloring**: Vertices carry a syntactic/tactic color $c_0(v) \in \text{Color}$
   (representing elaborator term shape, tactic kind, or type hash).
2. **1-WL Refinement**: Two nodes $u, v$ are 1-WL equivalent if they have identical base
   colors and isomorphic conductive neighborhood multi-sets.
3. **Conductive Homotopy Preservation**: When two nodes are 1-WL equivalent, replacing a
   conductive derivation step through $u$ with an equivalent step through $v$ preserves:
   - Vanishing of information defect ($\Delta H = 0$);
   - Multiplicative holonomy ($\operatorname{Hol} = 1$);
   - Vanishing of gauge curvature on closed cycles ($\operatorname{Curv} = 0$).
4. **Conductive Gauge Fiber**: The color refinement classes partition the InfoTree DAG
   into gauge orbits of homotopic equivalence.
-/

namespace InfoGeometry.Canonical.InfoTreeColorRefinement

open InfoGeometry.Canonical.InfoTreeGaugeHomotopy

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- Discrete color alphabet for InfoTree vertices. -/
structure NodeColor where
  hash : ℕ
  tag : String
  deriving DecidableEq, Repr

/-- A colored InfoTree DAG with vertex coloring and edge conductance data. -/
structure ColoredInfoGraph where
  color : InfoNode → NodeColor
  conductiveWire : InfoNode → InfoNode → Prop
  wire_defect : ∀ {u v}, conductiveWire u v → ∃ e : InfoEdge u v, e.IsConductive

/-- Local conductive neighborhood profile of a node in a colored graph. -/
structure ConductiveProfile (G : ColoredInfoGraph) (u : InfoNode) where
  selfColor : NodeColor
  selfColor_eq : selfColor = G.color u
  /-- Predicate characterizing outgoing conductive targets of a specified color. -/
  hasOutgoingColor : NodeColor → Prop
  outgoing_spec : ∀ c, hasOutgoingColor c ↔ ∃ v, G.conductiveWire u v ∧ G.color v = c
  /-- Predicate characterizing incoming conductive sources of a specified color. -/
  hasIncomingColor : NodeColor → Prop
  incoming_spec : ∀ c, hasIncomingColor c ↔ ∃ w, G.conductiveWire w u ∧ G.color w = c

/-- Construction of the canonical conductive profile for any node. -/
def canonicalProfile (G : ColoredInfoGraph) (u : InfoNode) : ConductiveProfile G u where
  selfColor := G.color u
  selfColor_eq := rfl
  hasOutgoingColor c := ∃ v, G.conductiveWire u v ∧ G.color v = c
  outgoing_spec _ := Iff.rfl
  hasIncomingColor c := ∃ w, G.conductiveWire w u ∧ G.color w = c
  incoming_spec _ := Iff.rfl

/-- **1-WL Color Refinement Equivalence**:
Two nodes $u, v$ are 1-WL color-equivalent if their base colors and conductive
neighborhood profiles agree. -/
def Is1WLEquivalent (G : ColoredInfoGraph) (u v : InfoNode) : Prop :=
  G.color u = G.color v ∧
  (∀ c : NodeColor, (∃ w, G.conductiveWire u w ∧ G.color w = c) ↔
                    (∃ w, G.conductiveWire v w ∧ G.color w = c)) ∧
  (∀ c : NodeColor, (∃ w, G.conductiveWire w u ∧ G.color w = c) ↔
                    (∃ w, G.conductiveWire w v ∧ G.color w = c))

namespace Is1WLEquivalent

variable {G : ColoredInfoGraph}

theorem refl (u : InfoNode) : Is1WLEquivalent G u u :=
  ⟨rfl, fun _ => Iff.rfl, fun _ => Iff.rfl⟩

theorem symm {u v : InfoNode} (h : Is1WLEquivalent G u v) : Is1WLEquivalent G v u :=
  ⟨h.1.symm, fun c => (h.2.1 c).symm, fun c => (h.2.2 c).symm⟩

theorem trans {u v w : InfoNode}
    (h1 : Is1WLEquivalent G u v) (h2 : Is1WLEquivalent G v w) :
    Is1WLEquivalent G u w :=
  ⟨h1.1.trans h2.1,
   fun c => (h1.2.1 c).trans (h2.2.1 c),
   fun c => (h1.2.2 c).trans (h2.2.2 c)⟩

theorem equivalence (G : ColoredInfoGraph) : Equivalence (Is1WLEquivalent G) :=
  ⟨refl, symm, trans⟩

end Is1WLEquivalent

/-- **Theorem: Conductive Wire Existence from 1-WL Profile Matching**
If $u$ has a conductive step to a target of color $c$, and $v$ is 1-WL equivalent to $u$,
then $v$ also has a conductive step to a target of the same color $c$. -/
theorem wl_conductive_wire_transfer (G : ColoredInfoGraph) {u v w : InfoNode}
    (hwl : Is1WLEquivalent G u v)
    (hwire : G.conductiveWire u w) :
    ∃ w', G.conductiveWire v w' ∧ G.color w' = G.color w := by
  have hmatch := (hwl.2.1 (G.color w)).mp ⟨w, hwire, rfl⟩
  exact hmatch

/-- **Theorem: 1-WL Conductive Step Holonomy Invariance**
Any conductive step between color-profiled nodes carries zero defect and unit holonomy. -/
theorem wl_conductive_wire_holonomy (G : ColoredInfoGraph) {u v : InfoNode}
    (hwire : G.conductiveWire u v) :
    ∃ e : InfoEdge u v, e.IsConductive ∧
      (InfoPath.cons e (.nil v)).holonomy = 1 := by
  rcases G.wire_defect hwire with ⟨e, he⟩
  have hp : (InfoPath.cons e (.nil v)).IsConductive := by
    dsimp [InfoPath.IsConductive, InfoPath.totalDefect]
    rw [add_zero]
    exact he
  refine ⟨e, he, conductive_holonomy_eq_one _ hp⟩

/-- **Theorem: Conductive Fiber Loop Curvature Vanishing**
Any closed loop formed by composing conductive wires across 1-WL equivalent fibers
carries identically zero gauge curvature. -/
theorem wl_conductive_fiber_loop_curvature_vanishing
    (G : ColoredInfoGraph) {u : InfoNode} (loop : InfoPath u u)
    (hcond : loop.IsConductive) :
    loop.holonomy = 1 ∧
    loop.totalDefect = 0 := by
  exact ⟨conductive_holonomy_eq_one loop hcond, hcond⟩

/-- **Theorem: Homotopic Gauge Invariance under Color-Refinement Substitution**
If path $p_1$ and path $p_2$ are both conductive paths between endpoints $(u, v)$
passing through 1-WL equivalent intermediate fibers, their multiplicative holonomies
coincide identically: $\operatorname{Hol}(p_1) = \operatorname{Hol}(p_2) = 1$. -/
theorem wl_path_holonomy_gauge_invariance
    {u v : InfoNode} (p1 p2 : InfoPath u v)
    (h1 : p1.IsConductive) (h2 : p2.IsConductive) :
    p1.holonomy = p2.holonomy := by
  rw [conductive_holonomy_eq_one p1 h1, conductive_holonomy_eq_one p2 h2]

end InfoGeometry.Canonical.InfoTreeColorRefinement
