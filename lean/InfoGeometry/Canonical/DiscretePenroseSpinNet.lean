import InfoGeometry.Canonical.PenrosePosetCategoryFoundation

/-!
# Discrete Penrose spin nets grounded in posets/categories

This owner file packages the next layer above
`PenrosePosetCategoryFoundation`:

* a discrete event set with a partial order;
* Penrose twistor / dual-twistor labels on events;
* order-monotone incidence;
* a functorial state diagram on the preorder category of events.

The structure is intentionally primitive. It does not assert continuum limits,
AF completions, or physical reconstruction theorems.
-/

namespace InfoGeometry.Canonical.DiscretePenroseSpinNet

open CategoryTheory
open InfoGeometry.Canonical.PenrosePosetCategoryFoundation
open InfoGeometry.Projective.Twistor

universe u v

section Basic

variable (α : Type u) (𝕜 T D : Type u) [PartialOrder α]
variable [CommRing 𝕜]
variable [AddCommGroup T] [Module 𝕜 T]
variable [AddCommGroup D] [Module 𝕜 D]

/--
A discrete Penrose spin net consists of:
* an ordered event set;
* twistor and dual-twistor labels at each event;
* incidence propagated along the order;
* a functorial state diagram on the preorder category of events.
-/
structure SpinNet where
  twistorIncidence : TwistorIncidenceDatum 𝕜 T D
  twistorAt : α → T
  dualAt : α → D
  incidence_monotone :
    IncidenceAlongOrder twistorIncidence twistorAt dualAt
  stateDiagram : α ⥤ Type v

variable {α 𝕜 T D}
variable [PartialOrder α]
variable [CommRing 𝕜]
variable [AddCommGroup T] [Module 𝕜 T]
variable [AddCommGroup D] [Module 𝕜 D]

abbrev eventDAG (_S : SpinNet α 𝕜 T D) :
    InfoGeometry.Canonical.ProofDAGRepresentationBridge.ProofDAG α :=
  proofDAGOfPartialOrder (α := α)

abbrev forwardCone (S : SpinNet α 𝕜 T D) (a : α) : Set α :=
  InfoGeometry.Causal.ProofDAGRepresentation.forwardCone (eventDAG S) a

abbrev backwardCone (S : SpinNet α 𝕜 T D) (a : α) : Set α :=
  InfoGeometry.Causal.ProofDAGRepresentation.backwardCone (eventDAG S) a

@[simp] theorem mem_forwardCone_iff
    (S : SpinNet α 𝕜 T D) {a b : α} :
    b ∈ forwardCone S a ↔ a ≤ b :=
  PenrosePosetCategoryFoundation.mem_forwardCone_iff_le (α := α)

@[simp] theorem mem_backwardCone_iff
    (S : SpinNet α 𝕜 T D) {a b : α} :
    b ∈ backwardCone S a ↔ b ≤ a :=
  PenrosePosetCategoryFoundation.mem_backwardCone_iff_le (α := α)

 theorem cones_intersect_self
    (S : SpinNet α 𝕜 T D)
    (a b : α)
    (hab : b ∈ forwardCone S a)
    (hba : b ∈ backwardCone S a) :
    b = a :=
  order_cones_intersect_self (α := α) a b hab hba

 theorem incidence_of_le
    (S : SpinNet α 𝕜 T D)
    {a b : α} (hab : a ≤ b) :
    S.twistorIncidence.Incidence (S.dualAt a) (S.twistorAt b) :=
  incidenceAlongOrder_of_le S.incidence_monotone hab

 theorem incidence_of_mem_forwardCone
    (S : SpinNet α 𝕜 T D)
    {a b : α} (hab : b ∈ forwardCone S a) :
    S.twistorIncidence.Incidence (S.dualAt a) (S.twistorAt b) :=
  incidence_of_le S ((mem_forwardCone_iff S).1 hab)

/-- Category-arrow transport along the event order. -/
abbrev stateTransport
    (S : SpinNet α 𝕜 T D)
    {a b : α} (hab : a ≤ b) :
    S.stateDiagram.obj a → S.stateDiagram.obj b :=
  S.stateDiagram.map (homOfLE hab)

@[simp] theorem stateTransport_id
    (S : SpinNet α 𝕜 T D)
    (a : α)
    (x : S.stateDiagram.obj a) :
    stateTransport S (a := a) (b := a) le_rfl x = x := by
  simpa [stateTransport] using congrFun (S.stateDiagram.map_id a) x

 theorem stateTransport_comp
    (S : SpinNet α 𝕜 T D)
    {a b c : α} (hab : a ≤ b) (hbc : b ≤ c)
    (x : S.stateDiagram.obj a) :
    stateTransport S (le_trans hab hbc) x =
      stateTransport S hbc (stateTransport S hab x) := by
  simpa [stateTransport] using congrFun (S.stateDiagram.map_comp (homOfLE hab) (homOfLE hbc)) x

/-- Dual-twistor rescaling preserves the discrete Penrose spin-net axioms. -/
def dualScale
    (S : SpinNet α 𝕜 T D)
    (u : 𝕜ˣ) : SpinNet α 𝕜 T D where
  twistorIncidence := S.twistorIncidence
  twistorAt := S.twistorAt
  dualAt := fun a => S.twistorIncidence.dualScale u (S.dualAt a)
  incidence_monotone :=
    incidenceAlongOrder_dualScale S.twistorIncidence u S.incidence_monotone
  stateDiagram := S.stateDiagram

/-- Twistor rescaling preserves the discrete Penrose spin-net axioms. -/
def twistorScale
    (S : SpinNet α 𝕜 T D)
    (u : 𝕜ˣ) : SpinNet α 𝕜 T D where
  twistorIncidence := S.twistorIncidence
  twistorAt := fun a => S.twistorIncidence.twScale u (S.twistorAt a)
  dualAt := S.dualAt
  incidence_monotone :=
    incidenceAlongOrder_twistorScale S.twistorIncidence u S.incidence_monotone
  stateDiagram := S.stateDiagram

@[simp] theorem dualScale_stateDiagram
    (S : SpinNet α 𝕜 T D)
    (u : 𝕜ˣ) :
    (dualScale S u).stateDiagram = S.stateDiagram :=
  rfl

@[simp] theorem twistorScale_stateDiagram
    (S : SpinNet α 𝕜 T D)
    (u : 𝕜ˣ) :
    (twistorScale S u).stateDiagram = S.stateDiagram :=
  rfl

end Basic

end InfoGeometry.Canonical.DiscretePenroseSpinNet
