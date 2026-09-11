import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace DiscreteMaxFlowMinCut

namespace Generic

open Classical

/-- A finite directed network with real-valued capacities. -/
structure Network (V : Type*) where
  cap : V → V → ℝ
  s : V
  t : V

/-- A feasible flow assignment on every ordered vertex pair. -/
structure Flow {V : Type*} [Fintype V] (N : Network V) where
  f : V → V → ℝ
  capacity_bound : ∀ u v : V, f u v ≤ N.cap u v
  nonneg : ∀ u v : V, 0 ≤ f u v
  conservation : ∀ u : V, u ≠ N.s → u ≠ N.t →
    (∑ v : V, f u v) - (∑ v : V, f v u) = 0

/-- A source/sink separating cut. -/
structure Cut {V : Type*} (N : Network V) where
  S : Finset V
  s_in : N.s ∈ S
  t_out : N.t ∉ S

/-- The usual net value of a flow: total out of the source minus total into it. -/
noncomputable def flowValue {V : Type*} [Fintype V]
    {N : Network V} (F : Flow N) : ℝ :=
  (∑ v : V, F.f N.s v) - (∑ v : V, F.f v N.s)

/-- Capacity of a finite cut. -/
noncomputable def cutCapacity {V : Type*} [Fintype V] [DecidableEq V]
    {N : Network V} (C : Cut N) : ℝ :=
  Finset.sum C.S (fun u => Finset.sum C.Sᶜ (fun v => N.cap u v))

/-- Net flow crossing from the source side of a cut to its complement. -/
noncomputable def cutNetFlow {V : Type*} [Fintype V] [DecidableEq V]
    {N : Network V} (F : Flow N) (C : Cut N) : ℝ :=
  Finset.sum C.S (fun u => Finset.sum C.Sᶜ (fun v => F.f u v)) -
  Finset.sum C.S (fun u => Finset.sum C.Sᶜ (fun v => F.f v u))

/-- Residual capacity from `u` to `v`: unused forward capacity plus cancellable reverse flow. -/
def residualCapacity {V : Type*} [Fintype V] {N : Network V} (F : Flow N) (u v : V) : ℝ :=
  (N.cap u v - F.f u v) + F.f v u

/-- A list is an augmenting path when it starts at the source, ends at the sink,
and each adjacent residual edge has positive capacity. -/
def IsAugmentingPath {V : Type*} [Fintype V] {N : Network V}
    (F : Flow N) (p : List V) : Prop :=
  p.head? = some N.s ∧
  p.getLast? = some N.t ∧
  p.IsChain (fun u v => residualCapacity F u v > 0)

/-- Residual reachability via a positive-capacity path. -/
def Reachable {V : Type*} [Fintype V] {N : Network V}
    (F : Flow N) (u v : V) : Prop :=
  ∃ p : List V,
    p.head? = some u ∧
    p.getLast? = some v ∧
    p.IsChain (fun x y => residualCapacity F x y > 0)

/-- Every vertex reaches itself by the singleton path. -/
theorem reachable_refl {V : Type*} [Fintype V] {N : Network V} (F : Flow N) (u : V) :
    Reachable F u u := by
  refine ⟨[u], ?_, ?_, ?_⟩ <;> simp

/-- Residual reachability is closed under one positive residual edge. -/
theorem reachable_of_reachable_of_pos {V : Type*} [Fintype V] {N : Network V}
    (F : Flow N) {u v w : V} (hreachable : Reachable F u v)
    (hstep : residualCapacity F v w > 0) :
    Reachable F u w := by
  rcases hreachable with ⟨p, hhead, hlast, hchain⟩
  refine ⟨p ++ [w], ?_, ?_, ?_⟩
  · have hp_ne : p ≠ [] := by
      intro hp
      simp [hp] at hhead
    simpa [List.head?_append_of_ne_nil _ hp_ne] using hhead
  · simp
  · refine hchain.append (List.isChain_singleton w) ?_
    intro x hx y hy
    have hxv : x = v := by
      have hxv' : v = x := by
        simpa [hlast] using hx
      exact hxv'.symm
    have hyw : y = w := by
      have hyw' : w = y := by
        simpa using hy
      exact hyw'.symm
    subst hxv
    subst hyw
    exact hstep

/-- The cut induced by the residual vertices reachable from the source. -/
noncomputable def residualCut {V : Type*} [Fintype V] [DecidableEq V]
    {N : Network V} (F : Flow N)
    (no_path : ¬ Reachable F N.s N.t) : Cut N where
  S := Finset.univ.filter (fun v : V => Reachable F N.s v)
  s_in := by
    simp [reachable_refl]
  t_out := by
    simpa using no_path

/-- If `u` is on the source side of the residual cut and `v` is outside it,
then the residual edge `u → v` cannot have positive capacity. -/
theorem residualCapacity_nonpos_of_mem_residualCut {V : Type*} [Fintype V] [DecidableEq V]
    {N : Network V} (F : Flow N) (no_path : ¬ Reachable F N.s N.t)
    {u v : V} (hu : u ∈ (residualCut F no_path).S)
    (hv : v ∉ (residualCut F no_path).S) :
    residualCapacity F u v ≤ 0 := by
  by_contra hnonpos
  have hpos : residualCapacity F u v > 0 := lt_of_not_ge hnonpos
  have hreachable_u : Reachable F N.s u := by
    simpa [residualCut] using hu
  have hreachable_v : Reachable F N.s v :=
    reachable_of_reachable_of_pos F hreachable_u hpos
  have hv_mem : v ∈ (residualCut F no_path).S := by
    simpa [residualCut] using hreachable_v
  exact hv hv_mem

/-- A crossing edge of the residual cut is saturated by capacity boundedness and
nonnegativity from the feasible `Flow` structure. -/
theorem edge_saturation_of_mem_residualCut {V : Type*} [Fintype V] [DecidableEq V]
    {N : Network V} (F : Flow N) (no_path : ¬ Reachable F N.s N.t)
    {u v : V} (hu : u ∈ (residualCut F no_path).S)
    (hv : v ∉ (residualCut F no_path).S) :
    F.f u v = N.cap u v ∧ F.f v u = 0 := by
  have hres_nonpos :
      (N.cap u v - F.f u v) + F.f v u ≤ 0 := by
    simpa [residualCapacity] using
      residualCapacity_nonpos_of_mem_residualCut F no_path hu hv
  have hforward_nonneg : 0 ≤ N.cap u v - F.f u v := by
    linarith [F.capacity_bound u v]
  have hbackward_nonneg : 0 ≤ F.f v u := F.nonneg v u
  have hforward_zero : N.cap u v - F.f u v = 0 := by
    linarith
  have hbackward_zero : F.f v u = 0 := by
    linarith
  constructor
  · linarith
  · exact hbackward_zero

/-- If all non-source vertices in a cut satisfy flow conservation, the source
flow value is the net flow crossing that cut. -/
theorem flowValue_eq_cutNetFlow_of_conservation {V : Type*} [Fintype V] [DecidableEq V]
    {N : Network V} (F : Flow N) (C : Cut N)
    (hconserve : ∀ u : V, u ∈ C.S → u ≠ N.s →
      (∑ v : V, F.f u v) - (∑ v : V, F.f v u) = 0) :
    flowValue F = cutNetFlow F C := by
  let netAt : V → ℝ := fun u => (∑ v : V, F.f u v) - (∑ v : V, F.f v u)
  have hsum_source : flowValue F = Finset.sum C.S netAt := by
    rw [flowValue]
    symm
    refine Finset.sum_eq_single N.s ?_ ?_
    · intro u hu hne
      exact hconserve u hu hne
    · intro hs_notin
      exact False.elim (hs_notin C.s_in)
  have hsum_cut : Finset.sum C.S netAt = cutNetFlow F C := by
    simp only [netAt, cutNetFlow]
    rw [Finset.sum_sub_distrib]
    have hsplit_out :
        ∀ u : V,
          (∑ v : V, F.f u v) =
            Finset.sum C.S (fun v => F.f u v) + Finset.sum C.Sᶜ (fun v => F.f u v) := by
      intro u
      exact (Finset.sum_add_sum_compl C.S (fun v => F.f u v)).symm
    have hsplit_in :
        ∀ u : V,
          (∑ v : V, F.f v u) =
            Finset.sum C.S (fun v => F.f v u) + Finset.sum C.Sᶜ (fun v => F.f v u) := by
      intro u
      exact (Finset.sum_add_sum_compl C.S (fun v => F.f v u)).symm
    simp_rw [hsplit_out, hsplit_in]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    have hinternal :
        Finset.sum C.S (fun u => Finset.sum C.S (fun v => F.f u v)) =
          Finset.sum C.S (fun u => Finset.sum C.S (fun v => F.f v u)) := by
      exact Finset.sum_comm
    linarith
  exact hsum_source.trans hsum_cut

/-- Once the usual cut-decomposition identity has been proved for a feasible flow,
the residual cut saturation lemma turns it directly into equality with cut capacity. -/
theorem flow_equals_cutCapacity_of_cutNetFlow_eq {V : Type*} [Fintype V] [DecidableEq V]
    {N : Network V} (F : Flow N) (no_path : ¬ Reachable F N.s N.t)
    (hcut_decomp : flowValue F = cutNetFlow F (residualCut F no_path)) :
    flowValue F = cutCapacity (residualCut F no_path) := by
  rw [hcut_decomp, cutNetFlow, cutCapacity]
  have hforward :
      Finset.sum (residualCut F no_path).S
        (fun u => Finset.sum (residualCut F no_path).Sᶜ (fun v => F.f u v))
        =
      Finset.sum (residualCut F no_path).S
        (fun u => Finset.sum (residualCut F no_path).Sᶜ (fun v => N.cap u v)) := by
    refine Finset.sum_congr rfl ?_
    intro u hu
    refine Finset.sum_congr rfl ?_
    intro v hv
    have hv_not : v ∉ (residualCut F no_path).S := by
      simpa using hv
    exact (edge_saturation_of_mem_residualCut F no_path hu hv_not).1
  have hbackward :
      Finset.sum (residualCut F no_path).S
        (fun u => Finset.sum (residualCut F no_path).Sᶜ (fun v => F.f v u))
        = 0 := by
    refine Finset.sum_eq_zero ?_
    intro u hu
    refine Finset.sum_eq_zero ?_
    intro v hv
    have hv_not : v ∉ (residualCut F no_path).S := by
      simpa using hv
    exact (edge_saturation_of_mem_residualCut F no_path hu hv_not).2
  rw [hforward, hbackward, sub_zero]

/-- Feasible-flow version of Ford-Fulkerson optimality, using the fields bundled
into `Flow`. -/
theorem flow_equals_cut_if_no_path_of_feasible {V : Type*} [Fintype V] [DecidableEq V]
    {N : Network V} (F : Flow N) (no_path : ¬ Reachable F N.s N.t) :
    flowValue F = cutCapacity (residualCut F no_path) := by
  refine flow_equals_cutCapacity_of_cutNetFlow_eq F no_path ?_
  refine flowValue_eq_cutNetFlow_of_conservation F (residualCut F no_path) ?_
  intro u hu hsource
  have hsink : u ≠ N.t := by
    intro hut
    exact (residualCut F no_path).t_out (hut ▸ hu)
  exact F.conservation u hsource hsink

/-- Ford-Fulkerson optimality statement: if no residual `s`-`t` path exists, the
current flow value is the capacity of the residual reachability cut. -/
theorem flow_equals_cut_if_no_path {V : Type*} [Fintype V] [DecidableEq V]
    {N : Network V} (F : Flow N) (no_path : ¬ Reachable F N.s N.t) :
    flowValue F = cutCapacity (residualCut F no_path) := by
  exact flow_equals_cut_if_no_path_of_feasible F no_path

end Generic

/--
3-node directed toy network used in a fully concrete max-flow/min-cut check.

Nodes are `0,1,2` with edges and capacities:
* `0 → 1` : 3
* `1 → 2` : 2
* `0 → 2` : 1
-/

abbrev Node := Fin 3

/-- Edge capacities, zero elsewhere. -/
def cap01 : ℕ := 3

def cap12 : ℕ := 2

def cap02 : ℕ := 1

def capacity : Node → Node → ℕ
| 0, 1 => cap01
| 1, 2 => cap12
| 0, 2 => cap02
| _, _ => 0

def source : Node := 0
def sink : Node := 2

/-- Flow tuple for the only nontrivial edges: `(f01, f12, f02)`. -/
def FlowTriple : Type := ℕ × (ℕ × ℕ)

/-- Explicit finite brute-force domain for all possible bounded flow tuples. -/
def flowCandidates : Finset FlowTriple :=
  (Finset.range (cap01 + 1)).product ((Finset.range (cap12 + 1)).product (Finset.range (cap02 + 1)))

/-- Conservation at node `1` (with all capacities already respected by construction). -/
def feasibleFlow (p : FlowTriple) : Prop :=
  let f01 : ℕ := p.1
  let f12 : ℕ := p.2.1
  f01 = f12

instance : DecidablePred feasibleFlow := by
  intro p
  dsimp [feasibleFlow]
  infer_instance
/-- Brute-force feasible set (bounded and flow-conserving at node `1`). -/
def feasibleFlowCandidates : Finset FlowTriple :=
  flowCandidates.filter (fun p => feasibleFlow p)

/-- Net flow value for a feasible flow tuple: out at source = `f12 + f02`. -/
def flowValue (p : FlowTriple) : ℕ :=
  let f12 : ℕ := p.2.1
  let f02 : ℕ := p.2.2
  f12 + f02

/-- Max-flow for this toy instance by brute-force over bounded feasible flows. -/
def maxFlowValue : ℕ :=
  Finset.sup feasibleFlowCandidates flowValue

/-- Two source–sink separating cuts for this graph: `{source}` and `{source, 1}`. -/
def cut0 : Finset Node := {source}
def cut01 : Finset Node := {source, 1}

/-- Capacity of a cut under the fixed edge list. -/
def cutCost (S : Finset Node) : ℕ :=
  let c01 : ℕ := if (0 ∈ S) ∧ (1 ∉ S) then capacity 0 1 else 0
  let c12 : ℕ := if (1 ∈ S) ∧ (2 ∉ S) then capacity 1 2 else 0
  let c02 : ℕ := if (0 ∈ S) ∧ (2 ∉ S) then capacity 0 2 else 0
  c01 + c12 + c02

/-- Min-cut as min over the two admissible source–sink cuts in this toy graph. -/
def minCutValue : ℕ := min (cutCost cut0) (cutCost cut01)

/-- Brute-force max-flow equals min-cut for this fixed finite model. -/
theorem maxFlow_eq_minCut : maxFlowValue = minCutValue := by
  native_decide

/-- Numerical check: both sides are `3`. -/
theorem maxFlow_eq_three : maxFlowValue = 3 := by
  native_decide

theorem minCut_eq_three : minCutValue = 3 := by
  native_decide

/-- For transparency, record the cut costs explicitly. -/
theorem cut_costs : cutCost cut0 = 4 ∧ cutCost cut01 = 3 := by
  decide

end DiscreteMaxFlowMinCut
