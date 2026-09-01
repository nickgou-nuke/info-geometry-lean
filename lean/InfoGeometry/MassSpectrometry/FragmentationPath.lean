import Mathlib
import InfoGeometry.MassSpectrometry.StochasticFragmentGrammar
import InfoGeometry.MassSpectrometry.ValuedFragmentationDAG

/-!
# Typed fragmentation paths

Unlike the list-level grammar API, `ValidPath` carries proof that every step is
an edge of the fragmentation DAG.  Concatenation is structural, and additive
path surprisal is proved directly by induction.
-/

noncomputable section

namespace InfoGeometry.MassSpectrometry

namespace FragmentationDAG

variable {n : ℕ} (D : FragmentationDAG n)

/-- Proof-carrying directed path in the fragmentation DAG. -/
inductive ValidPath : Fin n → Fin n → Type
  | nil (v : Fin n) : ValidPath v v
  | cons {u v w : Fin n} (edge : D.edge u v) (rest : ValidPath v w) : ValidPath u w

namespace ValidPath

/-- Concatenation of proof-carrying fragmentation paths. -/
def concat {u v w : Fin n} :
    D.ValidPath u v → D.ValidPath v w → D.ValidPath u w
  | .nil _, q => q
  | .cons h p, q => .cons h (concat p q)

@[simp] theorem concat_nil_left {u v : Fin n} (p : D.ValidPath u v) :
    concat (.nil u) p = p := rfl

/-- Edge labels underlying a valid path. -/
def edges {u v : Fin n} : D.ValidPath u v → List (FragmentEdge n)
  | .nil _ => []
  | .cons (u := a) (v := b) h rest => (a, b) :: edges rest

@[simp] theorem edges_nil (u : Fin n) :
    edges (D := D) (.nil u) = [] := rfl

@[simp] theorem edges_cons {u v w : Fin n}
    (h : D.edge u v) (rest : D.ValidPath v w) :
    edges (D := D) (.cons h rest) = (u, v) :: edges rest := rfl

/-- Edge lists respect path concatenation. -/
theorem edges_concat {u v w : Fin n}
    (p : D.ValidPath u v) (q : D.ValidPath v w) :
    edges (D := D) (concat p q) = edges p ++ edges q := by
  induction p with
  | nil x => rfl
  | cons h rest ih =>
      simp [concat, edges, ih]

/-- Every valid nontrivial path strictly decreases the abstract DAG rank. -/
theorem rank_lt_of_cons {u v w : Fin n}
    (h : D.edge u v) (rest : D.ValidPath v w) :
    D.rank w < D.rank u := by
  induction rest with
  | nil x => simpa using D.rank_decreases h
  | cons h₂ rest ih =>
      exact Nat.lt_trans ih (D.rank_decreases h)

end ValidPath

end FragmentationDAG

namespace StochasticGrammar

variable {n : ℕ} {D : FragmentationDAG n} (G : StochasticGrammar D)

/-- Surprisal of a proof-carrying fragmentation path. -/
def validPathSurprisal {u v : Fin n} (p : D.ValidPath u v) : ℝ :=
  G.pathSurprisal (FragmentationDAG.ValidPath.edges p)

/-- Probability weight of a proof-carrying fragmentation path. -/
def validPathProbability {u v : Fin n} (p : D.ValidPath u v) : ℝ :=
  G.pathProbability (FragmentationDAG.ValidPath.edges p)

/-- Surprisal is additive under concatenation of valid fragmentation paths. -/
theorem validPathSurprisal_concat {u v w : Fin n}
    (p : D.ValidPath u v) (q : D.ValidPath v w) :
    G.validPathSurprisal (FragmentationDAG.ValidPath.concat p q) =
      G.validPathSurprisal p + G.validPathSurprisal q := by
  induction p with
  | nil x => simp [validPathSurprisal, FragmentationDAG.ValidPath.concat,
      FragmentationDAG.ValidPath.edges, pathSurprisal]
  | cons h rest ih =>
      simp [validPathSurprisal, FragmentationDAG.ValidPath.concat,
        FragmentationDAG.ValidPath.edges, pathSurprisal, ih, add_assoc]

/-- Path probability is multiplicative under valid-path concatenation. -/
theorem validPathProbability_concat {u v w : Fin n}
    (p : D.ValidPath u v) (q : D.ValidPath v w) :
    G.validPathProbability (FragmentationDAG.ValidPath.concat p q) =
      G.validPathProbability p * G.validPathProbability q := by
  induction p with
  | nil x => simp [validPathProbability, FragmentationDAG.ValidPath.concat,
      FragmentationDAG.ValidPath.edges, pathProbability]
  | cons h rest ih =>
      simp [validPathProbability, FragmentationDAG.ValidPath.concat,
        FragmentationDAG.ValidPath.edges, pathProbability, ih, mul_assoc]

end StochasticGrammar

end InfoGeometry.MassSpectrometry
