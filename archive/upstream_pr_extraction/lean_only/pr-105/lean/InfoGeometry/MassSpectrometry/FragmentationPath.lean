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
def concat {u v w : Fin n} (p : D.ValidPath u v) (q : D.ValidPath v w) :
    D.ValidPath u w :=
  match p with
  | .nil _ => q
  | .cons h p => .cons h (concat p q)

@[simp] theorem concat_nil_left {u v : Fin n} (p : D.ValidPath u v) :
    concat D (ValidPath.nil u) p = p := rfl

/-- Edge labels underlying a valid path. -/
def edges (D : FragmentationDAG n) {u v : Fin n} : D.ValidPath u v → List (FragmentEdge n)
  | .nil _ => []
  | .cons (u := a) (v := b) h rest =>
      (a, b) :: edges D rest

@[simp] theorem edges_nil (u : Fin n) :
    edges D (ValidPath.nil u) = [] := rfl

@[simp] theorem edges_cons {u v w : Fin n}
    (h : D.edge u v) (rest : D.ValidPath v w) :
    edges D (ValidPath.cons h rest) = (u, v) :: edges D rest := rfl

/-- Edge lists respect path concatenation. -/
theorem edges_concat {u v w : Fin n}
    (p : D.ValidPath u v) (q : D.ValidPath v w) :
    edges D (concat D p q) = edges D p ++ edges D q := by
  induction p with
  | nil x => rfl
  | cons h rest ih =>
      simp [concat, edges, ih]

/-- Every valid nontrivial path strictly decreases the abstract DAG rank. -/
theorem rank_lt_of_cons {u v w : Fin n}
    (h : D.edge u v) (rest : D.ValidPath v w) :
    D.rank w < D.rank u := by
  cases rest with
  | nil => exact D.rank_decreases h
  | cons h₂ rest =>
    exact Nat.lt_trans (rank_lt_of_cons h₂ rest) (D.rank_decreases h)

end ValidPath

end FragmentationDAG

namespace StochasticGrammar

variable {n : ℕ} {D : FragmentationDAG n} (G : StochasticGrammar D)
include G

/-- Surprisal of a proof-carrying fragmentation path. -/
def validPathSurprisal {u v : Fin n} (p : D.ValidPath u v) : ℝ :=
  G.pathSurprisal (FragmentationDAG.ValidPath.edges D p)

/-- Probability weight of a proof-carrying fragmentation path. -/
def validPathProbability {u v : Fin n} (p : D.ValidPath u v) : ℝ :=
  G.pathProbability (FragmentationDAG.ValidPath.edges D p)

theorem pathSurprisal_append (xs ys : List (FragmentEdge n)) :
    G.pathSurprisal (xs ++ ys) = G.pathSurprisal xs + G.pathSurprisal ys := by
  induction xs with
  | nil => simp [pathSurprisal]
  | cons x xs ih => simp [pathSurprisal, ih, add_assoc]

theorem pathProbability_append (xs ys : List (FragmentEdge n)) :
    G.pathProbability (xs ++ ys) = G.pathProbability xs * G.pathProbability ys := by
  induction xs with
  | nil => simp [pathProbability]
  | cons x xs ih => simp [pathProbability, ih, mul_assoc]

/-- Surprisal is additive under concatenation of valid fragmentation paths. -/
theorem validPathSurprisal_concat {u v w : Fin n}
    (p : D.ValidPath u v) (q : D.ValidPath v w) :
    validPathSurprisal G (FragmentationDAG.ValidPath.concat D p q) =
      validPathSurprisal G p + validPathSurprisal G q := by
  unfold validPathSurprisal
  rw [FragmentationDAG.ValidPath.edges_concat]
  exact pathSurprisal_append G _ _

/-- Path probability is multiplicative under valid-path concatenation. -/
theorem validPathProbability_concat {u v w : Fin n}
    (p : D.ValidPath u v) (q : D.ValidPath v w) :
    validPathProbability G (FragmentationDAG.ValidPath.concat D p q) =
      validPathProbability G p * validPathProbability G q := by
  unfold validPathProbability
  rw [FragmentationDAG.ValidPath.edges_concat]
  exact pathProbability_append G _ _

end StochasticGrammar

end InfoGeometry.MassSpectrometry
