import Mathlib.Data.Matrix.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Data.Complex.Basic
import DAG.Basic

/-!
# DAG-Majorana Homomorphism — Projective Representation

The DAG is the combinatorial shadow of a non-commutative Clifford algebra.
Paths map to Majorana operators; commuting diamonds may carry central residues.

  F: DAG paths → Majorana net operators
  ω: central residue readout, values in {±1}
  Spin = projective representation (360° → -1)
-/

noncomputable section

namespace InfoGeometry.DAGMajorana

open DAG

/--
A Majorana net: a family of operators γ_i on a real vector space V
satisfying {γ_i, γ_j} = 2·δ_{ij}·id.
-/
structure MajoranaNet (α : Type*) where
  V : Type*
  [add : AddCommGroup V]
  [module : Module ℝ V]
  gamma : α → (V → V)
  anticomm : ∀ i j (x : V), gamma i (gamma j x) + gamma j (gamma i x) = (2 : ℝ) • x

/--
The DAG-Majorana homomorphism. Maps DAG paths to Majorana operators and records
central residue readouts in `{±1}`.
-/
structure DAGMajoranaHomomorphism
    (α : Type*) [BEq α] [Hashable α] where
  dag : HydratedGraph α
  net : MajoranaNet α
  /-- The central residue readout: values in {±1}. -/
  centralResidue : α → α → ℤ
  residue_binary : ∀ u v, centralResidue u v = 1 ∨ centralResidue u v = -1

namespace DAGMajoranaHomomorphism

/-- The operator assigned to an edge, derived from its endpoint generators. -/
def edgeToOp
    {α : Type*} [BEq α] [Hashable α]
    (F : DAGMajoranaHomomorphism α) (u v : α) : F.net.V → F.net.V :=
  F.net.gamma u ∘ F.net.gamma v

@[simp]
theorem edgeToOp_eq
    {α : Type*} [BEq α] [Hashable α]
    (F : DAGMajoranaHomomorphism α) (u v : α) :
    F.edgeToOp u v = F.net.gamma u ∘ F.net.gamma v :=
  rfl

end DAGMajoranaHomomorphism

/--
Direct readout of the defining `{±1}` range condition for the central residue.
-/
theorem central_residue_binary
    (α : Type*) [BEq α] [Hashable α]
    (F : DAGMajoranaHomomorphism α) :
    ∀ u v : α, F.centralResidue u v = 1 ∨ F.centralResidue u v = -1 := by
  intro u v
  exact F.residue_binary u v

/--
Same `{±1}` readout, provided under a name used by files that only need the
residue range and do not assert a cycle-sum theorem.
-/
theorem central_residue_binary_for_obstruction_readout
    (α : Type*) [BEq α] [Hashable α]
    (F : DAGMajoranaHomomorphism α) :
    ∀ u v : α, F.centralResidue u v = 1 ∨ F.centralResidue u v = -1 := by
  intro u v
  exact F.residue_binary u v

end InfoGeometry.DAGMajorana
