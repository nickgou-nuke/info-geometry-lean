import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Finite chemical graph owner

This file introduces the minimal theorem-facing chemical graph layer needed by
mass-spectrometry reconstruction.  It deliberately stops before SMILES, IUPAC,
valence models, aromaticity perception, or conformer geometry.

A molecular graph has:

* a finite vertex carrier `Fin n`;
* an atom label at each vertex;
* a symmetric bond-kind matrix with no diagonal bonds.

Embeddings and isomorphisms preserve both atom and bond labels exactly.
-/

namespace InfoGeometry.MassSpectrometry

/-- Minimal atom label.  `atomicNumber = 0` is allowed at the type level so
applications may represent placeholders explicitly rather than through a
partial function. -/
structure AtomLabel where
  atomicNumber : ℕ
  isotopeMassNumber : Option ℕ := none
  formalCharge : ℤ := 0
  deriving DecidableEq, Repr

/-- Finite bond vocabulary.  `none` means absence of a bond. -/
inductive BondKind
  | none
  | single
  | double
  | triple
  | aromatic
  deriving DecidableEq, Repr

namespace BondKind

/-- Whether a bond label represents an actual edge. -/
def Present : BondKind → Prop
  | .none => False
  | _ => True

@[simp] theorem not_present_none : ¬ Present .none := by
  simp [Present]

end BondKind

/-- A finite atom- and bond-labelled molecular graph. -/
structure MolecularGraph (n : ℕ) where
  atom : Fin n → AtomLabel
  bond : Fin n → Fin n → BondKind
  bond_symm : ∀ i j, bond i j = bond j i
  bond_diag : ∀ i, bond i i = .none

namespace MolecularGraph

variable {n m k : ℕ}

/-- Underlying adjacency predicate. -/
def Adj (G : MolecularGraph n) (i j : Fin n) : Prop :=
  G.bond i j ≠ .none

@[simp] theorem not_adj_self (G : MolecularGraph n) (i : Fin n) :
    ¬ G.Adj i i := by
  simp [Adj, G.bond_diag]

/-- Adjacency is symmetric. -/
theorem adj_symm (G : MolecularGraph n) {i j : Fin n} :
    G.Adj i j ↔ G.Adj j i := by
  simp [Adj, G.bond_symm]

/-- Native Mathlib `SimpleGraph` shadow of the labelled bond structure. -/
def toSimpleGraph (G : MolecularGraph n) : SimpleGraph (Fin n) where
  Adj := G.Adj
  symm := fun _ _ h => (G.adj_symm).mp h
  loopless := ⟨fun i => G.not_adj_self i⟩

/-- Exact structure-preserving embedding of one molecular graph into another. -/
structure Embedding (G : MolecularGraph n) (H : MolecularGraph m) where
  toFun : Fin n → Fin m
  injective : Function.Injective toFun
  atom_preserving : ∀ i, H.atom (toFun i) = G.atom i
  bond_preserving : ∀ i j, H.bond (toFun i) (toFun j) = G.bond i j

namespace Embedding

/-- Identity molecular embedding. -/
def id (G : MolecularGraph n) : G.Embedding G where
  toFun := fun i => i
  injective := Function.injective_id
  atom_preserving := by intro i; rfl
  bond_preserving := by intro i j; rfl

/-- Composition of exact molecular embeddings. -/
def comp {G : MolecularGraph n} {H : MolecularGraph m} {K : MolecularGraph k}
    (f : G.Embedding H) (g : H.Embedding K) : G.Embedding K where
  toFun := g.toFun ∘ f.toFun
  injective := g.injective.comp f.injective
  atom_preserving := by
    intro i
    rw [Function.comp_apply, g.atom_preserving, f.atom_preserving]
  bond_preserving := by
    intro i j
    rw [Function.comp_apply, Function.comp_apply, g.bond_preserving, f.bond_preserving]

@[simp] theorem id_toFun (G : MolecularGraph n) (i : Fin n) :
    (Embedding.id G).toFun i = i := by rfl

@[simp] theorem comp_toFun
    {G : MolecularGraph n} {H : MolecularGraph m} {K : MolecularGraph k}
    (f : G.Embedding H) (g : H.Embedding K) (i : Fin n) :
    (f.comp g).toFun i = g.toFun (f.toFun i) := rfl

/-- Embeddings preserve adjacency. -/
theorem adj_iff {G : MolecularGraph n} {H : MolecularGraph m}
    (f : G.Embedding H) {i j : Fin n} :
    H.Adj (f.toFun i) (f.toFun j) ↔ G.Adj i j := by
  simp [MolecularGraph.Adj, f.bond_preserving]

end Embedding

/-- Exact molecular-graph isomorphism. -/
structure Iso (G : MolecularGraph n) (H : MolecularGraph n) where
  vertexEquiv : Equiv.Perm (Fin n)
  atom_preserving : ∀ i, H.atom (vertexEquiv i) = G.atom i
  bond_preserving : ∀ i j, H.bond (vertexEquiv i) (vertexEquiv j) = G.bond i j

namespace Iso

/-- Identity molecular isomorphism. -/
def refl (G : MolecularGraph n) : G.Iso G where
  vertexEquiv := Equiv.refl _
  atom_preserving := by intro i; rfl
  bond_preserving := by intro i j; rfl

/-- A molecular isomorphism gives an embedding. -/
def toEmbedding {G H : MolecularGraph n} (e : G.Iso H) : G.Embedding H where
  toFun := e.vertexEquiv
  injective := e.vertexEquiv.injective
  atom_preserving := e.atom_preserving
  bond_preserving := e.bond_preserving

end Iso

end MolecularGraph

end InfoGeometry.MassSpectrometry
