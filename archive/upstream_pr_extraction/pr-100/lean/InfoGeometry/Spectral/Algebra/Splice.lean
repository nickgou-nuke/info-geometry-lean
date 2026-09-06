import InfoGeometry.Spectral.Algebra.ChainComplexMap

/-!
# Splice input data

The reference `splice.hlean` interleaves a family of chain complexes using
degree-shift equivalences and commuting squares.  Its old `stratified` index
is not part of the Lean 4 API, so this file first ports the invariant input
datum on the native chain-complex carrier.  The datum is deliberately not
presented as a splice construction: the indexing/reindexing choice must be
supplied before such a construction is canonical.
-/

namespace InfoGeometry.Spectral.Algebra.ModuleChainComplex

open CategoryTheory

universe u v

variable {R : Type u} [Ring R]

/-- A family of complexes together with a reindexing equivalence and the
chain-level identifications used when splicing adjacent rows. -/
structure SpliceData (I : Type v) where
  family : I → Carrier R
  reindex : I ≃ I
  transport : ∀ i, family i ≅ family (reindex i)

/-- The three-position interleaving index used by the reference splice.
Position `2` is the boundary at which the family is reindexed. -/
abbrev SpliceIndex (I : Type v) := I × Fin 3

def nextIndex (S : SpliceData (R := R) I) : SpliceIndex I → SpliceIndex I
  | (i, ⟨0, _⟩) => (i, ⟨1, by decide⟩)
  | (i, ⟨1, _⟩) => (i, ⟨2, by decide⟩)
  | (i, ⟨2, _⟩) => (S.reindex i, ⟨0, by decide⟩)
  | (i, ⟨n + 3, h⟩) => Fin.elim0 (by omega)

@[simp] theorem nextIndex_zero (S : SpliceData (R := R) I) (i : I) :
    nextIndex S (i, ⟨0, by decide⟩) = (i, ⟨1, by decide⟩) := rfl

@[simp] theorem nextIndex_one (S : SpliceData (R := R) I) (i : I) :
    nextIndex S (i, ⟨1, by decide⟩) = (i, ⟨2, by decide⟩) := rfl

@[simp] theorem nextIndex_two (S : SpliceData (R := R) I) (i : I) :
    nextIndex S (i, ⟨2, by decide⟩) = (S.reindex i, ⟨0, by decide⟩) := rfl

def prevIndex (S : SpliceData (R := R) I) : SpliceIndex I → SpliceIndex I
  | (i, ⟨0, _⟩) => (S.reindex.symm i, ⟨2, by decide⟩)
  | (i, ⟨1, _⟩) => (i, ⟨0, by decide⟩)
  | (i, ⟨2, _⟩) => (i, ⟨1, by decide⟩)
  | (i, ⟨n + 3, h⟩) => Fin.elim0 (by omega)

theorem prevIndex_nextIndex (S : SpliceData (R := R) I) (x : SpliceIndex I) :
    prevIndex S (nextIndex S x) = x := by
  rcases x with ⟨i, ⟨n, hn⟩⟩
  have hcases : n = 0 ∨ n = 1 ∨ n = 2 := by omega
  rcases hcases with rfl | rfl | rfl <;> simp [nextIndex, prevIndex]

theorem nextIndex_prevIndex (S : SpliceData (R := R) I) (x : SpliceIndex I) :
    nextIndex S (prevIndex S x) = x := by
  rcases x with ⟨i, ⟨n, hn⟩⟩
  have hcases : n = 0 ∨ n = 1 ∨ n = 2 := by omega
  rcases hcases with rfl | rfl | rfl <;> simp [nextIndex, prevIndex]

/-- The interleaving transition is an equivalence of the three-position index. -/
def nextIndexEquiv (S : SpliceData (R := R) I) : SpliceIndex I ≃ SpliceIndex I where
  toFun := nextIndex S
  invFun := prevIndex S
  left_inv := prevIndex_nextIndex S
  right_inv := nextIndex_prevIndex S

@[simp] theorem nextIndexEquiv_apply (S : SpliceData (R := R) I)
    (x : SpliceIndex I) :
    nextIndexEquiv S x = nextIndex S x := rfl

@[simp] theorem nextIndexEquiv_symm_apply (S : SpliceData (R := R) I)
    (x : SpliceIndex I) :
    (nextIndexEquiv S).symm x = prevIndex S x := rfl

namespace SpliceData

variable {I : Type v} (S : SpliceData (R := R) I)

def transport_hom_component (i : I) (n : ℕ) :=
  (S.transport i).hom.f n

def transport_inv_component (i : I) (n : ℕ) :=
  (S.transport i).inv.f n

end SpliceData
end InfoGeometry.Spectral.Algebra.ModuleChainComplex
