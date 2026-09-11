import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.SymbolicLatentLoop
import InfoGeometry.Topology.SymbolicLatentPathHomotopyPathReversal
import InfoGeometry.Topology.SymbolicLatentPathHomotopyReversalFixedPoints

namespace InfoGeometry.Topology

open CategoryTheory

/-!
# Based-loop fiber of the symbolic-latent homotopy quotient

The endpoint map provides a canonical topological fiber over `(x,x)`.  This
is the honest based-loop object available before proving a quotient
composition law.  Reversal preserves this fiber and therefore acts on it by
a genuine involutive `TopCat` homeomorphism.
-/

abbrev SymbolicLatentBasedLoopHomotopyQuotient
    {X : Type} [TopologicalSpace X] (x : X) :=
  {q : SymbolicLatentPathHomotopyQuotient (X := X) //
    symbolicLatentPathHomotopyEndpointMap q = (x, x)}

def symbolicLatentBasedLoopHomotopyQuotientInclusionTopCatHom
    {X : Type} [TopologicalSpace X] (x : X) :
    TopCat.of (SymbolicLatentBasedLoopHomotopyQuotient x) ⟶
      TopCat.of (SymbolicLatentPathHomotopyQuotient (X := X)) :=
  TopCat.ofHom
    { toFun := Subtype.val
      continuous_toFun := continuous_subtype_val }

theorem symbolicLatentBasedLoopHomotopyQuotient_mem_endpoint_fiber
    {X : Type} [TopologicalSpace X]
    (x : X) (q : SymbolicLatentBasedLoopHomotopyQuotient x) :
    symbolicLatentPathHomotopyEndpointMap q.1 = (x, x) :=
  q.2

noncomputable def symbolicLatentBasedLoopHomotopyQuotient_constant
    {X : Type} [TopologicalSpace X] (x : X) :
    SymbolicLatentBasedLoopHomotopyQuotient x :=
  ⟨symbolicLatentPathHomotopyQuotientMap
      (constantSymbolicLatentPath x), by
    rfl⟩

theorem symbolicLatentBasedLoopHomotopyQuotient_reversal_mem
    {X : Type} [TopologicalSpace X]
    (x : X) (q : SymbolicLatentBasedLoopHomotopyQuotient x) :
    symbolicLatentPathHomotopyEndpointMap
        (reversePathHomotopyQuotientHomeomorph q.1) = (x, x) := by
  have hswap := reversePathHomotopyQuotient_endpoint_swap q.1
  rw [q.2] at hswap
  simpa using hswap

noncomputable def symbolicLatentBasedLoopHomotopyQuotientReversalHomeomorph
    {X : Type} [TopologicalSpace X] (x : X) :
    SymbolicLatentBasedLoopHomotopyQuotient x ≃ₜ
      SymbolicLatentBasedLoopHomotopyQuotient x :=
  { toFun := fun q =>
      ⟨reversePathHomotopyQuotientHomeomorph q.1,
        symbolicLatentBasedLoopHomotopyQuotient_reversal_mem x q⟩
    invFun := fun q =>
      ⟨reversePathHomotopyQuotientHomeomorph q.1,
        symbolicLatentBasedLoopHomotopyQuotient_reversal_mem x q⟩
    left_inv := by
      intro q
      apply Subtype.ext
      exact reversePathHomotopyQuotientHomeomorph.left_inv q.1
    right_inv := by
      intro q
      apply Subtype.ext
      exact reversePathHomotopyQuotientHomeomorph.left_inv q.1
    continuous_toFun := by
      exact (reversePathHomotopyQuotientHomeomorph.continuous_toFun.comp
        continuous_subtype_val).subtype_mk
        (fun q => symbolicLatentBasedLoopHomotopyQuotient_reversal_mem x q)
    continuous_invFun := by
      exact (reversePathHomotopyQuotientHomeomorph.continuous_toFun.comp
        continuous_subtype_val).subtype_mk
        (fun q => symbolicLatentBasedLoopHomotopyQuotient_reversal_mem x q) }

theorem symbolicLatentBasedLoopHomotopyQuotientReversalHomeomorph_apply
    {X : Type} [TopologicalSpace X] (x : X)
    (q : SymbolicLatentBasedLoopHomotopyQuotient x) :
    symbolicLatentBasedLoopHomotopyQuotientReversalHomeomorph x q =
      ⟨reversePathHomotopyQuotientHomeomorph q.1,
        symbolicLatentBasedLoopHomotopyQuotient_reversal_mem x q⟩ :=
  rfl

noncomputable def symbolicLatentBasedLoopHomotopyQuotientReversalTopCatHom
    {X : Type} [TopologicalSpace X] (x : X) :
    TopCat.of (SymbolicLatentBasedLoopHomotopyQuotient x) ⟶
      TopCat.of (SymbolicLatentBasedLoopHomotopyQuotient x) :=
  TopCat.ofHom
    { toFun := symbolicLatentBasedLoopHomotopyQuotientReversalHomeomorph x
      continuous_toFun :=
        (symbolicLatentBasedLoopHomotopyQuotientReversalHomeomorph x).continuous_toFun }

theorem symbolicLatentBasedLoopHomotopyQuotientReversalTopCatHom_square
    {X : Type} [TopologicalSpace X] (x : X) :
    symbolicLatentBasedLoopHomotopyQuotientReversalTopCatHom x ≫
        symbolicLatentBasedLoopHomotopyQuotientReversalTopCatHom x =
      𝟙 (TopCat.of (SymbolicLatentBasedLoopHomotopyQuotient x)) := by
  ext q
  change reversePathHomotopyQuotientHomeomorph
      (reversePathHomotopyQuotientHomeomorph q.1) = q.1
  exact reversePathHomotopyQuotientHomeomorph.left_inv q.1

end InfoGeometry.Topology
