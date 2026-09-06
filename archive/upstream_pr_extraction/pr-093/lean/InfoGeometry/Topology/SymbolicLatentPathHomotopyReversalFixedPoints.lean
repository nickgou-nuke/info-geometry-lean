import Mathlib
import InfoGeometry.Topology.SymbolicLatentPathHomotopyPathReversal
import InfoGeometry.Topology.SymbolicLatentInvolutionTopCat

namespace InfoGeometry.Topology

/-!
# Fixed points of path-parameter reversal

The fixed locus consists of homotopy classes invariant under path reversal.
Its endpoint readout lies on the diagonal, as forced by reversal's endpoint
swap; no converse is asserted.
-/

noncomputable def symbolicLatentPathHomotopyReversalInvolution
    {X : Type} [TopologicalSpace X] :
    SymbolicLatentInvolution
      (SymbolicLatentPathHomotopyQuotient (X := X)) where
  toFun := reversePathHomotopyQuotientHomeomorph
  continuous_toFun :=
    reversePathHomotopyQuotientHomeomorph.continuous_toFun
  involutive := by
    intro q
    exact reversePathHomotopyQuotientHomeomorph.left_inv q

abbrev symbolicLatentPathHomotopyReversalFixedPointObject
    {X : Type} [TopologicalSpace X] :=
  SymbolicLatentInvolutionFixedPointObject
    (symbolicLatentPathHomotopyReversalInvolution (X := X))

noncomputable def symbolicLatentPathHomotopyReversalFixedPointInclusion
    {X : Type} [TopologicalSpace X] :
    symbolicLatentPathHomotopyReversalFixedPointObject (X := X) ⟶
      TopCat.of (SymbolicLatentPathHomotopyQuotient (X := X)) :=
  (symbolicLatentPathHomotopyReversalInvolution (X := X)).fixedPointInclusion

theorem reversePathHomotopyQuotient_endpoint_swap
    {X : Type} [TopologicalSpace X]
    (q : SymbolicLatentPathHomotopyQuotient (X := X)) :
    symbolicLatentPathHomotopyEndpointMap
        (reversePathHomotopyQuotientHomeomorph q) =
      (fun p => (p.2, p.1))
        (symbolicLatentPathHomotopyEndpointMap q) := by
  refine Quotient.inductionOn q ?_
  intro γ
  change (reverseSymbolicLatentPath γ).endpoints =
    (γ.endpoints.2, γ.endpoints.1)
  exact Prod.ext
    (reverseSymbolicLatentPath_start γ)
    (reverseSymbolicLatentPath_finish γ)

theorem symbolicLatentPathHomotopyReversal_fixed_endpoint_diagonal
    {X : Type} [TopologicalSpace X]
    (q : SymbolicLatentPathHomotopyQuotient (X := X))
    (hq : q ∈ symbolicLatentInvolutionFixedPointSet
      (symbolicLatentPathHomotopyReversalInvolution (X := X))) :
    (symbolicLatentPathHomotopyEndpointMap q).1 =
      (symbolicLatentPathHomotopyEndpointMap q).2 := by
  have hq' : reversePathHomotopyQuotientHomeomorph q = q := hq
  have hswap := reversePathHomotopyQuotient_endpoint_swap q
  rw [hq'] at hswap
  exact congrArg Prod.fst hswap

end InfoGeometry.Topology
