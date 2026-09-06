import DAG.GeneralizedTwoComplex

/-!
# A lawful generalized view of a finite `TwoComplex`

The raw executable carrier deliberately permits malformed cells.  This bridge
therefore requires the coefficientwise boundary law as an explicit hypothesis
before constructing the proof-carrying generalized carrier.
-/

namespace DAG

open Matrix

structure BoundaryTwoComplex
    {R : Type} [Semiring R]
    {α : Type} [BEq α] [Hashable α]
    (tc : TwoComplex α)
    (d1 : Fin tc.edges.size → Fin tc.base.toGraph.nodes.size → R)
    (d2 : Fin (tc.faces.size + tc.digons.size) → Fin tc.edges.size → R) where
  boundary_squared_zero : ∀ f v, ∑ e, d2 f e * d1 e v = 0

structure HodgeStarData
    {R : Type} [Semiring R] [StarRing R]
    {α : Type} [BEq α] [Hashable α]
    (tc : TwoComplex α) where
  star0 : (Fin tc.base.toGraph.nodes.size → R) → Fin tc.base.toGraph.nodes.size → R
  star1 : (Fin tc.edges.size → R) → Fin tc.edges.size → R
  star2 : (Fin (tc.faces.size + tc.digons.size) → R) →
    Fin (tc.faces.size + tc.digons.size) → R
  star0_involution : ∀ f v, star0 (star0 f) v = f v
  star1_involution : ∀ f e, star1 (star1 f) e = f e

def BoundaryTwoComplex.toGeneralized
    {R : Type} [Semiring R] [StarRing R]
    {α : Type} [BEq α] [Hashable α]
    {tc : TwoComplex α}
    {d1 : Fin tc.edges.size → Fin tc.base.toGraph.nodes.size → R}
    {d2 : Fin (tc.faces.size + tc.digons.size) → Fin tc.edges.size → R}
    (lawful : BoundaryTwoComplex tc d1 d2)
    (stars : HodgeStarData (R := R) tc) :
    GeneralizedTwoComplex R (Fin tc.base.toGraph.nodes.size)
      (Fin tc.edges.size) (Fin (tc.faces.size + tc.digons.size)) :=
  { d1 := d1
    d2 := d2
    star0 := stars.star0
    star1 := stars.star1
    star2 := stars.star2
    star0_involution := stars.star0_involution
    star1_involution := stars.star1_involution
    boundary_squared_zero := lawful.boundary_squared_zero }

theorem TwoComplex.toGeneralized_boundary_squared_zero
    {R : Type} [Semiring R] [StarRing R]
    {α : Type} [BEq α] [Hashable α]
    (tc : TwoComplex α)
    (d1 : Fin tc.edges.size → Fin tc.base.toGraph.nodes.size → R)
    (d2 : Fin (tc.faces.size + tc.digons.size) → Fin tc.edges.size → R)
    (lawful : BoundaryTwoComplex tc d1 d2)
    (f : Fin (tc.faces.size + tc.digons.size))
    (v : Fin tc.base.toGraph.nodes.size) :
    ∑ e, d2 f e * d1 e v = 0 :=
  lawful.boundary_squared_zero f v

end DAG
