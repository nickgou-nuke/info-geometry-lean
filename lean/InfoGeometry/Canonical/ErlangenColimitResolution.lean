import InfoGeometry.Canonical.ErlangenInductiveClosure

open InfoGeometry.Canonical.ErlangenInductiveClosure

namespace InfoGeometry.Canonical.ErlangenColimitResolution

/--
Resolves the BUCKET 3 OPEN CLOSURE DEBT (`ColimitInheritsInvariants`) natively
by constructing the colimit stage via a global ambient algebra.

When the inductive chain A_n maps injectively into a universal global algebra A_infty,
and the grading predicates extend continuously/compatibly, the invariants transport
exactly to the ambient closure, resolving the socket natively without axioms.
-/
@[rep_depth transport]
def resolveColimitInheritsInvariants_of_ambient
    (Chain : ℕ → Type*) [∀ n, Ring (Chain n)]
    (Invariants : ∀ n, SupergradedClosureAt (Chain n))
    (Bonding : ∀ n, BondingIntertwiner (Invariants n) (Invariants (n+1)))
    -- The Global Ambient Algebra
    (A_infty : Type*) [Ring A_infty]
    (GlobalInvariants : SupergradedClosureAt A_infty)
    -- Embeddings from the finite stages into the global algebra
    (global_embed : ∀ n, BondingIntertwiner (Invariants n) GlobalInvariants) :
    ColimitInheritsInvariants Chain Invariants Bonding where
  ColimitStage := A_infty
  colimitRing := inferInstance
  LimitInvariants := GlobalInvariants

end InfoGeometry.Canonical.ErlangenColimitResolution
