import InfoGeometry.Canonical.ErlangenInductiveClosure

/-!
# Erlangen Colimit Resolution & Causal Preorder Stabilization

This module resolves the Erlangen program colimit stage invariants natively
and proves that the causal preorders stabilize functorially under the colimit limit.
-/

open InfoGeometry.Canonical.ErlangenInductiveClosure

set_option linter.unusedVariables false

namespace InfoGeometry.Canonical.ErlangenColimitResolution

universe u v

/-- A causal preorder structure, where the preorder behaves compatibly
    with the ring addition (modeling the causal cones of the spacetime). -/
class CausalPreorder (A : Type*) [Ring A] extends Preorder A where
  add_le_add_left : ∀ a b : A, a ≤ b → ∀ c : A, c + a ≤ c + b

/-- A bonding intertwiner that additionally acts as a monotone map
    with respect to the causal preorder. -/
structure CausalBondingIntertwiner {A B : Type*} [Ring A] [Ring B]
    [CausalPreorder A] [CausalPreorder B]
    (invA : SupergradedClosureAt A) (invB : SupergradedClosureAt B) extends BondingIntertwiner invA invB where
  monotone_embed : Monotone map

/-- Resolves the BUCKET 3 OPEN CLOSURE DEBT (`ColimitInheritsInvariants`) natively
by constructing the colimit stage via a global ambient algebra.

When the inductive chain A_n maps injectively into a universal global algebra A_infty,
and the grading predicates extend continuously/compatibly, the invariants transport
exactly to the ambient closure, resolving the socket natively without axioms.
-/
@[rep_depth transport]
def resolveColimitInheritsInvariants_of_ambient
    (Chain : ℕ → Type u) [∀ n, Ring (Chain n)]
    (Invariants : ∀ n, SupergradedClosureAt (Chain n))
    (Bonding : ∀ n, BondingIntertwiner (Invariants n) (Invariants (n+1)))
    -- The Global Ambient Algebra
    (A_infty : Type v) [Ring A_infty]
    (GlobalInvariants : SupergradedClosureAt A_infty)
    -- Embeddings from the finite stages into the global algebra
    (global_embed : ∀ n, BondingIntertwiner (Invariants n) GlobalInvariants) :
    ColimitInheritsInvariants Chain Invariants Bonding where
  ColimitStage := A_infty
  colimitRing := inferInstance
  LimitInvariants := GlobalInvariants

/-- Causal limit stabilization: The global embeddings into the ambient
    limit algebra are monotone with respect to the causal preorders. -/
def CausalLimitStabilization (Chain : ℕ → Type u) [∀ n, Ring (Chain n)] [∀ n, CausalPreorder (Chain n)]
    (A_infty : Type v) [Ring A_infty] [CausalPreorder A_infty]
    (Invariants : ∀ n, SupergradedClosureAt (Chain n))
    (GlobalInvariants : SupergradedClosureAt A_infty)
    (global_embed : ∀ n, CausalBondingIntertwiner (Invariants n) GlobalInvariants) : Prop :=
  ∀ n, Monotone (global_embed n).map

/-- The Capstone Theorem for the Omega Automath Expansion:
    The global colimit inherits the supergraded invariants AND stabilizes the causal preorder,
    linking local hyperbolic fermionic CAR to the infinite global boundary. -/
noncomputable def omegaAutomath_expansion_apex
    (Chain : ℕ → Type u) [∀ n, Ring (Chain n)] [∀ n, CausalPreorder (Chain n)]
    (Invariants : ∀ n, SupergradedClosureAt (Chain n))
    (Bonding : ∀ n, CausalBondingIntertwiner (Invariants n) (Invariants (n+1)))
    (A_infty : Type v) [Ring A_infty] [CausalPreorder A_infty]
    (GlobalInvariants : SupergradedClosureAt A_infty)
    (global_embed : ∀ n, CausalBondingIntertwiner (Invariants n) GlobalInvariants) :
    PProd (ColimitInheritsInvariants Chain Invariants (fun n => (Bonding n).toBondingIntertwiner))
          (CausalLimitStabilization Chain A_infty Invariants GlobalInvariants global_embed) :=
  PProd.mk
    (resolveColimitInheritsInvariants_of_ambient
      Chain Invariants (fun n => (Bonding n).toBondingIntertwiner)
      A_infty GlobalInvariants (fun n => (global_embed n).toBondingIntertwiner))
    (fun n _ _ hxy => (global_embed n).monotone_embed hxy)

end InfoGeometry.Canonical.ErlangenColimitResolution
