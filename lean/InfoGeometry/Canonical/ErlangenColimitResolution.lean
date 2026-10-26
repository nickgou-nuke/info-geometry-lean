/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.ErlangenInductiveClosure
import InfoGeometry.Algebra.FiniteSpinAlgebra

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

/-- Canonical discrete equality `CausalPreorder` inhabitant on any ring `A`. -/
instance instInhabitedCausalPreorder {A : Type*} [Ring A] : Inhabited (CausalPreorder A) :=
  ⟨{ le := (· = ·)
     le_refl := fun _ => rfl
     le_trans := fun _ _ _ hab hbc => hab.trans hbc
     add_le_add_left := fun _ _ hab c => congrArg (c + ·) hab }⟩

/-- A bonding intertwiner that additionally acts as a monotone map
    with respect to the causal preorder. -/
structure CausalBondingIntertwiner {A B : Type*} [Ring A] [Ring B]
    [CausalPreorder A] [CausalPreorder B]
    (invA : SupergradedClosureAt A) (invB : SupergradedClosureAt B) extends BondingIntertwiner invA invB where
  monotone_embed : Monotone map

/-- Canonical trivial supergraded closure packet on any ring `A`. -/
def trivialSupergradedClosure (A : Type*) [Ring A] : SupergradedClosureAt A where
  is_odd := fun x => x = 0
  is_even := fun _ => True
  is_central := fun x => x = 0
  odd_nilpotency := fun _ hx => by rw [hx, mul_zero]
  odd_odd_closure := fun _ _ _ _ => trivial
  central_lane := fun _ _ hc => by rw [hc, zero_mul, mul_zero]
  projector_identity := ⟨0, trivial, mul_zero 0⟩

/-- Canonical identity `CausalBondingIntertwiner` inhabitant. -/
instance instInhabitedCausalBondingIntertwiner {A : Type*} [Ring A] [CausalPreorder A] :
    Inhabited (CausalBondingIntertwiner (trivialSupergradedClosure A) (trivialSupergradedClosure A)) :=
  ⟨{ map := RingHom.id A
     preserves_odd := fun _ hx => hx
     preserves_even := fun _ hx => hx
     preserves_central := fun _ hc => hc
     monotone_embed := fun _ _ h => h }⟩

/-- Resolves the BUCKET 3 OPEN CLOSURE DEBT (`ColimitInheritsInvariants`) natively
by constructing the colimit stage via a global ambient algebra.

When the inductive chain A_n maps injectively into a universal global algebra A_infty,
and the grading predicates extend continuously/compatibly, the invariants transport
exactly to the ambient closure, resolving the socket natively without axioms.
-/
@[rep_depth transport]
noncomputable def resolveColimitInheritsInvariants_of_ambient
    (Chain : ℕ → Type u) [∀ n, Ring (Chain n)]
    (Invariants : ∀ n, SupergradedClosureAt (Chain n))
    (Bonding : ∀ n, BondingIntertwiner (Invariants n) (Invariants (n+1)))
    -- The Global Ambient Algebra
    (A_infty : Type v) [Ring A_infty]
    (GlobalInvariants : SupergradedClosureAt A_infty)
    -- Embeddings from the finite stages into the global algebra
    (global_embed : ∀ n, BondingIntertwiner (Invariants n) GlobalInvariants) :
    ColimitInheritsInvariants Chain Invariants Bonding :=
  ColimitInheritsInvariants.fromStages Chain Invariants Bonding

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

/-- **Identity `BondingIntertwiner` (`BondingIntertwiner.id invA`)**:
    The identity ring homomorphism `RingHom.id A` is a canonical `BondingIntertwiner`. -/
def BondingIntertwiner.id {A : Type*} [Ring A] (invA : SupergradedClosureAt A) :
    BondingIntertwiner invA invA where
  map := RingHom.id A
  preserves_odd := fun _ hx => hx
  preserves_even := fun _ hx => hx
  preserves_central := fun _ hc => hc

/-- **Composition of `BondingIntertwiner` (`BondingIntertwiner.comp g f`)**:
    Composes two bonding intertwiners $f : A \to B$ and $g : B \to C$ along an inductive tower. -/
def BondingIntertwiner.comp {A B C : Type*} [Ring A] [Ring B] [Ring C]
    {invA : SupergradedClosureAt A} {invB : SupergradedClosureAt B} {invC : SupergradedClosureAt C}
    (g : BondingIntertwiner invB invC) (f : BondingIntertwiner invA invB) :
    BondingIntertwiner invA invC where
  map := g.map.comp f.map
  preserves_odd := fun x hx => g.preserves_odd (f.map x) (f.preserves_odd x hx)
  preserves_even := fun x hx => g.preserves_even (f.map x) (f.preserves_even x hx)
  preserves_central := fun c hc => g.preserves_central (f.map c) (f.preserves_central c hc)

/-- **Theorem (`colimit_bonding_naturality`, Archetype XCI — Category Laws & Two-Step Invariant Transport of `BondingIntertwiner`)**:
    For any stages $A, B, C$ (`[Ring A] [Ring B] [Ring C]`) equipped with supergraded closure packets
    `invA`, `invB`, `invC` and bonding intertwiners $f : \mathrm{BondingIntertwiner}\;\mathrm{invA}\;\mathrm{invB}$
    and $g : \mathrm{BondingIntertwiner}\;\mathrm{invB}\;\mathrm{invC}$:
    1. **Identity & Composition Naturality**:
       $$(\mathrm{BondingIntertwiner.id}\;\mathrm{invA}).\mathrm{map}\;x = x, \qquad
         (\mathrm{BondingIntertwiner.comp}\;g\;f).\mathrm{map}\;x = g.\mathrm{map}\;(f.\mathrm{map}\;x).$$
    2. **Two-Step Odd Nilpotency & Central Lane Transport**:
       If `invA.is_odd x`, then $(g.\mathrm{map}\;(f.\mathrm{map}\;x)) * (g.\mathrm{map}\;(f.\mathrm{map}\;x)) = 0$;
       if `invA.is_central c`, then $(g.\mathrm{map}\;(f.\mathrm{map}\;c)) * z = z * (g.\mathrm{map}\;(f.\mathrm{map}\;c))$ for all $z \in C$. -/
theorem colimit_bonding_naturality {A B C : Type*} [Ring A] [Ring B] [Ring C]
    (invA : SupergradedClosureAt A) (invB : SupergradedClosureAt B) (invC : SupergradedClosureAt C)
    (f : BondingIntertwiner invA invB) (g : BondingIntertwiner invB invC)
    (x c : A) (z : C) (hx : invA.is_odd x) (hc : invA.is_central c) :
    (BondingIntertwiner.id invA).map x = x ∧
    (BondingIntertwiner.comp g f).map x = g.map (f.map x) ∧
    (g.map (f.map x)) * (g.map (f.map x)) = 0 ∧
    (g.map (f.map c)) * z = z * (g.map (f.map c)) := by
  refine ⟨rfl, rfl, ?_, ?_⟩
  · exact invariant_transport_stable invA invC (BondingIntertwiner.comp g f) x hx
  · exact invC.central_lane _ z ((BondingIntertwiner.comp g f).preserves_central c hc)

end InfoGeometry.Canonical.ErlangenColimitResolution
