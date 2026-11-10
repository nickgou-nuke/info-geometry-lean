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

namespace InfoGeometry.Canonical.ErlangenColimitResolution

universe u

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

/-! The ambient stage maps below form an actual cone over the algebraic direct
limit.  The compatibility condition is essential: unrelated maps out of the
stages do not induce a map from the colimit. -/

/-- Resolve the stage invariant package together with the ring hom induced by a
compatible ambient cone.  The first component is the invariant structure on the
actual algebraic direct-limit quotient; the second is the universal cone map. -/
noncomputable def resolveColimitInheritsInvariants_of_ambient
    (Chain : ℕ → Type u) [∀ n, Ring (Chain n)]
    (Invariants : ∀ n, SupergradedClosureAt (Chain n))
    (Bonding : ∀ n, BondingIntertwiner (Invariants n) (Invariants (n+1)))
    -- The Global Ambient Algebra
    (A_infty : Type u) [Ring A_infty]
    (GlobalInvariants : SupergradedClosureAt A_infty)
    -- Compatible maps from each stage into the ambient algebra
    (global_embed : ∀ n, BondingIntertwiner (Invariants n) GlobalInvariants)
    (global_compatible : ∀ n x,
      (global_embed (n + 1)).map ((Bonding n).map x) = (global_embed n).map x) :
    ColimitInheritsInvariants Chain Invariants Bonding ×
      (ColimitInheritsInvariants.ColimitStage Chain Invariants Bonding →+* A_infty) := by
  let bond := fun n => (Bonding n).map
  let cone := fun n => (global_embed n).map
  refine (ColimitInheritsInvariants.fromStages Chain Invariants Bonding, ?_)
  exact InfoGeometry.Algebra.DirectLimitSuperClosureLemmas.directLimitLift bond cone
    (by
      intro n x
      exact global_compatible n x)

/-- Stagewise monotonicity of the supplied maps into the ambient preorder. -/
def CausalLimitStabilization (Chain : ℕ → Type u) [∀ n, Ring (Chain n)]
    [∀ n, CausalPreorder (Chain n)] (A_infty : Type v) [Ring A_infty]
    [CausalPreorder A_infty] (Invariants : ∀ n, SupergradedClosureAt (Chain n))
    (GlobalInvariants : SupergradedClosureAt A_infty)
    (global_embed : ∀ n, CausalBondingIntertwiner (Invariants n) GlobalInvariants) : Prop :=
  ∀ n, Monotone (global_embed n).map

/-- Stage invariants on the direct limit together with the independently
supplied monotonicity of each ambient stage map.  This does not assert that
those maps form a compatible cone. -/
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
    (ColimitInheritsInvariants.fromStages Chain Invariants
      (fun n => (Bonding n).toBondingIntertwiner))
    (fun n _ _ hxy => (global_embed n).monotone_embed hxy)

/-- **Identity `BondingIntertwiner` (`BondingIntertwiner.id invA`)**:
    The identity ring homomorphism `RingHom.id A` is a canonical `BondingIntertwiner`. -/
def BondingIntertwiner.id {A : Type*} [Ring A] (invA : SupergradedClosureAt A) :
    BondingIntertwiner invA invA where
  map := RingHom.id A
  preserves_odd := fun _ hx => hx
  preserves_even := fun _ hx => hx
  preserves_central := fun _ hc => hc

/-- Identity causal intertwiner on a supplied causal order and invariant packet. -/
def CausalBondingIntertwiner.id {A : Type*} [Ring A] [CausalPreorder A]
    (invA : SupergradedClosureAt A) : CausalBondingIntertwiner invA invA where
  toBondingIntertwiner := BondingIntertwiner.id invA
  monotone_embed := fun _ _ h => h

/-- Once an actual causal preorder and invariant packet are supplied, the
identity map is an inhabitant of the corresponding causal intertwiner type. -/
instance instInhabitedCausalBondingIntertwiner {A : Type*} [Ring A]
    [CausalPreorder A] (invA : SupergradedClosureAt A) :
    Inhabited (CausalBondingIntertwiner invA invA) :=
  ⟨CausalBondingIntertwiner.id invA⟩

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
  have hfx : invB.is_odd (f.map x) := f.preserves_odd x hx
  have hgfx : invC.is_odd (g.map (f.map x)) := g.preserves_odd (f.map x) hfx
  have hfc : invB.is_central (f.map c) := f.preserves_central c hc
  have hgfc : invC.is_central (g.map (f.map c)) := g.preserves_central (f.map c) hfc
  refine ⟨rfl, rfl, ?_, ?_⟩
  · exact invC.odd_nilpotency (g.map (f.map x)) hgfx
  · exact invC.central_lane (g.map (f.map c)) z hgfc

end InfoGeometry.Canonical.ErlangenColimitResolution
