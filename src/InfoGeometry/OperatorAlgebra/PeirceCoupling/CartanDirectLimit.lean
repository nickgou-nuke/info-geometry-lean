/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Core.DualSeedCartan
import Mathlib.Algebra.Colimit.DirectLimit

/-!
# Reflexive noncommuting seeds in the native directed colimit

This is Mathlib's actual quotient `DirectLimit` of associative rings, not a
finite recursion and not the commutative `Ring.DirectLimit`. The existing
split-Clifford directed system is one possible input; no replacement tower
or analytic completion is introduced. Injectivity is stated exactly where
nonzero support or a nondegenerate Cartan triple is concluded.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceCoupling.CartanDirectLimit

attribute [local instance 100] LieRing.ofAssociativeRing

open InfoGeometry.Core.DualSeedPeirce

variable {I : Type*} [Preorder I] [Nonempty I] [IsDirectedOrder I]
variable {A : I → Type*} [∀ i, Ring (A i)]
variable (f : ∀ i j, i ≤ j → A i →+* A j)
variable [DirectedSystem A (fun i j hij => f i j hij)]

/-- Native quotient inclusions are faithful for an injective directed system. -/
theorem of_injective (hf : ∀ i j hij, Function.Injective (f i j hij)) (i : I) :
    Function.Injective (DirectLimit.Ring.of A f i) :=
  DirectLimit.mk_injective f hf i

/-- Polynomial seed equations descend without any injectivity assumption. -/
theorem seedPair_of {i : I} {d b : A i} (h : IsDualSeedPair d b) :
    IsDualSeedPair (DirectLimit.Ring.of A f i d) (DirectLimit.Ring.of A f i b) :=
  h.map (DirectLimit.Ring.of A f i)

/-- Support is transported as the existing support expression, not a new definition. -/
theorem support_of (i : I) (d b : A i) :
    DirectLimit.Ring.of A f i (carrierSupport d b) =
      carrierSupport (DirectLimit.Ring.of A f i d) (DirectLimit.Ring.of A f i b) := by
  change DirectLimit.Ring.of A f i (d * b + b * d) =
    DirectLimit.Ring.of A f i d * DirectLimit.Ring.of A f i b +
      DirectLimit.Ring.of A f i b * DirectLimit.Ring.of A f i d
  simp only [map_add, map_mul]

/-- Nonzero support survives in the actual colimit under faithful bonding maps. -/
theorem support_of_ne_zero
    (hf : ∀ i j hij, Function.Injective (f i j hij))
    {i : I} {d b : A i} (h : IsDualSeedPair d b) (hd : d ≠ 0) :
    DirectLimit.Ring.of A f i (carrierSupport d b) ≠ 0 := by
  intro hz
  apply h.support_ne_zero hd
  apply of_injective f hf i
  simpa only [map_zero] using hz

/-- The Cartan triple lives in the quotient algebra, not merely at a finite stage. -/
theorem isSl2Triple_of
    (hf : ∀ i j hij, Function.Injective (f i j hij))
    {i : I} {d b : A i} (h : IsDualSeedPair d b) (hd : d ≠ 0) :
    IsSl2Triple
      (phasePolarization (DirectLimit.Ring.of A f i d) (DirectLimit.Ring.of A f i b))
      (DirectLimit.Ring.of A f i d) (DirectLimit.Ring.of A f i b) :=
  h.isSl2Triple_map hd (DirectLimit.Ring.of A f i) (of_injective f hf i)

/-- Noncommutativity is retained; the construction is not a commutative quotient. -/
theorem not_commute_of
    (hf : ∀ i j hij, Function.Injective (f i j hij))
    {i : I} {d b : A i} (h : IsDualSeedPair d b) (hd : d ≠ 0) :
    ¬ Commute (DirectLimit.Ring.of A f i d) (DirectLimit.Ring.of A f i b) := by
  apply (seedPair_of f h).seeds_not_commute
  intro hz
  apply hd
  apply of_injective f hf i
  simpa only [map_zero] using hz

/-- Idempotence is a polynomial statement, not a quantitative spectral bound. -/
theorem support_of_idempotent {i : I} {d b : A i} (h : IsDualSeedPair d b) :
    IsIdempotentElem (DirectLimit.Ring.of A f i (carrierSupport d b)) := by
  change DirectLimit.Ring.of A f i (carrierSupport d b) *
    DirectLimit.Ring.of A f i (carrierSupport d b) = _
  rw [← map_mul, h.support_idempotent]

/-- The integral Casimir identity holds in the actual quotient. -/
theorem casimir_of {i : I} {d b : A i} (h : IsDualSeedPair d b) :
    let d' := DirectLimit.Ring.of A f i d
    let b' := DirectLimit.Ring.of A f i b
    phasePolarization d' b' * phasePolarization d' b' +
      (2 : ℕ) • carrierSupport d' b' = (3 : ℕ) • carrierSupport d' b' :=
  (seedPair_of f h).quadratic_casimir

/-- Universal factorization is supplied by Mathlib's constructed colimit. -/
theorem lift_exists_unique {B : Type*} [Ring B]
    (g : ∀ i, A i →+* B)
    (hg : ∀ i j hij x, g j (f i j hij x) = g i x) :
    ∃! ψ : DirectLimit A f →+* B,
      ∀ i x, ψ (DirectLimit.Ring.of A f i x) = g i x := by
  refine ⟨DirectLimit.Ring.lift A f B g hg, ?_, ?_⟩
  · intro i x
    rfl
  · intro ψ hψ
    apply DirectLimit.Ring.hom_ext
    intro i
    ext x
    exact hψ i x

end InfoGeometry.OperatorAlgebra.PeirceCoupling.CartanDirectLimit
