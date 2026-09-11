import InfoGeometry.Algebra.Zorn.G2BruhatResidualRoots
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.Zorn.G2NativeOrderedRootProduct

namespace InfoGeometry.Algebra.Zorn.G2NativePositiveRootSubgroupSystem

open InfoGeometry.Algebra.Zorn.G2Combinatorics
open InfoGeometry.Algebra.Zorn.G2BruhatResidual
open InfoGeometry.Algebra.Zorn.G2SteinbergRoots
open InfoGeometry.Algebra.Zorn.G2TwoRootSystem
open InfoGeometry.Algebra.Zorn.G2NativeOrderedRootProduct
open InfoGeometry.Algebra.Zorn.G2UnipotentWord6Cardinality
open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem

private def rootIndex : G2PositiveRoot → Fin 6
  | .alpha => 0
  | .beta => 1
  | .alpha_add_beta => 2
  | .two_alpha_beta => 3
  | .three_alpha_beta => 4
  | .three_alpha_two_beta => 5

private def rootAt : Fin 6 → G2PositiveRoot
  | 0 => .alpha
  | 1 => .beta
  | 2 => .alpha_add_beta
  | 3 => .two_alpha_beta
  | 4 => .three_alpha_beta
  | 5 => .three_alpha_two_beta

/-! The native part of the positive-root system.  Product normal forms and
    rank-one peeling are intentionally not asserted here: those are the
    additional Chevalley/BN-pair statements identified by the specification.
-/
structure System where
  root : G2PositiveRoot → Bool → SplitOctF2Aut
  root_mem : ∀ α t, root α t ∈ positiveRootSubgroup
  root_zero : ∀ α, root α false = 1
  root_additive : ∀ α s t,
    root α (s ^^ t) = root α s * root α t
  root_injective : ∀ α, Function.Injective (root α)

noncomputable def native : System where
  root := positiveRootGenerator
  root_mem := positiveRootGenerator_mem_positiveRootSubgroup
  root_zero := positiveRootGenerator_false
  root_additive := by
    intro α s t
    simpa [positiveRootGenerator, rootIndex] using
      (positiveRootAction_add (rootIndex α) s t)
  root_injective := by
    intro α s t h
    cases s <;> cases t
    · rfl
    · exfalso
      exact positiveRootGenerator_ne_one α h.symm
    · exfalso
      exact positiveRootGenerator_ne_one α h
    · rfl

theorem native_root_mem (α : G2PositiveRoot) (t : Bool) :
    native.root α t ∈ positiveRootSubgroup :=
  native.root_mem α t

theorem native_root_zero (α : G2PositiveRoot) :
    native.root α false = 1 :=
  native.root_zero α

theorem native_root_additive (α : G2PositiveRoot) (s t : Bool) :
    native.root α (s ^^ t) = native.root α s * native.root α t :=
  native.root_additive α s t

theorem native_root_injective (α : G2PositiveRoot) :
    Function.Injective (native.root α) :=
  native.root_injective α

theorem native_rootAt_apply (i : Fin 6) (t : Bool) :
    native.root (rootAt i) t = positiveRootAction i t := by
  fin_cases i <;> cases t <;> rfl

/-! The ordered six-root product is exposed separately from the individual
    root-subgroup axioms.  Its image is not identified with the whole
    positive-root subgroup here; the native development proves only the
    image inclusion and its exact size. -/

noncomputable def orderedRootProduct (b : Fin 6 → Bool) :
    SplitOctF2Aut :=
  unipotentWord6 b

theorem orderedRootProduct_eq_rootProduct (b : Fin 6 → Bool) :
    orderedRootProduct b =
      native.root (rootAt 0) (b 0) *
        native.root (rootAt 1) (b 1) *
        native.root (rootAt 2) (b 2) *
        native.root (rootAt 3) (b 3) *
        native.root (rootAt 4) (b 4) *
      native.root (rootAt 5) (b 5) := by
  simp only [orderedRootProduct, unipotentWord6, native_rootAt_apply]

theorem orderedRootProduct_mem (b : Fin 6 → Bool) :
    orderedRootProduct b ∈ positiveRootSubgroup := by
  exact nativeOrderedRootProduct_mem b

theorem orderedRootProduct_injective :
    Function.Injective orderedRootProduct := by
  exact unipotentWord6_injective

noncomputable def orderedRootProductEquiv :
    (Fin 6 → Bool) ≃ Set.range orderedRootProduct :=
  Equiv.ofInjective orderedRootProduct orderedRootProduct_injective

theorem orderedRootProduct_range_card :
    Nat.card (Set.range orderedRootProduct) = 64 := by
  exact nativeOrderedRootProduct_range_card

theorem orderedRootProduct_unique (x : Set.range orderedRootProduct) :
    ∃! b : Fin 6 → Bool, orderedRootProduct b = x.1 := by
  rcases x with ⟨x, ⟨b, rfl⟩⟩
  refine ⟨b, rfl, ?_⟩
  intro c hc
  exact orderedRootProduct_injective hc

end InfoGeometry.Algebra.Zorn.G2NativePositiveRootSubgroupSystem
