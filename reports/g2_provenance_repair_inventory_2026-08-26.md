# G₂ provenance-repair inventory — 2026-08-26

Scope: retained kernel-supported native additions plus renamed product-image / conditional-interface owners after freezing `main`.

Deleted/staged-out brute-force artifact lane:
- `lean/InfoGeometry/Algebra/Zorn/G2FlagCellWitnessCertificate.lean`
- `lean/InfoGeometry/Algebra/Zorn/G2FlagCellWitnessSoundness.lean`

Method: every retained owner below was checked with a narrow `lake env lean` invocation before any subsystem build; `#print axioms` was then run on each retained theorem. No broad build claims are made here.

## `lean/InfoGeometry/Algebra/Zorn/G2NativeRootSubgroupSystem.lean`

- owner summary: native root-subgroup axioms
- imports: `InfoGeometry.Algebra.Zorn.G2RootSubgroupBaseEquiv`
- carrier / quotient / proxy status: carrier-native; no quotient/proxy
- build evidence: narrow check: `lake env lean .../G2NativeRootSubgroupSystem.lean` exit 0; subsystem build: `lake build ...G2NativeRootSubgroupSystem ...G2NativeBruhatRootSubgroupSystem ...G2NativePositiveRootSubgroupSystem ...G2NativeOrderedRootProduct ...G2BruhatResidualLengthOne` exit 0

| theorem | exact statement | hypotheses | `#print axioms` | semantic classification |
|---|---|---|---|---|
| `native_parameter_card` | `theorem native_parameter_card (α : G2Root) : Nat.card (rootSubgroup α) = 2` | `(α` | `propext, Classical.choice, Quot.sound` | cardinality theorem |
| `native_parameter_mem` | `theorem native_parameter_mem (α : G2Root) (t : Bool) : (native.parameter α t : rootSubgroup α).1 ∈ rootSubgroup α` | `(α` | `propext, Classical.choice, Lean.ofReduceBool, Lean.trustCompiler, Quot.sound` | membership theorem |
| `native_parameter_surjective` | `theorem native_parameter_surjective (α : G2Root) : Function.Surjective (native.parameter α)` | `(α` | `propext, Classical.choice, Lean.ofReduceBool, Lean.trustCompiler, Quot.sound` | finite-carrier surjectivity/bijectivity theorem |
| `native_root_element` | `theorem native_root_element (α : G2Root) (t : Bool) : ((native.parameter α t : rootSubgroup α) : OperatorAlgebra.G2TwoAutomorphismTheorem.SplitOctF2Aut) = xRoot α t` | `(α` | `propext, Classical.choice, Lean.ofReduceBool, Lean.trustCompiler, Quot.sound` | native root-subgroup axioms |
| `native_root_zero` | `theorem native_root_zero (α : G2Root) : xRoot α false = (1 : OperatorAlgebra.G2TwoAutomorphismTheorem.SplitOctF2Aut)` | `(α` | `propext, Classical.choice, Lean.ofReduceBool, Lean.trustCompiler, Quot.sound` | native root-subgroup axioms |
| `native_root_additive` | `theorem native_root_additive (α : G2Root) (a b : Bool) : xRoot α (a ^^ b) = xRoot α a * xRoot α b` | `(α` | `propext, Classical.choice, Lean.ofReduceBool, Lean.trustCompiler, Quot.sound` | native root-subgroup axioms |
| `native_root_inverse` | `theorem native_root_inverse (α : G2Root) (t : Bool) : (xRoot α t)⁻¹ = xRoot α t` | `(α` | `propext, Classical.choice, Quot.sound` | native root-subgroup axioms |
| `native_root_injective` | `theorem native_root_injective (α : G2Root) : Function.Injective (fun t : Bool => xRoot α t)` | `(α` | `propext, Classical.choice, Lean.ofReduceBool, Lean.trustCompiler, Quot.sound` | injectivity theorem |
| `native_c_transport` | `theorem native_c_transport (α : G2Root) (t : Bool) : (rootSubgroupEquiv_c α).toEquiv (native.parameter α t) = native.parameter (cAction α) t` | `(α` | `propext, Classical.choice, Lean.ofReduceBool, Lean.trustCompiler, Quot.sound` | readback/transport theorem |
| `native_s_transport` | `theorem native_s_transport (α : G2Root) (t : Bool) : (rootSubgroupEquiv_s α).toEquiv (native.parameter α t) = native.parameter (sAction α) t` | `(α` | `propext, Classical.choice, Lean.ofReduceBool, Lean.trustCompiler, Quot.sound` | readback/transport theorem |

## `lean/InfoGeometry/Algebra/Zorn/G2NativeBruhatRootSubgroupSystem.lean`

- owner summary: native Bruhat root-subgroup axioms
- imports: `InfoGeometry.Algebra.Zorn.G2NativeRootSubgroupSystem`
- carrier / quotient / proxy status: carrier-native; no quotient/proxy
- build evidence: narrow check: `lake env lean .../G2NativeBruhatRootSubgroupSystem.lean` exit 0 (warning: unnecessary intro suggestion); same root/product subsystem build exit 0

| theorem | exact statement | hypotheses | `#print axioms` | semantic classification |
|---|---|---|---|---|
| `native_root_mem` | `theorem native_root_mem (α : G2Root) (t : Bool) : xRoot α t ∈ rootSubgroup α` | `(α` | `propext, Classical.choice, Lean.ofReduceBool, Lean.trustCompiler, Quot.sound` | membership theorem |
| `native_root_zero` | `theorem native_root_zero (α : G2Root) : xRoot α false = 1` | `(α` | `propext, Classical.choice, Lean.ofReduceBool, Lean.trustCompiler, Quot.sound` | native Bruhat root-subgroup axioms |
| `native_root_additive` | `theorem native_root_additive (α : G2Root) (s t : Bool) : xRoot α (s ^^ t) = xRoot α s * xRoot α t` | `(α` | `propext, Classical.choice, Lean.ofReduceBool, Lean.trustCompiler, Quot.sound` | native Bruhat root-subgroup axioms |
| `native_root_inverse` | `theorem native_root_inverse (α : G2Root) (t : Bool) : (xRoot α t)⁻¹ = xRoot α t` | `(α` | `propext, Classical.choice, Quot.sound` | native Bruhat root-subgroup axioms |
| `native_root_injective` | `theorem native_root_injective (α : G2Root) : Function.Injective (xRoot α)` | `(α` | `propext, Classical.choice, Lean.ofReduceBool, Lean.trustCompiler, Quot.sound` | injectivity theorem |

## `lean/InfoGeometry/Algebra/Zorn/G2NativePositiveRootSubgroupSystem.lean`

- owner summary: positive-root native interface plus ordered-product image facts
- imports: `InfoGeometry.Algebra.Zorn.G2BruhatResidualRoots`, `InfoGeometry.Algebra.Zorn.G2NativeOrderedRootProduct`
- carrier / quotient / proxy status: carrier-native; image-only, not quotient proxy
- build evidence: narrow check: `lake env lean .../G2NativePositiveRootSubgroupSystem.lean` exit 0; same root/product subsystem build exit 0

| theorem | exact statement | hypotheses | `#print axioms` | semantic classification |
|---|---|---|---|---|
| `native_root_mem` | `theorem native_root_mem (α : G2PositiveRoot) (t : Bool) : native.root α t ∈ positiveRootSubgroup` | `(α` | `propext, Classical.choice, Lean.ofReduceBool, Lean.trustCompiler, Quot.sound` | membership theorem |
| `native_root_zero` | `theorem native_root_zero (α : G2PositiveRoot) : native.root α false = 1` | `(α` | `propext, Classical.choice, Lean.ofReduceBool, Lean.trustCompiler, Quot.sound` | positive-root native interface plus ordered-product image facts |
| `native_root_additive` | `theorem native_root_additive (α : G2PositiveRoot) (s t : Bool) : native.root α (s ^^ t) = native.root α s * native.root α t` | `(α` | `propext, Classical.choice, Lean.ofReduceBool, Lean.trustCompiler, Quot.sound` | positive-root native interface plus ordered-product image facts |
| `native_root_injective` | `theorem native_root_injective (α : G2PositiveRoot) : Function.Injective (native.root α)` | `(α` | `propext, Classical.choice, Lean.ofReduceBool, Lean.trustCompiler, Quot.sound` | injectivity theorem |
| `native_rootAt_apply` | `theorem native_rootAt_apply (i : Fin 6) (t : Bool) : native.root (rootAt i) t = positiveRootAction i t` | `(i` | `propext, Classical.choice, Lean.ofReduceBool, Lean.trustCompiler, Quot.sound` | positive-root native interface plus ordered-product image facts |
| `orderedRootProduct_eq_rootProduct` | `theorem orderedRootProduct_eq_rootProduct (b : Fin 6 → Bool) : orderedRootProduct b = native.root (rootAt 0) (b 0) * native.root (rootAt 1) (b 1) * native.root (rootAt 2) (b 2) * native.root (rootAt 3) (b 3) * native.root (rootAt 4) (b 4) * native.root (rootAt 5) (b 5)` | `(b` | `propext, Classical.choice, Lean.ofReduceBool, Lean.trustCompiler, Quot.sound` | positive-root native interface plus ordered-product image facts |
| `orderedRootProduct_mem` | `theorem orderedRootProduct_mem (b : Fin 6 → Bool) : orderedRootProduct b ∈ positiveRootSubgroup` | `(b` | `propext, Classical.choice, Quot.sound` | membership theorem |
| `orderedRootProduct_injective` | `theorem orderedRootProduct_injective : Function.Injective orderedRootProduct` | `none` | `propext, Classical.choice, Quot.sound` | injectivity theorem |
| `orderedRootProduct_range_card` | `theorem orderedRootProduct_range_card : Nat.card (Set.range orderedRootProduct) = 64` | `none` | `propext, Classical.choice, Quot.sound` | cardinality theorem |
| `orderedRootProduct_unique` | `theorem orderedRootProduct_unique (x : Set.range orderedRootProduct) : ∃! b : Fin 6 → Bool, orderedRootProduct b = x.1` | `(x` | `propext, Classical.choice, Quot.sound` | positive-root native interface plus ordered-product image facts |

## `lean/InfoGeometry/Algebra/Zorn/G2NativeOrderedRootProduct.lean`

- owner summary: ordered-product image/injectivity
- imports: `InfoGeometry.Algebra.Zorn.G2UnipotentWord6Cardinality`
- carrier / quotient / proxy status: carrier-native image; not subgroup equality
- build evidence: narrow check: `lake env lean .../G2NativeOrderedRootProduct.lean` exit 0; same root/product subsystem build exit 0

| theorem | exact statement | hypotheses | `#print axioms` | semantic classification |
|---|---|---|---|---|
| `unipotentWord6_injective` | `theorem unipotentWord6_injective : Function.Injective unipotentWord6` | `none` | `propext, Classical.choice, Quot.sound` | injectivity theorem |
| `nativeOrderedRootProduct_mem` | `theorem nativeOrderedRootProduct_mem (b : Fin 6 → Bool) : unipotentWord6 b ∈ positiveRootSubgroup` | `(b` | `propext, Classical.choice, Quot.sound` | membership theorem |
| `nativeOrderedRootProduct_range_card` | `theorem nativeOrderedRootProduct_range_card : Nat.card (Set.range unipotentWord6) = 64` | `none` | `propext, Classical.choice, Quot.sound` | cardinality theorem |

## `lean/InfoGeometry/Algebra/Zorn/G2BruhatResidualLengthOne.lean`

- owner summary: selected concrete rows / length-one residual cardinalities
- imports: `InfoGeometry.Algebra.Zorn.G2BruhatResidual`, `InfoGeometry.GroupTheory.G2BruhatInversions`
- carrier / quotient / proxy status: carrier-native; no quotient/proxy
- build evidence: narrow check: `lake env lean .../G2BruhatResidualLengthOne.lean` exit 0; same root/product subsystem build exit 0

| theorem | exact statement | hypotheses | `#print axioms` | semantic classification |
|---|---|---|---|---|
| `first_simple_length` | `theorem first_simple_length : dihedralLength (0, true) = 1` | `none` | `propext, Quot.sound` | selected concrete rows / length-one residual cardinalities |
| `second_simple_length` | `theorem second_simple_length : dihedralLength (1, true) = 1` | `none` | `propext, Quot.sound` | selected concrete rows / length-one residual cardinalities |
| `first_simple_residual_exponent_card` | `theorem first_simple_residual_exponent_card : Fintype.card (BruhatResidualExponent (0, true)) = 2` | `none` | `propext, Classical.choice, Quot.sound` | cardinality theorem |
| `second_simple_residual_exponent_card` | `theorem second_simple_residual_exponent_card : Fintype.card (BruhatResidualExponent (1, true)) = 2` | `none` | `propext, Classical.choice, Quot.sound` | cardinality theorem |

## `lean/InfoGeometry/Algebra/Zorn/G2ConcreteBruhatOrbitCertificate.lean`

- owner summary: conditional orbit-membership assembly
- imports: `InfoGeometry.Algebra.Zorn.G2FlagOrbitPartitionCertificate`, `InfoGeometry.Algebra.Zorn.G2GroupOrderReduction`
- carrier / quotient / proxy status: quotient-explicit; proxy/hypothesis interface
- build evidence: narrow check exit 0; subsystem build: `lake build ...G2ConcreteBruhatOrbitCertificate ...G2Fin189OrbitMembership ...G2FlagFactorizationRecursion ...G2FactorizationAlignmentCertificate` exit 0

| theorem | exact statement | hypotheses | `#print axioms` | semantic classification |
|---|---|---|---|---|
| `covering_eq_univ` | `theorem covering_eq_univ (enum : Fin 189 ≃ CarrierQuotient) (p : Fin 12 → WeylG2) (cells : Fin 12 → Finset (Fin 189)) (hcell : ∀ (k : Fin 12) (i : Fin 189), i ∈ cells k → ∃ b : SplitOctF2Aut, b ∈ InfoGeometry.Algebra.Zorn.G2TwoPCSubgroupClosure.unipotentSubgroup ∧ enum i = b • (QuotientGroup.mk (weylNF (p k).1 (p k).2) : CarrierQuotient)) (hpartition : Finset.univ.biUnion cells = Finset.univ) : concreteBruhatCovering = Set.univ` | `(enum` | `propext, Classical.choice, Quot.sound` | conditional orbit-membership assembly |
| `quotient_card` | `theorem quotient_card (enum : Fin 189 ≃ CarrierQuotient) : Nat.card CarrierQuotient = 189` | `(enum` | `propext, Classical.choice, Quot.sound` | cardinality theorem |
| `ambient_order` | `theorem ambient_order (enum : Fin 189 ≃ CarrierQuotient) : Nat.card SplitOctF2Aut = 12096` | `(enum` | `propext, Classical.choice, Lean.ofReduceBool, Lean.trustCompiler, Quot.sound` | conditional orbit-membership assembly |

## `lean/InfoGeometry/Algebra/Zorn/G2Fin189OrbitMembership.lean`

- owner summary: conditional orbit-membership assembly
- imports: `InfoGeometry.Algebra.Zorn.G2CellFactorizationCertificate`, `InfoGeometry.Algebra.Zorn.G2ConcreteBruhatOrbitCertificate`
- carrier / quotient / proxy status: quotient-explicit; proxy via `CellFactorizationCertificate`
- build evidence: narrow check exit 0; same orbit/factorization subsystem build exit 0

| theorem | exact statement | hypotheses | `#print axioms` | semantic classification |
|---|---|---|---|---|
| `fin189_orbit_membership` | `theorem fin189_orbit_membership (C : CellFactorizationCertificate) (k : Fin 12) (i : Fin 189) (hi : i ∈ orbitCells k) : ∃ b : SplitOctF2Aut, b ∈ unipotentSubgroup ∧ G2FlagOrbitPartitionCertificate.orbitEnum i = b • (QuotientGroup.mk (weylNF (orbitWeyl k).1 (orbitWeyl k).2) : G2ConcreteBruhatOrbitCertificate.CarrierQuotient)` | `(C` | `propext, Classical.choice, Quot.sound` | membership theorem |
| `concreteBruhatCovering_eq_univ_of_factorization` | `theorem concreteBruhatCovering_eq_univ_of_factorization (enum : Fin 189 ≃ G2ConcreteBruhatOrbitCertificate.CarrierQuotient) (C : CellFactorizationCertificate) (henum : ∀ i : Fin 189, enum i = G2FlagOrbitPartitionCertificate.orbitEnum i) : concreteBruhatCovering = Set.univ` | `(enum` | `propext, Classical.choice, Quot.sound` | selected-row factorization theorem |

## `lean/InfoGeometry/Algebra/Zorn/G2FlagFactorizationRecursion.lean`

- owner summary: selected-row factorization recursion
- imports: `InfoGeometry.Algebra.Zorn.G2CASFactorizationCarrier`, `InfoGeometry.Algebra.Zorn.G2FlagOrbitPartitionCertificate`, `InfoGeometry.Algebra.Zorn.G2FlagWordCertificateEval`, `InfoGeometry.Algebra.Zorn.G2TwoConcreteWeylG2`, `InfoGeometry.Algebra.Zorn.G2TwoBruhatClassification`, `Mathlib.Algebra.Group.Basic`, `Mathlib.Data.Fin.Basic`
- carrier / quotient / proxy status: carrier-native recursion with explicit predecessor interface
- build evidence: narrow check exit 0; same orbit/factorization subsystem build exit 0

| theorem | exact statement | hypotheses | `#print axioms` | semantic classification |
|---|---|---|---|---|
| `FactorizationStep.factorization_of_predecessor` | `theorem FactorizationStep.factorization_of_predecessor {G K ι : Type*} [Group G] {T : FactorizationTarget G K ι} {k : K} {n : ι} {r : ι → ι → Prop} (step : FactorizationStep T k n r) (hpred : T.representative k step.predecessor = T.factorized k step.predecessor) : T.representative k n = T.factorized k n` | `step, hpred` | `propext, Classical.choice, Quot.sound` | selected-row factorization theorem |
| `factorization_of_predecessor` | `theorem factorization_of_predecessor {ι : Type*} (T : FactorizationTarget G K ι) (r : ι → ι → Prop) (hwell : WellFounded r) (hbase : ∀ k i, (∀ j, ¬ r j i) → T.representative k i = T.factorized k i) (hstep : ∀ k i, (∃ j, r j i) → FactorizationStep T k i r) : ∀ k i, T.representative k i = T.factorized k i` | `{ι` | `propext, Classical.choice, Quot.sound` | selected-row factorization theorem |
| `factorization_of_depth` | `theorem factorization_of_depth {G K ι : Type*} [Group G] (T : FactorizationTarget G K ι) (depth : ι → ℕ) (hbase : ∀ k i, depth i = 0 → T.representative k i = T.factorized k i) (hstep : ∀ k i, depth i ≠ 0 → DepthFactorizationStep T depth k i) : ∀ k i, T.representative k i = T.factorized k i` | `{G K ι` | `none` | selected-row factorization theorem |
| `flagRepresentative_factorization_of_cell_certificate` | `theorem flagRepresentative_factorization_of_cell_certificate (C : G2CellPredecessorCertificate k) : ∀ i, i ∈ orbitCells k → flagRepresentative i = g2FlagFactorizationTarget.factorized k i` | `(C` | `propext, Classical.choice, Quot.sound` | selected-row factorization theorem |
| `flagRepresentative_factorization_of_predecessor_certificate` | `theorem flagRepresentative_factorization_of_predecessor_certificate (hbase : ∀ k i, (∀ j : Fin 189, ¬ j.val < i.val) → flagRepresentative i = collect (leftFactorWord k i) * weylNF (orbitWeyl k).1 (orbitWeyl k).2 * collect (rightFactorWord k i)) (hstep : ∀ k i, (∃ j : Fin 189, j.val < i.val) → FactorizationStep g2FlagFactorizationTarget k i (fun j i => j.val < i.val)) : ∀ (k : Fin 12) (i : Fin 189), flagRepresentative i = collect (leftFactorWord k i) * weylNF (orbitWeyl k).1 (orbitWeyl k).2 * collect (rightFactorWord k i)` | `(hbase` | `propext, Classical.choice, Quot.sound` | selected-row factorization theorem |

## `lean/InfoGeometry/Algebra/Zorn/G2FactorizationAlignmentCertificate.lean`

- owner summary: selected-row factorization/alignment interface
- imports: `InfoGeometry.Algebra.Zorn.G2QuotientRepresentativeInjectivity`
- carrier / quotient / proxy status: quotient-explicit; proxy package of obligations
- build evidence: narrow check exit 0; same orbit/factorization subsystem build exit 0

| theorem | exact statement | hypotheses | `#print axioms` | semantic classification |
|---|---|---|---|---|
| `generic_factorization` | `theorem generic_factorization (C : FactorizationAlignmentCertificate) : ∀ k i, flagRepresentative i = collect (leftFactorWord k i) * weylNF (orbitWeyl k).1 (orbitWeyl k).2 * collect (rightFactorWord k i)` | `(C` | `propext, Classical.choice, Quot.sound` | selected-row factorization theorem |
| `concrete_factorization` | `theorem concrete_factorization (C : ConcreteFactorizationAlignmentCertificate) : ∀ k i, flagRepresentative i = collect (leftFactorWord k i) * weylNF (orbitWeyl k).1 (orbitWeyl k).2 * collect (rightFactorWord k i)` | `(C` | `propext, Classical.choice, Quot.sound` | selected-row factorization theorem |
| `generic_alignment` | `theorem generic_alignment (C : FactorizationAlignmentCertificate) : ∀ i j, quotientRepresentative i = quotientRepresentative j → ∃ k : Fin 12, i ∈ orbitCells k ∧ j ∈ orbitCells k ∧ residualWord k i = residualWord k j` | `(C` | `propext, Classical.choice, Quot.sound` | alignment interface theorem |
| `concrete_alignment` | `theorem concrete_alignment (C : ConcreteFactorizationAlignmentCertificate) : ∀ i j, quotientRepresentative i = quotientRepresentative j → ∃ k : Fin 12, i ∈ orbitCells k ∧ j ∈ orbitCells k ∧ residualWord k i = residualWord k j` | `(C` | `propext, Classical.choice, Quot.sound` | alignment interface theorem |
| `concrete_quotientRepresentative_injective` | `theorem concrete_quotientRepresentative_injective (C : ConcreteFactorizationAlignmentCertificate) : Function.Injective quotientRepresentative` | `(C` | `propext, Classical.choice, Quot.sound` | injectivity theorem |
| `concrete_factorization_alignment` | `theorem concrete_factorization_alignment (C : ConcreteFactorizationAlignmentCertificate) (hsurj : Function.Surjective quotientRepresentative) : (∀ k i, flagRepresentative i = collect (leftFactorWord k i) * weylNF (orbitWeyl k).1 (orbitWeyl k).2 * collect (rightFactorWord k i)) ∧ (∀ i j, quotientRepresentative i = quotientRepresentative j → ∃ k : Fin 12, i ∈ orbitCells k ∧ j ∈ orbitCells k ∧ residualWord k i = residualWord k j) ∧ Function.Injective quotientRepresentative ∧ Nonempty (Fin 189 ≃ InfoGeometry.Algebra.Zorn.G2NativeQuotientRepresentative.CarrierQuotient)` | `(C` | `propext, Classical.choice, Quot.sound` | alignment interface theorem |
| `quotientRepresentative_injective` | `theorem quotientRepresentative_injective (C : FactorizationAlignmentCertificate) : Function.Injective quotientRepresentative` | `(C` | `propext, Classical.choice, Quot.sound` | injectivity theorem |

## `lean/InfoGeometry/Algebra/Zorn/G2CanonicalResidualTopEquiv.lean`

- owner summary: product-image equivalence for top residual fiber
- imports: `InfoGeometry.Algebra.Zorn.G2BruhatResidualCanonicalEquiv`, `InfoGeometry.Algebra.Zorn.G2TopOrderedRootProduct`, `InfoGeometry.Algebra.Zorn.G2BruhatResidual`
- carrier / quotient / proxy status: finite carrier equivalence; not subgroup equality
- build evidence: narrow check exit 0; subsystem build: `lake build ...G2NativeFlagStabilizerReadback ...G2NativeFlagStabilizerCardinality ...G2NativeIntrinsicLineFiberBridge ...G2NativeIntrinsicFlagBridge ...G2CanonicalResidualTopEquiv ...G2CanonicalResidualPCEquiv ...G2BruhatResidualEquiv` exit 0

| theorem | exact statement | hypotheses | `#print axioms` | semantic classification |
|---|---|---|---|---|
| `canonicalTopResidual_card` | `theorem canonicalTopResidual_card : Nat.card (CanonicalResidualExponent (weylElementOfNF (3, false))) = Nat.card (residualSubgroup (3, false))` | `none` | `propext, Classical.choice, Lean.ofReduceBool, Lean.trustCompiler, Quot.sound` | cardinality theorem |
| `canonicalTopResidual_card_eq_sixtyFour` | `theorem canonicalTopResidual_card_eq_sixtyFour : Nat.card (CanonicalResidualExponent (weylElementOfNF (3, false))) = 64` | `none` | `propext, Classical.choice, Lean.ofReduceBool, Lean.trustCompiler, Quot.sound` | cardinality theorem |

## `lean/InfoGeometry/Algebra/Zorn/G2CanonicalResidualPCEquiv.lean`

- owner summary: product-image equivalence for longest-cell PC image
- imports: `InfoGeometry.Algebra.Zorn.G2CanonicalResidualPCWords`, `InfoGeometry.Algebra.Zorn.G2TwoPCSubgroupClosure`, `InfoGeometry.Algebra.Zorn.G2NativeOnePointStabilizer`
- carrier / quotient / proxy status: finite carrier equivalence; no generic residual equality
- build evidence: narrow check exit 0; same residual/stabilizer/bridge subsystem build exit 0

| theorem | exact statement | hypotheses | `#print axioms` | semantic classification |
|---|---|---|---|---|
| `canonicalResidualPCWord_mem_unipotent` | `theorem canonicalResidualPCWord_mem_unipotent (e : CanonicalResidualExponent G2WeylElement.w0) : canonicalResidualPCWord G2WeylElement.w0 e ∈ unipotentSubgroup` | `(e` | `propext, Classical.choice, Quot.sound` | membership theorem |
| `canonicalW0PCWordToUnipotent_injective` | `theorem canonicalW0PCWordToUnipotent_injective : Function.Injective canonicalW0PCWordToUnipotent` | `none` | `propext, Classical.choice, Lean.ofReduceBool, Lean.trustCompiler, Quot.sound` | injectivity theorem |
| `canonicalW0PCWordToUnipotent_bijective` | `theorem canonicalW0PCWordToUnipotent_bijective : Function.Bijective canonicalW0PCWordToUnipotent` | `none` | `propext, Classical.choice, Lean.ofReduceBool, Lean.trustCompiler, Quot.sound` | finite-carrier surjectivity/bijectivity theorem |
| `canonicalW0PCWordEquiv_card` | `theorem canonicalW0PCWordEquiv_card : Nat.card (CanonicalResidualExponent G2WeylElement.w0) = Nat.card unipotentSubgroup` | `none` | `propext, Classical.choice, Lean.ofReduceBool, Lean.trustCompiler, Quot.sound` | cardinality theorem |

## `lean/InfoGeometry/Algebra/Zorn/G2BruhatResidualEquiv.lean`

- owner summary: product-image equivalence and counterexample boundary
- imports: `InfoGeometry.Algebra.Zorn.G2ResidualSimpleExact`, `InfoGeometry.Algebra.Zorn.G2BruhatResidualSimpleEquiv`, `InfoGeometry.Algebra.Zorn.G2BruhatResidual`, `InfoGeometry.GroupTheory.G2BruhatInversions`, `InfoGeometry.Algebra.Zorn.G2CanonicalResidualFibers`, `InfoGeometry.Algebra.Zorn.G2CanonicalResidualPCWords`
- carrier / quotient / proxy status: finite carrier/image interface; no generic residual equality
- build evidence: narrow check exit 0 (warning: unnecessary `simpa` at line 102); same residual/stabilizer/bridge subsystem build exit 0

| theorem | exact statement | hypotheses | `#print axioms` | semantic classification |
|---|---|---|---|---|
| `zeroBitPCExponentEquiv_symm_apply_succ` | `theorem zeroBitPCExponentEquiv_symm_apply_succ (f : Fin 5 → Bool) (i : Fin 5) : (zeroBitPCExponentEquiv.symm f).1 i.succ = f i` | `(f` | `propext, Quot.sound` | product-image equivalence and counterexample boundary |
| `correctedSimpleResidualCoordinateEquiv_apply` | `theorem correctedSimpleResidualCoordinateEquiv_apply (f : Fin 5 → Bool) : (correctedSimpleResidualCoordinateEquiv f).1 = G2TwoSylowSubgroup.pcWord (zeroBitPCExponentEquiv.symm f).1` | `(f` | `propext, Classical.choice, Lean.ofReduceBool, Lean.trustCompiler, Quot.sound` | product-image equivalence and counterexample boundary |
| `correctedSimpleResidualCoordinateEquiv_coordinate_readback` | `theorem correctedSimpleResidualCoordinateEquiv_coordinate_readback (f : Fin 5 → Bool) (i : Fin 5) : (zeroBitPCExponentEquiv (correctedSimpleResidualEquiv.symm (correctedSimpleResidualCoordinateEquiv f))) i = f i` | `(f` | `propext, Classical.choice, Lean.ofReduceBool, Lean.trustCompiler, Quot.sound` | product-image equivalence and counterexample boundary |
| `correctedSimpleResidualCoordinateEquiv_card` | `theorem correctedSimpleResidualCoordinateEquiv_card : Fintype.card (Fin 5 → Bool) = 32` | `none` | `propext, Classical.choice, Quot.sound` | cardinality theorem |
| `correctedSimpleResidual_card_eq_pow_five` | `theorem correctedSimpleResidual_card_eq_pow_five : Nat.card (residualSubgroup (2, true)) = 2 ^ 5` | `none` | `propext, Classical.choice, Lean.ofReduceBool, Lean.trustCompiler, Quot.sound` | cardinality theorem |
| `no_bruhatResidual_equiv_correctedSimple` | `theorem no_bruhatResidual_equiv_correctedSimple : ¬ Nonempty (BruhatResidualExponent (2, true) ≃ residualSubgroup (2, true))` | `none` | `propext, Classical.choice, Lean.ofReduceBool, Lean.trustCompiler, Quot.sound` | counterexample boundary theorem |
| `residualToPCExponent_eq_false_of_not_mem_active` | `theorem residualToPCExponent_eq_false_of_not_mem_active (w : G2WeylElement) (e : CanonicalResidualExponent w) (i : Fin 6) (hi : i ∉ canonicalActivePCIndices w) : residualToPCExponent w e i = false` | `(w` | `propext, Classical.choice, Quot.sound` | membership theorem |
| `residualToPCExponent_active_readback` | `theorem residualToPCExponent_active_readback (w : G2WeylElement) (e : CanonicalResidualExponent w) (α : { α : G2PositiveRoot // α ∈ canonicalSignedInversionRoots w }) : residualToPCExponent w e (rootPCAlignment α.1) = e α` | `(w` | `propext, Classical.choice, Quot.sound` | product-image equivalence and counterexample boundary |
| `canonicalResidualImage_card` | `theorem canonicalResidualImage_card : Nat.card {x : residualSubgroup (2, true) // x ∈ canonicalResidualImage} = 8` | `none` | `propext, Classical.choice, Lean.ofReduceBool, Lean.trustCompiler, Quot.sound` | cardinality theorem |
| `orderedInversionRoots_apply` | `theorem orderedInversionRoots_apply (p : WeylG2) (i : Fin (dihedralLength p)) : (orderedInversionRoots p i).1 ∈ bruhatInversionRoots p` | `(p` | `propext, Classical.choice, Quot.sound` | product-image equivalence and counterexample boundary |
| `orderedInversionRoots_bijective` | `theorem orderedInversionRoots_bijective (p : WeylG2) : Function.Bijective (orderedInversionRoots p)` | `(p` | `propext, Classical.choice, Quot.sound` | finite-carrier surjectivity/bijectivity theorem |

## `lean/InfoGeometry/Algebra/Zorn/G2NativeFlagStabilizerReadback.lean`

- owner summary: native readback plus conditional stabilizer census
- imports: `InfoGeometry.Algebra.Zorn.G2NativeFlagStabilizerTransport`, `InfoGeometry.Algebra.Zorn.G2PCWordSubgroupEquiv`, `InfoGeometry.Algebra.Zorn.G2StructuralFlagQuotient`
- carrier / quotient / proxy status: mixed: native inclusion facts plus conditional census proxy
- build evidence: narrow check exit 0; same residual/stabilizer/bridge subsystem build exit 0

| theorem | exact statement | hypotheses | `#print axioms` | semantic classification |
|---|---|---|---|---|
| `nativeFlagStabilizer_smul_baseIntrinsicFlag` | `theorem nativeFlagStabilizer_smul_baseIntrinsicFlag {g : SplitOctF2Aut} (hg : g ∈ nativeFlagStabilizer) : g • baseIntrinsicFlag = baseIntrinsicFlag` | `{g` | `propext, Classical.choice, Lean.ofReduceBool, Lean.trustCompiler, Quot.sound` | readback/transport theorem |
| `nativeFlagStabilizer_fixes_base_point` | `theorem nativeFlagStabilizer_fixes_base_point {g : SplitOctF2Aut} (hg : g ∈ nativeFlagStabilizer) : octImPointPerm g G2NativeOnePointStabilizer.nativeBaseIsotropicPoint = G2NativeOnePointStabilizer.nativeBaseIsotropicPoint` | `{g` | `propext, Classical.choice, Lean.ofReduceBool, Lean.trustCompiler, Quot.sound` | readback/transport theorem |
| `nativeFlagStabilizer_le_nativePointStabilizer` | `theorem nativeFlagStabilizer_le_nativePointStabilizer : nativeFlagStabilizer ≤ nativePointStabilizer` | `none` | `propext, Classical.choice, Lean.ofReduceBool, Lean.trustCompiler, Quot.sound` | native readback plus conditional stabilizer census |
| `nativeFlagStabilizer_eq_unipotentSubgroup_of_card_eq` | `theorem nativeFlagStabilizer_eq_unipotentSubgroup_of_card_eq (hcard : Fintype.card nativeFlagStabilizer = Fintype.card G2TwoPCSubgroupClosure.unipotentSubgroup) : nativeFlagStabilizer = G2TwoPCSubgroupClosure.unipotentSubgroup` | `(hcard` | `propext, Classical.choice, Lean.ofReduceBool, Lean.trustCompiler, Quot.sound` | cardinality theorem |
| `nativeFlagStabilizer_card_eq_64_of_flag_transitive_sigma` | `theorem nativeFlagStabilizer_card_eq_64_of_flag_transitive_sigma (h_enum : Fintype.card SplitOctF2Aut = 12096) (h_flag_card : Fintype.card (Σ p : OctImIsotropicPoint, IntrinsicLine p) = 189) (h_trans : Function.Surjective (fun g : SplitOctF2Aut => g • baseIntrinsicFlag)) : Fintype.card nativeFlagStabilizer = 64` | `(h_enum` | `propext, Classical.choice, Lean.ofReduceBool, Lean.trustCompiler, Quot.sound` | cardinality theorem |
| `nativeFlagStabilizer_card_eq_64_of_flag_transitive` | `theorem nativeFlagStabilizer_card_eq_64_of_flag_transitive (h_enum : Fintype.card SplitOctF2Aut = 12096) (h_flag_card : Fintype.card IntrinsicFlag = 189) (h_trans : Function.Surjective (fun g : SplitOctF2Aut => g • baseIntrinsicFlag)) : Fintype.card nativeFlagStabilizer = 64` | `(h_enum` | `propext, Classical.choice, Lean.ofReduceBool, Lean.trustCompiler, Quot.sound` | cardinality theorem |
| `nativeFlagStabilizer_preserves_base_line` | `theorem nativeFlagStabilizer_preserves_base_line {g : SplitOctF2Aut} (hg : g ∈ nativeFlagStabilizer) : HEq (intrinsicLineMap g baseIntrinsicLine) baseIntrinsicLine` | `{g` | `propext, Classical.choice, Lean.ofReduceBool, Lean.trustCompiler, Quot.sound` | readback/transport theorem |

## `lean/InfoGeometry/Algebra/Zorn/G2NativeFlagStabilizerCardinality.lean`

- owner summary: conditional stabilizer equality interface
- imports: `InfoGeometry.Algebra.Zorn.G2NativeFlagStabilizerReadback`
- carrier / quotient / proxy status: conditional proxy on sigma-cardinality/transitivity hypotheses
- build evidence: narrow check exit 0; same residual/stabilizer/bridge subsystem build exit 0

| theorem | exact statement | hypotheses | `#print axioms` | semantic classification |
|---|---|---|---|---|
| `nativeFlagStabilizer_eq_unipotentSubgroup_of_flag_census_sigma` | `theorem nativeFlagStabilizer_eq_unipotentSubgroup_of_flag_census_sigma (h_enum : Fintype.card SplitOctF2Aut = 12096) (h_flag_card : Fintype.card (Σ p : OctImIsotropicPoint, IntrinsicLine p) = 189) (h_trans : Function.Surjective (fun g : SplitOctF2Aut => g • baseIntrinsicFlag)) : nativeFlagStabilizer = unipotentSubgroup` | `(h_enum` | `propext, Classical.choice, Lean.ofReduceBool, Lean.trustCompiler, Quot.sound` | conditional census theorem |
| `nativeFlagStabilizer_eq_unipotentSubgroup_of_flag_census` | `theorem nativeFlagStabilizer_eq_unipotentSubgroup_of_flag_census (h_enum : Fintype.card SplitOctF2Aut = 12096) (h_flag_card : Fintype.card IntrinsicFlag = 189) (h_trans : Function.Surjective (fun g : SplitOctF2Aut => g • baseIntrinsicFlag)) : nativeFlagStabilizer = unipotentSubgroup` | `(h_enum` | `propext, Classical.choice, Lean.ofReduceBool, Lean.trustCompiler, Quot.sound` | conditional census theorem |

## `lean/InfoGeometry/Algebra/Zorn/G2NativeIntrinsicLineFiberBridge.lean`

- owner summary: conditional finite carrier line bridge
- imports: `InfoGeometry.Algebra.Zorn.G2NativeLineFiberDistinctness`, `InfoGeometry.Algebra.Zorn.G2IntrinsicBaseLineCensus`, `InfoGeometry.Algebra.Zorn.G2NativeOnePointStabilizer`, `Mathlib.Data.Fintype.EquivFin`
- carrier / quotient / proxy status: cardinality proxy; not geometric identification
- build evidence: narrow check exit 0; same residual/stabilizer/bridge subsystem build exit 0

| theorem | exact statement | hypotheses | `#print axioms` | semantic classification |
|---|---|---|---|---|
| `nativeLine_card_eq_intrinsicBaseLine_card` | `theorem nativeLine_card_eq_intrinsicBaseLine_card : Fintype.card NativeLine = Fintype.card (IntrinsicLine nativeBaseIsotropicPoint)` | `none` | `propext, Classical.choice, Lean.ofReduceBool, Lean.trustCompiler, Quot.sound` | cardinality theorem |
| `nativeLineCardinalityEquivBaseIntrinsicLine_surjective` | `theorem nativeLineCardinalityEquivBaseIntrinsicLine_surjective : Function.Surjective (nativeLineCardinalityEquivBaseIntrinsicLine : NativeLine → IntrinsicLine nativeBaseIsotropicPoint)` | `none` | `propext, Classical.choice, Lean.ofReduceBool, Lean.trustCompiler, Quot.sound` | finite-carrier surjectivity/bijectivity theorem |
| `not_three_distinct_named_parabolic_lines` | `theorem not_three_distinct_named_parabolic_lines : ¬ (lineZero ≠ lineInfinity ∧ lineInfinity ≠ lineOne ∧ lineZero ≠ lineOne)` | `none` | `propext, Classical.choice, Lean.ofReduceBool, Lean.trustCompiler, Quot.sound` | counterexample boundary theorem |

## `lean/InfoGeometry/Algebra/Zorn/G2NativeIntrinsicFlagBridge.lean`

- owner summary: conditional finite carrier flag bridge
- imports: `InfoGeometry.Algebra.Zorn.G2NativeFlagCardinality`, `InfoGeometry.Algebra.Zorn.G2InvariantIncidenceCandidates`, `InfoGeometry.Algebra.Zorn.G2IntrinsicLineFiberTransport`, `Mathlib.Data.Fintype.EquivFin`
- carrier / quotient / proxy status: cardinality proxy; not geometric identification
- build evidence: narrow check exit 0; same residual/stabilizer/bridge subsystem build exit 0

| theorem | exact statement | hypotheses | `#print axioms` | semantic classification |
|---|---|---|---|---|
| `nativeFlag_card_eq_intrinsicFlagSigma_card_of_card189` | `theorem nativeFlag_card_eq_intrinsicFlagSigma_card_of_card189 (hflag : Fintype.card (Σ p : OctImIsotropicPoint, IntrinsicLine p) = 189) : Fintype.card NativeFlag = Fintype.card (Σ p : OctImIsotropicPoint, IntrinsicLine p)` | `(hflag` | `propext, Classical.choice, Lean.ofReduceBool, Lean.trustCompiler, Quot.sound` | cardinality theorem |
| `nativeFlagCardinalityEquivIntrinsicFlagSigmaOfCard189_surjective` | `theorem nativeFlagCardinalityEquivIntrinsicFlagSigmaOfCard189_surjective (hflag : Fintype.card (Σ p : OctImIsotropicPoint, IntrinsicLine p) = 189) : Function.Surjective (nativeFlagCardinalityEquivIntrinsicFlagSigmaOfCard189 hflag : NativeFlag → (Σ p : OctImIsotropicPoint, IntrinsicLine p))` | `(hflag` | `propext, Classical.choice, Lean.ofReduceBool, Lean.trustCompiler, Quot.sound` | finite-carrier surjectivity/bijectivity theorem |

