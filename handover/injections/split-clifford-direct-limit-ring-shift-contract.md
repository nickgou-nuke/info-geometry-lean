# Ground-truth contract: ring-level tail shift for the split Clifford colimit

## Claim
For each finite offset `k`, the algebraic direct limit of the split Clifford
stages `SplitClNNAlg (n + k)` with the actual shifted transition maps is ring
isomorphic to the existing direct limit `SplitCliffordInfinity` of
`SplitClNNAlg n`. The equivalence is induced by the tower transition maps and
canonical stage maps.

## Carrier and operations
- Stage `n`: `InfoGeometry.Canonical.SplitCliffordTensorBridge.SplitClNNAlg n`.
- Original bond: `splitCliffordMap m n h : SplitClNNAlg m →ₐ[ℝ] SplitClNNAlg n`.
- Original colimit: root `DirectLimit SplitClNNAlg (fun m n h => splitCliffordMap m n h)`.
- Tail at `k`: root `DirectLimit (fun n => SplitClNNAlg (n + k))` with bond
  `splitCliffordMap (m + k) (n + k) (Nat.add_le_add_right h k)`.
- Multiplication and addition are the native algebraic direct-limit operations;
  no commutativity or scalar matrix model is introduced.

## Existing owner facts
- `Canonical/SplitCliffordDirectLimit.lean` defines
  `splitCliffordMap`, proves transition composition and installs
  `splitCliffordDirectedSystem`; `SplitCliffordInfinity` is its root direct
  limit.
- `Canonical/SplitCliffordDirectLimitShift.lean` already proves
  `splitCliffordModuleLimit_shift_equiv`, a module equivalence between the
  original module colimit and any fixed module tail.
- `Canonical/SplitCliffordTensorBridge.lean` proves finite-stage graded tensor
  factorization `SplitClNNAlg (n + 1) ≃ₐ[ℝ] SplitClNNTensorStep n` and head/tail
  generator readbacks.
- Mathlib `DirectLimit.Ring.lift`, `DirectLimit.Ring.lift_of`, and
  `DirectLimit.Ring.hom_ext` provide the ring colimit universal property for
  the root direct-limit construction.

## Smallest gap
The existing tail-shift equivalence is only linear. Construct compatible ring
homomorphisms in both directions using the actual stage transition maps and
prove they are inverse by `DirectLimit.Ring.hom_ext`.

## Explicit boundaries
This claim does not assert an equivalence
`Cl(1,1) ᵍ⊗ Cl(∞,∞) ≃ Cl(∞,∞)`: the tail stages form a cofinal shift, but a
colimit-level graded tensor product and its compatible maps are separate
structures. It also does not identify the algebraic colimit with an analytic
infinite tensor product or a completion.

## Verification target
New owner module importing the split direct-limit and Mathlib colimit owners;
verify with the repository's locked Lake build, no-placeholder scan, and
`#print axioms` on the resulting equivalence.
