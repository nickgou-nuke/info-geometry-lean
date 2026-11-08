# Reversible Peirce gates: theorem contract

## Intake and provenance

The user supplied `Pasted text(20261106-155543).txt` and requested native
Lean 4 / Mathlib formalization and publication on the upstream repository.
The original 25,134-byte attachment was preserved without normalization.
Its SHA-256 is
`2ff378326bf52a519d6b6ac7cd8e2db2c424051d59bd74b0f7d734cee60465c8`.
The implementation base is `3d7eb6d9b0af5636ab12b3d0b91b82740507e49e`.

This contract records the mathematical content after distinguishing the
different carriers in the intake. The verification section records source
compilation and independent checks at their actual scope.

## Exact carriers and conventions

1. **Associative algebra.** In an arbitrary unital `Ring B`, fix `P * P = P`.
   Write `a = conePlus P A`, `b = coneMinus P C`,
   `u = conePlus P dA`, and `v = coneMinus P dC`.
   The existing `epistemicCornerShear P A C` is `(1+a)*(1+b)`;
   `epistemicCornerShearInv P A C` is `(1-b)*(1-a)`.
   Multiplication order is retained throughout.
2. **Actual differentiation.** A normed algebra over a nontrivially normed
   field supplies the topology and continuous linear maps for native
   `HasFDerivAt` and `fderiv`. The idempotent is fixed; differentiating a
   variable projector would add terms.
3. **Matrix cotangents.** Full finite complex matrices are viewed as a real
   normed vector space. The existing real Hilbert--Schmidt pairing is
   `MatrixTraceQuadratic.tracePair X Y = (Matrix.trace (star X * Y)).re`.
   A self-adjoint idempotent supplies the orthogonal corner projections.
   The pairing is positive definite, but is not the operator norm squared.
4. **Nested words.** Native `BinaryTree` stores labels at nodes; native
   `List (α × Bool)` stores opening and closing letters. Each closing letter
   has the inverse value of its matching opening letter. Native `FreeGroup`
   reduction and arbitrary group evaluation retain the order of the word.
5. **Zorn multiplication.** `Algebra.SplitOctonionZorn.SplitOctonion` is the
   existing full real, eight-dimensional split-octonion carrier, with cross
   terms in its nonassociative product. It is distinct from the associative
   Peirce ring and from the reduced `Projective.SplitOctonions.ZornMatrix`
   product. Brackets are explicit.

## Source ownership and smallest missing implications

The search covers repository-owned Lean sources, `proofs/`, relevant
documentation, and the pinned Mathlib sources, including alternate names for
shears, unipotents, corner projections, trace pairing, balanced words, and
Zorn products. A documentation or filename match is only a navigation lead.

| Existing owner | Reused surface | Missing implication addressed here |
| --- | --- | --- |
| `OperatorAlgebra.PeirceSpine.Basic` | `conePlus`, `coneMinus`, same-corner annihilation, additivity | Ordered variation and finite-word collapse |
| `OperatorAlgebra.PeirceSpine.EpistemicCompilerPeirceBridge` | `epistemicCornerShear`, `epistemicCornerShearInv`; inverse laws inside `master_epistemic_compiler_synthesis` | Focused reconstruction and right-trivialized variation |
| Mathlib calculus and continuous linear maps | Product rule and bounded linear multiplication | Actual derivative of the parameterized gate action |
| `Analysis.MatrixTraceQuadratic` | `tracePair`, symmetry, positive definiteness | Full-matrix cotangent pullback and scalar-loss chain rule |
| Mathlib `BinaryTree`, `DyckWord`, `FreeGroup`, `Units` | Native recursion, tree/Dyck correspondence, reduction, universal group evaluation and the units coercion homomorphism | Labeled nested-word construction, reduction, and specialization to the actual Peirce shear/inverse pair |
| `Canonical.ZornAssociatorKreinBridge` | Upper/lower products, cyclic `tripleDet`, both bracketings | Identify `tripleDet` with native `Matrix.det`, then prove the precisely bracketed triple anticommutator |

Existing consumers and import graphs are inspected before adding a new owner.
The new group-word construction has no dependency on Yangian terminology.

## Claim ledger

| Intake atom | Exact disposition |
| --- | --- |
| Same-corner products vanish | Existing algebraic theorem, reused |
| The ordered gate has a polynomial inverse | Existing theorem, used for reconstruction |
| `(dG)*G⁻¹ = u + (1+a)*v*(1-a)` | New exact ring identity, followed by an actual analytic derivative |
| `dy = u*y + (1+a)*v*mid + G*dx` | New output-coordinate derivative formula |
| Both parameter gradients can be expressed through output and midpoint | Real trace-pairing pullback on full matrices, with fixed self-adjoint `P` |
| Reconstructing an input and pulling back its cotangent use the same map | Reconstruction uses `G⁻¹`; the trace-pairing cotangent pullback uses `G⋆`. No unitarity assumption identifies them |
| The gradient is independent of the lower parameter | Only absence of an explicit lower coefficient after changing coordinates; the output and loss cotangent can still depend on that parameter |
| The formula is an exact finite first-order increment | In general there is a mixed quadratic remainder; derivative and finite increment must be distinguished |
| `[a,v]` is the full variation of `Σ = [a,b]` | With both parameters varying the linear variation is `[u,b] + [a,v]`; identifying a Berry curvature additionally needs geometric data |
| Nested inverse-labeled words cancel | Recursive native group-word reduction, for every finite tree |
| Same-corner openers provide a noncommutative syntax encoding | They commute; finite products depend on the sum of their corner parameters |
| Cancellation preserves a parse tree | All balanced trees have identity value, so this evaluation is not injective when labels exist |
| The Zorn triple anticommutator is a determinant times the unit | Valid on the existing full nonassociative Zorn carrier, with explicit bracketing and native `Matrix.det` of the ordered coordinate rows |
| All statements are `Ring` / `StarRing` theorems | False as a scope claim: calculus, positivity, trace pairing and Zorn multiplication require different structures |
| CPT equals inversion | Requires a specified CPT map and a compatibility proof; inverse-labeled words alone do not construct one |
| RTT, central quantum determinant, transfer spectra | No construction of the requested RTT formal-series algebra was found in the searched owners; these remain separate targets |
| Zero total memory, constant runtime, exact floating-point reversal, parser accuracy | No machine model, implementation, error bound or empirical result is supplied; none follows from the algebra alone |

## Dependency order

The algebraic branch is: corner multiplication laws → ordered gate variation
and reconstruction → native derivative → real matrix cotangent pullback →
scalar-loss chain rule. The word branch is: labeled tree traversal → native
free-group reduction → evaluation in arbitrary groups. Constructing the
actual Peirce shears as native units connects this reduction to the ordered
operator gates and their polynomial inverses. The same-corner
product theorem explains the loss of order in the proposed special encoding.
The Zorn branch uses its own nonassociative multiplication; there is no
unproved edge from that branch to the associative gate calculus or RTT theory.

## External mathematical context

Molev, Nazarov and Olshanskii, *Yangians and Classical Lie Algebras*,
[arXiv:hep-th/9409025](https://arxiv.org/abs/hep-th/9409025), define the
Yangian through formal generating series and an RTT relation. The shift,
entry order and `R`-matrix convention must be fixed before adopting a quantum
determinant formula. No centrality theorem for an arbitrary ring is inferred.

Gomez, Ren, Urtasun and Grosse, *The Reversible Residual Network:
Backpropagation Without Storing Activations*,
[NeurIPS 2017](https://papers.nips.cc/paper/2017/file/f9be311e65d81a9ad8150a60844bb94c-Paper.pdf),
give an implemented reversible-network architecture with activation storage
independent of depth. That algorithmic result is distinct from the algebraic
and analytic theorems in this change.

## Acceptance requirements

Preserve the pinned Lean and Mathlib versions. Serialize compilation with the
repository build lock. Independently inspect every new theorem's assumptions,
carrier, multiplication order and interpretation. Compile the fresh source
closure, independently recompile the changed owners and audit all their
declarations for axioms. Only `propext`, `Classical.choice` and `Quot.sound`
are permitted. Run the installed commit and push gates at their stated scope.
Record any root-build dependency obstruction without changing pins or claiming
that an isolated source-closure check is a successful root Lake build.

## Verification

### Source compilation

The five new modules contain 25 public theorems and two definitions. The
selected project-source dependency closure contains 138 modules: the five new
owners and 133 unchanged dependencies. The complete closure passed with
Lean `v4.34.1` (compiler commit
`5045d0056413266e57c625dcd7c365b10e377c52`) and Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`. All five new owner logs are empty,
with no errors or warnings. Unchanged baseline warnings are kept in the
verification logs.

The development runs compiled every module in this closure from source.
Proof repairs reused only the same source-hash-checked snapshot with
`--incremental`. No borrowed project cache was accepted as proof of
compilation. The maintained checker held the shared repository build lock.
Its final invocation selected these exact targets:

```bash
python3 tools/quality/check_operator_geometry.py \
  --repo "$repo" --mathlib "$mathlib" --work-dir "$verification/development" \
  --incremental \
  --target InfoGeometry.OperatorAlgebra.PeirceSpine.ReversibleGateVariation \
  --target InfoGeometry.Analysis.PeirceReversibleDifferential \
  --target InfoGeometry.Analysis.PeirceReversibleMatrixPullback \
  --target InfoGeometry.Algebra.NestedGroupWords \
  --target InfoGeometry.Canonical.ZornTripleContraction
```

The run used the repository checkout, exact pinned Mathlib checkout, and the
task verification directory for `repo`, `mathlib`, and `verification`. The
final source-closure receipt SHA-256 is
`2f20c7c79b4c459b5dc3a923eb505dd78d6db31e0f7bfdc174cf34e2925d2952`.

| New owner | Verified source SHA-256 |
| --- | --- |
| `InfoGeometry.OperatorAlgebra.PeirceSpine.ReversibleGateVariation` | `c23eaaea5b3e08e549f6b7b3cc3b3fc0f90fe63d3cc9e8e98f9f327dd287de99` |
| `InfoGeometry.Analysis.PeirceReversibleDifferential` | `0332ac7f3d77fd11e69f044a77536eaf4345f27f7dbf8772db4887b5d93c50a7` |
| `InfoGeometry.Analysis.PeirceReversibleMatrixPullback` | `6fad24310572b7ee23543c19627fef3cc9f0acea3147da04309fde4e8c4338d2` |
| `InfoGeometry.Algebra.NestedGroupWords` | `3b538ab36e97df38850b5180566216a955af1a94db9ebc8e1d6f4042311ac4fd` |
| `InfoGeometry.Canonical.ZornTripleContraction` | `3b62ed7c9a2a9b2558d292966b5a2c21177c0866b8e95dd104305c54e86bd4b4` |

### Independent verification

A non-author reviewer independently checked the statements and their carriers,
then recompiled all five new owners in a separate import root using the
unchanged QA runner. Every one of the 133 unchanged dependencies was checked
against the exact base Git blob, final source snapshot, compiler log and
artifact hash before its artifact was reused. All new owner artifacts were
built afresh. Source, dependency-pin, compiler, verification-tool and artifact
hashes were checked again after compilation.

The unchanged native audit enumerated all **55 declarations owned by the five
modules**, including private and compiler-generated auxiliaries. It rejected
unsafe/partial declarations and nonstandard axioms. The final run passed; its
observed axioms are exactly `propext`, `Classical.choice` and `Quot.sound`.
The traversal uses native `BinaryTree.rec`, which avoids introducing an owned
unsafe recursive implementation helper. No audit exception was added.

| Owner | Audited declarations |
| --- | ---: |
| `InfoGeometry.OperatorAlgebra.PeirceSpine.ReversibleGateVariation` | 16 |
| `InfoGeometry.Analysis.PeirceReversibleDifferential` | 23 |
| `InfoGeometry.Analysis.PeirceReversibleMatrixPullback` | 7 |
| `InfoGeometry.Algebra.NestedGroupWords` | 7 |
| `InfoGeometry.Canonical.ZornTripleContraction` | 2 |

All five new-owner compilation logs are empty. The preserved logs for the
unchanged baseline contain 230 existing warnings across 29 modules; these
are not new-owner warnings and were not suppressed. The final source scan
found no proof holes, custom axioms or proof bypasses in the five new owners.

The independent command used the same exact compiler and package pins:

```bash
python3 "$verification/qa/run_qa.py" \
  --repo "$repo" --reference "$verification/development" \
  --mathlib "$mathlib" --lean "$lean" \
  --work "$verification/qa/final-recursor" \
  --development-log "$verification/development.log" \
  --development-log "$verification/development-2.log" \
  --development-log "$verification/development-3.log" \
  --development-log "$verification/development-4.log" \
  --development-log "$verification/development-5.log" \
  --development-log "$verification/development-6.log" \
  --development-log "$verification/development-7.log"
```

The QA runner calls the repository's unchanged
`tools/quality/reviewed_audit_source.py` and uses the shared build lock.
The QA receipt SHA-256 is
`5bb74463fc03d222f5ca7761b416ffff306ea8df68fdd8ab2f80e61f262fd5cb`;
the native audit log SHA-256 is
`90763475573ce7f82e19ca736454fa93808a283c4a026b0049a56c3ad7ea87e8`.

Acceptance is `[kernel_verified]` for the exact declared statements and
`[accepted_limited_scope]` for the normalized fragment of the intake. The
unsupported claims in the ledger remain explicit open debt.

### Root-package integration boundary

These source and axiom checks do not certify the root Lake integration gate.
The checkout's pinned GIFT gitlink is
`e6f3c3ac2140c2324fb2ae029c32233e73aa5e92`, and its required
`external_refs/gift-framework-core/lakefile.lean` is unavailable. Dependency
pins and verification infrastructure are unchanged. The installed commit and
push gates are invoked for publication; their actual outcomes are recorded in
the pull request. This integration obstruction is separate from the verified
five-owner source closure and native declaration audit.
