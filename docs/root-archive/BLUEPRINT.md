# InfoGeometry formalisation blueprint

This document records the repository's proof architecture. It separates
kernel-checked results from research interpretation and states the next
theorem frontier. The Lean kernel is the authority: graph exports, CAS
calculations, external papers and generated prose are design evidence only.

## Epistemic contract

Every promoted result has an explicit carrier, scalar field, ordering and
multiplication convention; a complete proof in a small owner file; a
successful relevant build; and no `sorry`, `admit`, custom axiom, proxy
witness or vacuous hypothesis.

`Iso`, `Equiv`, `LinearEquiv` and `LieEquiv` are distinct interfaces. A map is
not invertible merely because it is called a transport, and equality of
morphisms is not automatically a bundled higher morphism.

## Proof architecture

```text
concrete finite carriers
    -> native morphisms and exact readbacks
    -> structural invariants
    -> categorical limits/colimits
    -> interpretation and applications
```

The categorical owners (`Algebra/Grothendieck.lean`,
`Canonical/TensorTowerColimit.lean`, `Canonical/ErlangenColimitResolution.lean`
and the cone-uniqueness owner) are reused by concrete instances. Matrix code
does not replace an existing categorical theorem.

## G₂ finite layer

```text
Weyl parameters
    -> inversion-root labels
    -> Boolean residual coordinates
    -> verified PC-word coordinates
    -> SplitOctF2Aut subgroups
```

For the longest parameter `(3, false)`, the verified route is:

```text
bruhatInversionRoots
    -> root-PC alignment
    -> ordered root-product
    -> six-bit pcWord
    -> residualSubgroup (3, false)
```

`G2TopOrderedRootProduct.lean` supplies an explicit ordered-product
equivalence. `G2BruhatResidualTopEquiv.lean` supplies the semantic
finite-to-canonical residual bridge. These are separate constructions;
cardinality equality does not prove equality of their functions.

The corrected simple case uses `ZeroBitPCExponent`. It is not an equivalence
between the full `BruhatResidualExponent (2, true)` and its residual subgroup;
the repository proves the corresponding cardinality obstruction. Therefore a
generic theorem

```lean
BruhatResidualExponent p ≃ residualSubgroup p
```

requires a genuine intermediate root-subgroup normal form: ordered product,
membership, unique factorisation and generation/surjectivity. Finite carrier
enumeration alone is not semantic root identification.

## Spectral and colimit layer

```text
ExactCouple
    -> DerivedCouple
    -> iterated pages
    -> bounded/eventual stabilisation
    -> stabilised-tail cocone
    -> IsColimit
```

The colimit of an iso-legged stabilised tail is categorical. It is not by
itself the reconstruction theorem

```text
E∞ ≃ associated graded of the filtered target.
```

That theorem is a separate owner requiring explicit filtration,
exhaustiveness/separatedness and compatibility hypotheses. Dependent index
problems in `Convergence.lean` must not be hidden by casts or placeholders.

Finite Cantor-word stages provide a directed word tower and observable
colimit. They are not automatically a topological mapping cylinder, a
homological mapping cone, a homotopy type or a HoTT spectrum. These
constructions keep distinct names and carriers.

## Interpretation boundary

The repository can support a directed categorical–homological calculus:

```text
directed carriers
    -> morphisms and commuting equalities
    -> homology/spectral invariants
    -> limits and colimits
```

This supports path-like, causal and higher-coherence interpretations, but it
is not yet a formal DirHoTT, infinity-category, dagger category, quantum
cohomology ring or physical theory unless the structures and laws are
explicitly defined and kernel-checked.

In particular:

- Lean equality witnesses are not native univalence or higher-inductive types;
- directed rewriting need not be reversible, while causality is not identical
  to thermodynamic irreversibility;
- a chiral involution is not a dagger functor without contravariance,
  involutivity and composition laws;
- finite `weylNF` and real Weyl automorphisms remain distinct carriers until a
  real lift and compatibility theorem exist;
- quantum-Schubert data should be named for the flag variety `G₂/B`, not the
  finite group `G₂(2)`, unless a different object is explicitly defined.

## Promotion workflow

1. Audit existing definitions and dependents.
2. State the weakest correctly typed theorem.
3. Reuse the owning carrier and categorical infrastructure.
4. Prove one substantive lemma at a time.
5. Run `lake env lean` on the owner and the relevant aggregate build.
6. Run applicable quality gates, stage the source, and report exact evidence.

The guiding question is:

> What exact type-level or structural obstruction prevents the desired result,
> and what is the smallest native theorem that removes it?
