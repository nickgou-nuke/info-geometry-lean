# Non-isotropic three-point configuration: literature lemma chain

Target space:

```text
F_Q(C^D,3) = { (x1,x2,x3) | q(xi-xj) != 0 for all i<j }.
```

After translation this is the complement in `C^D x C^D` of the three
quadrics `QA=q(a)`, `QB=q(b)`, `QAB=q(a-b)`.

## Lemma Chain

1. **One-edge quadric complement.**
   Use the fibration `q : C^D \ {q=0} -> C*`; the fiber `q=1` is the affine
   smooth quadric.  Over `C`, this gives the visible edge classes
   `alpha` in degree `1` and `beta` in degree `D-1`.  For even `D`, the
   monodromy `x -> -x` acts trivially on middle cohomology.

2. **Three-divisor hypersurface arrangement model.**
   Use the Looijenga/Bibby/Dupont hypersurface-arrangement Orlik-Solomon
   spectral sequence/Gysin model for the complement of a hypersurface
   arrangement.  This is the correct replacement for an ordinary hyperplane
   Orlik-Solomon algebra.

3. **Resolution/wonderful compactification.**
   The natural projective compactification in `P^4 x P^4` has singular
   closures at the affine origins and along the projective diagonal.  Therefore
   one must first resolve/blow up and verify that the transformed boundary is a
   hypersurface arrangement before applying Dupont's comparison theorem.

4. **Relation-choice theorem.**
   Compute the Gysin maps for the resolved strata.  This is the step that must
   decide between the finite candidates currently separated in Lean:
   product/Leray rank `32`, OS-alpha rank `24`, and the corrected D4
   alpha/beta candidate.  The current strengthened interface records the
   rank-32 branch explicitly as `chosenPresentation = ModelChoice.productLeray`,
   while keeping the actual Dupont/Oaku comparison as a socket.

5. **Oaku--Takayama D-module computation.**
   As an independent algorithmic route, apply Oaku--Takayama to the affine
   hypersurface complement for
   `f = q(a) q(b) q(a-b)` in eight affine variables when `D=4`.  The needed
   external certificate is a Weyl-algebra/Groebner computation whose output
   matches the chosen finite presentation.  Lean records this as an explicit
   `OakuTakayamaDModuleLemma`, not as an in-kernel Weyl-Groebner engine.

6. **Point count to cohomology.**
   The polynomial point count is not by itself a Betti-number theorem.  It
   becomes cohomological only with a purity/mixed-Tate comparison theorem,
   following the Katz-style point-count-to-`E`-polynomial bridge.

7. **Cooperad functoriality.**
   Collision maps must extend to the resolved boundary, and Dupont functoriality
   must preserve the Gysin differential and signs.  This discharges the cooperad
   socket.

## Sources Found

- Clément Dupont, *The Orlik-Solomon model for hypersurface arrangements*,
  arXiv:1302.2103, Ann. Inst. Fourier 65 (2015), 2507-2545.
  <https://arxiv.org/abs/1302.2103>

- Published AIF page for Dupont's paper.
  <https://aif.centre-mersenne.org/articles/10.5802/aif.2994/>

- Dupont slides summarizing the Orlik-Solomon spectral sequence and the
  degeneration criterion for projective/pure cases.
  <https://people.dm.unipi.it/gaiffi/webpagePisafeb2016/slides/dupont.pdf>

- Edward Fadell and Lee Neuwirth, *Configuration Spaces*, Mathematica
  Scandinavica 10 (1962), 111-118.
  <https://eudml.org/doc/165793>

- Burt Totaro, *Configuration spaces of algebraic varieties*.
  <https://www.math.ucla.edu/~totaro/papers/public_html/config.pdf>

- Nicholas Katz appendix used in Hausel-Rodriguez-Villegas,
  *Mixed Hodge polynomials of character varieties*, for point-count to
  `E`-polynomial logic under the required hypotheses.
  <https://arxiv.org/pdf/math/0612668>

- Dan Petersen, *A spectral sequence for stratified spaces and configuration
  spaces of points*, Geometry & Topology 21 (2017), 2527-2555.
  <https://msp.org/gt/2017/21-4/gt-v21-n4-p16-s.pdf>

- Toshinori Oaku and Nobuki Takayama, *An algorithm for de Rham cohomology
  groups of the complement of an affine variety via D-module computation*.

## Lean Socket

The Lean encoding of this proof-roadmap is:

```text
proofs/NonIsoConf3LiteratureLemmaChain.lean
```

It packages the external obligations as:

```text
EdgeQuadricComplementLemma
DupontArrangementLemma
RelationChoiceLemma
OakuTakayamaDModuleLemma
PointCountPurityLemma
CooperadFunctorialityLemma
NonIsoConf3ExternalLemmaPackage
```

and proves that such a package discharges the current de Rham/cooperad sockets.
The strengthened bridge theorems are:

```text
literature_chain_productLeray_choice
literature_chain_rank32_discharge
PenroseSpinTilingCapstone.penrose_capstone_literature_rank32_oaku_bridge
```

These say, conditionally on the external Dupont/Oaku/purity/cooperad lemmas,
that the Penrose capstone channel receives the rank-32 product/Leray branch
rather than the rank-24 OS-alpha branch.
