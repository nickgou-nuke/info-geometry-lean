# Square-zero Peirce, Weyl-unit and weighted-trace synthesis

## Provenance and intended base

Adaptation of `Pasted text(20261024-074204).txt`, headed
`UnifiedGeometryOperatorSignificance.lean`. The inspected main revision is
`21189e55133ed207043f2f05e37aa52d1fc8a9f5`.

The source supplies a finite algebraic master theorem and a broader geometric
interpretation. This addition preserves the former's valid identities and
records the necessary corrections below. It does not certify the uploaded
standalone code unchanged or silently turn its broader claims into theorems.

## Owners reused

- `Singular.MoorePenrose`: actual four-equation inverse predicate.
- `Singular.SquareZeroChiralHodge`: exact, coexact, harmonic and chiral
  supports, inverse square-zero, partition/absorption and Hodge package.
- `Core.DiracSuperalgebra`: Majorana generators, support identities, star
  qualification and partial matrix-unit multiplication.
- `Core.JordanAssociatorRing`: the division-free associative-envelope
  associator identity and the square-zero inner-inverse associator law.

No alternative generalized-inverse predicate or duplicate support carrier is
introduced. Earlier PRs 203/204 are not required. No owner, umbrella import,
dependency pin, training code or other branch is changed.

## New theorem chain

1. A native MP witness for `(d,b)` and `d*d=0` supply the existing support
   decomposition. There is no unconditional inverse-existence theorem.
2. The unipotent product `(1+d)(1-b)(1+d)` equals
   `w = harmonicSupport d b + majoranaMinus d b`.
3. Both inverse equations are proved; `weylUnit` is a native `Aˣ`, with inverse
   `harmonicSupport d b - majoranaMinus d b`. Its fourth power is one and its
   conjugation swaps supports and sends `d` to `-b`, `b` to `-d`.
4. The supported third and sixth roots satisfy their cyclotomic polynomials
   and powers with `activeSupport d b` as constant/identity. Exact orders are
   not asserted. Their product with the skew generator recovers `Delta+d`.
5. For arbitrary central scalars `u,v`, the density `u*(bd)+v*(db)` obeys four
   eigen-relations and the two cross-multiplied intertwining laws. Squared
   parameters recover the intake's convention. An actually tracial native
   `LinearMap` transports these to weighted trace identities.
6. Native `Module.End` Jordan multiplication operators satisfy
   `[J_s,J_t](x)=[[s,t],x]` and the associative Leibniz rule. The source's
   associator orientation is related to this corrected bracket using the
   existing associator owner.
7. `peirce_weyl_trace_synthesis` connects the constructions on the same carrier.

## Corrections and qualifications, not silent reinterpretations

- **Sign:** With the source's unnormalized Jordan product,
  `J_s(J_t(x))-J_t(J_s(x))=[[s,t],x]`, not `[[t,s],x]`.
  Its associator `[t,x,s]_Jordan` equals the former. An integral matrix-unit
  counterexample refutes the opposite sign.
- **Cyclotomic two:** `Gamma^2=Delta` is the involution relation, not the
  polynomial `Phi_2(t)=t+1`. In the active corner, `-Delta` is a root of
  `Phi_2`; the nonzero integral grading is not. The third/fourth/sixth
  equations keep their intended supported constant term.
- **Associators:** Square-zero kills the appropriate support overlap; it does
  not annihilate every Jordan associator. The exact integral example has
  `[d,d,b]_Jordan=-2d`, not zero.
- **Hodge/complex terminology:** The harmonic idempotent is an algebraic
  complement. `d+b` need not be the metric operator `d+star d`. The skew
  operator has square `-Delta`, not necessarily ambient `-1`. The explicit
  three-dimensional example has a nonzero harmonic summand.
- **Geometry:** No manifold, differential, symplectic/Kähler form, connection,
  Ehresmann/Levi-Civita curvature, principal bundle or orientability class is
  constructed. These geometric names in the intake are motivation, not the
  type of the proved output.
- **KMS:** Scalar density/trace intertwining is proved, including zero weights.
  Neither positivity/normalization/faithfulness of the functional nor analytic
  strip boundary conditions or a real-time modular group are provided. The
  density annihilates the harmonic support; squaring arbitrary ring scalars
  by itself does not add an ordered positivity structure.
- **Exceptional claims:** The submitted master theorem works in associative
  `A`. It contains no split-octonion carrier, Clifford map, supertrace-zero
  Lie carrier, or F4/E6 classification. This PR does not manufacture one from
  the associative Jordan identity. Alternative multiplication, operator-lift
  faithfulness, supercolor closure and the associator-as-Nambu interpretation
  remain separate contracts requiring their own actual carriers and proofs.
- **Scope:** No universal theorem about all non-normal operators, all
  generalized-inverse existence, or exact finite order in all characteristics.

## Verification

The dedicated `peirce-weyl.yml` workflow compiles all five new modules and their
complete unchanged repository import closure in an isolated checkout of the
root-pinned Mathlib, under `/tmp/info-geometry-build.lock`. It uses public
`Lean.collectAxioms` to inspect all declarations originating in the new modules,
including generated declarations. It rejects unsafe/partial declarations and
all axioms outside `propext`, `Classical.choice`, `Quot.sound` without exemptions.

The workflow result and artifact are the acceptance evidence. This document
does not itself assert a passing run. The check is not a full root Lake package
build or an all-green repository CI claim. Source imports are never stripped,
dependency pins/sources are not changed, and no build cache is deleted.

Production import:

```lean
import InfoGeometry.Canonical.PeirceWeylSynthesis
```

Full-checkout check, with root package dependencies available:

```bash
python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock \
  InfoGeometry.Canonical.PeirceWeylExamples
```
