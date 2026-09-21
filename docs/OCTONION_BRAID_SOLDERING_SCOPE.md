# Octonion operator transport: proved scope and missing hypotheses

`Synthesis/OctonionBraidSoldering.lean` imports the existing circular grading,
regular-action CAR, and categorical Artin braid owners. It introduces no
replacement octonion carrier, multiplication law, or braid presentation.

The operator sandwich `A J B` is associative as a binary operation with fixed
`J`. Algebra automorphisms transport it with the metric; keeping the same
metric requires the explicit hypothesis that the automorphism fixes `J`.
Merely linear braid maps need not preserve operator products.

The module retains the concrete regular-action multiplication defect on the
three circular root vectors. Associativity of endomorphism composition does
not imply `L(x*y) = L(x)L(y)`. The selected-mode CAR theorem is reused from its
owner and transported through algebra automorphisms; it does not follow merely
from a vector space having bilinear multiplication.

`Canonical/SplitOctonionRightRegularBraid.lean` now constructs a finite
`ArtinBraid 2` (three-strand) representation on the actual right-regular
endomorphisms. The operators are `majorana_i = R_(rootPlus i) + R_(rootMinus i)`
and the invertible gates are `1 + majorana_i * majorana_(i+1)`. The Artin
calculation reuses the existing Jordan--Wigner owner's algebraic lemma;
the CAR relations come from the native right-regular owner, not hypotheses.
Conjugation by these units supplies the sandwich action. The existing
`fockBdGEquiv` intertwines the exterior creation/contraction gates with these
right-regular gates. Neither the representation nor its faithfulness is
deduced from the circular `ZMod 3` grading alone.

This real finite Majorana representation is distinct from the complex
left-regular `YangBaxterZornBridge.zornPhi`; no identification between them is
claimed. `Synthesis/ZornBraidIntertwiner.lean` uses the latter's existing
canonical coordinate transport and extends its action to arbitrary braid
words and inverses on the existing categorical Zorn colimit.

The sandwich is not identified with a Fierz expansion or a spinor dyad.
Those constructions have their own adjoint, outer-product, and basis data in
`CliffordWeyl/SpinorBilinearSoldering.lean` and `SplitSpinorFierz.lean`.
Further intertwiners are required to identify these different constructions.

There is no knot-closure definition, knot invariant, nuclear dynamics,
stability theorem, anomaly calculation, or mass-gap estimate in this module.
The Artin relation equates braid words; it is not a trefoil or rigidity theorem.

## Verification

Full proof scripts contain no placeholders. Kernel checking is pending the
shared build lane; compilation is not yet certified.

```
python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock \
  InfoGeometry.Synthesis.OctonionBraidSoldering
```
