# Koszul extensions and coarse splitting

## Source and theorem contract

Source: Hao Song, *From Koszul-Complex Stabilizer Models to Superselection
Profiles: Topological Rigidity and Nonsplit Extensions*, arXiv:2608.09913v1,
10 August 2026, Construction 2 (equations 155–158) and Appendix G
(equations G1–G8). The supplied 34-page PDF is the intake source.

The implementation covers the explicit algebraic construction described below.
The source statements, their hypotheses, and the scope boundaries are separate
from the broader classification claims of the paper.

1. Over a commutative coefficient ring, construct the three-generator Koszul
   differentials on an actual module, allowing their coefficients to be
   pairwise commuting linear endomorphisms. Keep the ambient endomorphism
   algebra noncommutative. Prove both adjacent composites vanish.
2. For modules `K0`, `K1`, `K2`, `K3`, maps `d1`, `d2`, `d3`, and compatible
   couplings `a : K3 →ₗ K1`, `b : K2 →ₗ K0`, construct the native mathlib
   short complex with differentials
   `D2(u,v) = (d2 u + a v, d3 v)` and
   `D1(x,y) = (d1 x - b y, d2 y)`.
   Prove exactness from the explicit hypotheses
   `range d2 = ker d1` and `range d3 = ker d2`.
3. Construct invertible triangular changes of coordinates and a native
   short-complex isomorphism to the uncoupled complex when
   `a = d2 ∘ G - H ∘ d3` and `b = Q ∘ d2 - d1 ∘ H`.
   Derive the induced mathlib homology isomorphism.
4. On the actual finite-support translation ring
   `R = AddMonoidAlgebra (ZMod 2) (Fin 3 → ℤ)`, realize the even-translation
   coefficient action by `y_i ↦ x_i²`. Construct the parity-lowering maps
   `T_j(x^n) = (n_j mod 2) x^(n-e_j)` as linear maps for that coefficient
   action, including negative exponents. Prove
   `T_j F_j + F_j T_j = id` and `T_j F_l = F_l T_j` for `j ≠ l`, where
   `F_j` is multiplication by `x_j - 1`. These are identities of operators
   on Laurent polynomials, not identities in their commutative scalar ring.
5. Use these maps to construct Appendix G's `G`, `H`, and `Q` for the eight
   constant vectors `a ∈ (ZMod 2)^3`, prove the splitting equations, and
   instantiate the native complex and homology isomorphisms.

The dependency order is: native linear maps and Koszul identities; compatible
triangular extension; finite-support parity operators and their even-translation
linearity; explicit splitting identities; short-complex isomorphism; homology
isomorphism. Each dependency must be an actual imported declaration.

## Implementation owners

| Owner under `lean/InfoGeometry/` | Main declarations and purpose |
|---|---|
| `Algebra/TriangularShortComplex.lean` | `complex`, `exact`, `homology_isZero`, `shear`, and `splittingIso`: compatible block differentials, conditional exactness, and signed splitting over any ring |
| `Quantum/KoszulThree.lean` | `d1`, `d2`, `d3`, `d1_comp_d2`, `d2_comp_d3`, and `coupling_compatible`: explicit signed cyclic Koszul maps with commuting operator coefficients |
| `Quantum/KoszulThreeExtension.lean` | `extension`, `G_H_identity`, `Q_H_identity`, and `coarseSplittingIso`: Construction 2 and the computed characteristic-two shear identities |
| `Quantum/EvenTranslationOperators.lean` | `lowerLinear_mul`, `lowerLinear_coarse_smul`, `lowering_mul_difference_add_difference_mul_lowering`, and `lowering_difference_noncommute`: actual Laurent operators and even-translation linearity |
| `Quantum/KoszulEvenTranslationSplitting.lean` | `splittingIso`, `splittingIso_middle_apply`, `splittingHomologyIso`, and `splittingHomologyLinearEquiv`: the concrete theorem for all `a : Fin 3 → ZMod 2` |

Import the final owner for the complete construction. Its namespace is
`InfoGeometry.Quantum.KoszulEvenTranslationSplitting`. The final type is

```lean
splittingIso (a : Fin 3 → ZMod 2) : blockedExtension a ≅ splitExtension
```

Both sides are native `ShortComplex (ModuleCat CoarseRing)` objects. Their
underlying modules are products of the original finite-support Laurent ring.
The induced native homology equivalence is linear over `CoarseRing`.

## Conventions and scope boundaries

The cyclic basis of degree two is `(e23, e31, e12)`. Thus
`d1 = (f1,f2,f3)`, `d3 = (f1,f2,f3)ᵀ`, and
`d2 = [[0,f3,-f2],[-f3,0,f1],[f2,-f1,0]]`.
The positive signs in Appendix G's shear equations use characteristic two;
the general shear theorem retains the minus signs written above.

The exactness transfer is conditional on adjacent Koszul exactness. It does
not prove regular-sequence exactness or the second, dagger-dual CSS sector.
The paper's definition of regularity omits properness of the generated ideal;
its direct mathlib counterpart is `Sequence.IsWeaklyRegular`, not necessarily
`Sequence.IsRegular`.

The translation coefficient ring is commutative. The lowering and translation
endomorphisms are not. Restricting scalars to even translations is essential:
the lowering maps are not linear over the entire original translation ring.
Only constant coupling vectors are claimed in the paper specialization.
The direct Laurent construction proves the operator formulas and relations
of G2–G3. It does not separately construct G1's explicit rank-eight basis;
that decomposition is unnecessary for this direct restriction-of-scalars proof.

This contribution does not establish the derived superselection profiles,
their Ext layers, the Tor description of periodic logical operators, the
ground-state degeneracy formula, stable Clifford classification, nonsplitting
before coarse graining, or a finite-depth CNOT circuit. In particular, an
isomorphism of the Z-sector short complexes alone is not a proof of all these
physical equivalences. The involution-twisted module and its untwisted version
are not identified without a separately proved map.

## Owner search

The bounded owner search examined canonical `lean/InfoGeometry`, `src/InfoGeometry`,
the repository categorical map, and the pinned mathlib algebra/homological
owners. No existing native Koszul stabilizer extension owner was found.
`Cl55ExteriorContractionGrading` constructs a genuine exterior-contraction
complex over `ℝ`, but its unit-pairing exactness contract does not supply the
regular-sequence resolution needed over a Laurent ring. Existing Weyl/Pauli
owners concern physical operators and do not replace the translation-module
construction here.
`Algebra/EulerLaurentDerivation.lean` supplies a univariate finite-support
differential and residue, but not the multivariable convolution Leibniz theorem
or its even-sublattice scalar restriction. `Clifford/KoszulFoundation.lean`
concerns Clifford anticommutators rather than these Koszul chain maps.

The native interfaces to reuse are `ShortComplex.moduleCatMk`,
`ShortComplex.moduleCat_exact_iff`, `ShortComplex.isoMk`,
`LinearEquiv.toModuleIso`, `ShortComplex.homologyMapIso`, and finite-support
group-algebra linear maps. The pinned mathlib does not provide a Koszul-complex
implementation under that name; it does provide regular-sequence and native
homological infrastructure.

## Validation scope

The toolchain and dependency revisions remain pinned by this repository.
The native source-closure check includes every declaration in all five owners:

```bash
python3 tools/quality/check_clifford_dirac.py \
  --mathlib-root .lake/packages/mathlib \
  --target InfoGeometry.Algebra.TriangularShortComplex \
  --target InfoGeometry.Quantum.KoszulThree \
  --target InfoGeometry.Quantum.KoszulThreeExtension \
  --target InfoGeometry.Quantum.EvenTranslationOperators \
  --target InfoGeometry.Quantum.KoszulEvenTranslationSplitting \
  --output /absolute/path/to/fresh/verification
```

This maintained checker accepts explicit targets despite its historical
Clifford filename. Acceptance uses neither `--incremental` nor `--skip-audit`.
Its warning hard-failure prefix is specific to the historical target, so the
per-module warning counts for these five owners must also be inspected and
required to be zero.

The package-level checks remain distinct:

```bash
python3 tools/infra/run_locked_lean.py --wait-for-build-lock \
  lean/InfoGeometry/Quantum/KoszulEvenTranslationSplitting.lean
python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock \
  InfoGeometry.Quantum.KoszulEvenTranslationSplitting
```

Independent semantic review, fresh QA, axiom inspection, staged proof checks,
placeholder and semantic-vacuity checks, and the actual pre-push gate accompany
publication. Results must distinguish native proof validation from package
configuration failures; a scoped native pass is not a whole-repository build
certificate.
