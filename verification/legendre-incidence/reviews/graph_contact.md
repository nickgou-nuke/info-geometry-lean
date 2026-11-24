# Independent source review: graph geometry and Fenchel contact

Reviewer: `operator_chiral_audit`, independent of the two source authors.
Date: 2026-11-24.

## Reviewed snapshots

| File | SHA256 |
|---|---|
| `candidates/legendre_completion/GraphGeometry.lean` | `6d1dbbcaee2821a49ce10a407457966ef8a46dd0c807d7ceabefe6bcb2109fcd` |
| `lean/InfoGeometry/Twistor/FenchelContactIncidence.lean` | `ca3371b1771d00b6fcc730c412cd41ba518e1007fc42ec63ee71091a9da930cb` |

Pinned Mathlib source inspected: `d13f23b723b8a846827a245b89c10fc7d3f11612`.
The reviewer read definitions, theorem types, relevant imports and proofs.
No owner was edited and no Lean, Lake or build command was run.

## Disposition

**Source-review approval, pending kernel validation.** No blocking mathematical,
sign, hypothesis or API-shape issue was found in these snapshots. This review
does not certify elaboration, transitive axiom dependencies or a build.

## GraphGeometry findings

1. **The orthogonal is the correct one.** Mathlib's
   `LinearMap.BilinForm.mem_orthogonal_iff` tests `B n m = 0` for every
   `n` in the source submodule. With the existing Geometry-sign form, testing
   `(u, H u)` against `(x, alpha)` gives `alpha u - H u x = 0`.
   Consequently the exact formula `graph H` orthogonal equals `graph H.flip`
   is correct. The graph-injectivity proof turns self-orthogonality into the
   stated symmetry condition, with no finite-dimensional assumption.

2. **Maximal isotropy is established on actual submodules.** An isotropic
   submodule containing a symmetric graph lies in that graph's orthogonal,
   which is the graph itself. This is stronger than the older pairwise
   isotropy alias. The separate neutral-form pullback has factor `2`, correctly
   reflecting the unnormalized `RealDualTwistor.neutralForm`; positive
   Hessian graphs are not thereby declared neutral-null.

3. **Dimension and Grassmannian claims use genuine equivalences.**
   `graphSourceEquiv H` has type `H.graph ≃ₗ[ℝ] V` and
   `graphQuotientEquiv H` identifies the ambient quotient with the dual.
   The finite-dimensional construction supplies finite/projective quotient
   proofs by these equivalences. The pinned `Module.Grassmannian` indexes
   quotient rank, exactly as the candidate states. No global manifold or
   supermanifold construction follows from this single native chart.

4. **The incidence swap and grading criterion are exact.**
   `RealTwistorIncidence.incidenceSpace H` uses `(H v, v)`; the displayed
   `prodComm` comap therefore lands in the correct coordinate order. Under
   the fixed grading `(v, alpha) ↦ (v, -alpha)`, graph preservation forces
   `-H v = H v`, hence `H = 0` over the reals. This prevents an ordinary
   nonzero Hessian graph from being mislabeled homogeneous for that grading.

5. **The analytic statements differentiate the actual graph.**
   `HasFDerivAt.prodMk` produces the derivative of `y ↦ (y, p y)` on the
   continuous-dual carrier. `ContinuousLinearMap.coeLM` then forgets
   continuity explicitly; the derivative range is proved equal to the native
   algebraic graph, with an explicit preimage for every graph vector.
   No topology on the full algebraic dual is assumed.

6. **The C² corollaries discharge Hessian symmetry.** The pinned
   `ContDiffAt.fderiv_right` requires `m + 1 ≤ n`, so `m = 1`, `n = 2`
   supplies the actual derivative field locally. The pinned
   `ContDiffAt.isSymmSndFDerivAt` requires `minSmoothness ℝ 2 ≤ 2` and
   returns exactly the iterated Fréchet-derivative symmetry used after the
   forgetful map. Normed real spaces suffice; completeness, strict convexity,
   positive definiteness and global invertibility are not being inferred.

These statements are nonvacuous. For example, the ordinary real quadratic
potential `f(t) = t²/2` has a nonzero symmetric Hessian and a nonzero graph;
its graph is symplectically self-orthogonal and is not stable under the fixed
primal/dual grading. This is a mathematical witness, not an executed Lean test.

## FenchelContactIncidence findings

1. The homogeneous point has last coordinate `1`; the hyperplane covector
   evaluates to `-1` on `(0, 1, 0)`. Both factors and the native dyad are
   nonzero even for `p = 0` or a zero-dimensional source.
2. Evaluation is exactly minus the existing Fenchel gap. Reuse of the ordered
   rank-one product therefore gives `D² = -gap • D`, without cancellation of
   a potentially zero operator.
3. The native last-coordinate covector has value `1` on the homogeneous point.
   The projector construction consequently gives `P² = P`, `PD = D` and
   `DP = -gap • P` in the correct order. At contact, `PD(1-P) = D` is an
   actual upper Peirce-corner identity. This cut depends on the point and
   homogeneous chart; no self-adjointness, lower generator, global fixed
   grading or physical supersymmetry is claimed.
4. Real conditional-supremum boundedness remains explicit in the general
   epigraph inequality and attainment equivalence. For global convexity and
   `HasFDerivAt f p x`, the affine-line/slope proof derives first-order support,
   the greatest support value, boundedness, contact and square-zero in that
   order. No equality hypothesis is smuggled into this derivative corollary.
5. The contact regime is inhabited: `f = 0`, `p = 0` gives bounded support
   set `{0}` and a nonzero square-zero dyad. Weak epigraph separation remains
   separate from contact, and arbitrary `fStar` is not called a conjugate.

## Remaining validation

Root must run the serialized narrow compiler/build and axiom checks against
the integrated files. Any source modification changes the corresponding
reviewed hash and needs an appropriately scoped follow-up review. No new
mathematical edit is requested by this source review.

## Promotion and root-authored tactic delta review

The reviewer compared the promoted owners with the reviewed graph candidate,
the committed contact source, and the original cotangent candidate. The
cotangent candidate was authored by this reviewer; the independence of this
additional review concerns the subsequent root-authored tactic changes, not a
second independent audit of that original candidate.

| Promoted owner | SHA256 |
|---|---|
| `lean/InfoGeometry/Geometry/LegendreGraphGeometry.lean` | `36a9a5bfda3b273306fc96547398564f4b1ef831a0606f6b0590081dae041b58` |
| `lean/InfoGeometry/Geometry/CotangentOperators.lean` | `b403e1f70c96d2dcb8adec12851d7e3c67cca80a913239c3b871e868c9f47d5b` |
| `lean/InfoGeometry/Twistor/FenchelContactIncidence.lean` | `e9a3083b47f36bcd6175d08b5b9d89de0f59e84042709b44fe64315de972be70` |

**Delta disposition: source-review approved, pending kernel validation.**
No theorem statement or definition changed in these deltas.

- Graph promotion changes only the docstring word `candidate` to `module`.
- The contact inequality now uses `linarith only [ht, hy]`. These are exactly
  the two required inequalities `f y ≤ t` and `p y ≤ f y + fStar p`; they
  imply the displayed nonpositivity after scalar normalization.
- The cotangent form-invariance and linear-additivity goals use `abel` after
  explicit scalar evaluation. The ordered endomorphism expressions remain
  unchanged inside the evaluated terms.
- Scalar homogeneity uses `mul_add`, and the Hamiltonian contraction identity
  uses `sub_neg_eq_add`; each is the exact displayed scalar identity.
- The full quadratic expansion distributes linear-map evaluation and scalar
  multiplication, rewrites `t²` and multiplication association, then uses
  `ac_rfl` to reorder the resulting sum. The linear and quadratic coefficients
  remain exactly those in the original theorem; no operator factors are
  commuted or discarded.

This append-only review involved source comparison and hash calculation only.
No Lean/Lake/build command or owner edit was performed.
