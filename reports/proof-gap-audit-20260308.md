# Proof-Gap Audit (2026-03-08)

> Status: `generated/historical report`
> Audited: 2026-05-02
> Note: Treat this as a snapshot. Regenerate before relying on it.
> See: [README.md](../README.md), [docs/README.md](../docs/README.md), [docs/CODEBASE_STATUS.md](../docs/CODEBASE_STATUS.md)

## 1) Hard-axiom status (environment-level)

- `lake build -R` succeeds on current worktree.
- Exported all `InfoGeometry.*` declarations via `lean/DAG/ExportDecls.lean`:
  - total declarations: 5318
  - kinds: 2624 `def`, 2548 `theorem`, 146 `inductive`
  - `axiom` declarations: **0**
- Text scan in `lean/**/*.lean` found no `sorry`/`admit`/`postulate`.

Conclusion: there are no explicit Lean axioms/sorries left in `InfoGeometry.*`.

## 2) Axiomatish declarations still acting as external assumptions

These are not Lean `axiom`s, but they are assumption carriers that block full constructive closure.

### P0 (publish-blocking)

1. **True BA descent not proved (IB core)**
   - Current theorem [`ib_lagrangian_monotone`](../lean/InfoGeometry/Canonical/IBCore.lean#L194) proves monotonicity for a *descent-corrected* map [`ibIteration`](../lean/InfoGeometry/Canonical/IBCore.lean#L179), not for raw BA step [`ibBAProposal`](../lean/InfoGeometry/Canonical/IBCore.lean#L171).
   - Open problem OP-IB-1: prove
     - `ibLagrangian prob (ibBAProposal prob p) ≤ ibLagrangian prob p`
     - under formal finite-support positivity/normalization side conditions.

2. **Fisher-Killing proportionality still assumption-driven**
   - [`fisher_metric_eq_killing_form`](../lean/InfoGeometry/Canonical/NoetherInference.lean#L70) currently requires a global bridging assumption `hBridge` ([line 78](../lean/InfoGeometry/Canonical/NoetherInference.lean#L78)).
   - Open problem OP-NI-1: replace `hBridge` by structural hypotheses (invariance + irreducibility/isotropy representation assumptions) and derive proportionality constant constructively.

3. **Wheeler-DeWitt equivalence still depends on external bridge direction**
   - [`ThermodynamicFromGeometricAlgebraic`](../lean/InfoGeometry/Canonical/GrandSynthesis.lean#L619)
   - [`GeometricAlgebraicFromThermodynamic`](../lean/InfoGeometry/Canonical/GrandSynthesis.lean#L633)
   - Open problem OP-GS-1: discharge both directions from existing constructive layers (currently one direction is still a bridge hypothesis).

4. **Yang-Mills obligations encoded as witness layer**
   - [`QFTAxiomsLayer`](../lean/InfoGeometry/Canonical/YangMillsBridge.lean#L38)
   - [`YangMillsMassGapBridge`](../lean/InfoGeometry/Canonical/YangMillsBridge.lean#L53)
   - Open problem OP-YM-1: replace witness packaging with derived statements from a formal Euclidean QFT development (reflection positivity + OS + reconstruction chain).

### P1 (major rigor debt)

5. **Analytical index invariance currently reduced to full pointwise constancy**
   - [`analyticalIndex_eq_of_chiralParts_eq`](../lean/InfoGeometry/Canonical/AnalyticalIndex.lean#L52) is currently proved only from `D = D'` and `Γ = Γ'` (not from chiral-part equality conditions).
   - [`indexInvariantAlong_of_chiralPart_const`](../lean/InfoGeometry/Canonical/AnalyticalIndex.lean#L67) uses `hD/hΓ` constancy, not chiral decomposition invariance.
   - Open problem OP-AI-1: restore a genuinely chiral proof based on projector identities + finite-dimensional rank/trace lemmas.

6. **Generalized inverses remain axiomatized interfaces**
   - [`IsMoorePenroseInverse` (Canonical)](../lean/InfoGeometry/Canonical/MoorePenrose.lean#L23)
   - [`IsDrazinInverse` (Canonical)](../lean/InfoGeometry/Canonical/Drazin.lean#L7)
   - duplicate versions also exist in [`Canonical/Singular.lean`](../lean/InfoGeometry/Canonical/Singular.lean#L18).
   - Open problem OP-SG-1: consolidate into one interface and connect to concrete matrix/operator existence/uniqueness results where available.

7. **KK compactness is still abstract interface-level**
   - [`CompactLike`](../lean/InfoGeometry/KK/CompactLike.lean#L14)
   - used by [`KasparovCycle`](../lean/InfoGeometry/KK/KasparovCycle.lean#L20).
   - Open problem OP-KK-1: bridge to a concrete compact-operator predicate for the chosen analytic model.

## 3) Mathlib assets already available (high leverage)

1. KL / Gibbs
   - `Mathlib.InformationTheory.KullbackLeibler.Basic`
   - key lemmas: `integral_llr_add_sub_measure_univ_nonneg`, `klDiv_eq_zero_iff`.

2. Finite-dimensional rank identities
   - `Submodule.finrank_sup_add_finrank_inf_eq`
   - `LinearMap.finrank_range_add_finrank_ker`

3. Projector/idempotent machinery
   - `LinearMap.IsIdempotentElem.range_eq_ker`
   - `LinearMap.IsIdempotentElem.ker_eq_range`
   - `LinearMap.IsIdempotentElem.isCompl`
   - `LinearMap.IsProj.trace`

4. Trace machinery
   - `LinearMap.trace_mul_comm`, `LinearMap.trace_conj'`, `LinearMap.trace_one`

5. Lie/Killing infrastructure
   - `LieAlgebra.killingForm`
   - `LieAlgebra.killingForm_of_equiv_apply`
   - `LieAlgebra.IsKilling` stack
   - invariant form framework: `Mathlib/Algebra/Lie/InvariantForm.lean`

6. Schur-type algebraic tools
   - `Mathlib/RingTheory/SimpleModule/Basic.lean` (Schur lemmas)
   - `Mathlib/RepresentationTheory/AlgebraRepresentation/Basic.lean`

## 4) Literature map for immediate proof development

### IB descent / alternating minimization

- Tishby, Pereira, Bialek (NIPS 1999): Information Bottleneck fixed-point equations.
  - https://papers.nips.cc/paper_files/paper/1999/hash/be3e9d3f7d70537357c67bb3f4086846-Abstract.html
- Tishby et al. “The Information Bottleneck Method” (2000).
  - https://arxiv.org/abs/physics/0004057
- Csiszar, Tusnady (1984): alternating KL minimization convergence template.
  - https://www.mit.edu/~6.454/www_fall_2002/shaas/Csiszar.pdf
- Recent convergent IB algorithm (semi-relaxed IB, 2024).
  - https://arxiv.org/abs/2404.04862

### Fisher/Killing proportionality on homogeneous/symmetric spaces

- Fisher geometry of multivariate normal families as symmetric-space geometry:
  - https://doi.org/10.1023/A:1007608121688
- Isotropy-irreducible/homogeneous metric uniqueness up to scale (Schur-lemma mechanism):
  - https://link.springer.com/article/10.1007/s12220-021-00695-z
  - https://link.springer.com/article/10.1007/s12220-024-01654-7

### Yang-Mills / OS-Wightman obligations

- Clay problem statement (mass gap target):
  - https://www.claymath.org/millennium/yang-mills-and-mass-gap/
- Osterwalder-Schrader axioms source record:
  - https://www.numdam.org/item/AIHPA_1973__19_1_1_0/

## 5) Recommended execution order (next coding steps)

1. OP-IB-1 (`IBCore`): prove one-step BA descent for raw BA proposal.
2. OP-NI-1 (`NoetherInference`): derive nontrivial proportionality constant without `hBridge`.
3. OP-AI-1 (`AnalyticalIndex`): restore chiral invariance proof from projector identities.
4. OP-GS-1 (`GrandSynthesis`): remove remaining bridge-direction assumption.
5. OP-SG-1 / OP-KK-1: consolidate inverse/compactness interfaces into constructive targets.
