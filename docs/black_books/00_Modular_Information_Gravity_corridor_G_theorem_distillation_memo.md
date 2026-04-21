# Corridor G theorem-distillation memo

Corridor:
- Casimir / Pfaffian / Berezinian / Zeta Regularization / Critical Stiffness

Black-book source shards reviewed:
- `00v_supervolume_python_realization_and_casimir_entropy.md`
- `00w_drazin_penrose_lightcone_projectors_and_casimir_gravity.md`
- `00y_zeta_anomaly_heat_kernel_and_dirac_souriau_pressure.md`
- `00aa_information_equilibrium_theorem_and_casimir_weyl_duality.md`
- `00ac_critical_stiffness_arxiv_abstracts_and_simulation_architecture.md`
- `00ad_weyl_casimir_variational_derivation_repeated_closure.md`

Repo surfaces checked:
- `lean/InfoGeometry/Canonical/WeylAnomalySource.lean`
- `lean/InfoGeometry/Canonical/ConformalAnomalyOperator.lean`
- `lean/InfoGeometry/Canonical/ConformalAnomalyReadout.lean`
- `lean/InfoGeometry/Canonical/EinsteinAnomalyOperator.lean`
- `lean/InfoGeometry/Canonical/CentralChargeAnomaly.lean`
- `lean/InfoGeometry/Canonical/TopologicalResidue.lean`
- `lean/InfoGeometry/Canonical/WeylGaugeOperatorLift.lean`
- `lean/InfoGeometry/Canonical/RestrictedVolumeCharacter.lean`
- `lean/InfoGeometry/Canonical/UniversalVolume.lean`
- `lean/InfoGeometry/Canonical/BekensteinBound.lean`
- `lean/InfoGeometry/Canonical/VortexAnomalyLink.lean`
- `lean/InfoGeometry/Canonical/SuperAnomaly.lean`

Search result of note:
- direct grep over `lean/InfoGeometry` for `Pfaff|Berezin|zeta|Casimir|stiffness` returned no direct canonical theorem-owner hits.

## 1. Core symbolic claims in Corridor G

Recurring pressure in the black-book shards:

1. Entropy or effective action is governed by a Pfaffian/Berezinian ratio.
2. Casimir energy is a zeta-regularized residual of the supervolume or vacuum functional.
3. Weyl anomaly is the operatorial/scalar shadow of the same residual tension.
4. Central charge / zero-mode / topological residue protects the system near a BPS limit.
5. A critical stiffness threshold separates collapse-dominated and expansion-dominated regimes.
6. Cosmological-dark-energy rhetoric is built on top of this anomaly/Casimir residual.

The black-book material is rhetorically unified, but the actual repo support is uneven across these six layers.

## 2. What is already owner-backed in the repo

### A. There is a real anomaly owner lane

The strongest actually owned lane in this corridor is not “Casimir energy” or “Pfaffian/Berezinian superdeterminant” directly.
It is the noncommutative anomaly/operator lane.

`ConformalAnomalyOperator.lean` owns the operator-first surface:
- projector obstruction as the primary anomaly operator,
- KKT grade-zero / diagonal-block packaging,
- dilation source identities relating dilation commutators to the projector obstruction.

This is a genuine owner/trunk surface for the anomaly corridor.

### B. There is a clean scalar-readout layer, but it is explicitly secondary

`ConformalAnomalyReadout.lean` is very explicit:
- scalar quantities like `obstructionScale`, `chiralScale`, `epsilon`, `unitOfAction`
  are readouts of the operator obstruction,
- they are not independent ontology.

This matters a lot for Corridor G.
The repo already guards against collapsing operator structure into scalar rhetoric.
So any scalar “anomaly coefficient” or “vacuum energy scale” talk must be read as a derived image lane unless promoted by further theorem bridges.

### C. Weyl-anomaly sourcing is real

`WeylAnomalySource.lean` already proves source-style statements such as:
- nonzero chiral anomaly implies a chiral inference state,
- nonzero anomaly can force nonzero transported Einstein residual under explicit source hypotheses,
- Cartan/Weyl closure reuses the same source trunk.

So the repo does own a meaningful route from anomaly data to a nonzero Einstein-like residual.
This is one of the strongest repo-native anchors for the black-book claim that anomaly has geometric/gravitational consequences.

### D. There is a real volume/log-character lane

`WeylGaugeOperatorLift.lean` and `RestrictedVolumeCharacter.lean` own:
- determinant character,
- relative volume scale,
- logarithmic relative volume potential,
- common/relative logarithmic Weyl coordinates,
- operator-valued logarithmic generator.

This is important because it gives the repo a precise log-volume / Weyl-scale / determinant-character corridor.
It is the nearest owner-supported lane to some of the Berezinian/log-supervolume rhetoric, even though it does not formalize the Berezinian itself.

### E. There is a real topological residue / central charge lane

`OperatorialCentralCharge.lean` and `CentralChargeAnomaly.lean` own:
- operatorial central charge as Fredholm/chiral analytical index,
- transport invariance of that central charge,
- anomaly-freeness as equality between central charge and topological residue.

`TopologicalResidue.lean` owns:
- `wittenIndexResidue`,
- zero-mode / topological-memory vocabulary,
- current canonical fact that the modular-supercharge residue vanishes on the canonical doubled-carrier lane.

So the repo does have a rigorous topological residue / index corridor, but it is much more operatorial and index-theoretic than the black-book Pfaffian stories.

### F. There is a constructive entropy-bound lane

`BekensteinBound.lean` gives:
- nonnegative RN-barrier entropy budget,
- Connes-cocycle lift to the topological Bekenstein bound,
- additive entropy-potential bridge.

This is a real entropy/volume/log-potential surface, but it is not the same thing as a Pfaffian/Berezinian supervolume theorem.
It should be treated as adjacent support, not as a synonym.

## 3. What is only partially owned / still requires theorem work

### A. Direct Pfaffian/Berezinian ownerhood is not present in the inspected repo surfaces

The black-book corridor repeatedly centers expressions like:
- `Pf_reg(iD) / sqrt(Ber_reg(M))`,
- `S = log Pf - 1/2 log Ber`,
- Casimir energy from zeta-regularized superdeterminants.

But direct searches in `lean/InfoGeometry` did not return canonical theorem surfaces for:
- Pfaffian,
- Berezinian,
- zeta regularization,
- Casimir energy,
- critical stiffness.

So as of the inspected state, these are not owned theorem surfaces in the same way the anomaly/operator/volume-character lanes are.

### B. The nearest repo-native replacement is anomaly/volume/operator language, not the exact black-book formulas

Repo-faithful reformulation should currently prefer:
- projector obstruction operator,
- scalar anomaly readout,
- operatorial central charge,
- topological residue,
- log-relative-volume potential,
- transported Einstein residual.

This is a genuine corridor.
But it is not yet the same as a proved Pfaffian/Berezinian/zeta/Casimir calculus.

### C. “Critical stiffness” appears to be black-book capstone rhetoric, not an owned theorem surface

The source shards repeatedly define or discuss:
- `kappa`, `kappa_crit`,
- phase-transition thresholds,
- vacuum hardening and dark-energy ignition.

No direct owner theorem file for this threshold was found in the inspected Lean surfaces.
So currently this should remain debt/proposal rather than promotion-ready theorem language.

### D. Dark-energy / cosmological-constant identification is still capstone-level

The source often states:
- Casimir residual = cosmological constant,
- Weyl anomaly = dark energy,
- critical stiffness = acceleration onset.

The repo does support a weaker and cleaner statement:
- anomaly can source a nonzero transported Einstein residual.

But the larger cosmological identifications are not currently closed by the inspected owner files.
They remain capstone extrapolation.

## 4. Owner-level statements we can already safely extract

These are safe, repo-faithful statements for Corridor G:

1. The primary anomaly object is operatorial, not scalar.
   The scalar readouts are derived functorial images of the obstruction operator.

2. The repo already owns a Weyl-anomaly source lane in which nonzero anomaly can force a nonzero transported Einstein residual under explicit source hypotheses.

3. The repo already owns a logarithmic volume/character lane through determinant-character and log-relative-volume potential constructions.

4. The repo already owns a topological residue / operatorial central charge lane, with transport invariance and anomaly-freeness formulated as equality with the residue.

5. The repo already owns a constructive entropy-bound corridor via RN-barrier / Connes-cocycle data.

6. These owned lanes provide a strong algebraic-anomaly backbone for Corridor G, even though they do not yet amount to a direct Pfaffian/Berezinian/zeta/Casimir owner package.

## 5. Statements that must remain marked as debt/proposal

These should not yet be promoted as proved:

1. Entropy equals a proved repo-native formula of the form
   `log Pf_reg(iD) - 1/2 log Ber_reg(M)`.

2. Casimir energy is already formalized in the repo as a zeta-regularized superdeterminant residual.

3. Seeley–DeWitt coefficient extraction or heat-kernel asymptotics are already owned theorem surfaces in the inspected repo state.

4. A critical stiffness coefficient or hard threshold has already been formalized and proved.

5. The cosmological-constant / dark-energy interpretation is already a closed theorem consequence of the anomaly package.

## 6. Best repo-native reading of the corridor right now

The best disciplined translation is:

Black-book rhetoric:
- Pfaffian/Berezinian/zeta/Casimir/critical stiffness

Current repo-native theorem corridor:
- operator obstruction,
- anomaly readout,
- Weyl source,
- transported Einstein residual,
- operatorial central charge,
- topological residue,
- log-relative-volume potential,
- entropy-bound cocycle barrier.

So Corridor G is not empty in the repo.
But its current closure is by surrogate operator/anomaly/volume structures, not by the exact superdeterminant language used in the source shards.

## 7. Best next theorem targets for Corridor G

Priority targets:

1. Add an explicit bridge from topological residue / central charge to the anomaly readout lane.
- The repo already has both pieces.
- A sharper theorem corridor could reduce rhetorical drift around “Pfaffian protection”.

2. Add a canonical “vacuum residual” definition on the anomaly side.
- This should likely sit as an operator/scalar residual derived from the obstruction/readout package,
  not as immediate cosmological language.

3. If the project really wants Pfaffian/Berezinian language,
   create exact owner surfaces rather than continuing metaphorical reuse.
- a Pfaffian owner file,
- a Berezinian/superdeterminant owner file,
- a carefully scoped regularization layer,
- only then a bridge to anomaly readouts.

4. Keep “critical stiffness” downstream until the analytic owner exists.
- It should emerge from an already-owned Hessian/readout operator lane,
  not arrive as a capstone slogan.

## 8. Pauli-style closure status for Corridor G

ROLE:
- mixed corridor: strong anomaly/operator owner lane, weak direct superdeterminant/Casimir ownerhood

SEMANTIC_FIDELITY:
- medium-to-high when translated through anomaly/operator/volume language
- low if taken literally as already-formalized Pfaffian/Berezinian/zeta/Casimir calculus

THEOREM_STRENGTH:
- high on anomaly/operator/readout/central-charge transport surfaces
- medium on volume/log-potential support
- low on direct Casimir/Pfaffian/Berezinian/critical-stiffness claims

CLOSURE_STRENGTH:
- owner-closed on anomaly/operator readout and central-charge residue lanes
- bridge-valid-but-not-closed for using those lanes as stand-ins for black-book Casimir rhetoric
- capstone-only for dark-energy and critical-stiffness overgrowth

PROMOTION_ALLOWED:
- yes for anomaly/operator/volume/residue statements listed in section 4
- no for literal Pfaffian/Berezinian/zeta/Casimir/critical-stiffness claims listed in section 5

## 9. Recommended extraction order inside Corridor G

Extract in this order:

1. `00aa` and `00ad`
   - only for the anomaly/Weyl duality pressure, translated into operator obstruction and sourced Einstein residual language.

2. `00y`
   - only for the zeta/anomaly intuition, but mark direct zeta/heat-kernel formulas as still unowned unless exact files are later added.

3. `00v`
   - use as upstream motivation for a future Pfaffian/Berezinian owner lane; do not treat it as already grounded.

4. `00ac`
   - keep “critical stiffness” explicitly in debt/proposal status unless a live owner theorem is introduced.

5. `00w`
   - use only the parts overlapping with anomaly/regularization/topological protection; leave Casimir-gravity inflationary rhetoric as capstone.

## 10. Bottom line

Corridor G is not yet a direct “Casimir/Pfaffian/Berezinian theorem corridor” in the repo.

What the repo really has today is:
- a robust noncommutative anomaly operator lane,
- scalar anomaly readouts explicitly subordinate to that operator lane,
- transport-invariant central charge / residue machinery,
- a log-volume and entropy-barrier side corridor.

That is enough to support a disciplined theorem-distillation memo.
It is not enough to claim that the full black-book supervolume/Casimir/zeta/critical-stiffness package is already formally owned.