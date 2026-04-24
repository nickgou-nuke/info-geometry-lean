# SuperMetriplectic Basis-Adaptation Program

> For Hermes: treat this as a theorem-role planning document, not as closure proof. The purpose is to turn the current scalar/body-level supermetriplectic skeleton into a disciplined derivation queue for operator lifts.

## Goal

Rewrite the scalar supermetriplectic packets in the basis best adapted to the repo's operator-owner geometry before attempting stronger noncommutative lifts.

The working conjecture is:
- the current scalar/body packets correctly capture the shape of the theory,
- but many intended operator lifts still look opaque because the scalar packets are written in a basis that mixes chiral, doubled, and involution-eigenspace information,
- therefore the next correct move is not immediate operator inflation, but basis adaptation of the scalar skeleton.

In this document:
- "scalar layer" means the conservative supermetriplectic packets in `lean/InfoGeometry/SuperMetriplectic/*`;
- "operator layer" means the existing owner/translator/coherence corridor under `lean/InfoGeometry/Canonical/*`, `lean/InfoGeometry/Krein/*`, `lean/InfoGeometry/Quantum/*`, and the doubled/transport branches already audited.

---

## Architectural Thesis

The scalar shadow layer is not a toy substitute for the theory. It is the representation skeleton of the theory.

Its role is to expose:
1. the stable algebraic packet shape,
2. the intended left/right and even/odd closures,
3. the Schur/defect/entropy readout pattern,
4. the exact places where operator lifts are still missing.

The operatorial noncommutative layer should then realize this skeleton. The discrepancy between scalar skeleton and operator realization is the map of missing lift theorems.

The key conjecture for the next phase is:

> Many currently-missing operator lifts will become cleaner when the scalar packets are rewritten in a basis adapted to chiral splitting, doubled-real structure, and the relevant involutions.

This is a basis-adaptation program, not an excuse to claim closure in advance.

---

## The Three Basis Rewrites

### 1. Chiral basis rewrite

Purpose:
- split packets by left/right anomaly lanes before operator lifting.

Expected scalar primitives:
- left shadow lane
- right shadow lane
- net odd lane
- central/defect correction lane

Operator-owner surfaces this should line up with:
- `χ_L`, `χ_R`
- `Q_D := χ_R - χ_L`
- `H_D`
- `Z_D`
- chiral anomaly / right-chiral anomaly surfaces

Why this helps:
- reduces mixing between translation-shadow and defect-shadow terms,
- makes odd-odd closure look like a left/right assembly rather than a single opaque scalar formula,
- gives a clearer conjectural target for future `{Q_D, Q̄_D}`-style lifts.

### 2. Doubled basis rewrite

Purpose:
- present the scalar packets in the same representation style as the repo's doubled-real carrier and phase-space/Krein lanes.

Expected scalar organization:
- paired lanes for conjugate/readout channels,
- explicit exchange or swap operation on doubled scalar coordinates,
- scalar analogues of regular vs complementary sectors.

Operator-owner surfaces this should line up with:
- doubled carrier / doubled real space surfaces,
- Kramers and Majorana compatibility corridors,
- modular Hamiltonian doubled bridge,
- Hestenes real-structure packaging.

Why this helps:
- avoids collapsing operatorially distinct channels into a single scalar quantity,
- prepares the scalar skeleton to receive conjugate and involution-based operator lifts,
- should make Schur hidden-sector elimination look more like an actual block reduction than a single scalar formula.

### 3. Involution-eigenspace basis rewrite

Purpose:
- diagonalize or block-diagonalize the scalar skeleton with respect to the involutions that already organize the operator corridor.

Candidate involutions:
- spectral Cartan involution / `Γ_S`
- geometric grading / `Γ_G`
- Kramers/time-reversal involution
- real/Majorana involution
- any explicit left-right exchange involution once defined at scalar level

Expected scalar split:
- `+1 / -1` eigenspace packets,
- compact/noncompact shadow sectors,
- reversible/dissipative sectors,
- regular/defect sectors.

Operator-owner surfaces this should line up with:
- `SymmetricLieAlgebra` / Cartan `𝔨 ⊕ 𝔭` surfaces,
- KKT packet preservation,
- Drazin regular/defect projector packaging,
- doubled involution-adapted transport lanes.

Why this helps:
- isolates which terms are expected to commute, anticommute, or vanish,
- turns many mixed formulas into sector statements,
- localizes correction terms instead of spreading them through all equations.

---

## Packet-by-Packet Rewrite Queue

The queue below is ordered by expected semantic yield, not by implementation convenience.

### A. `SuperchargeClosure`

Current role:
- scalar odd-odd closure schema `Q,Q -> P + Z`.

Rewrite target:
- chiral basis first.

Desired refined packet shape:
- left odd shadow
- right odd shadow
- net odd shadow
- translation shadow
- defect/central shadow
- optional mixed left-right correction channel

Intended operator analogue:
- `χ_L`, `χ_R`, `Q_D`, `H_D`, `Z_D`
- eventual paired-odd lane if/when a canonical conjugate exists

Missing lift obligations likely exposed:
- exact scalar analogue of left/right-to-net decomposition,
- mixed-channel correction term for future operator pairing,
- condition under which scalar paired-odd bracket collapses to the self-bracket.

### B. `CartanOnsagerSplit`

Current role:
- scalar/abstract split aligned with `𝔨 ⊕ 𝔭`.

Rewrite target:
- involution-eigenspace basis first, then doubled basis.

Desired refined packet shape:
- explicit `(+1)` and `(-1)` eigenspace readouts,
- scalar shadow of regular/core vs dissipative/range support,
- optional doubled swap if a conjugate scalar lane is introduced.

Intended operator analogue:
- spectral Cartan involution from `Γ_S`,
- `𝔨` / `𝔭` split,
- future coupling to `Γ_G` and KKT-preserving symmetries.

Missing lift obligations likely exposed:
- scalar analogue of compatibility between spectral and geometric involutions,
- scalar-to-operator statement for commuting involutions if present,
- split theorem linking scalar chiral basis to scalar Cartan basis.

### C. `ScalarSchurDrazinBlock`

Current role:
- hidden-sector scalar Schur complement and Drazin defect projector shadow.

Rewrite target:
- doubled basis first, then involution-eigenspace basis.

Desired refined packet shape:
- visible block decomposition into regular/core and hidden/defect lanes,
- explicit scalar mismatch channel,
- explicit scalar anomaly channel,
- optional left/right hidden block if chiralized.

Intended operator analogue:
- operator block reduction / hidden-sector elimination,
- Drazin projector and complementary projector,
- anomaly from projector mismatch,
- regular-vs-defect decomposition.

Missing lift obligations likely exposed:
- operator hidden-block theorem matching scalar Schur reduction,
- operator defect projector theorem in the same block basis,
- operator anomaly decomposition corresponding to the scalar mismatch basis.

### D. `BodyEntropyProduction`

Current role:
- body-level second-law packet.

Rewrite target:
- involution-eigenspace basis first; possibly doubled basis if entropy force gets paired channels.

Desired refined packet shape:
- reversible entropy lane,
- transverse/dissipative entropy lane,
- total entropy lane,
- optional compact/noncompact entropy decomposition.

Intended operator analogue:
- metriplectic flow packet,
- coadjoint-leaf split,
- energy-degenerate Onsager motion.

Missing lift obligations likely exposed:
- operator entropy production readout matching the scalar quadratic form,
- operator statement that reversible entropy contribution vanishes in the chosen basis,
- link between defect block and entropy production if the hidden-sector basis is used.

### E. `DrazinPenroseSchurTriad`

Current role:
- scalar/body capstone joining hidden-block reduction to body entropy positivity.

Rewrite target:
- after C and D are rewritten; this is the first capstone to rewrite, not the first owner packet.

Desired refined packet shape:
- explicit hidden/core block structure,
- explicit entropy split,
- explicit defect readout,
- optional chiralized triad if left/right hidden lanes are introduced.

Intended operator analogue:
- compact capstone theorem relating inverse kernels, projector mismatch, defect support, and entropy readout.

Missing lift obligations likely exposed:
- the first honest operator-facing metriplectic capstone theorem,
- compatibility theorem between hidden-block elimination and entropy split,
- bridge from scalar defect projector to operator defect support readout.

### F. `BPSCentralChargePacket` and `WittenIndexThermoPacket`

Current role:
- protected scalar/body packets downstream of the main skeleton.

Rewrite target:
- chiral basis after the core packets above.

Desired refined packet shape:
- protected left/right or paired sectors,
- explicit central/defect/support lanes,
- optional involution-adapted protected/null-response packet.

Intended operator analogue:
- central charge and protected null-dissipation lanes,
- index support on protected sectors.

Missing lift obligations likely exposed:
- operator support theorem isolating protected sectors in the adapted basis,
- better semantic alignment between BPS null-response and defect/projector support.

---

## Recommended Implementation Order

This is the proposed order for actual repo work.

### Phase 0: Planning/documentation only
- This document.
- No closure claims.
- Identify exact packet names and operator-owner analogues.

### Phase 1: Chiralize odd-odd closure
Files likely involved:
- `lean/InfoGeometry/SuperMetriplectic/Axioms.lean`
- possibly a new translator file under `lean/InfoGeometry/SuperMetriplectic/`

Objective:
- rewrite `SuperchargeClosure` into left/right/net scalar form without inflating theorem strength.

### Phase 2: Rewrite Schur/defect shadow in basis-adapted block form
Files likely involved:
- `Axioms.lean`
- `InverseBridge.lean`
- `EntropyShadowBridge.lean`
- possibly a new `TriadBridge.lean`

Objective:
- expose hidden/core, mismatch/anomaly, and defect lanes explicitly.

### Phase 3: Rewrite entropy packet as reversible/transverse basis object
Files likely involved:
- `Axioms.lean`
- `Flow.lean`
- `EntropyShadowBridge.lean`

Objective:
- make the body entropy packet visibly compatible with coadjoint-leaf and Onsager degeneracy language.

### Phase 4: Build triad capstone bridge
Files likely involved:
- new `lean/InfoGeometry/SuperMetriplectic/TriadBridge.lean`
- `All.lean`
- new regression test

Objective:
- connect `DrazinPenroseSchurTriad` explicitly to the inverse-shadow and entropy-shadow bridges in one compact theorem-backed capstone.

### Phase 5: Attempt first operator-facing upgrade
Only after Phases 1–4.

Objective:
- formulate a small operator-facing bridge theorem whose scalar version is already basis-adapted.

---

## Theorem-Role Classification

This program should preserve theorem-role discipline.

### Owner-like scalar packets (but still scalar/body-level owners)
- `SuperchargeClosure`
- `CartanOnsagerSplit`
- `ScalarSchurDrazinBlock`
- `BodyEntropyProduction`
- `DrazinPenroseSchurTriad`

These are owners of the scalar skeleton, not owners of the full operator theory.

### Translator/bridge files already present
- `DrazinBridge.lean`
- `CartanBridge.lean`
- `InverseBridge.lean`
- `EntropyShadowBridge.lean`

These should remain translators. They must not start claiming operator closure beyond what they actually prove.

### Future capstone
- `TriadBridge.lean` (recommended future file)

This should be a capstone/coherence surface, not a root owner.

---

## Concrete Lift-Obligation Format

For each scalar theorem we intend to lift, use this template.

### Lift record template
- Scalar theorem name
- Basis used: chiral | doubled | involution-eigenspace
- Intended operator analogue
- Known correction/defect/central term
- Required hypotheses
- Current closest owner surface
- Missing theorem name (proposed)
- Status: absent | partially realized | bridged | owner-closed

### Example schematic record
- Scalar theorem: `hiddenBlock_chiralAnomaly_eq_zero_of_projectorMismatch_eq_zero`
- Basis used: doubled hidden-block basis
- Intended operator analogue: anomaly vanishing on operator hidden block under projector agreement
- Known correction term: defect-supported central channel may remain
- Required hypotheses: certified inverse-kernel support and block identification witness
- Closest owner surface: `CertifiedInverseKernel`, `MoorePenrose`, `DrazinSupercharge`
- Missing theorem name: `operator_hiddenBlock_chiralAnomaly_eq_zero_of_projectorAgreement`
- Status: absent

This is the discipline that turns the scalar skeleton into a real derivation queue.

---

## Recommended Immediate Next Step

The cleanest immediate mathematical/programmatic next step is still:

1. create a compact `TriadBridge` connecting
   - `DrazinPenroseSchurTriad`
   - `InverseBridge`
   - `EntropyShadowBridge`

But now that bridge should be written with this basis-adaptation program in mind, so it becomes the staging point for later chiral/doubled/involution rewrites instead of a dead-end capstone.

If a stronger structural move is preferred instead, then the first packet to actually rewrite is:

- `SuperchargeClosure` into chiral left/right/net scalar form.

That would likely give the greatest payoff for future operator lifting.

---

## Verification Rule

Nothing in this document counts as closure.

Promotion rule:
- this plan is useful only if future theorem statements remain explicit about:
  - scalar/body-level status,
  - operator-owner target,
  - assumptions still missing,
  - correction terms that arise from noncommutativity.

The scalar skeleton should generate operator conjectures. It must not be mistaken for already-proved operator theorems.
