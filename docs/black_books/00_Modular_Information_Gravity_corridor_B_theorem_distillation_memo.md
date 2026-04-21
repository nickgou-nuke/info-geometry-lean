# Corridor B theorem-distillation memo

Corridor:
- Grand Canonical / Chemical Potential / Carrier Number / ln Z

Black-book source shards reviewed:
- `00b_gauge_tkk_grand_canonical_black_hole_ensemble.md`
- `00k_operator_moment_map_grand_canonical_operator_ensemble.md`
- `00l_cross_onsager_mass_pressure_and_tkk_hessian_blocks.md`
- `00o_tkk_beta_mu_omega_cross_covariances.md`

Primary repo surfaces checked:
- `lean/InfoGeometry/GrandCanonical/Core.lean`
- `lean/InfoGeometry/Canonical/GrandCanonicalGaugePotentialBridge.lean`
- `lean/InfoGeometry/Canonical/GrandCanonicalFockNumberBridge.lean`

## 1. Core symbolic claims in Corridor B

Recurring claims in the source shards:

1. The grand canonical ensemble is the natural open-system carrier for exchanging energy and particle number.
2. Chemical potential `μ` is the intensive variable conjugate to particle/carrier number `N`.
3. `ln Z` is the Massieu / log-generating potential.
4. The effective thermal kernel is `exp(-β(H - μN))` or its operatorial analogue.
5. In the more geometric/gauge reading, `μ` behaves like a gauge/background coupling rather than a mere scalar bookkeeping term.
6. The `(β, μ, ω)` block structure of the Hessian / Onsager matrix should encode cross-couplings between energy, carrier number, and anisotropic sectors.

These claims split cleanly into what the repo already owns and what remains bridge/capstone extrapolation.

## 2. What is already owner-backed in the repo

### A. The finite grand-canonical lane is fully real

`GrandCanonical/Core.lean` owns the finite two-parameter thermodynamic model:
- `GrandCanonicalTwoParam` with
  - `energy : α → ℝ`
  - `number : α → ℝ`
- `shiftedEnergy params μ x = energy x - μ * number x`
- `partitionGC params β μ = ∑ exp(-β * shiftedEnergy)`
- `potentialGC = log Z(β, μ)`
- `gibbsWeightGC`
- `meanShift`
- `meanNumber`

This means the black-book formula
- `exp(-β(H - μN))`
is already formally present in the finite-state thermodynamic owner lane, with `H` specialized to the energy observable and `N` to the number observable.

### B. `ln Z` is explicitly formalized

Still in `GrandCanonical/Core.lean`:
- `potentialGC params β μ := Real.log (partitionGC params β μ)`

So the claim
- “`ln Z` is the Massieu/log-generating potential”
is already represented at the owner level as a precise object.

### C. The conjugate derivatives are already proved

The repo already proves:
- `∂β potentialGC = - meanShift`
- `∂μ potentialGC = β * meanNumber`

More precisely:
- `potentialGC_deriv_beta_eq_neg_meanShift`
- `potentialGC_deriv_mu_eq_beta_meanNumber`

So the strongest finite-state owner statement is:
- the `μ`-direction is conjugate to the count observable,
- the `β`-direction is conjugate to the shifted observable `E - μN`.

### D. The finite chemical-potential gauge bridge already exists

`GrandCanonicalGaugePotentialBridge.lean` already packages the gauge-style reinterpretation carefully:
- `chemicalPotentialGauge`
- `shiftedEnergy_eq_energy_sub_chemicalPotentialGauge`
- `grandCanonicalMassieuPotential`
- `chemicalPotential_conjugate_count_readout`
- `inverseTemperature_conjugate_shiftedEnergy_readout`

This is important because it shows the repo already has a controlled bridge saying:
- the chemical potential coupling can be represented as a background gauge coupling to the count observable

without overclaiming a full operatorial/Type-III identification.

### E. The Fock-side analogue also exists

`GrandCanonicalFockNumberBridge.lean` packages the Fock-side version:
- `fockNumberGauge`
- `grandCanonicalFockGenerator_eq_hamiltonian_sub_fockNumberGauge`
- `fockNumberGauge_is_mu_times_numberOperator`
- `grandCanonicalFockGenerator_zero_mu`

So the repo already has a second nontrivial lane showing the same affine form:
- Hamiltonian minus chemical-potential-coupled number object.

This is a strong sign that the grand-canonical chemical-potential story is structurally real in the repo, not just rhetoric.

## 3. What is only partially owned / still requires theorem work

### A. “μ is a gauge field” is only carefully true in the bridge sense

What is owned:
- a finite-state gauge-coupling bridge to the number observable,
- a Fock-side gauge coupling to the number operator.

What is not yet owned:
- a theorem saying `μ` is literally a Bogoliubov frame field, a Type-III modular background field, or a full temporal gauge connection in the operator-algebraic sense.

The existing bridge file itself states this boundary clearly:
- it does not identify `μ` with a Bogoliubov frame field or a Type III modular background.

So black-book language equating `μ` directly with a full gauge connection must still be treated as a bridge/capstone target, not an owner fact.

### B. The full TKK / Onsager block rhetoric is not yet owner-closed

The source shards repeatedly describe matrix blocks like:
- `(β, μ, ω)`
- cross-Onsager couplings between `N` and anisotropic pressure
- Weyl-covariant Hessian sectors

What the repo already has:
- KKT / thermodynamic operator lanes
- finite grand-canonical `μ` and `N`
- some gauge bridges

What is not yet clearly owner-backed as stated:
- a single theorem package realizing the exact black-book `(β, μ, ω)` cross-block matrix in a fully repo-native operator form.

So this remains partially symbolic and should not yet be promoted as already proved.

### C. Grand-canonical black-hole / Tolman-Klein / cosmological usage remains capstone

The black-book source ties grand-canonical ensemble language to:
- black holes,
- redshift,
- Weyl gauge in gravity,
- cosmological open systems.

Those are valid research directions, but the currently checked repo files do not yet own that full gravity-side theorem surface.

Status:
- capstone/proposal, not owner-closed.

## 4. Owner-level statements we can already safely extract

These are safe, repo-faithful statements:

1. The finite grand-canonical kernel is already formalized as:
   - `exp(-β(E - μN))`.

2. The shifted observable is owned exactly as:
   - `shiftedEnergy = E - μN`.

3. The grand-canonical log-partition potential is already formalized as:
   - `potentialGC = log Z(β, μ)`.

4. The `μ`-direction is conjugate to the count observable:
   - `∂μ potentialGC = β * meanNumber`.

5. The `β`-direction is conjugate to the shifted observable:
   - `∂β potentialGC = - meanShift`.

6. There is already a controlled finite bridge reading chemical potential as a background gauge coupling to the count observable.

7. There is already a Fock-side bridge reading chemical potential as a background gauge coupling to the number operator.

## 5. Statements that must remain marked as debt/proposal

These should not yet be promoted as already proved:

1. That chemical potential is already a full Type-III modular background field in the repo.
2. That the black-book `(β, μ, ω)` Hessian/Onsager block is already formalized exactly as written.
3. That black-hole/cosmological grand-canonical ensemble claims are already owner-derived from the current repo surfaces.
4. That the Weyl/gauge reading of `μ` has already been pushed through all operatorial transport lanes.

## 6. Best next theorem targets for Corridor B

Priority theorem targets:

1. Extend the finite-to-operator bridge
- connect the finite `chemicalPotentialGauge` lane to the operatorial transport / modular lane without overclaiming a Type-III identification.

2. Clarify the `(β, μ)` to `(K, gauge-data)` map
- add a precise translator theorem identifying where the finite grand-canonical affine form corresponds to an operatorial or Fock-side generator shift.

3. Isolate the safe Weyl language
- prove only the exact gauge-coupling statements already implicit in the bridge files;
- do not yet promote gravity/redshift/Tolman-Klein versions unless explicit owner files are added.

4. Later, if supported by new owner files
- build a thermodynamic cross-block bridge involving chemical potential and anisotropic/gauge sectors in a way that is theorem-backed rather than black-book schematic.

## 7. Pauli-style closure status for Corridor B

ROLE:
- owner-backed finite thermodynamic corridor with translator bridges to gauge and Fock language

SEMANTIC_FIDELITY:
- high for `μ`, `N`, `ln Z`, and conjugate-derivative statements
- medium for the gauge reinterpretation of `μ`
- low-to-medium for black-hole/cosmological grand-canonical rhetoric

THEOREM_STRENGTH:
- high on the finite grand-canonical owner lane
- medium on the finite gauge/Fock bridges
- low on the larger TKK/cosmology extrapolations as currently checked

CLOSURE_STRENGTH:
- owner-closed on the finite `β, μ, N, log Z` lane
- bridge-valid-but-not-closed on the gauge reinterpretation lane
- capstone-only on the gravity/cosmology usage

PROMOTION_ALLOWED:
- yes for the owner statements listed in section 4
- no for the extrapolative statements listed in section 5

## 8. Recommended extraction order inside Corridor B

Extract in this order:

1. `00k` -> operator moment-map / grand-canonical operator ensemble rhetoric
2. `00o` -> explicit `β`, `μ`, `N` thermodynamic vector claims
3. `00l` -> cross-block / anisotropy / Onsager claims
4. `00b` -> gravity-facing grand-canonical/Weyl/TKK rhetoric only after the finite owner surface is stated first

This keeps the theorem factory anchored in the already-real finite grand-canonical lane and prevents premature promotion of the more ambitious gauge/gravity language.
