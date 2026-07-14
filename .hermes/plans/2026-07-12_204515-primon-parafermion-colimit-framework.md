# Primon–Parafermion Grand-Canonical Colimit Framework Implementation Plan

> **For Hermes:** Use `subagent-driven-development` only in new sandbox files. The parent agent alone may patch live owner files after reviewing and reproducing sandbox proofs. Do not commit unless the user explicitly asks.

**Goal:** Complete the primon/Riemann, boson–fermion–parafermion, grand-canonical, Boltzmann/Massieu, and `d ln Q` framework using finite algebraic recurrence and categorical direct inductive colimits, with no analytic-convergence, analytic-continuation, or Taylor-limit route.

**Architecture:** The framework proceeds through explicit finite prime-cutoff stages, one-step bonding maps, recurrent finite-prefix identities, finite-chain invariance, and a genuine algebraic direct limit with canonical stage maps and compatible-cone lifts. Thermodynamic and `d ln Q` readouts are first proved at each finite stage and then transported through the direct system. Existing Mathlib zeta theorems may remain as classical comparison/readout theorems, but they are not the repository’s finite-to-infinite construction or proof authority.

**Tech Stack:** Lean 4.28.0; pinned Mathlib; `Finset`, `Finsupp`, `RingHom`/`StarRingHom`; `Mathlib.Algebra.Colimit.DirectLimit`; repository owners `FiniteToInfiniteTransitionSOP`, `DirectLimitSuperClosureLemmas`, `UHFInductiveColimitBoundary`, `TensorTowerColimit`, and `ErlangenColimitResolution`.

---

## Non-negotiable framework policy

1. No proof step may use analytic convergence to promote finite stages.
2. No analytic continuation may be introduced as a closure mechanism.
3. No `tendsto`, Cauchy-limit, infinite-product convergence, or topological completion may substitute for explicit categorical bonds and a direct limit.
4. “Taylor series” is not a valid infinite mechanism here. Existing finite Taylor-prefix files may be used only as finite recurrent polynomial identities. New owner terminology should use `finitePrefix`, `recurrentPrefix`, or `inductivePrefix` where possible.
5. Classical Mathlib theorems about `riemannZeta`, Dirichlet series, or Euler products are comparison shadows, not the construction of the repository’s infinite primon object.
6. No `axiom`, `sorry`, witness certificate, calibration equality, or propositional structure field may be promoted as closure.
7. Each finite theorem must compile before any chain or colimit transport theorem is attempted.
8. A colimit claim requires an actual stage family, one-step bonds, all-pairs bond maps, directed-system laws, a `DirectLimit`, and explicit canonical maps.
9. A readout on the colimit must come from a proved compatible cone; it must not be postulated as an arbitrary function with the desired values.
10. Existing owner files remain authoritative. Do not introduce parallel carriers or duplicate thermodynamic/parafermion namespaces.

## Current theorem-backed baseline

### Finite thermodynamics

- Owner: `lean/InfoGeometry/GrandCanonical/Core.lean`
- Owner: `lean/InfoGeometry/GrandCanonical/ResponseMatrix.lean`
- Closed: finite partition positivity, normalized Gibbs weights, first responses, Hessian/variance/covariance identities.

### Prime specialization

- Owner: `lean/InfoGeometry/Arithmetic/PrimeGrandCanonicalEnsemble.lean`
- Closed: finite prime-subset states, energy, number, Gibbs partition and responses.
- Open: explicit factorization into local prime factors.

### Prime boson/fermion/supertrace

- Owner: `lean/InfoGeometry/Arithmetic/PrimeBosonFermionGas.lean`
- Owner: `lean/InfoGeometry/Arithmetic/PrimeSuperalgebra.lean`
- Closed: finite bosonic, positive-fermionic, and signed-supertrace factor identities.
- Classical comparison only: infinite bosonic Euler product equals Mathlib `riemannZeta` on its classical half-plane.

### Primon state sum

- Owner: `lean/InfoGeometry/Analytic/PrimonZeta.lean`
- Closed: finite-point weight identity and real Dirichlet-series readout.
- Required refactor: treat this as a state-sum comparison owner, not as the finite-to-infinite authority; remove/repair prose suggesting that it implements RH.

### Parafermions

- Strongest finite owner: `lean/InfoGeometry/Arithmetic/PrimeParafermionGrandCanonicalClock.lean`
- Duplicate owners:
  - `lean/InfoGeometry/Canonical/PrimeParafermionGrandCanonicalClock.lean`
  - `lean/InfoGeometry/Parafermion/PrimeParafermionGrandCanonicalClock.lean`
- Closed: finite local factors; finite global product; `κ = 2` and `κ = 3` collapses; Massieu/free-energy/Boltzmann readouts.
- Open: generic complex geometric recurrence and categorical tower.

### Thermodynamic potentials

- Owner: `lean/InfoGeometry/Potential/Thermo.lean`
- Owner: `lean/InfoGeometry/Information/DeRhamScore.lean`
- Closed: `Ψ = S - θU`; scaled free-energy identity; pointwise real `d log Q = dQ/Q`.

### Categorical finite-to-infinite infrastructure

- Policy owner: `lean/InfoGeometry/Meta/FiniteToInfiniteTransitionSOP.lean`
- Algebraic direct-limit owner: `lean/InfoGeometry/Algebra/DirectLimitSuperClosureLemmas.lean`
- Mandated boundary owners:
  - `lean/InfoGeometry/Canonical/UHFInductiveColimitBoundary.lean`
  - `lean/InfoGeometry/Canonical/TensorTowerColimit.lean`
  - `lean/InfoGeometry/Canonical/ErlangenColimitResolution.lean`

---

## Phase 0: Freeze the authoritative owner map

### Task 0.1: Produce a declaration/duplication table

**Role:** audit/coherence

**Files:**
- Read: all owners listed above
- Create only if needed: `docs/PRIMON_PARAFERMION_COLIMIT_OWNER_MAP.md`

**Steps:**
1. Enumerate every definition named `localParafermionFactor`, `finiteParafermionLocalFactor`, `Q_kappa`, `Massieu`, `freeEnergy`, `grandPotential`, and `boltzmannEntropy`.
2. Record type signatures, imports, and direct consumers.
3. Choose `InfoGeometry.Arithmetic.PrimeParafermionGrandCanonicalClock` as the finite complex owner unless a stronger existing owner is found.
4. Classify duplicates as exact duplicates, real specializations, or genuinely distinct structures.
5. Do not delete or rewrite anything in this task.

**Gate:** every ownership claim must cite a live declaration and consumer.

### Task 0.2: Establish forbidden-surface checks

**Role:** verification infrastructure

**Steps:**
1. Define a repeatable source scan for new theorem files covering `sorry`, `admit`, `axiom`, certificate/socket fields, `Tendsto`, infinite-product convergence, analytic continuation, and topological completion.
2. Allow explanatory comments that explicitly state non-claims.
3. Record that Mathlib comparison imports are allowed only in isolated comparison modules.

**Gate:** no executable forbidden surface in new owner/translator files.

---

## Phase 1: Canonical finite prime cutoff stages

### Task 1.1: Define the canonical stage index and prime cutoff

**Role:** owner

**Likely file:**
- Create: `lean/InfoGeometry/Arithmetic/PrimeThermodynamicStage.lean`

**Objective:** define one finite stage carrier shared by boson, fermion, parafermion, and Gibbs lanes.

**Required data:**
- stage `n : ℕ`;
- finite prime cutoff, preferably `Nat.primesBelow` or the repository’s existing cutoff owner;
- subset state carrier at stage `n`;
- local activity attached to each prime in the cutoff.

**Required theorems:**
- cutoff monotonicity under `n ≤ m`;
- membership transport;
- stage-zero and successor readbacks;
- finite state-space `Fintype` and nonempty instances.

**Verification:**
```text
lake env lean lean/InfoGeometry/Arithmetic/PrimeThermodynamicStage.lean
lake build InfoGeometry.Arithmetic.PrimeThermodynamicStage
```

### Task 1.2: Define stage embeddings on states

**Role:** owner

**Objective:** embed each finite subset state into the successor cutoff without changing old occupations.

**Required theorems:**
- injectivity;
- cardinality preservation;
- energy preservation on old primes;
- compatibility for arbitrary `n ≤ m` by recurrence.

**Stop condition:** do not define a colimit before these transition laws compile.

---

## Phase 2: Close the finite prime Gibbs factorization

### Task 2.1: Prove the subset-product expansion

**Role:** translator

**Modify:**
- `lean/InfoGeometry/Arithmetic/PrimeGrandCanonicalEnsemble.lean`

**Objective:** prove that the finite subset-state grand-canonical sum factors into local fermionic factors.

**Target theorem shape:**

```text
partition at cutoff P
= ∏ p ∈ P, (1 + exp (-β * (energyWeight p - μ)))
```

For `energyWeight p = log p`, derive the local activity form without invoking a limit.

**Proof route:** finite Boolean subset expansion only (`Finset.sum_bij`, powerset product expansion, or an existing `Finset.prod_one_add`).

**Required corollaries:**
- zero chemical potential;
- fugacity notation;
- equality with `finiteGrandFermionPartition` at the same finite cutoff.

**Gate:** directly consume the existing Gibbs partition definition; no parallel partition definition.

### Task 2.2: Transport finite responses through the product readout

**Role:** translator/coherence

**Objective:** connect the generic derivative/mean theorems to the finite factorized partition.

**Targets:**
- factorized Massieu equality;
- finite Boltzmann entropy equality;
- occupation response as the existing `μ` response.

**Policy:** derivative theorems are finite calculus on finite sums/products, not a convergence argument.

---

## Phase 3: Canonicalize generic finite parafermion recurrence

### Task 3.1: Prove the generic complex geometric recurrence

**Role:** owner

**Modify:**
- `lean/InfoGeometry/Arithmetic/PrimeParafermionGrandCanonicalClock.lean`

**Required recurrence:**

```text
Q 0 x = 0
Q (κ + 1) x = Q κ x + x^κ
```

**Required generic quotient theorem:**

```text
(1 - x) * Q κ x = 1 - x^κ
```

and, only under `x ≠ 1`, the quotient readout:

```text
Q κ x = (1 - x^κ) / (1 - x)
```

**Proof route:** induction on `κ` and finite `Finset.range`; no infinite series.

**Required specializations:** recover existing `κ = 2` and `κ = 3` theorems as corollaries, then remove duplicate proof bodies only after dependers build.

### Task 3.2: Prove the global finite product recurrence

**Role:** owner

**Targets:**

```text
Ξ_{κ+1,S} = ∏ p∈S (Q_{κ,p} + x_p^κ)
```

and the finite quotient product:

```text
(∏ p∈S (1-x_p)) * Ξ_{κ,S}
= ∏ p∈S (1-x_p^κ)
```

Use explicit commutative finite-product algebra.

### Task 3.3: Reconcile the three parafermion namespaces

**Role:** coherence

**Files:**
- arithmetic owner above;
- canonical and minimal parafermion owners.

**Steps:**
1. Replace duplicated generic definitions with imports/abbreviations only when definitional equality is verified.
2. Preserve real-specialized theorems if they provide genuinely stronger order/positivity facts.
3. Add bridge theorems rather than rewriting consumers blindly.
4. Build all three modules and their direct importers.

**Gate:** exactly one canonical finite local-factor definition remains authoritative.

---

## Phase 4: Build the recurrent κ tower

### Task 4.1: Define occupancy-stage recurrence

**Role:** owner

**Likely file:**
- Create: `lean/InfoGeometry/Arithmetic/PrimeParafermionRecurrence.lean`

**Objective:** model `κ` as an inductive recurrence, not a limit of analytic functions.

**Data:**
- stage value `Q κ x`;
- successor increment `x^κ`;
- finite global stage `Ξ_{κ,S}`;
- recurrence witnesses as theorems, not fields.

**Required theorems:**
- recurrence at every local prime;
- recurrence under finite product;
- `κ=2` fermion stage;
- compatibility with arbitrary finite recurrent iteration.

### Task 4.2: Replace “Taylor” terminology in this corridor

**Role:** hygiene/coherence

**Read first:**
- `lean/InfoGeometry/Analysis/FiniteSpectralMellinTaylor.lean`
- `lean/InfoGeometry/Analysis/SpectralTaylorMellinBridge.lean`

**Action:** do not rewrite unrelated files. For this framework, use finite recurrent-prefix declarations modeled on `taylorMomentPrefix_succ`, but call them recurrent/inductive prefixes. If an existing finite-prefix theorem is reused, document that it is a finite polynomial recurrence only.

---

## Phase 5: Define the prime-cutoff algebra tower

### Task 5.1: Choose an algebraic stage carrier

**Role:** owner

**Objective:** choose a commutative semiring/ring stage that contains finite occupation polynomials and supports honest ring homomorphism bonds.

**Candidate carrier:** finite multivariate polynomial or finitely supported occupation algebra over the stage prime set.

**Decision requirements:**
- successor cutoff adds generators without changing old generators;
- stage maps are explicit `RingHom`/`AlgHom`;
- evaluations to boson/fermion/parafermion readouts are separate compatible cones;
- avoid defining a stage merely as a scalar partition value, because scalar values do not preserve the universal occupation structure.

**Gate:** prove the chosen carrier is not a vacuous constant-stage identity tower.

### Task 5.2: Define one-step prime bonds

**Role:** owner

**Required declarations:**

```text
PrimeStage : ℕ → Type
primeBond : ∀ n, PrimeStage n →+* PrimeStage (n+1)
```

**Required theorems:**
- generator readback;
- identity on old prime modes;
- injectivity;
- preservation of parity grading;
- preservation of finite occupation relations.

### Task 5.3: Define all-pairs recurrent bonds

**Role:** translator

Reuse:

```text
InfoGeometry.Algebra.DirectLimitSuperClosureLemmas.bondMap
bondMap_refl
bondMap_succ
bondMap_apply_trans
bondMap_injective
```

Do not reimplement this infrastructure.

---

## Phase 6: Construct the actual categorical direct inductive colimit

### Task 6.1: Instantiate the directed system

**Role:** categorical owner

**Likely file:**
- Create: `lean/InfoGeometry/Categorical/PrimeThermodynamicDirectLimit.lean`

**Required construction:**

```text
PrimeThermodynamicLimit := DirectLimitSuperClosure primeBond
primeStageOf n : PrimeStage n →+* PrimeThermodynamicLimit
```

using existing:

```text
bondDirectedSystem
directLimitOf
directLimitOf_bond
directLimitOf_bondMap
directLimitOf_injective
```

**Required theorem:** compatible recurrent stage elements have equal canonical images, using `directLimitOf_eq_zero_stage` or its appropriately named generalization.

### Task 6.2: Transport boson/fermion/parafermion relations

**Role:** categorical translator

**Targets on canonical images:**
- boson × signed fermion cancellation;
- positive fermion square-correction identity;
- parafermion local recurrence;
- `κ=2` fermion identification;
- parity/supertrace relation.

**Proof route:** stage theorem → bond preservation → canonical map equality. Never reason by convergence of products.

### Task 6.3: Connect to mandated boundary owners

**Role:** coherence/capstone

**Read and reuse:**
- `Canonical/UHFInductiveColimitBoundary.lean`
- `Canonical/TensorTowerColimit.lean`
- `Canonical/ErlangenColimitResolution.lean`

**Objective:** identify the exact existing boundary interface that can receive the prime thermodynamic tower.

**Required outputs:**
- an explicit functor or compatible cone from prime stages;
- a direct-limit lift;
- a canonical-image readback theorem;
- no claim that the algebraic direct limit is automatically a C*-completion, von Neumann algebra, or physical continuum.

---

## Phase 7: Compatible thermodynamic readout cones

### Task 7.1: Define finite evaluation homomorphisms

**Role:** translator

**Objective:** evaluate occupation algebra stages at finite prime activities.

Separate cones:
- bosonic evaluation;
- positive-fermionic evaluation;
- signed-supertrace evaluation;
- order-`κ` parafermionic evaluation.

**Required theorem:** each evaluation commutes with the prime bonding maps.

### Task 7.2: Lift compatible evaluations from the colimit

**Role:** categorical translator

Reuse:

```text
directLimitLift
directLimitLift_unique
directLimitLift_ext
```

**Targets:** stage readback of every lifted evaluation and uniqueness from cone compatibility.

**Critical honesty condition:** if scalar activities depend on the cutoff and break compatibility, do not force a cone. First define a compatible symbolic/formal activity target or leave the scalar specialization finite-stage only.

### Task 7.3: State the categorical Riemann/primon identification

**Role:** capstone

**Target strength:** identify the colimit bosonic object by its compatible finite Euler-factor images and recurrence/universal property.

Do not define it as an analytically convergent product. A separate classical comparison theorem may show that finite-stage readouts coincide with Mathlib’s finite Euler products, but `riemannZeta` is not the constructor of the colimit object.

---

## Phase 8: State-sum and prime-mode categorical equivalence

### Task 8.1: Build finite unique-factorization correspondence

**Role:** owner/translator

**Objective:** connect bounded exponent vectors over finite primes to natural-number states generated by those primes.

**Required finite theorems:**
- encode exponent vector as a product of prime powers;
- decode by valuations within the finite prime support;
- encode/decode inverse laws;
- energy additivity:
  `log(product p^e_p) = Σ e_p log p` under positive finite data;
- finite state-sum/product combinatorial equality.

**No infinite sums or convergence.**

### Task 8.2: Prove compatibility under cutoff extension

**Role:** translator

Show the finite unique-factorization equivalence commutes with stage bonds. This supplies a natural transformation/equivalence of direct systems.

### Task 8.3: Descend the equivalence to direct limits

**Role:** categorical capstone

Construct the induced colimit maps in both directions and prove inverse laws using the universal property and canonical-stage readbacks.

This is the repository-native replacement for an analytic equation between an infinite Dirichlet sum and an infinite Euler product.

### Task 8.4: Keep Mathlib zeta as comparison shadow

**Role:** comparison only

**Likely file:**
- Create: `lean/InfoGeometry/Analytic/PrimonColimitZetaComparison.lean`

Import classical zeta theorems only here. Prove that each finite stage has the expected classical finite readout and that the previously existing half-plane theorem agrees with the categorical finite-stage dictionary where both are stated.

Do not use this file upstream of the colimit construction.

---

## Phase 9: Boltzmann/Massieu/free-energy transport

### Task 9.1: Canonicalize terminology and units

**Role:** coherence

**Owners:**
- `Potential/Thermo.lean`
- `GrandCanonical/Core.lean`
- arithmetic parafermion owner
- `PrimonFreeEnergyRelativeTrace.lean`

**Canonical dictionary:**

```text
Massieu/log generator: Ψ = log Ξ
Dimensionless free energy: βF = -Ψ
Physical free/grand potential: Ω = -β⁻¹ Ψ
Boltzmann entropy: S_B = Ψ + β(U - μN)
```

Add bridge theorems between existing names; do not silently rename public declarations until consumers are mapped.

### Task 9.2: Prove finite-bond stability of thermodynamic identities

**Role:** translator

Use `FiniteToInfiniteTransitionSOP`:

```text
readout_stable_along_finite_chain
readout_eq_stable_along_finite_chain
predicate_stable_along_finite_chain
```

Targets:
- partition normalization;
- Massieu/free-energy identity;
- Boltzmann entropy identity;
- parity/supertrace equality.

### Task 9.3: Lift only compatible thermodynamic identities

**Role:** categorical translator

If `log` prevents a ring-hom compatible cone, transport the algebraic partition equality first, then state `log` readouts on finite canonical images. Do not invent a global colimit `log` without an owner operation and compatibility theorem.

---

## Phase 10: Native `d ln Q` recurrence and colimit transport

### Task 10.1: Specialize `score_as_de_rham_potential` to finite partitions

**Role:** translator

**Modify:**
- `lean/InfoGeometry/Information/DeRhamScore.lean` or a focused new bridge file if owner size warrants.

**Targets:**
- finite Gibbs partition;
- finite prime fermion partition;
- finite parafermion partition.

Prove pointwise:

```text
deriv (log ∘ Q_stage) = deriv Q_stage / Q_stage
```

under explicit differentiability and nonzero hypotheses.

### Task 10.2: Prove recurrent logarithmic derivative identities

**Role:** owner/translator

For finite products, use Mathlib’s finite `logDeriv_prod`; do not take limits.

Targets:
- log derivative of a finite prime product is a finite sum of local log derivatives;
- successor-cutoff recurrence adds one local logarithmic response;
- parafermion `κ+1` recurrence readout.

### Task 10.3: Build a compatible response cone where possible

**Role:** categorical translator

Define stage response objects algebraically so their successor law is explicit. Prove compatibility before forming a direct-limit lift.

If actual scalar derivatives are not invariant under cutoff extension, represent the response as a recurrent stage family or finitely supported formal 1-form rather than postulating a global scalar derivative.

### Task 10.4: Replace `LogQClockCalibration` debt

**Role:** owner repair

Current debt:

```text
dlogQ : ℂ → ℂ
dlogQ_eq_poleForm : dlogQ = poleForm
```

Plan:
1. Keep existing calibration theorems as conditional legacy surfaces initially.
2. Define actual finite-stage `logDeriv` from the partition.
3. Compute its finite divisor/pole decomposition algebraically.
4. Prove winding only for the explicit rational/polynomial form and explicit finite loops supported by existing owners.
5. Remove or deprecate the arbitrary `dlogQ` field only after all consumers use the native construction.

No global de Rham-class claim is allowed merely from exactness.

---

## Phase 11: Superalgebra and parafermion closure on the colimit

### Task 11.1: Preserve parity grading under bonds

**Role:** owner

Prove successor prime bonds preserve even/odd grading and finite supercommutator laws.

### Task 11.2: Transport superclosure through the direct limit

**Role:** categorical translator

Reuse `DirectLimitSuperClosureLemmas` canonical-image theorems. State closure first on canonical images; global closure requires direct-limit induction or generation by canonical images.

### Task 11.3: Separate positive fermion from signed supertrace permanently

**Role:** coherence

Add a central dictionary theorem/file documenting and proving:

```text
positive fermion ≠ signed supertrace as definitions
boson × signed supertrace = 1 at finite stages
generic parafermion κ=2 = positive fermion
```

Do not infer object inequality from notation alone; prove only exact equalities/non-equalities supported by hypotheses.

---

## Phase 12: Final capstone and documentation cleanup

### Task 12.1: Assemble the theorem-honest capstone

**Role:** capstone

**Likely file:**
- Create: `lean/InfoGeometry/Canonical/PrimonParafermionColimitFramework.lean`

The capstone should import owner/translator modules and state only composed theorems:
- finite Gibbs factorization;
- generic parafermion recurrence;
- direct-system construction;
- direct-limit canonical maps;
- state-sum/prime-mode colimit equivalence;
- finite/canonical-image Massieu and Boltzmann identities;
- native finite-stage `d ln Q` response;
- parity/supertrace colimit readbacks.

It must not introduce new carrier data or assumptions.

### Task 12.2: Repair misleading prose and status documents

**Files to audit:**
- `Analytic/PrimonZeta.lean` docstring;
- `Thermodynamics/PrimonGasPhaseTransition.lean`;
- `DERHAM_BOLTZMANN_MODULAR_STATUS.md`;
- `MULTI_ENGINE_FORMALIZATION_COMPLETE.md`;
- `sympy_supersymmetric_pairing.py`;
- any docs calling analytic convergence or Taylor limits the repository authority.

**Objective:** align prose with compiled theorem strength and the categorical-colimit mandate. Do not delete historical artifacts; mark stale claims and point to canonical owners.

### Task 12.3: Umbrella imports and dependency checks

Only after every owner and translator builds independently:
1. add imports to the narrowest appropriate `All.lean` files;
2. build those umbrella modules;
3. verify there are no cycles;
4. update architecture maps and evidence ledgers.

---

## Verification protocol for every theorem-bearing task

1. Direct source check:

```text
lake env lean lean/InfoGeometry/<Path>.lean
```

2. Locked module build:

```text
python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock InfoGeometry.<Module>
```

3. Axiom audit:

```text
python3 tools/infra/axiom_index.py InfoGeometry.<Module>
```

Allowed foundational axioms only:

```text
propext
Classical.choice
Quot.sound
```

4. Source hygiene scan for:

```text
sorry
admit
axiom
certificate
socket
Tendsto
analytic continuation
convergence
completion
```

Interpret comments separately from executable code.

5. Direct consumer build after modifying an owner.

6. For direct-limit tasks, verify explicitly:
- one-step bond;
- identity/composition laws;
- `DirectedSystem` instance;
- actual `DirectLimit` carrier;
- canonical maps;
- bond compatibility;
- compatible-cone lift and uniqueness;
- theorem stated on canonical images or proved by direct-limit induction.

7. Never run `lake update`, modify manifests, normalize packages, or touch `.lake/packages`.

---

## Dependency order

```text
finite prime cutoff stages
→ finite state embeddings
→ finite Gibbs subset/product factorization
→ generic finite parafermion recurrence
→ canonical parafermion owner consolidation
→ prime-stage algebra carrier
→ one-step bonds and recurrent all-pairs maps
→ directed-system laws
→ algebraic DirectLimit and canonical maps
→ compatible boson/fermion/parafermion cones
→ finite unique-factorization state-sum/prime-mode equivalence
→ naturality under bonds
→ direct-limit equivalence
→ finite/canonical-image Massieu and Boltzmann transport
→ finite-stage d ln Q and recurrent response
→ native replacement of calibration debt
→ superalgebra closure transport
→ capstone and documentation cleanup
```

## Explicit non-goals

This plan does not attempt:
- analytic convergence of a prime product or Dirichlet series;
- analytic continuation;
- Taylor-series convergence;
- topological completion;
- RH;
- Hilbert–Pólya;
- zeta-zero spectral claims;
- automatic C*- or von Neumann-algebra completion;
- a nontrivial de Rham class from a globally exact real `d ln Q`;
- physical continuum claims without explicit colimit transport through the mandated boundary owners.

## Completion criteria

The framework is complete only when:

1. the finite prime Gibbs partition is natively factored;
2. generic finite parafermion recurrence is canonical and deduplicated;
3. a nontrivial prime-stage algebra tower and injective one-step bonds exist;
4. the actual algebraic direct limit and canonical maps compile;
5. state-sum and prime-mode direct systems are explicitly equivalent;
6. boson, positive fermion, signed supertrace, and parafermion relations hold on canonical colimit images;
7. Massieu/free-energy/Boltzmann identities are transported only through proved compatible finite-stage laws;
8. `d ln Q` is derived from actual finite partition functions rather than supplied calibration data;
9. all promoted modules pass targeted builds and axiom audits;
10. no analytic-convergence or Taylor-limit claim is used as finite-to-infinite authority.
