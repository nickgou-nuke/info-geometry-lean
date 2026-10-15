# OpenGauss / TeamAntigravity: The 17 False-as-Stated Traps Catalog (T1–T17)

> Status: Operational Law for OpenGauss Drafters, Workers, and Adversarial Refuters (`tools/infra/opengauss_screener.py`).  
> Purpose: Distilled catalog of recurring semantic and structural defects that pass human or LLM surface reading audits, but break down under kernel-checked Lean 4 verification or assembly.

---

### T1 — Raw Chart/Coordinate Extraction off Basepoint
* **Defect**: Formulating continuity, differentiability, or integral bounds on raw coordinate projections ($M \to E$, `coordChange`, `extChartAt I α x`) on non-trivial manifolds or bundles. The preferred chart index `achart x` jumps discontinuously as $x$ moves.
* **Litmus Test**: Does the charted point stay pinned at the basepoint $\alpha$, or does it travel along an orbit, curve, or integration variable? If it travels, **T1 fires**.
* **Remedy**: State statements intrinsically using total-space sections, bundle projections, or metric inner pairings ($g(u, v)$).

---

### T2 & T2′ — Free-Family Quantifiers & $\exists\forall$ Inversion
* **Defect (T2)**: Quantifying over a family or operator data ($V, C, u$) without hypotheses binding it to the object it parameterizes. A counterexample family satisfies the binders while trivially breaking the conclusion.
* **Defect (T2′)**: Writing $\exists V, \forall t, \dots$ when uniqueness forces the witness $V$ to vary with $t$ (e.g. unique Fréchet derivatives).
* **Remedy**: Mirror sibling lemmas to include the exact binding hypothesis. Place $\exists$ innermost ($\forall t, \forall x, \exists V, \dots$).

---

### T3 — Global Flatness / Locally Constant Chart Assertions
* **Defect**: Introducing hypotheses like `HasLocallyConstantChartAt` or assuming bundle charts are globally constant across compact or curved manifolds (e.g. $S^2$).
* **Remedy**: Strictly prohibited. Work with genuine smooth transition cocycles and connections.

---

### T4 — Vacuous Binders & Degenerate Conditions
* **Defect**: Hypotheses that hold vacuously (e.g. `0 = 0`, `True`, `x = x`, `inner 0 v = 0`, $\forall x \in \emptyset$, continuity of a constant function, regularity already guaranteed by typeclasses).
* **Remedy**: Replace with the non-trivial geometric or algebraic constraint; eliminate vacuous binders.

---

### T5 — Headline Leak
* **Defect**: An internal lemma requires a localized hypothesis (e.g. compact support, domain smallness, background metric equality $g = g_0$) that is accidentally exposed on the headline public theorem.
* **Remedy**: Discharge localized constraints internally via partitions of unity or colimits. If the headline must change, stop and align with the orchestrator.

---

### T6 — Hypothesis Packaging (Severe Violation)
* **Defect**: Adding a hypothesis whose type is definitionally equal to the conclusion (or adding `h : P` and closing the proof with `exact h`).
* **Remedy**: Immediate revert. A proof must derive the conclusion from structural primitives, not from self-assuming packaging.

---

### T7 — Family-as-Input vs. Existential Output
* **Defect**: Turning an existentially produced object (e.g. a remainder section or coordinate representation) into a free universal input $\forall R, \dots$, enabling trivial counterexamples like $R \equiv 0$.
* **Remedy**: Keep existentially produced witnesses as outputs ($\exists R, \dots$), or bind them with their defining identity.

---

### T8 — Per-Fibre vs. Joint Continuity
* **Defect**: Inferring joint continuity $\mathrm{Continuous}((s, x) \mapsto f(s, x))$ solely from per-fibre continuity $\forall x, \mathrm{Continuous}(s \mapsto f(s, x))$. Separate continuity does not imply joint continuity ($xy / (x^2+y^2)$).
* **Remedy**: State and prove the joint continuity directly via uniform approximations or topological product topologies.

---

### T9 — Two-Sided vs. One-Sided Derivatives on Intervals
* **Defect**: Demanding two-sided differentiability ($\forall t \in \mathbb{R}, \mathrm{HasDerivAt}$) on cutoff flow families that equal identity outside $[0, T]$ and jump at boundaries.
* **Remedy**: Restate using one-sided or within-interval derivatives (`HasDerivWithinAt ... (Ici 0)` or `Ioo 0 T`).

---

### T10 — $C^\infty$ at Boundary Over-Demand
* **Defect**: Demanding smooth derivatives up to $t=0$ when boundary regularity is only $C^0$ or finite-order $C^k$ (e.g. $\sqrt{s}$ with $\partial_s \to \infty$). Finite time-regularity can never support an infinite derivative tower.
* **Remedy**: Require interior $C^\infty$ on $(0, T)$ and $C^0$ or $C^k$ on $[0, T)$.

---

### T11 — Over-Strong / Non-Tensorial Posits (Dominant Restatement Driver)
* **Defect**: Stating a posited child lemma stronger than its consumer requires:
  - Demanding **pointwise** cancellation where only an **integrated** bound is needed.
  - Demanding **strict** bounds where a **non-strict** bound suffices.
  - Demanding **per-component / per-class** cancellation when cancellation is a property of the **summed whole tensor**.
* **Remedy**: Posit the consumer-minimal weakening. Extract the exact required signature directly from the parent proof glue.

---

### T12 — Multi-Conjunct $\exists$-Freedom Over-Constraint
* **Defect**: Asserting that $\exists w, P_1(w) \land \dots \land P_n(w)$ is satisfiable because each $P_i$ individually leaves $w$ free, while jointly the constraints force $w$ into an impossible remainder space.
* **Remedy**: Check the witness existence against all conjuncts simultaneously before positing the lemma.

---

### T13 — Metric Signature & Orientation Clashes
* **Defect**: Conflating Riemannian positive-definite inner products with split-signature Minkowski/Krein products ($\eta = \operatorname{diag}(1, -1)$), or reversing orientation signs in Levi-Civita / Clifford volume elements.
* **Remedy**: Maintain explicit metric signatures and orientation invariants in the type definition (e.g. `KreinMetric`, `q22`).

---

### T14 — Constant Factor & Dimension Scaling Mismatches
* **Defect**: Hardcoding dimension-dependent numerical factors (e.g. $1/2$, $1/4$, $2\pi$) across inductive colimit levels where dimension scales with matrix order $2^n$.
* **Remedy**: Parameterize bounds by explicit dimension or trace normalization ($\mathrm{tr}(1) = d$).

---

### T15 — Definitional Expansion & Unfolding Loops
* **Defect**: Permitting unrestricted `dsimp` or `unfold` on deep categorical colimits (`TensorTower`, `Colimit`, `Quotient`), generating multi-megabyte proof terms that time out the Lean elaborator.
* **Remedy**: Use opaque barriers, module projections, and focused helper rewrite lemmas (`simp only [...]`) rather than raw global simplification.

---

### T16 — Semantic Surrogate / Scalar Toy Proxy (The Anti-Cheating Invariant)
* **Defect**: Substituting a genuine noncommutative operator, matrix algebra, Lie algebra, or supermanifold carrier with a trivial scalar record, or collapsing noncommutative products before evaluating algebraic relations.
* **Four Automated Enforcement Gates (`tools/infra/opengauss_screener.py`)**:
  1. **Scalar Surrogate Struct Ban (`check_scalar_surrogates`)**: Rejects `structure` declarations named `BlockSuperTrace`, `*ScalarProxy`, `*TraceProxy`, `*DummyCarrier`, or structures bundling two or more scalar `tr_*` / `det*` / `schur*` fields in place of matrix/operator carriers.
  2. **Pre-Commutator Homomorphism Rejection (`check_homomorphism_rejection`)**: Flags expressions that collapse non-commutative algebras into scalars before commutator/Lie bracket evaluation (e.g. `commutator (Matrix.trace A) (Matrix.trace B)` or `tr A * tr B - tr B * tr A`).
  3. **Carrier-Matched Non-Commutativity Witness Requirement (`check_noncommutative_witness_requirement`)**: Every module performing operator multiplication on square matrices `Matrix (Fin n) (Fin n) R` ($n \ge 2$), `CliffordAlgebra`, or `QuaternionAlgebra` must contain or import a closed, untainted non-commutativity witness ($A * B \neq B * A$, $[A, B] \neq 0$, or anticommutator $\{i, j\} = 0$) matching every active matrix carrier signature $(n, n, R)$.
  4. **Scalar Tactic Misuse on Operators (`check_tactic_misuse_on_operators`)**: Rejects applying commutative scalar tactics (`ring`, `linarith`, `nlinarith`) directly to unprojected operator goals without prior `ext` / `Matrix.ext` / `funext` component projection.
* **Remedy**: Ground theorems natively in `Matrix (Fin n) (Fin n) R`, `Module.End R V`, or native Clifford/Jordan algebras, and prove or import an explicit non-commutativity witness for each carrier.

---

### T17 — Unwitnessed Structure / Model Non-Degeneracy Risk (Gate 2.5)
* **Defect**: Defining a `structure` or `class` with potentially contradictory or vacuous fields without proving that at least one concrete mathematical object actually inhabits it. Theorems taking `(x : MyEmptyStruct)` then compile vacuously over the empty set.
* **Automated Enforcement (`check_model_witnessing`)**:
  - Every declared `structure` or `class` (excluding `*Audit` or private internal metadata) must have either `deriving Inhabited` or a closed declaration directly inhabiting `StructName`, `Inhabited StructName`, or `Nonempty StructName`.
  - The witness must be closed over ambient `section` `variable` declarations, may only assume standard algebraic law typeclasses (never a local provider class supplying the target or `[Inhabited StructName]`), and must be transitively free of local or imported `axiom`, `opaque`, `sorry`, or `admit` taint.
* **Remedy**: Provide a constructive `def canonicalModel : MyStruct := ⟨...⟩` or `instance : Inhabited MyStruct` in the same module.

