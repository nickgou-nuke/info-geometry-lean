# Stream 9 Closure Plan: Two-Sided Cayley–Dickson Laplace–Mellin Kernel

**File:** `lean/InfoGeometry/Canonical/TwoSidedCayleyDicksonLaplaceKernel.lean`
**Status:** Kernel-checked (Lean 4 v4.34.1), zero `sorry`, zero `admit`, zero custom axioms.
**Parent stream:** Ludkovsky (`arXiv:math/0612755`) — Two-Sided Laplace Transformation over Cayley–Dickson Algebras.

---

## 1. Current State

### 1.1 What is formalized and verified

| Component | Declaration | Status | Mathematical Content |
|-----------|-------------|--------|---------------------|
| Dual seed pair structure | `IsDualSeedPair (d B : A)` | Reused from `InfoGeometry.Core.DualSeedPeirce` | `d² = 0`, `B² = 0`, `dBd = d`, `BdB = B` |
| Poles and supports | `polePlus`, `poleMinus`, `carrierSupport`, `wheelGenerator` | Reused | `P₊ = d·B`, `P₋ = B·d`, `Δ = P₊ + P₋`, `J = d - B` |
| Hyperbolic Laplace kernel | `hyperbolicKernel lam mu d B` | Defined | `D(λ, μ) = λ•P₊ + μ•P₋` |
| Elliptic phase kernel | `ellipticKernel c s d B` | Defined | `R(c, s) = c•Δ + s•J` |
| Two-sided Laplace transform | `twoSidedHyperbolicLaplace lamL muL lamR muR d B X` | Defined | `D(λ_L, μ_L) * X * D(λ_R, μ_R)` |
| 8 atomic Peirce multiplication lemmas | `hyperbolicKernel_mul_d`, `d_mul_hyperbolicKernel`, `hyperbolicKernel_mul_B`, `B_mul_hyperbolicKernel`, `hyperbolicKernel_mul_polePlus`, `polePlus_mul_hyperbolicKernel`, `hyperbolicKernel_mul_poleMinus`, `poleMinus_mul_hyperbolicKernel` | Proven | Left/right multiplication rules of `D(λ, μ)` against `d`, `B`, `P₊`, `P₋` |
| 4-Sector eigen-scaling theorem | `twoSidedHyperbolicLaplace_sector_scaling` | Proven | `P₊ ↦ λ_L·λ_R`, `P₋ ↦ μ_L·μ_R`, `d ↦ λ_L·μ_R`, `B ↦ μ_L·λ_R` |
| Symmetric vs. antisymmetric selectivity | `symmetric_vs_antisymmetric_laplace_selectivity` | Proven | For `λ·μ = 1`: symmetric fixes `(d, B)`, scales `(P₊, P₋)`; antisymmetric fixes `(P₊, P₋)`, scales `(d, B)` |
| Moufang two-sided convolution | `moufang_two_sided_laplace_convolution` | Proven | Flexible sandwich `(K*X)*K = K*(X*K)` and middle Moufang `(K*X)*(Y*K) = K*((X*Y)*K)` on `StandardIntegralSplitOctonion` |

### 1.2 Infrastructure dependencies (already in repo, kernel-checked)

- `InfoGeometry.Core.DualSeedPeirce` — `IsDualSeedPair`, pole/plus/minus identities, Clifford squares, polarization/velocity identities.
- `InfoGeometry.Canonical.MoufangIdentities` — `splitOctonion_moufang_middle` for `StandardIntegralSplitOctonion` via rational transport through `ZornVectorMatrixRationalEquiv`.
- `InfoGeometry.Algebra.ZornAlternativeLaws` — `associator_left_alternative`, `associator_right_alternative`, `associator_flexible` on native `ZornVectorMatrix R`.
- `InfoGeometry.Canonical.StandardIntegralSplitOctonionMultiplication` — `splitOctonionMul`, `splitOctonion_flexible`.
- `InfoGeometry.Canonical.ZornVectorMatrixIsomorphism` — equivalence between integral and rational Zorn presentations.

### 1.3 What is NOT yet formalized (the 7 closure gaps)

The following gaps are ordered by **causal dependency**: earlier gaps must be closed before later ones can be meaningfully attempted. Each gap is scored by **leverage** (how many downstream corridors it unlocks).

---

## 2. Causal-Order Closure Plan

---

### Gap 1: Dual Seed Pair ≅ Cl(1,1) Modular Atom

**Leverage:** Critical — roots Stream 9 in the Connection Tower base. Without this, `D(λ, μ)` is just a Laplace kernel; with it, `D(λ, μ)` *is* the two-sided modular flow on the atom that the entire tower (tensor tower → KMS → Freudenthal → E7/E8) is built upon.

**Causal prerequisite:** None. Can start immediately.

**What is known (kernel-checked):**
- `InfoGeometry.Core.DualSeedPeirce.clifford_squares`: `(d - B)² = -(d·B + B·d)`, `(d + B)² = d·B + B·d`, `(P₊ - P₋)² = P₊ + P₋`.
- `polarization_velocity`: phase/velocity anticommutator vanishes.
- `velocity_eq_zero_iff`: `d + b = 0 ↔ d = 0 ∧ b = 0`.
- `InfoGeometry.Canonical.Cl11ModularAtom` / `PrimeCl11ModularAtomCore`: `P₊`, `P₋`, `Γ = P₊ - P₋`, `J = d - B`, `Δ = P₊ + P₋` (owner surface: proved/conditional).

**What to formalize:**
1. Identify `polePlus d B` with `P₊` of the Cl(1,1) atom and `poleMinus d B` with `P₋`.
2. Prove `carrierSupport d B = Δ` (active carrier) and `wheelGenerator d B = J` (skew-Majorana wheel).
3. Prove `Γ² = Δ` (chiral grading squares to active carrier).
4. Prove `J² = -Δ` (skew-Majorana squares to negative active carrier).
5. Prove `{Γ, J} = 0` (grading anticommutes with wheel).
6. Show `hyperbolicKernel lam mu d B = lam • P₊ + mu • P₋` matches the atom's hyperbolic damping factor `e^{-στΓ}`.
7. Show `ellipticKernel c s d B = c • Δ + s • J` matches the elliptic phase rotor `e^{-ωtJ}`.
8. Prove the loxodromic factorization `L(λ, μ, c, s) = D(λ, μ) * R(c, s)` requires and satisfies `[Δ, J] = 0` (commutativity of diagonal sum with wheel).

**Lean file target:** `lean/InfoGeometry/Canonical/DualSeedPeirceCl11AtomBridge.lean`

**Success criterion:** Kernel-checked theorem stating that `(d, B)` dual seed pair induces a Cl(1,1) modular atom with `Γ² = Δ`, `J² = -Δ`, `{Γ, J} = 0`, and `D(λ, μ)` = hyperbolic damping factor on that atom.

---

### Gap 2: Native Zorn Middle Moufang Law

**Leverage:** High — unlocks Moufang two-sided convolution for the *native* `ZornVectorMatrix` carrier, which is the owner for all split-octonion geometry (`SplitOctonionClassificationCore`, `SplitOctonionAssociator`, `SplitOctonionRigidity`, `ZornComposition`). Without this, Stream 9's Moufang law is trapped on `StandardIntegralSplitOctonion` and cannot interoperate with the native Zorn stack.

**Causal prerequisite:** Gap 1 (recommended, because the octonionic Moufang law should be proven on the same carrier that hosts the Cl(1,1) atom structure).

**What is known (kernel-checked):**
- `ZornAlternativeLaws`: `associator_left_alternative`, `associator_right_alternative`, `associator_flexible` on `ZornVectorMatrix R` (characteristic-free, Bruck–Kleinfeld associator calculus).
- `MoufangIdentities`: `splitOctonion_moufang_middle` for `StandardIntegralSplitOctonion` via rational transport.
- `ZornVectorMatrixRationalEquiv`: equivalence between integral and rational presentations.

**What to formalize:**
1. Prove `middle_moufang_native : ∀ (X Y Z : ZornVectorMatrix R), (X * Y) * (Z * X) = X * ((Y * Z) * X)` directly on `ZornVectorMatrix R`.
2. Prove `flexible_native : ∀ (X Y : ZornVectorMatrix R), (X * Y) * X = X * (Y * X)` (already exists as `associator_flexible`, but should be restated as flexible sandwich law).
3. Prove transport equivalence: middle Moufang on `StandardIntegralSplitOctonion` iff middle Moufang on `ZornVectorMatrix ℚ` via `zornVectorMatrixRationalEquiv`.
4. Show `splitOctonion_moufang_middle` is the integral presentation of the native Zorn middle Moufang.

**Lean file target:** `lean/InfoGeometry/Canonical/NativeZornMiddleMoufang.lean`

**Success criterion:** Kernel-checked middle Moufang identity on `ZornVectorMatrix R` for arbitrary commutative ring `R`, with transport equivalence to the integral presentation.

---

### Gap 3: Two-Sided Laplace Kernel = KMS / Modular Flow

**Leverage:** Very High — this is the bridge between "Laplace transform" and "modular thermodynamics." It makes Stream 9 the computational kernel of the KMS/modular layer rather than a standalone transform. Without it, the Laplace kernel has no physical interpretation in the repo's modular framework.

**Causal prerequisite:** Gap 1 (must identify `D(λ, μ)` with the Cl(1,1) atom before identifying it with modular flow).

**What is known (kernel-checked / documented):**
- `InfoGeometry.Canonical.InfiniteKMSCondition`, `KMSInteriorPoint` (owner surface: proved/conditional).
- `First Law of Modular Thermodynamics`: `dS = d⟨K⟩` derived from `d ln Q = 0` (documented in `docs/FIRST_LAW_MODULAR_THERMODYNAMICS.md`; local packet in `GrandIdentityDeRhamModular.lean`).
- Tomita–Takesaki modular automorphism group `σ_t`, modular conjugation `J`, KMS thermal periodicity `τ → τ + iβ`.
- Operator wavefront duality: `O_foc(τ) = σ_{-τ}(O₀)`, `O_defoc(τ) = σ_{+τ}(O₀')`, Klein glide reflection.

**What to formalize:**
1. Identify `λ = e^{-στ}`, `μ = e^{+στ}` with modular flow parameters.
2. Prove `D(λ_L, μ_L) * X * D(λ_R, μ_R)` corresponds to `σ_{-τ_L}(X) * σ_{+τ_R}(X)` (two-sided modular action).
3. Prove symmetric kernel (`λ_R = λ_L`, `μ_R = μ_L`, `λμ = 1`) fixes `(d, B)` and scales `(P₊, P₋)` corresponds to modular flow preserving the diagonal sectors.
4. Prove antisymmetric kernel (`λ_R = μ_L`, `μ_R = λ_L`, `λμ = 1`) fixes `(P₊, P₋)` and scales `(d, B)` corresponds to modular conjugation `J` swapping sectors.
5. Prove KMS periodicity `τ → τ + iβ` is encoded by `λ μ = 1` (unimodularity condition).
6. Show the First Law `dS = d⟨K⟩` emerges from the derivative of the two-sided Laplace kernel with respect to `τ` at `τ = 0`.

**Lean file target:** `lean/InfoGeometry/Canonical/TwoSidedLaplaceModularFlowBridge.lean`

**Success criterion:** Kernel-checked identification of `twoSidedHyperbolicLaplace` with the two-sided modular action on a KMS state, with symmetric/antisymmetric selectivity corresponding to modular flow vs. modular conjugation.

---

### Gap 4: Tensor Tower Colimit of Two-Sided Laplace Kernels

**Leverage:** Very High — satisfies the **Colimit Continuum Mandate**. Without this, the Laplace kernel remains finite-dimensional. The repo explicitly forbids analytical continuation; infinite boundaries must come from inductive colimits of finite algebras.

**Causal prerequisite:** Gap 3 (the colimit must be of modular/Laplace kernels, not just raw algebras).

**What is known (kernel-checked):**
- `InfoGeometry.Clifford.Cl11TensorTower.*` and `Canonical.TensorTowerColimit` (owner surface: proved/conditional).
- `Colimit Ledger Protocol` (`docs/COLIMIT_LEDGER_PROTOCOL.md`): colimit claims need named Lean declarations and universal properties; supplied cocones are not universal colimits.
- `ColimitContinuum` directory (owner surface).

**What to formalize:**
1. Define inductive system `A_n` with bonding maps `ι_n : A_n → A_{n+1}` where each `A_n` carries a dual seed pair `(d_n, B_n)`.
2. Prove bonding maps commute with the two-sided Laplace kernel: `ι_n(D_n(λ_L, μ_L) * X * D_n(λ_R, μ_R)) = D_{n+1}(λ_L, μ_L) * ι_n(X) * D_{n+1}(λ_R, μ_R)`.
3. Construct the colimit cone `ψ_n : A_n → A_∞` and prove `ψ_n ∘ ι_n = ψ_{n+1}`.
4. Define `colim D_n(λ_L, μ_L) * X_n * D_n(λ_R, μ_R)` as the continuum two-sided Laplace–Mellin transform.
5. Register in the Colimit Ledger with `genuineness = genuine_colimit` and `role = canonical_owner`.

**Lean file target:** `lean/InfoGeometry/ColimitContinuum/TwoSidedLaplaceColimit.lean`

**Success criterion:** Kernel-checked inductive colimit of two-sided Laplace kernels with universal property, registered in the Colimit Ledger.

---

### Gap 5: Freudenthal Charge Space ← Dual Seed Pair (concrete socket model)

**Leverage:** High — Freudenthal charge space is currently a **socket** (explicit debt in `ARCHITECTURE.md`: "proved abstract invariant formulas; socket for concrete split Albert model"). Giving it a concrete native model via the dual seed pair discharges debt and connects Stream 9 to the exceptional tower (E7/E8 target).

**Causal prerequisite:** Gap 1 (dual seed pair must be a Cl(1,1) atom before embedding into Freudenthal charge space).

**What is known (documented / socket):**
- `InfoGeometry.Exceptional.Freudenthal`, `FreudenthalAction`: abstract cubic Jordan and Freudenthal charge data; invariant actions preserving symplectic structure.
- `InfoGeometry.Canonical.AlbertCayleyDickson`: Albert doubling `A ⊕ A` with parameter `γ`, star involution `(p, q) ↦ (p*, -q)`; "does not claim a ring structure on the doubled carrier."
- No concrete split Albert model exists yet.

**What to formalize:**
1. Construct explicit embedding of `(A, d, B)` dual seed pair into Freudenthal charge space (or split Albert algebra via Albert doubling).
2. Show `P₊ = d·B`, `P₋ = B·d` are charge-space elements (idempotents in the Jordan product).
3. Show `d`, `B` are nilpotent charge elements (`d² = B² = 0`) with reflexive sandwich (`dBd = d`, `BdB = B`).
4. Prove two-sided Laplace weights act on Freudenthal quartic-invariant sectors.
5. Register as `closed_by_repo_owner` (discharging socket debt).

**Lean file target:** `lean/InfoGeometry/Exceptional/DualSeedPairFreudenthalEmbedding.lean`

**Success criterion:** Kernel-checked explicit embedding of dual seed pair into Freudenthal charge space, with quartic-invariant covariance under two-sided Laplace weights.

---

### Gap 6: Cuntz/Cantor Boundary ↔ Dual Seed Pair (tower base anchor)

**Leverage:** High — anchors Stream 9 at the **base** of the Connection Tower. Without this, the Laplace kernel floats above the Cuntz/Cantor foundation rather than being built into it.

**Causal prerequisite:** Gap 1 (recommended; the peirce/modular identification helps relate Cuntz corners to Peirce sectors).

**What is known (kernel-checked):**
- `InfoGeometry.Canonical.CantorCuntzBasis`, `CantorCuntzCliffordBridge`, `CuntzCantorSpectralTriple`, `HilbertCuntz` (owner surface: proved/conditional).
- Cuntz isometries `s_i` satisfy `s_i * s_j = δ_ij` (orthonormal isometries).
- `InfoGeometry.Quantum.FermionicOperators`, `CantorCuntzCliffordBridge` (Fermionic/CAR bridge).

**What to formalize:**
1. Represent `d` and `B` as Cuntz isometry differences or corner projections in the Cuntz algebra `O_∞` or `O_2`.
2. Show `d² = B² = 0` follows from Cuntz isometry orthogonality.
3. Show `dBd = d`, `BdB = B` as reflexive sandwich in the Cuntz corner.
4. Prove two-sided Laplace weights act on Cuntz boundary sectors (edge modes / corner states).
5. Relate `P₊`, `P₋` to Cuntz corner projections.

**Lean file target:** `lean/InfoGeometry/Canonical/CuntzDualSeedPairBridge.lean`

**Success criterion:** Kernel-checked representation of dual seed pair in Cuntz algebra, with two-sided Laplace weights acting on Cuntz boundary corners.

---

### Gap 7: Split Cl(4,4) Triality ↔ Octonionic Moufang (exceptional side branch)

**Leverage:** Medium-High — connects the **exceptional side branch** (`Oₛ → Der(Oₛ) = 𝔤₂` per `Real Hestenes–Krein–Souriau Quantization Protocol`) to the main tower. Not required for the Laplace kernel to function, but the natural route toward the `E7(7)` / `E8(8)` socket.

**Causal prerequisite:** Gap 2 (native Zorn middle Moufang must be closed before relating it to triality).

**What is known (proxy / socket):**
- `InfoGeometry.Canonical.SplitCl44TKKJordanLieBridge`, `Spin44CharacterShadow` (owner surface: "Split Cl(4,4) / triality proxy — proved proxy, not full classification").
- `Real Hestenes–Krein–Souriau Quantization Protocol`: exceptional side branch `Oₛ → Der(Oₛ) = 𝔤₂`; native split-octonion multiplication not replaced by associative Clifford multiplication.
- `ARCHITECTURE.md`: "E7/E8 exceptional realization: debt/socket. No owner file currently proves a concrete realization."

**What to formalize:**
1. Relate split Cl(4,4) triality automorphisms to automorphisms of split octonions (`G₂`).
2. Show middle Moufang identity is invariant under triality proxy.
3. Prove two-sided Laplace weights transform covariantly under triality.
4. Register progress toward E7/E8 socket (do not claim full realization).

**Lean file target:** `lean/InfoGeometry/Canonical/SplitCl44OctonionMoufangBridge.lean`

**Success criterion:** Kernel-checked covariance of Moufang two-sided convolution under split Cl(4,4) triality; explicit progress marker toward E7/E8 socket (no overclaim).

---

## 3. Execution Order and Dependencies

```
Gap 1: Dual Seed Pair = Cl(1,1) Atom
    │
    ├──→ Gap 2: Native Zorn Middle Moufang
    │         │
    │         └──→ Gap 7: Split Cl(4,4) Triality ↔ Moufang
    │
    ├──→ Gap 3: Two-Sided Laplace = KMS / Modular Flow
    │         │
    │         └──→ Gap 4: Tensor Tower Colimit of Kernels
    │
    ├──→ Gap 5: Freudenthal ← Dual Seed Pair (socket discharge)
    │
    └──→ Gap 6: Cuntz Boundary ↔ Dual Seed Pair
```

**Recommended execution sequence:**

1. **Gap 1** first — establishes the carrier identity that everything else builds on.
2. **Gap 2** second — frees the Moufang law from the integral presentation.
3. **Gap 3** third — connects Laplace to modular flow (the physical interpretation).
4. **Gap 4** fourth — extends to continuum via colimits (mandate compliance).
5. **Gap 5** fifth — discharges Freudenthal socket debt.
6. **Gap 6** sixth — anchors at tower base.
7. **Gap 7** seventh — exceptional side branch (optional for core deliverable, required for E7/E8 path).

---

## 4. Repository Compliance Rules (from AGENTS.md, ARCHITECTURE.md, Constructive Closure Mandate)

All formalization work must obey:

1. **Zero `sorry`, zero `admit`, zero custom axioms.** Only foundational Lean 4 axioms (`[propext, Classical.choice, Quot.sound]`).
2. **No `lake clean`;** use `python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock <target>` for all builds.
3. **Sequential builds only** — never concurrent `lake build` / `lake test`.
4. **Proactively stage:** `git add -A` after every file creation/modification.
5. **Constructive Closure Mandate:** witness packets / external certificates are temporary scaffolding only; prefer native Lean derivations.
6. **Colimit Ledger Protocol:** any colimit claim needs a named Lean declaration and universal property; supplied cocones ≠ universal colimits.
7. **Categorical Infrastructure Map:** matrix-level code is an instance layer, never a replacement for categorical owner layers.
8. **T16 Prohibition:** no scalar toy proxies for noncommutative operator algebras.

---

## 5. Definition of Done per Gap

Each gap is complete when:
- [ ] New Lean file(s) created under `lean/InfoGeometry/Canonical/` (or appropriate subdirectory).
- [ ] All theorems kernel-checked via `lake build <target>`.
- [ ] Zero `sorry`, zero `admit`, zero `axiom`s in the new file.
- [ ] File imports only existing owner infrastructure (no new dependencies outside repo).
- [ ] `git add -A` executed.
- [ ] Gap documented in this plan with status updated to `closed`.

---

## 6. Status Tracking

| Gap | Title | Status | Lean File | Dependencies |
|-----|-------|--------|-----------|--------------|
| 1 | Dual Seed Pair = Cl(1,1) Atom | `open` | `DualSeedPeirceCl11AtomBridge.lean` | None |
| 2 | Native Zorn Middle Moufang | `open` | `NativeZornMiddleMoufang.lean` | Gap 1 (rec) |
| 3 | Two-Sided Laplace = KMS / Modular Flow | `open` | `TwoSidedLaplaceModularFlowBridge.lean` | Gap 1 |
| 4 | Tensor Tower Colimit of Kernels | `open` | `TwoSidedLaplaceColimit.lean` | Gap 3 |
| 5 | Freudenthal ← Dual Seed Pair | `open` | `DualSeedPairFreudenthalEmbedding.lean` | Gap 1 |
| 6 | Cuntz Boundary ↔ Dual Seed Pair | `open` | `CuntzDualSeedPairBridge.lean` | Gap 1 (rec) |
| 7 | Split Cl(4,4) Triality ↔ Moufang | `open` | `SplitCl44OctonionMoufangBridge.lean` | Gap 2 |

**Stream 9 base module:** `TwoSidedCayleyDicksonLaplaceKernel.lean` — **`closed`** (kernel-checked, committed).

---

*This plan is navigation evidence. Lean owner files and kernel checks decide truth. Update status as each gap is closed.*