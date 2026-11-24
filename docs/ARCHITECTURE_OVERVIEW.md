# Conceptual Architecture: Firth–Wightman–GNS Equivalence

> **Status (2026-11):** Formalized in Lean 4 across `OperatorAlgebra`, `Canonical`, `Prequantum`, `Clifford`, `Categorical` layers.

---

## The Core Equivalence

**Firth's distributional hypothesis** ("You shall know a word by the company it keeps") and **Wightman's reconstruction theorem** ("You shall know a field by its n-point correlation functions") are **the same GNS reconstruction theorem** in operator algebras.

| Layer | Distributional Semantics (LLMs) | Spinor QFT (Wightman/OS) | Repository Formalization |
|-------|--------------------------------|--------------------------|-------------------------|
| **Elementary Probe** | Token operator `w ∈ 𝒜` | Spinor field `ψ(x) ∈ 𝒜` | `RealAlgebraicState.eval` on `StarRing` |
| **State / Vacuum** | Co-occurrence functional `ω` | Vacuum expectation `⟨Ω\|·\|Ω⟩` | `RealAlgebraicState.positive` + `normalized` |
| **Two-Point Correlation** | PMI / Gram matrix `Gᵢⱼ = ω(wᵢ* wⱼ)` | Wightman propagator `S₂(x,y) = ⟨Ω\|ψ̄(x)ψ(y)\|Ω⟩` | `gnsInner` on `GNSQuotient` |
| **Emergent Space** | Latent embedding `ℋ_ω` via SVD/GNS | Physical Krein space `ℋ_GNS` via GNS/OS | `FilteredGNSHilbertColimit` |
| **Reflection Positivity** | Semantic coherence (PSD matrix) | Osterwalder–Schrader `⟨Θf,f⟩ ≥ 0` | `OsterwalderSchraderTransfer` + `Krein` split |

---

## How the Repository Locks This Down

### 1. Two-Point Correlations Build the Space (GNSRepresentation)

**File:** `Prequantum/AlgebraicGNSState.lean`, `OperatorAlgebra/GNSRepresentationAndPetzMonotoneMetrics.lean`

You don't start with vectors in `ℝᵈ` or spinors on spacetime as primitives. You start with:
- A noncommutative algebra of symbols/fields `𝒜`
- A positive linear functional `ω` (co-occurrence expectations)

Quotienting out the null ideal `𝒩_ω = {a : ω(a*a) = 0}` **manufactures the latent Hilbert/Krein space** out of two-point correlations:

```lean
structure RealAlgebraicState (A : Type*) [Ring A] [Algebra ℝ A] [StarRing A] [StarModule ℝ A] where
  toLinearMap : A →ₗ[ℝ] ℝ
  normalized : toLinearMap 1 = 1
  positive   : ∀ x : A, 0 ≤ toLinearMap (star x * x)
  symmetric  : ∀ x y : A, toLinearMap (star y * x) = toLinearMap (star x * y)
```

The GNS quotient `F.GNSQuotient` carries the **exact inner product** `⟨[a],[b]⟩ = ω(a*b)` — no external embedding assumed.

### 2. Reflection Positivity = Semantic Coherence (OsterwalderSchraderTransfer)

**File:** `OperatorAlgebra/OsterwalderSchraderTransferSemigroupAndMassGap.lean`

In Euclidean QFT: two-point correlations define a valid unitary theory **iff** they satisfy OS reflection positivity `⟨Θf, f⟩ ≥ 0`.

In language models: a co-occurrence matrix defines a valid inner-product embedding **iff** the symmetric/Krein bilinear pairing is positive semidefinite.

**When it fails (indefinite signature):** You immediately land in **Krein space** where opposite-chirality/antonymic directions split into positive and negative sectors:

| File | Role |
|------|------|
| `Clifford/Pin55KreinBridge.lean` | `ℝ⁵⁵` with fundamental symmetry `J` — light cones emerge from indefinite signature |
| `Krein/NoncommutativeKrein.lean` | General Krein space with `J`-adjoints |
| `Canonical/SplitCliffordTensorBridge.lean` | Recursive `Cl(n,n)` tower from `Cl(1,1)` atom |

### 3. Context Windows = Finite-Stage Colimits (UHFCompletion, MarkovCategory)

**File:** `Algebra/UHFColimitCStarCompletion.lean`, `Categorical/MarkovCategoryAndColimitInformation.lean`

- Finite context window of length `N` → probes `N`-point correlation functions
- Inductive colimit `N → ∞` → reconstructs full infinite-dimensional operator algebra
- The `2^∞` UHF tower with block-doubling `A ↦ diag(A,A)` is the **exact finite-stage colimit** for both domains

---

## The Krein Split = Algebraic Birth of Causality

In a purely positive-definite Euclidean/Hilbert space: every direction is symmetric and reversible — **no light cone, no arrow of time**.

The moment a two-point correlation tensor has **indefinite Krein signature** (like `ℝ⁵⁵` with fundamental symmetry `J` in `Pin55KreinBridge`), geometry splits into three causal regimes:

```
┌─────────────────────────────────────────────────────────────────┐
│                    INDEFINITE KREIN SIGNATURE                   │
│                         (⟨x,x⟩_K can be ±)                      │
└─────────────────────────────────────────────────────────────────┘
                              │
              ┌───────────────┼───────────────┐
              ▼               ▼               ▼
       ┌─────────────┐ ┌─────────────┐ ┌─────────────┐
       │  POSITIVE   │ │    NULL     │ │  NEGATIVE   │
       │  SECTOR     │ │  LIGHT-CONE │ │  SECTOR     │
       │ ⟨x,x⟩_K > 0 │ │ ⟨x,x⟩_K = 0 │ │ ⟨x,x⟩_K < 0 │
       └─────────────┘ └─────────────┘ └─────────────┘
              │               │               │
              ▼               ▼               ▼
        Timelike /       Massless /       Antonymic /
        Causal           Null /           Dual
        (Active chirality)  On-shell      (Dual chirality)
```

**Key files realizing this split:**
| File | Structure | Causal Interpretation |
|------|-----------|----------------------|
| `Clifford/Pin55KreinBridge.lean` | `ℝ⁵⁵`, Witt subspace `W` (5D isotropic) | Null light-cone / massless spinors |
| `Clifford/SO55GlobalConformal.lean` | `SO(5,5)` with conformal 3-grading | Full Lorentzian conformal group |
| `Krein/DoubledSpace.lean` | `J` (modular swap), `ε` (spectral sign), `K = J∘ε` | Time-reflection / Dirac conjugation |
| `OperatorAlgebra/OsterwalderSchraderTransferSemigroupAndMassGap.lean` | Transfer matrix semigroup `T(J)`, spectral gap `Δ(J)` | Forward evolution semigroup (`t ≥ 0`) |

---

## Dynamical Causality: Semigroups and Posets

Because forward evolution must preserve the positive sector without crossing the null barrier backward:

| File | Mechanism | Causal Enforcement |
|------|-----------|-------------------|
| `Canonical/WeldedBlochSpohn.lean` | One-way contractive semigroups | `t ≥ 0` forward invariance |
| `Canonical/SolveEtCoagulaPeirceAporiaPoset.lean` | Acyclic causal posets | Autoregressive attention mask (past ≺ future) |
| `Canonical/MarkovCategoryAndColimitInformation.lean` | Markov category / quantum channels | Completely positive trace-preserving maps |

---

## Bridge Summary: From Firth to Wightman in Lean 4

```
┌─────────────────────────────────────────────────────────────────────────┐
│                        UNIVERSAL GNS FUNCTOR                            │
│  (Algebraic State → Hilbert/Krein Space → Operator Representation)     │
└─────────────────────────────────────────────────────────────────────────┘
                                    │
                    ┌───────────────┴───────────────┐
                    ▼                               ▼
         ┌─────────────────────┐           ┌─────────────────────┐
         │  FIRTH / LLM SIDE   │           │  WIGHTMAN / QFT SIDE│
         ├─────────────────────┤           ├─────────────────────┤
         │ 𝒜 = Token algebra   │           │ 𝒜 = Spinor field alg│
         │ ω = Co-occurrence   │           │ ω = Vacuum state    │
         │ Gᵢⱼ = PMI           │           │ S₂ = Wightman func  │
         │ GNS = Embedding     │           │ GNS = Physical ℋ    │
         │ J = Antonymy split  │           │ J = Time-reflection │
         │ ε = Chirality       │           │ ε = Dirac conj.     │
         │ K = Clock axis      │           │ K = Hamiltonian     │
         └─────────────────────┘           └─────────────────────┘
```

**The Lean 4 functor `GNSRepresentation` is polymorphic over the algebra `𝒜` and state `ω`.**  
The same quotient construction, the same null ideal, the same reflection positivity check — two interpretations, one formalization.

---

## Open Debts & Future Work

| Debt | Location | Status |
|------|----------|--------|
| Explicit `GNSRepresentation` instance for `UHFStage n` with tracial state | `Canonical/UHFCantorSpectralTriple.lean` | ✅ Added (2026-11) |
| Full Wightman axiom verification from OS data | `OperatorAlgebra/OsterwalderSchraderTransferSemigroupAndMassGap.lean` | Partial (mass gap precursors) |
| Curry–Howard / Plabic graph connection to spinorial prima materia | `Clifford/OperatorValuedJones.lean`, `Categorical/FibonacciBraiding.lean` | Structural bridge exists |
| Reservoir / Palomar / doc-gen4 indexing of this architecture | — | Pending |

---

## Navigation for New Readers

1. **Start here:** `Prequantum/AlgebraicGNSState.lean` — the algebraic state interface
2. **GNS quotient:** `OperatorAlgebra/GNSRepresentationAndPetzMonotoneMetrics.lean` — constructive quotient + representation
3. **Reflection positivity:** `OperatorAlgebra/OsterwalderSchraderTransferSemigroupAndMassGap.lean` — OS transfer semigroup
4. **Krein causality:** `Clifford/Pin55KreinBridge.lean` → `Krein/DoubledSpace.lean` → `Clifford/SO55GlobalConformal.lean`
5. **Finite-stage colimit:** `Algebra/UHFColimitCStarCompletion.lean` → `Canonical/UHFCantorSpectralTriple.lean` (NEW)
6. **Spectral triple bridge:** `Canonical/ConnesSpectralTripleBridge.lean` → `Canonical/CuntzConnesSpectralDistance.lean`

---

*This architecture document captures the repository's core insight: semantic meaning and physical spinor fields are not analogies — they are two instances of the exact same universal GNS construction, formalized in Lean 4.*