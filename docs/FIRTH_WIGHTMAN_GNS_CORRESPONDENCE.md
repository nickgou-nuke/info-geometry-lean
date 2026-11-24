# Firth–Wightman–GNS: Lean 4 Type-Level Correspondence

> **Purpose:** Direct mapping from conceptual table (ARCHITECTURE_OVERVIEW.md) to exact Lean 4 definitions and theorems.

---

## 1. Elementary Probe: The Algebra `𝒜`

| Concept | Lean 4 Type | Location |
|---------|-------------|----------|
| Token algebra / Spinor field algebra | `A : Type* [Ring A] [StarRing A]` | `Prequantum/AlgebraicGNSState.lean:45` |
| Generator `w` / `ψ(x)` | `x : A` | `RealAlgebraicState.eval` |
| Star operation `*` | `star : A → A` | `StarRing` typeclass |

**Key point:** The same `StarRing` carrier serves both domains.  
No separate "embedding layer" — the algebra *is* the probes.

---

## 2. State / Vacuum: The Functional `ω`

| Concept | Lean 4 Definition | Location |
|---------|-------------------|----------|
| Co-occurrence / Vacuum state | `RealAlgebraicState A` | `Prequantum/AlgebraicGNSState.lean:45` |
| Normalization `ω(1) = 1` | `normalized : toLinearMap 1 = 1` | Line 50 |
| Positivity `ω(a*a) ≥ 0` | `positive : ∀ x, 0 ≤ toLinearMap (star x * x)` | Line 52 |
| Symmetry `ω(b*a) = ω(a*b)` | `symmetric : ∀ x y, toLinearMap (star y * x) = toLinearMap (star x * y)` | Line 54 |
| Evaluation `ω(a)` | `eval F a := F.toLinearMap a` | Line 61 |

**Concrete instances:**
- UHF tracial state: `uhfTracialState n A = trace(A) / 2ⁿ` — `Canonical/UHFCantorSpectralTriple.lean:86`
- Cl(1,1) tower state: `normalizedTowerTrace` — `OperatorAlgebra/GNSRepresentationAndPetzMonotoneMetrics.lean:29`

---

## 3. Two-Point Correlation: The Gram/Bilinear Form

| Concept | Lean 4 Definition | Location |
|---------|-------------------|----------|
| Gram matrix `Gᵢⱼ = ω(wᵢ* wⱼ)` | `gnsInner F u v = F.eval (star u.repr * v.repr)` | `OperatorAlgebra/GNSRepresentationAndPetzMonotoneMetrics.lean:147` |
| Null ideal `𝒩_ω = {a : ω(a*a) = 0}` | `gnsNullSet F = {x : A | F.eval (star x * x) = 0}` | `Prequantum/AlgebraicGNSState.lean:105` |
| GNS quotient `ℋ_ω = A / 𝒩_ω` | `GNSQuotient F := Quot (gnsEquiv F)` | Line 108 |
| Quotient inner product | `⟨[a],[b]⟩ = ω(a*b)` | `gnsInner` construction in `GNSRepresentationAndPetzMonotoneMetrics.lean` |

**The fundamental theorem (GNS):**
```lean
theorem gnsInner_self_eq_zero_iff (F : RealAlgebraicState A) (u : F.GNSQuotient) :
    gnsInner F u u = 0 ↔ u = 0
```
— **Strict positivity** on the quotient (no null vectors survive).

---

## 4. Emergent Space: The GNS Hilbert/Krein Space

| Concept | Lean 4 Construction | Location |
|---------|---------------------|----------|
| Finite-stage GNS space | `GNSStage Stage T ω n` | `Canonical/CuntzGNSFilteredSystem.lean:37` |
| Hilbert space colimit | `GNSHilbertColimit Stage T ω` | Line 41 |
| Stage embedding | `gnsStageToHilbertColimit` | Line 45 |
| Density of union | `dense_iUnion_range_gnsStageToHilbertColimit` | Line 60 |
| Completeness | `gnsHilbertColimit_complete` | Line 69 |
| Topological colimit | `gnsTopologicalDiagram : ℕ ⥤ TopCat` | Line 88 |

**For UHF/Cantor specifically:**
- `UHFCantorGNSHilbertColimit` — `Canonical/UHFCantorSpectralTriple.lean:256`
- `uhfGNSStageToColimit` — Line 259

---

## 5. Reflection Positivity & Krein Split

### 5.1 Osterwalder–Schrader (Euclidean QFT)

| Concept | Lean 4 Definition | Location |
|---------|-------------------|----------|
| Transfer matrix `T(J)` | `transferMatrix J` | `OperatorAlgebra/OsterwalderSchraderTransferSemigroupAndMassGap.lean:97` |
| Ground projection `P₀` | `projGround = [[½,½],[½,½]]` | Line 58 |
| Excited projection `P₁` | `projExcited = [[½,-½],[-½,½]]` | Line 62 |
| Spectral gap `Δ(J) = -log(tanh J)` | `spectralGap J = -Real.log (tanh J)` | Line 156 |
| Exponential clustering `⟨W_L⟩ = e^{-LΔ}` | `wilsonLoopExpectation` | Line 178 |
| Reflection `Θ` | `osReflect` | Line 234 |

### 5.2 Krein Space Signature Split

| Concept | Lean 4 Definition | Location |
|---------|-------------------|----------|
| Fundamental symmetry `J` | `modular_j : E × E → E × E` | `Krein/DoubledSpace.lean:33` |
| Spectral sign `ε` | `spectral_epsilon` | Line 47 |
| Clock axis `K = J∘ε` | `clockAxis` | Line 61 |
| `ℝ⁵⁵` Witt subspace | `W : Submodule ℝ (ℝ⁵⁵)` | `Clifford/Pin55KreinBridge.lean` |
| Positive sector `⟨x,x⟩_K > 0` | `{x | 0 < ⟪x,x⟫_K}` | `Krein/NoncommutativeKrein.lean` |
| Null cone `⟨x,x⟩_K = 0` | `{x | ⟪x,x⟫_K = 0}` | `Clifford/SO55GlobalConformal.lean` |

**The causal split theorem (informal):**
```
ℝ⁵⁵ = V₊ ⊕ W ⊕ V₋   (orthogonal wrt Krein pairing)
  where  V₊ = {x | ⟨x,x⟩_K > 0}  (timelike / active chirality)
         W  = {x | ⟨x,x⟩_K = 0}  (null / light-cone / massless)
         V₋ = {x | ⟨x,x⟩_K < 0}  (antonymic / dual chirality)
```

---

## 6. Context Windows = Finite-Stage Colimits

| Concept | Lean 4 Construction | Location |
|---------|---------------------|----------|
| UHF stage `M_{2ⁿ}(ℂ)` | `UHFStage n = Matrix (Fin 2ⁿ) (Fin 2ⁿ) ℂ` | `Algebra/UHFColimitCStarCompletion.lean:45` |
| Block-doubling `A ↦ diag(A,A)` | `uhfStep n` | Line 48 |
| Isometry `‖uhfStep A‖ = ‖A‖` | `uhfStep_norm` | Line 120 |
| Directed colimit algebra | `UHFAlg` | Line 240 |
| C*-completion | `UHFCStar` | Line 270 |
| Traced state compatibility | `uhfTracialState_compat` | `Canonical/UHFCantorSpectralTriple.lean:100` |

**The colimit diagram:**
```
UHFStage 0 → UHFStage 1 → UHFStage 2 → ... → UHFAlg → UHFCStar
    │           │           │                │
    ▼           ▼           ▼                ▼
GNS₀       GNS₁       GNS₂          GNS_∞
    │           │           │                │
    └───────────┴───────────┴────────────────┘
                    │
                    ▼
            FilteredGNSHilbertColimit
```

---

## 7. Dynamics: Semigroups and Causal Posets

| Concept | Lean 4 Construction | Location |
|---------|---------------------|----------|
| Forward semigroup `t ≥ 0` | `transferMatrixSemigroup` | `OperatorAlgebra/OsterwalderSchraderTransferSemigroupAndMassGap.lean` |
| Contractivity | `‖T(J)ⁿ‖ ≤ 1` | Line 200+ |
| Peirce poset (acyclic) | `SolveEtCoagulaPeirceAporiaPoset` | `Canonical/SolveEtCoagulaPeirceAporiaPoset.lean` |
| Markov category / CP maps | `MarkovCategoryAndColimitInformation` | `Categorical/MarkovCategoryAndColimitInformation.lean` |
| Autoregressive mask | `causalAttentionMask` | (implicit in attention modules) |

---

## 8. Dirac Operator & Spectral Triple (Connes Distance)

| Concept | Lean 4 Definition | Location |
|---------|-------------------|----------|
| Cl(1,1) generator `γ₀` | `diracGenerator = [[0,1],[1,0]]` | `Canonical/UHFCantorSpectralTriple.lean:117` |
| Dirac `D_n = Σ γ₀ ⊗ ...` | `uhfDirac n` | Line 135 |
| Commutator `[D,a]` | `commutator D a = D*a - a*D` | `ConnesSpectralTripleBridge.lean:47` |
| Commutator norm `‖[D,a]‖` | `commutatorNorm` | Line 49 |
| Lipschitz ball `‖[D,a]‖ ≤ 1` | `LipschitzFunction` | Line 58 |
| Connes distance `d(μ,ν)` | `StateDistanceBound` | Line 63 |
| Distance symmetry | `distance_bound_symmetry` | Line 39 |
| Triangle inequality | `distance_bound_triangle` | Line 46 |

---

## 9. Navigation Index: Concept → File → Definition

```
CONCEPT                    FILE                                            KEY DEFINITION
──────────────────────────────────────────────────────────────────────────────────────
Algebraic state ω          Prequantum/AlgebraicGNSState.lean              RealAlgebraicState
GNS quotient               OperatorAlgebra/GNSRepresentationAndPetzMonotoneMetrics.lean  GNSQuotient, gnsInner
Null ideal                 Prequantum/AlgebraicGNSState.lean              gnsNullSet
Hilbert colimit            Canonical/CuntzGNSFilteredSystem.lean          GNSHilbertColimit
UHF tower                  Algebra/UHFColimitCStarCompletion.lean         UHFStage, uhfStep
UHF tracial state          Canonical/UHFCantorSpectralTriple.lean         uhfTracialState
Dirac operator             Canonical/UHFCantorSpectralTriple.lean         uhfDirac
Spectral triple            Canonical/ConnesSpectralTripleBridge.lean      SpectralTriple
Connes distance            Canonical/CuntzConnesSpectralDistance.lean     StateDistanceBound
OS reflection positivity   OperatorAlgebra/OsterwalderSchraderTransfer... osReflect, spectralGap
Krein fundamental symmetry Krein/DoubledSpace.lean                        modular_j, spectral_epsilon
ℝ⁵⁵ Witt subspace          Clifford/Pin55KreinBridge.lean                 W (5D isotropic)
Causal poset               Canonical/SolveEtCoagulaPeirceAporiaPoset.lean PeirceAporiaPoset
Finite-stage spectral trip Canonical/UHFCantorSpectralTriple.lean         uhfStageSpectralTriple
```

---

## 10. Polymorphic GNS Functor (The Unifying Theorem)

The entire architecture rests on this single polymorphic construction:

```lean
-- In Prequantum/AlgebraicGNSState.lean
structure RealAlgebraicState (A : Type*) [Ring A] [Algebra ℝ A] [StarRing A] [StarModule ℝ A] where
  toLinearMap : A →ₗ[ℝ] ℝ
  normalized  : toLinearMap 1 = 1
  positive    : ∀ x : A, 0 ≤ toLinearMap (star x * x)
  symmetric   : ∀ x y : A, toLinearMap (star y * x) = toLinearMap (star x * y)

-- In OperatorAlgebra/GNSRepresentationAndPetzMonotoneMetrics.lean
def GNSQuotient (F : RealAlgebraicState A) : Type* := Quot (gnsEquiv F)
def gnsInner (F : RealAlgebraicState A) (u v : F.GNSQuotient) : ℝ := F.eval (star u.repr * v.repr)
```

**This same structure is instantiated by:**
1. `uhfTracialState n : RealAlgebraicState (UHFStage n)` — LLM context window
2. `clTowerRealState n : RealAlgebraicState (ClTower ℝ n)` — Cl(1,1) tensor tower
3. Vacuum state on spinor field algebra — Wightman QFT

**The quotient `GNSQuotient F`, the inner product `gnsInner`, the representation `gnsRep` — all are definitionally identical.**  
Only the carrier `A` and state `F` change.

---

*This correspondence table is the "source of truth" for navigating from the conceptual architecture (ARCHITECTURE_OVERVIEW.md) to the exact Lean 4 formalization.*