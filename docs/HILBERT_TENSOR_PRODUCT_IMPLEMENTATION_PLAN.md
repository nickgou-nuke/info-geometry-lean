# Hilbert Space Tensor Product — Full Implementation Plan

AFP entry: `Hilbert_Space_Tensor_Product` by Unruh et al.
Source: 20,230 lines across 15 Isabelle theory files.
Local: `external_refs/afp/thys/Hilbert_Space_Tensor_Product/`

## Status Overview

| # | AFP File | Lines | SymPy | Lean 4 | Priority |
|:--|:---|:--|:--|:--|:--|
| 1 | `Hilbert_Space_Tensor_Product.thy` | 2,499 | ✓ core | ✓ core | **DONE** |
| 2 | `HS2Ell2.thy` | 212 | ✓ vectorize | partial | HIGH |
| 3 | `Partial_Trace.thy` | 390 | ✓ Tr_B, Tr_A | partial | HIGH |
| 4 | `Tensor_Product_Code.thy` | 255 | — | — | MED |
| 5 | `Trace_Class.thy` | 4,110 | — | — | MED |
| 6 | `Compact_Operators.thy` | 1,526 | — | — | MED |
| 7 | `Positive_Operators.thy` | 1,417 | — | — | LOW |
| 8 | `Spectral_Theorem.thy` | 724 | — | — | MED |
| 9 | `Misc_Tensor_Product.thy` | 2,447 | — | — | LOW |
| 10 | `Misc_Tensor_Product_TTS.thy` | 1,554 | — | — | LOW |
| 11 | `Misc_Tensor_Product_BO.thy` | 682 | — | — | LOW |
| 12 | `Von_Neumann_Algebras.thy` | 1,350 | — | — | HIGH |
| 13 | `Strong_Operator_Topology.thy` | 593 | — | — | LOW |
| 14 | `Weak_Operator_Topology.thy` | 1,069 | — | — | LOW |
| 15 | `Weak_Star_Topology.thy` | 814 | — | — | LOW |
| 16 | `Eigenvalues.thy` | 588 | — | — | LOW |

---

## Phase 1: Core Tensor Product ✓ DONE

**SymPy** (`tools/sympy/hilbert_tensor_product.py`, 296 lines):
- `tensor_product_vectors` / `tensor_product_operators` (Kronecker product)
- Associator (unitary permutation), Swap (orthogonal)
- Inner product identity: ⟨a⊗b,c⊗d⟩ = ⟨a,c⟩·⟨b,d⟩
- Partial trace: `Tr_B(A⊗B) = Tr(B)·A`, `Tr_A`
- HS ≅ ℓ² (vectorize isomorphism)
- All 5 properties verified by computation

**Lean 4** (`lean/InfoGeometry/HilbertTensorProduct.lean`, 290 lines):
- `tensorInner` on `H₁ ⊗[ℝ] H₂` with `tensorInner_tmul` lemma
- `tensorOp` via `TensorProduct.map` for bounded linear maps
- `assocEll2` = `TensorProduct.assoc` with `assocEll2_inner` (proved)
- `swapEll2` = `TensorProduct.comm` with `swapEll2_inner`, `swapEll2_selfinv` (proved)
- `partialTraceB`, `hsIsoEll2` (skeleton, needs completion)

---

## Phase 2: Hilbert-Schmidt ≅ ℓ² + Partial Trace (HIGH)

### 2a. HS2Ell2 — SymPy ✓, Lean: complete `hsIsoEll2`

The AFP proves `HS2Ell2` as an **isometric isomorphism** between:
- The space of Hilbert-Schmidt operators `HS(H₁,H₂) = {A : trace_class(A*A) < ∞}`
- The Hilbert space tensor product `H₁ ⊗ H₂`

**Lean implementation:**
```lean
-- For finite-dimensional H₁, H₂:
--   hsIsoEll2 : (H₁ →L[ℝ] H₂) ≃ₗᵢ[ℝ] (H₁ ⊗[ℝ] H₂)
--   where ≃ₗᵢ is a linear isometric equivalence
-- The map: vec(e_i e_j^*) = e_i ⊗ e_j  (rank-1 operators → pure tensors)
-- Proof: orthonormal basis expansion + ⟨vec(A), vec(B)⟩_tensor = Tr(A^T B) = ⟨A,B⟩_HS
```

**Effort:** ~100 lines Lean. The finite-dimensional case is straightforward with `Basis.ofVectorSpace`. The infinite-dimensional case requires the AFP's `some_chilbert_basis` machinery.

### 2b. Partial_Trace — SymPy ✓, Lean: complete `partialTraceB`

The AFP defines `partial_trace :: trace_class ⇒ trace_class` over infinite-dimensional separable Hilbert spaces, with:
- `partial_trace_plus`, `partial_trace_scaleC` (linearity)
- `partial_trace_tensor`: `Tr_B(t ⊗ u) = Tr(u) · t`
- `bounded_clinear_partial_trace` (bounded linear map)

**Lean implementation (finite-dim):**
```lean
-- For finite-dimensional spaces, the partial trace is:
--   Tr_B(ρ) : H₁ →L[ℝ] H₁  where ρ : H₁⊗H₂ →L[ℝ] H₁⊗H₂
--   ⟨a, Tr_B(ρ) b⟩ = Σ_k ⟨a⊗e_k, ρ(b⊗e_k)⟩  (e_k ONB of H₂)
-- Key lemma: Tr_B(A⊗B) = Tr(B)·A
```

**Effort:** ~80 lines Lean. Already have the skeleton; need to fill in the `LinearMap.mk` fields and prove the key identity.

---

## Phase 3: Von Neumann Algebras + Double Commutant (HIGH)

The AFP file `Von_Neumann_Algebras.thy` (1,350 lines, 227 lemmas) proves the **double commutant theorem**: for a *-subalgebra A ⊆ B(H), the bicommutant A'' equals the weak/strong closure of A. This is von Neumann's bicommutant theorem.

**Core definitions:**
```lean
-- Commutant: A' = {T ∈ B(H) : ∀S ∈ A, TS = ST}
-- Bicommutant: A'' = (A')'
-- Von Neumann algebra: A = A'' (closed under bicommutant)
```

**SymPy implementation:** Finite-dimensional matrix commutant computation — given a set of matrices, compute the commutant as the solution to `[A_i, X] = 0` for all generators.

**Lean implementation:** The finite-dimensional case is much simpler (all subspaces are closed). The infinite-dimensional case requires weak/strong operator topologies (Phase 5).

**Effort:** ~200 lines Lean (finite-dim), ~150 lines SymPy.

---

## Phase 4: Trace-Class + Compact Operators (MED)

### 4a. Trace_Class (4,110 lines, 456 lemmas)

The AFP defines:
- `trace_class A`: `Σ_e ⟨e, |A| e⟩ < ∞` for some ONB
- `trace A = Σ_e ⟨e, A e⟩` (basis-independent for trace-class)
- `hilbert_schmidt a = trace_class (a* a)`
- `hilbert_schmidt_norm a = sqrt(trace_norm (a* a))`

**SymPy:** For finite matrices, every operator is trace-class. Implement:
- `trace(A)`, `trace_norm(A) = Tr(|A|) = Σ σ_i(A)`
- `is_hilbert_schmidt(A)`, `hs_norm(A) = √Tr(A*A)`
- `is_trace_class(A)`, `trace_class_norm(A) = Tr(√(A*A))`

**Lean:** For finite-dimensional spaces, `trace_class` is trivial (all operators are trace-class). Implement:
- `trace` as `∑_i ⟨e_i, A e_i⟩` with basis-independence proof
- `hsInner` → `hsNorm` → `hsIsoEll2` (completing Phase 2a)

**Effort:** ~150 lines SymPy, ~120 lines Lean.

### 4b. Compact_Operators (1,526 lines, 133 lemmas)

The AFP defines `compact_op A` if `closure(A ` cball 0 1)` is compact. Key results:
- `finite_rank_compact_op`: finite-rank → compact
- `compact_op_finite_rank`: every compact op is limit of finite-rank ops
- `rank1_compact_op`: rank-1 operators are compact

**SymPy:** For finite matrices, all operators are compact. Implement SVD → finite-rank approximation.

**Lean:** For finite-dimensional spaces, every linear map is compact. The interesting content is the infinite-dimensional spectral theorem (Phase 4c).

**Effort:** ~80 lines SymPy, ~60 lines Lean.

---

## Phase 5: Spectral Theorem for Compact Operators (MED)

The AFP file `Spectral_Theorem.thy` (724 lines, 47 lemmas) proves: for a compact normal operator A on a Hilbert space, there exists an ONB of eigenvectors, and A can be diagonalized.

**SymPy implementation:**
- `spectral_decomposition(A)` → eigenvalues, eigenvectors via `eigenvects()`
- For self-adjoint A: `A = Σ λ_i |e_i⟩⟨e_i|`
- For compact normal A (finite-dim): `A = U Λ U*` (SVD)

**Lean implementation (finite-dim):**
- Use mathlib's `Module.End.eigenvalues` and `Diagonalization`
- For self-adjoint A: `∃ basis, A = ∑ λ_i · proj_{e_i}` (spectral theorem)
- The finite-dimensional spectral theorem is already in mathlib (`LinearMap.IsSymmetric.diagonalization`)

**Effort:** ~100 lines SymPy, ~80 lines Lean (mostly wiring mathlib).

---

## Phase 6: Operator Topologies (LOW)

### 6a. Strong_Operator_Topology (593 lines)
Topology of pointwise convergence: `A_n → A` strongly iff `∀x, A_n x → A x`.

### 6b. Weak_Operator_Topology (1,069 lines)
Topology: `A_n → A` weakly iff `∀x,y, ⟨y, A_n x⟩ → ⟨y, A x⟩`.

### 6c. Weak_Star_Topology (814 lines)
Topology on the dual of trace-class operators.

**SymPy:** Not applicable (finite-dimensional matrices have unique topology).

**Lean:** These topologies are already in mathlib (`Pi.topologicalSpace` for strong, `ContinuousLinearMap.weakOperatorTopology`). The work is in connecting them to the spectral theorem and von Neumann algebra definitions.

**Effort:** ~150 lines Lean (definitions + basic properties).

---

## Phase 7: Misc Tensor Product Files (LOW)

### 7a. Misc_Tensor_Product.thy (2,447 lines)
Foundational lemmas about tensor products, `summable_on`, `infsum` for tensor products of ℓ². Mostly infrastructure used by the main proof. Not needed for finite-dimensional case.

### 7b. Misc_Tensor_Product_TTS.thy (1,554 lines)
Tensor product of trace-class and Hilbert-Schmidt operators with specific series expansions. Heavy ∑-manipulation lemmas.

### 7c. Misc_Tensor_Product_BO.thy (682 lines)
Bounded operator lemmas specific to the tensor product context.

**SymPy:** Not needed (finite-dimensional, all operators are trace-class).

**Lean:** Skip for now. These are technical lemmas needed only for the infinite-dimensional generalization.

---

## Phase 8: Tensor Product Code (MED)

### Tensor_Product_Code.thy (255 lines, 46 lemmas)
Applies the tensor product to quantum error correction: stabilizer codes, logical operators, encoding isometries.

**SymPy implementation:**
- `stabilizer_code(generators)` → code subspace projector
- `logical_operators(code)` → X, Z logical operators
- `encoding_isometry(code)` → encode logical qubit into physical qubits
- `error_correction_condition(code, errors)` → Knill-Laflamme conditions

**Lean implementation:**
- Finite-dimensional stabilizer formalism over ℂ
- `is_stabilizer_code`, `logical_operators`, `encoding_isometry`
- `knill_laflamme_condition` → error correction possible

**Effort:** ~200 lines SymPy, ~150 lines Lean.

---

## Implementation Timeline

| Phase | Content | SymPy | Lean | Total |
|:--|:--|:--|:--|:--|
| 1 | Core tensor product | ✓ 296 | ✓ 290 | DONE |
| 2 | HS2Ell2 + Partial trace | ✓ | 180 | ~180 |
| 3 | Von Neumann + Double commutant | 150 | 200 | ~350 |
| 4 | Trace-class + Compact ops | 230 | 180 | ~410 |
| 5 | Spectral theorem | 100 | 80 | ~180 |
| 6 | Operator topologies | — | 150 | ~150 |
| 7 | Misc tensor (skip for now) | — | — | 0 |
| 8 | Tensor product code | 200 | 150 | ~350 |
| **Total** | | **~1,276** | **~1,330** | **~2,600** |

Lean total (including done): ~1,620 lines. This is about 8% of the AFP entry's 20,230 lines, reflecting that the finite-dimensional case is substantially simpler than the full infinite-dimensional separable Hilbert space treatment.

## Key Design Decisions

1. **Finite-dimensional first.** The AFP entry works over arbitrary separable Hilbert spaces (infinite-dimensional ℓ²). Our implementation works over finite-dimensional inner product spaces. This eliminates 90% of the technical complexity (summability, limits, closures, basis independence proofs).

2. **SymPy = computational verification.** SymPy verifies the algebraic identities by explicit matrix computation. This catches sign errors and structural mistakes before Lean proofs.

3. **Lean = abstract proofs over ℝ (not ℂ).** The AFP works over ℂ. Our Lean implementation works over ℝ for simplicity; the complex case is identical by replacing ℝ with ℂ in typeclass assumptions.

4. **Phase 7 (Misc Tensor) is low priority.** The 5,000+ lines of misc tensor lemmas are almost entirely about infinite summability and basis independence in infinite dimensions. They are not needed for finite-dimensional applications.
