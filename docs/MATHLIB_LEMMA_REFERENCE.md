# Mathlib Lemma Reference for InfoGeometry Closure Debt

Comprehensive reference of existing Mathlib lemmas and literature that can
close the open proof obligations. Generated 2026-06-15.

---

## 1. Nilpotent Exponential Truncation

### Mathlib lemmas (directly usable)

| Lemma | Module | Statement |
|---|---|---|
| `TrivSqZeroExt.exp_inr` | `Mathlib/Analysis/Normed/Algebra/TrivSqZeroExt` | `exp(inr m) = 1 + inr m` — exactly nilpotent exponential truncation! |
| `IsNilpotent.exp` | `Mathlib/RingTheory/Nilpotent/Exp` | Exponential of nilpotent element `a` where `a^k = 0` |
| `IsNilpotent.exp_eq_sum` | `Mathlib/RingTheory/Nilpotent/Exp` | `exp a = Σ_{i<k} a^i/i!` when `a^k = 0` |
| `IsNilpotent.exp_mul_exp_neg_self` | `Mathlib/RingTheory/Nilpotent/Exp` | `exp(a)·exp(-a) = 1` |
| `Matrix.exp_blockDiagonal'` | `Mathlib/Analysis/Normed/Algebra/MatrixExponential` | exp of block diagonal is block diagonal of exps |

### Usage for `BregmanMonodromyFusion.lean`

```lean
import Mathlib.RingTheory.Nilpotent.Exp
import Mathlib.Analysis.Normed.Algebra.TrivSqZeroExt

-- If K^2 = 0, then IsNilpotent K (with k=2), so:
-- IsNilpotent.exp K = I + K  (since all higher terms vanish)
-- This proves exponentialRemainder_is_jordan_block
```

### Literature reference
- **Hall (2015)**, *Lie Groups, Lie Algebras, and Representations*, §3.3 — matrix exponential nilpotent truncation

---

## 2. ℓ² Convergence of Orthogonal Series (Cuntz O_∞)

### Mathlib lemmas

| Lemma | Module | Statement |
|---|---|---|
| `OrthogonalFamily.summable_iff_norm_sq_summable` | `Mathlib/Analysis/InnerProductSpace/Subspace` | For orthogonal family V_i: Σ V_i(f_i) converges iff Σ ‖f_i‖² converges |
| `OrthogonalFamily.hasSum_linearIsometry` | `Mathlib/Analysis/InnerProductSpace/l2Space` | HasSum for orthogonal family in ℓ² |
| `OrthogonalFamily.linearIsometry` | `Mathlib/Analysis/InnerProductSpace/l2Space` | OrthogonalFamily → linear isometry from ℓ²(G) to E |

### Usage for `L2CuntzConvergence.lean`

The Cuntz isometries S_p satisfy `S*_p S_q = δ_{pq}·I` (orthogonal ranges).
With `OrthogonalFamily` and coefficients `a_p = p^{-β}`, the summability condition
`Σ a_p² < ∞` for `β > 1/2` gives norm convergence via `OrthogonalFamily.hasSum_linearIsometry`.

### Prime zeta convergence

| Lemma | Module | Statement |
|---|---|---|
| `Nat.Primes.summable_rpow` | `Mathlib/NumberTheory/SumPrimeReciprocals` | `Σ p^r` converges iff `r < -1` |
| `riemannZeta_eulerProduct_tprod` | `Mathlib/NumberTheory/EulerProduct/DirichletLSeries` | Euler product for Re(s) > 1 |
| `LSeriesSummable_one_iff` | `Mathlib/NumberTheory/LSeries/Dirichlet` | L-series summability criterion |

### Usage
For `β > 1/2`: let `r = -2β`. Then `r < -1` iff `β > 1/2`, so `Σ p^{-2β} = Σ p^r` converges
by `Nat.Primes.summable_rpow`. Hence `a_p = p^{-β}` is in ℓ².

---

## 3. Zorn's Lemma (Maximal Elements in Partially Ordered Sets)

### Mathlib lemmas (full suite)

| Lemma | Module | Statement |
|---|---|---|
| `zorn_subset_nonempty` | `Mathlib/Order/Zorn` | ∀ chain c ⊆ S, ∃ ub ∈ S bound for c → ∀ x ∈ S, ∃ maximal m ⊇ x |
| `zorn_le` | `Mathlib/Order/Zorn` | Every chain bounded above → ∃ maximal element |
| `zorn_le₀` | `Mathlib/Order/Zorn` | Chain condition on subset S → ∃ maximal element in S |
| `zorn_le_nonempty₀` | `Mathlib/Order/Zorn` | Same with nonempty chains |
| `exists_maximal_of_chains_bounded` | `Mathlib/Order/Zorn` | Generic Zorn (transitive relation) |

### Usage for `ZornsFurnace.lean` (already proved)
The proof uses `zorn_subset_nonempty` on the subset `S' = {x ∈ S | a ≤ x}`.

---

## 4. Clifford Algebra and Pin Group

### Mathlib lemmas

| Lemma | Module | Statement |
|---|---|---|
| `pinGroup` | `Mathlib/LinearAlgebra/CliffordAlgebra/SpinGroup` | Submonoid of Pin elements in Clifford algebra |
| `pinGroup.instGroup` | `Mathlib/LinearAlgebra/CliffordAlgebra/SpinGroup` | Pin group is a group |
| `pinGroup.conjAct_smul_ι_mem_range_ι` | `Mathlib/LinearAlgebra/CliffordAlgebra/SpinGroup` | Twisted adjoint action preserves vector subspace |

### Usage for `ConformalSpinorBridge`, `ConformalSL2GeneratorBridge`, `DAGMajorana`

The Pin group `Pin(5,5)` acts on the Clifford algebra `Cl(5,5)` via the
twisted adjoint action `g·x = g x α(g)^{-1}` where `α` is the parity
automorphism. This action preserves the quadratic form and maps onto `O(5,5)`.

The projective 2-cocycle arises from the central extension:
`1 → {±1} → Pin(V,Q) → O(V,Q) → 1`

---

## 5. Lie Algebra Extensions and 2-Cocycles

### Mathlib lemmas

| Lemma | Module | Statement |
|---|---|---|
| `LieAlgebra.Extension` | `Mathlib/Algebra/Lie/Extension` | Central extension of Lie algebras |
| `LieAlgebra.Extension.twoCocycleOf` | `Mathlib/Algebra/Lie/Extension` | Extract 2-cocycle from extension |
| `LieAlgebra.Extension.ofTwoCocycle` | `Mathlib/Algebra/Lie/Extension` | Construct extension from 2-cocycle |
| `LieModule.Cohomology.twoCocycle` | `Mathlib/Algebra/Lie/Cohomology` | 2-cocycle in Lie algebra cohomology |

### Usage for `DAGMajorana.lean`
The central residue is a 2-cocycle in Lie algebra cohomology.
`LieAlgebra.Extension.ofTwoCocycle` constructs the extension, and
`LieAlgebra.Extension.twoCocycleOf` recovers the cocycle.

### Literature
- **Moore (1964)**, *Group extensions of p-adic and adelic linear groups*
- **Atiyah–Bott–Shapiro (1964)**, *Clifford modules*, Topology 3

---

## 6. Von Neumann Algebras and KMS Theory

### Mathlib lemmas

| Lemma | Module | Statement |
|---|---|---|
| `VonNeumannAlgebra` | `Mathlib/Analysis/VonNeumannAlgebra/Basic` | Von Neumann algebra on Hilbert space |
| `VonNeumannAlgebra.commutant` | `Mathlib/Analysis/VonNeumannAlgebra/Basic` | Commutant (double commutant theorem) |
| `VonNeumannAlgebra.mem_commutant_iff` | `Mathlib/Analysis/VonNeumannAlgebra/Basic` | `z ∈ S' ↔ ∀ g ∈ S, gz = zg` |

### Usage for `HarmonicKMS.lean`
The KMS condition involves the modular automorphism group `σ_t` on the
Cuntz algebra `O_∞`, which is a von Neumann algebra factor (the hyperfinite
II₁ factor). `VonNeumannAlgebra` provides the algebraic infrastructure.

### Literature
- **Haag–Hugenholtz–Winnink (1967)**, *On the equilibrium states in quantum
  statistical mechanics*, Comm. Math. Phys. 5
- **Connes (1994)**, *Noncommutative Geometry*, §III.3
- **Bratteli–Robinson (1987)**, *Operator Algebras and Quantum Statistical Mechanics 1*

---

## 7. Twisted Adjunction in TrivSqZeroExt (Clifford Algebra Nilpotents)

### Mathlib lemmas

| Lemma | Module | Statement |
|---|---|---|
| `TrivSqZeroExt` | `Mathlib/Algebra/TrivSqZeroExt` | Trivial square-zero extension R ⊕ M with (r,m)·(r',m') = (rr', rm'+mr') |
| `TrivSqZeroExt.exp_inr` | `Mathlib/Analysis/Normed/Algebra/TrivSqZeroExt` | `exp(inr m) = 1 + inr m` (since m² = 0 in square-zero extension) |

### Usage
`TrivSqZeroExt` is the algebraic model for the Clifford algebra nilpotent
generators (K_e² = 0). The exponential truncation `exp(εK) = I + εK` when
`K² = 0` follows directly from `TrivSqZeroExt.exp_inr`.

---

## 8. Minkowski Gauge and Self-Concordant Barriers

### Mathlib lemmas

| Lemma | Module | Statement |
|---|---|---|
| `gauge` | `Mathlib/Analysis/Convex/Gauge` | Minkowski gauge functional |
| `gaugeSeminorm` | `Mathlib/Analysis/Convex/Gauge` | Gauge as seminorm for balanced convex absorbing sets |
| `interior_subset_gauge_lt_one` | `Mathlib/Analysis/Convex/Gauge` | Interior points have gauge < 1 |

### Usage for `BregmanMonodromyFusion.lean` (Dikin envelope lemma)
The Dikin envelope `ω(t) = t - log(1+t)` is the self-concordant barrier
bound. The Minkowski gauge `gauge` gives the norm on the feasible cone.

### Literature
- **Nesterov–Nemirovskii (1994)**, *Interior-Point Polynomial Algorithms in
  Convex Programming*, Thm 2.3.3
- **Renegar (2001)**, *A Mathematical View of Interior-Point Methods*

---

## 9. Golden Ratio Identities (QuantumSl2, Fibonacci Anyons)

### Mathlib lemmas

| Lemma | Module | Statement |
|---|---|---|
| `Real.sqrt` | `Mathlib/Data/Real/Sqrt` | Real square root |
| `Real.sq_sqrt` | `Mathlib/Data/Real/Sqrt` | `(Real.sqrt x)^2 = x` for `x ≥ 0` |
| `Complex.exp_add` | `Mathlib/Analysis/Complex/Exponential` | `exp(x+y) = exp(x)·exp(y)` |

### Usage for `QuantumSl2.lean`
The identity `φ² = φ + 1` where `φ = (1+√5)/2` is already proved (see
`fibonacci_fusion_from_quantum_group`). The trig identity
`e^{πi/5} + e^{-πi/5} = 2·cos(π/5) = φ` can be proved using Chebyshev
polynomials or `Complex.exp_add` + `Complex.cos`.

---

## 10. TKK Construction and Koecher–Vinberg Theorem

### NOT in Mathlib — requires new formalization

| Concept | Status | Reference |
|---|---|---|
| TKK Lie algebra from Jordan algebra | **Not in Mathlib** | Loos (1975), *Jordan Pairs*, LNM 460 |
| Koecher–Vinberg correspondence | **Not in Mathlib** | Faraut–Korányi (1994), *Analysis on Symmetric Cones* |

### Literature for new formalization

**TKK Construction:**
- **Loos (1975)**, *Jordan Pairs*, Lecture Notes in Math. 460 — the definitive monograph.
  Constructs the 3-graded Lie algebra L = J⁻ ⊕ str(J) ⊕ J⁺ from a Jordan pair J.
  Proof of Jacobi identity uses Jordan pair axioms.
- **Neher (1993)**, *Generators and relations for 3-graded Lie algebras* —
  gives a generators-and-relations proof suitable for formalization.
- **Faulkner (2000)**, *Jordan pairs and Hopf algebras* — Appendix A gives
  a detailed treatment of the TKK bracket.

**Koecher–Vinberg Theorem:**
- **Koecher (1957)**, *Positivitätsbereiche im Rⁿ*
- **Vinberg (1960)**, *The theory of homogeneous convex cones*, Trans. Moscow Math. Soc. 12
- **Faraut–Korányi (1994)**, *Analysis on Symmetric Cones*, Oxford — §§II-III
  give the complete proof: Jordan algebra ↔ homogeneous self-dual cone.

### Strategy for formalization
1. Use Mathlib's `IsJordan` / `IsCommJordan` from `Algebra/Jordan/Basic`
2. Use Mathlib's `LieAlgebra` from `Algebra/Lie/Basic`
3. Construct the TKK bracket explicitly as a 3-graded structure on `J × str(J) × J`
4. Verify Jacobi identity via case analysis on grades (finite computation)
5. For Koecher–Vinberg: construct the symmetric cone as `{x² : x ∈ J, invertible}ᵒ`,
   prove convexity via quadratic representation `P(x) = 2L_x² - L_{x²}`.

---

## 11. Discrete Hodge Decomposition (Eckmann's Theorem)

### NOT in Mathlib — requires new formalization

| Concept | Status | Reference |
|---|---|---|
| Discrete Hodge decomposition | **Not in Mathlib** | Eckmann (1945), Dodziuk (1976) |

### Literature

- **Eckmann (1945)**, *Harmonische Funktionen und Randwertaufgaben* —
  original discrete Hodge theorem. The kernel of the combinatorial Laplacian
  L_k is isomorphic to homology H_k.
- **Dodziuk (1976)**, *Finite-difference approach to the Hodge theory of
  harmonic forms*, Amer. J. Math. 98 — shows Whitney forms connect discrete
  and continuous Hodge theory.
- **Parzanchevski–Rosenthal–Tessler (2016)**, *Isoperimetric inequalities
  in simplicial complexes*, Combinatorica 36 — provides the modern treatment
  with explicit inner product choices.
- **arXiv:2512.05319** — *Eckmann's theorem for simplicial complexes* (2025)
  provides a self-contained treatment of the eigenvalue 0 multiplicity = Betti
  number theorem.

### Strategy for formalization
1. Define boundary operators ∂_k : C_k → C_{k-1} as matrices over ℤ
2. Define adjoints ∂_k* via the standard inner product ⟨e_i, e_j⟩ = δ_{ij}
3. Define Laplacian L_k = ∂_{k+1}∂_{k+1}* + ∂_k*∂_k
4. Prove: ker L_k = ker ∂_k ∩ ker ∂_{k-1}*
5. Prove: C_k = im ∂_{k+1} ⊕ ker L_k ⊕ im ∂_{k-1}* (orthogonal decomposition)
6. Conclude: dim(ker L_k) = β_k (Betti number)

### Usage for `HarmonicKMS.lean` and `BregmanMonodromyFusion.lean`
The Hodge decomposition classifies monodromy by chain type (exact/coexact/harmonic).

---

## 12. Cuntz Algebra (O_∞)

### Mathlib — partial

| Lemma | Module | Statement |
|---|---|---|
| `CuntzAlgebra` | (not in Mathlib — new construction needed) | Universal C*-algebra generated by isometries S_i with Σ S_i S_i* = 1 |

### Strategy
The Cuntz algebra O_∞ is the universal C*-algebra generated by isometries
`S_i` (`i ∈ ℕ`) satisfying `S_i* S_i = 1` and `S_i S_i*` are pairwise orthogonal
projections. Mathlib has the `VonNeumannAlgebra` infrastructure but not the
Cuntz algebra specifically. The construction can use:
- `StarAlgebra` / `CStarAlgebra` from Mathlib's analysis library
- The universal property: O_∞ = lim→ M_{2^n}(ℂ) (via the UHF embedding)

### Literature
- **Cuntz (1977)**, *Simple C*-algebras generated by isometries*, Comm. Math. Phys. 57
- **Davidson (1996)**, *C*-Algebras by Example*, §V.4

---

## 13. Modular Automorphism Group and Tomita–Takesaki Theory

### Mathlib — partial

| Lemma | Module | Statement |
|---|---|---|
| `VonNeumannAlgebra` | `Mathlib/Analysis/VonNeumannAlgebra/Basic` | Von Neumann algebra structure |

### NOT in Mathlib
- Tomita–Takesaki modular automorphism group σ_t
- KMS condition (β-KMS state, modular flow)
- Connes cocycle derivative theorem

### Literature
- **Takesaki (2003)**, *Theory of Operator Algebras II*, §VIII-IX
- **Connes (1973)**, *Une classification des facteurs de type III*, Ann. Sci. ENS 6
- **Summers (2006)**, *Tomita-Takesaki Modular Theory*, Encyclopedia of Mathematical Physics

---

## 14. Spectral Triple and Cyclic Cohomology (Connes)

### Mathlib — partial

| Lemma | Module | Statement |
|---|---|---|
| (none directly) | — | Spectral triple, cyclic cocycle, Chern character |

### Literature
- **Connes (1994)**, *Noncommutative Geometry*, §IV (spectral triples), §III (cyclic cohomology)
- **Connes–Marcolli (2008)**, *Noncommutative Geometry, Quantum Fields and Motives*
- **Gracia-Bondía–Várilly–Figueroa (2001)**, *Elements of Noncommutative Geometry*

---

## 15. Summary: What Exists vs. What Needs New Formalization

### CONFIRMED in local Mathlib cache (apply immediately)

Verified via `lean_local_search` against `external_refs/atlas-lean/.lake/packages/mathlib/`.

| # | Lemma | Local path |
|---|---|---|
| 1 | `TrivSqZeroExt.exp_inr` | `Mathlib/Analysis/Normed/Algebra/TrivSqZeroExt.lean` |
| 2 | `zorn_subset_nonempty` | `Mathlib/Order/Zorn.lean` |
| 3 | `OrthogonalFamily.summable_iff_norm_sq_summable` | `Mathlib/Analysis/InnerProductSpace/Subspace.lean` |
| 4 | `pinGroup` | `Mathlib/LinearAlgebra/CliffordAlgebra/SpinGroup.lean` |
| 5 | `Nat.Primes.summable_rpow` | `Mathlib/NumberTheory/SumPrimeReciprocals.lean` |

### Available in Mathlib (verified via LeanSearch, not in local cache)

| # | Lemma | Mathlib module |
|---|---|---|
| 6 | `IsNilpotent.exp_eq_sum` | `Mathlib/RingTheory/Nilpotent/Exp` |
| 7 | `IsNilpotent.exp_mul_exp_neg_self` | `Mathlib/RingTheory/Nilpotent/Exp` |
| 8 | `Matrix.exp_blockDiagonal'` | `Mathlib/Analysis/Normed/Algebra/MatrixExponential` |
| 9 | `LieAlgebra.Extension.twoCocycleOf` | `Mathlib/Algebra/Lie/Extension` |
| 10 | `LieAlgebra.Extension.ofTwoCocycle` | `Mathlib/Algebra/Lie/Extension` |
| 11 | `VonNeumannAlgebra` | `Mathlib/Analysis/VonNeumannAlgebra/Basic` |
| 12 | `zorn_le`, `zorn_le₀`, `zorn_le_nonempty₀` | `Mathlib/Order/Zorn` |
| 13 | `Complex.exp_add` | `Mathlib/Analysis/Complex/Exponential` |
| 14 | `gauge`, `gaugeSeminorm` | `Mathlib/Analysis/Convex/Gauge` |
| 15 | `riemannZeta_eulerProduct_tprod` | `Mathlib/NumberTheory/EulerProduct/DirichletLSeries` |

### Needs new formalization (major effort)
1. 🔴 TKK Lie algebra construction (3-graded structure from Jordan algebra)
2. 🔴 Koecher–Vinberg correspondence (formally real Jordan ↔ symmetric cone)
3. 🔴 Discrete Hodge decomposition on finite complexes (Eckmann theorem)
4. 🔴 Cuntz algebra O_∞ (universal C*-algebra of isometries)
5. 🔴 Tomita–Takesaki modular automorphism group
6. 🔴 Spectral triple / cyclic cocycle pairing
7. 🔴 Connes cocycle condition (u(s+t) = u(s)σ_s(u(t)))
8. 🔴 KMS condition / KMS state construction on Cuntz algebra

### Partially available (can be built from Mathlib components)
1. 🟡 SL(2,ℝ)/SO(1,1) symmetric space bijection — can use `InnerProductSpace` + Lorentz metric
2. 🟡 Thermofield double partial trace — can use `FiniteDimensional` + tensor product
3. 🟡 Matrix exponential definability — available via `NormedSpace.exp` for complete normed algebras
4. 🟡 Projective 2-cocycle — `LieAlgebra.Extension` works for Lie algebras; needs Clifford adaptation

---

## References

- **Mathlib4**: https://github.com/leanprover-community/mathlib4
- **Loogled results**: Type-pattern search at https://loogle.lean-lang.org/
- **LeanSearch**: Natural-language search at https://leansearch.net/
- **Mathlib docs**: https://leanprover-community.github.io/mathlib4_docs/
