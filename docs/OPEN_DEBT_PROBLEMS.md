# Open Debt Problems — Detailed Mathematical Formulation

> This document states every open Bucket 3 theorem as a complete math problem:
> explicit premises, explicit proposition, and the context that explains why it
> matters.  Each problem is self‑contained and can be handed to a Lean
> formalizer without further research.

---

## Preliminary: The Fibonacci Fusion Category

Let `τ` be the Fibonacci anyon charge satisfying the fusion rule

```
τ ⊗ τ ≅ 1 ⊕ τ
```

with fusion matrix `F` and braiding matrix `R`.  Over ℂ, the F‑matrix is

```
F(τ,s) = ⎡τ   s⎤
         ⎣s  −τ⎦
```

where `τ² + τ = 1` and `s² = τ`.  The braid generator `σ₁` on two anyons is

```
B(τ,s,q) = F(τ,s) · R(q) · F(τ,s)
```

with `R(q) = diag(q⁻⁴, q³)` where `q` is a unit in ℂ.  At the Fibonacci root
of unity, `q = exp(iπ/5)`, the scalar `τ` is the golden ratio conjugate
`τ = (√5 − 1)/2 ≈ 0.618`.

---

## Problem 1: Full‑Twist Monodromy as Hadjiivanov Matrix

### Context

The **full twist** in the braid group `B₂` is `Δ = σ₁²`.  Under the Fibonacci
representation `π₂ : B₂ → GL(2,ℂ)`, the image `π₂(σ₁) = B(τ,s,q)`.  The full
twist `π₂(Δ) = B²` is the **monodromy matrix** — it describes the phase
acquired by the two‑anyon wavefunction after a full 2π rotation.

The logarithmic CFT literature (Georgiev–Hadjiivanov–Todorov) gives an explicit
formula for this monodromy:

```
M(h) = ⎡e^{2πih}    2πi·e^{2πih}⎤
       ⎣   0            e^{2πih} ⎦
```

where `h ∈ ℂ` is the conformal weight of the primary field.  This is the
**Hadjiivanov monodromy matrix**.

The open problem is to prove that these two descriptions coincide: that the
full‑twist matrix `B²` (expressed in the Fibonacci data `τ,s,q`) equals
`M(h)` under the correct specialization of `q` and identification of `h`.

### Premises

1. **Fibonacci scalar data** — two complex numbers `τ, s ∈ ℂ` satisfying

   ```
   τ² + τ = 1,    s² = τ
   ```

2. **Braid generator** — the 2×2 complex matrix

   ```
   B(τ,s,q) = F(τ,s) · R(q) · F(τ,s)
   ```

   where

   ```
   F(τ,s) = ⎡τ   s⎤            R(q) = ⎡q⁻⁴   0 ⎤
            ⎣s  −τ⎦                   ⎣ 0    q³⎦
   ```

   and `q ∈ ℂˣ` is a unit.

3. **Conformal weight** — a complex number `h ∈ ℂ`.

4. **Hadjiivanov monodromy** — the 2×2 matrix

   ```
   M(h) = ⎡e^{2πih}    2πi·e^{2πih}⎤
          ⎣   0            e^{2πih} ⎦
   ```

5. **Specialization condition** — there exists a unit `q₀ ∈ ℂˣ` such that

   ```
   q₀ = exp(iπ/5),    τ = (√5 − 1)/2,    s = √τ
   ```

   and the conformal weight `h` satisfies

   ```
   e^{2πih} = q₀⁴    (equivalently  h ≡ 1/5  mod ℤ)
   ```

### Proposition

Under premises 1–5, the full‑twist matrix equals the Hadjiivanov monodromy:

```
B(τ,s,q₀)² = M(1/5)
```

### Dependency graph

```
┌─────────────────────────────────────┐
│ FiniteFibonacciFusionMatrix         │
│  ├ fibonacciFusionMatrix τ s        │
│  ├ fibonacciRMatrix q               │
│  └ fibonacciBMatrix q τ s          │
├─────────────────────────────────────┤
│ LogCftMonodromy                     │
│  ├ hadjiivanovMonodromy h           │
│  ├ lcftPhase h                      │
│  ├ logShear h                       │
│  └ monodromy_decomposition h        │
├─────────────────────────────────────┤
│ ❌ OPEN: braid_sq_hecke_form        │
│  requires: root-of-unity            │
│  specialization q = exp(iπ/5)       │
└─────────────────────────────────────┘
```

### Why It’s Open

The difficulty is entirely the **specialization step**: the Fibonacci scalars
`τ, s` and the braid parameter `q` are kept generic in the existing
formalization (`FiniteFibonacciFusionMatrix` uses `τ, s : ℂ` and
`q : Units ℂ` without any relation between them).  Closing the debt requires:

(a) constructing the concrete root‑of‑unity `q₀ = exp(iπ/5)` as an
    `Units ℂ` element,
(b) proving the numeric identities `τ²+τ=1` and `s²=τ` for the specific
    golden‑ratio values,
(c) computing `B²` explicitly at those values and matching it to `M(1/5)`.

Step (c) is a finite algebraic computation in ℂ — it can be done by `ring`
and `norm_num` once (a) and (b) are in place.

---

## Problem 2: F‑Matrix Diagononalization of the Hadjiivanov Monodromy

### Context

For generic conformal weight `h` (when `e^{4πih} ≠ 1`), the Hadjiivanov
monodromy `M(h)` is diagonalizable.  The Fibonacci F‑matrix is precisely
the diagonalizing transformation:

```
M(h) = F⁻¹ · diag(e^{2πih}, e^{-2πih}) · F
```

This expresses a deep fact: the F‑matrix, which is the associator of the
Fibonacci fusion category, simultaneously diagonalizes the braiding and
the monodromy.  At resonant values (e.g. `h = 0` where `e^{4πih}=1`),
the diagonalization degenerates and the monodromy becomes a Jordan block —
this is the logarithmic CFT signature.

### Premises

1. **F‑matrix** — a 2×2 complex matrix `F` satisfying

   ```
   F² = I,    det F = −1
   ```

   (In the Fibonacci case `F = F(τ,s)`, but the theorem holds for any
   involutive, determinant‑(−1) `F`.)

2. **Conformal weight** — `h ∈ ℂ` such that `e^{4πih} ≠ 1` (generic case).

3. **Hadjiivanov monodromy** — the matrix `M(h)` defined as in Problem 1.

4. **Diagononal phase matrix**

   ```
   D(h) = diag(e^{2πih}, e^{−2πih})
   ```

### Proposition

Under premises 1–4:

```
F · M(h) · F = D(h)
```

Equivalently, `M(h) = F · D(h) · F` (using `F² = I`).

### Dependency graph

```
┌─────────────────────────────────────┐
│ FiniteFibonacciFusionMatrix         │
│  ├ fibonacciFusionMatrix_sq         │  (F² = I)
│  └ det_fibonacciFusionMatrix        │  (det F = 1 → invertible)
├─────────────────────────────────────┤
│ LogCftMonodromy                     │
│  └ hadjiivanovMonodromy h          │
├─────────────────────────────────────┤
│ ❌ OPEN: monodromy_F_diagonalization│
│  requires: generic condition on h   │
│  and the explicit F‑matrix entries  │
└─────────────────────────────────────┘
```

### Why It’s Open

The computation reduces to a 2×2 matrix conjugation, but the algebra involves
the exponential function `e^{2πih}` which is not algebraically closed in ℂ.
The existing formalization of `lcftPhase h` uses `Complex.exp`; to handle
the generic case one needs:

(a) the identity `logShear h = 2πi · lcftPhase h`,
(b) the matrix product `F · M(h) · F` with `F = F(τ,s)`,
(c) the scalar conditions `τ²+τ=1` and `s²=τ` to cancel the off‑diagonal
    terms, leaving a diagonal matrix `D(h)`.

Step (c) is a 2×2 computation with `τ, s, exp(2πih)` — it can be done by
`ring` and `simp` once the scalar hypotheses are available.

---

## Problem 3: Tensor‑Tower Colimit Sends the Full Twist to the Hadjiivanov Monodromy

### Context

The Fibonacci braid representations fit into a tensor tower:

```
A₁ → A₂ → A₃ → … → A_∞
```

where `A_n = End((ℂ²)^{⊗n})` is the endomorphism algebra of the
`n`‑anyon Hilbert space, and the bonding map `iota_n : A_n → A_{n+1}`
tensors with the identity on the `(n+1)`‑th factor.  The universal
colimit `A_∞` carries the infinite braid group representation.

The full twist `Δ ∈ A₂` (the image of `σ₁² ∈ B₂`) should map under the
colimit cone `psi₂ : A₂ → A_∞` to the Hadjiivanov monodromy operator
acting on the infinite Fock space.

### Premises

1. **Indexed family** — `A : ℕ → Type*` where `A_n` is an `AddCommGroup`
   and `ℂ`‑module (concretely `A_n = End((ℂ²)^{⊗n})`).

2. **Bonding maps** — for each `n : ℕ`, a ℂ‑linear map

   ```
   iota_n : A_n → A_{n+1}
   ```

   satisfying the compatibility `(iota_{n+1})∘(iota_n) = iota_n` for the
   tower.

3. **Colimit cone** — a ℂ‑module `A_∞` and ℂ‑linear maps

   ```
   psi_n : A_n → A_∞
   ```

   satisfying

   ```
   psi_{n+1} ∘ iota_n = psi_n      for all n
   ```

4. **Full twist at stage 2** — an element `Δ ∈ A₂` such that under the
   identification `A₂ ≅ End(ℂ²)`, the matrix `Δ` equals `M(0)`:

   ```
   Δ ≅ ⎡1  2πi⎤
        ⎣0   1 ⎦
   ```

   (the `h=0` resonant case of the Hadjiivanov monodromy).

### Proposition

Under premises 1–4:

```
psi₂(Δ) = psi₂(M(0))   in A_∞
```

where the right‑hand side is `psi₂` applied to the matrix `M(0)` under the
identification `A₂ ≅ End(ℂ²)`.

### Dependency graph

```
┌─────────────────────────────────────┐
│ TensorTowerColimit                  │
│  ├ psi_comp_iota_seq               │
│  └ protected_states_survive_colimit │
├─────────────────────────────────────┤
│ FiniteFibonacciGeneralBraidGenerators│
│  └ fibonacciBlockDimension n       │
├─────────────────────────────────────┤
│ ❌ OPEN: monodromy_as_colimit_of_twist│
│  requires: explicit identification  │
│  A₂ ≅ End(ℂ²) carrying the braid   │
│  generator to fibonacciBMatrix      │
└─────────────────────────────────────┘
```

### Why It’s Open

The colimit infrastructure (`TensorTowerColimit.lean`) is generic —
it works for any `A_n`, `iota_n`, `psi_n`.  Closing this debt requires:

(a) constructing the concrete instance where `A_n = End((ℂ²)^{⊗n})`,
    with `iota_n` being tensoring with `id_{ℂ²}`,
(b) constructing the cone `psi_n` sending the braid generators to the
    explicit Fibonacci matrices,
(c) proving that `psi₂` sends `Δ` (the full twist in `B₂`) to the
    matrix `M(0) = [[1, 2πi], [0, 1]]`.

Step (c) is Problem 1: once we know `B² = M(1/5)` at the root of unity,
and `M(0)` is the `h→0` limit, the colimit statement follows by
functoriality.

---

## Summary

| # | Theorem | Owner file | Key blocker |
|---|---------|-----------|-------------|
| 1 | `braid_sq_hecke_form` | `HadjiivanovMonodromyProjection` | Numeric root‑of‑unity `q₀ = exp(iπ/5)` with explicit golden‑ratio τ |
| 2 | `monodromy_F_diagonalization_generic` | `HadjiivanovMonodromyProjection` | Matrix computation with `Complex.exp`, needing scalar identities τ²+τ=1, s²=τ |
| 3 | `monodromy_as_colimit_of_twist` | `HadjiivanovMonodromyProjection` | Concrete instantiation of `A₂ ≅ End(ℂ²)` carrying the braid representation |

All three are **finite algebraic computations in ℂ** once the scalar
specializations are in place.  No analysis, no infinite‑dimensional
functional analysis, no CFT analytic continuation — only 2×2 matrix
arithmetic with `τ, s, exp(2πih), q`.

## Bilingual translation

The complex language (matrices over ℂ, `Complex.I`) is translated to the
real Hestenes–Krein language via `Canonical/BilingualRealHestenesDictionary`:

| Complex | Real (Krein) | Owner theorem |
|---------|-------------|---------------|
| `i` | `K = J·ε` (`clockAxis`) | `realPhaseAxis_eq_complex_i` |
| `exp(θ·i)` | `R(θ) = exp(θ·K)` (rotor) | `realPhaseAxis_sq` (`K² = −I`) |
| `M(h) ∈ Mat(2,ℂ)` | `M_real(h) ∈ Mat(4,ℝ)` | `hadjiivanovMonodromy_phase_nilpotent` |
| `logShearBase = −2πi` | `−2π·K` | `clockAxis_eq_complex_i` |

The translation is theorem-only: no file duplicates either side.
`Clifford.LogCftMonodromy` owns the complex matrices;
`BilingualRealHestenesDictionary` owns the Krein translation;
`Canonical.HadjiivanovMonodromyProjection` bridges them.

---

*Last updated: 2026-06-02*
