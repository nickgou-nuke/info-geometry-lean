# Geometric Quantization Master Protocol

> ⚠️ **NORMATIVE DEPENDENCY CONTRACT**
> This file is the primary master protocol for extending the Real Hestenes-Krein-Souriau-Duflo framework in this repository. It governs theorem direction, owner boundaries, and prevents speculative overclaims. It is binding on all future Lean subagents and formalizations.

## The Master DAG

The foundational architecture rejects complex numbers as an ontology, instead placing quantization and noncommutative deformation over a real geometric carrier.

```text
I. Real geometric carriers
Cl(p,q),   𝔤, 𝔤*,   𝕆_s
         |
         v
II. Internal geometric operators
I² = -1,      K² = +1,      P_± = ½(1 ± K)
         |
         v
III. Souriau phase/statistical geometry
(T*G, ω),   J,   Θ,   exp(-⟨β, J⟩),   Z, Ψ, C_β
         |
         v
IV. Symmetry layer
G,  W(G₂),   ρ_w,  P_w,   Fisher-Souriau covariance
         |
         v
V. Quantization
Q : Sym(𝔤) → U(𝔤)
         |
         v
VI. Deformation algebra
f ⋆ g = Q⁻¹(Q(f)Q(g))
         |
         v
VII. Noncommutative characters / transforms
E_g(X) = exp_⋆(I k(g) · X)
         |
         v
VIII. Operator/modular layer
Δ,      𝒦 = -log Δ
```

**Exceptional Branch (G₂):**
```text
𝕆_s ⟶ Der(𝕆_s) = 𝔤₂
```
This branch does *not* reduce to a Clifford algebra.

---

## Transform Dictionary

The following identifies the exact geometric origins of functional characters:

*   **Elliptic/Fourier channel:**
    `I² = -1  ⟹  exp(θI) = cos θ + I sin θ`
*   **Hyperbolic/Mellin channel:**
    `K² = +1  ⟹  exp(tK) = e^t P_+ + e^{-t} P_-`
*   **Loxodromic channel:**
    `[I, K] = 0  ⟹  exp(θI + tK) = exp(θI)exp(tK)`
*   **Souriau/Gibbs channel:**
    `exp(-⟨β, J⟩)`

---

## THEOREM-HONEST BOUNDARIES

Do not overclaim. The following boundaries are absolute:

*   `I² = -1` internal structure ≠ automatic replacement of every complex scalar construction
*   `K² = +1` ≠ physical time by itself
*   Cartan Mellin character ≠ full noncommutative G₂ Fourier transform
*   Weyl invariance ≠ Duflo quantization
*   Duflo on invariant polynomials ≠ automatic quantization of Massieu/Fisher functionals
*   star-product ≠ existence of a valid algebra representation unless compatibility is proved
*   Clifford representation of octonionic operators ≠ associative replacement of native split-octonion multiplication
*   projective null geometry ≠ spinorial sign geometry

---

## OWNER MAP

Existing and future modules must strictly align with this map.

*   `DiracHodgeDoubledSpace` ⟶ owns internal I² = -1
*   `FundamentalSymmetryProjectors` ⟶ owns Krein K² = +1 / projectors
*   `SplitQ11Projectors` ⟶ owns split Peirce realization
*   `ChiralGrandCanonicalLoxodromicRotor` ⟶ owns commuting elliptic/hyperbolic rotor calculus
*   `KreinSpace` ⟶ owns indefinite metric/adjoint
*   `CartanSouriau*` ⟶ owns affine moment map, Gibbs, Massieu, Fisher
*   `CanonicalZornG2Cartan*` ⟶ owns G₂ Cartan/Weyl specialization
*   `SplitOctonion*` ⟶ owns genuine nonassociative exceptional geometry
*   *future Duflo owner* ⟶ owns quantization-map / invariant-polynomial bridge
*   *future G₂ noncommutative Fourier owner* ⟶ requires explicit star-product compatibility/existence

---

## Owner Creation Rule

> Нов owner се създава само ако въвежда нов theorem-level edge. Ако само преименува I, K, projector, rotor, Gibbs kernel или existing transform, той е duplicate и не се допуска.
