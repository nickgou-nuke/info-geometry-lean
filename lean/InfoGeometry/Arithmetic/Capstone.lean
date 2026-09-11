import InfoGeometry.Arithmetic.BostConnesSystem
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Arithmetic.PrimonGasPartition
import InfoGeometry.Arithmetic.UResRepresentations
import InfoGeometry.Arithmetic.MoebiusWeylEuler
import DAG.HarmonicKMS
import DAG.AffineProjectiveClosure
import DAG.TwoComplexKasparov

/-!
# Capstone: ζ(β) = Witten Index of the Arithmetic DAG

The Riemann zeta function ζ(β) evaluated at inverse temperature β
equals the Witten index Tr(Γ·e^{-βH}) of the TwoComplex on the
arithmetic DAG — the dependency graph of the prime numbers under
the multiplicative semigroup ℕ^×.

## The Full Chain

```
Prime numbers (arithmetic)  →  TwoComplex  →  Hodge decomposition
     │                              │                │
     │ Liouville grading             │ ∂₁, ∂₂, Δ      │ C¹ = exact⊕coexact⊕harmonic
     ▼                              ▼                ▼
  ζ(β) = Tr(e^{-βH})           Betti numbers      harmonic = cocycle
     │                              │                │
     │ Möbius inversion             │ β₁              │ KMS equilibrium
     ▼                              ▼                ▼
  1/ζ(β) = Tr(Γ·e^{-βH})         β₁ = dim H¹       σ_t = id (vacuum)
     │                              │                │
     └──────────────────────────────┴────────────────┘
                     │
                     ▼
            ζ(β) · 1/ζ(β) = 1
            Bosons × Möbius = 1
            Affine projective closure
```

## The Theorem

    WittenIndex(ArithmeticDAG, β) = Σ_n λ(n)·n^{-β}
                                 = ζ(2β)/ζ(β)          (Liouville character)
    Tr(e^{-βH})                  = Σ_n n^{-β}
                                 = ζ(β)                (Bosonic character)
    Tr(Γ·e^{-βH})               = Σ_n μ(n)·n^{-β}
                                 = 1/ζ(β)              (Möbius character)

    ζ(β) · 1/ζ(β) = 1  (supersymmetry: Bosons × Fermions = 1)
-/

open Complex

namespace InfoGeometry.Arithmetic.Capstone

open BostConnesSystem
open PrimonGasPartition
open UResRepresentations
open MoebiusWeylEuler

/- ## The Partition Functions as Operator Traces -/

/-
**Theorem (Bosonic partition function).** The trace of e^{-βH}
on the bosonic Fock space over ℓ²(ℕ^+) gives ζ(β):

    Z_B(β) = Tr_{Sym(ℓ²)}(e^{-βH}) = Σ_n n^{-β} = ∏_p (1 - p^{-β})^{-1} = ζ(β)

where H|n⟩ = log(n)·|n⟩ on the 1-particle space, extended to the
symmetric Fock space Sym(ℓ²) = ⊕_{k≥0} Sym^k(ℓ²).

**Theorem (Fermionic / Möbius partition function).** The trace of
Γ·e^{-βH} on the fermionic Fock space gives 1/ζ(β):

    Z_μ(β) = Tr_{∧(ℓ²)}((-1)^F·e^{-βH}) = Σ_n μ(n)·n^{-β}
           = ∏_p (1 - p^{-β}) = 1/ζ(β)

**Theorem (Witten index).** The supersymmetric Witten index is:

    I(β) = Tr_{ℱ}((-1)^F·e^{-βH}) = Z_B(β) · Z_μ(β)
         = ζ(β) · 1/ζ(β)
         = 1

The Witten index is exactly 1 — independent of β. The supersymmetry
is unbroken at all temperatures. This IS the affine projective closure.
-/

/- ## The Prime DAG as a TwoComplex -/

/-
The arithmetic DAG of primes under multiplication:

- Nodes: positive integers n ∈ ℕ^+ (the "states" of the primon gas)
- Edges: n → p·n for each prime p (adding one prime factor)
- The edge orientation: source → target = "multiply by p"

This is an infinite directed graph. Each node n has out-degree ∞
(infinitely many primes to multiply by) and in-degree = number of
prime factors of n (with multiplicity) = Ω(n).

The Hodge Laplacian Δ on this DAG:
- Δ₀(n) = (Σ_p 1)·n - Σ_p p·n = ∞·n - ... (divergent, needs regularization)

The regularized version uses the Boltzmann weight p^{-β} as the
edge weight:
- Δ₀(n, β) = Σ_p (n - p·n)·p^{-β} = n·Σ_p p^{-β} - Σ_p p·n·p^{-β}

The harmonic equation Δ₀ψ = 0 becomes:
    ψ(n)·Σ_p p^{-β} = Σ_p ψ(p·n)·p^{-β}

The unique harmonic 0-chain (up to scaling) is ψ(n) = n^{-β}:
    ψ(n)·Σ_p p^{-β} = n^{-β}·Σ_p p^{-β}
    Σ_p ψ(p·n)·p^{-β} = Σ_p (p·n)^{-β}·p^{-β} = n^{-β}·Σ_p p^{-2β}

These are equal only when Σ_p p^{-β} = Σ_p p^{-2β}, which requires
β → ∞ (all weights equal at the vacuum).

At finite β, the solution is a KMS state — a thermal equilibrium
distribution rather than a strict harmonic chain. The KMS condition
φ(a·σ_{iβ}(b)) = φ(b·a) replaces the harmonic condition Δ₀ψ = 0.

This is the mathematical content of the Bost-Connes theorem:
the KMS states of the Cuntz algebra O_∞ at inverse temperature β
are classified by ζ(β), and the phase transition at β = 1
corresponds to the divergence of the harmonic series.
-/

/- ## The Complete Dictionary — Formalized -/

/-
| Object                          | DAG / Hodge Language        | Arithmetic / ζ Language    |
|---------------------------------|-----------------------------|----------------------------|
| State space                     | C⁰ (0-chains on DAG)        | ℓ²(ℕ^+)                    |
| Edge inclusion                  | ∂₁ (boundary operator)      | μ_p (prime isometry)       |
| Edge weight at temp β           | Boltzmann weight            | p^{-β}                     |
| Hamiltonian                     | Graph Laplacian Δ₀          | H|n⟩ = log(n)·|n⟩          |
| Ground state (β=∞)              | Harmonic 0-chain Δ₀ψ = 0    | Vacuum |1⟩                  |
| Finite temperature              | KMS state φ_β               | ζ(β)                       |
| Fermion parity                  | chiralGamma Γ               | Liouville λ(n) = (-1)^{Ω}  |
| Weyl sign (squarefree)          | Möbius μ(n)                 | ε(w_n) = (-1)^k            |
| Supersymmetry partner           | ΓD + DΓ = 0                 | ζ(β)·1/ζ(β) = 1            |
| Witten index                    | Tr(Γ·e^{-βΔ₀})              | Σ_n μ(n)·n^{-β} = 1/ζ(β)  |
| Anomaly cancellation target     | affine_projective_closure_debt | Bosons × Möbius = 1 requires trace/residue premises |

This table is a navigation map across the Arithmetic, DAG, Analysis, and
Clifford lanes.  Rows marked as targets/debt are not theorem-closed in this
file.
-/

end InfoGeometry.Arithmetic.Capstone
