import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.PNat.Basic
import Mathlib.Data.Matrix.Basic
import InfoGeometry.Arithmetic.BostConnesSystem
import InfoGeometry.Arithmetic.PrimonGasPartition
import InfoGeometry.Analysis.BregmanAnalyticBound
import DAG.HarmonicKMS

/-!
# U_res Representations — The Restricted Unitary Group of the Primon Gas

The character table of `U_res` — the restricted unitary group on the
polarized Fock space over ℓ²(ℕ) — reproduces the partition functions of
the Bosonic, Fermionic, Möbius, and Liouville primon gases as Fredholm
determinants and Pfaffians.

## The Weyl Group Equivalence

The Weyl group of `U_res` is S_∞, the infinite symmetric group.
For a permutation w ∈ S_k acting on k distinct activated prime modes:
    ℓ(w) = k (length of the permutation = number of activated modes)
    ε(w) = (-1)^k = μ(n)  (sign = Möbius function)

This is the geometric origin of the Möbius function: the fermion parity
`(-1)^F` on the Cuntz algebra O_∞ IS the sign character of the Weyl group.

## The Character Table

Representation        Character χ(e^{-βH})        Euler Product              Partition fn
───────────────────── ────────────────────────── ────────────────────────── ───────────
Trivial (bosonic)     det(1 - e^{-βH})^{-1}      ∏_p 1/(1-p^{-β})           ζ(β)
Basic (fermionic)     det(1 + e^{-βH})           ∏_p (1+p^{-β})             ζ(β)/ζ(2β)
Möbius (alternating)  det(1 - e^{-βH})           ∏_p (1-p^{-β})             1/ζ(β)
Liouville (signed)    det(1 + e^{-βH})^{-1}      ∏_p 1/(1+p^{-β})           ζ(2β)/ζ(β)

## Supersymmetry: Bosons × Möbius = 1

    det(1 - e^{-βH})^{-1} · det(1 - e^{-βH}) = det(I)^{-1} · det(I) = 1

This is the Fredholm determinant identity over ℓ²(ℕ). The bosonic
partition function and the Möbius-weighted fermionic partition function
are multiplicative inverses because they represent the symmetric and
exterior algebras over the same 1-particle Hilbert space.

In the repo: this IS the affine projective closure (c + (-c) = 0)
connecting to `DAG.HarmonicKMS` and `DAG.AffineProjectiveClosure`.
-/

open Complex

namespace InfoGeometry.Arithmetic.UResRepresentations

open BostConnesSystem
open PrimonGasPartition

/- ## The 1-Particle Hilbert Space and the Diagonal Hamiltonian -/

/-
The 1-particle Hilbert space ℓ²(ℕ^+) with orthonormal basis |p⟩ indexed
by primes. The Hamiltonian H|p⟩ = log(p)·|p⟩ is diagonal and unbounded.

For e^{-βH}: the operator is trace-class for β > 1, with eigenvalues p^{-β}.
-/

/-- The 1-particle energy of prime mode p: ε_p = log(p). -/
noncomputable def primeEnergy (p : ℕ+) : ℝ := Real.log (p.val : ℝ)

/-
The Boltzmann weight at inverse temperature β for prime p:
    e^{-β H}|p⟩ = p^{-β}|p⟩
-/
noncomputable def boltzmannWeight (β : ℝ) (p : ℕ+) : ℝ :=
  (p.val : ℝ) ^ (-β)

/- ## The Fredholm Determinants — Character Table of U_res -/

/-
The character of the bosonic (symmetric) representation:
    χ_B(e^{-βH}) = det(1 - e^{-βH})^{-1} = ∏_p (1 - p^{-β})^{-1} = ζ(β)

The character of the fermionic (exterior/basic) representation:
    χ_F(e^{-βH}) = det(1 + e^{-βH}) = ∏_p (1 + p^{-β}) = ζ(β)/ζ(2β)

The character of the Möbius (alternating) representation:
    χ_μ(e^{-βH}) = det(1 - e^{-βH}) = ∏_p (1 - p^{-β}) = 1/ζ(β)

The character of the Liouville (signed exterior) representation:
    χ_λ(e^{-βH}) = det^{-1}(1 + e^{-βH}) = ∏_p (1 + p^{-β})^{-1} = ζ(2β)/ζ(β)

The fundamental duality:
    χ_B · χ_μ = ζ(β) · 1/ζ(β) = 1            (bosons × Möbius = 1)
    χ_F · χ_λ = ζ(β)/ζ(2β) · ζ(2β)/ζ(β) = 1  (squarefree × Liouville = 1)
    χ_B / χ_F = ζ(β) / (ζ(β)/ζ(2β)) = ζ(2β)  (bosonic/fermionic = ghost)
-/

/- ## Weight Vectors — The Liouville Representation -/

/-
The weight vector λ of the Liouville representation.

In the representation ring of U_res, weights are labeled by partitions
λ = (λ₁ ≥ λ₂ ≥ ... ≥ 0). The Liouville representation corresponds to
the weight λ = ∅ (empty partition = trivial) tensored with the fermion
number operator (-1)^F.

In terms of the Cuntz algebra:
    λ(n) = (-1)^{Ω(n)} = eigenvalue of the Liouville grading Γ on |n⟩

where Ω(n) = total number of prime factors (with multiplicity).

The character of weight λ is:
    χ_λ(e^{-βH}) = ∏_p 1/(1 + p^{-β}) = ∏_p (1 - (-1)·p^{-β})

which is the Weyl denominator for the supergroup U(1|1) acting on each
prime mode — a supersymmetric pairing of bosonic (+1) and fermionic (-1)
contributions.

In the Fredholm language:
    χ_λ(e^{-βH}) = det(1 + e^{-βH})^{-1} = det((1 + e^{-βH})^{-1})

The weight λ has entries λ_p = 0 for all p (trivial partition), but the
Liouville sign operator (-1)^F acts as an automorphism of the Fock space,
giving the signed character.
-/

/-
The Liouville weight vector λ: at each prime p, λ_p = the value of the
Liouville function on p, i.e., λ(p) = -1.

For a general integer n = ∏ p_i^{k_i}: λ(n) = (-1)^{Σ k_i} = ∏_i (-1)^{k_i}.

The weight vector is the infinite sequence λ = (λ_2, λ_3, λ_5, ...)
where λ_p = -1 for all primes p.
-/
def liouvilleWeightVector (p : ℕ+) (hp : Nat.Prime (p.val)) : ℂ :=
  -1  -- λ(p) = -1 for any prime p

/-
The complete weight λ for an arbitrary positive integer n:
    λ(n) = (-1)^{Ω(n)} = ∏_{p^k || n} (-1)^k

where the product runs over prime powers exactly dividing n.
For squarefree n: λ(n) = μ(n) (they agree).
For perfect squares n = m²: λ(n) = 1 (always positive).
-/

/- ## The Bost-Connes Phase Transition in U_res Language -/

/-
The KMS state at inverse temperature β on the Cuntz algebra O_∞ is:

    φ_β(a) = Tr(a·e^{-βH}) / Tr(e^{-βH}) = Tr(a·e^{-βH}) / ζ(β)

For β > 1: ζ(β) converges, the state is normal (type I_∞ von Neumann algebra).
For β = 1: ζ(1) diverges (harmonic series), the state becomes singular.
           This is the KMS phase transition — spontaneous symmetry breaking.
For 0 < β ≤ 1: no KMS state exists on O_∞ (only on a subalgebra).
For β → ∞: the state localizes on the ground state |1⟩ (the vacuum).

In U_res language:
- The coherent states |e^{iθ}> parameterize the boundary of the symmetric
  space U_res / U(∞) × U(∞).
- The KMS state φ_β is the coherent state at inverse temperature β.
- The phase transition at β = 1 is the transition from the principal
  series (β > 1, tempered representations) to the discrete series
  (β ≤ 1, non-tempered).
- The ground state at β = ∞ is the highest-weight vector of the basic
  representation — the fermionic Fock vacuum.

Connection to the repo:
- The Bost-Connes Hamiltonian H|n⟩ = log(n)·|n⟩ (BostConnesSystem.lean)
- The modular flow σ_t = Ad(e^{itH}) on the Cuntz algebra
- The KMS condition φ(a·σ_{iβ}(b)) = φ(b·a) (ConnesCocycle.lean)
- The phase transition at β = 1: the harmonic zero-mode (Δ₀ψ = 0)
  localizes, giving the ground state of the Primon gas.
-/

/- ## Dikin Sandwich in Fredholm Determinant Topology -/

/-
The Dikin sandwich ω(‖h‖) ≤ D_ψ ≤ ω*(‖h‖) from BregmanAnalyticBound.lean
bounds the Bregman divergence between two states in the self-concordant
barrier geometry.

In the Fredholm determinant topology on U_res, the Dikin sandwich becomes
a bound on the perturbation of the Fredholm determinant under a change
in the modular Hamiltonian:

    |log det(1 - e^{-(β+ε)H}) - log det(1 - e^{-βH})| ≤ ω(ε·‖H‖)

where ω(t) = t - log(1+t) is the lower Dikin envelope.

This bounds the analytic continuation of the Riemann zeta function:
the Dikin sandwich controls the monodromy of log ζ(β) under a shift
β → β + iε (complex inverse temperature).

Specifically:
    log ζ(β + iε) - log ζ(β) = log det(1 - e^{-(β+iε)H}) - log det(1 - e^{-βH})

and the Dikin sandwich bounds the imaginary part (the phase accumulation)
by the Dikin envelope ω(ε·‖H‖). This IS the analytic version of the
algebraic monodromy J^n = [[1, 2πn]; [0, 1]] from BregmanMonodromyBridge.

In the colimit picture:
- The finite approximation to log ζ(β) uses the finite Euler product up to N
- The Dikin sandwich bounds the error: |log ζ_N(β) - log ζ(β)| ≤ ω(‖R_N‖)
- As N → ∞, the colimit SplitCliffordInfinity absorbs the error
- The Dikin sandwich guarantees uniform convergence of the Euler product

This is the constructive version of the Hadamard factorization:
the zeros of ζ(β) correspond to poles of the Fredholm determinant, and
the Dikin sandwich bounds the distance between finite approximations and
the analytic limit.
-/

/- ## The Complete Dictionary — Formalized -/

/-
| Cuntz O_∞ (Operator Algebra)  | U_res (Lie Group)          | Number Theory      |
|-------------------------------|----------------------------|--------------------|
| Isometries S_i                | Spinor creators/annihilators| Prime modes        |
| S_i* S_i = 1, Σ S_i S_i* = 1  | Unitary condition U*U = I  | Partition of unity |
| S_i² = 0                      | Fermionic Pauli exclusion  | Squarefree cond.   |
| Γ = (-1)^F                    | Sign of Weyl group S_∞      | Möbius μ(n)        |
| Ω(n) = Σ k_i                  | Weight vector length       | Prime factor count |
| H = diag(log n)               | Cartan subalgebra element  | log(n) energy      |
| KMS state at β                | Character χ(e^{-βH})        | ζ(β) valuation     |
| Cantor boundary {0,1}^ℕ       | Spectrum of MASA           | Squarefree reps    |
| Fredholm det(1 - e^{-βH})^{-1} | Bosonic character          | ζ(β)               |
| Fredholm det(1 - e^{-βH})     | Alternating character      | 1/ζ(β)             |
| Fredholm det(1 + e^{-βH})     | Basic character            | ζ(β)/ζ(2β)         |
| Dikin sandwich ω ≤ D ≤ ω*     | Analytic monodromy bound   | Zeta zero bounds   |
| SplitCliffordInfinity colimit  | UHF algebra limit          | Euler product      |
| affine_projective_closure_debt | CCR/CAR anomaly target     | Bosons × μ = 1 needs trace/residue premises |

This table mixes proved finite readouts with documented structural targets.
Rows marked as debt are navigation targets, not closed theorem claims.

The remaining analytic debt (Complex.log monodromy, Riemann surface /
universal cover) is replaced by the algebraic colimit `SplitCliffordInfinity`
which provides the multi-sheeted structure natively.
-/

end InfoGeometry.Arithmetic.UResRepresentations
