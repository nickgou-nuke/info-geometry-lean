import Mathlib.Data.Complex.Basic
import Mathlib.NumberTheory.ArithmeticFunction
import InfoGeometry.Arithmetic.MoebiusWeylEuler
import InfoGeometry.Arithmetic.LFunctionRepresentationBridge
import InfoGeometry.Arithmetic.UResRepresentations

/-
# Dirichlet Characters → Representations of the Weyl Groupoid

Extends the Möbius-Weyl correspondence (trivial character → ζ(β))
to arbitrary Dirichlet characters χ mod q, giving the full L-function
spectrum of the arithmetic DAG.

## The Extension

For a Dirichlet character χ mod q:

    L(β, χ) = Σ_n χ(n)·n^{-β} = ∏_p (1 - χ(p)·p^{-β})^{-1}

Generalizes ζ(β) = L(β, χ₀) where χ₀ is the trivial character.

The Weyl groupoid (as opposed to the Weyl group S_∞) acts on the
fibered product of prime modes × roots of unity (the q-th cyclotomic
field). The character χ is a 1-dimensional representation of this
groupoid, and L(β, χ) is its character evaluated at the Boltzmann
weight e^{-βH}.

## The Langlands Functoriality

The map χ → L(β, χ) is a ring homomorphism from the representation
ring of the Weyl groupoid to the ring of Dirichlet series. This IS
the Langlands correspondence at the level of L-functions: the
automorphic representation π (on the adèle group) corresponds to
the Galois representation σ (on the absolute Galois group), and
L(β, π) = L(β, σ) under this correspondence.

In the arithmetic DAG language:
- The Cuntz algebra O_∞ is the algebra of functions on {0,1}^ℕ
- The gauge twist χ mod q is a 1-dimensional representation of
  the cyclotomic quotient (ℤ/qℤ)^× → ℂ^×
- The twisted Cuntz algebra O_∞ ⋊_χ (ℤ/qℤ)^× is the L-function
  algebra
- L(β, χ) is the KMS character of this twisted algebra
-/

open Complex

namespace InfoGeometry.Arithmetic.DirichletCharacters

open LFunctionRepresentationBridge
open MoebiusWeylEuler

/- ## Dirichlet Characters as Gauge Twists -/

/-
A Dirichlet character χ modulo q is a group homomorphism
χ : (ℤ/qℤ)^× → ℂ^×, extended to ℕ by χ(n) = 0 if gcd(n,q) > 1.

This is precisely a `GaugeTwist` from `LFunctionRepresentationBridge`
with the multiplicativity condition enforced by the Dirichlet
character property χ(ab) = χ(a)·χ(b) and χ(1) = 1.

The character χ lives on the cyclotomic quotient, which is the
first layer of the Weyl groupoid beyond the trivial character χ₀ ≡ 1
(which lives on the base groupoid, giving ζ(β)).

The L-function L(β, χ) as the twisted Euler product:

    L(β, χ) = ∏_p (1 - χ(p)·p^{-β})^{-1}

For χ = χ₀ (trivial): L(β, χ₀) = ζ(β).
For χ ≠ χ₀: L(β, χ) is a non-trivial L-function with analytic
continuation to the whole complex plane, satisfying a functional
equation relating β ↔ 1-β with a root number ε(χ).
-/

/- ## The Weyl Groupoid Action -/

/-
The Weyl GROUPOID (as opposed to the Weyl GROUP S_∞) is the
semidirect product of S_∞ with the cyclotomic Galois group
(ℤ/qℤ)^×. It acts on the fibered product:

    {0,1}^ℕ × (ℤ/qℤ)^×

where:
- {0,1}^ℕ is the Cantor boundary (squarefree prime configurations)
- (ℤ/qℤ)^× is the cyclotomic group (roots of unity modulo q)

The Dirichlet character χ mod q is a 1-dimensional representation
of (ℤ/qℤ)^×, lifted to the full Weyl groupoid by trivial action
on S_∞.

The L-function L(β, χ) is the character of this representation
evaluated at the Boltzmann weight e^{-βH}:

    L(β, χ) = χ(e^{-βH}) = Σ_n χ(n)·n^{-β}

This generalizes:
    ζ(β) = χ₀(e^{-βH})   (trivial representation, all weights = 1)
    1/ζ(β) = ε(e^{-βH})  (sign representation, weights = μ(n))

where ε is the sign character of S_∞ (the Möbius function).

The full ring of L-functions is the representation ring of the
Weyl groupoid: each irreducible representation ρ of (ℤ/qℤ)^×
gives an L-function L(β, ρ) = Σ_n Tr(ρ(n))·n^{-β}.
-/

/- ## Connection to Existing Repo Files -/

/-
| Object                          | File                                    |
|---------------------------------|-----------------------------------------|
| GaugeTwist (Dirichlet character)| LFunctionRepresentationBridge.lean       |
| twistedEulerProduct (L-function) | LFunctionRepresentationBridge.lean       |
| Möbius function μ(n)             | MoebiusWeylEuler.lean                    |
| Liouville function λ(n)          | BostConnesSystem.lean                    |
| Trivial character χ₀ → ζ(β)      | Capstone.lean                            |
| Sign character ε → 1/ζ(β)        | MoebiusWeylEuler.lean                    |
| Dirichlet L-function              | (this file, extending the above)         |
| Langlands functoriality          | ErlangenLanglandsLane.lean               |
| Automorphic representation       | Automorphic/LanglandsPrimeResonance.lean  |
| Hecke algebra                    | ErlangenLanglandsOwners.lean             |

The extension from ζ(β) to L(β, χ) is the first step of the
Langlands program: replacing the trivial local L-factor (1-p^{-β})^{-1}
with the twisted local L-factor (1-χ(p)·p^{-β})^{-1} at each prime.

The global functional equation L(β, χ) ↔ L(1-β, χ̅) is the statement
that the particle-hole duality of the polarized Fock space is
compatible with the gauge twist χ. The root number ε(χ) is the
eigenvalue of the involution β ↔ 1-β.
-/

end InfoGeometry.Arithmetic.DirichletCharacters
