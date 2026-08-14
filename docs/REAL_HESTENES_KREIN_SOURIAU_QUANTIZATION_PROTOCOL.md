# Real Hestenes–Krein–Souriau Quantization Protocol

## Purpose

This document is a normative dependency contract for future Lean owners and
proof agents. It records ownership, dependency direction, and theorem-honest
boundaries for the real geometric, Souriau, Weyl, quantization, and transform
layers.

It is not a claim that all layers below are already formalized.

## Architectural dependency direction

```text
I.   Real geometric carriers
     Cl(p,q), Lie algebras and duals, split octonions
       ↓
II.  Internal geometric operators
     I² = -1, K² = +1, P± = (1 ± K)/2
       ↓
III. Souriau phase/statistical geometry
     T*G, symplectic/Poisson data, J, Θ, Gibbs, Z, Ψ, Cβ
       ↓
IV.  Symmetry layer
     G, G₂ Weyl actions, charge/parameter transport, Fisher covariance
       ↓
V.   Quantization
     Q : Sym(g) → U(g)
       ↓
VI.  Deformation algebra
     f ⋆ g = Q⁻¹(Q(f) Q(g))
       ↓
VII. Noncommutative characters and transforms
     E_g(X) = exp⋆(I · k(g) · X)
       ↓
VIII.Operator/modular layer
     Δ, 𝒦 = -log Δ
```

The exceptional side branch is separate:

```text
Oₛ → Der(Oₛ) = 𝔤₂
```

Native split-octonion multiplication and its associator are not replaced by
an associative Clifford multiplication.

## Real internalization rule

The safe statement is not that every complex construction is merely notation.
The valid representation-level statement is:

> In a chosen real representation, an external complex phase may be
> internalized by an operator `I` satisfying `I² = -1`, provided the required
> commutation, centrality, and intertwining properties are proved.

This is a conditional bridge, not a universal identification of complex
Hilbert-space structures with one Clifford blade.

## Transform dictionary

```text
I² = -1
  ⇒ elliptic/Fourier rotor:      cos θ + I sin θ

K² = +1
  ⇒ hyperbolic/Mellin rotor:     cosh t + K sinh t
                                  = exp(t) P+ + exp(-t) P-

[I,K] = 0
  ⇒ loxodromic factorization:    exp(θ I + t K)
                                  = exp(θ I) exp(t K)

exp(-⟨β,J⟩)
  ⇒ Souriau/Gibbs character
```

The commuting mixed formula is conditional on `[I,K] = 0`. Concrete
Hestenes generators that anticommute must not be silently treated as commuting
ones; the commuting loxodromic rotor is a separate owner.

## Mixed-generator regime split

The protocol distinguishes two different mixed planes:

```text
[I,K] = 0
  ⇒ exp(θ I + η K) = exp(θ I) exp(η K)
     commuting loxodromic channel

{I,H} = 0,  I² = -1, H² = +1
  ⇒ A = θ I + η H
     A² = (η² - θ²) 1
     anticommuting Clifford channel
```

The second line is a real `Cl(1,1)`-type coefficient plane, not a
bicomplex scalar factorization. Its algebraic regimes are classified by
`q(η, θ) = η² - θ²`: positive, zero, and negative give hyperbolic, null, and
elliptic square type respectively. The square identity and this trichotomy
are kernel-checked in `HestenesKreinSouriauCompatibility.lean`.

The corresponding formulas for the operator exponential remain separate
theorem targets. They must not be imported from an unproved generic
exponential scaffold or conflated with the commuting factorization.

## Quadratic Lie-generator and affine-Souriau dictionary

When a concrete generator satisfies

```text
A² = q · 1
```

the sign of `q` is the algebraic regime classifier:

```text
q > 0  → hyperbolic/split
q = 0  → parabolic/null
q < 0  → elliptic/compact
```

This is the finite real-algebra shadow of the corresponding Lorentzian
quadratic form on a Lie-algebra plane. It is independent of any claim that
the exponential has already been evaluated in Lean.

The affine Souriau route is a separate, compatible corridor:

```text
J(gx) = ρg J(x) + Θ(g)
Θ(gh) = Θ(g) + ρg Θ(h)
        ↓
exp(-⟨J(x), β⟩)
        ↓
Z(β), Ψ(β) = log Z(β)
        ↓
D²Ψ = covariance/Fisher form
```

The charge action, contragredient parameter transport, and left parameter
action remain distinct interfaces. A generalized Casimir entropy condition
may be a valid affine-coadjoint invariant without being a polynomial element
of `Sym(g)`. Therefore it is not, by itself, a Duflo input.

## Parabolic representation boundary

The rank-two Mellin character has a representation-theoretic readout on a
split Cartan factor `A = exp(a₀)`:

```text
χs(t) = exp(-⟨s,t⟩) = χν(exp t),   ν = -s
```

The theorem-safe extension is a parameter interface, not a full nonabelian
Fourier transform:

```text
χs on A
  → πM ⊠ χν on MA
  → parabolic induction iPᴳ(πM ⊠ χν)
```

Generic irreducibility, integral-root hyperplanes, Weyl walls, Cayley
transforms, and KLV algorithms are separate representation-theoretic owners.
In particular, generic irreducibility hyperplanes must not be identified
automatically with ordinary Weyl reflection walls.

The quantization/readout corridor is likewise staged:

```text
Sym(g)^G → Z(U(g)) → Harish–Chandra infinitesimal character → ℂ
```

The Duflo map creates the central observable; the infinitesimal character
evaluates it. Neither construction follows automatically from a Massieu
potential, a Fisher functional, or a Clifford/Hestenes generator.

## Souriau and quantization boundary

The exact standard Duflo statement is the invariant-polynomial bridge:

```text
Sym(g)^g  ──D──→  Z(U(g))
```

It does not automatically send a Massieu potential or Fisher functional to a
central element. Since `Ψ = log Z` and `D²Ψ = Cβ` need not be polynomial
elements of `Sym(g)`, that identification requires a separate theorem for
specific invariant polynomials, Casimirs, or an explicitly defined completed
functional calculus.

Likewise, a quantization map does not by itself prove existence of a valid
star-algebra representation. Coordinate, coproduct, product, and
representation compatibility must be supplied and kernel-checked.

## Theorem-honest boundaries

```text
I² = -1 internal structure
  ≠ automatic replacement of every complex scalar construction

K² = +1
  ≠ physical time by itself

Cartan Mellin character
  ≠ full noncommutative G₂ Fourier transform

Weyl invariance
  ≠ Duflo quantization

Duflo on invariant polynomials
  ≠ automatic quantization of Massieu/Fisher functionals

star-product
  ≠ existence of a valid algebra representation without compatibility proof

Clifford representation of octonionic operators
  ≠ associative replacement of native split-octonion multiplication

projective null geometry
  ≠ spinorial sign geometry
```

## Current owner map

```text
DiracHodgeDoubledSpace
    internal doubled involutions and I² = -1

FundamentalSymmetryProjectors
    Krein involution/projectors

SplitQ11Projectors
    split Peirce realization

ChiralGrandCanonicalLoxodromicRotor
    concrete elliptic/hyperbolic rotor calculus

KreinSpace
    indefinite metric and adjoint structure

CartanSouriau*
    affine moment maps, Gibbs kernels, Massieu, Fisher geometry

CanonicalZornG2Cartan*
    concrete G₂ Cartan and Weyl specialization

SplitOctonion*
    native nonassociative exceptional geometry

future Duflo owner
    quantization-map and invariant-polynomial bridge

future G₂ noncommutative Fourier owner
    explicit star-product compatibility and existence
```

## Owner creation rule

Create a new owner only when it introduces a new kernel-checkable theorem-level
edge. A file that merely renames or redefines an existing `I`, `K`, projector,
rotor, Gibbs kernel, or transform is a duplicate and must not be created.

Every future owner must state its upstream owner, its new theorem surface, and
the claims it deliberately does not make.
