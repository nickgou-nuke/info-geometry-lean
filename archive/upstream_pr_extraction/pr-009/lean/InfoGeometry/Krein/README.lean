/-!
# InfoGeometry.Krein — Greenfield Categorical Foundation (Mathlib 4.28.0)

This folder is a **greenfield** foundation: the core structures are defined using **Mathlib 4.28.0**
typeclasses only, with no dependency on legacy `InfoGeometry` definitions.

## Layer stack (canonical intent)

Layer 5: KK-theory / Kasparov products
Layer 4: Clifford modules with indefinite metric
Layer 3: Krein spaces (this layer)
Layer 2: Hilbert carriers / doubled spaces / projectivization
Layer 1: Measure theory + Radon–Nikodym potentials

## Layer 3: KreinSpace (single source of truth)

A real Krein space is a real Hilbert space `(H, ⟪·,·⟫)` equipped with a **fundamental symmetry**
`J : H ≃ₗᵢ[ℝ] H` such that:
- involution: `J (J x) = x`
- self-adjointness: `⟪J u, v⟫ = ⟪u, J v⟫`

The Krein inner product is:
`[u, v]_J := ⟪J u, v⟫`.

Derived API (must be centralized in `KreinSpace.lean`):
- `kreinInner`, `kreinAdjoint A := J ∘ A† ∘ J`
- `IsKreinSelfAdjoint`, `IsKreinSkewAdjoint`, `IsKreinIsometry`
- `Star (H →L[ℝ] H)` via `kreinAdjoint`
- Lie interaction lemmas (`kreinAdjoint_lie`, `kreinAdjoint_lie_neg`, closure of skew-adjoints)

## Two distinct canonical models (do not conflate)

There are **two** fundamental symmetries used in the project, and they define **different Krein spaces**:

1) Diagonal Pontryagin model (signature (n,n)):
- carrier: `WithLp 2 (E × E)`
- symmetry: `J_diag(x,y) = (x, -y)`
- Krein form: `⟪x₁,y₁⟫ - ⟪x₂,y₂⟫`

2) Neutral Hessian/Bogoliubov model (cross-term):
- carrier: `NeutralSpace E` (a newtype wrapper over `WithLp 2 (E × E)`)
- symmetry: `J_neut(x,y) = (y, x)`
- Krein form: `⟪x₁,y₂⟫ + ⟪x₂,y₁⟫`

These are not definitionally equal, and must not share a single `KreinSpace` instance.
Newtype isolation is required to prevent instance resonance.

## Canonical equivalence between models (implemented bridge)

The diagonal and neutral forms are congruent via the 45° rotation:

`P(x,y) := ( (x+y)/√2 , (x-y)/√2 )`.

This is implemented as `NeutralSpace.rotation45KreinEquiv` in `HilbertBridge.lean`,
as a `KreinEquiv` from the neutral model to the diagonal model preserving `kreinInner`.
This is the mathematically correct bridge between the Hessian/Bogoliubov pairing and
the diagonal `(n,n)` Krein model.

## Layer 4 status (Clifford modules)

Phase-5 core lives in `Clifford.lean`:
- `KreinGradedModule` (grading involution `Γ`)
- `SymmetricCliffordModule` (Clifford action compatible with grading and Krein adjoint)
- concrete `Cl(1,1)` representation on `HilbertDoubled E`
- transported neutral grading and conjugated neutral Clifford action via `rotation45`

## Category layer

A category `Krein` is provided where:
- objects are bundled `(H, J)` with `[KreinSpace H]`
- morphisms are continuous linear maps preserving `kreinInner` (i.e. `KreinHom`)

This category is the correct home for later Clifford-module and KK-theory layers.

-/

namespace InfoGeometry.Krein
end InfoGeometry.Krein
