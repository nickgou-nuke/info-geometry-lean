# Cuntz-Cantor Boundary Shift API

> Status: `live API overview`
> Audited: 2026-06-10
> Owner module: `lean/InfoGeometry/Canonical/CuntzCantorBoundaryShift.lean`
> Operator bridge: `lean/InfoGeometry/Canonical/CantorBoundaryCuntzShift.lean`
> Boundary: finite Cantor prefix-shift algebra only. This is not a full Cuntz
> `O₂` representation, Hilbert-space partial-isometry theorem, KMS state, or
> zeta/RH theorem.

This module is the finite action layer over the existing diagonal-UHF Cantor
cylinder skeleton in `UHFInductiveColimitBoundary.lean`.

The companion `CantorBoundaryCuntzShift.lean` attaches the same boundary branch
conventions to the existing abstract `CuntzO2Carrier`, reuses
`CantorCuntzBasisPacket.orbit`, and exposes the already-owned `carFromCuntz`
CAR readouts. It is still finite/operator-algebraic: topology and KMS structure
remain later proof-carrying context.

## Core Objects

```lean
def prependBit (b : Bool) (x : CantorBoundary) : CantorBoundary
def tail (x : CantorBoundary) : CantorBoundary
def branchPrefix (n : ℕ) (b : Bool) (w : BitWord n) : BitWord (n + 1)
def branchPullback (n : ℕ) (b : Bool) (f : DiagAlg (n + 1)) : DiagAlg n
```

`prependBit false` and `prependBit true` are the finite Cantor-boundary shadows
of the two binary branch shifts.

## Kernel-Checked Shift Laws

```lean
theorem tail_prependBit (b : Bool) (x : CantorBoundary) :
    tail (prependBit b x) = x

theorem prependBit_head (b : Bool) (x : CantorBoundary) :
    prependBit b x 0 = b

theorem prependBit_injective (b : Bool) :
    Function.Injective (prependBit b)

theorem prependBit_tail_of_head {x : CantorBoundary} {b : Bool} (h : x 0 = b) :
    prependBit b (tail x) = x
```

## Binary Branch Cover

```lean
theorem prependBit_range_cover (x : CantorBoundary) :
    x ∈ Set.range (prependBit false) ∪ Set.range (prependBit true)

theorem prependBit_false_true_disjoint :
    Disjoint (Set.range (prependBit false)) (Set.range (prependBit true))
```

The two branches cover the Cantor carrier and have disjoint ranges.

## Cylinder Pullback

```lean
theorem boundaryPrefix_prependBit (n : ℕ) (b : Bool) (x : CantorBoundary) :
    boundaryPrefix (n + 1) (prependBit b x) =
      branchPrefix n b (boundaryPrefix n x)

theorem cylinder_branch_pullback (n : ℕ) (b : Bool) (f : DiagAlg (n + 1)) :
    (fun x : CantorBoundary => cylinder (n + 1) f (prependBit b x)) =
      cylinder n (branchPullback n b f)

theorem branch_pullback_mem_colimit (n : ℕ) (b : Bool) (f : DiagAlg (n + 1)) :
    cylinder n (branchPullback n b f) ∈ CylinderColimit
```

Pulling a finite cylinder observable back along one branch is again a finite
cylinder observable.

## Consolidated Theorem

```lean
theorem finite_cuntz_cantor_shift_synthesis :
    Function.Injective (prependBit false) ∧
    Function.Injective (prependBit true) ∧
    Disjoint (Set.range (prependBit false)) (Set.range (prependBit true)) ∧
    (∀ x : CantorBoundary,
      x ∈ Set.range (prependBit false) ∪ Set.range (prependBit true)) ∧
    (∀ n : ℕ, ∀ b : Bool, ∀ f : DiagAlg (n + 1),
      (fun x : CantorBoundary => cylinder (n + 1) f (prependBit b x)) =
        cylinder n (branchPullback n b f)) ∧
    (∀ n : ℕ, ∀ b : Bool, ∀ f : DiagAlg (n + 1),
      cylinder n (branchPullback n b f) ∈ CylinderColimit)
```

## Companion SymPy Script

```bash
python3 tools/sympy/cuntz_cantor_boundary_shift.py
python3 tools/sympy/cantor_boundary_cuntz_shift.py
```

## Explicit Non-Claims

This API does not claim:

- full Cuntz `O₂` relations on a Hilbert space;
- adjoints or partial isometries;
- a C*-completion;
- a Cantor measure or spectral theorem;
- KMS dynamics;
- zeta/RH consequences.
