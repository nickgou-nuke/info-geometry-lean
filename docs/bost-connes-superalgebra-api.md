# Bost-Connes Superalgebra API

> Status: `live API overview`
> Audited: 2026-06-10
> Public module: `lean/InfoGeometry/Canonical/BostConnesSuperalgebra.lean`
> Constructive owner: `lean/InfoGeometry/Canonical/BostConnesSuperalgebraConstructive.lean`
> Boundary: finite algebraic Euler/Witten factors and parity-supertrace
> cancellation only.

This API gives the theorem-safe Bost-Connes/Witten-parity corridor currently
owned by the repository. It avoids postulating an infinite UHF algebra or KMS
phase transition and instead works with explicit algebraic premises.

## Local Euler Factor

```lean
def localBosonFactor {R : Type*} [Field R] (x : R) : R := (1 - x)⁻¹
def localWittenFactor {R : Type*} [Field R] (x : R) : R := 1 - x

theorem local_boson_mul_wittenFactor
    {R : Type*} [Field R] (x : R) (h : 1 - x ≠ 0) :
    localBosonFactor x * localWittenFactor x = 1

theorem wittenFactor_mul_local_boson
    {R : Type*} [Field R] (x : R) (h : 1 - x ≠ 0) :
    localWittenFactor x * localBosonFactor x = 1
```

These are the finite regulated shadows of bosonic Euler inversion by the signed
Witten/Mobius factor.

## Parity Supertrace

```lean
abbrev StarWittenParity (A : Type*) [Ring A] [StarRing A]
abbrev AlgebraicState (A : Type*) [Ring A]

def supertrace
    {A : Type*} [Ring A] [StarRing A]
    (P : StarWittenParity A) (φ : AlgebraicState A) (x : A) : ℂ

theorem invariant_state_supertrace_parity_odd_eq_zero
    {A : Type*} [Ring A] [StarRing A]
    (P : StarWittenParity A) (φ : AlgebraicState A)
    (hφ : StateParityInvariant P φ) {x : A} (hx : ParityOdd P x) :
    supertrace P φ x = 0
```

The cancellation theorem is conditional on explicit parity invariance of the
state and explicit oddness of the element.

## Cuntz/CAR Readout

```lean
abbrev ParityEquivariantCuntzCarrier (A : Type*) [Ring A] [StarRing A]

theorem cuntz_carFromCuntz_parity_odd
    {Op : Type*} [Ring Op] [StarRing Op]
    (E : ParityEquivariantCuntzCarrier Op) :
    ParityOdd E.parity (carFromCuntz E.cuntz)

theorem invariant_state_supertrace_carFromCuntz_eq_zero
    {Op : Type*} [Ring Op] [StarRing Op]
    (E : ParityEquivariantCuntzCarrier Op)
    (φ : AlgebraicState Op) (hφ : StateParityInvariant E.parity φ) :
    supertrace E.parity φ (carFromCuntz E.cuntz) = 0
```

The branch grading is model data supplied by `ParityEquivariantCuntzCarrier`;
it is not derived from bare Cuntz relations alone.

## Companion Witness

```bash
python3 tools/sympy/bost_connes_superalgebra_constructive.py
```

## Explicit Non-Claims

This API does not claim:

- an infinite UHF/C*-completion;
- the Bost-Connes KMS simplex or phase transition;
- BEC/Hagedorn thermodynamics;
- Galois action on cyclotomic fields;
- Tate adelic functional equation;
- zeta analytic continuation or RH consequences.
