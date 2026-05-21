# Mode Extension Boundary

Lean module:

`InfoGeometry.Canonical.ModeExtensionBoundary`

## Purpose

This module introduces only the conservative zero-mode interface

```text
u₊  ↦  u₊,n
u₋  ↦  u₋,n
ε   ↦  εₙ
```

with the following meaning:

```text
u₊,0 = u₊
u₋,0 = u₋
ε₀  = ε
u₊,n = 0, u₋,n = 0, εₙ = 0 for n ≠ 0
```

This is not a current algebra.  It is the mode-labeled finite seed that makes
the next missing theorem precise.

## Proved

At the zero label the module recovers the finite Tomita-Krein atom:

```text
u₊,0² = 0
u₋,0² = 0
u₊,0 u₋,0 = P₊
u₋,0 u₊,0 = P₋
{u₋,0, u₊,0} = 1
[u₊,0, u₋,0] = ε₀
```

For arbitrary labels:

```text
[u₊,m, u₋,n] = ε   if m = 0 and n = 0
[u₊,m, u₋,n] = 0   otherwise
```

So the zero-mode seed has no Heisenberg anomaly.

## Boundary

The module deliberately does not prove

```text
[J_m, J_n] = m δ_{m+n,0} K
```

That bracket is already implemented in the external Virasoro library as
`HeisenbergAlgebra.lie_jgen`.

The missing future theorem is a real bosonization/current construction proving
that a mode-indexed family derived from the split-Clifford completion satisfies
the external Heisenberg current law.  The zero-mode seed is only the finite
input to that future theorem.
