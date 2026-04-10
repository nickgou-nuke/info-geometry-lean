# Lift Naturality Diagnostics

- module: `InfoGeometry.Canonical.All`
- namespace: `InfoGeometry`
- tagged lift functors: `2`
- matched equality theorems: `3`
- normalized defeq seeds: `3`

Tagged lift functors:

- `InfoGeometry.Canonical.GeneratedFlow.along`
- `InfoGeometry.Canonical.LogGenerator.generate`

## `InfoGeometry.Canonical.GeneratedFlow.along_apply`

- head lift mentions: [`InfoGeometry.Canonical.GeneratedFlow.along`]
- lift mentions: [`InfoGeometry.Canonical.GeneratedFlow.along`]
- raw hash match: `false`
- normalized hash match: `true`
- normalized defeq: `true`

### Raw sides

```lean
lhs := Φ.along L w
rhs := Φ.flowOf (L.logGen w)
```

### Normalized sides

```lean
lhs := Φ.1 (L.logGen w)
rhs := Φ.1 (L.logGen w)
```

## `InfoGeometry.Canonical.LogGenerator.generate_apply`

- head lift mentions: [`InfoGeometry.Canonical.LogGenerator.generate`]
- lift mentions: [`InfoGeometry.Canonical.LogGenerator.generate`]
- raw hash match: `false`
- normalized hash match: `true`
- normalized defeq: `true`

### Raw sides

```lean
lhs := L.generate Φ w
rhs := Φ.flowOf (L.logGen w)
```

### Normalized sides

```lean
lhs := Φ.1 (L.logGen w)
rhs := Φ.1 (L.logGen w)
```

## `InfoGeometry.Canonical.LogGenerator.generate_eq_along`

- head lift mentions: [`InfoGeometry.Canonical.GeneratedFlow.along`, `InfoGeometry.Canonical.LogGenerator.generate`]
- lift mentions: [`InfoGeometry.Canonical.GeneratedFlow.along`, `InfoGeometry.Canonical.LogGenerator.generate`]
- raw hash match: `false`
- normalized hash match: `true`
- normalized defeq: `true`

### Raw sides

```lean
lhs := L.generate Φ
rhs := Φ.along L
```

### Normalized sides

```lean
lhs := fun w => Φ.flowOf (L.logGen w)
rhs := fun w => Φ.flowOf (L.logGen w)
```

