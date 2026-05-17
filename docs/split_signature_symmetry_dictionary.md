# Split-Signature Symmetry Dictionary

This note fixes the repository vocabulary for split-signature emerging
geometry.  The local symmetry is a tower, not one interchangeable group name.

## Rule Of Thumb

1. **Tangent-space metric:** use `O(n,n)`.
2. **Fermionic / Majorana / Clifford fiber:** use `Spin(n,n)` or, in the
   current Lean surfaces, a Clifford lift of split quadratic isometries.
3. **Reflections, CPT, orientation-reversing flips:** use `Pin(n,n)`.
4. **Boundary charts and projective compactifications:** use `PGL`, `PSL`, or a
   related projective group only at the chart/projective layer.

If old prose says `Pi(n,n)`, read it as `Pin(n,n)` unless the surrounding text
defines a different symbol.

## Repository-Facing Mapping

| Layer | Correct symmetry language | Repo owner surfaces | Status |
| --- | --- | --- | --- |
| Split metric base | `O(n,n)` / split orthogonal geometry | `lean/InfoGeometry/Krein/OrthogonalGroup.lean`, `lean/InfoGeometry/Geometry/SplitOrthogonalSpace.lean`, `lean/InfoGeometry/Clifford/Hestenes.lean`, `lean/InfoGeometry/Algebraic/NarainOrthogonalCore.lean` | Local metric symmetry of the doubled split carrier. |
| Quadratic-form isometries | split quadratic isometry | `lean/InfoGeometry/Algebraic/CliffordSymmetryLift.lean` via `SplitQuadraticSymmetry` | Native lift input for Clifford automorphisms. |
| Clifford/spinor lift | `Spin(n,n)` when orientation-preserving even Clifford data is intended | `lean/InfoGeometry/Clifford/Hestenes.lean`, `lean/InfoGeometry/Clifford/RealDoubledHestenesAnchor.lean`, `lean/InfoGeometry/Core/MajoranaLiftPacket.lean`, `lean/InfoGeometry/Krein/DoubledSpace.lean`, plus `lean/InfoGeometry/Algebraic/SplitCliffordCarrier.lean` and `lean/InfoGeometry/Algebraic/CliffordSymmetryLift.lean` | Fermionic / Majorana transport on the split base. Do not call the base metric action Spin unless it has been lifted. |
| Reflection/CPT lift | `Pin(n,n)` | `lean/SelfReference/Moebius.lean`, `lean/InfoGeometry/Canonical/MoebiusVirasoroBridge.lean`, `lean/InfoGeometry/Clifford/SplitQ11PhaseFlip.lean`, `lean/InfoGeometry/LLM/PinCPTBridge.lean`, `lean/InfoGeometry/OperatorAlgebra/O44PinMobiusProjective.lean`, `lean/InfoGeometry/OperatorAlgebra/O44PinCPTReflectionBridge.lean` | Used for involutive conjugations, odd/even sectors, reflections, CPT-style flips, and non-orienting Möbius twists. |
| Projective charts/boundaries | `PGL`, `PSL`, or projective orthogonal/conformal groups according to the chart | `lean/InfoGeometry/Geometry/RealMoebiusAction.lean`, `lean/InfoGeometry/Thermodynamics/SouriauTemperatureProjective.lean`, `lean/InfoGeometry/Core/ProjectiveSimplex.lean`, `lean/InfoGeometry/Canonical/ProjectiveFoundation.lean`, `lean/InfoGeometry/ProjectiveFoundation.lean`, `lean/InfoGeometry/ProjectiveFoundation/RealProjectiveDescent.lean`, `lean/InfoGeometry/Canonical/PSLDescent.lean` | Boundary atlas and chart compactification symmetry, not the intrinsic local metric symmetry. |
| Möbius compactification | projective/conformal extension of the split-orthogonal data | `lean/InfoGeometry/OperatorAlgebra/O44PinMobiusProjective.lean`, `lean/InfoGeometry/Canonical/MoebiusBogoliubovVirasoroBridge.lean` | Use only after naming the projective/conformal carrier. |

## Line-By-Line Dictionary

- **Metric layer:** `O(n,n)` is the symmetry of the split base geometry.
- **Spinor layer:** `Spin(n,n)` is the symmetry of fermionic / Majorana
  transport on that base.
- **Reflection layer:** `Pin(n,n)` is the symmetry once orientation-reversing
  involutions are admitted.
- **Projective layer:** `PGL` is the symmetry of chart compactification or
  boundary reparametrization.

## Guardrails

- `O(n,n)` preserves the split metric.  It is the base-space symmetry.
- `Spin(n,n)` is a cover/lift acting on spinors or Clifford modules.  It is not
  a synonym for the metric symmetry.
- `Pin(n,n)` is the reflection-extended lift.  Use it for CPT-style
  orientation reversal, odd Clifford elements, or non-orienting Möbius flips.
- `PGL`/`PSL` is chart or boundary language.  It belongs to projective descent,
  compactification, or Möbius reparameterization, not to the raw tangent metric.
- The doubled `Cl(1,1)` and self-reference twist sit at the Pin-type level, not
  at raw projective symmetry.
- The Möbius action on a real boundary is projective geometry; by itself it is
  not the intrinsic local metric symmetry of the emerging manifold.
- The finite prime Boolean cube and exterior carriers are representation
  layers.  They inherit or instantiate the tower; they do not define the tower.

The defensible default for emerging-manifold prose is therefore:

```text
split metric base symmetry      : O(n,n)
operator / spinor symmetry      : Spin(n,n)
reflection / Möbius / CPT lift  : Pin(n,n)
boundary chart action           : PGL / PSL / projective group layer
```

## Current Lean Evidence

- `SplitOrthogonalCartanSpace` records the split-orthogonal base-space carrier
  for the Narain / `O(n,n)` lane.
- `InfoGeometry.Krein.OrthogonalGroup` is the Krein-side orthogonal group
  surface for indefinite metric symmetries.
- `SplitQuadraticSymmetry` is a quadratic-form isometry of the real split
  carrier, and `splitCliffordLift` maps it to a Clifford algebra automorphism.
- `InfoGeometry.Clifford.Hestenes`, `RealDoubledHestenesAnchor`,
  `MajoranaLiftPacket`, and `DoubledSpace` are the repo-native anchors for the
  doubled Clifford / Majorana lift language.
- `PinAction` in `PinCPTBridge.lean` proves the native algebraic behavior of an
  involutive reflection: odd elements flip under conjugation, odd squares are
  even, and conjugation is involutive.
- `SelfReference.Moebius` and `SplitQ11PhaseFlip.lean` are Pin-type surfaces
  for Möbius/self-reference and split phase-flip behavior.  The Virasoro bridge
  surface for that lane is currently `InfoGeometry.Canonical.MoebiusVirasoroBridge`.
- `O44PinMobiusProjective.lean` explicitly separates `O(4,4)`, `Pin(4,4)`, and
  projective/Möbius extension language.
- `ProjectiveFoundation.lean` owns `SL2R`, `PSL2R`, and cover-cocycle descent
  language for the projective layer.

This dictionary is a naming constraint.  It does not add a new theorem that
identifies all these layers; it prevents them from being silently collapsed.
