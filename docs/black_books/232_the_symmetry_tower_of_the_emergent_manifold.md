# 232. The Symmetry Tower of the Emergent Manifold

When describing the split-signature emerging manifold and its doubled tangent space, the local symmetry is not a single group, but a strict hierarchical tower. It is critical to maintain the precise boundaries between the intrinsic local symmetries of the metric and the extrinsic symmetries of the boundary charts. 

This chapter provides a strict, repo-facing dictionary that maps each layer of the $O \to Spin \to Pin \to PGL$ symmetry tower to the exact Lean 4 surfaces that realize them.

## The Clean Hierarchy

The symmetry tower is strictly ordered from the base geometry up to the boundary compactification:

1.  **$O(n,n)$**: The metric symmetry of a split $(n,n)$ form.
2.  **$Spin(n,n)$**: The double cover when you lift to spinors / Majorana-Clifford data.
3.  **$Pin(n,n)$**: The reflection-extended lift (used when you allow reflections, CPT-type involutions, or non-orienting flips).
4.  **$PGL$**: The symmetry of chart projectivization or boundary data. It is **not** the native local symmetry of the metric itself.

## The Repo-Facing Dictionary

This theoretical tower maps directly line-by-line onto the formalized Lean surfaces within the repository.

### 1. The Metric Layer: $O(n,n)$
**Role:** The symmetry of the split base geometry (the local metric symmetry of the doubled split carrier).
**Lean Surface Matches:**
*   `InfoGeometry.Krein.OrthogonalGroup` (The indefinite orthogonal layer over the split tangent form)
*   `InfoGeometry.Clifford.Hestenes` (The split quadratic-form carrier)

### 2. The Spinor Layer: $Spin(n,n)$
**Role:** The symmetry of fermionic / Majorana transport on that base geometry (the Spinor/Clifford lift).
**Lean Surface Matches:**
*   `InfoGeometry.Clifford.Hestenes` (Doubled Majorana and $Cl(1,1)$ carrier)
*   `InfoGeometry.Clifford.RealDoubledHestenesAnchor`
*   `InfoGeometry.Core.MajoranaLiftPacket`
*   `InfoGeometry.Krein.DoubledSpace`

### 3. The Reflection Layer: $Pin(n,n)$
**Role:** The symmetry once orientation-reversing involutions are admitted (the reflection-extended lift for parity flips, CPT-type involutions, or Möbius reversals).
**Lean Surface Matches:**
*   `SelfReference.Moebius` (The self-reference Möbius twist)
*   `InfoGeometry.Canonical.MoebiusVirasoroBridge`
*   `InfoGeometry.Clifford.SplitQ11PhaseFlip` (Split phase-flip surfaces)

### 4. The Projective Layer: $PGL$
**Role:** The symmetry of chart compactification or boundary reparametrization. **Crucial Correction:** $PGL$ is the atlas symmetry, not the intrinsic local symmetry of the manifold.
**Lean Surface Matches:**
*   `InfoGeometry.Geometry.RealMoebiusAction`
*   `InfoGeometry.Thermodynamics.SouriauTemperatureProjective`
*   `InfoGeometry.Core.ProjectiveSimplex`
*   `InfoGeometry.Canonical.ProjectiveFoundation`

## Key Architectural Readings

To preserve the purity of the physics reading against the Lean compiler surface, the following rules apply:

1.  **The Self-Reference Position:** The doubled $Cl(1,1)$ complex structure and the `moebiusTwist` (self-reference) sit strictly at the **$Pin$-type level**. They are intrinsic, reflection-admitting symmetries, *not* raw projective symmetries.
2.  **The Projective Action:** The Möbius action on the real boundary is projective geometry ($PGL$), but it is orientation-preserving by itself. It lives purely at the boundary layer.
3.  **The Finite Representation:** The finite prime Boolean cube and the prime exterior carriers are representation layers. They *inherit* the symmetry tower, but they do not *define* it. 

The intrinsic local tower is exclusively **$O \to Spin \to Pin$**. Boundary chart action sits atop this as **$PGL$**.
