# Graph Hodge Spectrum

Global spectral report on the **undirected shadow** of the declaration DAG.
The 2-complex uses transitive triangles (a modelling choice, not intrinsic).

## Simplicial Complex

| | Count |
|---|---|
| vertices | 14178 |
| edges | 70857 |
| triangles | 166680 |
| χ = V−E+F | 110001 |

## Betti Numbers

- b₀ = 128  (connected components)
- b₁ ∈ [0, 56807]  (Euler bounds)

## Spectrum  (largest CC, 12956 nodes)

- Fiedler λ₂ = `0.0012931944732145332`
- λ_max = `3448.004251475397`
- λ₂/λ_max = `0.000000`

## Pseudoinverse (largest CC only, 12956 nodes)

L⁺ = (L + J/n)⁻¹ − J/n,  solved by CG on the invertible (L + J/n).

- Kirchhoff index K = n·tr(Δ₀⁺) ≈ `57466562.89`
- mean effective resistance ≈ `0.684758`

### Effective Resistance Samples

| u | v | R(u,v) |
|---|---|---|
| `InfoGeometry.Krein.instL2InnerProduct` | `InfoGeometry.Krein.instL2NormedGroup` | 0.002804 |
| `InfoGeometry.Krein.instL2InnerProduct` | `InfoGeometry.Volume.RadonNikodym.HasScalarRNBridge.ctor` | 1.341133 |
| `InfoGeometry.Volume.RadonNikodym.HasScalarRNBridge.ctor` | `InfoGeometry.Volume.Pfaffian.pfaffian2D` | 3.345341 |

## Directed Asymmetry

‖L_dir − L_dirᵀ‖_F / ‖L_dir‖_F = `0.470355`

Frobenius norm ratio measuring how far the directed Laplacian is from symmetric.

## Parity-Mixing Score

- tagged nodes: 16/14178
- same-parity edges: 70730/70857 (99.82%)
- **caveat**: only 16/14178 nodes carry RepDepth tags; untagged default to +1, so this metric is dominated by defaults

## Degree Stats

mean=10.0  median=7.0  max=3447  p95=23.149999999999636  isolated=70

*Computed in 59.2s.*
