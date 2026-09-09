# Polarized Minkowski boundary: quadratic extension, Clifford action, and bivectors

## Source, interpretation, and verification

The requested source is `Pasted markdown(20260906-072133).md`, titled “Structural Analysis: The 10D Lift and the K^(5,5) Metric.” Its displayed polynomial diagonalization is retained. This extension separates that identity from the additional physical and topological claims in the source. The development builds on `main` at `b0fa422e6cb6d3da5be7cbbb5ecfae5c12f3237b`; it does not depend on the earlier draft PRs and does not change existing files.

Six new Lean modules contain 55 public theorems, 30 definitions, and three abbreviations. Their proof scripts are explicit, but **have not been elaborated or checked by the Lean kernel here**. The actual local launcher exited 127 because `lake` is not installed or on PATH. Independent exact symbolic and finite-matrix tests passed. A comment-aware source scan found no new proof placeholders, mathematical axioms, unsafe implementations, or native_decide. These checks do not inspect transitive proof dependencies. The native audit must run before certification.

## 1. An actual quadratic isometry, rather than another unbundled record

Reuse `Cl55MinkowskiCelestialSlice.Minkowski13 = Real × (Fin 3 → Real)` and group the source coordinates as

```
Boundary55 = (Real × Minkowski13) × (Real × Minkowski13),
z = ((alpha,U),(beta,V)).
```

The independently defined native quadratic form is

```
q(z) = alpha beta - U0 V0 + sum_i U_i V_i.
```

The source's diagonalization is implemented as a real-linear equivalence with a proved two-sided inverse:

```
p = ((alpha+beta)/2, (U0-V0)/2, (Usp+Vsp)/2),
n = ((alpha-beta)/2, (U0+V0)/2, (Usp-Vsp)/2).
```

It satisfies `Q55(diagonalEquiv z)=q(z)` for the repository-owned `Clifford55.Q55`, and is bundled as `diagonalIsometry : q.IsometryEquiv Q55`. The dimension theorem is a genuine `Module.finrank Real Boundary55 = 10` calculation. No new octonion multiplication is introduced. Having two additional vector coordinates and a quadratic polynomial does not itself specify a composition algebra.

## 2. What “eight to ten” means with the existing Zorn norm

For the actual canonical Zorn element `X=(a,b,x,y)`, the old norm is `N(X)=ab-x dot y`. The sign-compatible inclusion is

```
X ↦ ((a,(0,x)), (b,(0,-y))).
```

Appending zero time coordinates without changing the lower spatial sign would instead yield `ab+x dot y`. The new source proves the correct inclusion is injective and preserves the old norm and its null condition.

More strongly, it constructs the full real-linear equivalence

```
Boundary55 ≃ₗ[Real] NativeZorn × (Real × Real),
((alpha,U),(beta,V)) ↦ ((alpha,beta,Usp,-Vsp),(U0,V0)),
q(z) = N(X) - t s.
```

This is the precise quadratic extension by a hyperbolic plane. It is not a claim that the octonion product extends to a ten-dimensional octonion product.

## 3. The source's involutions and a separate fundamental symmetry

Retain the actual coordinate operations:

```
S(alpha,beta,U,V) = (alpha,beta,-U,-V),
J(alpha,beta,U,V) = (beta,alpha,V,U),
G = J S.
```

Their involutive identities, commutation, and preservation of q are proved. They are packaged as native quadratic isometries. G is lifted by Clifford functoriality, and the lift squares to identity on the entire Clifford algebra, not only its generators.

However, S is not a positive fundamental symmetry. On the scalar null-ray difference `z=alphaRay-betaRay`, the polar form satisfies

```
polar(q)(z,Sz) = -2.
```

The corrected fundamental symmetry is a different map:

```
F(alpha,beta,U0,Usp,V0,Vsp)
  = (beta,alpha,-V0,Vsp,-U0,Usp).
```

In the established diagonal coordinates it acts as `(p,n)↦(p,-n)`. It preserves q and satisfies F²=1. Its induced polar expression is exactly

```
polar(q)(z,Fz) = alpha²+beta²+U0²+V0²+sum_i U_i²+sum_i V_i²,
```

which is proved strictly positive for every nonzero z. When the bilinear metric is taken as half the polar form, the corresponding expression is half this sum; the positivity statement is unchanged.

The matrix of J in explicit diagonal coordinates is also derived:

```
diag(1,-1,1,1,1, -1,1,-1,-1,-1).
```

Its determinant is -1. Thus the source's full linear q-preserving group is not restricted to the special-orthogonal subgroup. The complete quadratic-isometry group is the orthogonal group; determinant one is a separate restriction.

A real slot exchange is not, without operator-algebraic data, a Tomita conjugation. G fixes the origin, so its square-one law is not a free Klein-bottle deck action on this carrier. No quotient surface, orientable double cover, unitarity, or anomaly cancellation is inferred from it. The file names use `pairSwap`, `vectorFlip`, and `mixedSwap` rather than encoding those unproved physical interpretations in the definitions.

## 4. Native Clifford and exterior-spinor actions

The quadratic isometry supplies, through Mathlib's universal construction,

```
CliffordAlgebra q ≃ₐ[Real] Clifford55.Cl55.
```

Composing with the existing `cl55SpinorAlgEquiv` gives the repository's native 32-by-32 real matrix realization. Independently, the coordinate map enters the existing neutral vector/covector model through `Cl55NeutralHyperbolicIsometry.neutralToV55.symm`; its actual wedge-plus-contraction action on `ExteriorAlgebra Real (Fin 5 → Real)` then satisfies

```
c(z)² = q(z) id.
```

The matrix action has the same square and the anticommutator `c(z)c(w)+c(w)c(z)=polar(q)(z,w) id`. These are derived from the existing operators and Clifford functoriality, not postulated commutator fields.

The scalar directions `alphaRay` and `betaRay` are null, with polar pairing one. Their matrix actions are therefore square-zero operators whose mixed anticommutator is identity. Null Clifford vectors are not the Zorn idempotents themselves; products of such null operators can provide idempotents in a separate construction. No equality of the two poles or horizon degeneration is asserted.

The extension does not add a theorem identifying separately chosen exterior and matrix spinor bases, nor a quantum time evolution or measurement model. Those are different obligations from the proved-target quadratic and Clifford action identities.

## 5. Genuine exterior bivectors and reused Lorentzian Hodge sectors

The four-vector slot remains a real Minkowski vector, not a two-component Weyl spinor. Its exterior product is constructed in the native second exterior power

```
Bivector13 = ⋀[Real]^2 Minkowski13,
u ∧ v = exteriorPower.ιMulti Real 2 ![u,v].
```

A real-linear coefficient readout into the existing `TwoFormC = Fin 6 → Complex` is induced by the native exterior-power universal property. Its order is `(01,02,03,23,31,12)`, matching the existing Hodge owner. This is not merely a new six-field surrogate called an exterior algebra.

The exterior self-product `u∧u=0` is proved by alternation. A separate finite sum theorem shows that commuting scalar coefficients `u_i u_j` contract to zero with a skew tensor. Consequently the source's repeated-ray expression cannot by itself generate a nonzero curvature. Operator-valued noncommuting coefficients would require a separately specified carrier and differential calculus.

The imported finite Lorentzian Hodge operator is reused without changing conventions. It has square -1 and complex eigenspace projectors `(1-i*)/2` and `(1+i*)/2`. Their established reconstruction theorem is applied to the readout of the actual exterior bivector. No metric-derived bundle Hodge star, connection curvature, or field equation is inferred.

Two transformations must be distinguished:

- Swapping the two state slots sends `U∧V` to `-U∧V`; G does the same. Its Hodge image acquires the same minus sign. This operation does not automatically exchange self-dual and anti-self-dual sectors.
- Spacetime spatial inversion `(t,x)↦(t,-x)` induces `diag(-1,-1,-1,+1,+1,+1)` on the two-form readout. It anti-commutes with the selected Lorentzian Hodge operator and exchanges the two complex chiral projections. Those identities are explicitly implemented.

The real six-dimensional bivector space and its complexification are different scalar-field statements. In particular the familiar `(1,0)⊕(0,1)` notation refers to complex representation sectors, not two independent real three-dimensional eigenspaces of a real star whose square is -1.

## 6. Scope of the remaining source claims

The equality `q=alpha beta-U dot V` is not, by itself, an identification of `alpha beta` with a quantum transition amplitude, an AAV weak-value denominator, or a Schwinger–Keldysh boundary condition. Those require an explicit pairing/state construction.

Similarly, the ten-dimensional vector quadratic carrier is not itself a contact five-graded Lie algebra. Constructing the corresponding orthogonal Lie algebra, a selected grading, its bracket, and its representation assignments is separate. No claim of a contact decomposition or “minimal conformal representation” follows just from counting ten vector coordinates here.

## Execution

From a full checkout with the pinned dependencies:

```sh
bash scripts/check_polarized_boundary55.sh
python3 scripts/audit_polarized_boundary55_sources.py
python3 scripts/audit_polarized_boundary55_exact.py
```

The native audit covers all 88 public declarations and rejects unexpected transitive axioms or incomplete audit output. The exact regression script requires SymPy. It checks both inverse maps, the polarization, isometry matrices, positivity polynomial and negative witness, norm extension, wedge/Hodge/parity formulas, and the full symbolic 32-by-32 exterior-action square. It is not a Lean certificate.

The principal reused owners are `Cl55MinkowskiCelestialSlice`, `Clifford55`, `Cl55NeutralHyperbolicIsometry`, `SplitClifford55ExteriorSpinor`, `HodgeStar4DFinite`, and the canonical `Algebra/Zorn/Basic`. The new files leave all existing carriers and operations unchanged.
