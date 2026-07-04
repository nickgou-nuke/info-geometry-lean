# Split-Octonionic Primon Gas: theorem inventory and axiomatic architecture

Status: repo-grounded synthesis over the current Lean checkout.

Authority convention:

- kernel authority = named Lean declarations listed below;
- computational/CAS authority = local scripts or wrappers explicitly named elsewhere;
- external physics language = interpretation layer over the named declarations;
- promotion criterion = a statement appears as a Lean declaration with a checked proof term or as an explicitly checked finite external certificate.

## 0. Algebraic carriers

### 0.1 Concrete Zorn split-octonion carrier

Owner:

- `lean/InfoGeometry/OperatorAlgebra/SplitOctonionMultiplication.lean`

Carrier:

\[
X=(a,b,x_0,x_1,x_2,y_0,y_1,y_2)
\]

with determinant

\[
\det_Z(X)=ab-(x_0y_0+x_1y_1+x_2y_2).
\]

Product:

\[
\operatorname{mulZ}(X,Y)
\]

is the explicit Zorn vector-matrix product with dot and cross terms.

Checked basis/norm/conjugation declarations:

- `detZ`
- `mulZ`
- `associator`
- `basisElem_mul`
- `basis_table_packet`
- `conjZ`
- `conjZ_conjZ`
- `detZ_conjZ`
- `mul_conjZ_eq_scalar_detZ`
- `conjZ_mulZ`
- `splitOctonion_multiplication_packet`

### 0.2 Concrete composition carrier

Owner:

- `lean/InfoGeometry/Algebra/Zorn/ConcreteComposition.lean`

Carrier:

\[
X=(r,s,x_1,x_2,x_3,y_1,y_2,y_3).
\]

The determinant and polar form are

\[
\det_Z(X)=rs-(x_1y_1+x_2y_2+x_3y_3),
\]

\[
B_Z(X,Y)=\det_Z(X+Y)-\det_Z(X)-\det_Z(Y).
\]

Checked declarations:

- `ZornCell.detZ`
- `ZornCell.polarZ`
- `ZornCell.polarZ_comm`
- `ZornCell.polarZ_self`
- `ZornCell.polarZ_self_of_detZ_zero`
- `ZornCell.polarZ_self_zero_iff_detZ_zero_of_two_ne_zero`
- `ZornCell.detZ_mul`
- `ZornCell.detZ_left_mul_normOne`
- `ZornCell.detZ_right_mul_normOne`
- `ZornCell.detZ_mul_eq_zero_of_left_null`
- `ZornCell.detZ_mul_eq_zero_of_right_null`

The algebraic metric statement is:

\[
B_Z(X,X)=2\det_Z(X),
\]

and, over an integral domain with `2 ≠ 0`,

\[
B_Z(X,X)=0 \Longleftrightarrow \det_Z(X)=0.
\]

## 1. Local metric frame: composition and nonassociative defect

### 1.1 Determinant composition

Owners:

- `lean/InfoGeometry/Canonical/ZornComposition.lean`
- `lean/InfoGeometry/Algebra/Zorn/ConcreteComposition.lean`
- `lean/InfoGeometry/OperatorAlgebra/SplitOctonionNormComposition.lean`

Checked theorems:

\[
\det_Z(XY)=\det_Z(X)\det_Z(Y).
\]

Declarations:

- `InfoGeometry.Canonical.ZornComposition.detZ_mul`
- `InfoGeometry.Algebra.Zorn.ConcreteComposition.ZornCell.detZ_mul`
- `InfoGeometry.OperatorAlgebra.SplitOctonions.NormComposition.detZ_mulZ`

Consequences:

\[
\det_Z(U)=1 \Longrightarrow \det_Z(UX)=\det_Z(X),
\]

\[
\det_Z(U)=1 \Longrightarrow \det_Z(XU)=\det_Z(X),
\]

\[
\det_Z(X)=0 \Longrightarrow \det_Z(XY)=0,
\]

\[
\det_Z(Y)=0 \Longrightarrow \det_Z(XY)=0.
\]

### 1.2 Basis-level nonassociativity

Owner:

- `lean/InfoGeometry/OperatorAlgebra/SplitOctonionMultiplication.lean`

Checked declarations:

- `associator`
- `associator_up0_up1_down1`
- `associator_up0_up1_down1_ne_zero`
- `splitOctonion_multiplication_packet`

The finite witness is:

\[
[u_0,u_1,d_1] \ne 0.
\]

Thus the concrete Zorn product carries a checked nonassociative defect while preserving the split norm composition law.

## 2. Modular-J / conjugation layer

Owner:

- `lean/InfoGeometry/OperatorAlgebra/SplitOctonionModularJ.lean`

Definition:

\[
J(a,b,x_0,x_1,x_2,y_0,y_1,y_2)=
(b,a,-x_0,-x_1,-x_2,-y_0,-y_1,-y_2).
\]

Checked theorems:

- `modularJ_apply`
- `modularJ_involutive`
- `modularJ_anti_automorphism`
- `detZ_modularJ_invariant`
- `mul_modularJ_eq_scalar_detZ`
- `modularJ_structure_packet`

Equations:

\[
J^2=1,
\]

\[
J(XY)=J(Y)J(X),
\]

\[
\det_Z(JX)=\det_Z(X),
\]

\[
XJ(X)=\det_Z(X)\,1.
\]

This is the checked algebraic reflection packet for the concrete Zorn split-octonion product.

## 3. Determinant-ratio / relative-volume layer

Owner:

- `lean/InfoGeometry/Projective/SplitOctonions/ZornFlowRelativeVolume.lean`

Definitions:

\[
\operatorname{RN}_Z(X,Y)=\frac{\det_Z(Y)}{\det_Z(X)}.
\]

\[
\operatorname{DetPreserving}(\Phi) \equiv
\forall X,\ \det_Z(\Phi X)=\det_Z(X).
\]

\[
\operatorname{DetSimilitude}(\Phi,\chi) \equiv
\forall X,\ \det_Z(\Phi X)=\chi\det_Z(X).
\]

Checked theorems:

- `flowRelativeVolumeRN_eq_zornRelativeVolumeRN`
- `flowRelativeVolumeRN_self`
- `flowRelativeVolumeRN_comp`
- `zornLogBarrier_flowDifference`
- `detPreserving_id`
- `detSimilitude_one_of_detPreserving`
- `RN_of_detSimilitude`
- `RN_of_detPreserving`
- `detSimilitude_scalarScale`
- `RN_scalarScale_from_detSimilitude`
- `flowRelativeVolumeRN_scalarScale_right`
- `flowRelativeVolumeRN_scalarScale_left`

Equations:

\[
\operatorname{RN}_Z(X,X)=1 \quad (\det_Z(X)\ne0),
\]

\[
\operatorname{RN}_Z(X,Z)=\operatorname{RN}_Z(X,Y)\operatorname{RN}_Z(Y,Z)
\quad (\det_Z(X),\det_Z(Y)\ne0),
\]

\[
-\log\operatorname{RN}_Z(X,Y)=\varphi(Y)-\varphi(X)
\]

on the positive determinant stratum, where

\[
\varphi(X)=-\log\det_Z(X).
\]

For unit scalar scaling by `u`,

\[
\operatorname{RN}_Z(X,uX)=u^2.
\]

## 4. Split-quaternion control model

Owner:

- `lean/InfoGeometry/Algebra/SplitQuaternionAutomorphismStructure.lean`

Carrier:

\[
M_2(\mathbb R),\qquad \det_2\begin{pmatrix}a&b\\c&d\end{pmatrix}=ad-bc.
\]

Checked theorems:

- `mul_adj2`
- `adj2_mul`
- `mul_inv2`
- `inv2_mul`
- `det2_inv2`
- `innerConj_mul`
- `innerConj_one`
- `det2_innerConj`
- `det2_leftRight`
- `det2_transpose`
- `transpose_mul_reverse`
- `trace2_traceZeroMatrix`
- `det2_traceZeroMatrix`
- `det2_splitQuaternion_signature`
- `structure_group_generators_packet`
- `inner_automorphism_packet`

Equations:

\[
A\operatorname{adj}(A)=\det(A)I,
\]

\[
\operatorname{adj}(A)A=\det(A)I,
\]

\[
\det(A X B)=\det(A)\det(B)\det(X),
\]

\[
\det(X^T)=\det(X),
\]

\[
(XY)^T=Y^TX^T,
\]

\[
\det\begin{pmatrix}z&x+y\\x-y&-z\end{pmatrix}=y^2-x^2-z^2.
\]

This is the checked associative `M₂(ℝ)` control model for determinant similitudes and anti-automorphic transpose reversal.

## 5. Primon gas finite Euler and thermodynamic layers

Owner:

- `lean/InfoGeometry/Arithmetic/PrimonCrystallizationFactIndex.lean`

Finite Euler factors:

\[
Z_B(S,x)=\prod_{p\in S}(1-xp)^{-1},
\]

\[
Z_F(S,x)=\prod_{p\in S}(1+xp),
\]

\[
Z_\mu(S,x)=\prod_{p\in S}(1-xp).
\]

Checked theorems:

- `boson_signed_closure`
- `fermion_signed_second_order`
- `mobius_squarefree_parity`
- `repeated_prime_sector_killed`
- `inverse_determinant_free_energy`
- `gibbs_kms_free_energy_minimizer`
- `finite_prime_lattice_entropy_maximizer`
- `finite_vandermonde_nonzero_iff_injective`
- `finite_vandermonde_zero_iff_collision`
- `finite_dyson_vandermonde_potential`
- `branch_defect_dyson_packet`
- `resonator_flat_berry_packet`

Equations:

\[
Z_B(S,x)Z_\mu(S,x)=1,
\]

\[
Z_F(S,x)Z_\mu(S,x)=\prod_{p\in S}(1-(xp)^2),
\]

\[
\mu(n)=0\quad(n\notin \mathrm{SqFree}),
\]

\[
F(Z^{-1})=\log Z\quad(Z>0),
\]

\[
D(\rho\mid \sigma_\beta)\ge0,\ \beta>0
\Longrightarrow
F(\sigma_\beta)\le F(\rho),
\]

\[
H_{\mathrm{Dyson}}(\lambda,V)=E_{\mathrm{ext}}(\lambda,V)-\log |\Delta(\lambda)|^2
\]

on the finite separated-node branch.

## 6. Vandermonde exclusion / collision locus

Owner:

- `lean/InfoGeometry/Canonical/VandermondeExclusionBridge.lean`

Definitions:

\[
V(v)=\operatorname{Matrix.vandermonde}(v),
\qquad
\Delta(v)=\det V(v).
\]

Checked theorems:

- `determinant_eq_pairwise_separation`
- `determinant_eq_zero_iff_collision`
- `determinant_ne_zero_iff_injective`
- `collision_forces_determinant_zero`
- `determinant_ne_zero_forbids_collision`
- `exclusion_packet`

Equations:

\[
\det V(v)=\prod_i\prod_{j\in Ioi(i)}(v_j-v_i),
\]

\[
\det V(v)=0
\Longleftrightarrow
\exists i\ne j,\ v_i=v_j,
\]

\[
\det V(v)\ne0
\Longleftrightarrow
v\ \text{injective}.
\]

## 7. Positive formal dictionary

The current checked architecture supports the following formal dictionary.

| Physical phrase | Formal object | Checked theorem surface |
| --- | --- | --- |
| split-octonionic state | `SplitOct` / `ZornCell` | `SplitOctonionMultiplication`, `ConcreteComposition` |
| partition-function norm | `detZ` | `detZ_mul`, `detZ_mulZ` |
| nonassociative defect | `associator` | `associator_up0_up1_down1_ne_zero` |
| conjugation/reflection | `modularJ = conjZ` | `modularJ_anti_automorphism`, `detZ_modularJ_invariant` |
| determinant RN factor | `flowRelativeVolumeRN` | `flowRelativeVolumeRN_comp`, `RN_of_detSimilitude` |
| finite Euler boson/fermion pair | `Z_B`, `Z_F`, `Z_μ` | `boson_signed_closure`, `fermion_signed_second_order` |
| Möbius parity on squarefree states | `mobiusReadout = fermionParity` | `mobius_squarefree_parity` |
| finite Coulomb/Dyson potential | `dyson_hamiltonian` | `finite_dyson_vandermonde_potential` |
| collision/exclusion locus | `det(V)=0` | `finite_vandermonde_zero_iff_collision` |

## 8. Publication theorem statement currently supported

A theorem-honest publication statement can be formulated as:

**Theorem inventory.**  In the current Lean development there is a finite,
coordinate-level Zorn split-octonion algebra with determinant `detZ` and product
`mulZ` such that:

\[
\det_Z(XY)=\det_Z(X)\det_Z(Y),
\]

\[
[X,Y,Z]\ne0
\]

for an explicit basis triple,

\[
J^2=1,
\qquad
J(XY)=J(Y)J(X),
\qquad
\det_Z(JX)=\det_Z(X),
\]

and determinant-ratio factors satisfy the algebraic RN cocycle law.  The primon
finite Euler layer supplies exact boson/signed-fermion cancellation,
Möbius-squarefree parity, Gibbs free-energy minimization under the stated
relative-entropy hypotheses, finite Vandermonde collision/exclusion, and finite
Dyson/Vandermonde potential identities.

## 9. Explicit next theorem targets

The following statements are natural next formalization targets because the
inventory above supplies their algebraic ingredients as separate checked layers.

### 9.1 Analytic Tomita realization of `modularJ`

Data required:

\[
(M,\varphi,H,J_{TT},\Delta)
\]

with Tomita--Takesaki hypotheses and a map

\[
\iota:\operatorname{SplitOct}\to M.
\]

Target equation:

\[
J_{TT}(\iota X)=\iota(JX).
\]

### 9.2 Lie-group automorphism classification

Data required:

\[
\operatorname{Aut}(\mathbb O_s),\quad G_{2(2)},\quad
\operatorname{Lie}(\operatorname{Aut}(\mathbb O_s)).
\]

Target equations:

\[
\operatorname{Aut}(\mathbb O_s)\cong G_{2(2)},
\]

\[
\mathfrak{der}(\mathbb O_s)\cong\mathfrak g_{2(2)}.
\]

### 9.3 Zorn spectral/Fredholm truncation layer

Data required:

\[
\operatorname{tr}_Z,
\quad
\operatorname{char}_Z(t),
\quad
\operatorname{Fredholm}_Z(t).
\]

Target equations:

\[
X^2-\operatorname{tr}_Z(X)X+\det_Z(X)1=0,
\]

\[
\operatorname{Fredholm}_Z(t)=1-t\operatorname{tr}_Z(X)+t^2\det_Z(X)
\]

on the chosen associative/alternative sub-surface where the expression is
well-typed and checked.

### 9.4 Parabolic modular-time specialization

Data required:

\[
N^2=0,
\qquad
\Phi_t=1+tN.
\]

Target equations:

\[
\Phi_{s+t}=\Phi_s\Phi_t,
\]

\[
\det_Z(\Phi_t X)=\det_Z(X)
\]

for a concrete action of the nilpotent shear on the Zorn carrier.

### 9.5 Zeta-zero analytic bridge

Data required:

\[
\zeta(s),\quad \rho\in\mathbb C,\quad \zeta(\rho)=0,
\quad \Re(\rho)=1/2,
\]

and a proved map from analytic zero data into the finite Vandermonde/Dyson node
system.  The existing finite theorem supplies

\[
\det V(v)=0\Longleftrightarrow\text{collision},
\]

and

\[
H_{\mathrm{Dyson}}=E_{\mathrm{ext}}-\log|\Delta|^2.
\]

The analytic bridge target is the construction of the node map and its spectral
or asymptotic hypotheses.
