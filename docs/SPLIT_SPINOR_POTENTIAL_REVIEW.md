# Split Cartan spinors, para-Kähler potentials, and thermodynamics

## Result and proof boundary

The exterior Clifford construction is sound. The proposed universal
chirality polarization, real Krein diagonal potential, real skew-generator
charge, and rescaled fundamental symmetry are not. The corrected geometric
construction can be related to a statistical potential after choosing an
actual map of parameter spaces and proving nondegeneracy. Thermodynamic
normalization and positive dissipation are additional requirements.

Four new Lean owners extend the existing repository. They retain native
exterior algebras, algebraic duals, arbitrary endomorphism composition, and
native derivatives. The Mukai parity classification and the explicit quantum
example below are mathematical derivations/literature-supported analysis;
they are not claimed as new kernel-checked theorems in this patch.

## 1. Keep the carriers distinct

Let `dim W = n ≥ 1` and set `V = W ⊕ W*`. The vector metric is

\[
h((w,\alpha),(v,\beta))
=\tfrac12(\alpha(v)+\beta(w)),\qquad q(w,\alpha)=\alpha(w).
\]

The spinor carrier is `S = Λ W`, of dimension `2^n`. Its creation and
annihilation operators satisfy the genuine ordered CAR:

\[
\varepsilon_w\varepsilon_v+\varepsilon_v\varepsilon_w=0,\quad
\iota_\alpha\iota_\beta+\iota_\beta\iota_\alpha=0,\quad
\iota_\alpha\varepsilon_w+\varepsilon_w\iota_\alpha=\alpha(w)I.
\]

Thus `c(w,α)=ε_w+ι_α` obeys `c(w,α)^2=q(w,α)I`. The existing
`InfoGeometry.Clifford.abstractSpinorRep` in `ChevalleySpinorBlueprint` already implements the native
Clifford universal property. The new `ChevalleyNeutralCompatibility` connects
it to the neutral-form and Kähler–Atiyah owners and proves a noncommutation
witness. It does not replace the existing representation.

An isotropic polarization of **S** is a further construction. It is not the
same object as the original polarization of **V**.

## 2. Mukai pairing and the parity obstruction

Choose a nonzero volume trivialization `Λ^n W ≅ ℝ`; without it the pairing
is top-form-valued. Let

\[
B(s,t)=[\tau(s)\wedge t]_{\mathrm{top}},\qquad K=(-1)^{\deg}.
\]

The elementary degree calculation gives

\[
B(t,s)=(-1)^{n(n-1)/2}B(s,t),\qquad
B(Ks,Kt)=(-1)^n B(s,t).
\]

Only degrees summing to `n` pair. Consequently:

| n mod 4 | B | Nonzero chirality pairings | Construction using chirality |
|---|---|---|---|
| 0 | symmetric | same chirality | not a neutral polarization |
| 1 | symmetric | opposite chirality | g=B, ω=B(K·,·) |
| 2 | alternating | same chirality | not a Lagrangian polarization |
| 3 | alternating | opposite chirality | ω=B, g=B(K·,·) |

For even `n`, inserting `K` cannot turn the chirality splitting into dual null
factors: it preserves the symmetry type of `B`. Additional polarization data
are required. A universal alternative `L ⊕ L*` is possible, but its dimension
and relation to the original spinor representation must be stated.

For `n=2`, in the basis `(1,e12;e1,e2)`, the Mukai matrix is
`diag(ε,ε)` with `ε=[[0,1],[-1,0]]`. Each chirality is symplectic, and the
cross-chirality pairing is zero.

For `n=3`, with `vol=e1∧e2∧e3`, take

\[
p=(1,e_{23},e_{31},e_{12}),\qquad
q=(\mathrm{vol},-e_1,-e_2,-e_3).
\]

Then `B(p_A,q^B)=δ_A^B`, `B(q^B,p_A)=-δ_A^B`, and both chiral self-pairings
vanish. This realizes a real `4+4` split spinor space.

Triality is the `n=4` case `Spin(4,4)`. The first nontrivial chiral pure-spinor
quadric has equation `2ac-[B₂∧B₂]_vol=0` for `a+B₂+c vol`.

## 3. Correct flat potential and Krein operators

On a justified polarization `L ⊕ L*`, use dual coordinates `(x,y)` and fix

\[
g((x,y),(u,v))=y(u)+v(x),\quad K(x,y)=(x,-y),\quad
\omega(U,V)=g(KU,V).
\]

Then

\[
\Psi_0(x,y)=x^Ay_A=\tfrac12g(\psi,\psi),\quad
\omega_0=\sum_A dx^A\wedge dy_A,\quad
g_0=\sum_A(dx^A\otimes dy_A+dy_A\otimes dx^A).
\]

The reconstruction sign is `g(U,V)=ω(KU,V)=-ω(U,KV)`. Choosing the opposite
symplectic convention is permitted only if every Hamiltonian sign changes
consistently.

The proposed expression `g(ψ,Kψ)/2` is zero, because symmetry and
`g(KU,KV)=-g(U,V)` imply `g(ψ,Kψ)=-g(ψ,Kψ)`. The new obstruction owner proves
this on the actual dual carrier. It also proves the second finite difference
of `Ψ₀` is `g`.

The factor `1/2` in the proposed `Ψ₀=(x·y)/2` is a legitimate alternate
normalization, provided both `g` and `ω` are also halved. The input vector
metric normalization `h=B/2` does not force the same normalization on the
separate spinor-space geometric potential.

After a positive inner product identifies the two coordinate factors, take

\[
J=\begin{pmatrix}0&I\\I&0\end{pmatrix},\qquad
K=\begin{pmatrix}I&0\\0&-I\end{pmatrix}.
\]

Here `J²=K²=I` and `JK=-KJ`. The `J` eigenspaces `(u,±u)` are definite;
the `K` eigenspaces are null. The expressions `(I±J)/√2` are scaled
projections, not an invertible basis rotation. The normalized block Hadamard
matrix transforms the diagonal neutral form into the cross-pairing form.

For a complex Hermitian Krein form and Krein-skew `K`, the form
`C(U,V)=[U,KV]` is anti-Hermitian. On the underlying real space `Re C` is
alternating and `Im C` is symmetric. Thus the proposed imaginary-part formula
does not provide the required real symplectic form.

## 4. A valid curved potential construction

Let `Ψ` be a sufficiently smooth real function on an open subset of
`ℝ^m × ℝ^m`, and write

\[
H_{AB}=\partial_{x^A}\partial_{y_B}\Psi.
\]

If `det H ≠ 0`, define

\[
\omega_\Psi=\sum_{A,B}H_{AB}dx^A\wedge dy_B,\quad
g_\Psi=\sum_{A,B}H_{AB}(dx^A\otimes dy_B+dy_B\otimes dx^A).
\]

Their matrices are `[[0,H],[-Hᵀ,0]]` and `[[0,H],[Hᵀ,0]]`. In particular
`H` need not itself be symmetric. Commuting partial derivatives gives
`dω=0`; the constant polarization is integrable; the metric has signature
`(m,m)`. This is a local para-Kähler construction. Adding a function only of
`x` or only of `y` does not change either mixed tensor.

One explicit bridge from a smooth parameter potential `f` is

\[
\Psi(x,y)=f(x+y).
\]

This uses a **chosen** identification of the two coordinate factors with the
parameter space. The new `ParaPotentialPullback` proves by native Fréchet
calculus that the mixed derivative is `Hess f(x+y)`. It proves the associated
mixed forms separate points when `Hess f` separates both variables. In an
infinite-dimensional normed space this is weak nondegeneracy, not a bounded
inverse onto the full continuous dual.

The ordinary full Hessian is the pulled-back form
`H(Ux+Uy,Vx+Vy)`. Its opposite-direction kernel differs from the neutral
mixed metric. The module proves invariance under `(x,y)↦(x+u,y-u)` and the
algebraic kernel identity for that pulled-back form; it does not bundle a
global para-Kähler manifold.

## 5. Noncommuting quantum example

Let

\[
Z=\begin{pmatrix}1&0\\0&-1\end{pmatrix},\quad
X=\begin{pmatrix}0&1\\1&0\end{pmatrix},\quad ZX=-XZ,
\]

and `A(θ)=θ₁Z+θ₂X`. Its log partition is

\[
f(\theta)=\log\operatorname{Tr}e^{A(\theta)}
=\log(2\cosh r),\quad r=\sqrt{\theta_1^2+\theta_2^2}.
\]

The Hessian eigenvalues are `sech²r` and `tanh(r)/r`, with both equal to one
at the origin by continuous extension. They are strictly positive at every
finite parameter. Therefore `Ψ(x,y)=f(x+y)` has a nondegenerate mixed metric
of signature `(2,2)`, and

\[
\det\Psi_{xy}=\operatorname{sech}^2r\,\frac{\tanh r}{r}.
\]

The observables remain noncommuting. Their quantum Hessian uses the
Bogoliubov–Kubo–Mori correlation, not a substitution of commuting random
variables. This statistical model is additional data, not automatically a
`Spin(n,n)`-equivariant Souriau model. Two independent tensor factors supply
four parameters and hence a mixed `4+4` coordinate model when desired.

This explicit example is derived mathematically and supported by Nakamura's
calculation. This patch formalizes the general pullback calculus, not the
matrix-exponential closed form or its Hessian spectrum.

## 6. Hamiltonian charges retain operator order

For an arbitrary endomorphism `A` of `L`, define

\[
L_A(x,y)=(Ax,-y\circ A),\qquad H_A(x,y)=y(Ax).
\]

The new owner constructs `μ(X)` as an actual linear functional on the entire
endomorphism algebra and proves

\[
H_A(X)=\tfrac12\omega(L_AX,X),\qquad
dH_A|_X(V)=\omega(L_AX,V),
\]

where the Lean derivative is a native `HasDerivAt` along every real affine
line. The exact polynomial underlying it is

\[
H_A(X+tV)=H_A(X)+t\omega(L_AX,V)+t^2H_A(V).
\]

It also proves

\[
[L_A,L_B]=L_{AB-BA},\qquad
\omega(L_AX,L_BX)=H_{AB-BA}(X).
\]

No commutativity assumption is imposed. In contrast, for real symmetric `g`
and a `g`-skew operator, `g(X,AX)=0`; that diagonal cannot be the proposed
nonconstant charge.

The functional has codomain `End(L)*`; a restriction to the Spin Lie algebra
and a proof of group equivariance are additional constructions.

## 7. Souriau normalization, entropy, and volume

For a specified Hamiltonian group action on a symplectic state space `M`,
with moment map `μ` and Liouville measure `λ`, the statistical object is

\[
Z(\beta)=\int_M e^{-\langle\mu(z),\beta\rangle}\,d\lambda(z),\quad
f=\log Z.
\]

One must establish a nonempty domain with `0<Z<∞` and the differentiation
hypotheses. Then `-df=Eβ μ`, `Hess f=Covβ(μ)` in the classical setting, and
dimensionless Gibbs entropy is

\[
s=f+\langle\beta,E_\beta\mu\rangle
=f-\langle\beta,df\rangle.
\]

Thus `β·df-f` is its negative, not the entropy. A geometric potential has no
automatic statistical entropy interpretation. For the chosen bridge
`Ψ=f(x+y)`, the proposed joint coordinate expression also equals `-s`.
Its two gradients coincide after identifying the factors, so their joint
map is not an invertible `2m`-dimensional Legendre correspondence.

For `m>0`, the flat integral `∫ exp[-y(Ax)] dx dy` on the entire split carrier
diverges for every `A`: integration in `y` already diverges for every fixed
`x`. A lower-dimensional orbit needs its own intrinsic symplectic volume,
not the ambient top-degree volume restricted to it.

Writing `log det Ψ_xy` inside the definition of `Ψ` is an implicit equation.
An external volume factor pulls outside an integral; it does not solve the
equation. Positive volume densities satisfy

\[
\frac{d\lambda_\Psi}{d\lambda_0}
=\frac{|\det H|}{|\det H_0|}.
\]

For `Ψ₀=x·y`, `H₀=I`. For the input's `Ψ₀=(x·y)/2`, `H₀=I/2`, so on the
positive determinant branch the prescribed-volume equation is
`det H=2^{-m}e^σ`. Finite relative change is `e^σ-1`; infinitesimal change is
`δ log λ=tr(H⁻¹δH)`.

## 8. Dissipation and Landauer require a process

Applying the proved scalar-rescaling obstruction to `c=exp(σ/2)` gives
`J'=e^{σ/2}J` with square `e^σI`, so it cannot remain an involution unless
`σ=0`. This exponential specialization is a mathematical consequence, not a
separate kernel theorem in this patch. Scaling both the Krein form
and its associated positive Hilbert form can keep `J` fixed. With fixed
`K`, a conformal metric scaling gives `ω'=e^fω`; in dimension at least four,
closedness requires `df=0`. Arbitrary local conformal rescaling therefore
does not preserve para-Kähler geometry.

Krein self-adjointness also does not imply positivity of a Gibbs state.
For `J=diag(1,-1)`, the real matrix `[[0,1],[-1,0]]` is Krein self-adjoint
but has imaginary eigenvalues.

Standard metriplectic data require an extra positive semidefinite map `M`
and the degeneracy identities `P dS=0`, `M dE=0`. If `P` is invertible,
then `dS=0`. This conditional obstruction is already present in
`Thermo.GenericMetriplecticFlow`; its source was reviewed. It is not a new
construction of dissipation from volume.

A consistent extension adds an entropy coordinate `s`, takes total energy
`E=H(z)+Ts`, `T>0`, and chooses a positive Hilbert gradient `u=∇H`. For
`γ≥0`, set

\[
M=\gamma\begin{pmatrix}TI&-u\\-u^T&\|u\|^2/T\end{pmatrix}.
\]

Its quadratic form is `γT‖v-(a/T)u‖²`; it annihilates `dE`. The resulting
equations `ż=X_H-γ∇H`, `ṡ=γ‖∇H‖²/T` conserve total energy and produce
entropy. Choosing `γ` from a volume field is a constitutive assumption.

Landauer's bound uses heat into a thermal reservoir and entropy removed from
the system. Under the usual initially uncorrelated, thermal-reservoir,
joint-unitary assumptions, in units `k_B=1`,

\[
\beta Q= s(\rho_S)-s(\rho'_S)
+I(S':R')+D(\rho'_R\Vert\rho_R)
\ge s(\rho_S)-s(\rho'_S).
\]

Neither a determinant deformation nor a Krein rescaling supplies those
process assumptions or the proposed general Lie-valued heat bound.

Finally, for odd `n` the restriction of the flat symplectic form to a single
chiral pure-spinor cone is zero. For `n=3` its projectivization is `ℝP³`,
which is odd-dimensional. A projective restriction needs a separately
constructed reduction/contact/symplectic geometry.

## Primary references

1. [Gualtieri, Generalized complex geometry, §§1.3–1.5](https://www.math.utoronto.ca/mgualt/gcg/gcg.pdf).
2. [Hitchin lectures, notes by Gualtieri, Low-dimensional geometry, pp.16–17](https://www.math.toronto.edu/mgualt/courses/19-1312/docs/Lowdimgeom.pdf).
3. [Bor–Makhmali–Nurowski, Para-Kähler-Einstein 4-manifolds, Proposition 2.14](https://users.fuw.edu.pl/~nurowski/prace/para_kahler_published.pdf).
4. [Marle, On Gibbs States of Mechanical Systems with Symmetries, §§3.1–3.2](https://marle.perso.math.cnrs.fr/pdffiles/2020/GibbsStatesJGSPPart1.pdf).
5. [Nakamura, Scalar Curvature of the Quantum Exponential Family, §§2–3](https://arxiv.org/pdf/2212.12919).
6. [Bloch–Morrison–Ratiu, Gradient flows and metriplectic systems, §4.1](https://web2.ph.utexas.edu/~morrison/12arXiv1208.6193_morrison.pdf).
7. [Reeb–Wolf, An improved Landauer Principle, §2.1 and Theorem 3](https://arxiv.org/pdf/1306.4352).

See `SPLIT_SPINOR_POTENTIAL_CONTRACT.md` for the precise theorem contracts and
`SPLIT_SPINOR_POTENTIAL_VERIFICATION.md` for actual validation scope.
