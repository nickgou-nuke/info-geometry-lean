# 193. Real Split Clifford and the Drazin-Schur Bridge

The clean way to state the whole structure is: these are not all the same object, but they are linked by a small set of exact representations and quotient maps.

$$
C\ell(n,n)\cong M_{2^n}(\mathbb R)
$$

is the real split Clifford tower, while

$$
\mathbb H_{\mathbb C}:=\mathbb C\otimes_{\mathbb R}\mathbb H\cong M_2(\mathbb C)
$$

is the Pauli/biquaternion algebra that carries the spinor model of Minkowski space. Gallier’s Clifford notes explicitly give $C\ell_{1,1}\cong M_2(\mathbb R)$, the recurrence $C\ell_{p+1,q+1}\cong C\ell_{p,q}\otimes C\ell_{1,1}$, and $\mathbb C\otimes_{\mathbb R}\mathbb H\cong M_2(\mathbb C)$. 

So:

$$
C\ell(1,1)\cong M_2(\mathbb R),
$$

$$
C\ell(2,2)\cong M_4(\mathbb R),
$$

$$
C\ell(4,4)\cong M_{16}(\mathbb R).
$$

But one should keep the roles distinct. $C\ell(2,2)\cong M_4(\mathbb R)$ is a split real matrix model. Physical spacetime algebra is usually $C\ell(1,3)$ or $C\ell(3,1)$, depending on sign convention. Its even subalgebra is the Pauli/biquaternion algebra:

$$
C\ell^+(1,3)\cong C\ell(3,0)\cong M_2(\mathbb C).
$$

That is the precise location where Hestenes STA, Pauli spinors, biquaternions, and $SL(2,\mathbb C)$ meet.

The central spinor-to-spacetime dictionary is:

$$
x=(t,x,y,z)
\quad\longmapsto\quad
X=x^\mu\sigma_\mu
=tI+x\sigma_1+y\sigma_2+z\sigma_3
=
\begin{pmatrix}
t+z & x-iy\\
x+iy & t-z
\end{pmatrix}.
$$

Then

$$
\det X=t^2-x^2-y^2-z^2.
$$

For $A\in SL(2,\mathbb C)$,

$$
X\mapsto X'=AXA^\dagger
$$

preserves the determinant and therefore induces a proper orthochronous Lorentz transformation on $x^\mu$. The map $SL(2,\mathbb C)\to SO^+(1,3)$ is two-to-one, since $A$ and $-A$ give the same Lorentz transformation. 

The exact $2\times2\to4\times4$ extraction formula is:

$$
\Lambda^\mu{}_\nu(A)
=
\frac12\operatorname{tr}\left(\sigma_\mu A\sigma_\nu A^\dagger\right),
$$

with

$$
x'^\mu=\Lambda^\mu{}_\nu(A)x^\nu.
$$

Equivalently, using column vectorization,

$$
\operatorname{vec}(AXA^\dagger)
=
(A^*\otimes A)\operatorname{vec}(X).
$$

If

$$
\operatorname{vec}(X)
=
S
\begin{pmatrix}
t\\x\\y\\z
\end{pmatrix},
\qquad
S=
\begin{pmatrix}
1&0&0&1\\
0&1&i&0\\
0&1&-i&0\\
1&0&0&-1
\end{pmatrix},
$$

then

$$
\Lambda(A)=S^{-1}(A^*\otimes A)S.
$$

That is the explicit flattening of the $2\times2$ spinor action into the standard $4\times4$ Lorentz action.

The biquaternion zero-divisor correction is important. The real quaternions ($\mathbb H$) are a division algebra, but the biquaternions are not:

$$
\mathbb H_{\mathbb C}\cong M_2(\mathbb C).
$$

The zero divisors of $M_2(\mathbb C)$ are precisely the nonzero singular complex matrices. But the null cone is not all of that zero-divisor variety. The precise statement is:

$$
\boxed{
\text{null Minkowski vectors}
=
\{\text{singular Hermitian }2\times2\text{ matrices}\}.
}
$$

So the null cone is the intersection of the biquaternionic zero divisors with the Hermitian Minkowski slice.

For a nonzero Hermitian $X$,

$$
\det X=0
$$

means $X$ has rank one. Hence it factors as a spinor dyad:

$$
X^{AA'}=\lambda^A\bar\lambda^{A'}
$$

for the future null cone, up to an overall real sign for the past cone. This is the algebraic seed of the twistor incidence picture: null directions are spinor projective lines, and spacetime points are encoded by incidence relations among such spinors.

The Jones-calculus identification is then almost literal. A Jones vector is a two-component complex spinor,

$$
E=
\begin{pmatrix}
E_x\\E_y
\end{pmatrix},
$$

and its coherency matrix

$$
\rho=EE^\dagger
$$

expands as

$$
\rho=\frac12(S^0I+S^1\sigma_1+S^2\sigma_2+S^3\sigma_3).
$$

A deterministic nondepolarizing optical element acts by

$$
\rho\mapsto J\rho J^\dagger.
$$

If $J\in SL(2,\mathbb C)$, the induced Stokes transformation is Lorentz. If $J\in GL(2,\mathbb C)$, the Lorentz transformation is accompanied by an overall intensity scale. The optics literature explicitly states this: Jones matrices form a two-by-two representation of the Lorentz group, Jones vectors behave like spinors, and Stokes parameters behave like Minkowski four-vectors. ([arXiv][1])

In STA, the same structure becomes coordinate-free. A spacetime vector is

$$
x=t\gamma_0+x\gamma_1+y\gamma_2+z\gamma_3,
$$

with

$$
\gamma_0^2=1,\qquad \gamma_i^2=-1.
$$

Then the interval is simply

$$
x^2=t^2-x^2-y^2-z^2.
$$

A Lorentz transformation is represented by a rotor $R$:

$$
x\mapsto x'=Rx\widetilde R,
\qquad
R\widetilde R=1.
$$

Hestenes states this rotor form directly and identifies the rotor group as a double-valued representation of the restricted Lorentz group. ([David Hestenes Archive][2])

The Cartan split in STA should be stated carefully. Reversion is not the Cartan involution. Reversion sends every bivector to its negative:

$$
\widetilde B=-B.
$$

The Cartan involution relative to the observer $\gamma_0$ is better written as

$$
\theta(B)=\gamma_0 B\gamma_0.
$$

For boost bivectors

$$
K_i=\gamma_i\gamma_0,
$$

one gets

$$
\theta(K_i)=-K_i.
$$

For spatial rotation bivectors

$$
J_i=\gamma_j\gamma_k,
$$

one gets

$$
\theta(J_i)=J_i.
$$

Thus

$$
\mathfrak{so}(1,3)=\mathfrak k\oplus\mathfrak p,
$$

where

$$
\mathfrak k=\operatorname{span}\{\gamma_2\gamma_3,\gamma_3\gamma_1,\gamma_1\gamma_2\}
$$

generates spatial rotations, and

$$
\mathfrak p=\operatorname{span}\{\gamma_1\gamma_0,\gamma_2\gamma_0,\gamma_3\gamma_0\}
$$

generates boosts. This is the geometric-algebra version of the matrix split into skew-Hermitian rotation generators and Hermitian boost generators.

The Schur/Cartan/Drazin thread should also be slightly sharpened. For a complex matrix $A$,

$$
A=K+P,
\qquad
K=\frac12(A-A^*),
\qquad
P=\frac12(A+A^*),
$$

is the Lie-algebra Cartan decomposition into skew-Hermitian and Hermitian parts. The matrix is normal exactly when these two parts commute:

$$
A^*A=AA^*
\quad\Longleftrightarrow\quad
[K,P]=0.
$$

Schur decomposition gives

$$
A=QTQ^*,
$$

with $T$ upper triangular. If $A$ is normal, $T$ is diagonal. If $A$ is non-normal, the strictly upper-triangular part of $T$ measures the departure from normality. More exactly, if $T=D+N$, with $D$ diagonal and $N$ strictly upper triangular, then

$$
|N|_F^2
=
|A|_F^2-\sum_i|\lambda_i|^2.
$$

So the “Schur shear” is not merely metaphorical; in Frobenius norm it is an exact non-normality measure.

Iwasawa decomposition is related but not identical to Schur. Schur is unitary similarity:

$$
A=QTQ^*,
$$

so the diagonal of $T$ contains eigenvalues. Iwasawa/QR is a factorization:

$$
A=KAN,
$$

where $K$ is unitary or orthogonal, $A$ is positive diagonal, and $N$ is unit upper triangular. Its diagonal part is not generally the eigenvalue list. Thus Iwasawa unifies compact, Abelian, and nilpotent directions, but it does not replace Schur as a spectral triangularization.

For the Drazin inverse, the Schur form is the stable numerical route. After reordering the Schur form,

$$
T=
\begin{pmatrix}
T_1 & C\\
0 & T_0
\end{pmatrix},
$$

where $T_1$ contains the nonzero spectrum and $T_0$ contains the zero spectrum. If $T_0$ is nilpotent, one solves a Sylvester equation to remove $C$ by similarity. In the decoupled basis,

$$
T\sim
\begin{pmatrix}
T_1&0\\
0&T_0
\end{pmatrix},
$$

and the Drazin inverse is

$$
T^D\sim
\begin{pmatrix}
T_1^{-1}&0\\
0&0
\end{pmatrix}.
$$

So the Drazin inverse is the spectral inverse on the nonzero Riesz component and zero on the nilpotent component. The Moore–Penrose inverse instead comes from orthogonal range/nullspace geometry. Schur is the computational bridge; it preserves metric stability through unitary transformations while exposing the spectral data needed by Drazin theory.

The final compressed statement is:

$$
\boxed{
\begin{aligned}
C\ell(n,n)&\cong M_{2^n}(\mathbb R),\\
\mathbb H_{\mathbb C}&\cong M_2(\mathbb C),\\
x^\mu\sigma_\mu&\leftrightarrow \text{Hermitian }2\times2\text{ matrix},\\
\det(x^\mu\sigma_\mu)&=x_\mu x^\mu,\\
SL(2,\mathbb C)/\{\pm I\}&\cong SO^+(1,3),\\
X\mapsto AXA^\dagger&\leftrightarrow \text{Lorentz/Jones/Stokes action},\\
\det X=0&\leftrightarrow \text{null vector/rank-one spinor dyad}.
\end{aligned}
}
$$

The only essential correction is that biquaternions do have zero divisors; the physically significant statement is that their singular Hermitian elements are precisely the null vectors of Minkowski space.

[1]: https://arxiv.org/pdf/physics/9707016 "arXiv:physics/9707016v1  [physics.optics]  20 Jul 1997"
[2]: https://davidhestenes.net/geocalc/pdf/SpaceTimeCalc.pdf "SpaceTimeCalc.pdf"