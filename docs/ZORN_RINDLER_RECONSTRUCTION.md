# Zorn pinors, Rindler coordinates, and semiconductor band bending

## Status and scope

This change reconstructs the supplied Zorn code and Bulgarian physics stream.
The source's algebraic content is separated from its physical interpretations.
It adds eight Lean source modules, with 112 theorem statements and complete
proof scripts, on the existing repository owners and the pinned Mathlib.

**Lean elaboration and kernel verification have not been performed here.**
The authoring container has no Lean/Lake executable. The supplied check exits
with status 2 in that environment. All 52 exact symbolic regressions pass;
Python and Bash syntax checks pass. These are independent diagnostics, not
proof certificates accepted by Lean. Keep the pull request draft until a
successful exact-head build and transitive axiom readback are available.

No new `sorry`, `admit`, custom `axiom`, `unsafe`, or `native_decide` declarations
are introduced. This is a source-level statement; the transitive dependency
claim is deliberately deferred to the included axiom audit. No dependency pin,
existing owner, existing aggregate, or CI workflow is changed.

## 1. Existing carriers and the source sign convention

Use `InfoGeometry.Algebra.ZornVec3 ℝ = Fin 3 → ℝ` and
`InfoGeometry.Algebra.ZornVectorMatrix ℝ`, not a new Vec3 or octonion type.
The repository product has upper cross term `-w × w'` and lower cross term
`+v × v'`; the submitted code has the opposite signs.

The linear involution F(a,v,w,b)=(a,-v,-w,b) satisfies

    F(X sourceProduct Y) = mul(F X, F Y),
    norm(F X) = norm X.

`orientation_sourceProduct` and `orientation_norm` implement these facts. F is
an isomorphism between the two presentations, not an automorphism of a single
fixed product. The transported source generators are

    c(u)=(0,-u,0,0), a(u)=(0,0,-u,0),
    gamma(u)=c(u)-a(u), kappa(u)=c(u)+a(u).

The native owner supplies the complementary diagonal elements E11 and E22.
They never become equal: `poles_distinct` is an explicit coordinate obstruction
to the proposed horizon interpretation E11=E22.

`gamma_product` proves for arbitrary real vectors

    gamma(u) gamma(v) = -dot(u,v) 1 + gamma(u × v).

The actual Mathlib quaternion carrier `Quaternion ℝ` embeds injectively by
q ↦ (re q,-im q,+im q,re q), with its multiplication preserved. Associativity
is proved on that image without installing an associative multiplication on
all Zorn elements. The relations of Q8 are visible in this quaternion sector,
but no Pin group or Clifford grading is obtained merely by assigning that
name to the three imaginary units. In particular their element volume is -1;
the submitted code does not distinguish the full odd Clifford volume.

## 2. From nonassociative elements to genuine associative CAR

The native operator target is `Module.End ℝ (ZornVectorMatrix ℝ)`. The curried
left multiplication L is linear and injective, but not multiplicative:
`leftMultiplication_not_multiplicative` gives an explicit counterexample.
Even the quaternion identity between the three elements does not imply the
same equality for their left actions on the entire octonion module; see
`gamma_operator_product_ne`.

The correct bridge is the existing left-alternativity theorem:

    L_X L_X = L_(XX).

Polarization gives

    L_X L_Y + L_Y L_X = L_(XY+YX).

This yields the ordinary associative CAR for R(u)=L_c(u), A(u)=L_a(u):

    R(u)R(v)+R(v)R(u)=0,
    A(u)A(v)+A(v)A(u)=0,
    R(u)A(v)+A(v)R(u)=dot(u,v) Id.

`splitBilin.toQuadraticMap` constructs the native quadratic form
Q(u,v)=dot(v,v)-dot(u,u). `cliffordVector(u,v)=gamma(u)+kappa(v)` squares to
Q(u,v)1, and alternativity gives its operator square. The actual universal
property `CliffordAlgebra.lift` then constructs

    CliffordAlgebra splitQuadratic →ₐ[ℝ] Module.End ℝ Z.

This is an algebra representation of the six-dimensional split quadratic
carrier. It is not an octonion algebra homomorphism and does not assume a
classification of Cl(3,3), faithfulness, or a Pin action.

The adjoint is also explicit rather than rhetorical. The positive native
bilinear coefficient pairing is

    <X,Y> = Xa Ya + Xb Yb + dot(Xv,Yv) + dot(Xw,Yw).

Its diagonal is nonnegative and vanishes exactly at zero. It is distinct from
the split multiplicative Zorn norm. `raise_lower_adjoint` proves

    <R(u)X,Y> = <X,A(u)Y>.

The number operator R(u)A(u) has nonnegative quadratic form and is idempotent
when dot(u,u)=1. No C*-completion or complex Fock equivalence is asserted.

## 3. Rindler coframe, acceleration and flatness

Use c=hbar=k_B=1, a>0, and N(x)=1+ax>0. The existing positive-radius
`Dynamics.RindlerWedge.RindlerCoordinates` is reused with

    r=x+1/a, rapidity=a*t.

Native `HasDerivAt` proofs supply all four partial derivatives of
T=r sinh(at), X=r cosh(at). Their Jacobian pulls back the Minkowski metric to
-N² dt²+dx² and has determinant N. The unchanged transverse Euclidean
directions may be appended; this PR computes the nontrivial (t,x) plane.

The stationary proper acceleration is a/N, not the same constant at all x:

    (log N)'=a/N, (a/N)'=-(a/N)².

The normalized hyperbolic velocity and its proper-time derivative have norms
-1 and r^(-2), respectively. Thus fixed-radius observers are accelerated,
not Minkowski geodesics. Minus the log gradient is the opposite, gravitational
force sign convention, not the support acceleration of a stationary observer.

For metric diag(-1,1), the mixed Lorentz connection is

    omega^0_1=omega^1_0=a dt.

Its lowered matrix is antisymmetric; the mixed matrix need not be Euclidean
skew. `connectionForm` uses the existing Cl11Matrix.J1 and satisfies the
native matrix compatibility identity omega^T eta + eta omega = 0.
The time torsion equation is represented in a native bilinear alternating
area form using the already-proved derivative N'. The coordinate curvature
d(omega)+omega wedge omega is zero, with `fderiv` applied to the constant
connection coefficients. This is a vector-frame connection calculation;
a spinor connection requires a specified spin representation and normalization.
It is not an electrochemical-potential gradient by definition.

## 4. Clock normalization is not a substitute for a modular theorem

For Euclidean polar angle theta=a*tau, a full 2*pi turn has coordinate period
beta_t=2*pi/a. In a positive boost convention, rapidity=2*pi*s, hence

    s=a*t/(2*pi),

not 2*pi*a*t. With Delta^(is)=exp(-is K_mod), K_mod=2*pi B and a physical
boost exp(+iat B), the orientation instead gives s=-at/(2*pi).

The formal endpoint is the real normalization identity, not an assertion
that an unspecified state has this modular generator. The vacuum wedge
statement is the Bisognano--Wichmann/QFT input discussed in [1, section 3.9].
Its analytic and state hypotheses are not introduced as a premise that hides
an unproved target. The new code does not assert that theorem.

The local redshift identity is Tlocal*N=T0. Substituting T0=a/(2*pi) gives
Tlocal=(a/N)/(2*pi). In physical units k_B*T_U=hbar*a_proper/(2*pi*c).
A regular Euclidean extension and the Minkowski vacuum select the Unruh
normalization; an arbitrary semiconductor is not assigned that temperature.

## 5. Electron bands, Nambu doubling and scalar shifts

The native Hermitian two-band electron matrix is

    H(b,m,d) = [[b+m,d],[conj d,b-m]], b=-e*phi.

Its centre is b and the characteristic determinant is

    det(H-E Id)=(b-E)²-(m²+|d|²).

The two real roots are b±sqrt(m²+|d|²), and their difference is independent
of b. The bare diagonal splitting 2m is not the hybridized gap when d≠0.
`lapse_not_affine` proves that N*H(0,m,d)=H(b,m,d), for m≠0, forces N=1 and
b=0. This exact counterexample already excludes the claimed universal
identification of lapse rescaling with scalar band bending.

The derivative of b=-e*phi is eE when E=-phi'. This electric field is a
separate structure from the Lorentz connection. A two-band electron basis is
not a Nambu electron-hole basis: the latter has a particle-hole constraint
and opposite electron/hole diagonal shifts, as illustrated in [2].

At a fixed momentum, with C=tau_x conjugation, the stated 2x2 block satisfies
C H C^-1=-H exactly when b=0 and d=0. This is the scope of
`same_point_particleHole_iff`, not a no-superconductivity theorem. Momentum
reversal or a larger spin block changes the constraint. They must be modeled
explicitly instead of importing the fixed-point conclusion into those cases.

## 6. Charge sign, dopants, Poisson and the allowed analogue

For the nondegenerate Boltzmann model [3], define eta=(EF-Ei)/(k_B T):

    n=ni exp(eta), p=ni exp(-eta), np=ni²,
    rho_intrinsic=e(p-n)=-2e ni sinh(eta).

The submitted plus sign is incorrect. The derivative with respect to eta is
-2e ni cosh(eta). Ionized dopants enter separately as e(ND+ - NA-).
Intrinsic neutrality is eta=0; with Ei=-e*phi this means phi=-EF/e. This
neither closes the spectral gap nor merges the two algebraic projectors.

A constant-charge solution is constructed explicitly:

    phi=c0+c1*x-rho*x²/(2 eps), E=rho*x/eps-c1,
    eps*E'=rho, phi''=-rho/eps.

The exact nonlinear Poisson--Boltzmann boundary-value problem remains a
separate development. In particular no equality between Newtonian Poisson,
semiconductor Poisson, and flat Rindler geometry is asserted.

A restricted analogue can be CHOSEN: phi=c log N. Then E=-c*a/N, while the
charge required by electrostatic Gauss law is

    rho=eps*c*(a/N)².

The code proves this value and its positivity on the positive parameter
domain. The Rindler connection remains flat. This supplies an explicit
comparison and a counterexample to identifying electrostatic charge with
Rindler curvature. It is not claimed that these prescribed profiles also
solve the semiconductor charge constitutive equation.

## Entry points and validation

    import InfoGeometry.Canonical.ZornRindlerReconstruction

Run in the repository with its existing dependencies and build coordinator:

    bash scripts/quality/check_zorn_rindler_reconstruction.sh

The script calls the existing locked narrow-build owner, then runs the
112-theorem `#print axioms` audit sequentially. It rejects missing readbacks
and any axiom other than propext, Classical.choice or Quot.sound. It does not
call lake update or remove a build cache. Respect the repository's idle-build
precondition before starting the script.

Symbolic reproduction, explicitly outside the Lean trust boundary:

    python3 tools/sympy/check_zorn_rindler_reconstruction.py

## Exact next developments, not assumptions in this PR

1. Complete exact-head Lean checking and repair any elaboration errors.
2. Prove faithfulness/surjectivity of the six-generator Clifford action and
   compare its positive adjoint representation with the existing Fock owner.
3. Install the manifold/spin-connection layer above the coordinate results.
4. Develop a self-consistent Poisson--Boltzmann boundary-value problem and an
   explicit semiconductor kinetic operator before claiming an analogue map.
5. Develop the state, locality, spectrum and analyticity hypotheses needed for
   a genuine modular/Unruh theorem. No Zener--Unruh radiation equality follows
   from the present finite algebra or coordinate formulas.

## External primary references used for the physical audit

[1] H. Casini and M. Huerta, *Lectures on entanglement in quantum field theory*,
section 3.9, equations (3.43)--(3.47), arXiv:2201.13310v2 (2023).
https://arxiv.org/pdf/2201.13310

[2] TU Delft, *Topology in condensed matter*, "Bulk-edge correspondence in the
Kitaev chain", sections on momentum-space particle-hole symmetry, especially
H(k)=-tau_x H*(-k) tau_x and the chemical-potential term proportional to tau_z.
https://topocondmat.org/w1-topointro/d-1

[3] P. Hehenberger, doctoral dissertation, appendix B.1, *Surface Space Charge
Region of an n-Type MOS Capacitor*, equations (B.1)--(B.4), (B.8)--(B.9).
https://www.iue.tuwien.ac.at/phd/hehenberger/dissse52.html
