# Coupled real exponentials and finite divergence geometry

## Intake and source authority

This follow-up starts from upstream PR #419, source commit
8aa3a5ba924ac451e069e1a60c4e5dc0bcd02136, tree
920c52faed4d5611ce6d2e883293de8a6ac4a382. The local starting commit
a42dbde657a019bc5b53c44cf2466a91af47f032 has that same tree.

The source is the user attachment Pasted text(20261120-141808).txt, SHA256
1d5729c0c6fd280ba2e147ff13f867111b7cc28bd36d205a6183929b0c15b162.
The original attachment is preserved separately from this corrected contract.
Its claims are mathematical intake, not evidence that a theorem is present or
that an earlier source audit remains current.

## Existing owners retained

The attachment proposes three bridges and one differential-geometric extension.
Two bridges, and the directional-derivative part of the extension, already exist.

| Intake claim | Actual existing owner and scope |
| --- | --- |
| Relative modular logarithm and quantum generalized KL | Canonical/MatrixRelativeModular.lean constructs the full vectorized matrix operator, proves native CFC positivity and logarithm, and proves the actual square-root-state expectation with both trace corrections. Its RCLike parameter includes real scalars. |
| Existing operator and thermodynamic consumers | Canonical/MatrixRelativeModularPhysicsBridge.lean identifies the regular bimodule action and IS expression and derives the generalized Gibbs balance. Canonical/MatrixRealificationThermodynamics.lean proves the encoded-real-sector compatibility. |
| Full-dimensional covariance scale and shape | Jordan/BurgStein.lean proves determinant normalization and the exact split. Canonical/GaussianBurgStein.lean proves both terms nonnegative using the actual scaled SPD source covariance and Probability/GaussianTraceLogdet.lean. |
| Derivatives of finite generalized KL | InformationGeometry/PositiveMeasureDifferential.lean proves first derivatives and genuine affine second derivatives of PositiveMeasure.gklTerm and its finite sum, with both arguments moving. |
| Block Gaussian factorization | NCG/BerezinianGaussianFactorization.lean proves the actual UDL identity over any associative coefficient ring, given a two-sided inverse of the lower-right block. |
| Algebraic neutral geometry | Canonical/ParaComplexConnectionBridge.lean owns the involution and Peirce projections. Canonical/ParaComplexNeutralForm.lean owns Datum and NondegenerateDatum, including isotropy and self-annihilator consequences. The opposite eigenspaces pair nondegenerately. Probability/FiniteWeightedSplitKreinAdjoint.lean owns the actual weighted symmetric and skew pairings and polarization. |

These results are reused rather than duplicated. The existing relative
distortion Y⁻¹X need not be symmetric when X and Y are SPD. Its normalized
shape is therefore not silently declared SPD. The existing Gaussian consumer
uses the actual SPD covariance s⁻¹X with the original reference Y.

## Corrected exponential contract

For a complete real normed associative algebra A, define convergent kernels

    F(Z) = Σ k≥0, Z^k / (2k)!
    G(Z) = Σ k≥0, Z^k / (2k+1)!.

The target is the actual native exponential identity

    exp(-H) = F(H²) - H G(H²).

Both kernels are defined by their convergent power series, including at zero;
F(0) = G(0) = 1. No matrix square root, inverse of a square root, positivity,
diagonalizability, or commutativity of the ambient algebra is assumed.

For full real matrix blocks U and V and a real scalar beta, use the existing
grading Gamma = diag(I,-I) and the actual matrix

    H = beta Gamma + [[0,U],[V,0]].

The required square is diag(beta² I + UV, beta² I + VU), with both product
orders retained. The kernel identity specializes to an explicit four-block
exponential. A common scalar identity component can be split using its proved
centrality. U and V are not required to commute.

For an arbitrary diagonal block B instead of beta I, the square has
off-diagonal entries BU-UB and VB-BV. Those defects must be retained unless
their vanishing is proved. Anticommutation with Gamma alone does not make a
noncentral coefficient beta commute with U and V.

The UDL specialization uses the existing factorization owner. When H is real
symmetric, exp(-H) is proved SPD and its lower-right principal block is proved
SPD and invertible. This supplies the actual pivot inverse. General invertible
exponentials do not have an automatically invertible diagonal block.

Parity of powers is distinct from Gamma-homogeneous block parity. The term
H G(H²) contains both its diagonal and off-diagonal components when beta is
nonzero; it is not described as an entirely odd block matrix.

## Corrected differential contract

On the finite positive cone, use the existing generalized-KL summands

    D(p,q) = Σ i, p_i log(p_i/q_i) - p_i + q_i.

The target is a native continuous-linear first derivative and a genuine
Frechet derivative of that first derivative. At coincidence p=q=r, the
bilinear Hessian must evaluate to

    Hess D[(u,v),(u',v')] = Σ i, (u_i-v_i)(u'_i-v'_i)/r_i.

Its negative mixed restriction is the Fisher form

    g_r(u,v) = Σ i, u_i v_i/r_i.

The full joint Hessian is positive semidefinite with diagonal kernel u=v.
It is not the neutral doubled metric. Construct that separate native bilinear
form explicitly as

    G_r((u,v),(u',v')) = g_r(u,v') + g_r(v,u'),
    K(u,v) = (u,-v).

The intended finite algebraic result constructs the existing
ParaComplexStructure, Datum, and NondegenerateDatum, proving K²=id,
symmetry, G(Kx,Ky)=-G(x,y), nondegeneracy, and cross-sheet nondegeneracy.
Its fundamental skew form is the existing weighted split symplectic pairing.
No manifold, differential-form
closedness, connection, integrability, or global para-Kahler geometry is
inferred from these fiberwise identities. The initial route through
FiniteParaKahler imported an unrelated unresolved Architect dependency;
the lighter canonical neutral-form owners supply exactly the needed laws.

## Rejected extrapolations and counterexamples

1. A general real positive square root of H² does not exist: beta=0, U=1,
   V=-1 gives H²=-I. Division by a square root is also invalid at zero.
2. Invertibility of exp(-H) alone does not provide the D pivot. A quarter-turn
   real exponential has zero diagonal blocks.
3. The homogeneous-even Berezinian exponential law does not extend to
   arbitrary ordinary-real coupled blocks. For H=[[0,1],[1,0]], the Schur
   determinant-ratio readout of exp(-H) is 1/cosh(1)², whereas exp(-str H)=1.
   The existing block-diagonal exponential law retains its original scope.
4. The abstract RelativeModularDatum multiplicative chain law is not a law
   of the actual full Hilbert-Schmidt relative modular family. The concrete
   matrix owners and their direct IS consumers remain separate from that
   supplied abstract datum.
5. A general Radon-Nikodym IS/KL identity needs absolute-continuity, mass,
   and integrability hypotheses. For P=delta_0 and Q=(delta_0+delta_1)/2,
   KL(P||Q)=log 2, but E_P phi(dQ/dP)=log 2-1/2. The finite strictly-positive
   measure lane does not encounter this singular-part obstruction.

## Verification scope

Generation, source audit, and final acceptance use distinct agents. Candidate
proofs are not acceptance evidence. The final record will report native source
compilation, axiom dependencies, selected-owner warnings, source-only heuristic
findings and their dispositions, exact source hashes, and hosted publication
results. Lean and Mathlib pins, validation helpers, and installed hooks remain
unchanged. The previously observed missing root path dependency is an
integration issue to report at its actual scope, not a reason to weaken proofs.

The companion verification record distinguishes native theorem acceptance
from repository integration and the explicit boundaries above.

## Mathematical references

- Prashanth Nadukandi and Nicholas J. Higham, *Computing the Wave-Kernel
  Matrix Functions*, SIAM Journal on Scientific Computing 40(6), 2018,
  A4060–A4082, [DOI 10.1137/18M1170352](https://doi.org/10.1137/18M1170352).
  The entire wave-kernel formulation motivates the root-free F and G series;
  the actual Lean statements prove convergence and the native exponential
  identity directly over a complete real normed algebra.
- Israel Gelfand, Sergei Gelfand, Vladimir Retakh, and Robert Lee Wilson,
  *Quasideterminants*, [arXiv:math/0208146](https://arxiv.org/abs/math/0208146).
  The D-pivot Schur complement agrees with the corresponding block
  quasideterminant expression when that pivot is invertible. This expression
  does not supply an ordinary multiplicative determinant on an arbitrary
  noncommutative ring.

Source statements and their formal hypotheses remain the acceptance authority;
these references explain terminology and do not substitute for native proofs.
