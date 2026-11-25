# Octonionic flavor source audit and native theorem targets

## Source and evidence boundary

The source repository is
[`theaiwillwin/octonionic-flavor-research`](https://github.com/theaiwillwin/octonionic-flavor-research),
inspected at immutable commit
`fcdb44161381be4537a7f3fb749cf410b6c1dd4c`.
Its complete returned recursive tree contains no Lean source, Lake project,
or Lean toolchain file. Its code, numerical artifacts, and mathematical
arguments are research inputs, not Mathlib proof certificates.

The current consolidated publication is
[`publication/unified_flavor_arxiv_v1/main_v5.tex`](https://github.com/theaiwillwin/octonionic-flavor-research/blob/fcdb44161381be4537a7f3fb749cf410b6c1dd4c/publication/unified_flavor_arxiv_v1/main_v5.tex),
with the title *Reachability Is Not Selection in Target-Free G2 Flavor-Frame
Dynamics*. Its
[claim ledger](https://github.com/theaiwillwin/octonionic-flavor-research/blob/fcdb44161381be4537a7f3fb749cf410b6c1dd4c/publication/unified_flavor_arxiv_v1/CLAIM_LEDGER_v2.md)
explicitly limits the conclusions to a finite action ensemble and does not
claim a Standard Model flavor derivation or a global no-go theorem.

The external repository was inspected without modification. Its reviewed
standalone `octonion_g2_kernel.py` was run in a separate audit directory and
exited successfully. No vacuum optimizer, Hessian computation, flavor fit,
or external publication build was rerun. The quantitative scan results below
are attributed to saved source artifacts.

## 1. Fix the real form before transferring a theorem

The
[kernel](https://github.com/theaiwillwin/octonionic-flavor-research/blob/fcdb44161381be4537a7f3fb749cf410b6c1dd4c/octonion_g2_kernel.py)
uses ordinary real division octonions. All seven imaginary basis elements
square to minus one, and the norm is positive definite. Its invariant
three-form, Euclidean frame geometry, and fixed-unit stabilizer concern
compact G2 and SU(3).

Our canonical Zorn carrier has norm `a*b - dot x y`, of signature (4,4),
and the imaginary norm has signature (3,4). Its automorphism algebra is the
split real form. There is no real algebra isomorphism identifying the
division and split carriers: the split carrier has nonzero zero divisors.

Alternativity and automorphism covariance are reusable algebraic statements.
Euclidean sums of squares, positivity arguments, and compact stabilizers
require their own assumptions. Replacing the external squared Euclidean
norm by `zornNorm` loses nonnegativity; placing a positive coordinate dot
product on the split carrier does not make it invariant under split
automorphisms.

The external convention has associator `[u,v,w] = (u*v)*w - u*(v*w)` and
tensor `A_ijkl = <[e_i,e_j,e_k],e_l> = -2 psi_ijkl`, where `psi = *phi` in
its declared coordinate orientation. The fresh kernel run reported zero
errors for the Cayley-Dickson/Fano comparison and the contractions
`phi_imn phi_jmn = 6 delta_ij`, `psi_imnp psi_jmnp = 24 delta_ij`, and
`A_iklm A_jklm = 96 delta_ij`. These finite checks do not certify a universal
Lean theorem.

## 2. Basis covariance determines the operator type

The explicit
[covariance correction](https://github.com/theaiwillwin/octonionic-flavor-research/blob/fcdb44161381be4537a7f3fb749cf410b6c1dd4c/OCTONIONIC_FLAVOR_BIFURCATION_THEOREM.md)
replaces the entrywise squared expression

`M_ab = ||[l_a,r_b,H]||^2`

with the signed bilinear operator

`Y_ab = <[l_a,V,H],r_b>`.

The distinction can be seen without numerical examples. Replacing the left
frame by its negative leaves every squared entry of M unchanged, whereas
the required bilinear covariance under `O_L = -I` sends a nonzero matrix to
its negative. Simultaneous octonion-automorphism invariance is a separate
property and cannot supply independent flavor-basis covariance.

For a fixed linear map `A x = [x,V,H]`, a bilinear pairing, and frames
transformed as `L -> L O_L` and `R -> R O_R`, finite-sum linearity gives

`Y(L O_L, R O_R) = O_L^T Y(L,R) O_R`.

In a positive inner-product realization, orthogonal changes of basis then
preserve the singular values. This covariance theorem is the first native
translation target. The corrected operator must not be replaced by a
different derivation merely because both are linear maps.

## 3. Isolate the spectral obstruction from octonions

For the original same-frame expression
`M_ab = ||[u_a,u_b,H]||^2`, alternativity makes M symmetric and hollow.
The resulting three-dimensional singular-value obstruction is more general:

> Every traceless real symmetric 3 by 3 matrix has ordered singular values
> `s1 = s2 + s3`.

To see this, let the real eigenvalues be `lambda1, lambda2, lambda3`.
Their sum is zero. Unless all are zero, there is a positive and a negative
eigenvalue. At most one sign occurs twice. The absolute value on the other
side equals the sum of the two remaining absolute values, including any
zero. A symmetric matrix's singular values are its absolute eigenvalues.
Entrywise nonnegativity and conditional-negative-type arguments are not
needed for this particular three-dimensional conclusion.

After normalizing a nonzero spectrum, the general form is `(1,r,1-r)` with
`1/2 <= r <= 1`. Only the extra ansatz `(1,x,x^2)` forces `1 = x + x^2`
and the positive inverse-golden-ratio root. This is not a derivation of a
Cabibbo angle or of all fermion mass ratios. The source's
[mass-hierarchy discussion](https://github.com/theaiwillwin/octonionic-flavor-research/blob/fcdb44161381be4537a7f3fb749cf410b6c1dd4c/OCTONIONIC_MASS_HIERARCHY_WITHOUT_SPECTRAL_RIGIDITY.md)
already makes the geometric-progression qualification explicit.

The native proof should use `Matrix.IsHermitian.trace_eq_sum_eigenvalues`
and the ordered `LinearMap.singularValues` API. The remaining formal task is
the three-real-eigenvalue argument and the precise singular-value bridge.
This audit does not claim that theorem has been added or compiled.

## 4. Distinguish covariant associators from genuine derivations

The associator response `A_(a,b)(x) = [a,b,x]` is linear and covariant, but
is generally not a multiplication derivation. The standard derivation is

`D_(a,b) = [L_a,L_b] + [L_a,R_b] + [R_a,R_b]`

with normal form

`D_(a,b)(x) = [[a,b],x] - 3[a,b,x]`.

The local owners already supply the relevant generic surfaces:

- `Algebra/AlternativeDerivations.lean`: associator swaps/cyclicity,
  `stanDerMap_apply_normal_form`, `stanDerMap_isLeibniz`, and `stanDerivation`.
- `Algebra/RegularActionAssociator.lean`:
  `leftRightCommutator_apply_of_right_alternative`, which bundles the fixed
  associator response as a linear map after the cyclic identity is applied.
- `Algebra/Zorn/SplitOctonionDerivationConjugation.lean`:
  `nativeAut_map_associator` for split automorphism covariance.
- `Canonical/ZornCl44DerivationInvariant.lean`:
  `canonicalDerivation_bilin_skew`, `derivationOrthogonalLieHom`, and
  `canonicalDerivation_structureTensor_invariant` for the split pairing.

These are source-level reuse findings. The PR's complete owner compilation
and declaration-axiom audit remain governed by its separate verification
contract.

## 5. Constant invariants do not select a vacuum

For imaginary division octonions the useful underlying identity is

`||[u,v,w]||^2 + 4 phi(u,v,w)^2 = 4 det Gram(u,v,w)`.

For an orthonormal three-frame X, define the associator and three-form
energies by summing over unordered pairs of its columns. With unit h and
`P_X = X X^T`, this gives

`E_A(XXh) + 4 E_phi(XXh) + 8 h^T P_X h = 12`.

Summing the same identity over the three columns of another orthonormal
frame Y gives

`E_A(XXY) + 4 E_phi(XXY) + 8 tr(P_X P_Y) = 36`.

The source
[trace-extremum report](https://github.com/theaiwillwin/octonionic-flavor-research/blob/fcdb44161381be4537a7f3fb749cf410b6c1dd4c/G2_INVARIANT_TRACE_EXTREMUM_REPORT_v1.md)
finds these combinations in a gradient nullspace. Their gradients vanish
everywhere because they are constant. They do not select the archived
fitted frames. A reusable formalization should establish the Gram identity
first and derive the constants by finite sums.

Likewise the publication's unitary-link elimination yields
`min_(Sigma in U(3)) -Re tr(Sigma^* K) = -||K||_*`.
For unitary K all three singular values are one, so this term is constant
at minus three over the constructed unitary family. Representing every
unitary mixing matrix does not itself choose one.

## 6. A concrete verification defect and its limited consequence

The
[pipeline verifier](https://github.com/theaiwillwin/octonionic-flavor-research/blob/fcdb44161381be4537a7f3fb749cf410b6c1dd4c/verify_target_free_g2_action_to_flavor_pipeline_v1.py)
imports solver v1 as `slow`, then solver v3 as `fast`.
[Solver v3](https://github.com/theaiwillwin/octonionic-flavor-research/blob/fcdb44161381be4537a7f3fb749cf410b6c1dd4c/target_free_g2_vacuum_solver_v3.py)
imports the same cached v1 module as `solver` and executes
`solver.feature_matrix = feature_matrix_fast` at module scope.

Consequently the later calls to `slow.feature_matrix` and
`fast.feature_matrix_fast` invoke the same function. The saved zero error
does not independently validate the optimized contraction. The other twelve
pipeline checks assert properties of saved JSON rather than rerunning the
optimizer or Hessians. This defect does not by itself establish that the
underlying contractions or negative numerical conclusions are false.

A repair would retain the original implementation before importing the
mutating module, or remove that import-time mutation, and compare genuinely
distinct functions on deterministic samples. PyTorch was unavailable here;
no fresh contraction comparison is claimed.

## 7. Numerical results retain their declared scope

The current claim ledger reports 74 actions built from 21 sampled feature
directions, with four starts per action. It retains 68 numerically stable
branches, 29 classified as isolated modulo residual symmetry, and six
isolated full-rank two-sector spectra. None of those six passes both
adjacent decade-gap requirements in both sectors.

The later auxiliary-link extension records 21 angle-evaluable branches,
16 smooth Hessians, two isolated smooth branches, and zero branches within
all three declared angle intervals. That angle test is explicitly
post-exposure. The five rank-deficient cases do not receive classical
Hessians because the nuclear norm is nonsmooth there.

The baseline 48-dimensional stability script counts small Hessian
eigenvalues and subtracts the residual-orbit rank. Extra numerical zero
modes do not prove continuous families of stationary points: a direction
can have vanishing second derivative and nonzero higher derivatives. The
later smooth-link verifier separately projects out the residual orbit and
compares Hessian spectra; its evidence must not be conflated with the
baseline receipt.

## Native dependency order

1. Specify the compact or split carrier, product, associator, and pairing.
2. Reuse alternativity and bundled multiplication maps to define the signed
   bilinear operator; prove its frame covariance.
3. Prove the independent traceless three-dimensional spectral obstruction.
4. Establish the compact Gram/associator identity before its frame sums.
5. Reuse genuine derivations for Lie-algebra and tensor-invariance claims.
6. Treat a specified action, its critical points, stability, and observable
   selection as separate targets requiring additional evidence.

No flavor parameter, physical gauge completion, outer triality action, or
real-form equivalence is inferred from these finite algebraic statements.
