# Projective expectation geometry and nonassociative operator-Zorn attention

## Scope and status

This development reconstructs the five sections of the supplied attention
brainstorm (`Pasted markdown(20260905-103513).md`) under the explicit corrections:
no primitive spacetime, no associative replacement of the Zorn field algebra,
and no removal of operator commutators, associators or gauge-frame terms.

The source's equations are not presumed true. Source proposals, counterexamples,
implemented replacements and remaining obligations are separated below.

The implementation uses the existing `PositiveMeasure.Proj` quotient and the
existing `NCZornElement.mul`. It is a finite positive readout-state chart with
operator-valued fibers, not a classification of all quantum states. There is
no extra state quotient, no trace assumption for a general Type III weight,
and no positivity claim for the indefinite split-Zorn quadratic norm.

**Verification:** complete Lean proof scripts, not yet elaborated or checked
by Lean. Lean/Lake are unavailable in the authoring environment. The supplied
native check exits 2 in that environment. Independent symbolic checks do not
replace native compilation or the transitive axiom audit. This PR is stacked
on the unverified gauge sources of PR #146 and must remain draft.

Entry point:

```lean
import InfoGeometry.Canonical.ProjectiveZornAttention
```

## 1. Clifford factors are not central head projectors

The source combines the correct split Clifford classification with an invalid
head partition. The proposed products of `(1 + sigma_z)/2` on disjoint mode
sets are tensor-factor occupation projectors. Disjoint factors commute, but
the projectors can have a common nonzero range and need not sum to one.

`AttentionFrameCorrections` constructs the actual two-bit function module.
`occupationProjection_eq` identifies its occupation projector with exactly
`(1 + bitParity)/2`. At the all-false bit string:

    P_0 P_1 1 = 1,     (P_0 + P_1) 1 = 2.

Thus orthogonality and completeness fail already for two one-mode heads.
An explicit endomorphism also shows that this projector is not central.
These are concrete source-equation counterexamples, not model assumptions.

For an already chosen finite product `H -> V`, the native linear maps
`headProjection h` instead satisfy orthogonality and completeness. They do
not establish that a learned multi-head architecture is a Clifford module,
that its head spaces are invariant under every Clifford action, or that the
full split Clifford matrix algebra has nontrivial central idempotents.

The existing Clifford/Bott/Jordan-Wigner owners remain separate. This PR does
not re-prove all-stage Clifford matrix classification and never applies that
classification to replace the nonassociative operator-Zorn carrier.

## 2. Chiral labels, phases, tensors and genuine curvature

A grading eigenspace is not, by itself, a retarded or advanced propagator.
The source supplies no evolution operator, support theorem, boundary condition
or causal order justifying that interpretation. A direct-sum chiral split is
also not a tensor-product split on which a partial trace is automatically
defined. No such propagation or partial-trace assertion is installed.

The symmetric part of a dyad is a symmetric tensor, not automatically a scalar
metric. The antisymmetric part is an alternating tensor, not automatically
nondegenerate, closed, or equal to connection curvature. Those conclusions
need the relevant contractions, connection and differential calculus.

The actual ordered Zorn algebra is preserved. For operator coefficients:

    U cross U = ([U_2,U_3], [U_3,U_1], [U_1,U_2]),

which need not vanish. `OperatorZornRealModule` supplies only the additive real
module needed for linear forms and expectations. It does not alter `mul` or
install an associative, alternative or Lie algebra on the Zorn carrier.

The two gauge owners from PR #146 are generalized from `Fin 4` to an arbitrary
`Direction`. `FourPotential`, `electric` and `magnetic` survive only as legacy
finite-index adapters; they carry no spacetime interpretation. The general
curvature and Bianchi theorems have no fixed index cardinality.

## 3. Homogeneous ratios and logarithmic phase characters

For a strictly positive weight vector w, use the existing quotient ray [w].
Define on that quotient, not merely on representatives:

    r_ij([w]) = w_i / w_j,
    C_ij([w],[v]) = w_i v_j / (w_j v_i),
    ell_ij([w]) = log r_ij([w]).

`ExpectationRatioMetric` proves ray well-definedness, positivity, the ratio
cocycle, two independent scale invariances and separation by the complete
coordinate family. It constructs native `MetricSpace` data by pulling back
the existing sup metric along the proved-injective map `ell`:

    d([w],[v]) = ||ell([w]) - ell([v])||_infinity.

For finite positive coordinates this is Hilbert's projective distance:

    max_i log(w_i/v_i) - min_i log(w_i/v_i).

The Lean statements use the sup-norm form and prove nonnegativity, symmetry,
triangle inequality and zero exactly on equal rays. No arbitrary selected
observable family is claimed to separate an unspecified larger state space;
without such separation, the pullback to that space is only a pseudometric.
The new metric is data, not a global instance replacing existing topologies.

The logarithmic phase character

    chi_nu(r) = exp(i nu log r)

has unit norm, is multiplicative on positive r, and obeys the ratio cocycle.
This is an exact scale/phase component, not an integral Fourier-Mellin or
Radon transform. A dot-product evaluation specifies an incidence/projection
coordinate, not integration of a field over a hyperplane. No transform
convergence, inversion or equality with attention is asserted from that
single dot product. Position labels need not be spacetime coordinates.

## 4. Projective Gibbs rows, expectation ratios and Fisher energy

### Exponential tilting of an explicit reference

Keep strictly positive reference weights w and define

    w_i(beta,s) = w_i exp(beta s_i).

`GibbsRayGeometry` constructs this positive measure and its existing ray.
It identifies its unit-reference normalization with the existing
`Routing.FiniteSoftmax.weight`; it does not introduce a second softmax owner.
The exact log-ratio theorem is

    ell_ij([w exp(beta s)]) = log(w_i/w_j) + beta(s_i-s_j).

For beta nonzero, two score rows give the same ray precisely when they differ
by a constant. Multiplying the scores is therefore not generally gauge:
it changes relative ratios and corresponds to changing the effective tilt.
Rescaling all reference weights, or adding a constant score, changes only
the representative. For the same reference, the exact distance formula is

    d(q_s,q_t) = ||beta ((s_i-t_i)-(s_j-t_j))_(i,j)||_infinity.

An expectation is the homogeneous ratio

    mean_w(f) = (sum_i w_i f_i)/(sum_i w_i),

and `rayMean` is defined directly on the quotient. Additivity, real linearity,
normalization on constants, nonnegativity for nonnegative f and scale
invariance are proved. Attention-value contraction is exactly this expectation
for unit-reference Gibbs weights, without any nonorthogonal Born-rule claim.

### Correct thermodynamic signs and reference dependence

The existing `Analytic.LogSumExp` owner supplies the genuine derivatives.
For exp(beta s), the first derivative of log Z is **plus** mean(s); it is
minus mean(E) only after E = -s. The second derivative is the centered variance
and is nonnegative. Relative entropy readout is explicitly

    S_w(p) = -sum_i p_i log(p_i/w_i) = log Z - beta mean_p(s).

This is a reference-dependent scalar identity. It is not an operator logarithm,
a von Neumann entropy of arbitrary nonorthogonal key mixtures, or a theorem
about irreversible entropy production. The reference is never silently erased.

`GibbsReferenceGauge` additionally removes its arbitrary scale. The
reference-scale invariant log-partition comparison is

    Psi = log(Z_tilt/Z_reference).

The fully normalized reference entropy is

    S_barw(p) = -sum_i p_i log(p_i/normalize(w)_i)
              = Psi - beta mean_p(s).

Its invariance under reference rescaling and common score shifts is proved
in the scripts. Psi alone still changes under a common score shift; the
entropy combination does not. Raw log Z and S_w are gauge potentials, not
scale-independent observables.

### State variations, not spacetime derivatives

`LogRatioDifferential` bundles the native linear map

    theta_w(v)_ij = v_i/w_i - v_j/w_j

and proves it is the derivative of pairwise log readouts along affine paths.
A locally varying change of lift sends

    w -> c w,     v -> c v + b w,     c > 0.

The differential is invariant under this entire change, including b, the
derivative of the scale. Its kernel is proved to be exactly v = a w.

The finite Fisher energy is

    G_w(v) = sum_i p_i (v_i/w_i - mean_w(v/w))^2,   p = normalize(w).

It is nonnegative, has the same radial kernel, and is invariant under the
same change of lift. For v_i = w_i f_i it is exactly the covariance/variance
formula. This proves a concrete directional Fisher statement; degeneracy
is not equated with vanishing Riemannian curvature or a loss-landscape theorem.
Hilbert distance and Fisher energy are distinct structures, not renamed copies.

### Nonorthogonal keys do not automatically produce softmax

The source's proposed spectral expansion uses nonorthogonal overcomplete keys
as though they were orthogonal spectral projectors. The new counterexample
uses three unit vectors in R^2: (1,0), (0,1), (3/5,4/5). For the normalized
positive density I/2 each quadratic key readout is 1/2, so their sum is 3/2.
At zero logits the Gibbs density of the proposed zero Hamiltonian is I/2,
whereas the classical three-entry softmax is 1/3 at every key. The claimed
identification therefore fails even for normalized keys and zero scores.
No numerical approximation is involved in the Lean statements.

## 5. Full Zorn fields over projective state variations

### A native horizontal potential form

Let C([w],i,j) be arbitrary full operator-Zorn coefficients depending on the
ray, with no commuting, Cartan, single-colour or diagonal identification.
`OperatorZornStateGeometry.statePotential` is a native linear map in v:

    A_w(v) = sum_(i,j) theta_w(v)_ij C([w],i,j).

It annihilates the radial direction and is invariant under (w,v)->(cw,cv+bw).
Its Zorn bracket under two such direction lifts is invariant, not set to zero.
The four internal Zorn fields do not introduce an external four-dimensional
base. This is a fiberwise horizontal form on homogeneous state variations;
no smoothness of the arbitrary family C is stored as a proof assumption.

### Products and associators precede expectation

For a family of real linear coefficient observations E_i, form their ray
expectation m_q. Entrywise readout of NC-Zorn values is linear, not a ring
homomorphism. In particular,

    Read_q(as(X,Y,Z)) = Read_q((X star Y) star Z)
                        - Read_q(X star (Y star Z)).

There is no factorization through expectations of individual factors.
The full parent curvature identity survives linear normalized readout:

    [nabla_xi,nabla_eta]X
      = delta_[Pxi,Peta] X + F_xi,eta star X
        - as(Phi_xi,Phi_eta,X) + as(Phi_eta,Phi_xi,X).

Both associators and the background curvature remain present. Its cyclic
Bianchi expression retains the coefficient-curvature terms and the full
six-term Akivis alternation. No Jacobi or alternativity cancellation is used.

Coefficient-unit frame transformations act contragrediently on the observations.
The readouts of products, associators, full curvature action and Bianchi are
frame-invariant with that simultaneous change. The parent's inhomogeneous
term remains P' = P - [P,g]g^-1. General units are algebraic frames; positivity
of a star-state under arbitrary non-star-preserving units is not asserted.

### Constructed positive example, nonzero associator

For a real matrix coefficient algebra, diagonal vector states give an actual
normalized positive functional:

    m_q(I)=1,     m_q(M^T M)=mean_q(sum_j M_ji^2)>=0.

The weights (2,1) and the full NC-Zorn elements

    X = sigmaPlus(e12,e21,0),    E = nPlus(I)

satisfy an exact scalar readout of the lower third associator coefficient:

    Read_[2:1](as(X,X,E)).sigma_minus[2] = 1/3.

This explicitly shows that projective normalization and positive expectation
do not annihilate nonassociativity. Real matrices are coefficients here;
Zorn multiplication has not been replaced by matrix multiplication.

## Remaining exact frontier

The current work constructs the quotient invariants, a true finite-ray metric,
horizontal differential forms, positive coefficient states, and normalized
readouts of the full algebraic gauge identities. It does not yet construct a
smooth connection on a quotient tangent bundle and identify its exterior
derivative with the coefficient-commutator backend. For that next theorem,
the coefficient family must be concretely differentiable and the base
derivative/field action must be soldered by a genuine proof, not by a field
asserting the desired equality. Moving-frame terms must be retained.

Likewise, a full noncommutative/Type III state-space metric, arbitrary observable
separation, all-stage Clifford classification, Radon/Fourier-Mellin inversion,
a learned-transformer equivalence and a tensor-factor partial trace remain
separate tasks. No missing conclusion appears as a new axiom or target-shaped
hypothesis, and no source assertion is declared proved merely by relabeling.

## Reproduction and evidence

On a complete idle checkout with pinned Lean/Mathlib dependencies:

```sh
bash scripts/quality/check_projective_zorn_attention.sh
```

This uses the repository's locked narrow-build owner and then prints the
transitive axioms of the declarations listed in the new audit. Missing results
or axioms outside propext, Classical.choice and Quot.sound fail the gate.
No dependency update or cache cleaning is performed. The local attempt is
recorded as unavailable, not successful.

Independent exact algebraic diagnostics:

```sh
python3 tools/quality/check_projective_zorn_attention.py
python3 tools/quality/check_operator_zorn_gauge_algebra.py
```

The new script has 47 checks: exact symbolic identities and counterexamples,
plus an explicitly labelled finite metric-triangle sanity check. The parent
free-noncommuting-coefficient checker has 16 identities / 116 coordinate
comparisons. Neither is a Lean certificate. Source-token scans and hashes are
reported separately from elaboration and transitive-axiom verification.

## Source and primary context

The uploaded five-section document is the reconstruction target. Earlier
Cl(1,1)/Rindler narratives are not substituted for that new attachment.
The user's projective/no-spacetime and nonassociative constraints determine
the retained interpretation. Repo source owners, not archived summaries or
file names, determine reuse. Context checked against primary sources:

- Vaswani et al., Attention Is All You Need (2017), arXiv:1706.03762.
- Su et al., RoFormer: Enhanced Transformer with Rotary Position Embedding,
  arXiv:2104.09864.
- Reeb, Kastoryano and Wolf, Hilbert's projective metric in quantum information
  theory, arXiv:1102.5170.
- Pinned Mathlib v4.28.1 metric-space, real-logarithm and linear-map sources.

These references orient the audit. The explicit definitions and displayed
counterexamples, not appeals to physical analogy, supply its mathematical
content.
