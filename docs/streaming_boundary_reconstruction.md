# Boundary-conditioned streaming: corrected mathematical reconstruction

## Scope and evidence

The source is the current brainstorm and the attached `Pasted markdown(20260905-094838).md`. Its recurring structural ideas are causal memory, two boundary messages, doubled graded operators, symmetry-indexed routing, and changing local frames. They motivate the constructions below. The proposed identifications with superconductivity, gravity, human perception, or the physical dynamics of language models are not premises of the formalization.

This is an independent extension of `nickgou-nuke/info-geometry-lean` at `b0fa422e6cb6d3da5be7cbbb5ecfae5c12f3237b`. It reuses the existing guarded weak-value definition, finite softmax, signed G2 root coordinates and Weyl reflections, spin matrices, nilpotent raising matrix, and generic Dirac-Hodge algebra. No prior draft branch is required.

All new theorem declarations have proof scripts, but neither Lean elaboration nor the transitive axiom audit executed in this environment. The local launcher exited 127 because `lake` is unavailable. Independent symbolic regressions were executed; they are not kernel certification. The proposed PR must remain draft pending a successful focused build and audit.

## 1. Causal memory is exact without claiming lossless infinite history

`CausalMemory.lean` constructs, for any real module and endomorphism T,

```
h_0=x,
h_(n+1)=T h_n+u_n.
```

Its prefix theorem proves that h_n accesses only u_0,...,u_(n-1). Its chunk theorem proves that processing consecutive chunks gives exactly the same state as processing their concatenation. The closed form is the actual finite convolution

```
h_n=T^n x+sum_(k<n) T^(n-1-k) u_k.
```

The state can retain contributions from all earlier inputs without imposing a rectangular context window. This does not assert that a finite-dimensional state retains all input information. The concrete zero-transition case demonstrates forgetting.

There is also a genuinely continuous native interval integral:

```
h(t)=exp(-r t) integral_0^t exp(r s) u(s) ds
    = integral_0^t exp(-r(t-s)) u(s) ds.
```

For continuous u, the source supplies a `HasDerivAt` proof of `h'=-r h+u` using Mathlib's fundamental theorem of calculus and the exponential derivative. Positive r and nonnegative elapsed time give a positive decay factor no larger than one. The causal interpretation of the integral uses t>=0; Lean's oriented interval integral remains defined outside that interpretation.

The attachment's assertion that *any* causal kernel has an exact finite constant-matrix realization is not adopted. Finite LTI realizations have rational transfer functions `C(sI-A)^(-1)B+D`; a general wavelet or long-memory kernel may require approximation, infinite-dimensional state, or time-varying dynamics. HiPPO is a precise online polynomial-projection framework, not a theorem of perfect biological memory or a generic exact realization of every causal wavelet. Its approximation and timescale hypotheses are separate work.

The supplied Klein-Gordon expression contains no damping term. Positive and negative frequency signs do not by themselves distinguish retarded and advanced boundary conditions. No relativistic signal equation follows from a recurrent update without additional structure.

## 2. Positive two-boundary conditioning and quantum weak values are distinct

`PositiveBoundaryConditioning.lean` constructs a finite transition K from the repository's actual softmax, a forward row mass a, and a backward likelihood b. Define

```
a' = a K,
h_i = sum_j K_ij b_j,
Z = sum_i a_i h_i = sum_j a'_j b_j.
```

The equality of the two expressions for Z is derived by finite sum interchange. The conditioned mass and transition are

```
mu_i = a_i h_i/Z,
K^b_ij = K_ij b_j/h_i.
```

On the actual regular domain, the new source proves normalization, nonnegativity, row stochasticity of K^b, and the consistency equation

```
mu K^b = (a K) .* b / Z.
```

A hard terminal condition is allowed: b may vanish at some states. A positive softmax kernel and one positive component of b give every h_i>0. Nonzero nonnegative forward mass then gives Z>0. The combined theorem derives these denominator conditions rather than assuming the conditioned kernel is already stochastic.

This is a one-step Doob-type conditioning construction, not a complete Schrödinger-bridge existence or optimal-control theorem. Its future likelihood is supplied from a known target or a separately computed backward model. It cannot reveal unseen future tokens. Repeating the identities does not imply physical propagation backward in time.

For real observables f bounded between l and u, the conditioned expectation remains between l and u. That theorem is deliberately contrasted with the complex quantum ratio.

`WeakValueBoundary.lean` reuses the existing `SarsModularWeakValue.weakValue? : Option Complex`. Exactly orthogonal states remain `none`. It proves regular probe additivity and invariance under nonzero post-selection rescaling. The identity operator has weak value one even when its nonzero overlap is arbitrarily small: near orthogonality alone does not guarantee amplification.

For the existing Pauli sigma_x, preselection |0>, and post-selection direction (epsilon,1), the explicit result is

```
A_w=1/epsilon,                       epsilon!=0,
p_success=epsilon^2/(1+epsilon^2),
p_success |A_w|^2=1/(1+epsilon^2)<=1.
```

The success expression includes normalization of the post-selection direction. No physical measurement interaction, pointer distribution, or universal information-benefit bound is asserted by this example. The imaginary part of a weak value has meter-dependent effects in weak measurement; it is not automatically a semantic phase-gradient force. A TSVF amplitude is not a positive classical likelihood and the two are not silently identified.

## 3. Attention weights need separate connection data

An attention kernel K_ij is a scalar averaging weight. A discrete gauge link U_ij is an invertible linear map from the frame at j to the frame at i. `GaugeCovariantRouting.lean` constructs their combination

```
y_i=sum_j K_ij U_ij x_j.
```

For frame changes g_i, it defines `x'_i=g_i x_i` and `U'_ij=g_i U_ij g_j^(-1)`, and proves exactly `y'_i=g_i y_i`. This theorem fixes scalar K while transforming the links and values. A learned score-generation mechanism still needs its own invariant/equivariant construction; that is not inferred from ordinary query-key dot products.

The path defect

```
R_ijk(v)=U_ij U_jk v-U_ik v
```

transforms covariantly. Links constructed purely from one family of frames, `U_ij=g_i g_j^(-1)`, have zero defect. Normalized routing preserves parallel sections in that pure-frame case.

This is an actual discrete compatibility theorem, not a claim that a matrix of softmax weights is itself a Christoffel connection. A two-point averaging example has a nontrivial kernel, so normalized value aggregation need not even be invertible. The singular average is not a parallel transport isomorphism.

Ordinary scaled dot-product attention does not enforce a differential Green-function equation, a metric-compatibility equation, or Einstein's equations. A query-key matrix is not generally a symmetric positive metric. Row normalization does not imply column normalization; the existing repository already requires additional column conditions for a Birkhoff decomposition.

The repeated gravity paragraph is treated as one analogy. In the usual weak-field signature (-,+,+,+), `g00=-(1+2 Phi)` gives `Gamma^i_00 approximately partial_i Phi` and coordinate acceleration `-Gamma^i_00`. With `Phi=-G integral rho(y)/|x-y| dy`, the usual Poisson convention is `Delta Phi=+4 pi G rho`, not the displayed negative sign. A nonzero connection can describe an accelerated frame in flat space; curvature is a different object. No physical acceleration, Unruh temperature, or gravitational source is assigned to a token score.

## 4. Concrete graph Hodge-Dirac realization

The generic repository Hodge owner required two nilpotent inputs. `BipartiteGraphDirac.lean` supplies them from a finite incidence matrix B on the actual total cochain carrier

```
C^0(vertices) direct-sum C^1(edges).
```

The constructed maps are

```
d(x,y)=(0,Bx),
delta(x,y)=(B^T y,0),
D=d+delta,
Gamma(x,y)=(x,-y).
```

The two nilpotences are proved from the block construction. A coordinate pairing is defined, and the adjoint identity `<dx,y>=<x,delta y>` is proved by finite sums. The source then applies the repository's generic theorem to obtain

```
D^2=diag(B^T B,B B^T),
D Gamma=-Gamma D.
```

For the chosen source and target maps, B annihilates constant vertex functions. Its energy satisfies the actual sum-of-squares identity `x^T B^T Bx=sum_a(Bx)_a^2>=0`.

This is a two-term graph/cochain model. It is not a complete higher-dimensional de Rham complex, continuum Hodge decomposition, or a self-adjoint unbounded PDE realization with open-boundary conditions. The continuum formula for the codifferential contains dimension/degree/sign conventions and domains; it is not universally `-star d star`.

A direct sum of two sectors does not establish thermofield entanglement or identify a commutant. Thermofield purification ordinarily uses tensor-product Hilbert spaces; Nambu doubling has its own redundancy. A number-conserving hopping bilinear `a^dagger_i a_j+h.c.` is not a Cooper-pair creation term `a^dagger_i a^dagger_j+h.c.`. Their number gradings must remain distinct.

## 5. The G2 router: root length is not grading degree

`G2GradedRouter.lean` uses the existing signed integer root carrier and the two already constructed simple Weyl reflections. It introduces no alternative G2 root model.

For the simple-root coordinates `(m,n)`, choose degree n. The actual positive roots are

```
(1,0), (0,1), (1,1), (2,1), (3,1), (3,2).
```

Including their negatives, the source evaluates the finite root counts

```
degree:       -2 -1  0  1  2
root count:    1  4  2  4  1.
```

The two-dimensional Cartan contributes separately at degree zero. With the usual split root-space decomposition this gives the contact-grading dimensions (1,4,4,4,1), not six long-root pair modes and six short-root single modes. The new Lean declaration itself proves the finite coordinate counts, not a new Lie-algebra decomposition theorem.

The squared-length form is `2m^2-6mn+6n^2`. The long simple root `(0,1)` has degree one, and the short simple root `(1,0)` has degree zero. These explicit examples refute the proposed identification of root length with five-grading level.

The module proves softmax normalization is invariant under any bijective reindexing, derives the corresponding weight covariance, and applies it to each actual Weyl reflection. Weighted aggregation is unchanged when scores and experts are reindexed together. This is a finite Weyl-equivariant score/channel construction. It does not prove arbitrary neural feature extraction is G2-equivariant or that the full continuous G2 group acts by permuting twelve experts.

The two root lengths and the rotated hexagons are useful geometry. But the G2 Coxeter element has order six; a 30-degree exchange of the two length classes is not a Weyl symmetry. The cyclotomic polynomial Phi_12 has four primitive twelfth roots, not all twelve roots of x^12-1. Root lengths or expert roles are additional data. D4 triality requires the actual three representations and their compatible maps; naming Q,K,V does not construct them.

## 6. Pairing blocks and the precise Andreev zero condition

`PairingGapSeparation.lean` reuses the existing Pauli matrices to construct the finite Hermitian block

```
H(xi,Delta)=[[xi,Delta],[conjugate(Delta),-xi]].
```

It proves Hermiticity, `H^2=(xi^2+|Delta|^2)I`, and the characteristic polynomial. This is deliberately different from a bosonic/Krein evolution generator with an indefinite spectral square. No spatial kinetic operator or scattering boundary-value problem is introduced here.

For the proposed short-junction scalar energy, with 0<=T<=1,

```
E=gap sqrt(1-T sin(phi/2)^2),
1-T sin(phi/2)^2=(1-T)+T cos(phi/2)^2>=0.
```

For nonzero gap, the source proves `E=0` iff `T=1` and `cos(phi/2)=0`, and at phase pi it gives `E^2=gap^2(1-T)`. A transmission perturbation therefore lifts the zero in this formula. There is no topological invariant, spatial localization, or protection theorem here; the scalar crossing is not a Majorana-zero-mode proof.

The physical short-junction formula requires its physical scattering assumptions. Andreev retroreflection is not exact in every material or energy regime; local off-diagonal coupling in a differential equation does not mean a completed reflection occurs at every infinitesimal step. Bound states of a conservative Hamiltonian are not dissipative attractors. Currents require occupations and the appropriate occupied-state or free-energy derivative. No electric-charge factor 2e/hbar is promoted to an information current by relabeling.

## 7. Nilpotent generators are not nilpotent group factors

`UnipotentMemoryShift.lean` uses the existing rational `SpinCore.J_plus`, whose square-zero theorem is already in the repository. A square-zero n gives an actual unit

```
u=1+n,  u^(-1)=1-n.
```

The family `1+t J_plus` obeys the additive parameter law. Every power of the unit remains nonzero. Thus its nilpotent generator and its invertible unipotent transport are proved different notions.

For a GL(n,R) QR/Iwasawa-type factorization, the compact factor is O(n), the positive diagonal factor belongs to A, and N is upper unitriangular. Neither Pin-minus(3) nor Kramers symmetry follows for arbitrary n. A factorization theorem, stable online numerical algorithm, and the associated error analysis are not supplied by this one-parameter example.

## 8. Further source claims that remain unsupported

The proposed branchial quantity `-log Tr(rho_A rho_B)` is not generally a metric: for a mixed state its diagonal value is `-log Tr(rho^2)>0`. The log absolute cross-ratio displayed in the attachment is a signed potential difference; exchanging A and B negates it, contrary to metric symmetry. A branchial metric or entanglement geometry must be constructed separately.

Two distinct orthogonal nonzero Peirce idempotents cannot become equal while retaining those algebra laws: if p=q and pq=0 with p^2=p, then p=0. A metric degeneration or chart singularity is not an identity equating the fixed idempotents. It cannot be called a black-hole horizon on that basis.

The full proposal still needs a selected dynamical state carrier, update law, training objective, symmetry-compatible feature maps, and explicit causal treatment of the terminal likelihood. The present extension gives independently usable pieces with exact compatibility statements. It does not establish that a Transformer, a human listener, or a new trained model physically implements TSVF, a superconductor, or general relativity.

## Verification entry points and primary references

```
bash scripts/check_streaming_boundary.sh
python3 scripts/audit_streaming_sources.py
python3 scripts/audit_streaming_exact.py
```

The first command requires the full repository and its pinned Lean/Mathlib dependencies. It builds `InfoGeometry.Streaming.StreamingBoundaryPristineChain`, runs all new public `#print axioms` commands, and rejects unexpected axioms or incomplete output. The Python checks require SymPy and use exact symbolic/rational arithmetic. The source scan is comment-aware and does not inspect imported proof dependencies.

Primary external background, distinct from new formal claims:

- Gu et al., *HiPPO: Recurrent Memory with Optimal Polynomial Projections* (2020), https://arxiv.org/abs/2008.07669.
- Vaswani et al., *Attention Is All You Need* (2017), https://arxiv.org/abs/1706.03762.
- Jozsa, *Complex weak values in quantum measurement* (2007), https://arxiv.org/abs/0706.4207.
- Cayao, *Non-Hermitian zero-energy pinning of Andreev and Majorana bound states in superconductor-semiconductor systems* (2024), https://arxiv.org/abs/2404.11026.

The derivations in this extension do not rely on these citations as proof hypotheses. The cited work supplies background and distinguishes established physical constructions from the brainstorm's proposed identifications.

