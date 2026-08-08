# Genuine Lemma Chains for `F_Q(C^D,3)` de Rham/Cooperad Sockets

This note records theorem-honest routes from standard mathematics to the sockets
in the finite Lean spine.  It distinguishes what can be discharged with existing
finite kernels from what requires importing serious topology/algebraic-geometry
machinery.

## Problem

Let `V = C^D`, `D` even, and let `q` be a nondegenerate complex quadratic form.

```latex
F_Q(V,3)=\{(x_1,x_2,x_3)\in V^3: q(x_i-x_j)\ne 0\text{ for }i<j\}.
```

Translation gives

```latex
F_Q(V,3) \cong V \times U_D,
\qquad
U_D=\{(a,b)\in V^2:q(a)q(b)q(a-b)\ne0\}.
```

Since `V` is contractible, the de Rham problem is the complement `U_D` of the
three hypersurfaces

```latex
Q_a=\{q(a)=0\},\quad Q_b=\{q(b)=0\},\quad Q_{a-b}=\{q(a-b)=0\}.
```

## Chain A — Translation reduction socket

**Target socket:** `translationReduction`.

1. Define
   ```latex
   \Phi(x_1,x_2,x_3)=(x_1,x_1-x_2,x_1-x_3).
   ```
2. Define inverse
   ```latex
   \Psi(c,a,b)=(c,c-a,c-b).
   ```
3. Prove `Phi ∘ Psi = id` and `Psi ∘ Phi = id` by coordinate algebra.
4. Check nonisotropic conditions transform as
   ```latex
   q(x_1-x_2)=q(a),\quad q(x_1-x_3)=q(b),\quad q(x_2-x_3)=q(b-a).
   ```

**Lean status:** mostly discharged in `QuadraticConfiguration3.Reduced3.toConfig`
and `Config3.toReduced`; remaining improvement is packaging as an explicit
`Equiv` between sigma/subtype spaces.

## Chain B — One-quadric complement `V \ {q=0}`

**Target sockets:** `baseCohomology`, `pairComplementClassAlpha`,
`pairComplementClassBeta`.

Standard theorem chain:

1. Over `C`, every nondegenerate quadratic form is linearly equivalent to
   ```latex
   z_1^2+\cdots+z_D^2.
   ```
2. The map
   ```latex
   q:V\setminus q^{-1}(0)\to C^*
   ```
   is a locally trivial fibration.
3. Fiber over `1` is the smooth affine quadric
   ```latex
   Q_1=\{z_1^2+\cdots+z_D^2=1\}.
   ```
4. `Q_1` deformation retracts onto the real sphere `S^{D-1}`.  One route is the
   standard identification of the complex affine quadric with `T^*S^{D-1}`.
5. Monodromy around `C^*` is induced by `z ↦ -z` on the sphere, degree
   `(-1)^D`.  For even `D`, this is cohomologically trivial.
6. Therefore, over a characteristic-zero field,
   ```latex
   H^*(V\setminus q^{-1}(0)) \cong H^*(S^1\times S^{D-1}).
   ```
7. Generators:
   ```latex
   \alpha=d\log q \in H^1,
   \beta\in H^{D-1}
   ```
   where `β` is the fiber/sphere orientation class.

**References / theorem names:** Milnor fibration of homogeneous isolated
hypersurface singularity; affine complex quadric deformation retracts to
`S^{D-1}` / `T^*S^{D-1}`; Wang sequence or Serre spectral sequence with trivial
monodromy for even `D`.

**Lean feasibility:** topology-heavy.  Best near-term Lean target is finite
interface theorem:
`QuadricComplementModel D` with fields for fibration, fiber sphere cohomology,
monodromy triviality, and two generators.

## Chain C — Fiber of `U_D -> V\{q=0}`

**Target sockets:** `fiberCohomology`, `lerayLocalSystemTrivial`,
`lerayCollapse`.

Projection:

```latex
p(a,b)=a.
```

For `q(a)≠0`, fiber is

```latex
F_a=V\setminus(\{q(b)=0\}\cup\{q(b-a)=0\}).
```

Genuine proof route:

1. Use the orthogonal group action to normalize `a` to a vector with `q(a)=1`.
2. Decompose
   ```latex
   V=C a \oplus a^\perp,
   \qquad b=s a+w.
   ```
3. Then
   ```latex
   q(b)=s^2+q_\perp(w),
   \qquad
   q(b-a)=(s-1)^2+q_\perp(w).
   ```
4. Analyze the complement of the two divisors in this pencil using either:
   - Gysin/Alexander duality for the union of two affine quadrics; or
   - Dupont's hypersurface-arrangement model; or
   - Oaku--Takayama D-module de Rham algorithm.
5. The expected product/Leray candidate gives
   ```latex
   P(F_a,t)=(1+t)^2(1+t^{D-1}).
   ```
6. Then the base contribution would give
   ```latex
   P(U_D,t)=(1+t)^3(1+t^{D-1})^2.
   ```

**Important caveat:** direct SymPy projection audit on actual `dlog(q)` forms shows
`dlog(q12)∧dlog(q23) - dlog(q12)∧dlog(q13) + dlog(q23)∧dlog(q13)` is not zero
(`dx0^dy0` coefficient = 52), so this is currently a finite-candidate pattern, not
a literal `dlog` identity theorem. Therefore Chain C must decide between:

```latex
(1+t)^3(1+t^{D-1})^2 \quad\text{rank }32
```

and

```latex
(1+3t+2t^2)(1+t^{D-1})^2 \quad\text{rank }24.
```

**Lean status:** finite alternatives formalized in `NonIsoConf3DeRhamCooperad`.

## Chain D — Dupont hypersurface-arrangement model

**Target sockets:** `chosenPresentationIsActualDeRham`,
`quadricArnoldRelationsHold`, `betaGysinRelationsComputed`,
`cooperadCompatibility`.

Reference: Clément Dupont, *The Orlik-Solomon model for hypersurface
arrangements*, Ann. Inst. Fourier 65 (2015), arXiv:1302.2103.

Theorem route:

1. Compactify `V^2` to a smooth projective variety `X` containing the three
   affine divisors and the divisor at infinity.
2. Resolve the divisor union to a normal-crossing or Dupont-admissible
   hypersurface arrangement.
3. Build Dupont's model from strata:
   ```latex
   A^*(L)=\bigoplus_{S\in L} H^{*-2\operatorname{codim}S}(S)(-\operatorname{codim}S)
   ```
   with product and Gysin differential.
4. Identify the three degree-one classes on the compactified divisor model (the
   relation form must be induced from Dupont/Gysin boundary algebra, not assumed
   as naive `dlog` wedge closure).
5. Compute the degree `D-1` fiber/Gysin classes `β_ij` and their incidence
   constraints.
6. Compute the cohomology of this finite DGA.
7. Prove the DGA is quasi-isomorphic to the de Rham complex of the complement.

**Lean finite subgoals already available:**

- Boolean stratum poset: `StratumMask`, `stratumMask_card = 8`.
- Gysin cover arrows: `GysinCover`, `gysinCover_card = 12`.
- Degree/twist arithmetic via `DupontHypersurfaceOSModel`.

**Next formalizable Lean subgoal:** define an explicit finite chain complex over
`Q`/`Z` for the 8 strata and 12 cover arrows, with abstract vector-space ranks,
and compute its Euler characteristic/rank alternatives.

## Chain E — D-module/Oaku--Takayama route

**Target sockets:** `oakuTakayamaBridge`, `deRhamPresentationIsComplete`.

Reference: Oaku--Takayama, algorithm for de Rham cohomology groups of the
complement of an affine variety, arXiv:math/9801114.

Theorem route:

1. Let
   ```latex
   f=q(a)q(b)q(a-b) \in C[a_1,...,a_D,b_1,...,b_D].
   ```
2. Compute the algebraic de Rham cohomology of `C^{2D}\setminus V(f)` using the
   localization `C[x,1/f]` as a `D`-module.
3. Use Bernstein--Sato/localization, Fourier transform, and Weyl Gröbner basis, and
   restriction/integration algorithms.
4. Extract Betti numbers and, with representatives, ring generators.

For reproducible execution in this repository, use:

- `proofs/non_iso_conf3_projection_audit.py` (symbolic `dlog` obstruction)
- `proofs/non_iso_conf3_rank32_external_audit.py` (toolchain launcher: Singular/Macaulay2/Sage)
  - this now also emits `non_iso_conf3_rank32_sagemanifolds.sage` as a geometry/spec layer witness
- `proofs/NonIsoConf3DModuleRankAudit.lean` (Lean JSON parser + rank socket adaptor)

**Lean feasibility:** implementing Weyl Gröbner is large.  Better short-term:
provide a verified finite example or interface plus reproducible external
Singular/Macaulay2/Sage script output.

## Chain F — finite-field/motivic route

**Target sockets:** `countsForAllPrimePowers`, `comparisonWithMotivicEPolynomial`,
`pointCountToCohomologyBridge`.

For `D=4`, current fingerprint:

```latex
\#U_4(F_p)=p^2(p-1)^2(p+1)(p^3-2p^2-p+3)
```

for sampled odd primes.  To upgrade:

1. Prove the formula for all odd prime powers `q` using finite quadratic-form
   counts.
2. Better: prove the Grothendieck-ring class
   ```latex
   [U_4]=L^2(L-1)^2(L+1)(L^3-2L^2-L+3).
   ```
3. Use Hodge--Deligne motivic measure to get
   ```latex
   E_c(U_4;u,v)=P(uv).
   ```
4. Only after purity/mixed-Tate/formality can one recover ordinary Betti/ring
   data directly.

**Existing Lean finite algebra:** `GrothendieckGromovWittenYangBaxter` proves the
polynomial equality between inclusion--exclusion and the factorized class
candidate.

## Chain G — cooperad structure

**Target socket:** `cooperadCompatibility`.

Genuine theorem route:

1. Work with Fulton--MacPherson or Axelrod--Singer compactifications of the
   nonisotropic configuration spaces, adapted to the quadric divisor.
2. Boundary strata are indexed by nested collision trees/partitions.
3. Pullback/restriction of logarithmic divisor classes gives cocomposition on
   cohomology.
4. In arity 3, this reduces to the three decompositions:
   ```latex
   \{1,2\}|\{3\},\quad \{1,3\}|\{2\},\quad \{2,3\}|\{1\}.
   ```
5. Internal edge maps to the arity-2 factor; cross edges map to the outer factor.

**Lean status:** arity-three edge bookkeeping proved in `QuadraticConfiguration3`
and reused in `NonIsoConf3DeRhamCooperad`.

## Recommended discharge order

1. Package translation reduction as a Lean `Equiv`.
2. Prove/axiomatize as named external theorem the one-quadric complement model:
   `H^*(C^D\Q) = H^*(S^1×S^{D-1})` for even `D`.
3. Build the Dupont finite chain complex for the three-divisor arrangement.
4. Compute the finite DGA rank to choose between rank `32` and rank `24`.
5. Only then claim the de Rham ring/cooperad presentation.
6. Separately strengthen the motivic route by proving the D=4 Grothendieck class
   geometrically, then use `E_c` as a conditional cohomological fingerprint.

## Theorem-honest current conclusion

```text
The finite colimit/cooperad/OS/D4/point-count skeleton compiles.
Human-math routes exist to discharge the sockets, chiefly via Dupont's
hypersurface-arrangement model, Oaku--Takayama D-modules, and the motivic
finite-field/Grothendieck-class route.
The next real mathematical bottleneck is computing the Dupont/Gysin model for
three affine quadric divisors and deciding the rank-32 vs rank-24 presentation.
```
