# Human-Knowledge Lemma Chains for Discharging the `F_Q(C^D,3)` Sockets

This is a literature-driven map of genuine theorem chains that can replace the
current sockets in the finite Lean spine for the three-point non-isotropic
complex quadric configuration space.

The goal is not to claim these chains are already formalized.  The goal is to
identify named theorems whose hypotheses can be checked and then exposed as
Lean interfaces until fully formalized.

## 0. Object and current formal target

Let `D` be even, `V = C^D`, and `q` a nondegenerate complex quadratic form.

```latex
F_Q(V,3)=\{(x_1,x_2,x_3)\in V^3:q(x_i-x_j)\ne0\text{ for }i<j\}.
```

Translation reduction gives the open complement

```latex
U_D=\{(a,b)\in V^2:q(a)q(b)q(a-b)\ne0\}.
```

The finite Lean spine currently proves/skeletonizes:

- translation/reduced-coordinate bookkeeping;
- arity-three cooperad edge bookkeeping;
- alpha Orlik--Solomon relation skeleton;
- D=4 candidate alpha/beta finite model;
- point-count fingerprint for sampled primes;
- product/Leray rank `32` vs OS-alpha rank `24` finite alternatives;
- the `non_iso_conf3_projection_audit.py` SymPy check confirms the raw quadric `dlog`
  Arnold relation is not literal, so OS-alpha should currently be treated as a
  quotient/projection branch;
- external D-module/Oaku audit is now emitted via
  `non_iso_conf3_rank32_external_audit.py` as
  `artefacts/non_iso_conf3_rank32_audit/non_iso_conf3_rank32_report.json`;
- SageManifolds stack is integrated as an **optional differential-geometry witness**
  layer (parameter base, charts, vector fields/forms/lies, exponential-flow
  bookkeeping); its generated script is
  `non_iso_conf3_rank32_sagemanifolds.sage`.
- Dupont/Gysin stratum poset counts: `8` strata and `12` cover arrows;
- inductive finite colimit chain: cooperad -> OS -> D4 candidate -> point-count.

The unresolved socket is the actual de Rham/cooperad theorem.

---

## 1. Chain for translation reduction

**Socket:** `translationReduction`.

**Lemma chain:**

1. Define
   ```latex
   \Phi(x_1,x_2,x_3)=(x_1,a=x_1-x_2,b=x_1-x_3).
   ```
2. Define inverse
   ```latex
   \Psi(c,a,b)=(c,c-a,c-b).
   ```
3. Direct coordinate calculation proves `Phi` and `Psi` inverse.
4. Nonisotropic conditions transform as
   ```latex
   q(x_1-x_2)=q(a),\quad q(x_1-x_3)=q(b),\quad q(x_2-x_3)=q(b-a).
   ```
5. Since `C^D` is contractible, projection to `U_D` induces de Rham equivalence.

**Formalization status:** very feasible in Lean.  Upgrade the existing
`Config3.toReduced` / `Reduced3.toConfig` to an explicit `Equiv` between subtypes.

---

## 2. Chain for one-quadric complement

**Sockets:** `baseCohomology`, `pairComplementClassAlpha`,
`pairComplementClassBeta`.

**Classical theorem chain:**

1. Over `C`, every nondegenerate quadratic form is linearly equivalent to
   `z_1^2+...+z_D^2`.
2. The polynomial `q: C^D -> C` has an isolated critical point at `0` and is
   weighted homogeneous.
3. Milnor fibration theorem for weighted homogeneous isolated singularities:
   ```latex
   q:C^D\setminus q^{-1}(0)\to C^*
   ```
   is a locally trivial fibration.
4. Fiber `q^{-1}(1)` is the smooth affine quadric.
5. Smooth affine quadric `q^{-1}(1)` is diffeomorphic/deformation equivalent to
   `T^*S^{D-1}` and deformation retracts onto `S^{D-1}`.
6. Monodromy around `C^*` is `z -> -z` on the fiber.  On `H^{D-1}(S^{D-1})` it
   acts by degree `(-1)^D`; for even `D`, it is trivial.
7. Serre/Wang spectral sequence for the fibration over `S^1` gives
   ```latex
   H^*(C^D\setminus\{q=0\}) \cong H^*(S^1\times S^{D-1}).
   ```
8. The degree-one generator is `alpha=dlog(q)`.  The degree `D-1` generator is
   the sphere/fiber orientation class `beta`.

**References / theorem names to cite:**

- Milnor, *Singular Points of Complex Hypersurfaces*: Milnor fibration.
- Standard fact: affine quadric `sum z_i^2=1` is symplectomorphic/diffeomorphic
  to `T^*S^{D-1}`.
- Wang sequence / Serre spectral sequence for fibration over `S^1`.

**Formalization route:** This is topology-heavy.  Short-term Lean should expose a
named theorem interface:

```lean
structure QuadricComplementCohomologyTheorem (D : ℕ) where
  evenD : D % 2 = 0
  alphaDegree : ... = 1
  betaDegree : ... = D - 1
  poincare : P = (1+t)*(1+t^(D-1))
```

---

## 3. Chain for the three-divisor complement via Dupont

**Sockets:** `chosenPresentationIsActualDeRham`, `quadricArnoldRelationsHold`,
`betaGysinRelationsComputed`, `cooperadCompatibility`.

**Primary reference:**

Clément Dupont, *The Orlik-Solomon model for hypersurface arrangements*,
Ann. Inst. Fourier 65 (2015), arXiv:1302.2103.

**Critical theorem labels in the local copy:**

- `Theorem \ref{bos}`: Brieskorn--Orlik--Solomon theorem for hyperplane arrangements.
- `Theorem \ref{qis}`: local logarithmic form complex quasi-isomorphic to complement.
- `Theorem \ref{qisglobal}`: global logarithmic complex quasi-isomorphic to
  `j_* Omega_{X\setminus L}`.
- `Theorem \ref{mhc}` and `\ref{mhs}`: mixed Hodge complex / MHS construction.
- `Proposition \ref{product}`: product on the `E_1` term / model.
- `Proposition \ref{differential}`: Gysin differential on the `E_1` term.
- `Theorem \ref{maintheorem}`: the Orlik--Solomon model computes the
  weight-graded cohomology, functorially, as a DGA in split MHS.
- `Lemma \ref{blowuphyparr}` and `Theorem \ref{seqblowups}`: blowups / wonderful
  compactifications turn arrangements into normal-crossing-like arrangements.
- `Theorem \ref{formulaMpi}`: explicit formula for the model under a blow-up.
- `Theorem \ref{thmrationalhomotopy}`: rational homotopy model consequence.

**Lemma chain for our `U_D`:**

1. Compactify `C^{2D}` to a smooth projective `X`, e.g. `P^D × P^D` plus affine
   chart.
2. Take divisors:
   ```latex
   Q_a=\{q(a)=0\},\quad Q_b=\{q(b)=0\},\quad Q_{a-b}=\{q(a-b)=0\},
   ```
   plus boundary at infinity as needed.
3. Naive compactification is not directly Dupont-ready: singularities occur at
   affine origins and projective diagonal.  This is already detected by
   `NonIsoConf3QuadricCompactification`.
4. Use wonderful compactification / blowups along bad strata:
   - blow up affine `a=0` locus;
   - blow up affine `b=0` locus;
   - blow up projective diagonal / base locus;
   - include boundary divisors.
5. Check the transformed divisor union is a hypersurface arrangement in Dupont's
   sense: locally union of hyperplanes.
6. Apply Dupont `qisglobal` / `maintheorem` to get a finite DGA model.
7. Compute strata cohomology and Gysin maps.
8. Compute the cohomology of the DGA.
9. Read off alpha, beta, mixed relations and settle rank `32` vs `24`.

**Near-term Lean route:**

We should not try to formalize all blow-up geometry immediately.  Instead:

```lean
structure ResolvedDupontInput where
  XsmoothProjective : Prop
  transformedDivisorsHypersurfaceArrangement : Prop
  complementIsoToOriginalU : Prop
  strataCohomologyComputed : Prop
  gysinMapsComputed : Prop
```

Then prove the finite DGA consequence from explicit strata/rank/Gysin data.

---

## 4. Chain via Orlik--Solomon / Brieskorn local model

**Socket:** alpha Arnold relation.

Dupont recalls the classical OS presentation: for a hypersurface/hyperplane
arrangement, the OS algebra is the quotient of an exterior algebra by:

1. monomials for empty intersections;
2. `delta(e_I)` for dependent sets.

For three local hyperplanes in the `A_2` braid arrangement, the dependent triple
produces

```latex
\alpha_{12}\alpha_{23}
-\alpha_{12}\alpha_{13}
+\alpha_{23}\alpha_{13}=0.
```

**Lemma chain:**

1. Near generic triple intersections, divisor germs linearize to a local
   hyperplane arrangement.
2. The three local equations satisfy one linear dependence, analogous to
   `f_12 - f_13 + f_23 = 0` in the diagonal arrangement.
3. Brieskorn--OS theorem gives the Arnold relation in the local logarithmic
   algebra.
4. Dupont functorial/global model transports it to the global DGA.

**Caution:** this proves the alpha relation in the Dupont model, but does not by
itself determine beta/Gysin relations or total ordinary cohomology.

---

## 5. Chain via Oaku--Takayama D-modules

**Socket:** `oakuTakayamaBridge`, algorithmic de Rham completeness.

**Reference:** Oaku--Takayama, *An algorithm for de Rham cohomology groups of the
complement of an affine variety via D-module computation*, arXiv:math/9801114.

**Lemma chain:**

1. Let
   ```latex
   f=q(a)q(b)q(a-b) \in C[a_1,...,a_D,b_1,...,b_D].
   ```
2. Algebraic de Rham theorem identifies cohomology of `C^{2D}\setminus V(f)`
   with de Rham cohomology of the localization `C[x,1/f]`.
3. Regard `C[x,1/f]` as a holonomic `D`-module.
4. Use Bernstein--Sato / localization algorithm to present the module.
5. Use Fourier transform and Weyl Gröbner basis to compute restriction/integration.
6. Extract cohomology dimensions and representatives.
7. Compare representatives with alpha/beta/Dupont generators.

**Practical route:** Use Singular/Macaulay2/Sage as an external audit,
with SageManifolds limited to differential-geometric parameter/fibration checks and
D-module (or equivalent) for the actual de Rham computation. Import only certified
finite output into Lean.

---

## 6. Chain via finite fields and motives

**Sockets:** `countsForAllPrimePowers`, `comparisonWithMotivicEPolynomial`,
`pointCountToCohomologyBridge`.

For `D=4`, the current polynomial candidate is

```latex
P(q)=q^2(q-1)^2(q+1)(q^3-2q^2-q+3).
```

**Lemma chain:**

1. Prove split/nondegenerate quadratic-form point counts over every odd finite
   field `F_q`, not just prime fields:
   - isotropic cone count;
   - nonzero/nonisotropic vector count;
   - orthogonal incidence count.
2. Deduce `#U_4(F_q)=P(q)` for all odd prime powers.
3. Stronger motivic route: prove in `K_0(Var)`
   ```latex
   [U_4]=L^2(L-1)^2(L+1)(L^3-2L^2-L+3).
   ```
4. Apply the Hodge--Deligne motivic measure:
   ```latex
   E_c(U_4;u,v)=P(uv).
   ```
5. If `U_4` is mixed Tate/pure enough and the weight spectral sequence is
   controlled, recover compact-support Betti data.
6. Use Poincare duality only if smoothness/orientability/hypotheses are checked.
7. Ring structure still needs Dupont/DGA, not just point counts.

**Important theorem-honesty note:** polynomial point counts do not by themselves
prove the ordinary de Rham ring.

---

## 7. Chain for cooperad structure

**Socket:** `cooperadCompatibility`.

**Human theorem sources:** Fulton--MacPherson/Axelrod--Singer compactifications;
Getzler gravity operad; Kriz--Totaro models; Dupont functoriality.

**Lemma chain:**

1. Use compactification of configuration spaces where boundary strata are indexed
   by nested collision trees/partitions.
2. For nonisotropic quadric configurations, include exceptional/boundary divisors
   for light-cone collision avoidance.
3. Insertion of configurations corresponds to a morphism of pairs
   ```latex
   (X,L) \to (X',L')
   ```
   satisfying Dupont functoriality hypotheses.
4. Dupont functoriality (`functorialityM`, theorem/proposition chain around
   `\ref{functoriality}`, `\ref{propfunctoriality}`, `\ref{maintheorem}`)
   induces DGA maps.
5. Passing to cohomology gives cooperad cocomposition.
6. In arity three, the only decompositions are:
   ```latex
   {1,2}|{3}, {1,3}|{2}, {2,3}|{1}.
   ```
7. Internal edge classes restrict to the micro factor; cross edges restrict to
   the macro/outer factor.  This is exactly the finite Lean edge map already
   proved.

---

## 8. Chain for resolving the rank-32 vs rank-24 fork

This is the immediate mathematical bottleneck.

### Product/Leray rank-32 route

Need to prove:

1. `p:U_D -> C^D\Q` is a locally trivial fibration.
2. Fiber cohomology is `(1+t)^2(1+t^{D-1})`.
3. Base monodromy on fiber cohomology is trivial for even `D`.
4. Leray/Serre spectral sequence collapses multiplicatively.
5. No literal naive alpha Arnold identity for the actual quadric `dlog` forms survives
after direct symbolic check (`non_iso_conf3_projection_audit.py`: `dx0^dy0` coefficient 52,
 nonzero in 33/66 components); OS-alpha should therefore remain a projection branch
 unless transported through the full Dupont/Gysin model.

If all five hold, then:

```latex
P(U_D,t)=(1+t)^3(1+t^{D-1})^2,
\quad \operatorname{rank}=32.
```

### OS-alpha rank-24 route

Need to prove:

1. Dupont model applies after resolution.
2. The alpha sector is the `A_2` OS algebra:
   ```latex
   1+3t+2t^2.
   ```
3. Flux/beta sector has two independent exterior generators:
   ```latex
   (1+t^{D-1})^2.
   ```
4. Mixed/beta Gysin relations do not add/remove further classes beyond this.

If all four hold, then:

```latex
P(U_D,t)=(1+3t+2t^2)(1+t^{D-1})^2,
\quad \operatorname{rank}=24.
```

### How to decide

The fastest decisive route is **compute the Dupont/Gysin DGA** for the resolved
three-quadric arrangement.  The second-fastest route is an Oaku--Takayama run for
`D=4` to obtain Betti numbers.  Point counts alone are insufficient to decide
ordinary cohomology without purity/formality data.

---

## 9. Formalization priority list

1. Lean `Equiv` for translation reduction.
2. Lean finite DGA framework for a Dupont model with:
   - finite strata type;
   - strata ranks;
   - Gysin edge maps;
   - differential squares to zero;
   - rank computation of cohomology.
3. External computation for the D=4 Oaku--Takayama or Dupont DGA Betti numbers.
4. Import certified finite Betti/rank data into Lean.
5. Only then collapse the `ModelChoice` socket to either `productLeray` or
   `osAlpha`.
6. After the correct model is fixed, formalize the arity-three cooperad maps at
   the DGA level and prove relation preservation.

---

## 10. Bottom line

The strongest genuine chain is:

```text
translation reduction
  -> resolved hypersurface arrangement / wonderful compactification
  -> Dupont logarithmic-form comparison theorem
  -> explicit strata + Gysin DGA
  -> finite cohomology calculation
  -> cooperad functoriality
```

The fallback computational chain is:

```text
f=q(a)q(b)q(a-b)
  -> Oaku--Takayama D-module localization
  -> Weyl Groebner integration
  -> Betti numbers and representatives
  -> compare with Dupont alpha/beta generators
```

The motivic chain is valuable but not enough for the ring:

```text
finite-field counts / Grothendieck class
  -> E_c polynomial
  -> conditional purity/formality
  -> Betti fingerprints, not ring presentation by itself
```
