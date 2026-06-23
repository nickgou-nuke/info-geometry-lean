# De Rham Klein-quadric rank audit

This folder contains a reproducible **sandbox** for the model

`a, b` in `\mathbf C^4` and the target polynomial in `\mathbf C^{2D}`:

\[
Q(a,b) = q(a)\,q(b)\,q(a-b)
\]

with

\[
q(x_0,\dots,x_{D-1}) = x_0^2 + \cdots + x_{D-1}^2.
\]

(or an alternate quadratic signature if requested).

The current goal is to compute evidence for whether
\(H^*_{\mathrm{dR}}(\mathbf C^{2D}\setminus V(Q))\) has a total rank compatible
with the claimed `32` in the `D=4` case.

Do **not** assume rank `32`.  The audit treats it as a hypothesis to test.

## Quick start

```bash
python3 scripts/experiments/DeRhamKleinQuadric/audit_rank32.py \
  --dim 4 \
  --signature euclidean \
  --run singular macaulay2 sage finite_field \
  --fields 3,5,7,11,13,101 \
  --self-check
```

Results are written to:

```text
artifacts/de_rham_klein_quadric/rank32_audit.json
```

To ask Macaulay2/Dmodules for actual de Rham cohomology, opt into the heavier
branch:

```bash
python3 scripts/experiments/DeRhamKleinQuadric/audit_rank32.py \
  --dim 4 \
  --signature euclidean \
  --run macaulay2 \
  --m2-derham \
  --m2-timeout 600
```

The `--m2-derham` path uses Macaulay2's `Dmodules`/Oaku-Takayama
`deRham f` routine for the complement of `{f = 0}` and records either Betti
ranks or a timeout/error.  A timeout is useful evidence about computational
cost, not a mathematical disproof.

There is also an explicit Weyl-localization branch matching the root
`compute_derham.m2` script:

```bash
python3 scripts/experiments/DeRhamKleinQuadric/audit_rank32.py \
  --dim 4 \
  --signature euclidean \
  --run macaulay2 \
  --m2-derham \
  --m2-method dlocalize-ext \
  --m2-timeout 600
```

This constructs the Weyl algebra, localizes the structure sheaf by
`Dlocalize(Ivars, f)`, and asks `rationalFunctionExt` for the resulting Ext
table.  It is an exact-computation attempt, not a proof until it returns a
stable table that is independently interpreted and checked.

For partial recovery, compute one degree at a time:

```bash
python3 scripts/experiments/DeRhamKleinQuadric/audit_rank32.py \
  --dim 4 \
  --signature euclidean \
  --run macaulay2 \
  --m2-derham \
  --m2-degree 1 \
  --m2-timeout 600
```

This calls `deRham(k, f)` and records only `H^k_dR`.

For a more surgical D-module lane that often finishes even when `deRham` and
`Dlocalize + rationalFunctionExt` time out, run the bounded Bernstein-Sato
probes:

```bash
python3 scripts/experiments/DeRhamKleinQuadric/run_m2_surgical_probe.py \
  --factor-timeout 60 \
  --components-timeout 60 \
  --product-timeout 120
```

This writes:

```text
artifacts/de_rham_klein_quadric/m2_surgical_probe.json
```

and records exact Macaulay2 certificates for:

- `globalBFunction` on each individual quadric factor;
- `generalB {q(a), q(b), q(a-b)}` on the three-factor ideal;
- a bounded attempt at `globalBFunction (q(a) q(b) q(a-b))` on the full product.

These Bernstein-Sato outputs are not de Rham Betti certificates, but they are
useful exact-rational D-module invariants when the heavier Oaku localization
lane remains computationally open.

A second-stage stratified Macaulay2 lane is available from the factor wrapper:

```bash
python3 scripts/experiments/DeRhamKleinQuadric/factor_stratified_de_rham_wrapper.py \
  --dimension 4 \
  --m2-timeout 120 \
  --singular-timeout 60 \
  --stage2-strata \
  --stage2-timeout 120 \
  --out artifacts/de_rham_klein_quadric/factor_stratified_stage2.json
```

This emits one Macaulay2 script per factor/pair/triple stratum under:

```text
artifacts/de_rham_klein_quadric/stage2_strata_scripts/
artifacts/de_rham_klein_quadric/stage2_strata_logs/
```

Each script explicitly loads both `BernsteinSato` and `Dmodules`, records the
commutative stratum dimension/codimension, tries the remaining-factor
Bernstein-Sato polynomial, and makes a bounded `Dlocalize`/
`rationalFunctionExt` probe on the stratum D-module.  With
`--stage2-derham0`, it also tries `deRham(0, localizer)` for strata with a
nontrivial remaining localizer.  These stage-2 outputs are still probes: do not
promote rank-8 or rank-32 claims unless an actual `deRham` payload returns.

## What is checked

1. Builds the polynomial `f = q(a) q(b) q(a-b)`.
2. For Singular:
   - singular locus ideal `J = (f, \partial f/\partial a_i, \partial f/\partial b_j)`
   - dimensions of pairwise and triple quadric intersections
3. For Macaulay2:
   - emits easy invariants
   - with `--m2-derham`, attempts actual de Rham cohomology via `deRham f`
4. `finite_field` (pure-Python): exact point counts on `F_p^{8}` for odd
   primes using quadratic-form inclusion-exclusion, with optional brute-force
   self-check for tiny fields.
   For `D=4`, Euclidean signature, the complement count is recorded
   symbolically as

   ```text
   # {f != 0 over F_p} =
     p^2*(p - 1)^2*(p + 1)*(p^3 - 2*p^2 - p + 3)
   ```

   for odd primes.
5. Sage finite-field backend: independently evaluates the same
   quadratic-form inclusion-exclusion counts over the requested prime fields.

## Why this split

This problem is best attacked with a CAS chain:

- **Singular** for local stratification/primary decomposition diagnostics.
- **Macaulay2** for algebraic invariants and, if available, de Rham-complement routines.
- **finite_field** pure-Python finite-field diagnostics for
  `#({(a,b) in F_p^{2D} | f(a,b) != 0})`.
- **Sage** for robust finite-field orchestration and future cohomological pipelines.

## Environment status in this checkout

This checkout has been exercised with local `sage`, `Singular`, and `M2`.
Macaulay2 reports the `Dmodules` package, including `deRham`, is available.

The first output is a JSON diagnostic per engine plus a compact summary.

## Current interpretation

The default audit can give point counts and singular-strata diagnostics quickly.
It cannot by itself certify rank `32`.

For `D=4` Euclidean signature, the finite-field complement count is polynomial:

```text
p^8 - 3*p^7 + 7*p^5 - 4*p^4 - 4*p^3 + 3*p^2
```

This is useful motivic/E-polynomial evidence if the complement is in a
polynomial-count/mixed-Tate corridor, but it is not a total Betti-rank
certificate by itself.

The rank question is only answered by a successful cohomology computation, e.g.
Macaulay2 `deRham f` returning Betti ranks whose sum is `32`, or by an
independent certified presentation with 32 basis classes.  Until then, JSON
summaries deliberately report `"rank32_status": "not_assumed"`.

Observed local runs:

- default finite-field/Singular/Macaulay2-smoke/Sage-smoke audit completed and
  wrote `artifacts/de_rham_klein_quadric/rank32_audit.json`;
- finite-field plus Sage audit for `p = 3, 5, 7, 11` completed and wrote
  `artifacts/de_rham_klein_quadric/rank32_trackA_3_5_7_11.json`;
- all-degree `D=4` Macaulay2 `deRham f` timed out after 600 seconds with about
  5.2 GB max RSS;
- degree-zero `D=4` Macaulay2 `deRham(0, f)` timed out after 180 seconds with
  about 1.7 GB max RSS;
- the `Dlocalize + rationalFunctionExt` branch reaches the same heavy
  localization phase in `D=4` and should be treated as open computation debt
  until it produces a completed Ext table;
- the bounded surgical Bernstein-Sato lane completed locally and wrote
  `artifacts/de_rham_klein_quadric/m2_surgical_probe.json`, including
  `generalB {q(a), q(b), q(a-b)} = (s+3)^2 (s+4)` and
  `globalBFunction` for each individual quadric factor equal to `(s+1) (s+2)`;
- the same surgical lane still times out on the full product Bernstein-Sato
  polynomial within a 120-second bound, so it narrows but does not close the
  full product computation debt;
- the same Macaulay2 de Rham path is validated on the smaller `D=2` case.

So the current evidence does not prove or disprove rank `32`; it shows the
straight Oaku-Takayama computation for `D=4` is a heavy run and needs either a
longer isolated job, factor/stratum-aware decomposition, or a different D-module
backend.
