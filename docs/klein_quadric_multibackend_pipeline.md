# Klein Quadric / Monodromy Multibackend Pipeline

This note supplements `klein_quadric_monodromy_synthesis.md` with a concrete
multi-backend verification pipeline used by `formalizations/klein_quadric_multibackend_pipeline.py`.
A higher-level computational bridge script is `formalizations/klein_quadric_motive_bridge.py` for the same
motivic/Klein-quadric monodromy theme.

## Scope

The script compares the same geometric object across:

- **SymPy**: algebraic identities, gradient/Jacobian shape, and the local
  residue integral `∮ dz/z = 2πi`.
- **GAP**: quadratic polar Gram form (`B(P,P)`), rank and nullspace diagnostics.
- **Sage**: polynomial model
  `f = q(a) q(b) q(a-b)` in 8 variables and singular ideal construction.
- **galgebra / Clifford**: geometric-algebra sanity checks for the 4-vector model.
- **Macaulay2**: optional `deRham` attempt for `f` (best-effort, since `BernsteinSato`
  may require additional normal form libraries).

## Command

```bash
python3 formalizations/klein_quadric_multibackend_pipeline.py
# full (expensive) Macaulay2 deRham check:
python3 formalizations/klein_quadric_multibackend_pipeline.py --heavy --m2-timeout 900
```

## Expected output

The script prints one block per backend and a final summary dictionary.
A `True` entry indicates successful execution; `False` indicates missing backend
or environment-specific failure.

By default, the Macaulay2 block runs a lightweight deRham smoke check (`deRham(x^2)`) and
reports that status. Add `--heavy` to run the full 8-variable witness:
`f = q(a)q(b)q(a-b)`.

On slower environments, heavy mode may return:
`m2 deRham command timed out (computation may be intensive).`

## Track B: external Oaku/D-localization witness

A mathematically faithful, non-lean D-module check is provided in
`compute_derham.m2` (Weyl algebra + `Dlocalize` + `rationalFunctionExt`).
It is intentionally heavyweight and should be run manually in a background session:

```bash
nohup M2 --script compute_derham.m2 > /tmp/compute_derham.out 2>&1 &

# or via the helper (recommended)
python3 formalizations/compute_derham_track_b.py --launch --watch --log /tmp/compute_derham.out
```

Monitor an existing run with:

```bash
python3 formalizations/compute_derham_track_b.py --pid 296633 --log /tmp/compute_derham.out --watch --json
```

This track is not used as a build gate; if it times out, treat that as a
computational-limit outcome, not a dependency failure.

The script is a computational complement to the theorems in
`lean/InfoGeometry/Projective/KleinQuadricMonodromy.lean`:

- `circleIntegral_one_div`
- `deRhamClass_of_winding`
- `wilsonPhase_of_winding`
- `chiralNullConductor_eq_selfOrthogonal`