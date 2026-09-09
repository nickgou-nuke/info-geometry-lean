# Detector response integral — native Lean owners

Status: integrated on `main` by commit `ec1aa539c`. On 2026-09-09 the locked build of `InfoGeometry.Nuclear.DetectorResponseAudit`, `InfoGeometry.Nuclear.DetectorResponseBridgeAudit`, and `InfoGeometry.Nuclear.All` passed (8,207 jobs). This verifies those targets, not a master build. The original authoring attempt in `validation/lean_attempt.log` predates integration and returned exit 127.

Target: `nickgou-nuke/info-geometry-lean`, main commit `fdce23724bcbd3cc63f78c6e0cdca7e371d99c1f`.

Pinned environment: Lean `v4.28.1`; Mathlib `8f9d9cff6bd728b17a24e163c9402775d9e6a365`.

## Mathematical object

For a homogeneous solid cylinder `V = {(x,y,z) | x²+y² ≤ R², 0 ≤ z ≤ L}` and an isotropic point source at `(0,0,-d)`, `d>0`, set

```
s(p) = sqrt(x² + y² + (d+z)²)
ell(p) = z*s(p)/(d+z)
response(mu,d,R,L,kappa) = integral over V of
    mu * exp(-mu*ell(p)) / (4*pi*s(p)²) * kappa(p) dV.
```

`mu` is the linear attenuation coefficient at a fixed photon energy. `kappa` is the conditional probability of the selected recorded outcome given the first interaction at `p`; it may depend parametrically on energy and source distance. Setting `kappa=1` counts all first interactions, not full-energy peaks. No inverse-square or inverse-fourth law for the integrated response is assumed.

## Source organization

The sole maintained Lean sources are in `lean/InfoGeometry/Nuclear/` at the repository root. The eight former bundle copies were removed after comparing every file: all definitions and theorem statements remain in those native owners, with compilation repairs in three proof files. The mathematical progression remains cylinder geometry → transport kernel → volume response and Fubini → Beer–Lambert path integral → disk aperture integral → existing flux bridge. No mathematical API was removed.

- `DetectorTransportKernel`: compact cylinder, true Euclidean source distance, material path, front-face entrance, continuity, positivity, domination.
- `DetectorVolumeResponse`: actual 3D Bochner integral, integrability from compactness/continuity, native Fubini, acceptance monotonicity, linearity, explicit count normalization.
- `DetectorBeerLambert`: actual path integral equals `1-exp(-mu*ell)` by the fundamental theorem of calculus, acceptance bounds, partial collision channel.
- `DetectorDiskIntegral`: actual finite-aperture radial integral, exact closed form, rationalization, inverse-square upper bound.
- `DetectorResponseCore`: aggregate of these four owners.
- `DetectorResponseIntegral`: optional bridge reusing `ApollonianBipolarField.fluxDensity` INSIDE the spatial integral and the existing on-axis separation.
- `DetectorResponseAudit` and `DetectorResponseBridgeAudit`: transitive axiom reports for every public proof declaration.

There are 51 public core proof implementations, 3 public bridge implementations, and 2 private helpers. A count is not a certificate of elaboration or proof validity.

## Verification

From this bundle directory, against an existing pinned repository with its Mathlib dependencies built:

```bash
bash scripts/check_lean.sh /path/to/info-geometry-lean
bash scripts/check_lean.sh /path/to/info-geometry-lean --bridge
```

The script builds the native owners through the shared repository build lock. Inspect active compiler processes before invoking it. Public axiom reports cover all 54 public theorems; standard Lean dependencies are `Classical.choice`, `propext`, and `Quot.sound`. The source audit checks report coverage without rewriting Lean files.

Supporting checks, requiring Python plus SymPy, NumPy, and SciPy:

```bash
python3 scripts/audit_sources.py
python3 scripts/check_math.py
```

The symbolic and quadrature checks remain diagnostics, not substitutes for Lean verification.

## Scope and remaining proof obligations

Continuity of `kappa` on the cylinder is a sufficient regularity condition, not a detector law. The ideal model omits a coaxial bore, dead layers, endcap attenuation and external scattering unless separately represented. The coordinate `d` is measured from the active front; a mechanical window gap is not automatically the VPD depth.

The native Cartesian volume integral and disk/depth Fubini theorem are implemented. The full polar/ray Jacobian equality, the sharp global volume-response/solid-angle bound, a microscopic construction of full-energy `kappa`, correlated cascade transport, and a quantitative VPD approximation theorem are not formalized here. The independent ray/volume quadratures are diagnostics, not proofs of the missing change of variables.

The prior module's definition `coincidenceRate = 1/[a(d+d0)]^4` is not used to infer the volume integral. Defining a response to be a power law does not establish physical point-detector reduction or crystal diameter recovery.
