# Detector response integral — canonical owners and retained candidate bundle

The canonical Lean owners are the modules in the repository's root `lean/InfoGeometry/Nuclear/` tree. This directory also retains the incoming PR 169 candidate bundle, including its eight Lean snapshots, for provenance and file-by-file comparison. The snapshots are not active owners and are **not claimed to be kernel-verified**: the candidate records that its authoring environment's compiler attempt returned exit 127. Source scans and numerical checks are diagnostics, not proof certificates. Do not promote the snapshots over the canonical owners without review and a targeted kernel build.

The canonical owner modules were previously integrated on `main` (commit `ec1aa539c`). A locked build reported in the existing integration record checked `InfoGeometry.Nuclear.DetectorResponseAudit`, `InfoGeometry.Nuclear.DetectorResponseBridgeAudit`, and `InfoGeometry.Nuclear.All` (8,207 jobs); that verifies those targets only, not a master build. The separate PR candidate's recorded Mathlib revision differs from the repository integration record, so treat its pin metadata as historical candidate context, not the active environment.

## Mathematical object

For a homogeneous solid cylinder `V = {(x,y,z) | x²+y² ≤ R², 0 ≤ z ≤ L}` and an isotropic point source at `(0,0,-d)`, `d>0`, set

```text
s(p) = sqrt(x² + y² + (d+z)²)
ell(p) = z*s(p)/(d+z)
response(mu,d,R,L,kappa) = integral over V of
    mu * exp(-mu*ell(p)) / (4*pi*s(p)²) * kappa(p) dV.
```

`mu` is the linear attenuation coefficient at a fixed photon energy. `kappa` is the conditional probability of the selected recorded outcome given the first interaction at `p`; it may depend parametrically on energy and source distance. Setting `kappa=1` counts all first interactions, not full-energy peaks. No inverse-square or inverse-fourth law for the integrated response is assumed.

## Source organization

The canonical sources are maintained in root `lean/InfoGeometry/Nuclear/`:

- `DetectorTransportKernel`: compact cylinder, true Euclidean source distance, material path, front-face entrance, continuity, positivity, domination.
- `DetectorVolumeResponse`: 3D Bochner integral, integrability, Fubini, acceptance monotonicity, linearity, count normalization.
- `DetectorBeerLambert`: path-integral identity, acceptance bounds, partial collision channel.
- `DetectorDiskIntegral`: finite-aperture radial integral, closed form, rationalization, inverse-square upper bound.
- `DetectorResponseCore`: aggregate of the four owners.
- `DetectorResponseIntegral`: optional bridge reusing `ApollonianBipolarField.fluxDensity` inside the spatial integral and the existing on-axis separation.
- `DetectorResponseAudit` and `DetectorResponseBridgeAudit`: transitive axiom reports.

The candidate snapshots remain under this artifact directory and do not replace those modules. The candidate describes 51 public core proof implementations, 3 public bridge implementations, and 2 private helpers; such counts do not establish elaboration or proof validity.

## Verification

The canonical-owner script invokes the repository's shared locked build runner. Inspect active compiler processes before any build; do not run concurrent builds. Public axiom reports cover the public declarations; standard Lean dependencies include `Classical.choice`, `propext`, and `Quot.sound`. The source audit is read-only with respect to Lean source files and checks report coverage.

```bash
bash scripts/check_lean.sh /path/to/info-geometry-lean
bash scripts/check_lean.sh /path/to/info-geometry-lean --bridge
python3 scripts/audit_sources.py
python3 scripts/check_math.py
```

The retained candidate's original verification script and status are part of its provenance; its isolated snapshots need a separate, policy-compliant kernel check before promotion. Symbolic and quadrature checks are diagnostics, not substitutes for Lean verification. A general repository build does not by itself certify isolated snapshots.

## Scope and remaining proof obligations

Continuity of `kappa` on the cylinder is a sufficient regularity condition, not a detector law. The ideal model omits a coaxial bore, dead layers, endcap attenuation and external scattering unless separately represented. The coordinate `d` is measured from the active front; a mechanical window gap is not automatically the VPD depth.

The Cartesian volume integral and disk/depth Fubini theorem are implemented in the canonical owners. The full polar/ray Jacobian equality, sharp global volume-response/solid-angle bound, microscopic construction of full-energy `kappa`, correlated cascade transport, and quantitative VPD approximation theorem are not formalized here. Independent ray/volume quadratures are diagnostics, not proofs of the missing change of variables.

The prior module's definition `coincidenceRate = 1/[a(d+d0)]^4` is not used to infer the volume integral. Defining a response to be a power law does not establish physical point-detector reduction or crystal diameter recovery.
