# Cobalt angular-model scope

The mathematical owner is `lean/InfoGeometry/Physics/CobaltAsymmetry.lean`.
It formalizes the two angular expressions supplied in the discussion:

\[
B(a,\theta)=1-a\cos\theta,\qquad
G(A,b,\theta)=A^2-b\sin^2\theta.
\]

These are prescribed angular intensity models, not a derivation of the complete
Co-60 decay distribution, a normalized density on the sphere, or experimental
validation of an octonionic field model.

## Formal distinctions

- `betaAngularIntensity_nonneg` requires `|alignment| ≤ 1`.
- `beta_reflection_invariant_iff` establishes that the beta model is invariant
  under `angle ↦ π - angle` exactly when its alignment coefficient is zero.
- `beta_anisotropic` gives explicit unequal values at zero and `π/2` when the
  alignment coefficient is nonzero.
- `gamma_reflection_invariant` proves reflection invariance for all parameters.
- `gamma_global_bounds` proves actual global bounds for nonnegative anisotropy;
  `gamma_minimal_at_equator` consequently proves global, not merely endpoint,
  minimality at `π/2`.
- `gamma_nonneg` additionally requires `anisotropy ≤ amplitude²`.
- `anisotropy_does_not_imply_reflection_violation` constructs an everywhere
  nonnegative, anisotropic, reflection-invariant intensity.

The dependency poset has separate beta and gamma branches. In particular, it
does not insert an unproved arrow from beta parity violation to a Zorn norm or
to CPT conservation.

## Krein and physical interpretation

No replacement `KreinCPT` structure is introduced. A pairing with no bilinearity,
nondegeneracy, or fundamental-decomposition requirements does not establish a
Krein space. Assuming that a transformation preserves such a pairing and then
specializing the assumption to two equal arguments does not derive the physical
CPT theorem. The existing fundamental-symmetry and Krein-adjoint owners remain
unchanged; this scalar angular model makes no identification between that
fundamental symmetry, modular conjugation, and CPT.

The historical Wu experiment concerns parity nonconservation in beta decay:
[Wu et al., Physical Review 105, 1413 (1957)](https://journals.aps.org/pr/abstract/10.1103/PhysRev.105.1413).
The experiments took place in late 1956, as described by
[NIST](https://www.nist.gov/pml/fall-parity/reversal-parity-law-nuclear-physics).
The nuclear-rotation chirality literature is a distinct modeling layer; see
[Meng and Zhang (2010)](https://arxiv.org/abs/1002.0907).

No numerical residuals are inferred from photon energies alone. Such a test
requires measured intensities, angle definitions, uncertainties, and a specified
prediction and detector-response model.

## Verification status

The source, finite dependency poset, and seven regression examples are staged.
Eight axiom audits are included in `CobaltAsymmetryTests.lean`. The new modules
are **pending Lean 4.28.1 kernel verification**, to run after the currently live
sequential dependency rebuild. They are not yet imported into `InfoGeometry.All`.

```bash
python3 /tmp/isnp-rebuild-pinned.py InfoGeometry.Physics.CobaltAsymmetryTests
```

Successful checks must precede any claim that these modules compile.
