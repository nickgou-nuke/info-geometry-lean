# Native (5,5) para-Kähler / metriplectic verification

## Implemented scope

- `Clifford/NeutralPhaseSpaceCore.lean`: nondegeneracy of the actual evaluation
  skew form over arbitrary projective real modules.
- `Clifford/ParaKahlerGeneralizedMetric.lean`: reuse the existing metric datum
  and zero-B-field generalized metric. Prove K/S anticommutation, `(K S)^2=-1`,
  reflected complex twin, positive definiteness and nondegeneracy. No finite
  dimension is imposed in these structural results.
- `Clifford/Cl55ParaKahlerMetric.lean`: construct the Euclidean base-dual datum,
  transport K/S/phase through the existing neutral-to-Q55 equivalence, and prove
  the exact polar/skew/positive-metric normalizations. A negative polar direction
  explicitly prevents using the indefinite form as positive dissipation.
- `Thermo/BilinearMetriplecticReduction.lean`: native `BilinForm.toDual`
  construction `A B♯ A*`, preserving skewness/symmetry/positivity. Constructs
  GENERIC systems from image-annihilation conditions. The source W is finite
  dimensional; the target V is an arbitrary real module. For positive B, the
  reduced operator's kernel is exactly the annihilator of the image of A.
- `Clifford/Cl55MetriplecticReduction.lean`: specializes the construction to
  the actual V55 forms. An explicit two-mode system has reversible vector
  `e_pos 1`, dissipative vector `e_pos 0`, both nonzero, and entropy rate 2.
  Its energy rate is zero by the existing GENERIC owner theorem.
- `Clifford/Cl55ParaKahlerPinTransport.lean`: general Q55-isometry transport of
  the para structure; positive-metric preservation by the existing negative-vector
  real split-Pin lift. A single-pair reflection is neither symplectic nor globally
  antisymplectic for the selected fixed skew form.
- `Thermo/GenericMetriplecticFlow.lean`: injective L forces `dS=0`, hence zero
  entropy production; injective M forces `dH=0`. Nontrivial GENERIC evolution
  needs the appropriate degeneracies.
- Renamed the misleading `paraKahlerK_preserves_Q55` to
  `paraKahlerK_anti_isometry`; no uses of the old name were found in searched
  Lean owners/consumers. Integrated the new chain through `Clifford/All.lean`.

## User-supplied cyclotomic report

The actual `Canonical/GrassmannianBundleCyclotomicOrientability.lean` already
contained unit-orbit, active-support, ambient-reflection and counterexample
corrections. This task only corrected remaining overclaiming comments there.
Concurrent additions `matGUnit`, `matKUnit` and their inverse/stabilizer laws
were inspected and preserved, not attributed to this task.

The precise claims are algebraic: one conjugacy orbit, possibly degenerate
trace pairing, cubic annihilation (not minimality), and active-support
Phi_3/Phi_4/Phi_6 laws. Gamma squared = Delta is NOT Phi_2(Gamma)=0.
No topological principal bundle, cotangent identification, Ehresmann curvature
or Spin/Pin orientability follows from that owner's ring equations.

## Verification

- Locked `InfoGeometry.All`: **27,021 jobs**, exit 0.
  Final log: `/tmp/cl55-para-integrated-final2.log`.
- Kernel replay plus transitive axiom collection: **475 declarations in 12
  owners**, all PASS, exit 0. Only `propext`, `Classical.choice`, `Quot.sound`
  allowed. Log: `/tmp/cl55-para-axioms-final.log`.

| Owner | Audited declarations |
|---|---:|
| NeutralPhaseSpaceCore | 35 |
| PhaseSpaceGeneralizedMetric | 122 |
| Cl55NeutralHyperbolicIsometry | 35 |
| Cl55PureSpinorParaGrassmannianBridge | 21 |
| ParaKahler55SUSYClosure | 34 |
| ParaKahlerGeneralizedMetric | 11 |
| Cl55ParaKahlerMetric | 33 |
| Cl55MetriplecticReduction | 23 |
| Cl55ParaKahlerPinTransport | 6 |
| GenericMetriplecticFlow | 50 |
| BilinearMetriplecticReduction | 16 |
| GrassmannianBundleCyclotomicOrientability | 89 |

The five new owners account for 89 declarations. Their final builds have no
own-source warnings. Dependency warnings and unrelated umbrella axiom reports
remain; this is not a repository-wide axiom or warning-free certification.

- Source-aware forbidden-token scan: PASS for the nine edited/new mathematical
  owners; staged whitespace check PASS.
- Tracked-source hash drift: empty before/after final replay and final scan.
  An earlier replay was deliberately aborted when a concurrent writer added
  the concrete unit witnesses. Those changes were inspected and the umbrella
  rebuilt before the final successful replay.
- `scripts/check_cl55_para_metriplectic.py`: **22 exact rational checks**, PASS.
  Run with `/home/goutev/miniforge3/envs/sage/bin/python`; output
  `/tmp/cl55-para-cas-final.json`. It freezes basis, multiplication and covector
  conventions, and source hashes. This supplementary checker is not a Lean parser
  or substitute for kernel proof.

### New-owner SHA-256

```text
28aeee37a1fb75544a03cb1a46f05ac5244e77ae4859c308ed473b7794867598  ParaKahlerGeneralizedMetric
80f6dcb40a50c708200519133583ce9a28a7a0937e8d283734d30833c763dc1e  Cl55ParaKahlerMetric
e85bd74c50e6a7753c884172ca4aeca873fd5e978fb95964da207eee82cbe688  Cl55MetriplecticReduction
f17dbd866a3cbc512d2242d6ed04bd95e429926e9b0d91e247d1276fb0b500e2  Cl55ParaKahlerPinTransport
69fb559bc701249a62544cf30bc00de1dc9acf01bb5ca288cd8305c4d2de0300  BilinearMetriplecticReduction
```

No global super-Grassmannian, sheaf descent, geometric spinor holonomy,
state-dependent Poisson Jacobi law, physical CPT or continuum theorem is claimed.
All changes staged; no task commit.
