# Centered-Zeta / Trifactor Corridor Map

Audited from live repo state on 2026-06-10.

This note separates:
1. tracked owner theorems,
2. currently compiling but untracked / modified bridge surfaces,
3. the exact remaining closure gap.

It does not claim RH, off-axis annihilation, or unconditional vacuum localization.

## 1. Tracked owner facts verified in the live tree

### 1.1 Centered chart and critical-line fixed locus
File:
- `lean/InfoGeometry/Arithmetic/ZetaSymmetryAdaptedDefinitions.lean`

Direct compile:
- `lake env lean lean/InfoGeometry/Arithmetic/ZetaSymmetryAdaptedDefinitions.lean` -> exit 0

Kernel-backed facts read from the file:
- `centeredParameter_eq_half_plus_u_plus_iv`
  - the standard parameter is represented as `s = 1/2 + u + iv` in the centered chart.
- `centeredCriticalLine`
  - defined as `x.u = 0`.
- `criticalMirror_fixed_iff_centeredCriticalLine`
  - the critical mirror fixes exactly the centered critical line.
- `centeredDirichletMode_of_centeredCriticalLine`
  - on `u = 0`, the scale-normal envelope collapses and only the half-density/phase factors remain.

Honest reading:
- the centered chart is real and compile-backed;
- the fixed-locus statement `mirror fixed <-> u = 0` is compile-backed;
- this is not yet an RH theorem.

### 1.2 Evenness of the symmetry-adapted completed Xi
File:
- `lean/InfoGeometry/Arithmetic/RiemannZetaEquivalences.lean`

Direct compile:
- `lake env lean lean/InfoGeometry/Arithmetic/RiemannZetaEquivalences.lean` -> exit 0

Kernel-backed fact:
- `symmetryAdaptedXi_is_even`
  - `symmetryAdaptedXi z = symmetryAdaptedXi (-z)`.

Honest reading:
- the functional equation has been turned into centered parity/evenness for `Xi`;
- evenness alone does not force a zero onto `u = 0`.

### 1.3 Tracked centered Souriau/Tomita readback surface
File:
- `lean/InfoGeometry/Canonical/SouriauTomitaZetaCenteredBridge.lean`

Direct compile:
- `lake env lean lean/InfoGeometry/Canonical/SouriauTomitaZetaCenteredBridge.lean` -> exit 0

Important scope note from the file itself:
- it explicitly says it does not prove operator-level factorization or RH;
- it also explicitly says it does not rely on treating the untracked arithmetic bridge as canonical.

Kernel-backed facts read from the file:
- `scaleEnvelope_eq_one_of_centeredCriticalLine`
- `centeredDirichletMode_of_centeredCriticalLine`
- `centeredXi_JOddProjection_eq_zero`
- `centeredXi_JEvenProjection_eq_self`
- Souriau modular-potential readbacks such as
  - `modularPotential_eq_pairing_add_partitionPotential`
  - `entropy_eq_expectation_pairing_add_partitionPotential`

Honest reading:
- there is a tracked bridge from centered-zeta parity language to projector/readback language;
- it is still a readback bridge, not the missing annihilation theorem.

### 1.4 Tracked topological sign-flip surface
File:
- `lean/InfoGeometry/GrandUnification/UVCoordinateSymmetry.lean`

Direct compile:
- `lake env lean lean/InfoGeometry/GrandUnification/UVCoordinateSymmetry.lean` -> exit 0

Kernel-backed facts read from the file:
- `functional_equation_isomorphism`
  - the centered inversion picture is formalized at the coordinate level.
- `harmonic_trap_survives`
- `exact_annihilation`
- `coexact_annihilation`

Honest reading:
- this gives a tracked sign-flip / survival-vs-annihilation surface for exact, coexact, and harmonic sectors;
- it does not itself prove that a `Xi`-zero state has vanishing exact/coexact support.

## 2. Currently compiling but non-canonical bridge surfaces in the live tree

These files compile in the current checkout, but the repo status shows them as untracked or modified, so they should not be described as settled owner closure.

### 2.1 Arithmetic trifactor bridge
File:
- `lean/InfoGeometry/Arithmetic/TrifactorZetaBridge.lean`

Repo status:
- untracked (`?? lean/InfoGeometry/Arithmetic/TrifactorZetaBridge.lean`)

Direct compile:
- `lake env lean lean/InfoGeometry/Arithmetic/TrifactorZetaBridge.lean` -> exit 0

Closed finite algebra in the file:
- `active_projectors_sum_eq_square`
- `vacuum_sector_of_active_support_zero`
- `vacuum_sector_of_square_zero`
- `vacuum_sector_of_active_components_zero`

Conditional zeta-facing surface:
- structure `TrifactorZetaMode` contains the explicit field
  - `activeSupportZero : (P_plus T + P_minus T) * state = 0`
- then proves
  - `centeredXi_zero_reflected`
  - `trifactorZetaMode_reflected_zero`
  - `trifactorZetaMode_in_vacuum_sector`

Honest reading:
- the file proves only: if active support is supplied as zero, then `P_zero T * state = state`.
- it does not derive active-support vanishing from `symmetryAdaptedXi z = 0`.

### 2.2 Hodge/trifactor dictionary bridge
File:
- `lean/InfoGeometry/GrandUnification/HodgeTrifactorBridge.lean`

Repo status:
- untracked (`?? lean/InfoGeometry/GrandUnification/HodgeTrifactorBridge.lean`)

Readout facts:
- exact = `P_plus`
- coexact = `P_minus`
- harmonic = `P_zero`
- `harmonicSector_eq_self_of_active_sectors_vanish`

Honest reading:
- this is a finite dictionary and projector-collapse lemma;
- it still requires active-sector vanishing as input.

## 3. Exact theorem corridor currently available

What is already compile-backed in the live tree is the following corridor:

1. Centered coordinate change:
   - `s = 1/2 + u + iv`.
2. Fixed-locus geometry:
   - mirror-fixed points are exactly `u = 0`.
3. Completed-Xi parity:
   - `Xi(z) = Xi(-z)`.
4. J-even / J-odd projector readback:
   - the odd projector vanishes on centered `Xi` readouts.
5. Trifactor projector algebra:
   - if the active `P_plus + P_minus` support vanishes, then the state is localized in `P_zero`.
6. Topological sign-flip surface:
   - exact/coexact sectors flip sign under the topological involution, while the harmonic sector survives.

This is a real corridor.

## 4. Exact missing bridge

The missing theorem is an unconditional implication of the form:

- from a centered `Xi` zero, mirror/J-fix data, or equivalent tracked owner hypotheses,
- derive active-support vanishing:
  - `(P_plus T + P_minus T) * state = 0`,
  or equivalently enough hypotheses to conclude `P_zero T * state = state`.

In other words, the live repo still lacks a tracked owner theorem of the shape:

- `symmetryAdaptedXi z = 0 -> activeSupportZero`, or
- `centeredXi/J-fixed hypotheses -> P_zero-localization`, or
- `zero condition -> exact/coexact annihilation on the specific zeta mode`.

That implication is exactly where the closure debt still sits.

## 5. Bottom line

Safe statement:
- Yes: the repo really does formalize the centered chart `s = 1/2 + u + iv`, the fixed-line condition `u = 0`, the evenness `Xi(z) = Xi(-z)`, and finite projector consequences once active support is known to vanish.

Unsafe statement at present:
- No: the live tracked corridor does not yet prove that every centered `Xi` zero forces active-support collapse or `P_zero` localization, and therefore it does not yet justify an RH-closure claim from that route alone.
