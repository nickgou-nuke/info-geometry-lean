# Vopson proposal: mathematical extraction and Lean formalization

## Result and source

Four Lean modules extract the precise mathematical content of Melvin M.
Vopson's *Experimental protocol for testing the mass-energy-information
equivalence principle*, AIP Advances 12, 035311 (2022),
DOI 10.1063/5.0087175. The modules contain 32 theorem declarations and three
definitions. They connect the preceding reconstruction framework to a genuine
erasure map on the full matrix algebra, then separate energy bookkeeping,
channel assumptions, spectral inference, and momentum constraints.

The [theorem contract](VOPSON_INFORMATION_ENERGY_CONTRACT.md) records source
provenance, owner searches, carriers, hypotheses, and scope boundaries.
All page references below are PDF pages. The PDF has a publisher cover, so
its article page numbers are one less than the PDF page numbers.

## 1. Logical erasure is a trace/remainder decomposition

Owner: `InfoGeometry.Physics.InformationEnergy.TraceErasure`.

Let `K` be a field, let `n` be a finite index type, and let `sigma` be any
matrix with trace one. Define the maps using native Mathlib objects:

\[
E=\operatorname{tr}:M_n(K)\to K,
\qquad D(z)=z\sigma.
\]

Trace normalization proves `E.comp D = LinearMap.id`. The earlier
`Holographic.BoundaryReconstruction` owner therefore applies directly.
The resulting reset map is the native expression
`(Matrix.traceLinearMap n K K).smulRight sigma`, acting as

\[
\mathcal R_\sigma(X)=\operatorname{tr}(X)\sigma.
\]

The new module proves:

\[
\mathcal R_\sigma^2=\mathcal R_\sigma,\qquad
\ker\mathcal R_\sigma=\ker\operatorname{tr},\qquad
\operatorname{range}\mathcal R_\sigma=K\sigma.
\]

`traceSplitEquiv` constructs the actual linear equivalence

\[
M_n(K)\simeq_K K\times\ker\operatorname{tr},
\qquad
X\longmapsto
\bigl(\operatorname{tr}X,\ X-\operatorname{tr}(X)\sigma\bigr).
\]

Its inverse sends `(z,Y)` to `z • sigma + Y`. The fiber theorem identifies
exactly which inputs become indistinguishable: their reset outputs agree if
and only if their traces agree.

The idempotent here is the **superoperator** `R_sigma`. A mixed prepared
matrix `sigma` need not satisfy `sigma * sigma = sigma`.

### Noncommutative information is lost in a precise way

Native cyclic trace gives

\[
\mathcal R_\sigma(XY-YX)=0.
\]

The exact multiplication defect is

\[
\mathcal R_\sigma(XY)-\mathcal R_\sigma(X)\mathcal R_\sigma(Y)
=\operatorname{tr}(XY)\sigma
-\operatorname{tr}(X)\operatorname{tr}(Y)\sigma^2.
\]

No input matrices are diagonalized or assumed to commute. For distinct
indices `i` and `j`, the matrix unit `E_ij` is nonzero with zero trace.
Consequently the reset is not injective. Further,

\[
\mathcal R_\sigma(E_{ij})=0,
\quad\mathcal R_\sigma(E_{ji})=0,
\quad\mathcal R_\sigma(E_{ij}E_{ji})=\sigma\ne0,
\]

so it is not multiplicative. The module proves that no invertible conjugation
`X |-> U * X * U^-1` on this same matrix algebra can implement the reset.
This does not exclude a larger-system unitary realization followed by discarding
an environment; no such dilation is constructed in this task.

The existing `Quantum.ReplacementStateChannel` owner has this same formula
and separately proves complete positivity for positive output states. The
present results certify the algebraic trace map over arbitrary fields. Its
complete-positivity import closure is not part of this selected verification,
and trace normalization alone is not a positivity hypothesis.

## 2. Erasure heat and stored energy are separate quantities

Owner: `InfoGeometry.Physics.InformationEnergy.EnergyAccounting`.

The paper assigns a proposed energy `q = I kB T log 2` to information, then
assigns the mass `q/c^2` to that energy. A heat-cost constraint by itself does
not establish this stored-mass assignment.

The first-law countermodel is explicit. Under

\[
\Delta U=W-Q,\qquad Q\ge B,
\]

choose `Q=B`, `W=B`, and `Delta U=0`. Thus even a positive, saturated erasure
heat bound is compatible with unchanged stored energy when work is supplied.
The theorem refutes an implication between these balance constraints. It does
not experimentally refute the paper's separate mass conjecture.

Existing Landauer-named repository owners define candidate heat expressions
and prove consequences such as positivity. Their inspected statements do not
derive the particle-mass assignment or an emitted-photon channel. The new
balance theorems therefore keep `q` as explicit supplied energy data.

## 3. The mass ledger must count each contribution once

Equations 3 and 5 on PDF pages 3-4 define

\[
m_{\rm total}=m_{\rm physical}+q/c^2.
\]

For `c != 0`, Lean proves

\[
m_{\rm total}c^2=m_{\rm physical}c^2+q.
\]

Equation 9 on PDF page 5 adds `q` again on top of `m_total c^2`. If the mass
symbol retains the earlier definition, that ledger counts the same energy
twice. For a particle pair the formalized excess is exactly `q1 + q2`, and
the double-counted ledger is strictly larger when that sum is positive.

The finite output-budget theorem is stronger than a single scalar cancellation:
if a gamma-energy sum already equals the exact input energy, conservation and
nonnegativity imply that **every** extra-channel energy in the finite family
is zero.

A consistent alternative allocation remains possible. Let `m` denote each
particle's total rest mass and `q` its assigned extra-channel energy. Under

\[
2mc^2=2E_\gamma+2q,
\]

the proved relation is

\[
E_\gamma=mc^2-q.
\]

The paper's gamma energies are described as approximately 511 keV. Such rounded
labels do not exclude a small shift. The obstruction concerns exact unchanged
total-rest-energy gamma outputs, not the existence of four-photon final states.

## 4. Conservation does not choose the photon channel

For every positive natural number `N` and positive scalar budget `Q`, the
module constructs a positive function on `Fin N` whose sum is `Q`: each value
is `Q/N`. This proves that scalar energy conservation alone does not select
two photons. Momentum, spin, transition amplitudes, and branching assumptions
are separate requirements.

If a chosen channel has `N` equal-energy photons and carries the fraction
`eta` of an energy budget `Q`, the explicit balance and photon relation are

\[
N E=\eta Q,\qquad E\lambda=hc.
\]

For positive allocated energy, the formal consequence is

\[
\lambda=\frac{Nhc}{\eta Q}.
\]

The code then derives the paper's Eq. 11 from the additional assumptions
that the complete proposed pair energy `2 I kB T log 2` is assigned equally
to exactly two photons. A separate concrete countermodel shows that positive
total output can coexist with zero IR allocation when another channel carries
the budget. This matches the paper's own PDF page 7 qualification: IR conversion
is an additional strong assumption, and a different channel might carry the
proposed energy.

## 5. Spectral scaling and parameter inference

Owner: `InfoGeometry.Physics.InformationEnergy.ThermalSpectrum`.

The proposed monochromatic law is

\[
\lambda(h,c,k_B,I,T)=\frac{hc}{I k_B T\ln2}.
\]

The native real-analysis and ordered-field results prove:

- Positive parameters give a positive wavelength.
- `lambda * I * T = h*c/(kB*log 2)`.
- Scaling temperature by positive `a` divides wavelength by `a`.
- Wavelength is strictly decreasing on positive temperatures.
- At fixed positive temperature, wavelength order reverses information order.
- Positive wavelength data give the exact conditional inversion
  `I = h*c/(kB*T*log 2*lambda)`.

PDF page 5 uses the word "proportional" for the dependence on temperature and
information. Equation 11 and its plotted curves instead give **inverse**
proportionality.

An explicit sensitivity model assigns only a fraction `eta` of the proposed
per-particle energy to the putative emitted photon. In this model, equal
positive-channel wavelengths are equivalent to

\[
\eta_1 I_1=\eta_2 I_2.
\]

The transformations `eta |-> a eta`, `I |-> I/a` preserve the spectrum.
Therefore wavelength identifies the effective product `eta I`; recovering
intrinsic `I` requires knowledge of the allocation. Physical restrictions such
as `eta <= 1` must also be retained when choosing reparametrizations.

Here `eta` means **emitted energy allocation**, not detector efficiency.
Failing to detect some photons changes counts and does not by itself change
each detected photon's wavelength.

## 6. Momentum conservation: the two- and four-vector cases

Owner: `InfoGeometry.Physics.InformationEnergy.MomentumBalance`.

The code reuses `Physics.LorentzBoostMinkowski.FourVector` and its actual
`(+---)` quadratic form. It adds a native `Fin 3 -> Real` spatial projection.
The interpretation uses `c=1`, so the time component is energy.

For two future-null vectors, zero total spatial momentum forces equality of
their squared time components. Nonnegative time components then force equal
energies. If their total energy is fixed, each is half that total.

For four vectors, the module proves the conditional residual result: total
spatial momentum zero **and a separately balanced gamma pair** imply a balanced
residual pair; future-null residual vectors then have equal energies.

The separate-pair assumption cannot be removed. The explicit vectors

\[
(1,1,0,0),\quad (1,0,1,0),\quad
(1,-1,0,0),\quad (1,0,-1,0)
\]

are strictly future-null and have zero total spatial momentum and total energy
four. The first two have nonzero combined spatial momentum. Thus total
four-particle conservation does not impose the paper's designated pairwise
back-to-back geometry by itself.

These are kinematics results. No spin/helicity representation, QED scattering
amplitude, or emission probability is supplied.

## 7. Numerical checks, separate from the Lean certificate

Evaluating Eq. 11 with the paper's printed `h = 6.62e-34` and
`kB = 1.38064e-23`, using `c = 299792458 m/s` and `T = 300 K`, gives the
following values. The electronvolt conversion uses
`1 eV = 1.602176634e-19 J`.

| Conditional quantity | Numerical evaluation |
|---|---:|
| Photon wavelength for `I=1` | 69.1276 micrometres |
| Photon wavelength for `I=1.509` | 45.8102 micrometres |
| Photon wavelength for `I=3` | 23.0425 micrometres |
| Per-photon proposed energy for `I=1.509` | 0.02703996 eV |
| Proposed two-photon energy | 0.05407992 eV |

The approximate 50-micrometre prediction is consistent with the rounding in
the source. These are numerical evaluations of a conditional model, not
observations and not kernel-certified numerical bounds.

The copper example on PDF page 3 also has internal arithmetic inconsistencies:

- Its stated isotope proportions give `0.7*34 + 0.3*36 = 34.6`, not `34.5`.
- Using its printed constituent counts and converting molar mass to
  `0.06355 kg/mol` gives about `3.13869e27` bits per kilogram, rather than
  the printed `2.98e27`.
- Its Eq. 2 then gives about `3.34205e-11 kg` for a 100 K change. Using its
  printed bit count instead gives about `3.17308e-11 kg`.

No exact value of intrinsic particle information is derived from these checks.
The supplied paper does not specify a probability distribution that would turn
its cited ensemble estimate into a theorem assigning 1.509 bits to every
individual electron and positron.

## 8. Verification and integration scope

The four new modules are imported by `InfoGeometry.All`. Dependency and
toolchain pins remain unchanged. The selected closure also includes the
previous boundary-reconstruction owner, `Algebra.FiniteSpinAlgebra`, and
`Physics.LorentzBoostMinkowski`.

The independent QA disposition is `ACCEPTED_WITH_LIMITED_SCOPE`.

| Check | Observed result |
|---|---|
| Independent fresh source-closure compilation | All seven repository modules compiled without incremental reuse; exit zero and zero warnings for every module |
| Native axiom audit | 73 declarations including generated auxiliaries; only `propext`, `Classical.choice`, and `Quot.sound` |
| Public source declarations | 32 theorems and three definitions |
| Strict placeholder checks | All four files passed; zero hard findings; two short-proof advisory findings independently accepted |
| Semantic-vacuity gate | Complete four-file coverage; passed at error threshold; one native trace-corollary warning independently accepted |
| Strict source screener and refutation | Both passed with zero traps, errors, or warnings |
| Static Gate 4 | All four final owner hashes covered by clean static results; separate native compilation supplies the kernel evidence |
| Independent mathematical and documentation review | Passed, including the explicit proof-fact repairs |
| Root path-package preflight | Exit one for the existing dependency blockers below |

The two short-proof advisories concern a linear energy-balance consequence
and native cyclic trace. Their hypotheses and mathematical content were
independently reviewed. The strict screener's earlier lexical warnings about
implicit tactic context were resolved by explicitly naming the actual
`linarith` facts and positivity chain; no gate was suppressed.

The native audit counts by owner are 19 for TraceErasure, 31 for
ThermalSpectrum, 17 for EnergyAccounting, and six for MomentumBalance.
A selected closure check does not certify the unchanged remainder of
`InfoGeometry.All`.

The independent preflight reconfirmed that Atlas and HomotopyHypothesis
sources/configurations are absent and the pinned GIFT gitlink
`e6f3c3ac2140c2324fb2ae029c32233e73aa5e92` is uninitialized.
InfoGeometryCore passes the path-package preflight. The required root gate
remains incomplete; draft publication is not a certificate that this gate or
the whole root package build passed.

### Reproduce selected verification

From the repository root, with the exact pinned native Mathlib cache:

```bash
python3 tools/quality/check_clifford_dirac.py \
  --mathlib-root /path/to/mathlib-4.34.1 \
  --lean /path/to/lean-4.34.1/bin/lean \
  --output /tmp/vopson-verification \
  --target InfoGeometry.Physics.InformationEnergy.TraceErasure \
  --target InfoGeometry.Physics.InformationEnergy.ThermalSpectrum \
  --target InfoGeometry.Physics.InformationEnergy.EnergyAccounting \
  --target InfoGeometry.Physics.InformationEnergy.MomentumBalance
```

The maintained checker verifies dependency/toolchain identity, holds the shared
build lock, compiles the exact repository import closure, and audits selected
declarations. Omit incremental reuse for an independent fresh verification.

## Remaining physical hypotheses

The proved branches do not establish intrinsic stored particle information,
temperature-dependent electron rest mass, equality of electron/positron
information from CPT, logical erasure from physical annihilation, saturation
of an erasure heat bound, a particular radiative channel, or information as a
new state of matter. Each would require additional definitions, physical
assumptions, and evidence. The paper itself labels the underlying proposals
conjectures and explicitly qualifies its proposed IR channel.
