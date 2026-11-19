# Radon leakage, boundary conditions, and observation artifacts

## Scope and source record

This extends the original nine-cartridge audit with the subsequent leakage
hypotheses and supplied manuscript. The mathematical models are useful; the
data do not identify a unique physical cause of either endpoint deviation.

- `leak_draft_081239.txt` and `leak_draft_duplicate_081452.txt` preserve the two
  supplied leak drafts. They are byte-identical, SHA-256
  `996f02691f41c456069258389440faacc11f4552a9b01a116aa66ae906b46b0e`.
- `manuscript_222Rn.tex` preserves the LaTeX source uploaded as `222Rn.md`,
  SHA-256 `0ec9986a1fe53a92d1c1f52ccf4cdba584594801665076936690e36555fb1ed0`.
- The inline follow-up additionally proposes a constant `0.75 cps` correction
  to the original 609 keV sinh model and a `2*R2` inlet extrapolation. Those
  parameters are recorded explicitly in the reproducible numerical audit.
- All numerical comparisons retain the original start-time correction of the
  supplied count areas. They do not silently apply the finite-acquisition factor.

## Concentration convention in the new manuscript

Unlike an unspecified use of the word "pore diffusivity," this manuscript
explicitly defines

\[
C=S C_g,\qquad S=\varepsilon+\rho_bK_a,\qquad
D_{\rm pore}=(\varepsilon/\tau)D_0,\qquad D_e=D_{\rm pore}/S.
\]

For constant storage this consistently gives
`J = -D_pore * C_g' = -D_e * C'`. Porosity is already included in its defined
`D_pore`; no missing-porosity criticism applies to this version. The canonical
Lean interface uses pore-gas concentration and `J = -B*C'`, so its `B` is the
manuscript's bulk coefficient `D_pore`. A Robin conductance must be expressed
against the same concentration convention as its concentration variable.

The manuscript still mixes its stated geometry `L=9*d`, `x_i=(i-1/2)*d` with
`10-i` in the discrete Dirichlet and linear expressions. The consistent
midpoint argument is `mu*(9.5-i)` for both finite-column shapes.

## Three separate models

### Two prescribed reservoir concentrations

For `D*k^2=lambda`, and a nonzero `sinh(k*L)`, the two-reservoir solution is

\[
C(x)=C_{\rm in}\frac{\sinh(k(L-x))}{\sinh(kL)}
    +C_{\rm out}\frac{\sinh(kx)}{\sinh(kL)}.
\]

This satisfies both prescribed endpoint values and the homogeneous equation.
At cartridge centers, the second term uses `sinh(mu*(i-1/2))`. Its spatial
contribution is not a constant offset. Uniform cartridge averaging multiplies
the whole homogeneous hyperbolic profile by the common factor already proved
in `RadonDiffusionProfiles`.

### Robin exchange with an external reservoir

For the outlet-basis family

\[
C(x)=a\sinh(k(L-x))+b\cosh(k(L-x)),
\]

the actual endpoint values are

\[
C(L)=b,\qquad J(L)=Bk\,a.
\]

Consequently the boundary law

\[
J(L)=h\big(C(L)-C_{\rm env}\big)
\]

is exactly the coefficient condition `B*k*a=h*(b-C_env)`. This is a boundary
assumption. A positive outgoing flux alone does not imply positive endpoint
concentration: the ideal Dirichlet profile has `C(L)=0` and strictly positive
outgoing flux for positive inlet concentration, length, attenuation, and `B`.
`dirichlet_zero_value_positive_flux` proves this directly for the actual profile.

For zero external concentration, let `beta=h/(B*k)`. The general normalized
Robin family is

\[
C_\beta(x)=C_0
\frac{\cosh(k(L-x))+\beta\sinh(k(L-x))}
     {\cosh(kL)+\beta\sinh(kL)}.
\]

The denominator is positive for `beta,k,L >= 0`. Its exact special cases are
Neumann at `beta=0` and `C0*exp(-k*x)` at `beta=1`.

A positive shifted-sinh expression has the expansion

\[
A\sinh(k(L+\delta-x))
=A\cosh(k\delta)\sinh(k(L-x))
 +A\sinh(k\delta)\cosh(k(L-x)).
\]

Under its Robin law, nonzero amplitude, and positive `B,k,delta`, it requires

\[
\tanh(k\delta)=\frac{Bk}{h},\qquad h>Bk.
\]

Thus this representation covers the `beta>1` branch. The supplied appendix
recognizes a corresponding Biot-number restriction, but its main discussion
treats the shifted expression as universal and incorrectly links an infinite
shift to a blocked end. With fixed inlet normalization, increasing the positive
shift approaches the exponential case; at fixed amplitude the expression
diverges. The current Lean source proves the coefficient identities, branch
restriction, and `beta=1` exponential identity; it does not claim a `Tendsto`
theorem for that limiting interpretation.

There is an exact obstruction to the proposed flattening explanation:

\[
\sinh(u+v)=e^v\sinh u+e^{-u}\sinh v,
\qquad
\frac{\sinh(u+v)}{\sinh u}>e^v\quad(u,v>0).
\]

For a positive shifted-sinh tail at `mu=0.686`, the adjacent ratio is therefore
greater than `exp(mu)=1.9857566`. The entered corrected 609 keV ratio at
cartridges 8/9 is `1.635729`. Under consistent homogeneous geometry and detector
response, that particular shifted-sinh formula cannot produce the proposed
flattening. This excludes the specified formula at its specified attenuation;
it does not identify an alternative physical mechanism.

Robin exchange, internal dual-porosity transport, advective bypass, and ambient
radon ingress require different physical assumptions. A Robin endpoint law
does not establish the presence of two pore populations or a bypass channel.

### Additive detector background or another observation component

A count-rate observation can have the form `response*C + background`. If a
constant is instead added to the homogeneous concentration profile itself,

\[
D(C+b)''-\lambda(C+b)=-\lambda b.
\]

For a nonzero loss rate and nonzero offset, this is not the same homogeneous
equation with a changed boundary. It is compatible with a constant distributed
source term `+lambda*b`, or with a separate additive observation component.
`constantOffset_solves_iff` preserves both differentiability hypotheses and
proves that the homogeneous equation holds exactly when `lambda*b=0`.

A stationary measurement-time background also changes under the draft's
reference-time correction:

\[
(s_i+b)e^{\lambda\Delta t_i}
=s_i e^{\lambda\Delta t_i}+b e^{\lambda\Delta t_i}.
\]

Therefore a constant floor in corrected rates is not automatically a constant
instrumental background. The integrated acquisition model has an exact inverse
after subtracting the specified stationary background counts `b*t_live`.
That theorem treats the background as an input; it does not estimate it from
an endpoint fit. The supplied peak areas have no residual-background or
peak-fit covariance model attached.

## Numerical checks of the proposed formulas

For the inline proposal `0.975*sinh(0.686*(10-i))+0.75`, the recomputed values are:

| Cartridge | Observed 609 keV cps | Proposed cps | Observed minus proposed cps |
|---:|---:|---:|---:|
| 1 | 175.078353 | 234.799042 | -59.720688 |
| 2 | 127.068219 | 118.612407 | 8.455811 |
| 3 | 63.416682 | 60.100916 | 3.315766 |
| 4 | 38.163377 | 30.632379 | 7.530998 |
| 5 | 19.507502 | 15.786575 | 3.720927 |
| 6 | 9.713939 | 8.298813 | 1.415126 |
| 7 | 4.837865 | 4.505010 | 0.332855 |
| 8 | 2.529927 | 2.548695 | -0.018767 |
| 9 | 1.546667 | 1.472558 | 0.074109 |

The corrected-rate `R²` improves from `0.985121` to `0.988275` over 2–9,
and worsens from `0.881814` to `0.880293` over 1–9. The tail improves, but the
claimed whole-column match is not reproduced.

The two identical leak drafts contain further arithmetic inconsistencies:

| Supplied expression | Evaluation | Recomputed cps | Claimed cps |
|---|---|---:|---:|
| `1.41*sinh(log(2)*(9.5-i))+1.55` | Cartridge 9 | 2.048510 | 1.55 |
| `2.21*sinh(log(2)*(9.5-i))+2.55` | Cartridge 9 | 3.331353 | 2.55 |
| `0.675*sinh(0.686*(10.6-i))` | Cartridge 2 | 123.149950 | 122.9 |
| `0.675*sinh(0.686*(10.6-i))` | Cartridge 9 | 0.898862 | 1.44 |

The floor models equal their floors at the physical outlet coordinate `i=9.5`,
not at the last cartridge center `i=9`. All 18 predictions in the shared table
(repeated identically in both leak drafts) disagree with the stated formula at
their displayed precision.

The manuscript does not specify a numerical shifted-sinh amplitude. Even with
that amplitude free, its printed 609 keV shifted-sinh column is inconsistent
with a single amplitude at `mu=0.686, delta=1.10`: the first row requires
`A in [0.67099164,0.67101924]`, while the last requires
`A in [1.07761302,1.08512252]`. These are printing-rounding intervals, not
measurement-uncertainty intervals. Its plotted curve labeled leaking/cosh is
literally the original cosh formula, rather than the advertised shifted sinh.
Under the stated homogeneous transport law, that cosh profile has zero outlet
derivative and therefore zero outlet flux; the plot label does not change its
boundary condition.

For `phi=6.174`, `phi/sinh(phi)=0.0257196096938`, or `2.57196096938%`.
This is the same-inlet Dirichlet-to-no-loss-linear outlet flux ratio. It is
not a measured transmission of the proposed Robin column, nor a ratio of
outlet flux to inlet flux. The new formal owner proves the actual flux ratio
directly; it does not substitute into a totalized `0/0` concentration ratio.

## What the endpoint data establish

Relative to the assumed baseline `2*R2`, the inlet deficit is `31.108520%` at
609 keV and `31.132987%` at 352 keV. Relative to the original fixed cosh curve,
the corresponding deficits are `28.379775%` and `28.371976%`. These are
conditional residuals from different extrapolations, not measured loss fractions.

The recorded `7753 s = 2 h 9 min 13 s` is a difference between measurement
start times. Even if disassembly preceded the first measurement, that span does
not establish how long a particular cartridge was unsealed, its sealing quality,
or its desorption rate. There is no supplied measurement assigning a 30% capacity
loss to humidity or showing that all subsequent cartridges received dry gas.

Independent experiments demonstrate that radon retention and desorption depend
on carbon, water loading, geometry, and exposure protocol. One study reports
strong water-loading dependence in its tested canisters; a different study
found no detectable humidity dependence during its short exposures and observed
desorption from unsealed samples. These establish plausible mechanisms, not
quantitative explanations for these nine cartridges. See the primary references
below.

The measured lines belong to lead-214 and bismuth-214, rather than to radon-222
itself. If radon escapes while some progeny remain, the subsequent peak rates
depend on decay-chain evolution and retention. Converting a peak-rate deficit
into a fraction of radon lost therefore needs an appropriate time-dependent
chain model. The single-exponential acquisition theorem is conditional and does
not establish that extra model or its equilibrium assumptions.

The 352/609 count-rate ratio is not a photon branching ratio or an activity ratio
without response corrections. For a two-line mixture

\[
\rho(A)=\frac{q_1 A+b_1}{q_2 A+b_2},
\]

the ratio equals `q1/q2` exactly when `q2*b1=q1*b2`, under the explicit nonzero
denominators in `mixtureRatio_eq_response_ratio_iff`. A change at low signal can
be consistent with residual background, calibration/geometry changes, daughter
disequilibrium, or peak-estimation errors. The entered ratio alone does not
select one of those explanations.

Measurement order can also confound spatial and temporal loss. Under the
conditional affine-clock model `t_i=a+b*i`, an additional exponential loss gives

\[
A e^{-\mu i}e^{-\gamma t_i}
=A e^{-\gamma a}e^{-(\mu+\gamma b)i}.
\]

The code proves this identity without assuming the recorded times are exactly
affine. Removing the endpoint observations does not prove the remaining slope
is intrinsic. Descriptive log-linear fits on 2–7 give `mu=0.646880723` and
`0.649751443` for 609 and 352 keV, respectively; neither calculation supplies a
confidence interval or statistical test against `log(2)`.

Useful discriminating evidence includes recorded loading/disassembly/sealing
times, repeated spectra of the same retained samples, matched blank-container
and blank-carbon measurements, energy-dependent efficiency and peak-fit
uncertainties, recorded humidity/water uptake, and independently measured inlet,
outlet, and ambient concentrations or flow. These would constrain separate
mechanisms instead of choosing a background solely to improve the last points.

## Native owners and reproduction

- `RadonBoundaryModels.lean`: actual hyperbolic derivatives, two-reservoir
  profiles, Robin coefficient laws, a positive-flux Dirichlet counterexample,
  restricted shifted-sinh branch, strict tail-ratio inequality, and actual
  Dirichlet/linear outlet-flux ratio.
- `RadonObservationArtifacts.lean`: constant-offset residual and regularity,
  affine observation ambiguity, two-peak mixture ratio, background handling in
  decay correction, and conditional space/time loss confounding.

The compilation and axiom-audit status is reported separately for the exact
integrated source hashes; this scientific audit is not a compiler certificate.

```bash
python3 scripts/analysis/audit_radon_leakage.py \
  data/radon_diffusion/intake_20261118.txt \
  data/radon_diffusion/leak_draft_081239.txt \
  data/radon_diffusion/leak_draft_duplicate_081452.txt \
  data/radon_diffusion/manuscript_222Rn.tex \
  /tmp/radon-leakage-audit
```

The script uses Python and NumPy. The checked outputs are stored under
`data/radon_diffusion/leakage/`. Comparisons that borrow an amplitude from a
companion draft are labeled as such; the manuscript itself does not provide
every coefficient used in its table.

## Primary measurement references

1. [Scarpitta and Harley (1990), adsorption/desorption experiments](https://pubmed.ncbi.nlm.nih.gov/2398008/):
   dependence on bed depth and adsorbed water under the tested conditions.
2. [Maier et al. (2021), Radon Adsorption in Charcoal](https://pmc.ncbi.nlm.nih.gov/articles/PMC8122700/):
   short-exposure humidity findings and unsealed-sample desorption measurements.
3. [NIST RPD-P-23](https://www.nist.gov/system/files/documents/2024/01/29/Procedure%2023v100.pdf),
   equation (1): efficiency, photon-emission probability, live time, and corrections
   enter count-to-activity conversion.
4. [EPA high-resolution gamma-spectrometry guide](https://www.epa.gov/sites/default/files/2020-07/documents/guide_for_high_resolution_gamma_spectrometry_analyses_camera_ready.pdf):
   acquisition-time decay corrections and parent/daughter assumptions.
5. [IAEA-TECDOC-1712](https://www-pub.iaea.org/MTCD/Publications/PDF/TE-1712_web.pdf),
   Appendix, Table 5: radon-222 and the lead-214/bismuth-214 gamma lines.
