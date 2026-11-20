# Spectral-table numerical bridge

This directory reproduces the numerical comparison of a decimal five-channel
spectral table with an earlier rounded 352/609-keV table. It separates three
questions: agreement of geometric and Sinkhorn sample factors, spectral
interaction after double centering logarithms, and deviations of the common
sample profile from a fitted spatial exponential.

The code reads compact numerical fixtures. It does not require the prose from
which the earlier rounded table was extracted, and it does not install or fetch
dependencies.

## Run

From the repository root:

```bash
python3 tools/spectral_table_bridge/reproduce.py
```

The default destination is `artifacts/spectral_table_bridge/`, containing
`results/`, `figures/`, and `verification/`. To choose another destination:

```bash
python3 tools/spectral_table_bridge/reproduce.py --output-dir /tmp/spectral-bridge-check
```

The runner resolves input paths from its own location. It can therefore also be
invoked by its full path from another working directory. Relative custom output
paths are interpreted relative to the invoking working directory. Every public
entry point accepts `--output-dir` with the same destination convention.

The full run requires Python, NumPy, and Matplotlib in the existing environment.
It was verified with Python 3.12.14, NumPy 2.3.5, and Matplotlib 3.10.8. SciPy is
not required. To omit the plot and the Matplotlib dependency:

```bash
python3 tools/spectral_table_bridge/reproduce.py --skip-figure
```

The exact interval calculation can run independently using only the Python
standard library:

```bash
python3 tools/spectral_table_bridge/certify_decimal_two_line.py
```

Individual other entry points are `audit_spectral_domains.py` and
`plot_spectral_bridge.py`. The plot reads the numerical audit under the chosen
output directory; run the audit first, or supply `--input` explicitly.

## Input fixtures and provenance

Inputs are stored in `data/spectral_table_bridge/`. `PROVENANCE.json` supplies
SHA-256 fingerprints and the exact field mapping. Input integrity checks are
part of the calculations; editing a fixture requires an explicit review and
update of its pinned fingerprint.

| File | Role |
| --- | --- |
| `Radon_5Line_Master_Analysis.csv` | Byte-identical decimal-area source for nominal channels 77, 242, 295, 352, and 609 keV. |
| `rounded_two_line.json` | Compact extraction of the decay constant, acquisition fields, and rounded 352/609-keV areas for cartridges 1–9. |
| `prior_five_line_balancing_results.json` | Numerical reference used to verify the earlier all-nine normalization results. |
| `prior_two_line_bounds_audit.json` | Numerical reference used to reproduce the earlier rounded-input interval endpoints. |
| `PROVENANCE.json` | Fixture fingerprints, extraction scope, and field mapping. |

The compact rounded fixture has SHA-256
`eb8443cf5f2fd3f0e802f261465667c9725278529de72e9242b99291cf84445d`.
Its `original_source.sha256` records the original text fingerprint,
`882b6799b2787041c86e07b36c7fe892ee1e7807756e05273227ac73b9411754`.
The original text is not distributed. That fingerprint documents extraction
provenance; the public run verifies the extracted fixture and its consistency
with the retained numerical reference, rather than re-extracting an omitted
document.

All decimal quantities in `rounded_two_line.json` are strings so that parsing
does not introduce binary floating-point rounding. The field mapping from the
original fenced CSV is:

| Fixture field | Original field and conversion |
| --- | --- |
| `cartridge` | Column 1, `Cartridge No. (i)`, parsed as an integer. |
| `start_time` | Column 2, `Start Time`, retained verbatim. |
| `real_minutes_source` | Column 3, `T_real [min]`, retained verbatim. |
| `live_minutes_source` | Column 4, `T_live [min]`, retained verbatim. |
| `real_seconds` | Exact decimal value of column 3 multiplied by 60. |
| `live_seconds` | Exact decimal value of column 4 multiplied by 60. |
| `elapsed_seconds` | Column 5, `Elapsed Time dt [s]`, retained verbatim. |
| `areas.609` | Column 6, `Net Counts (609 keV)`, retained verbatim. |
| `areas.352` | Column 7, `Net Counts (352 keV)`, retained verbatim. |
| `lambda_per_second` | Parameter value next to `Rn-222 Decay Constant (lambda)`, retained verbatim. |

Only these measured fields and the decay constant were extracted. Prose and the
rounded source's spreadsheet formula columns are absent. The decimal CSV and
prior reference JSONs are retained byte for byte; unused derived columns or
reference metadata do not supply fitted parameters to the new calculation.

The two source versions have identical acquisition fields and decay constant
but different peak-area precision. For example, cartridge 9 at 609 keV is
1392.4 in the decimal source and 1392 in the rounded source. Neither source is
silently substituted for the other.

## Numerical conventions

Samples are rows and spectral channels are columns. Baseline corrected rates
are `area / live_seconds * exp(lambda * elapsed_seconds)`. No acquisition-time
integral correction is included in that baseline. A separate sensitivity
calculation applies the finite-acquisition factor conditionally on pure parent
decay and a constant live fraction.

The audit compares four channel selections: all five supplied channels; the
four gamma channels excluding the nominal 77-keV ROI; the three Pb channels
242/295/352; and 352/609. For each selection it balances all nine cartridges and
independently balances the interior seven, 2–8, with uniform probability margins.
Sample factors are recentered on the same comparison cartridges before their
relative differences are evaluated. Restricting geometric factors preserves
their fitted slope, while restricting a balanced plan generally changes its
column margins and is not equivalent to balancing the smaller table.

The nominal 77-keV ROI remains unresolved. No photon yield, species assignment,
pseudocount, or absolute efficiency is assigned to it. The input supplies net
peak areas without the covariance, background, or replicate information needed
for measurement-error intervals. SVD is descriptive; no physical cause or
statistical significance is inferred from its rank or singular values.

Selected decimal-source checks are:

| Quantity | Reproduced value |
| --- | ---: |
| All-five geometric slope, cartridges 2–8 | 0.654214245447861 per cartridge |
| All-five Sinkhorn slope, balancing all nine then fitting 2–8 | 0.6541678504539126 per cartridge |
| All-five Sinkhorn slope, balancing only 2–8 | 0.6541743020675433 per cartridge |
| All-five maximum Sinkhorn/geometric factor difference, all-nine comparison | 0.03277218260473878% |
| All-five maximum factor difference, interior normalization and comparison | 0.02718511447509992% |
| All-five interior maximum absolute log interaction | 0.052502856486543514 |
| All-five interior maximum common relative residual | 6.922871438189467% |
| Two-line decimal interior maximum factor difference | 0.0033282936054207864% |

Floating-point last digits may depend on Python, NumPy, and the numerical
backend. The rational certificate uses exact decimal-to-`Fraction` conversion,
explicit series-tail enclosures, exact root signs, and outward rational rounding;
no floating-point value decides a certified inequality.

## Interval-kernel preservation and verification

`audit_exact_two_line_bounds.py` is retained byte-identically, with SHA-256
`b22d93a4a44ec5e2d2b43c1b7c3d96585f2c76f5aea22b79218602efbacb5784`.
The new certificate imports its arithmetic and interval functions only. Its
legacy text parser and legacy command-line entry point are not called by this
workflow. Use `certify_decimal_two_line.py` as the public certificate entry point.

`reproduce.py` records dependency versions, script fingerprints, exit codes,
captured logs, and generated-file fingerprints under `verification/`. It also
checks the original rounded-input interval endpoints against the retained
reference JSON. The new decimal certificate and the old rounded certificate
remain separate. A Python interval certificate is not a Lean-kernel check of
the numerical endpoints and is not an experimental uncertainty interval.

The two-panel PNG/PDF figure shows `100 * expm1(h)` for the common spatial
residual and `100 * E` for the double-centered interior log interaction, with a
symmetric heatmap scale. Its caption and numerical metadata are saved alongside
the figure.
