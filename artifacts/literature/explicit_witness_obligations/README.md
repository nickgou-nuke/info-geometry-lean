# Explicit witness obligation proof sources

Kernel formal sources used:
- `mathlib_Finset_Basic.lean`: finite big-operator algebra, including product/sum machinery.
- `mathlib_Analysis_Complex_Exponential.lean`: `Real.exp_sum`, `Complex.exp_sum`.
- `mathlib_ContinuousLinearMap.lean`: bounded linear operator carrier `H →L[𝕜] H`.

External mathematical references archived for the same finite facts:
- nLab / Wikipedia spectral theorem pages: finite spectral decomposition background.
- nLab / Wikipedia partition function and Gibbs measure pages: finite Gibbs partition factorization background.

Repository formalization:
- `lean/InfoGeometry/Canonical/ExplicitWitnessObligations.lean`
- `lean/InfoGeometry/Arithmetic/PrimonFockTraceFinite.lean`
