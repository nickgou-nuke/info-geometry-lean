# Two-sheet residue and zero-mode pairing

The supplied narrative yields two mathematical chains with different
hypotheses: local pole transport followed by finite residue balance, and
operator intertwining followed by equality of kernel dimensions.  Sign
monodromy supplies a representation of the integer loop group.  None of
these chains identifies a fluid velocity or derives a dissipative evolution.

## Carriers and dependency order

| Supplied concept | Existing carrier | New result |
| --- | --- | --- |
| Left/right sheet | `Topology.Weyl.ChiralSheet`, `ChiralSheet.swap` | `reflectedDeck`, its involution and absence of fixed points |
| Local pole | `Analysis.BipolarSimplePoleResidues.HasSimplePoleCoefficientAt` | Uniqueness, reflection, pullback, and conjugation of actual punctured-limit coefficients |
| Twin-pole balance | The same limit predicate on the two sheet fields | `twin_pole_cancellation`, `pairedField_hasCoefficient` |
| Closed finite family of punctures | Native `Finset`, stable under `reflectedDeck` | `finite_residue_balance`, proved by `Finset.sum_involution` |
| One-loop sign reversal | Native `Multiplicative ℤ →* ℂˣ` | `signMonodromy`; one loop is `-1`, two loops are `1` |
| Chiral zero modes | `Canonical.FiniteSuperchargeIndex.FiniteSupercharge`; native `LinearMap.ker` | `kernelEquivOfIntertwining`, using `LinearEquiv.ofSubmodules` |
| Index neutrality | Existing kernel-dimension `wittenIndex` | `wittenIndex_eq_zero_of_intertwining`, using native `finrank_eq` |
| Regular combined observable | Two complete principal parts in the same local coordinate, with analytic remainders | `analytic_extension_of_opposite_principal_parts` |

The entry module is `InfoGeometry.Canonical.TwoSheetResiduePairing`, exported
by `Canonical.All`.  Its analytic and finite-supercharge helper modules may
also be imported separately.

## Exact transformation law

Write the owner predicate as

\[
\lim_{z\to a,\;z\ne a}(z-a)f(z)=r.
\]

It permits zero coefficient and does not alone assert meromorphicity or an
exact pole order.  For the scalar coefficient and the one-form pullback,
respectively, the new theorems give

\[
f(c-z):\quad (c-a,-r),\qquad
-f(c-z):\quad (c-a,r).
\]

The second sign is the Jacobian of the reflection.  Consequently the pasted
condition `uR z = -uL (-z)` gives equal coefficients.  Opposite coefficients
follow from `uR z = uL (-z)`, with the reflection Jacobian accounted for when
interpreting the coefficients as one-forms.

The anti-linear transformation is also explicit:

\[
\overline{f(\overline{c-z})}:
\quad(c-\bar a,-\bar r).
\]

Ordinary scalar cancellation with `r` additionally requires `r = conj r`,
or a specified different rule for comparing the two readouts.  Complex
conjugation is not silently identified with a complex-linear involution.

## What cancels and what extends

The finite balance theorem derives opposite coefficients from actual local
limits and the field seam law.  It assumes closure of the finite puncture set
under the deck involution.  It is not the global residue theorem for an
arbitrary compact Riemann surface.

`no_continuous_extension` proves that a nonzero coefficient excludes every
continuous extension of that individual channel.  Applied to the existing
`dlog01`, it proves this at both poles, whose coefficients are `1` and `-1`.
Thus a balanced residue sum does not remove either pole or turn it into a
branch point.

A positive extension theorem is provided separately.  If, in one local
coordinate, the two fields have complete principal parts `r/(z-a)` and
`-r/(z-a)` with analytic remainders, their sum extends analytically as the sum
of the remainders.  This states the additional hypotheses under which a
regular combined observable is obtained.

## Zero modes and monodromy

For an existing `FiniteSupercharge m n`, a linear equivalence
`e : Plus m ≃ₗ[ℝ] Minus n` satisfying

\[
q_- e = e^{-1} q_+
\]

restricts to an equivalence of the two kernels.  Their dimensions, and hence
their difference, are equal.  The kernel equivalence is constructed; equal
kernel dimensions are not supplied as a premise.

The examples retain any number of paired zero modes at index zero and give
index one for one extra unpaired zero mode.  A nonzero index is therefore
well-defined in this finite setting.  The existing index counts kernels of
the supplied odd blocks; no identification with a heat supertrace, Fredholm
index, cohomological Euler characteristic, or physical Hamiltonian is made.

The sign character proves integer monodromy and norm preservation.  A global
sign reversal alone neither swaps arbitrary chiral operators nor creates a
dissipative sink.  A geometric bundle, a compact doubled surface, and a
Navier–Stokes readout with an analytic regularity estimate remain separate
constructions.

## Validation environment

Base repository commit: `ec7c289661eb1cd45b2afcd886847ca992318de5`.
Pinned Mathlib revision: `8f9d9cff6bd728b17a24e163c9402775d9e6a365`.
The repository requests Lean 4.28.1; the available native cache for that
Mathlib source revision uses Lean 4.28.0.  Local verification uses the matching
4.28.0 runtime, with untouched sources and separate output artifacts.  Neither
the repository toolchain nor its dependency manifest is changed.

All three new modules passed that kernel check: 28 new theorems, zero errors,
and zero warnings in the new modules.  Their imported repository owners were
also checked; existing linter warnings in some of those owners are unchanged.
The nine principal declarations were inspected with `#print axioms` and depend
only on `propext`, `Classical.choice`, and `Quot.sound`.  The staged proof-proxy
gate and whitespace check passed.  The entire `Canonical.All` aggregate and
the requested 4.28.1 runtime were not validated in this session.
