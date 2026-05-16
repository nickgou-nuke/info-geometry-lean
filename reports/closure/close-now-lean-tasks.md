# Close-Now Lean Tasks

Generated: 2026-05-16

These are closure tasks that should be paid before attacking RH-level sockets.

## 1. Close `CayleyCriticalWitness`

Target:
`InfoGeometry.Canonical.PrimeHurwitzLimit.CayleyCriticalWitness`

Owner class:
`mathlib_owned`

Required Lean work:
- Prove `cayleyInv (cayley s) = s` for `s != 1`.
- Prove `OnCriticalLine s -> OnUnitCircle (cayley s)`.
- Prove `OnUnitCircle (cayley s) -> OnCriticalLine s`.
- Prove `cayley (1 - s) = (cayley s)⁻¹` under nonzero/nonone side conditions.

Why now:
This is complex algebra, not an open problem.

## 2. Close `RiemannFieldPullback`

Target:
`InfoGeometry.Canonical.PrimePartitionPolynomials.RiemannFieldPullback`

Owner class:
`mathlib_owned`

Required Lean work:
- Instantiate `field s = s - (1/2 : ℂ)`.
- Instantiate `localFugacity s i = Complex.exp (-(field s) * (D.ell i : ℂ))`.
- Use `Complex.abs_exp` and real-part arithmetic to close `re_pos_inner` and `re_neg_outer`.
- Close `critical_of_field_re_zero` by arithmetic on real parts.

Why now:
This is elementary complex exponential algebra.

## 3. Verify finite ferromagnetic closures remain owned

Target:
`InfoGeometry.Canonical.PrimeLeeYangFerromagnet`

Owner class:
`repo_owned`

Current status:
Focused build passed.  The finite positivity proofs are already present for stored `ell_pos`.

Optional strengthening:
Add a constructor showing `ell_pos` follows from `Nat.Prime (p i)` and `ell_eq_log`, if the extra arithmetic coercion proof is worth the dependency cost.

## 4. Keep `LeeYangApproximants.renormZ_lee_yang` closed

Target:
`InfoGeometry.Canonical.PrimeHurwitzLimit.LeeYangApproximants.renormZ_lee_yang`

Owner class:
`repo_owned`

Current status:
Closed by `mul_eq_zero` plus `renorm_nonzero`.

Potential follow-up:
Add a ledger note tying this theorem directly to D16 so the audit graph sees the renormalization nonzero owner.

## 5. Keep finite SUSY parity readback closed

Target:
`InfoGeometry.Canonical.PrimeSUSYVacuum.wittenCharacter_eq_parityTrace`

Owner class:
`repo_owned`

Current status:
Closed by direct field projection to `PrimeGasPartitions.finiteParityTrace`.

Boundary:
Do not promote the infinite Euler product to a theorem here.  It remains witness-gated in `PrimeGasPartitions`.

## 6. Keep pulled Lee-Yang zero-to-line logic closed under witnesses

Target:
`InfoGeometry.Canonical.PrimePartitionPolynomials.zero_implies_field_re_zero`
and
`InfoGeometry.Canonical.PrimePartitionPolynomials.zero_implies_critical_line`

Owner class:
`repo_owned_under_D14_D15_witnesses`

Current status:
Focused build passed.  The logical trichotomy step is closed, conditional on `LeeYangPolydiscWitness` and `RiemannFieldPullback`.

Next improvement:
After D15 is instantiated, only D14 should remain as the Lee-Yang literature socket for this file.

