# Color occupation and six-charge polynomial audit

## Source and scope

The user-provided 2026-10-24 intake claims universal polynomial cancellations for ordered three-channel color occupations, a quadratic Cartan expression, and a scaled charge formula. The default-branch search did not find the exact proposed declarations in the inspected source snapshot. This candidate adds focused owners rather than modifying an existing Clifford/Fock representation.

## Exact identities

- `ColorOccupationPolynomials.number_expansion`: ordered quark/diquark/baryon expression for `a+b+c`.
- `colored_sum`: sum of quark and diquark polynomials reduces to the ordered quadratic.
- `sector_sum`: four occupancy polynomials add to one without commutation assumptions.
- `cartan_polynomial`: the symmetrized ordered quadratic polynomial, including square-minus-linear defects.
- `ColorIsospinCharge.iso_partition`: two-channel ordered occupancy partition.
- `charge6_expansion`: charge expression expanded into ordered color-times-isospin terms.

These identities need only an associative `Ring A`. Their proof method is noncommutative polynomial normalization.

## Strict semantic boundary

No claim is made that the individual occupancy polynomials are idempotent, self-adjoint, mutually orthogonal, or nonzero under arbitrary ring substitutions. A true *spectral decomposition* and numerical eigenvalue theorem requires commuting idempotent occupation operators or the established concrete CAR matrix representation.

The defined scaled operator `charge6 = N_color + 3 (isoPlus - isoMinus)` corresponds to `Q = N_color/6 + (isoPlus - isoMinus)/2`, not `N_color/3 + (isoPlus - isoMinus)/2`. The numbers are formal charge weights, not automatically measured Standard Model particle charges.

The quadratic Cartan identity is a finite operator-polynomial relation, not a theorem proving nonperturbative SU(3) confinement or Regge slopes. The claimed physical table additionally needs group representation, dynamics and external physics evidence.

## Verification

These GitHub API changes are a **review draft**, not a kernel-verified build. The session lacks the repository's Lean/Lake binaries and build cache. Before acceptance run narrow `lake env lean`/locked Lake build, placeholder/vacuity screening and `#print axioms` under the repository's pinned toolchain, then the required full pre-push gate. No dependency pins were modified.
