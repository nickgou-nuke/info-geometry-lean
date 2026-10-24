# Jones phase versus permutation

The existing negative owner, `ProjectiveNullBoundaryJonesPermutationObstruction`,
proves that the native presented `B3` representation `phi : B3 →* GL8` cannot
factor through `braidPermutation`: the first generator square maps to `-I`
but its permutation is 1.

The constructive replacement uses the same carrier and actual permutation group:

- `Physics/JonesPhaseCharacter.lean` constructs `phase : B3 →* ℂˣ`, sending
  both generators to `i`, and the phase-removed representation.
- `Physics/JonesPermutationAction.lean` constructs `rho : Equiv.Perm (Fin 3) →* GL8`.
  Its state action fixes 0 and 7 and acts on ordered triples `(4,2,1)` and
  `(3,5,6)`. Native `Matrix.permMatrixHom` supplies the permutation matrices;
  conjugation by `diag(1,1,-1,1,1,-1,1,1)` supplies the signs.
- `Physics/JonesPhasePermutationFactorization.lean` identifies the two generator
  matrices, proves `phaseRemoved = rho.comp braidPermutation`, and proves
  `phi g = scalarUnit (phase g) * rho (braidPermutation g)`.
  On a fixed permutation fiber, `phi g = phi h` iff `phase g = phase h`.

This does not assert braid faithfulness or factorization of `phi` through
permutations alone. Scalar injectivity is proved by reading a matrix entry.

Parent locked build session 35628 passed (9,298 jobs, exit 0), recorded in
`/tmp/jones-factorization-current.log`. It compiled the full factorization.
Two unused simp arguments were then removed in response to compiler warnings.
Independent semantic review by Poincare passed the full factorization.
Independent kernel QA session 37195 passed: 9,278 jobs, exit 0, six axiom
reports using only `[propext, Classical.choice, Quot.sound]`, and two examples.
The new modules emitted zero warnings; dependencies emitted 561 warnings and
package configuration emitted two. Strict screening found zero traps.
Evidence: `/tmp/jones-phase-factorization-qa.log`.
The audit's missing license header was corrected and independently confirmed
without changing its proof body. Final disposition: accepted with the scope
stated above; no repository-wide completion or all-green build claim.
