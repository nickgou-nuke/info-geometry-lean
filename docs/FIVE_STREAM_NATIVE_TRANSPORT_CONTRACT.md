# Five-stream native transport contract

## Scope

Connect the existing five canonical streams to native units, orbit/stabilizer quotients,
tracial functionals, presented-group representations and exact dual-number
first jets. Do not duplicate the master intertwiner or replace native carriers.

## Grounded owners

- Stream 5: `IsDualSeedPair` gives d²=B²=0, dBd=d, BdB=B;
  `phaseRotor c s=P0+c•Delta+s•(d-B)` and its two moving poles.
- `ReflexiveNilpotentFlows.rotor_inverse`: both inverse orders follow from
  the four pair relations and c*c+s*s=1 (reverse by replacing s with -s).
- `IdempotentOrbitContracts.unitConjugation` and `quotientEquivOrbit`:
  the actual unit action and Mathlib quotient by its stabilizer, not a claim
  that all idempotents form a single orbit.
- `ReflexiveNilpotentFlows.weyl_factorization` supplies the quarter-turn/triple
  shear equality. The concurrent master intertwiner attempts additional
  cross-stream identities but failed the baseline build; leave it untouched
  and do not make new proofs depend on its unfinished source.
- PR #206 `ParabolicModularRepresentation.representation`: homomorphism from
  the presented modular-relations group into Aˣ; its first generator is the
  triple shear unit. No arbitrary-carrier faithfulness claim.
- Stream 3 `kmsModularWeight u v=u²•Pminus+v²•Pplus` and
  `TracialCARDensity.joint_covariance` for native `TracialFunctional R A`.
- `Core.InnerConjugationJet.conjugate`: exact square-zero first-order transport;
  Stream 5 `lieBracket_wheel_polePlus` supplies its tangent coefficient.
- Native `CARPair`, its squared-zero fields, and
  `TracialCARDensity.ann_cre_ann`/`cre_ann_cre` inhabit the existing seed
  predicate without requiring a new law-bearing carrier.

## New statements

Construct the normalized rotor as an ambient unit; place its moving pole in
the native stabilizer orbit and give a quotient preimage; identify its quarter
turn with the actual presented modular generator; prove joint covariance of
the moving weighted support and arbitrary observables; identify the exact
first-order moving projector in the dual-number ring; instantiate the seed
hypotheses from the native CAR carrier. Instantiate these laws on the already
constructed Cl(1,1) Jordan–Wigner tensor colimit, using
`Cl11CARFockColimitBridge` and `Cl11TensorInductiveLimit.ofStageAlgHom`:
rotors/moving projectors commute with the stage map, and the represented
modular generator is the stage image of the finite quarter turn.

No new topology, superscheme, analytic evolution, positivity, GNS state or
Tomita reconstruction is asserted. Existing names referring to KMS/Grassmannian
are used only at the algebraic scope of their Lean types. New proofs are small,
reusable lemmas, not a bundled certification packet.

## Evidence boundaries

The current audit command counts are 111/91/107/67/64 (440 total), not the
reported 112/91/107/67/64. Command counts are not generated declaration counts.
External A-A/QA-A conversation links are not independently readable here.
Their acceptance remains reported; local compilation/replay is recorded
separately. The shared master intertwiner is existing/concurrent work and is
not attributed to this task.
