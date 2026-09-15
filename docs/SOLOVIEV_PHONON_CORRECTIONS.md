# Soloviev pair-operator formalization

## Sources and reuse

[Soloviev, Sushkov and Shirikova, *Dipole excitations in deformed nuclei*](https://www1.jinr.ru/Archive/Pepan/v-31-4/v-31-4-2.pdf),
printed page 788, equations (1)–(3), supplies the Bogoliubov and phonon
expansions. Equation (3) contains the circular coefficients
`amplitude * (1 ± iσ) / (2√2)`, with `σ = ±1`.
The implementation checks their squared norms and the underlying ordered-pair
commutator, not the paper's complete angular-momentum-coupled sums.

[Tsoneva's Trento 2022 presentation](https://indico.ectstar.eu/event/154/contributions/3320/attachments/2119/2778/NTsoneva_Trento2022.pdf),
slides 6–7, motivates retaining fermionic corrections to the phonon commutator.
Both references were downloaded and the relevant equations visually checked.

The whole-tree content/recovery audit is in
`MENG_SOLOVIEV_DEEP_REUSE_AUDIT.md`. Additional recursive content searches
checked existing pair commutators, Bogoliubov CAR and fermionic corrections.
The new code reuses `NuclearQuasiparticleCARBridge` and
`NuclearTwoModeCARFiveGrade`; it introduces no replacement Zorn algebra,
spin matrices, Hamiltonian, or five-grading.

## Exact theorem boundary

Paths are relative to `lean/InfoGeometry/Physics/`.

- `NuclearPairCAR.lean`: derives the four-index pair commutator from the
  existing CAR interface, including all four occupation/coherence corrections.
  Its same-pair specialization is `[a₂a₁, a₁†a₂†] = 1 − N₁ − N₂`.
  The real Bogoliubov anticommutator has coefficient `u² + v²`.
- `SolovievPhononCorrections.lean`: for one ordered pair with complex forward
  and backward coefficients, derives `(‖forward‖² − ‖backward‖²)(1 − N₁ − N₂)`.
  The circular coefficient has squared norm `amplitude² / 4`.
  A finite partial order records these mathematical dependencies; it is not
  an extraction or certification of Lean's declaration environment.
- `SolovievTwoModePhonon.lean`: supplies the existing four-state CAR operators
  to the generic interface. The normalized pair commutator is minus the
  existing occupation Cartan: it acts as `+1` on the empty state and `−1`
  on the doubly occupied state. Therefore it is not the identity operator.
  The creation and annihilation pair components retain grades `+2` and `−2`.
- `SolovievPhononCorrectionsTests.lean`: rational normalization, both circular
  signs, vacuum action, nonidentity, and axiom audits.

The generic CAR interface does not assert a star operation relating `a` and
`adag`. Accordingly the coefficient-conjugated `phononAnnihilation` is an
explicit algebraic expression, not an abstract Hilbert-adjoint theorem.
The vacuum lemma assumes annihilation by each quasiparticle operator; it does
not construct the correlated QPM phonon vacuum. In particular, its empty
state need not be annihilated by a phonon with nonzero backward amplitude.

This extension does not solve the RPA secular equation, instantiate all
Clebsch–Gordan coefficients, derive measured dipole strengths, or identify
fermionic corrections with a Tomita commutant, CPT violation, or a two-state
vector interpretation. The existing multipole/Hamiltonian and Zorn bridges
remain separate owners, as recorded in the reuse audit.

## Source retrieval

- Soloviev PDF: `/tmp/meng-soloviev-dipole.pdf`; SHA-256
  `fe4525274c8cc54ceb2b13eda93bf14d0f54a6089a2af4cc134894153beebce2`.
- Tsoneva PDF: `/tmp/tsoneva-trento2022.pdf`; SHA-256
  `82b4f3935961d9dc078dd2ec4cbd92186bfa64e85d99e93bfd02e1c2c5d8120b`.
  Its server failed certificate validation; the user-approved download disabled
  certificate verification for that request only. The hash records the retrieved
  bytes, not independent authentication.

## Verification environment

The pinned Lean 4.28.1 toolchain is unavailable locally. Narrow checks use
installed Lean 4.28.0, cached Mathlib, isolated outputs in
`/tmp/isnp-metacompiler-validation`, and the shared build lock. No dependency
source, manifest, or toolchain pin is changed. This is not a claim of a complete
repository build on the pinned toolchain.

All four new Lean modules passed these narrow checks. The six regression
examples compile, and the 19 audited declarations (18 theorems and the concrete
CAR datum) use only `propext`, `Classical.choice`, and `Quot.sound`, or subsets
thereof. No `sorryAx`, custom axioms, or `native_decide` occur in the new proofs.

The deeper existing real-carrier import closure currently stops at the missing
`InfoGeometryCore.Basic` dependency. This extension instead checks the existing
complex two-mode carrier; it does not replace that deeper infrastructure.
