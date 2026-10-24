# Two-mode current scaling realignment

Contract: retain `SplitCliffordSuperVirasoroModes.L0`, `G1`, and `LG_defect`
on their native `Matrix (Fin 4) (Fin 4) ℝ` carrier. Evaluate the actual
commutator as `-G1` and the residual as `(-3/2) • G1`. Prove the constructive
classification for diagonal generators: their action on `G1` has weight
`d 2 - d 1`, so half-weight occurs exactly when this difference is `1/2`.
Use the existing current generator `Hdiag/4` to realize both opposite
half-weights on `Jplus = G1` and `Jminus`.

The original non-idempotence theorem already has a constructive explanation:
the same current is nonzero and square-zero. The old scaling-with-defect
theorem merely unfolds a residual; this addition evaluates it and provides
the correct generator instead of discarding the current.

Read owners: `Canonical.SplitCliffordSuperVirasoroModes`,
`Canonical.SplitCliffordJordanWignerTwoMode`,
`Canonical.SplitCliffordJordanWignerTwoModeCurrent`. The latter already proves
`Hdiag_comm_Jplus` and `Hdiag_comm_Jminus`. Current maintained references to
the original scaling module are aggregate imports; no other evaluation of
`LG_defect` appeared in the inspected references.

Scope: a finite two-mode matrix current action. This is not a super-Virasoro
representation, Sugawara construction, or infinite-mode relation.
Six new named lemmas are implemented in `Canonical.TwoModeCurrentScaling`.
The classification is proved for every real weight, not just half-weight.
The audit includes the original nilpotence/nonzero/non-idempotence results,
a three-parameter family of half-weight diagonal generators, and the exact
residual entry `LG_defect 2 1 = -3/2`.

Parent locked audit session 56044 exited zero (3100 jobs). All nine axiom
reports use exactly `propext`, `Classical.choice`, `Quot.sound`; new modules
produce zero warnings. Independent semantic review passed. Final independent
kernel QA session 68389 also exited zero (3100 jobs), confirming nine
standard-axiom reports and both examples, with zero own-source warnings,
zero strict-screen traps, and clean scoped diffs. Twelve dependency warnings
and two package notices remain outside this addition. Accepted with the
finite-current scope above. Session-local evidence:
`/tmp/two-mode-scaling-audit.log`, `/tmp/two-mode-scaling-qa.log`.
