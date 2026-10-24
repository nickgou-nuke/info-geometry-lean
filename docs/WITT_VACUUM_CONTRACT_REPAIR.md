# Creation-only vacuum contract repair

The legacy WittDecomposition pairing field required every pair to have nonzero
pairing unless both entries were zero. Setting the second entry to zero forced
W=0, contradicting W_dim=5. No declaration consumers were found by searches for
WittDecomposition, sheetAnnihilator, wittAct, and the qualified namespace outside
the owner; AllExhaustive imports the owner.

Replacement contract: arbitrary vector space W over a field R, native
ExteriorAlgebra R W, creation action by exterior multiplication. Its scalar
vacuum has zero creation-sheet annihilator. A positive finrank implies that
this annihilator does not have full sheet rank. This is not a Cartan impurity
theorem. Full neutral-space vacuum purity remains owned by
InfoGeometry.Clifford.scalarVacuum_isPureSpinor, using contraction and
creation together. The audit specializes both statements to Fin 5 → ℝ.

Remove the contradictory interface, rather than proving consequences from it.
No new Witt decomposition or physical identification is asserted. Parent build session 9349 passed (3,121 jobs, exit 0), with five standard-axiom
reports and three rank-five examples. Zero own warnings; strict screening
found zero traps. Log: /tmp/witt-vacuum-repair-v2.log. Independent semantic
review passed. Independent QA session 8153 passed both this audit and the Drazin criterion
audit (3,228 jobs, exit 0): nine axiom reports and five examples combined,
zero own warnings, 32 dependency warnings and two package notices. Log:
/tmp/witt-drazin-final-qa.log. Final semantic A-A review passed. Accepted for
the creation-only scope stated above.
