# Represented tilt motion v8 — intermediate matrix-tower specialization

Uncompiled new sandbox revision; no builds, tests, live edits, or budget increases.
V1–v7, centralizing v5 and finite Fock work remain intact.

Diagnostic read: /tmp/qa-a-tiltseedrealtimenontrivial20261024v7-druoa017/compile.log.
The actual numbered v7 source puts line186 and208 at generalize, immediately
AFTER unfold seedStageHom. The failure therefore does not establish that the
unfold command itself failed. Dependent generalization still traverses the
concrete family/type and v7 also reports a declaration-level isDefEq timeout.
The generic helper declarations produced no errors; the capped tail is unverified.

V8 removes generalize and unfold from all three seed proofs. First elaborate
three separate theorems with abstract omega on the actual CStarMatrixStage tower:
- matrixTowerStageMap_injective;
- matrixTowerStageMap_apply_ne_zero;
- matrixTowerStageRealTime_exists_move.

These discharge matrix type-copy equivalence, imported simplicity, and the
generic-to-matrix instance specialization BEFORE supplying the constructed
finiteSeedCompatibleStageStates. Each concrete proof is then one exact
application of an already matrix-specialized theorem. Local Jstage is notation
for the existing representedMatrixStageMap; it is not a replacement map or
carrier. No injectivity, nonzero image, or flow conclusion is assumed.

All three concrete statement interfaces remain unchanged, including the same
seedStageHom and seedRealTimeAut and all beta with h nonzero. The intermediary
flow theorem assumes only the raw finite commutator is nonzero; the concrete
01-coordinate calculation supplies that fact. No weaker flow/surrogate.

Remaining uncertainty: QA must check the abstract matrix specialization and
final definitional matching to seed wrappers terminate at existing limits
(1M / 500k). This source revision makes no compilation or closure claim.
Centralizing v5 remains unchanged per parent instruction pending screener review.
