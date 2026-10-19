# Wave 17 quarantine register

These synthetic modules are intentionally excluded from `InfoGeometry.All` until
an owner-level repair is available. They are not promoted as verified mathematics.

* `Superalgebra/TomitaTakesakiModularSpinHawkingUnitarity.lean`: the horizon
  information theorem currently expands to a false/unclosed coordinate goal in
  its local implementation; the canonical Tomita/Krein owners remain in
  `Volume/ConnesTomitaKreinDerivation.lean` and related modules.
* `Superalgebra/SplitOctonionGrandUnifiedTowerArchive.lean`: duplicate archival
  namespace with an unresolved coordinate theorem; no downstream owner depends
  on this duplicate.
* `Topological/ChernSimonsTemperleyLiebYangBaxterBraid.lean`: its concrete
  Temperley–Lieb matrix pair does not satisfy the declared TL relations, so the
  advertised Yang–Baxter theorem is not a valid target for repair by tactics.
* `Synthesis/Wave17TopologicalOctonionicHolographicSynthesis.lean`: synthetic
  aggregate with stale namespace aliases and no owner-level dependency role.

The quarantine is a build-scope correction, not a proof claim. Each module must
return to the aggregate only after its stated mathematical contract is repaired
and independently kernel-checked.
