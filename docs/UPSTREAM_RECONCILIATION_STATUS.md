# Upstream reconciliation status

This note records the source-level comparison against `upstream/main` used by
the canonical reconstruction work.  It is an inventory, not a claim that
every upstream theorem is mathematically valid.

At the comparison point, `upstream/main` contained 11,231 paths below
`lean/InfoGeometry`; 11,173 were present in the working tree and 58 were
absent.  The absent set is classified as follows:

* canonical and domain capstone wrappers: retained upstream as historical
  material unless their component contracts have a current owner;
* stale witness packets: not promoted when they depend on deleted or
  mismatched APIs;
* duplicate forwarding modules: represented by existing canonical owners;
* genuine recoverable contracts: rewritten into small current-owner modules.

The following recoverable upstream contracts have current implementations and
are exported through the normal aggregates:

* finite Zorn quadratic-sandwich and zero-cone laws;
* polarized Zorn exchange and metric bridge;
* operator-valued twin-vector and weak-ratio bridges;
* finite ambitwistor incidence, para-Kähler projectors, CCR transport, and
  two-boundary readout;
* modular, Souriau–Kähler, G2, Wheeler, and grand-unified arithmetic
  theorem packets.

The remaining absent paths are capstone-level wrappers or speculative packets.
They are not silently copied: each must first be checked against current
owners and promoted only as a truthful, kernel-checkable contract.  In
particular, a source-level upstream theorem is not evidence of a valid
implementation until its imports elaborate and its transitive axiom report
passes.

The restored arithmetic hologram entry point is:

```lean
import InfoGeometry.Quantum.GrandUnifiedQuantumArithmeticHologram
```

The current aggregate verification command is:

```bash
lake build InfoGeometry.All
```

At the latest verification, this completed successfully (14,531 jobs).

The inventory was subsequently rechecked against the fetched upstream tree.
Two representative absent capstones were audited and deliberately not
promoted: `HestenesModularKMSBridgeCapstone` references the removed
`HestenesKreinKMSPacket.ofStaticFlow` constructor, while
`RationalHodgeKreinBridgeCapstone` references unavailable anomaly and doubled
space contracts.  The current Hestenes/Krein packet remains available through
its native structure-based owner.  The current aggregate build completed with
14,575 jobs, including the repaired fourfold Peirce owner.

The upstream `AlgorithmicThermodynamicColimitDualityCapstone` is likewise not
promoted: its claimed forwarding theorem is absent from the current
`Quantum.AlgorithmicThermodynamicColimitDuality` owner, which currently defines
the component namespace and imports but no synthesis declaration.

The latest path inventory contains 54 upstream-only names.  Three are filename
normalization duplicates (`Möbius` versus `Mobius`, including the restored
canonical owner); the remaining names are capstones, external scratch files,
or packets whose contracts do not resolve against the current owners.
