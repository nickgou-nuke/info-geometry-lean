# Completed multi-mode CAR v2: native dependencies

Original proof author James; original independent AA Popper. This adaptation
changes only the stale pending-import prose. The original already imports exactly:

- InfoGeometry.Clifford.RealFockModeCoherence
- InfoGeometry.Clifford.RealFockCompletedSameModeCAR

No import of scratch helper implementations and no redefinition of either
native dependency. Preserve every byte from `noncomputable section` through the
end of the original: all theorem statements, proof bodies, namespace, local
instances and notation are identical. The original file is untouched.

## Exact source binding

Original source SHA256:
d085d3460bd7f0644747a03b2f6f7fa4953dea2b89c759d200b62a08c2bf53f4
Original contract SHA256:
4f02ad2ce8d34597345ff971a7409fb15f22f5985b02049f580296b39e3513bc

Native RealFockCompletedSameModeCAR SHA256:
23250a402fda59621b1e821b3402d7c7fa2c39b69e65d372761aa1f3f8593a35
Native RealFockModeCoherence SHA256:
66f2e16768ad44f5f6175ef423db3299f2bf44e5e448aa5878efa13b94981328
The latter matches James's independently reviewed v2 sandbox byte-for-byte.
Parent reports its native QA queued; no kernel result is inferred here.

## Unchanged contract

Actual RealFockCompletion and existing completed creation/contraction CLMs.
Density above a birth-stage cutoff gives completed same-birth cross CAR.
Native Clifford colimit transport gives birth-stage operator coherence.
Different-birth cross CAR compares shifted indices in any common upper stage;
the mixed identity coefficient is independent of that common upper stage.
No raw-index comparison across stages, new carrier, action, or assumed CAR.
No duplication of same-mode square-zero or adjoint proofs.

New v2 files only, staged. No builds/tests/live edits, budgets or transparency
changes. This is a mechanical adaptation, not a fresh independent mathematical
AA or kernel certificate. Ready for separate review and serial QA with native
dependencies; do not import both original and v2 candidate modules together,
as they intentionally declare the same consumer theorems.
