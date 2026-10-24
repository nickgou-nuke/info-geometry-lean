# Motion v7: direct native primitive projections in fixed sections

NEW sandbox only. V6 terminal /tmp/qa-a-finite-first-v6-klpnzdtg/compile.log65:11
still timed out synthesizing SeminormedRing at500k. A parent CStar instance alone
did not resolve that search. No repeat of the CStar-only attempt.

Fixed abstract omega section before matrixStageAut_eq_finitePath, then fixed
H/hH/beta section before the actual seed readback/motion lemmas. Each selects
local CStarAlgebra, NormedRing, SeminormedRing, Ring, MetricSpace and topology
from the SAME native representedCStarClosureCStarAlgebra. Use literal structure
projections and explicit @NormedRing.toSeminormedRing, not inferInstance to
reconstruct a seminormed ring through the root subtype.

Mathlib NormedRing directly extends Norm/Ring/MetricSpace; toSeminormedRing is
the native conversion ({beta with}), not an alternative norm. CStarAlgebra
extends NormedRing. Topology is its actual metric uniform-space projection.
Native precedent: FilteredGNSBoundedGeneratorUnitaryFlow pins inherited Ring
and MetricSpace before statements. No assumed equality of alternate structures.

The section variables factor the original binders without changing mathematical
inputs. All proof bodies and final all-beta/nonzero-tilt actual seed motion target
remain unchanged from v6. Generic and concrete carriers stay representedCStarClosure
of the original native family. Accepted native FiniteExponentialMotion and seed
faithfulness imports retained, accepted scratch alignment-v2 retained.

No builds/live edits/new assumptions/transparency changes. Budgets unchanged
1M/500k. Old files preserved; v7 uncompiled pending independent AA/serial QA.
