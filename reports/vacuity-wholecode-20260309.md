# Whole Codebase Vacuity Audit (2026-03-09)

This report separates strict vacuity (definite missing proofs) from broad syntactic vacuity candidates.

## Strict (Definite Missing Proofs)

Count: 9

### Locations
- lean/InfoGeometry/Krein/HilbertBridge.lean:58:    sorry
- lean/InfoGeometry/Krein/HilbertBridge.lean:60:    sorry
- lean/InfoGeometry/Krein/HilbertBridge.lean:62:    sorry
- lean/InfoGeometry/Krein/HilbertBridge.lean:64:    sorry
- lean/InfoGeometry/Krein/HilbertBridge.lean:66:    sorry
- lean/InfoGeometry/Krein/HilbertBridge.lean:78:    sorry
- lean/InfoGeometry/Krein/Metric.lean:41:  sorry
- lean/InfoGeometry/Canonical/IBCore.lean:137:  sorry
- lean/InfoGeometry/Canonical/IBCore.lean:162:  sorry

## Broad Syntactic Vacuity Candidates

These are exhaustive syntactic classes, not all mathematically vacuous.

- rfl occurrences: 241
- abbrev declarations: 267
- alias-like one-line assignments (tight regex): 155
- simpa ... using occurrences: 535
- direct assignment declarations (broad regex): 1152

### Top Files by abbrev Count
- 21	lean/InfoGeometry/Canonical/GrandCanonicalExperts.lean
- 15	lean/InfoGeometry/Core/GrandCanonical.lean
- 15	lean/InfoGeometry/Canonical/BogoliubovFockSuper.lean
- 7	lean/InfoGeometry/Krein/HilbertBridge.lean
- 7	lean/InfoGeometry/Core/SymmetricSpaces.lean
- 6	lean/InfoGeometry/Clifford/Cl11.lean
- 6	lean/InfoGeometry/Canonical/ConformalUnification.lean
- 6	lean/InfoGeometry/Canonical/CayleyBregmanBridge.lean
- 6	lean/InfoGeometry/Canonical/BottPeriodicity.lean
- 5	lean/InfoGeometry/Canonical/TomitaTakesaki.lean
- 5	lean/InfoGeometry/Canonical/AQFTOperatorInterface.lean
- 4	lean/InfoGeometry/ExponentialFamily/Analytic/Softmax.lean
- 4	lean/InfoGeometry/Clifford/Cl11Quaternion.lean
- 4	lean/InfoGeometry/Canonical/RicciMongeAmpere.lean
- 4	lean/InfoGeometry/Canonical/DeterminantCore.lean
- 4	lean/InfoGeometry/Canonical/BottDirac.lean
- 3	lean/InfoGeometry/Twistor/NullProjective.lean
- 3	lean/InfoGeometry/Thermo/FromBregman.lean
- 3	lean/InfoGeometry/MaxEnt/JaynesInfoStatMech.lean
- 3	lean/InfoGeometry/Krein/Clifford.lean

### Top Files by alias-like One-Line Assignments
- 9	lean/InfoGeometry/Clifford/Cl11Matrix.lean
- 8	lean/InfoGeometry/Canonical/ConformalUnification.lean
- 7	lean/DAG/GlobalDisassembler.lean
- 6	lean/InfoGeometry/Cartan/Involution.lean
- 6	lean/InfoGeometry/Canonical/GrandCanonicalExperts.lean
- 6	lean/DAG/Indexer.lean
- 5	lean/InfoGeometry/Projective/Null.lean
- 5	lean/InfoGeometry/EntropicInference.lean
- 5	lean/InfoGeometry/Canonical/BogoliubovFockSuper.lean
- 4	lean/InfoGeometry/Krein/HilbertBridge.lean
- 3	lean/InfoGeometry/Core/SymmetricLieGeneric.lean
- 3	lean/InfoGeometry/Clifford/MatrixCompat.lean
- 3	lean/InfoGeometry/Clifford/Cl11Quaternion.lean
- 3	lean/InfoGeometry/Causal/MirrorAlignment.lean
- 3	lean/Docs/emit_blueprint_tex.lean
- 3	lean/DAG/ServerExport.lean
- 2	lean/InfoGeometry/Thermal/FiniteMatrix.lean
- 2	lean/InfoGeometry/Projective/Projective.lean
- 2	lean/InfoGeometry/Krein/KreinSpace.lean
- 2	lean/InfoGeometry/Jordan/Core.lean

### Top Files by rfl Occurrences
- 16	lean/InfoGeometry/Canonical/GrandCanonicalExperts.lean
- 11	lean/InfoGeometry/Thermal/FiniteMatrix.lean
- 10	lean/InfoGeometry/Canonical/Triality.lean
- 8	lean/InfoGeometry/Krein/KreinSpace.lean
- 8	lean/InfoGeometry/Krein/DoubledSpace.lean
- 8	lean/InfoGeometry/Convex/HessianGeometry.lean
- 7	lean/InfoGeometry/Prequantum/Scaling.lean
- 7	lean/InfoGeometry/Potential/Thermo.lean
- 6	lean/InfoGeometry/Krein/Clifford.lean
- 6	lean/InfoGeometry/Basic.lean
- 5	lean/InfoGeometry/Core/SymmetricLie.lean
- 5	lean/InfoGeometry/Core/Entropy.lean
- 4	lean/InfoGeometry/Prequantum/Quotient.lean
- 4	lean/InfoGeometry/PositiveMeasure.lean
- 4	lean/InfoGeometry/LLM/TransformerBlock.lean
- 4	lean/InfoGeometry/LLM/PositionalEncoding.lean
- 4	lean/InfoGeometry/Krein/HilbertBridge.lean
- 4	lean/InfoGeometry/ExponentialFamily/Analytic/LogSumExp.lean
- 4	lean/InfoGeometry/Canonical/CayleyBregmanBridge.lean
- 3	lean/InfoGeometry/Thermo/FromBregman.lean

## Raw Extraction Files

- reports/vacuity/wholecode-explicit-proof-holes-20260309.txt
- reports/vacuity/wholecode-explicit-proof-holes-20260309.by-file.txt
- reports/vacuity/wholecode-rfl-occurrences-20260309.txt
- reports/vacuity/wholecode-rfl-occurrences-20260309.by-file.txt
- reports/vacuity/wholecode-abbrev-decls-20260309.txt
- reports/vacuity/wholecode-abbrev-decls-20260309.by-file.txt
- reports/vacuity/wholecode-alias-like-decls-20260309.txt
- reports/vacuity/wholecode-alias-like-decls-20260309.by-file.txt
- reports/vacuity/wholecode-simpa-using-occurrences-20260309.txt
- reports/vacuity/wholecode-simpa-using-occurrences-20260309.by-file.txt
- reports/vacuity/wholecode-direct-assign-decls-broad-20260309.txt
- reports/vacuity/wholecode-direct-assign-decls-broad-20260309.by-file.txt
- reports/vacuity/wholecode-trivial-occurrences-20260309.txt
- reports/vacuity/wholecode-trivial-occurrences-20260309.by-file.txt
