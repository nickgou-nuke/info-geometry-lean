# Anti-Obfuscation Vacuity Linter Report

Policy enforced by `scripts/vacuity-linter.py`:

```text
sorry = honest visible proof debt
socket/witness/bookkeeping/owner-debt structures = obfuscated proof debt
premise forwarding = not proof progress
```

Run:

```bash
cd /home/goutev/auto
python3 scripts/vacuity-linter.py \
  --scan-root proofs \
  --graph-json proofs/proof_graph.json \
  --out proofs/tools/lean_graph/out/anti_obfuscation_vacuity_report.json \
  --json
```

## Current summary after first cleanup

First cleanup target:

```text
proofs/MellinWaveletScaleShiftDigest.lean
```

Change made there:

```text
removed socket/witness premise structures and pass-through synthesis theorems;
replaced analytic claims with explicit `sorry` theorem targets;
kept only the closed finite kernel theorem for proved finite facts.
```

Updated counts:

```text
Lean files scanned:              520
files with anti-obfuscation hits: 358
anti-obfuscation findings:       2240
```

Classification counts:

```text
premise_obfuscation:                    220
premise_forwarding_or_suspicious_name:  137
suspiciously_vacuous:                    82
socket_pass_through:                     47
non_vacuous:                             23
sorry_target:                             9
bookkeeping_vacuous:                      2
```

Delta from previous run:

```text
MellinWaveletScaleShiftDigest.lean: premise_obfuscation -> sorry_target
anti-obfuscation findings: 2278 -> 2240
files with anti-obfuscation hits: 359 -> 358
```

## Top remaining flagged files

```text
36  proofs/WallpaperHolographicSelectionRules.lean
29  proofs/PenroseQuadricTopologySynthesis.lean
26  proofs/TrainsumQuanticsTensorTrainsDigest.lean
25  proofs/ModularRadonNikodymJacobianBridge.lean
22  proofs/EntropicChiralDeRhamDictionary.lean
21  proofs/ThesisMaster.lean
21  proofs/MotivicHolographyGroebnerLFunction.lean
21  proofs/TopologicalColorCrystalFormal.lean
20  proofs/ExceptionalTopologicalBandStructures.lean
20  proofs/GrothendieckGromovWittenYangBaxter.lean
```

## Meaning of major labels

```text
premise_obfuscation
  Structure/class names or Prop fields contain socket/witness/debt/claim/etc.
  These should become explicit premises or honest `sorry` theorem targets.

premise_forwarding_or_suspicious_name
  The theorem/lemma name or proof body suggests assumption forwarding.

socket_pass_through
  Legacy classifier: code shape strongly suggests a prose claim is being passed through.

sorry_target
  Honest visible hole. This is preferred to obfuscated structures.
```

Full machine-readable report:

```text
proofs/tools/lean_graph/out/anti_obfuscation_vacuity_report.json
```
