# Epistemic reactor ensemble infusion

This is the side-effect-free stochastic generation phase.

Input:

```text
info_geometry.epistemic_reactor.compressed_cone.v1
```

Outputs:

```text
ensemble_samples.jsonl
ensemble_consensus.json
```

Command:

```bash
lake script run epistemicReactorEnsemble -- \
  --input artifacts/epistemic_reactor/compressed_cone.json \
  --samples-out artifacts/epistemic_reactor/ensemble_samples.jsonl \
  --consensus-out artifacts/epistemic_reactor/ensemble_consensus.json \
  --prompt-out artifacts/epistemic_reactor/ensemble_prompt.md \
  --mode auto
```

Local endpoint mode uses an OpenAI-compatible chat completion endpoint:

```bash
lake script run epistemicReactorEnsemble -- \
  --input artifacts/epistemic_reactor/compressed_cone.json \
  --samples-out artifacts/epistemic_reactor/ensemble_samples.jsonl \
  --consensus-out artifacts/epistemic_reactor/ensemble_consensus.json \
  --mode openai-compatible \
  --endpoint http://localhost:11434/v1 \
  --model llama3.1:8b
```

Authority ladder:

```text
compressed_cone.json       navigation
ensemble_samples.jsonl     proposal
ensemble_consensus.json    proposal
shadow_plant_worker        hive_purified
LeanVerificationPacket     lean_checked
BuildPacket                build_checked
AuditPacket                audit_checked
```

Forbidden jumps:

```text
ensemble_consensus_is_truth
hive_purified_is_admitted
graph_is_proof
sample_is_proof
proposal_is_lean_checked
```

The ensemble packet is intentionally read-only.  It does not write to ArangoDB
and it does not promote any theorem claim.

