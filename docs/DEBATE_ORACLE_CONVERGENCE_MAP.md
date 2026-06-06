# Debate Oracle Convergence Map

> Status: `source-grounded map`
> Scope: external references for adversarial dialogue, oracle debate, and
> convergence language used by the Socratic proof-repair lane.
> Authority: external references are navigation and design evidence only. Lean
> source in this repo remains proof authority after a native port or import.

This note records the precise external material found for the phrase
"dialogue lemma about convergence of adversarials".

## Verified Sources

There are two relevant but distinct sources.

### Adversarial Dialogue: DeepMind Debate

Path:

```text
external_refs/deepmind-debate
```

This is a Lean 4 formalization of stochastic oracle debate. It models honest
players and adversarial substitutes, then proves finite probabilistic
correctness. It is the correct formal precedent for an adversarial Socratic
proof-auditor loop.

Important files:

- `external_refs/deepmind-debate/Debate/Protocol.lean`
- `external_refs/deepmind-debate/Debate/Correct.lean`
- `external_refs/deepmind-debate/Debate/Details.lean`

Important declarations:

- `OracleId`, `Alice`, `Bob`, `Vera`
- `debate`, `steps`, `step`
- `Correct`
- `completeness`
- `soundness`
- `correctness`
- `alices_close`
- `evil_bobs_lies`
- `evil_alices_lies`
- `bobs_catches`

What it proves:

```text
Honest Alice beats any adversarial Bob/Eve in the positive case.
Honest Bob beats any adversarial Alice/Eve in the negative case.
The default protocol is correct with probability 3/5.
```

What it does not prove:

```text
It is not an asymptotic convergence theorem for arbitrary chatbot dialogue.
It does not certify ChatGPT output.
It does not replace Lean checking in this repo.
```

### Analytic Convergence: L1 Subsequence

Path:

```text
external_refs/lean-stat-learning-theory/SLT/ConvergenceL1Subseq.lean
```

Important declaration:

```text
MeasureTheory.exists_seq_tendsto_ae_of_tendsto_eLpNorm_one
```

What it proves:

```text
If f_n converges to g in L1, then there is a strictly monotone subsequence
that converges to g almost everywhere.
```

What it does not prove:

```text
It has no adversarial dialogue or debate protocol content.
```

## Correct Interpretation

The useful bridge is:

```text
DeepMind debate gives the adversarial dialogue correctness pattern.
L1 subsequence convergence gives an analytic stabilization pattern.
The repo's Socratic oracle lane may cite both as design evidence, but any
formal theorem in info-geometry-lean must be ported or proved natively.
```

For proof repair, the practical protocol remains:

```text
complete owner file + all relevant Lean errors
  -> one aiClaw/ChatGPT adversarial audit prompt
  -> wait/read final visible answer
  -> one integrated source patch by the coding agent
  -> Lean kernel check
```

This is analogous to the DeepMind debate shape, but it is not itself a proved
convergence theorem until formalized in the repo.

## GEPA Metric Use

The debate precedent is also usable as a prompt-evaluation shape:

```text
proposal prompt profile
  -> archived oracle event reports
  -> empirical Lean verification outcome counts
  -> smoothed Jaynes posterior success estimate
  -> information-cost and regression penalties
  -> deploy only if better than the stable baseline
```

The local implementation is:

```text
tools/infra/socratic_oracle_prompt_gepa.py
tools/quality/oracle_prompt_regression_gate.py
configs/oracle_prompt_profiles/
```

This is not proof authority. It is process optimization for oracle prompts.

## Candidate Native Bridge

A small native bridge can be formalized later without importing the whole
external project:

```text
structure OracleDebateAudit where
  promptComplete : Prop
  adversarialReview : Prop
  integratedPatch : Prop
  kernelChecked : Prop

def auditAccepted (a : OracleDebateAudit) : Prop :=
  a.promptComplete ∧ a.adversarialReview ∧ a.integratedPatch ∧ a.kernelChecked
```

That bridge should be treated as process accounting, not theorem truth. Any
mathematical conclusion still belongs in the theorem owner file and must pass
Lean.
