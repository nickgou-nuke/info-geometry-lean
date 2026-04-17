# Socratic-Closure Protocol

This protocol separates exploration from closure in the agent stack.

## 1. Two Mandatory Modes

- `socratic_generator`:
  - produce alternatives, contradictions, obligations, and diagnostics
  - do **not** emit closure claims
  - return evidence packets and unresolved assumptions
- `closure_gate`:
  - evaluate only against compiled Lean outcomes and policy gates
  - either admit, stabilize, or quarantine
  - closure language is allowed only with compiled anchors

## 2. Hard Language Contract

- Exploration agents must return evidence packets and open obligations, not conclusions.
- Closure claims are allowed only in closure mode with compiled Lean anchors.
- Every closure claim must cite exact theorem/file anchors or build gate output.

## 3. Failure as Signal

- High-value failures are assets; preserve diagnostics.
- Do not optimize exploration for minimum failures.
- Optimize for:
  - high diagnostic clarity
  - explicit obstruction terms
  - minimal repair moves

## 4. Role Mapping

- `OpenClaw` / `Hermes`: `socratic_generator`
- `NemoClaw`: placement-risk filter, still non-closure unless explicitly in closure pass
- `ClawCode`: `closure_gate`
- Human orchestrator: selects which open obligations receive attention

## 5. Required Packet Shapes

`socratic_generator` output:
- competing formulations
- missing assumptions
- bridge obligations
- residual obstruction terms
- candidate theorem surfaces tagged `unclosed`

`closure_gate` output:
- gate-by-gate pass/fail
- exact rejection reasons
- minimal repair patch targets
- explicit admit/stabilize/quarantine decision

## 6. Jitter Safety Rule

- Perturbation/jitter is allowed on natural-language coordination text only.
- Do **not** jitter Lean source files (`.lean`), declaration names, theorem statements,
  or fenced/inline code spans.
- Kernel-facing symbolic anchors remain immutable.
