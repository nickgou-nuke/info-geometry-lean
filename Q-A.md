# Questions for Pi: OpenGauss collaboration

Use this packet to establish whether Pi/Archon can participate in an
OpenGauss task without being mistaken for the native Codex swarm or for an
independent proof auditor.

1. Which scheduler owns a task: Archon/Pi, Hive, or native Codex?
2. Can Pi emit a versioned OpenGauss packet containing:
   - task ID;
   - owner file;
   - exact theorem contract;
   - source hashes;
   - hypotheses and explicit non-claims?
3. How does Pi distinguish the scout, prover, refuter, A-A auditor, and QA-A
   verifier roles?
4. Can candidate Lean code be written only to a new sandbox file, without
   overwriting an existing owner file?
5. How does Pi return a failed proof without marking the task complete?
6. Which deterministic commands does Pi run for Lean checking, locked builds,
   placeholder scans, axiom checks, and vacuity checks?
7. How does Pi prevent concurrent builds and queue races?
8. Can Pi preserve the exact source hash used by the Formalist and auditor?
9. How does Pi establish that A-A and QA-A are separate contexts rather than
   repeated self-review?
10. What artifact does Pi return when native Codex `spawn_agent` is unavailable?
11. Can Pi requeue a task without overwriting prior candidates?
12. What exact condition changes a packet from `candidate` to `accepted`?

## Decisive question

Can Pi provide a file-backed, hash-bound OpenGauss packet and genuinely
separate audit contexts, or does it provide only sequential provider responses?

Until this is answered, Pi output remains review evidence and does not count as
QMS acceptance.
