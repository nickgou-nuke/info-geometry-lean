# Native Proof Mandate

> **UTMOST MANDATE**: The overarching goal of this repository is native Lean proof closure over witness/certificate scaffolding.

This skill is a **MANDATORY POLICY**. It is strictly forbidden to break it under any circumstances. 

## The Mandate

1. **Replace Existing Hypotheses**: All witness packets, certificate fields, external certificates, unproven assumptions, axioms, and `sorry`-based debt must be aggressively replaced with **real, native Lean proofs**.
2. **True Mathematical Closure**: Witness packets and external certificates are temporary scaffolding only. They are not final mathematical closure and carry no promotion authority.
3. **No Axioms**: Every promoted proposition must be discharged by native Lean derivation chains in-repo (owner -> translator -> mathlib-rooted proof path).
4. **Structural Progress**: Do not "resolve" debt with wording or documentation. Progress must be structural.
5. **Debt Preservation Until Closure**: Do not remove debt labels (like `sorry` or `socket_debt_tag`) unless there is a native explicit Lean proof term checked by the kernel closing that specific debt. Real progress equals replacing certificate/witness fields with theorem-backed native derivations.
6. **No Fake Bridges**: If you need an assumption, and you cannot prove it, leave it as an explicit parameter or structure field. Do not invent an axiom to bridge the gap.

## Enforcement

When writing code or planning architecture, you must always evaluate: "Does this rely on a hypothesis, or is it a native proof?"
If it relies on a hypothesis, you must record it as explicit closure debt. Your primary operational directive is to convert these recorded debts into kernel-checked native proofs.
