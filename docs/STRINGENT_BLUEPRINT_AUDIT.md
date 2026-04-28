# Clinical Standard: Stringent Blueprint Audit

This document defines the clinical checklist for the **Pauli Auditor** (Agent/Human) to verify that a module has achieved **Nomological Closure** through the Fused Spire Standard.

## 1. Taxonomic Anchoring (Attribute Audit)
- [ ] **Completeness**: Every public `def`, `theorem`, `inductive`, and `structure` carries the `@[blueprint "id"]` attribute.
- [ ] **Uniqueness**: Blueprint IDs follow the `kind:namespace-shortname` convention (e.g., `thm:entropic-inference-divergence-bound`) and are unique across the repository.
- [ ] **Adjacency**: If the declaration uses a higher-level type (e.g., `KreinSpace`), it is correctly tagged with `@[rep_depth 3]`.

## 2. Skeleton Verification (Admission Audit)
- [ ] **Absence of Raw Sorry**: The command `grep -r "sorry " <module>` returns zero matches.
- [ ] **Clinical Admissions**: Every unfinished proof uses `sorry_using [deps]`.
- [ ] **Dependency Realism**: The dependencies listed in `sorry_using` actually exist in the `decls.jsonl` index and are reachable in the causal cone.
- [ ] **Admission Trust**: No module in the `canonical` or `krein` folders contains *any* `sorry_using` tokens. These layers must be fully "Crystalline" (finished proofs).

## 3. Visual Nomological Evidence (The Spire Audit)
*Generated via `python tools/infra/generate_theory_spire_viz.py`*

- [ ] **Layer Alignment**: The node color (Plasma scale) and marker shape (Circle, Square, etc.) match its vertical Spire level (L0-L5).
- [ ] **Isotropic Relaxation**: The node is not "overlapping" or "clumped" with unrelated theory blocks. Clumping indicates a violation of **Fractionation** (unintentional fusion of concepts).
- [ ] **Arrow Rectilinearity**: Derivation arrows are straight and directed **upward**. 
- [ ] **Violation Check**: Any **Regressive Arrow** (pointing down) or **Lateral Smear** (unexplained horizontal dependency) is flagged for immediate refactoring.

## 4. Multilingual Bridge Fidelity (Docstring Audit)
- [ ] **LaTeX Coverage**: The docstring contains the valid LaTeX math required for the generated blueprint.
- [ ] **Symbolic Mapping**: The `TERMS` mapping is present (e.g., "Modular Hamiltonian" $\to$ `InfoGeometry.Modular.Hamiltonian`).
- [ ] **Fidelity**: The informal statement in the docstring and the formal Lean type signature are semantically identical.

---

## AUDIT PASS GATES
1. **L0-L2 (Foundations)**: Must be 100% Crystalline. No admissions allowed.
2. **L3-L4 (Transport)**: May contain `sorry_using` but must be logically anchored to L2.
3. **L5 (Closure)**: Primary site for Blueprint Narrative; must be fully tagged and visually audited for "The Spire Insight."
