# Audit Correction: Multi-System Attention/Fluid Claims

The former version of this report treated success of several unrelated
symbolic or computational examples as verification of the theorem
“Attention = Quantum Fluid.” That conclusion was not established by those
checks. The finite log-sum-exp identities, skew-matrix trace facts, and a
separately specified linear-field divergence computation do not provide a
map from transformer attention to a fluid state.

The valid formal boundary is recorded in
[Finite Attention Identities and Their Scope](../tools/infra/ATTENTION_SIMPLIFICATION_BREAKTHROUGH.md)
and [Finite Softmax Information Geometry](ATTENTION_IS_QUANTUM_FLUID.md).
Kernel evidence is the locked Lean build of the canonical owner modules; CAS
and other prover outputs are only evidence for their individual finite
examples unless their exact theorem and carrier are formalized in the owner
module.

The “eight systems verified” status is withdrawn. No multi-system run proves
the cross-domain attention/KMS/fluid identification. The missing bridge remains
an open development frontier: it would require explicit carriers, maps, and
proofs connecting the finite probability model to a specified observable
algebra, dynamics, and vector field.
