import InfoGeometry.Canonical.SemanticHighEntropyCompilationBridge

/-!
# Axiomatic Audit of SemanticHighEntropyCompilationBridge

This audit verifies that the SemanticHighEntropyCompilationBridge module relies solely
on standard Lean 4 / Mathlib axiomatic foundations.
Expected axioms: [propext, Classical.choice, Quot.sound].
-/

#print axioms InfoGeometry.Canonical.SemanticHighEntropyCompilation.certified_semantic_compilation_synthesis
#print axioms InfoGeometry.Canonical.SemanticHighEntropyCompilation.SemanticCompiler.causal_cone_frontier_closure
#print axioms InfoGeometry.Canonical.SemanticHighEntropyCompilation.SemanticCompiler.noise_annihilation
