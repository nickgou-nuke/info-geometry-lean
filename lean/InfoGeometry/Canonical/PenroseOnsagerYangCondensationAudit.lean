import InfoGeometry.Canonical.PenroseOnsagerYangCondensationPristineChain

/-!
# Transitive axiom inspection for the Penrose--Onsager--Yang core

These commands inspect elaborated declarations when Lean executes the file.
Any `sorryAx` or project-specific custom axiom in the dependency closure is a
verification failure.  This audit is not a substitute for kernel execution.
-/

#print axioms InfoGeometry.Quantum.PenroseOnsagerYang.occupation_le_total
#print axioms InfoGeometry.Quantum.PenroseOnsagerYang.sum_occupationFraction_eq_one
#print axioms InfoGeometry.Quantum.PenroseOnsagerYang.simple_not_fragmented
#print axioms InfoGeometry.Quantum.PenroseOnsagerYang.normal_not_simple
#print axioms InfoGeometry.Quantum.PenroseOnsagerYang.normal_not_fragmented

#print axioms InfoGeometry.Quantum.PenroseOnsagerYang.rankOneKernel_posSemidef
#print axioms InfoGeometry.Quantum.PenroseOnsagerYang.trace_rankOneKernel_eq_modeNormSq
#print axioms InfoGeometry.Quantum.PenroseOnsagerYang.rankOneKernel_globalPhase_invariant
#print axioms InfoGeometry.Quantum.PenroseOnsagerYang.modeNormSq_orderParameter
#print axioms InfoGeometry.Quantum.PenroseOnsagerYang.rankOneKernel_orderParameter
#print axioms InfoGeometry.Quantum.PenroseOnsagerYang.trace_orderParameterKernel
#print axioms InfoGeometry.Quantum.PenroseOnsagerYang.spectralKernel_posSemidef
#print axioms InfoGeometry.Quantum.PenroseOnsagerYang.trace_spectralKernel

#print axioms InfoGeometry.Quantum.PenroseOnsagerYang.coherentTwoModeKernel_det
#print axioms InfoGeometry.Quantum.PenroseOnsagerYang.coherent_incoherent_same_diagonal
#print axioms InfoGeometry.Quantum.PenroseOnsagerYang.coherent_ne_incoherent_of_cross_ne_zero
#print axioms InfoGeometry.Quantum.PenroseOnsagerYang.coherentTwoModeKernel_globalPhase_invariant

#print axioms InfoGeometry.Canonical.PenroseOnsagerYangCondensationPristineChain.penrose_onsager_yang_condensation_pristine_chain
