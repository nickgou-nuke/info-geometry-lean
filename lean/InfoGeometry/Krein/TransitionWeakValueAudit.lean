import InfoGeometry.Krein.TransitionWeakValueExamples

/-!
# Focused weak-value reconstruction audit

Build this target rather than the repository-wide aggregator during proof repair.
The printed dependencies must not contain `sorryAx` or additional physical axioms.
-/

#print axioms InfoGeometry.Krein.TransitionWeakValue.hadamard_null_iff_overlap_zero
#print axioms InfoGeometry.Krein.TransitionWeakValue.isometry_preserves_nonnull
#print axioms InfoGeometry.Krein.TransitionWeakValue.kreinReadout_intertwiner
#print axioms InfoGeometry.Canonical.WeakValuePoleBounds.norm_quotient_gt_of_lower_bound
#print axioms InfoGeometry.Canonical.WeakValuePoleBounds.realReadout_gt_iff
#print axioms InfoGeometry.Canonical.WeakValuePoleBounds.overlapBarrier_gt_iff
#print axioms InfoGeometry.Canonical.WeakValuePoleBounds.hasDerivAt_quotient
#print axioms InfoGeometry.Canonical.WeakValuePoleBounds.sampled_gradient_energy_lower_bound
#print axioms InfoGeometry.Krein.TransitionWeakValueExamples.state_null
#print axioms InfoGeometry.Krein.TransitionWeakValueExamples.node_data
#print axioms InfoGeometry.Krein.TransitionWeakValueExamples.arbitrarily_large_readout
#print axioms InfoGeometry.Krein.TransitionWeakValueExamples.identity_readout
