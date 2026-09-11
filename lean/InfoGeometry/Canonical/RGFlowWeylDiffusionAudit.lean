import InfoGeometry.Canonical.RGFlowWeylDiffusionBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Axiomatic Audit of RGFlowWeylDiffusionBridge

This audit verifies that RGFlowWeylDiffusionBridge depends solely on standard
foundational axioms in Lean 4 / Mathlib.
Expected axioms: [propext, Classical.choice, Quot.sound].
-/

#print axioms InfoGeometry.Canonical.RGFlowWeylDiffusion.certified_rg_flow_weyl_diffusion_synthesis
#print axioms InfoGeometry.Canonical.RGFlowWeylDiffusion.scaleHomothety_comp
#print axioms InfoGeometry.Canonical.RGFlowWeylDiffusion.scaleHomothety_zero
#print axioms InfoGeometry.Canonical.RGFlowWeylDiffusion.scaleHomothety_comm_linear
#print axioms InfoGeometry.Canonical.RGFlowWeylDiffusion.energyScale_zero
#print axioms InfoGeometry.Canonical.RGFlowWeylDiffusion.energyScale_anti_mono
#print axioms InfoGeometry.Canonical.RGFlowWeylDiffusion.harmonic_scalar_stationary
#print axioms InfoGeometry.Canonical.RGFlowWeylDiffusion.harmonic_vol_stationary
#print axioms InfoGeometry.Canonical.RGFlowWeylDiffusion.diffusion_intertwining
#print axioms InfoGeometry.Canonical.RGFlowWeylDiffusion.dilatation_commutes_laplacian
#print axioms InfoGeometry.Canonical.RGFlowWeylDiffusion.diffusion_preserves_subspace
