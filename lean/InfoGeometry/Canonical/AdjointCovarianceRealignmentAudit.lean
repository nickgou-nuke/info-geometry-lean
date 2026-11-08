/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Singular.MoorePenroseTransport
import InfoGeometry.CliffordWeyl.DiracSolderAdjoint
import InfoGeometry.Twistor.TwoTwistorIncidenceIsotropy

open InfoGeometry.Singular.MoorePenrose

#print axioms IsMoorePenroseInverse.transport
#print axioms similarity_selfAdjoint_iff_gram_commute
#print axioms IsMoorePenroseInverse.map_iff
#print axioms IsMoorePenroseInverse.similarity_iff
#print axioms IsMoorePenroseInverse.target_eq_similarity_iff
#print axioms IsMoorePenroseInverse.target_ne_similarity_iff

open InfoGeometry.CliffordWeyl.SpinorBilinearSoldering

#print axioms solder_metric_adjoint
#print axioms diracAdjoint_solder
#print axioms finiteSpin_metric_involution
#print axioms finiteSpin_metric_hermitian
#print axioms ordinary_adjoint_not_dirac_solder_exchange
#print axioms dirac_solder_pair_not_commute

open InfoGeometry.Twistor.TwoTwistorIncidenceIsotropy

#print axioms incidence_isotropy_implies_unitary
#print axioms frameSpacetimeNode_isotropy_implies_unitary
#print axioms incidence_hermitian_iff_frame_skew
#print axioms frameSpacetimeNode_hermitian_iff_frame_skew
#print axioms isotropy_does_not_imply_hermitian

open InfoGeometry.Algebra.FiniteSpin Matrix

example : ((2 : ℂ) • J_zero) * (-J_plus).conjTranspose * ((2 : ℂ) • J_zero) =
    J_minus := by
  simpa only [finiteSpin_solder_forward, finiteSpin_solder_reverse] using
    solder_metric_adjoint ((2 : ℂ) • J_zero) finiteSpin_metric_hermitian
      finiteSpin_metric_involution ![1, 0] ![0, 1]

open InfoGeometry.Twistor.PenroseIncidence
open InfoGeometry.Twistor.TwoTwistorSpacetimeNode

example (X P Ω : ComplexSpacetime) (hP : IsUnit P.det)
    (hinc : Ω = (Complex.I • X) * P)
    (hisot : Ω.conjTranspose * Ω = P.conjTranspose * P)
    (hskew : P.conjTranspose * Ω + Ω.conjTranspose * P = 0) :
    X * X = 1 := by
  have hX := (incidence_hermitian_iff_frame_skew X P Ω hP hinc).mpr hskew
  simpa only [hX] using incidence_isotropy_implies_unitary X P Ω hP hinc hisot
