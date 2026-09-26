import InfoGeometry.Algebra.H3ZornFreudenthalScaling
import InfoGeometry.Analysis.LogHomogeneousPotential

/-!
# Logarithmic readout of the existing split-Albert Freudenthal quartic

The domain is the positive quartic chamber. The cubic Jordan norm, the quartic
on the charge carrier, and its logarithm remain different functions on their
respective carriers. No exceptional-group or curved para-hyperkähler metric
identification is inferred from the logarithm.
-/

noncomputable section

namespace InfoGeometry.Exceptional.FreudenthalLogPotential

open InfoGeometry.Algebra.H3ZornFreudenthal
open InfoGeometry.Analysis.LogHomogeneousPotential

def potential (Q : Charge) : ℝ := logPotential quarticInvariant Q

theorem potential_scale (Q : Charge) (hQ : 0 < quarticInvariant Q)
    (r : ℝ) (hr : 0 < r) :
    potential (r • Q) = potential Q - 4 * Real.log r := by
  exact logPotential_smul quarticInvariant 4 quarticInvariant_smul Q hQ r hr

theorem potential_zero_iff (Q : Charge) (hQ : 0 < quarticInvariant Q) :
    potential Q = 0 ↔ quarticInvariant Q = 1 :=
  logPotential_zero_iff quarticInvariant Q hQ

theorem entropy_readout (Q : Charge) (hQ : 0 < quarticInvariant Q) :
    Real.pi * Real.sqrt (quarticInvariant Q) =
      Real.pi * Real.exp (-potential Q / 2) := by
  rw [sqrt_eq_exp_logPotential quarticInvariant Q hQ]
  rfl

theorem quartic_boundary_excluded (Q : Charge) (hQ : 0 < quarticInvariant Q) :
    quarticInvariant Q ≠ 0 := ne_of_gt hQ

end InfoGeometry.Exceptional.FreudenthalLogPotential
