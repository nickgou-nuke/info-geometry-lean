/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.ZornTransportNondegenerate
import InfoGeometry.Canonical.ZornNullPairDensity

/-! Actual endomorphism trace pairing is invariant when operators and the
split-polar form are transported together. No positive adjoint norm is asserted. -/
noncomputable section
namespace InfoGeometry.Canonical.ZornAdjointTraceTransport
open _root_.InfoGeometry.Canonical.ZornVectorMatrixExplicit
open ZornPolarizationMetricBridge ZornPolarFormTransport ZornTransportNondegenerate
open ZornPolarKetBra ZornNullPeirceWeyl ReflexiveNilpotentFlows

theorem conjugated_product_trace (S T a b : Module.End ℝ ZornCoord) (h : T*S=1) :
    LinearMap.trace ℝ ZornCoord ((S*a*T)*(S*b*T)) = LinearMap.trace ℝ ZornCoord (a*b) := by
  have hp : (S*a*T)*(S*b*T) = S*(a*b)*T := by
    calc
      _ = S*a*(T*S)*b*T := by noncomm_ring
      _ = _ := by rw [h]; noncomm_ring
  rw [hp, LinearMap.trace_mul_comm ℝ]
  congr 1
  calc T*(S*(a*b)) = (T*S)*(a*b) := by noncomm_ring
    _ = a*b := by rw [h, one_mul]

theorem transported_adjoint_trace (S T a f g k : Module.End ℝ ZornCoord)
    (hST : S*T=1) (hTS : T*S=1)
    (hg : LinearMap.IsAdjointPair polarForm polarForm f g)
    (hk : LinearMap.IsAdjointPair (transportedPolar T) (transportedPolar T)
      (S*f*T : Module.End ℝ ZornCoord) k) :
    LinearMap.trace ℝ ZornCoord ((S*a*T)*k) = LinearMap.trace ℝ ZornCoord (a*g) := by
  have he := transportedPolar_adjoint_unique S T (S*f*T) k (S*g*T) hST hTS hk
    (transported_adjoint S T f g hTS hg)
  rw [he]
  exact conjugated_product_trace S T a g hTS

theorem nullRotor_adjoint_trace (X Y : ZornCoord)
    (hX : polarPair X X=0) (hY : polarPair Y Y=0) (h : polarPair X Y=1)
    (c s : ℝ) (hc : c*c+s*s=1) (a f g k : Module.End ℝ ZornCoord)
    (hg : LinearMap.IsAdjointPair polarForm polarForm f g) :
    let S := rotor c s (ketBra X X) (ketBra Y Y)
    let T := rotor c (-s) (ketBra X X) (ketBra Y Y)
    LinearMap.IsAdjointPair (transportedPolar T) (transportedPolar T)
      (S*f*T : Module.End ℝ ZornCoord) k →
    LinearMap.trace ℝ ZornCoord ((S*a*T)*k) = LinearMap.trace ℝ ZornCoord (a*g) := by
  intro S T hk
  have hi := rotor_inverse (R := ℝ) (ketBra_sq_zero X X hX) (ketBra_sq_zero Y Y hY)
    (nullPair_reflexive X Y h) (nullPair_reflexive Y X (by rwa [polarPair_symm]))
  exact transported_adjoint_trace S T a f g k (hi c s hc)
    (by simpa only [neg_neg] using hi c (-s) (by simpa using hc)) hg hk

end InfoGeometry.Canonical.ZornAdjointTraceTransport
