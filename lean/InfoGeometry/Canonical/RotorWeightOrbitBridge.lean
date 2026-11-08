/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.DeBruijnRotorAlternationCycle
import InfoGeometry.Canonical.UnifiedGeometryOperatorSignificance
import InfoGeometry.Canonical.PeirceWeightedTrace
import InfoGeometry.Canonical.ReflexiveRotorRealTime

/-!
# Native rotor, unit orbit, and weighted readout connections

The existing Stream5 primitive pair supplies the native reflexive hypotheses.
Local actual units connect its moving pole to the existing Grassmannian orbit.
Density conjugation and joint tracial covariance use native weight/readout
owners. The final consumer reads Stream5's sin/cos path through the proved
native real-time derivative. No new carrier or aggregate certificate is used.
-/
noncomputable section

namespace InfoGeometry.Canonical.RotorWeightOrbitBridge

open DeBruijnRotorAlternationCycle (IsDualSeedPair phaseRotor movingPolePlus)
open ReflexiveNilpotentFlows (rotor_inverse rotor_reverse_inverse
  rotor_conjugate_minus rotor_conjugate_plus support_table)
open PeirceWeightedTrace (supportWeight)
open GrassmannianBundleCyclotomicOrientability (unitOrbitMap)
open InfoGeometry.OperatorAlgebra.TracialCARDensity (weighted weighted_apply joint_covariance)
open InfoGeometry.NCG (TracialFunctional)

section Algebraic
variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]

/-- Definition readback used to consume the native rotor inverse laws. -/
theorem phaseRotor_eq_native (c s : R) (d B : A) :
    phaseRotor c s d B = ReflexiveNilpotentFlows.rotor c s d B := rfl

/-- The Stream3 squared weight is a specialization of the native arbitrary weight. -/
theorem kmsWeight_eq_supportWeight (u v : R) (d B : A) :
    UnifiedGeometryOperatorSignificance.kmsModularWeight u v d B =
      supportWeight (u*u) (v*v) d B := rfl

/-- The moving pole is in the existing unit orbit, not just formally idempotent. -/
theorem movingPolePlus_mem_unitOrbit {d B : A} (h : IsDualSeedPair d B)
    (c s : R) (hc : c*c+s*s=1) :
    movingPolePlus c s d B ∈ Set.range (unitOrbitMap (d*B)) := by
  let u : Aˣ :=
    { val := ReflexiveNilpotentFlows.rotor c s d B
      inv := ReflexiveNilpotentFlows.rotor c (-s) d B
      val_inv := rotor_inverse h.d_sq h.B_sq h.dBd h.BdB c s hc
      inv_val := rotor_reverse_inverse h.d_sq h.B_sq h.dBd h.BdB c s hc }
  exact ⟨u, rfl⟩

/-- Rotation of the existing arbitrary density has a derived off-diagonal component.
No circle normalization is required for this polynomial identity. -/
theorem rotor_supportWeight_conjugation {d B : A} (h : IsDualSeedPair d B)
    (a b c s : R) :
    ReflexiveNilpotentFlows.rotor c s d B * supportWeight a b d B * ReflexiveNilpotentFlows.rotor c (-s) d B =
      (a*(s*s)+b*(c*c)) • (d*B) + (a*(c*c)+b*(s*s)) • (B*d) +
        ((a-b)*(c*s)) • (d+B) := by
  simp only [supportWeight, mul_add, add_mul, mul_smul_comm, smul_mul_assoc]
  rw [rotor_conjugate_minus h.d_sq h.B_sq h.dBd h.BdB,
    rotor_conjugate_plus h.d_sq h.B_sq h.dBd h.BdB]
  simp only [smul_add, smul_sub, smul_smul, add_smul, sub_mul, sub_smul]
  abel

/-- Joint transport of Stream3's density and Stream5's moving pole preserves the
actual native weighted readout. This is not fixed-density invariance. -/
theorem kmsWeight_movingPole_joint {d B : A} (h : IsDualSeedPair d B)
    (τ : TracialFunctional R A) (u v c s : R) (hc : c*c+s*s=1) :
    weighted τ
      (phaseRotor c s d B * UnifiedGeometryOperatorSignificance.kmsModularWeight u v d B *
        phaseRotor c (-s) d B) (movingPolePlus c s d B) = (v*v) * τ (d*B) := by
  rw [kmsWeight_eq_supportWeight]
  let g : Aˣ :=
    { val := ReflexiveNilpotentFlows.rotor c s d B
      inv := ReflexiveNilpotentFlows.rotor c (-s) d B
      val_inv := rotor_inverse h.d_sq h.B_sq h.dBd h.BdB c s hc
      inv_val := rotor_reverse_inverse h.d_sq h.B_sq h.dBd h.BdB c s hc }
  have hjoint := joint_covariance τ g (supportWeight (u*u) (v*v) d B) (d*B)
  change weighted τ (ReflexiveNilpotentFlows.rotor c s d B * supportWeight (u*u) (v*v) d B * ReflexiveNilpotentFlows.rotor c (-s) d B)
    (ReflexiveNilpotentFlows.rotor c s d B * (d*B) * ReflexiveNilpotentFlows.rotor c (-s) d B) =
      weighted τ (supportWeight (u*u) (v*v) d B) (d*B) at hjoint
  have hp : supportWeight (u*u) (v*v) d B * (d*B) = (v*v) • (d*B) := by
    obtain ⟨hpp, _, _, hmp, _, _, _, _, _⟩ :=
      support_table h.d_sq h.B_sq h.dBd h.BdB
    simp only [supportWeight, add_mul, smul_mul_assoc, hmp, hpp, smul_zero, zero_add]
  change weighted τ (ReflexiveNilpotentFlows.rotor c s d B * supportWeight (u*u) (v*v) d B * ReflexiveNilpotentFlows.rotor c (-s) d B)
    (ReflexiveNilpotentFlows.rotor c s d B * (d*B) * ReflexiveNilpotentFlows.rotor c (-s) d B) = (v*v) * τ (d*B)
  rw [hjoint, weighted_apply, hp, τ.map_smul, smul_eq_mul]

end Algebraic

section RealTime
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]

/-- Function equality connects Stream5's scalar formula to the actual native path. -/
theorem movingPolePlus_circle_eq_native (d B : A) :
    (fun t : ℝ => movingPolePlus (Real.cos t) (Real.sin t) d B) =
      ModularFlowGeneratorDerivative.conjugationPath
        (ReflexiveRotorRealTime.realRotor d B)
        (fun t => ReflexiveRotorRealTime.realRotor d B (-t)) (d*B) := by
  funext t
  simp only [movingPolePlus, phaseRotor_eq_native,
    DeBruijnRotorAlternationCycle.polePlus,
    ModularFlowGeneratorDerivative.conjugationPath,
    ReflexiveRotorRealTime.realRotor, Real.cos_neg, Real.sin_neg]

/-- Stream5's moving pole has a genuine derivative on its concrete sine/cosine path. -/
theorem hasDerivAt_movingPolePlus_circle {d B : A} (h : IsDualSeedPair d B) (t : ℝ) :
    HasDerivAt (fun s : ℝ => movingPolePlus (Real.cos s) (Real.sin s) d B)
      (GrassmannianBundleCyclotomicOrientability.lieBracket (d-B)
        (movingPolePlus (Real.cos t) (Real.sin t) d B)) t := by
  have hp := movingPolePlus_circle_eq_native d B
  have ht := congrFun hp t
  rw [hp, ht]
  exact ReflexiveRotorRealTime.hasDerivAt_rotorOrbit h.d_sq h.B_sq h.dBd h.BdB (d*B) t

end RealTime
end InfoGeometry.Canonical.RotorWeightOrbitBridge
