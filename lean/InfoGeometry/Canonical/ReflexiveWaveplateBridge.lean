/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.ReflexiveRotorMotion
import InfoGeometry.Canonical.RealDoubledWaveplate
import InfoGeometry.Quantum.CliffordDictionary
import InfoGeometry.CliffordWeyl.PeirceCircularQwpBridge

/-!
# Reflexive rotors and the existing real doubled waveplate

Contract: polynomial conjugation in an associative algebra is specialized to
the existing null maps on DoubledSpace. The order of these maps fixes the sign:
d is nullAnnihilation, B is nullCreation, so d-B is minus clockAxis.
The resulting rotor is phaseFlow at the negative angle. This is not an
identification with the complex Jones quarter-wave plate or its retardance.
-/
namespace InfoGeometry.Canonical.ReflexiveNilpotentFlows

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
variable {d B : A}

theorem rotor_conjugate_parity (hd : d*d=0) (hB : B*B=0)
    (hr : d*B*d=d) (hs : B*d*B=B) (c s : R) :
    rotor c s d B * (d*B-B*d) * rotor c (-s) d B =
      (c*c-s*s) • (d*B-B*d) - (2*c*s) • (d+B) := by
  rw [mul_sub, sub_mul, rotor_conjugate_plus hd hB hr hs,
    rotor_conjugate_minus hd hB hr hs]
  have htwo : 2*c*s = c*s+c*s := by rw [two_mul, add_mul]
  rw [htwo]
  simp only [sub_smul, smul_sub, add_smul]
  abel

end InfoGeometry.Canonical.ReflexiveNilpotentFlows

noncomputable section
namespace InfoGeometry.Canonical.ReflexiveWaveplateBridge
open InfoGeometry.Krein InfoGeometry.Quantum.Cl11Dictionary
open ReflexiveNilpotentFlows ProjectorEquivariance RealDoubledWaveplate

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The ordered null pair has the full ambient support. -/
theorem nullPair_support :
    support (nullAnnihilation (E := E)) (nullCreation (E := E)) = 1 := by
  exact null_creation_annihilation_CAR

/-- Positive pole minus negative pole is the existing spectral grading. -/
theorem nullPair_parity :
    nullAnnihilation (E := E) * nullCreation - nullCreation * nullAnnihilation =
      spectral_epsilon (E := E) := by
  apply ContinuousLinearMap.ext
  intro u
  apply DoubledSpace.ext <;>
    simp [nullAnnihilation_apply,
      nullCreation_apply, spectral_epsilon_apply, to_doubled]

/-- The scalar rotor has the opposite angle to the owned phase flow. -/
theorem nullPair_rotor (θ : ℝ) :
    ReflexiveNilpotentFlows.rotor (Real.cos θ) (Real.sin θ)
      (nullAnnihilation (E := E)) nullCreation = phaseFlow (E := E) (-θ) := by
  have hsub : nullAnnihilation (E := E) - nullCreation = -clockAxis (E := E) := by
    have h := null_generators_sub_eq_K (E := E)
    calc
      _ = -(nullCreation (E := E) - nullAnnihilation) := by abel
      _ = -clockAxis (E := E) := by rw [h]; rfl
  rw [ReflexiveNilpotentFlows.rotor, complement, nullPair_support, sub_self, zero_add, hsub]
  simp only [phaseFlow, Real.cos_neg, Real.sin_neg, smul_neg]
  change Real.cos θ • (1 : DoubledSpace E →L[ℝ] DoubledSpace E) +
      -(Real.sin θ • clockAxis) = Real.cos θ • 1 + (-Real.sin θ) • clockAxis
  module

/-- The doubled-angle law is inherited through an equality of actual operators. -/
theorem nullPair_rotor_conjugates_grading (θ : ℝ) :
    ReflexiveNilpotentFlows.rotor (Real.cos θ) (Real.sin θ) (nullAnnihilation (E := E)) nullCreation *
      spectral_epsilon *
      ReflexiveNilpotentFlows.rotor (Real.cos (-θ)) (Real.sin (-θ)) nullAnnihilation nullCreation =
        Real.cos (2*θ) • spectral_epsilon (E := E) -
          Real.sin (2*θ) • modular_j := by
  rw [nullPair_rotor, nullPair_rotor, neg_neg]
  exact phaseFlow_conj_spectral_epsilon θ

/-- A 45-degree rotor parameter changes the grading axis, rather than negating it. -/
theorem nullPair_rotor_pi_div_four :
    ReflexiveNilpotentFlows.rotor (Real.cos (Real.pi/4)) (Real.sin (Real.pi/4))
      (nullAnnihilation (E := E)) nullCreation * spectral_epsilon *
      ReflexiveNilpotentFlows.rotor (Real.cos (-(Real.pi/4))) (Real.sin (-(Real.pi/4)))
        nullAnnihilation nullCreation = -modular_j (E := E) := by
  rw [nullPair_rotor, nullPair_rotor, neg_neg]
  exact phaseFlow_conj_spectral_epsilon_pi_div_four

end InfoGeometry.Canonical.ReflexiveWaveplateBridge

namespace InfoGeometry.Canonical.ReflexiveJonesRephasing
open Matrix InfoGeometry.CliffordWeyl.PeirceCircularQwpBridge

/-- Complex coordinate rephasing, distinct from changing a Krein adjoint. -/
def rephasing : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, Complex.I]

theorem rephasing_unitary : rephasingᴴ * rephasing = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rephasing, Matrix.mul_apply, Fin.sum_univ_two]

/-- Rephasing the real skew rotor produces the Jones quarter-wave generator. -/
theorem rephasing_rotor (c s : ℂ) :
    rephasing * !![c, s; -s, c] * rephasingᴴ =
      !![c, -Complex.I*s; -Complex.I*s, c] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    (simp [rephasing, Matrix.mul_apply, Fin.sum_univ_two] <;> ring_nf)
  all_goals simp [Complex.I_sq]

/-- The exact existing QWP is the rephased equal-weight rotor. -/
theorem rephasing_equal_weight_eq_Uqwp :
    rephasing * !![s2, s2; -s2, s2] * rephasingᴴ = Uqwp := by
  rw [rephasing_rotor]
  rfl

end InfoGeometry.Canonical.ReflexiveJonesRephasing
