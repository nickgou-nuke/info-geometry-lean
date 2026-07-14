import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Explicit holographic pressure functional

This file contains only explicit scalar readouts.  It does not introduce packet
fields for area laws, free-energy laws, pressure laws, or Newtonian matching.

The core functions are:

* `weylBoundaryArea A0 q chi = A0 * exp (q * chi)`;
* `majoranaFreeEnergy F0 z Neff chi = F0 + (z / 2) * Neff * chi`;
* `outwardPressure = (dF/dchi)/(dA/dchi)` using the explicit derivative
  readouts for these two closed forms;
* `newtonianMatchedAlpha kappa c0 G = 4πGκ/c0²`;
* the Newtonian scalar Poisson readout follows by algebra from that definition.
-/

namespace HolographicPressureFunctional

/-! ## 1. Explicit Weyl area and Majorana free energy -/

/-- Explicit Weyl-scaled boundary area `A(χ) = A₀ exp(qχ)`. -/
noncomputable def weylBoundaryArea (A0 q chi : ℝ) : ℝ :=
  A0 * Real.exp (q * chi)

/-- Explicit derivative readout of `weylBoundaryArea` with respect to `χ`. -/
noncomputable def weylBoundaryAreaDerivative (A0 q chi : ℝ) : ℝ :=
  q * weylBoundaryArea A0 q chi

/-- The boundary-area derivative readout is by definition `q * A`. -/
theorem weylBoundaryAreaDerivative_eq_dim_mul_area (A0 q chi : ℝ) :
    weylBoundaryAreaDerivative A0 q chi = q * weylBoundaryArea A0 q chi :=
  rfl

/-- Explicit Majorana/Pfaffian free energy `F(χ) = F₀ + (z/2) N_eff χ`. -/
noncomputable def majoranaFreeEnergy (F0 z Neff chi : ℝ) : ℝ :=
  F0 + (z / 2) * Neff * chi

/-- Explicit derivative readout of the linear Majorana/Pfaffian free energy. -/
noncomputable def majoranaFreeEnergyDerivative (_F0 z Neff _chi : ℝ) : ℝ :=
  (z / 2) * Neff

/-- The free-energy derivative readout is by definition `(z/2) N_eff`. -/
theorem majoranaFreeEnergyDerivative_eq_half_z_modes (F0 z Neff chi : ℝ) :
    majoranaFreeEnergyDerivative F0 z Neff chi = (z / 2) * Neff :=
  rfl

/-- Outward pressure convention `P_out = (dF/dχ)/(dA/dχ)`. -/
noncomputable def outwardPressure (A0 q F0 z Neff chi : ℝ) : ℝ :=
  majoranaFreeEnergyDerivative F0 z Neff chi / weylBoundaryAreaDerivative A0 q chi

/-- First scalar pressure coefficient of the explicit Majorana/Pfaffian layer. -/
theorem holographicPressure_coeff (A0 q F0 z Neff chi : ℝ) :
    outwardPressure A0 q F0 z Neff chi =
      z * Neff / (2 * q * weylBoundaryArea A0 q chi) := by
  unfold outwardPressure majoranaFreeEnergyDerivative weylBoundaryAreaDerivative
  ring_nf

/-- Explicit positive partition function associated to the free energy. -/
noncomputable def boundaryPartitionFunction (F0 z Neff chi : ℝ) : ℝ :=
  Real.exp (-(majoranaFreeEnergy F0 z Neff chi))

/-- The explicit partition function is positive. -/
theorem boundaryPartitionFunction_pos (F0 z Neff chi : ℝ) :
    0 < boundaryPartitionFunction F0 z Neff chi := by
  unfold boundaryPartitionFunction
  exact Real.exp_pos _

/-- Explicit boundary free energy `-log Z`. -/
noncomputable def boundaryFreeEnergyFromPartition (F0 z Neff chi : ℝ) : ℝ :=
  -Real.log (boundaryPartitionFunction F0 z Neff chi)

/-- The explicit partition function recovers the explicit Majorana free energy. -/
theorem boundaryFreeEnergyFromPartition_eq_majoranaFreeEnergy
    (F0 z Neff chi : ℝ) :
    boundaryFreeEnergyFromPartition F0 z Neff chi = majoranaFreeEnergy F0 z Neff chi := by
  unfold boundaryFreeEnergyFromPartition boundaryPartitionFunction
  rw [Real.log_exp]
  ring

/-- Holographic pressure sign convention `P_holo = -P_out`. -/
noncomputable def holographicPressure (A0 q F0 z Neff chi : ℝ) : ℝ :=
  -outwardPressure A0 q F0 z Neff chi

/-- Explicit holographic pressure coefficient with the `P_holo = -P_out` convention. -/
theorem holographicPressure_eq_neg_coeff (A0 q F0 z Neff chi : ℝ) :
    holographicPressure A0 q F0 z Neff chi =
      -(z * Neff / (2 * q * weylBoundaryArea A0 q chi)) := by
  unfold holographicPressure
  rw [holographicPressure_coeff]

/-! ## 2. Toy equilibrium law -/

/--
Division-form toy equation of state:
`N / φ² = c φ` implies `φ³ = N / c`, provided the displayed denominators are
nonzero.
-/
theorem stableScale_cubic
    {N c phi : ℝ}
    (h_eq : N / phi ^ 2 = c * phi)
    (hphi : phi ≠ 0)
    (hc : c ≠ 0) :
    phi ^ 3 = N / c := by
  field_simp [hphi, hc] at h_eq ⊢
  nlinarith

/-! ## 3. Explicit Newtonian scalar limit -/

/-- Explicit scalar Weyl-pressure equation readout `∇²δχ = -(α/κ)ρ`. -/
noncomputable def weylLapDeltaChi (kappa alpha rho : ℝ) : ℝ :=
  -(alpha / kappa) * rho

/-- Laplacian-level readout of `δχ = -Φ/c₀²`: `∇²Φ = -c₀² ∇²δχ`. -/
noncomputable def newtonianLapPhi (kappa alpha c0 rho : ℝ) : ℝ :=
  -c0 ^ 2 * weylLapDeltaChi kappa alpha rho

/-- Explicit coupling value matching the Newtonian Poisson coefficient. -/
noncomputable def newtonianMatchedAlpha (kappa c0 G : ℝ) : ℝ :=
  4 * Real.pi * G * kappa / c0 ^ 2

/--
Explicit Newtonian limit:
with `α = 4πGκ/c₀²`, the scalar Weyl-pressure readout gives
`∇²Φ = 4πGρ`.
-/
theorem newtonianLimit_from_weylPressure
    {kappa c0 G rho : ℝ}
    (hkappa : kappa ≠ 0)
    (hc0 : c0 ≠ 0) :
    newtonianLapPhi kappa (newtonianMatchedAlpha kappa c0 G) c0 rho =
      (4 * Real.pi * G) * rho := by
  unfold newtonianLapPhi weylLapDeltaChi newtonianMatchedAlpha
  field_simp [hkappa, hc0]

/-! ## 4. Explicit quantum-limit balance law -/

/--
Two-term quantum-limit free-energy ansatz:
`A * ellK / L + B * L / ellE8`.

This is only an explicit scalar model.  Identifying the critical scale with a
physical Planck length is a later calibration step, not part of this theorem.
-/
noncomputable def quantumLimitFreeEnergy
    (A B ellK ellE8 L : ℝ) : ℝ :=
  A * ellK / L + B * L / ellE8

/-- Explicit critical-balance equation for the two-term ansatz. -/
def quantumLimitCriticalEquation
    (A B ellK ellE8 L : ℝ) : Prop :=
  -A * ellK / L ^ 2 + B / ellE8 = 0

/--
At a nondegenerate critical point of the two-term balance ansatz,
`L² = (A/B) * ellK * ellE8`.
-/
theorem quantumLimit_geometricMean_sq
    {A B ellK ellE8 L : ℝ}
    (hcrit : quantumLimitCriticalEquation A B ellK ellE8 L)
    (hL : L ≠ 0)
    (hB : B ≠ 0)
    (hellE8 : ellE8 ≠ 0) :
    L ^ 2 = (A / B) * ellK * ellE8 := by
  unfold quantumLimitCriticalEquation at hcrit
  field_simp [hL, hB, hellE8] at hcrit ⊢
  nlinarith

/--
At a nondegenerate critical point of the two-term balance ansatz, the critical
scale is the positive square root of the geometric-mean readout.
-/
theorem quantumLimit_geometricMean
    {A B ellK ellE8 L : ℝ}
    (hcrit : quantumLimitCriticalEquation A B ellK ellE8 L)
    (hL : 0 ≤ L)
    (hL0 : L ≠ 0)
    (hB : B ≠ 0)
    (hellE8 : ellE8 ≠ 0)
    (hR : 0 ≤ (A / B) * ellK * ellE8) :
    L = Real.sqrt ((A / B) * ellK * ellE8) := by
  have hsq := quantumLimit_geometricMean_sq hcrit hL0 hB hellE8
  have hs :
      (Real.sqrt ((A / B) * ellK * ellE8)) ^ 2 = (A / B) * ellK * ellE8 := by
    rw [Real.sq_sqrt hR]
  apply (sq_eq_sq₀ hL (Real.sqrt_nonneg _)).mp
  simpa [hs] using hsq

/-- If the two coefficients agree, the critical scale squares to `ellK * ellE8`. -/
theorem quantumLimit_geometricMean_sq_of_equal_coeff
    {A ellK ellE8 L : ℝ}
    (hcrit : quantumLimitCriticalEquation A A ellK ellE8 L)
    (hL : L ≠ 0)
    (hA : A ≠ 0)
    (hellE8 : ellE8 ≠ 0) :
    L ^ 2 = ellK * ellE8 := by
  rw [quantumLimit_geometricMean_sq hcrit hL hA hellE8]
  field_simp [hA]

end HolographicPressureFunctional
