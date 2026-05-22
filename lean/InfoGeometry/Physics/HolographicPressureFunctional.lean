import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Holographic Pressure Functional

Effective scalar pressure layer for the Weyl/Majorana boundary model.

This file proves only the scalar coefficient and effective-limit algebra:

* a Weyl-scaled boundary area with `dA/dχ = q A`;
* a Majorana/Pfaffian free-energy readout with `dF/dχ = (z/2) N_eff`;
* the outward pressure coefficient `P = z N_eff / (2 q A)`;
* the cubic toy equilibrium in division form;
* the conditional Newtonian Poisson limit from a Weyl-pressure scalar equation.

It does not assert a covariant Einstein equation, a spectral determinant
construction, or an `E₈` spectrum theorem.
-/

namespace InfoGeometry.Physics.HolographicPressureFunctional

/-! ## 1. Weyl boundary area and Majorana Pfaffian scaling -/

/--
Boundary area/volume scaling under a Weyl scalar `χ`.

The intended model is `A(χ) = A₀ exp(qχ)`, with derivative readout
`dA/dχ = q A`.
-/
structure WeylBoundaryArea where
  q : ℝ
  A0 : ℝ
  chi : ℝ
  A : ℝ
  dA_dchi : ℝ
  A_eq : A = A0 * Real.exp (q * chi)
  dA_dchi_eq : dA_dchi = q * A

namespace WeylBoundaryArea

theorem area_eq_exp_scale (B : WeylBoundaryArea) :
    B.A = B.A0 * Real.exp (B.q * B.chi) :=
  B.A_eq

theorem area_derivative_eq_dim_mul_area (B : WeylBoundaryArea) :
    B.dA_dchi = B.q * B.A :=
  B.dA_dchi_eq

end WeylBoundaryArea

/--
Majorana/Pfaffian boundary free-energy scaling.

The intended readout is
`F(χ) = F₀ + (z/2) N_eff χ`, coming from
`λ_k(χ) = exp(-zχ) λ_k(0)` and a regularized active-mode count.
-/
structure MajoranaPfaffianScaling where
  z : ℝ
  Neff : ℝ
  F0 : ℝ
  chi : ℝ
  F : ℝ
  dF_dchi : ℝ
  F_eq : F = F0 + (z / 2) * Neff * chi
  dF_dchi_eq : dF_dchi = (z / 2) * Neff

namespace MajoranaPfaffianScaling

theorem freeEnergy_eq_linear_weyl (M : MajoranaPfaffianScaling) :
    M.F = M.F0 + (M.z / 2) * M.Neff * M.chi :=
  M.F_eq

theorem freeEnergy_derivative_eq_half_z_modes (M : MajoranaPfaffianScaling) :
    M.dF_dchi = (M.z / 2) * M.Neff :=
  M.dF_dchi_eq

end MajoranaPfaffianScaling

/-- Outward pressure convention: `P_out = dF/dA = (dF/dχ)/(dA/dχ)`. -/
noncomputable def outwardPressure (B : WeylBoundaryArea) (M : MajoranaPfaffianScaling) : ℝ :=
  M.dF_dchi / B.dA_dchi

/--
First scalar pressure coefficient of the boundary Majorana/Pfaffian layer:

`P_out = z N_eff / (2 q A)`.
-/
theorem holographicPressure_coeff
    (B : WeylBoundaryArea) (M : MajoranaPfaffianScaling) :
    outwardPressure B M = M.z * M.Neff / (2 * B.q * B.A) := by
  unfold outwardPressure
  rw [M.dF_dchi_eq, B.dA_dchi_eq]
  ring_nf

/--
Boundary holographic functional packet.

This is the sign-convention-safe variational readout:

* `boundaryPartitionFunction` plays the role of `|Pf D_∂|`;
* `boundaryFreeEnergy = -log boundaryPartitionFunction`;
* `holographicPressure = -δF_∂/δA_∂`.

The file does not assert that the Pfaffian is constructed analytically; that
information is carried by the scalar readout fields.
-/
structure BoundaryHolographicFunctionalPacket where
  boundaryArea : WeylBoundaryArea
  boundaryPfaffian : MajoranaPfaffianScaling
  boundaryPartitionFunction : ℝ
  boundaryFreeEnergy : ℝ
  holographicPressure : ℝ
  boundaryPartitionFunction_pos : 0 < boundaryPartitionFunction
  boundaryFreeEnergy_eq_neg_log_partition :
    boundaryFreeEnergy = - Real.log boundaryPartitionFunction
  holographicPressure_eq_neg_outward :
    holographicPressure =
      - outwardPressure boundaryArea boundaryPfaffian

namespace BoundaryHolographicFunctionalPacket

/-- Boundary partition function is a positive Pfaffian magnitude. -/
theorem boundaryPartitionFunction_pos'
    (B : BoundaryHolographicFunctionalPacket) :
    0 < B.boundaryPartitionFunction :=
  B.boundaryPartitionFunction_pos

/-- Boundary free energy is the negative logarithm of the boundary partition function. -/
theorem freeEnergy_eq_neg_log_partition
    (B : BoundaryHolographicFunctionalPacket) :
    B.boundaryFreeEnergy = - Real.log B.boundaryPartitionFunction :=
  B.boundaryFreeEnergy_eq_neg_log_partition

/-- Holographic pressure is the negative outward-pressure readout. -/
theorem holographicPressure_eq_neg_outwardPressure
    (B : BoundaryHolographicFunctionalPacket) :
    B.holographicPressure =
      - outwardPressure B.boundaryArea B.boundaryPfaffian :=
  B.holographicPressure_eq_neg_outward

/-- The sign convention `P_holo = - δF/δA` is represented by `- outwardPressure`. -/
theorem holographicPressure_eq_neg_coeff
    (B : BoundaryHolographicFunctionalPacket) :
    B.holographicPressure =
      - (B.boundaryPfaffian.z * B.boundaryPfaffian.Neff
          / (2 * B.boundaryArea.q * B.boundaryArea.A)) := by
  rw [B.holographicPressure_eq_neg_outwardPressure,
    holographicPressure_coeff]

end BoundaryHolographicFunctionalPacket

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

/-! ## 3. Conditional Newtonian limit -/

/--
Scalar readout of the Weyl-pressure Poisson limit.

`lapDeltaChi` is the Laplacian of the Weyl fluctuation `δχ`; `lapPhi` is the
Laplacian of the Newtonian potential.  The relation
`δχ = -Φ/c₀²` is represented at Laplacian level by
`lapPhi = -c₀² lapDeltaChi`.
-/
structure WeylPoissonDatum where
  kappa : ℝ
  alpha : ℝ
  c0 : ℝ
  G : ℝ
  rho : ℝ
  lapDeltaChi : ℝ
  lapPhi : ℝ
  coupling_match : alpha * c0 ^ 2 / kappa = 4 * Real.pi * G
  weyl_poisson : lapDeltaChi = -(alpha / kappa) * rho
  potential_laplacian_relation : lapPhi = -c0 ^ 2 * lapDeltaChi

namespace WeylPoissonDatum

/-- The supplied scalar Weyl-pressure equation. -/
theorem lapDeltaChi_eq_source (W : WeylPoissonDatum) :
    W.lapDeltaChi = -(W.alpha / W.kappa) * W.rho :=
  W.weyl_poisson

/-- Laplacian-level form of `δχ = -Φ/c₀²`. -/
theorem lapPhi_eq_neg_c0_sq_lapDeltaChi (W : WeylPoissonDatum) :
    W.lapPhi = -W.c0 ^ 2 * W.lapDeltaChi :=
  W.potential_laplacian_relation

/--
Conditional Newtonian limit:
if the Weyl-pressure Poisson equation and coupling match are supplied, then
`∇²Φ = 4πGρ` at the scalar readout level.
-/
theorem newtonianLimit_from_weylPressure (W : WeylPoissonDatum) :
    W.lapPhi = (4 * Real.pi * W.G) * W.rho := by
  calc
    W.lapPhi = -W.c0 ^ 2 * W.lapDeltaChi := W.potential_laplacian_relation
    _ = -W.c0 ^ 2 * (-(W.alpha / W.kappa) * W.rho) := by
          rw [W.weyl_poisson]
    _ = (W.alpha * W.c0 ^ 2 / W.kappa) * W.rho := by
          ring
    _ = (4 * Real.pi * W.G) * W.rho := by
          rw [W.coupling_match]

end WeylPoissonDatum

end InfoGeometry.Physics.HolographicPressureFunctional
