import Mathlib
import InfoGeometry.OperatorAlgebra.KreinIsotropicCone
import InfoGeometry.OperatorAlgebra.JUnitaryTopologicalCharge

noncomputable section

namespace InfoGeometry.OperatorAlgebra.OperatorialJonesCalculus

/-! ## 1. Polarization projectors -/

/--
A pair of complementary polarization projectors.

The intended model is the Fresnel `s/p` basis.
-/
structure PolarizationProjectorPair
    (Op : Type*) [Ring Op] [Algebra ℂ Op] where
  /-- Fresnel `s`-sector projector. -/
  P_s : Op

  /-- Fresnel `p`-sector projector. -/
  P_p : Op

  /-- The `s` projector is idempotent. -/
  P_s_idem :
    P_s * P_s = P_s

  /-- The `p` projector is idempotent. -/
  P_p_idem :
    P_p * P_p = P_p

  /-- The sectors are disjoint in the `s`-then-`p` order. -/
  s_p_disjoint :
    P_s * P_p = 0

  /-- The sectors are disjoint in the `p`-then-`s` order. -/
  p_s_disjoint :
    P_p * P_s = 0

  /-- The two sectors decompose the identity. -/
  sum_eq_one :
    P_s + P_p = 1

namespace PolarizationProjectorPair

variable {Op : Type*} [Ring Op] [Algebra ℂ Op]
variable (P : PolarizationProjectorPair Op)

/--
The Fresnel reflection operator:

`R = r_s P_s + r_p P_p`.
-/
def fresnelReflector
    (r_s r_p : ℂ) : Op :=
  r_s • P.P_s + r_p • P.P_p

/--
The Fresnel Cartan operator for the `s/p` basis.
-/
def spCartan : Op :=
  P.P_s - P.P_p

/--
The `s/p` Cartan operator is an involution.

This is the optical Cartan-axis fact: complementary Fresnel projectors define
the polarization grading `chi_sp = P_s - P_p`.
-/
theorem spCartan_sq :
    P.spCartan * P.spCartan = 1 := by
  dsimp [spCartan]
  calc
    (P.P_s - P.P_p) * (P.P_s - P.P_p)
        = P.P_s * P.P_s - P.P_s * P.P_p -
            P.P_p * P.P_s + P.P_p * P.P_p := by
            noncomm_ring
    _ = P.P_s - 0 - 0 + P.P_p := by
            rw [P.P_s_idem, P.P_p_idem, P.s_p_disjoint, P.p_s_disjoint]
    _ = P.P_s + P.P_p := by
            abel
    _ = 1 := P.sum_eq_one

/-- The complementary projector identity `1 - P_s = P_p`. -/
theorem one_sub_P_s_eq_P_p :
    (1 : Op) - P.P_s = P.P_p := by
  rw [← P.sum_eq_one]
  abel

/-- The complementary projector identity `1 - P_p = P_s`. -/
theorem one_sub_P_p_eq_P_s :
    (1 : Op) - P.P_p = P.P_s := by
  rw [← P.sum_eq_one]
  abel

/--
The Fresnel reflector acts on the `s` eigensector by the scalar `r_s`.
-/
theorem fresnelReflector_mul_P_s
    (r_s r_p : ℂ) :
    P.fresnelReflector r_s r_p * P.P_s = r_s • P.P_s := by
  dsimp [fresnelReflector]
  rw [add_mul, smul_mul_assoc, smul_mul_assoc, P.P_s_idem, P.p_s_disjoint,
    smul_zero, add_zero]

/--
The Fresnel reflector acts on the `p` eigensector by the scalar `r_p`.
-/
theorem fresnelReflector_mul_P_p
    (r_s r_p : ℂ) :
    P.fresnelReflector r_s r_p * P.P_p = r_p • P.P_p := by
  dsimp [fresnelReflector]
  rw [add_mul, smul_mul_assoc, smul_mul_assoc, P.s_p_disjoint, P.P_p_idem,
    smul_zero, zero_add]

/--
The `s` eigensector reads out the scalar `r_s` on the left as well.
-/
theorem P_s_mul_fresnelReflector
    (r_s r_p : ℂ) :
    P.P_s * P.fresnelReflector r_s r_p = r_s • P.P_s := by
  dsimp [fresnelReflector]
  rw [mul_add, mul_smul_comm, mul_smul_comm, P.P_s_idem, P.s_p_disjoint,
    smul_zero, add_zero]

/--
The `p` eigensector reads out the scalar `r_p` on the left as well.
-/
theorem P_p_mul_fresnelReflector
    (r_s r_p : ℂ) :
    P.P_p * P.fresnelReflector r_s r_p = r_p • P.P_p := by
  dsimp [fresnelReflector]
  rw [mul_add, mul_smul_comm, mul_smul_comm, P.p_s_disjoint, P.P_p_idem,
    smul_zero, zero_add]

/--
Brewster reflector: the `p` channel is killed.
-/
def brewsterReflector
    (r_s : ℂ) : Op :=
  P.fresnelReflector r_s 0

/--
At Brewster angle, the reflector is a scalar multiple of the `s` projector.
-/
theorem brewsterReflector_eq
    (r_s : ℂ) :
    P.brewsterReflector r_s = r_s • P.P_s := by
  simp [brewsterReflector, fresnelReflector]

/--
Brewster reflection is projector-like up to its surviving scalar:

`R_B² = r_s R_B`.

It is literally idempotent only when the surviving amplitude is normalized to
`1`; projectively, the ray action is the same as `P_s` whenever `r_s ≠ 0`.
-/
theorem brewsterReflector_sq
    (r_s : ℂ) :
    P.brewsterReflector r_s * P.brewsterReflector r_s =
      r_s • P.brewsterReflector r_s := by
  rw [P.brewsterReflector_eq r_s]
  simp [smul_mul_assoc, mul_smul_comm, smul_smul, P.P_s_idem, mul_assoc]

/--
Candidate Drazin inverse for Brewster reflection when `r_s ≠ 0`.

The stronger Drazin API bridge can import this formula and prove the full
Drazin laws against the repository's Drazin definitions.
-/
def brewsterDrazinInverseCandidate
    (r_s : ℂ) : Op :=
  r_s⁻¹ • P.P_s

/--
The Brewster reflector composed with its inverse candidate gives the surviving
core projector `P_s`.
-/
theorem brewster_core_projector_left
    {r_s : ℂ}
    (hrs : r_s ≠ 0) :
    P.brewsterReflector r_s * P.brewsterDrazinInverseCandidate r_s = P.P_s := by
  rw [P.brewsterReflector_eq r_s]
  dsimp [brewsterDrazinInverseCandidate]
  simp [smul_mul_assoc, mul_smul_comm, smul_smul, P.P_s_idem, hrs]

/--
The inverse candidate composed with the Brewster reflector gives the same
surviving core projector `P_s`.
-/
theorem brewster_core_projector_right
    {r_s : ℂ}
    (hrs : r_s ≠ 0) :
    P.brewsterDrazinInverseCandidate r_s * P.brewsterReflector r_s = P.P_s := by
  rw [P.brewsterReflector_eq r_s]
  dsimp [brewsterDrazinInverseCandidate]
  simp [smul_mul_assoc, mul_smul_comm, smul_smul, P.P_s_idem, hrs, mul_comm]

/--
The complementary Brewster nil/generalized-zero projector is the killed
`p` sector.
-/
theorem brewster_nil_projector_eq_P_p
    {r_s : ℂ}
    (hrs : r_s ≠ 0) :
    (1 : Op) -
        P.brewsterReflector r_s * P.brewsterDrazinInverseCandidate r_s =
      P.P_p := by
  rw [P.brewster_core_projector_left hrs]
  exact P.one_sub_P_s_eq_P_p

/--
Total-internal-reflection / retarder branch.

The amplitudes are unit-modulus phases; this records the operator, not the
analytic Fresnel formula for the phases.
-/
def phaseRetarder
    (phi_s phi_p : ℝ) : Op :=
  (Complex.exp (Complex.I * (phi_s : ℂ))) • P.P_s +
    (Complex.exp (Complex.I * (phi_p : ℂ))) • P.P_p

/--
A deterministic Jones action on an operator-valued state.

For a concrete star-algebra this is the abstract form of `R ρ R†`.
-/
def jonesAction
    (adj : Op → Op)
    (R rho : Op) : Op :=
  R * rho * adj R

end PolarizationProjectorPair

end InfoGeometry.OperatorAlgebra.OperatorialJonesCalculus
