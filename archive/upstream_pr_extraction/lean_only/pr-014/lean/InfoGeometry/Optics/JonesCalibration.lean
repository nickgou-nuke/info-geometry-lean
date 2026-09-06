/-
InfoGeometry/Optics/JonesCalibration.lean

Jones calibration of operatorial polarization sectors.

This module connects abstract operator-sector data to optical polarization
readouts:

* s/p Fresnel eigenchannels;
* Jones reflection operators;
* Brewster rank collapse;
* total-internal-reflection phase retardance;
* metal-mirror dissipative calibration;
* V₄ / PT-sector labels as optical symmetry readouts.

No concrete Fresnel formula is hard-coded here. Angle, refractive index,
complex material response, and branch choices are supplied by later models.
-/

import Mathlib
import InfoGeometry.OperatorAlgebra.TopologicalSnap

noncomputable section

namespace InfoGeometry.Optics.JonesCalibration

/-! ## 1. Optical eigenchannels -/

/--
The two Fresnel eigenchannels for a smooth isotropic interface.
-/
inductive FresnelChannel where
  /-- s-polarization: electric field perpendicular to the plane of incidence. -/
  | s
  /-- p-polarization: electric field parallel to the plane of incidence. -/
  | p
deriving DecidableEq, Repr

/--
A minimal V₄-style PT label.

This is the optical boundary bookkeeping for parity/time flips. It is not yet
a full group implementation; it is the charge-label socket.
-/
structure V4Label where
  parityFlip : Bool
  timeFlip : Bool
deriving DecidableEq, Repr

namespace V4Label

/-- Identity component. -/
def identity : V4Label where
  parityFlip := false
  timeFlip := false

/-- Parity flip. -/
def P : V4Label where
  parityFlip := true
  timeFlip := false

/-- Time flip. -/
def T : V4Label where
  parityFlip := false
  timeFlip := true

/-- PT flip. -/
def PT : V4Label where
  parityFlip := true
  timeFlip := true

end V4Label

/-! ## 2. Polarization projector pair -/

/--
Complementary `s/p` polarization projectors in an operator algebra.

The interface is diagonal in this basis for a smooth isotropic surface.
-/
structure SPProjectorPair
    (Op : Type*) [Ring Op] [Algebra ℂ Op] where
  P_s : Op
  P_p : Op

  P_s_idem :
    P_s * P_s = P_s

  P_p_idem :
    P_p * P_p = P_p

  s_p_disjoint :
    P_s * P_p = 0

  p_s_disjoint :
    P_p * P_s = 0

  sum_eq_one :
    P_s + P_p = 1

namespace SPProjectorPair

variable {Op : Type*} [Ring Op] [Algebra ℂ Op]
variable (P : SPProjectorPair Op)

/--
The `s/p` Cartan readout:

`χ_sp = P_s - P_p`.
-/
def chiSP : Op :=
  P.P_s - P.P_p

/--
The projector associated to a Fresnel channel.
-/
def projectorOf : FresnelChannel → Op
  | FresnelChannel.s => P.P_s
  | FresnelChannel.p => P.P_p

/--
The `s/p` Cartan readout squares to one.
-/
theorem chiSP_sq :
    P.chiSP * P.chiSP = 1 := by
  dsimp [chiSP]
  calc
    (P.P_s - P.P_p) * (P.P_s - P.P_p)
        =
      P.P_s * P.P_s - P.P_s * P.P_p -
        (P.P_p * P.P_s - P.P_p * P.P_p) := by
          rw [sub_mul, mul_sub, mul_sub]
    _ = P.P_s - 0 - (0 - P.P_p) := by
          rw [P.P_s_idem, P.s_p_disjoint, P.p_s_disjoint, P.P_p_idem]
    _ = P.P_s + P.P_p := by
          abel
    _ = 1 := P.sum_eq_one

end SPProjectorPair

/-! ## 3. Jones/Fresnel coefficient data -/

/--
Abstract Fresnel coefficient datum.

The actual Fresnel equations are supplied by later optical models. This layer
only needs the two complex amplitudes plus proof-carrying calibration sockets.
-/
structure FresnelCoefficientDatum where
  r_s : ℂ
  r_p : ℂ

  /-- Law that the coefficients come from the intended optical model. -/
  fresnel_law : Prop

  /-- Evidence that the coefficients come from the intended optical model. -/
  fresnel_certificate :
    fresnel_law

namespace FresnelCoefficientDatum

/--
Brewster condition: the `p` reflected channel vanishes.
-/
def IsBrewster
    (F : FresnelCoefficientDatum) : Prop :=
  F.r_p = 0 ∧ F.r_s ≠ 0

/--
Total internal reflection / lossless retarder condition.

Both amplitudes have unit modulus.
-/
def IsTotalInternalReflection
    (F : FresnelCoefficientDatum) : Prop :=
  ‖F.r_s‖ = 1 ∧ ‖F.r_p‖ = 1

/--
Metal mirror / complex material branch certificate.

This is a socket for a complex refractive-index material model.
-/
structure MetalBranchDatum
    (F : FresnelCoefficientDatum) where
  /-- Law that this coefficient datum is in the metal/material branch. -/
  metal_branch_law : Prop

  /-- Evidence that this coefficient datum is in the metal/material branch. -/
  metal_branch_certificate :
    metal_branch_law

/--
The coefficient datum is calibrated as a metal/material branch.
-/
def IsMetalBranch
    (F : FresnelCoefficientDatum) : Prop :=
  Nonempty (MetalBranchDatum F)

end FresnelCoefficientDatum

/-! ## 4. Operatorial Jones reflector -/

/--
The operatorial Jones reflection datum

`R = r_s P_s + r_p P_p`.
-/
structure JonesReflector
    (Op : Type*) [Ring Op] [Algebra ℂ Op] where
  projectors : SPProjectorPair Op
  coeffs : FresnelCoefficientDatum

namespace JonesReflector

variable {Op : Type*} [Ring Op] [Algebra ℂ Op]
variable (J : JonesReflector Op)

/--
The Jones reflection operator:

`R = r_s P_s + r_p P_p`.
-/
def R : Op :=
  J.coeffs.r_s • J.projectors.P_s +
    J.coeffs.r_p • J.projectors.P_p

/--
The reflector is in the Brewster rank-collapse branch.
-/
def IsBrewsterBranch : Prop :=
  J.coeffs.IsBrewster

/--
The reflector is in the total-internal-reflection retarder branch.
-/
def IsRetarderBranch : Prop :=
  J.coeffs.IsTotalInternalReflection

/--
The reflector is in the metal/absorptive branch.
-/
def IsMetalBranch : Prop :=
  J.coeffs.IsMetalBranch

/--
At Brewster calibration, the Jones reflector collapses to the `s` channel:

`R = r_s • P_s`.
-/
theorem R_eq_smul_Ps_of_brewster
    (hJ : J.IsBrewsterBranch) :
    J.R = J.coeffs.r_s • J.projectors.P_s := by
  dsimp [IsBrewsterBranch, FresnelCoefficientDatum.IsBrewster] at hJ
  rcases hJ with ⟨hrp, _hrs⟩
  dsimp [R]
  rw [hrp]
  simp

/--
At Brewster calibration, the reflector kills the `p` channel.
-/
theorem R_mul_Pp_eq_zero_of_brewster
    (hJ : J.IsBrewsterBranch) :
    J.R * J.projectors.P_p = 0 := by
  rw [J.R_eq_smul_Ps_of_brewster hJ]
  calc
    (J.coeffs.r_s • J.projectors.P_s) * J.projectors.P_p
        = J.coeffs.r_s • (J.projectors.P_s * J.projectors.P_p) := by
            rw [smul_mul_assoc]
    _ = J.coeffs.r_s • 0 := by
            rw [J.projectors.s_p_disjoint]
    _ = 0 := by
            simp

/--
At Brewster calibration, the reflector is supported on the `s` channel.
-/
theorem R_mul_Ps_eq_R_of_brewster
    (hJ : J.IsBrewsterBranch) :
    J.R * J.projectors.P_s = J.R := by
  rw [J.R_eq_smul_Ps_of_brewster hJ]
  calc
    (J.coeffs.r_s • J.projectors.P_s) * J.projectors.P_s
        = J.coeffs.r_s • (J.projectors.P_s * J.projectors.P_s) := by
            rw [smul_mul_assoc]
    _ = J.coeffs.r_s • J.projectors.P_s := by
            rw [J.projectors.P_s_idem]

/--
At Brewster calibration, the `s` projector supports the reflector on the left.
-/
theorem Ps_mul_R_eq_R_of_brewster
    (hJ : J.IsBrewsterBranch) :
    J.projectors.P_s * J.R = J.R := by
  rw [J.R_eq_smul_Ps_of_brewster hJ]
  calc
    J.projectors.P_s * (J.coeffs.r_s • J.projectors.P_s)
        = J.coeffs.r_s • (J.projectors.P_s * J.projectors.P_s) := by
            rw [mul_smul_comm]
    _ = J.coeffs.r_s • J.projectors.P_s := by
            rw [J.projectors.P_s_idem]

/--
At Brewster calibration, the `p` channel has no left contribution either.
-/
theorem Pp_mul_R_eq_zero_of_brewster
    (hJ : J.IsBrewsterBranch) :
    J.projectors.P_p * J.R = 0 := by
  rw [J.R_eq_smul_Ps_of_brewster hJ]
  calc
    J.projectors.P_p * (J.coeffs.r_s • J.projectors.P_s)
        = J.coeffs.r_s • (J.projectors.P_p * J.projectors.P_s) := by
            rw [mul_smul_comm]
    _ = J.coeffs.r_s • 0 := by
            rw [J.projectors.p_s_disjoint]
    _ = 0 := by
            simp

/--
The Brewster core inverse:

`Rᴰ = r_s⁻¹ • P_s`.
-/
def brewsterCoreInverse : Op :=
  J.coeffs.r_s⁻¹ • J.projectors.P_s

/--
Brewster core identity:

`R Rᴰ = P_s`.
-/
theorem R_mul_brewsterCoreInverse_eq_Ps
    (hJ : J.IsBrewsterBranch) :
    J.R * J.brewsterCoreInverse = J.projectors.P_s := by
  dsimp [IsBrewsterBranch, FresnelCoefficientDatum.IsBrewster] at hJ
  rcases hJ with ⟨hrp, hrs⟩
  rw [J.R_eq_smul_Ps_of_brewster ⟨hrp, hrs⟩]
  dsimp [brewsterCoreInverse]
  calc
    (J.coeffs.r_s • J.projectors.P_s) *
        (J.coeffs.r_s⁻¹ • J.projectors.P_s)
        =
      (J.coeffs.r_s * J.coeffs.r_s⁻¹) •
        (J.projectors.P_s * J.projectors.P_s) := by
          rw [smul_mul_assoc, mul_smul_comm, smul_smul]
    _ = 1 • J.projectors.P_s := by
          simp [J.projectors.P_s_idem, mul_inv_cancel₀ hrs]
    _ = J.projectors.P_s := by
          simp

/--
Brewster left core identity:

`Rᴰ R = P_s`.
-/
theorem brewsterCoreInverse_mul_R_eq_Ps
    (hJ : J.IsBrewsterBranch) :
    J.brewsterCoreInverse * J.R = J.projectors.P_s := by
  dsimp [IsBrewsterBranch, FresnelCoefficientDatum.IsBrewster] at hJ
  rcases hJ with ⟨hrp, hrs⟩
  rw [J.R_eq_smul_Ps_of_brewster ⟨hrp, hrs⟩]
  dsimp [brewsterCoreInverse]
  calc
    (J.coeffs.r_s⁻¹ • J.projectors.P_s) *
        (J.coeffs.r_s • J.projectors.P_s)
        =
      (J.coeffs.r_s⁻¹ * J.coeffs.r_s) •
        (J.projectors.P_s * J.projectors.P_s) := by
          rw [smul_mul_assoc, mul_smul_comm, smul_smul]
    _ = 1 • J.projectors.P_s := by
          simp [J.projectors.P_s_idem, inv_mul_cancel₀ hrs]
    _ = J.projectors.P_s := by
          simp

/--
The killed sector is the complement of the Brewster core:

`1 - R Rᴰ = P_p`.
-/
theorem one_sub_R_mul_brewsterCoreInverse_eq_Pp
    (hJ : J.IsBrewsterBranch) :
    1 - J.R * J.brewsterCoreInverse = J.projectors.P_p := by
  rw [J.R_mul_brewsterCoreInverse_eq_Ps hJ]
  have hsum : J.projectors.P_s + J.projectors.P_p = 1 :=
    J.projectors.sum_eq_one
  rw [← hsum]
  abel

/--
The Brewster core inverse kills the `p` channel.
-/
theorem brewsterCoreInverse_mul_Pp_eq_zero :
    J.brewsterCoreInverse * J.projectors.P_p = 0 := by
  dsimp [brewsterCoreInverse]
  calc
    (J.coeffs.r_s⁻¹ • J.projectors.P_s) * J.projectors.P_p
        = J.coeffs.r_s⁻¹ • (J.projectors.P_s * J.projectors.P_p) := by
            rw [smul_mul_assoc]
    _ = J.coeffs.r_s⁻¹ • 0 := by
            rw [J.projectors.s_p_disjoint]
    _ = 0 := by
            simp

end JonesReflector

/-! ## 5. Brewster collapse and Drazin socket -/

/--
Brewster rank-collapse calibration.

At Brewster angle, `r_p = 0`, so the reflected operator is projectively a
scalar multiple of `P_s`. The elementary core/nil support facts are derived as
theorems from `brewster`; only the deeper Drazin inverse interpretation remains
proof-carrying at this generic algebraic level.
-/
structure BrewsterDrazinCalibration
    (Op : Type*) [Ring Op] [Algebra ℂ Op]
    (J : JonesReflector Op) where
  /-- Brewster branch hypothesis. -/
  brewster :
    J.IsBrewsterBranch

  /--
  Drazin interpretation law.

  Intended concrete statement: if `R = r_s P_s` and `r_s ≠ 0`, then
  `Rᴰ = r_s⁻¹ P_s`, `R Rᴰ = P_s`, and `1 - R Rᴰ = P_p`.
  -/
  drazin_rank_collapse_law : Prop

  /-- Evidence for the Drazin rank-collapse law. -/
  drazin_rank_collapse_certificate :
    drazin_rank_collapse_law

namespace BrewsterDrazinCalibration

variable {Op : Type*} [Ring Op] [Algebra ℂ Op]
variable {J : JonesReflector Op}
variable (B : BrewsterDrazinCalibration Op J)

/-- The Brewster reflector is `r_s • P_s`. -/
theorem R_eq_smul_Ps :
    (B : BrewsterDrazinCalibration Op J) →
    J.R = J.coeffs.r_s • J.projectors.P_s :=
  fun B =>
  J.R_eq_smul_Ps_of_brewster (BrewsterDrazinCalibration.brewster B)

/-- The Brewster reflector kills the `p` sector. -/
theorem kills_p :
    (B : BrewsterDrazinCalibration Op J) →
    J.R * J.projectors.P_p = 0 :=
  fun B =>
  J.R_mul_Pp_eq_zero_of_brewster (BrewsterDrazinCalibration.brewster B)

/-- The Brewster reflector is supported on the `s` sector. -/
theorem supported_on_s :
    (B : BrewsterDrazinCalibration Op J) →
    J.R * J.projectors.P_s = J.R :=
  fun B =>
  J.R_mul_Ps_eq_R_of_brewster (BrewsterDrazinCalibration.brewster B)

/-- The `p` sector also has no left contribution. -/
theorem p_left_kills :
    (B : BrewsterDrazinCalibration Op J) →
    J.projectors.P_p * J.R = 0 :=
  fun B =>
  J.Pp_mul_R_eq_zero_of_brewster (BrewsterDrazinCalibration.brewster B)

/-- The `s` sector supports the reflector on the left. -/
theorem s_left_supports :
    (B : BrewsterDrazinCalibration Op J) →
    J.projectors.P_s * J.R = J.R :=
  fun B =>
  J.Ps_mul_R_eq_R_of_brewster (BrewsterDrazinCalibration.brewster B)

/-- The Brewster core identity. -/
theorem core_identity :
    (B : BrewsterDrazinCalibration Op J) →
    J.R * J.brewsterCoreInverse = J.projectors.P_s :=
  fun B =>
  J.R_mul_brewsterCoreInverse_eq_Ps (BrewsterDrazinCalibration.brewster B)

/-- The killed sector is the complementary `p` channel. -/
theorem nil_identity :
    (B : BrewsterDrazinCalibration Op J) →
    1 - J.R * J.brewsterCoreInverse = J.projectors.P_p :=
  fun B =>
  J.one_sub_R_mul_brewsterCoreInverse_eq_Pp (BrewsterDrazinCalibration.brewster B)

/-- The reflected operator is exactly the surviving `s` channel. -/
theorem reflected_eq_s_channel :
    (B : BrewsterDrazinCalibration Op J) →
    J.R = J.coeffs.r_s • J.projectors.P_s :=
  fun B =>
  R_eq_smul_Ps B

/-- The reflected operator kills the `p` channel. -/
theorem kills_p_channel :
    (B : BrewsterDrazinCalibration Op J) →
    J.R * J.projectors.P_p = 0 :=
  fun B =>
  kills_p B

/-- The reflected operator is supported on the `s` channel. -/
theorem supported_on_s_channel :
    (B : BrewsterDrazinCalibration Op J) →
    J.R * J.projectors.P_s = J.R :=
  fun B =>
  supported_on_s B

/-- The Brewster core inverse kills the nil channel. -/
theorem coreInverse_kills_p :
    J.brewsterCoreInverse * J.projectors.P_p = 0 :=
  J.brewsterCoreInverse_mul_Pp_eq_zero

/-- Stored Drazin-rank-collapse interpretation. -/
theorem drazin_rank_collapse_valid :
    B.drazin_rank_collapse_law :=
  BrewsterDrazinCalibration.drazin_rank_collapse_certificate B

end BrewsterDrazinCalibration

/-! ## 6. Metal mirror calibration -/

/--
Metal mirror calibration.

This connects Jones/Fresnel optical data to thermodynamic/Bregman data. It
does not claim that the Bregman Hessian alone determines the refractive index.
That link is a material-model calibration.
-/
structure MetalMirrorJonesCalibration
    (Op : Type*) [Ring Op] [Algebra ℂ Op]
    (J : JonesReflector Op) where
  /-- Reflectivity readout. -/
  reflectivity : Op → ℝ

  /-- Retardance / relative phase readout. -/
  retardance : Op → ℝ

  /-- Ellipticity readout. -/
  ellipticity : Op → ℝ

  /-- Complex refractive-index readout. -/
  refractiveIndex : Op → ℂ

  /-- Law that heat/Bregman readout controls absorption. -/
  heat_controls_absorption_law : Prop

  /-- Evidence that heat/Bregman readout controls absorption. -/
  heat_controls_absorption :
    heat_controls_absorption_law

  /-- Law that Hessian/susceptibility readout controls retardance. -/
  hessian_controls_retardance_law : Prop

  /-- Evidence that Hessian/susceptibility readout controls retardance. -/
  hessian_controls_retardance :
    hessian_controls_retardance_law

  /-- Law that retardance and amplitude imbalance control ellipticity. -/
  retardance_controls_ellipticity_law : Prop

  /-- Evidence that retardance and amplitude imbalance control ellipticity. -/
  retardance_controls_ellipticity :
    retardance_controls_ellipticity_law

  /-- Law that the complex refractive-index model is calibrated. -/
  refractive_index_calibration_law : Prop

  /-- Evidence that the complex refractive-index model is calibrated. -/
  refractive_index_calibrated :
    refractive_index_calibration_law

/-! ## 7. V₄ sector calibration -/

/--
Calibration between V₄/PT labels and optical polarization channels.

This is where the abstract topological-sector bookkeeping is tied to the
observable `s/p` eigenchannels.
-/
structure V4JonesCalibration
    (Op : Type*) [Ring Op] [Algebra ℂ Op]
    (P : SPProjectorPair Op) where
  /-- V₄ label assigned to each Fresnel channel. -/
  labelOfChannel : FresnelChannel → V4Label

  /--
  Operator representative of a V₄ label.

  This is not a claim that the V₄ label is definitionally the optical
  projector. It is a model-specific calibration saying which operator
  represents the label in this optical model.
  -/
  operatorOfLabel : V4Label → Op

  /-- `s` channel calibration certificate. -/
  s_channel_calibrated :
    operatorOfLabel (labelOfChannel FresnelChannel.s) = P.P_s

  /-- `p` channel calibration certificate. -/
  p_channel_calibrated :
    operatorOfLabel (labelOfChannel FresnelChannel.p) = P.P_p

/-! ## 8. Topological snap calibration -/

/--
A Jones-level obstruction flow.

This says that an optical evolution preserves a discrete obstruction charge.
Then `TopologicalSnap` proves that a nontrivial optical sector cannot relax
into a flat/unpolarized sector unless the charge is trivial.
-/
structure JonesObstructionFlow
    (State Charge : Type*) [Zero Charge] where
  obstructionFlow :
    InfoGeometry.OperatorAlgebra.TopologicalSnap.ConservedObstructionFlow
      State Charge

  /-- Law that this is the Jones/optical sector flow. -/
  optical_calibration_law : Prop

  /-- Evidence that this is the Jones/optical sector flow. -/
  optical_calibration :
    optical_calibration_law

namespace JonesObstructionFlow

variable {State Charge : Type*} [Zero Charge]
variable (F : JonesObstructionFlow State Charge)

/--
A nontrivial Jones obstruction cannot flow into the flat optical sector.
-/
theorem nontrivial_cannot_relax_to_flat
    {x : State}
    (hx : F.obstructionFlow.invariant x ≠ 0)
    (t : ℝ) :
    F.obstructionFlow.flow t x ∉ F.obstructionFlow.Flat :=
  F.obstructionFlow.nontrivial_cannot_flow_to_flat hx t

end JonesObstructionFlow

/-! ## 9. Owner targets -/

/--
Owner target for an operatorial Jones calibration.
-/
def JonesCalibrationOwnerTarget
    (Op : Type*) [Ring Op] [Algebra ℂ Op] : Prop :=
  ∃ P : SPProjectorPair Op,
    Nonempty (V4JonesCalibration Op P)

/--
Owner target for a Brewster/Drazin calibration.
-/
def BrewsterDrazinCalibrationOwnerTarget
    (Op : Type*) [Ring Op] [Algebra ℂ Op] : Prop :=
  ∃ J : JonesReflector Op,
    Nonempty (BrewsterDrazinCalibration Op J)

/--
Owner target for a metal-mirror optical calibration.
-/
def MetalMirrorJonesCalibrationOwnerTarget
    (Op : Type*) [Ring Op] [Algebra ℂ Op] : Prop :=
  ∃ J : JonesReflector Op,
    Nonempty (MetalMirrorJonesCalibration Op J)

end InfoGeometry.Optics.JonesCalibration
