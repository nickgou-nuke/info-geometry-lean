/-
InfoGeometry/Thermo/MetalMirror.lean

Thermodynamic realization of a dissipative optical interface.

A metal mirror is modeled as a reduced dissipative reflection branch together
with an ideal lossless comparison branch. The macroscopic heat loss is the
Bregman divergence between the ideal reflected state and the actual reflected
state.

The total information-conserving picture is represented by a
Stinespring-Tomita dilation witness: the apparent loss in the system branch is
routed into a mirrored commutant/environment branch.

The public API is backend-generic and uses bounded real-linear channels. The
Drazin regular positive cone specialization is retained under the `RegularCone`
namespace.
-/

import Mathlib.Tactic
import InfoGeometry.Canonical.OperatorFenchelRegularCone
import InfoGeometry.Geometry.OperatorBregmanDivergence
import InfoGeometry.Krein.DoubledSpace
import InfoGeometry.OperatorAlgebra.PO55RicciFlux
import InfoGeometry.Meta.Architecture

noncomputable section

namespace InfoGeometry.Thermo.MetalMirror

open InfoGeometry.Canonical
open InfoGeometry.Canonical.OperatorFenchelRegularCone
open InfoGeometry.Geometry.OperatorBregmanDivergence
open InfoGeometry.OperatorAlgebra

variable {E : Type 0}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

namespace RegularCone

/-! ## 1. Metal mirror channel -/

/--
A metal mirror channel on the regular positive operator cone.

`actualFlow` is the reflected system branch. It may be dissipative or
trace-nonincreasing when viewed alone.

`idealFlow` is the lossless comparison branch, used as the reversible reference.

Analytic facts such as complete positivity, trace behavior, and optical
realizability belong to concrete channel theorems layered above this datum.
-/
structure MetalMirrorChannel
    (c : CertifiedModularReduction (E := InfoGeometry.Krein.DoubledSpace E)) where
  /-- Actual dissipative reflected branch. -/
  actualFlow : OperatorEnd E →L[ℝ] OperatorEnd E

  /-- Ideal lossless reflected branch for comparison. -/
  idealFlow : OperatorEnd E →L[ℝ] OperatorEnd E

  /-- Actual reflected branch preserves the regular positive cone. -/
  actual_preserves_cone :
    ∀ U : OperatorEnd E,
      U ∈ regularPositiveConeOmegaD c →
        actualFlow U ∈ regularPositiveConeOmegaD c

  /-- Ideal reflected branch preserves the regular positive cone. -/
  ideal_preserves_cone :
    ∀ U : OperatorEnd E,
      U ∈ regularPositiveConeOmegaD c →
        idealFlow U ∈ regularPositiveConeOmegaD c

  /-- The observed reduced branch is dissipative in the operator norm. -/
  actual_norm_nonincreasing :
    ∀ U : OperatorEnd E, ‖actualFlow U‖ ≤ ‖U‖

  /-- The ideal comparison branch is lossless in the operator norm. -/
  ideal_norm_preserving :
    ∀ U : OperatorEnd E, ‖idealFlow U‖ = ‖U‖

namespace MetalMirrorChannel

variable
    {c : CertifiedModularReduction (E := InfoGeometry.Krein.DoubledSpace E)}
    (M : MetalMirrorChannel c)

/-- Actual reflected state as a regular cone point. -/
def actualPoint
    (U : RegularConePoint c) :
    RegularConePoint c :=
  ⟨M.actualFlow U.op, M.actual_preserves_cone U.op U.mem⟩

/-- Ideal reflected state as a regular cone point. -/
def idealPoint
    (U : RegularConePoint c) :
    RegularConePoint c :=
  ⟨M.idealFlow U.op, M.ideal_preserves_cone U.op U.mem⟩

@[simp]
theorem actualPoint_op
    (U : RegularConePoint c) :
    (M.actualPoint U).op = M.actualFlow U.op :=
  rfl

@[simp]
theorem idealPoint_op
    (U : RegularConePoint c) :
    (M.idealPoint U).op = M.idealFlow U.op :=
  rfl

/-- Native dissipative-branch predicate: the reduced channel is contractive. -/
def ActualDissipativeBranch : Prop :=
  ∀ U : OperatorEnd E, ‖M.actualFlow U‖ ≤ ‖U‖

/-- Native lossless-branch predicate: the ideal channel preserves norm. -/
def IdealLosslessBranch : Prop :=
  ∀ U : OperatorEnd E, ‖M.idealFlow U‖ = ‖U‖

/-- The actual branch is dissipative by the channel's contraction law. -/
theorem actual_dissipative_branch :
    M.ActualDissipativeBranch :=
  M.actual_norm_nonincreasing

/-- The comparison branch is lossless by its norm-preservation law. -/
theorem ideal_lossless_branch :
    M.IdealLosslessBranch :=
  M.ideal_norm_preserving

end MetalMirrorChannel

/-! ## 2. Stinespring-Tomita dilation -/

/--
A Stinespring-Tomita dilation witness for a metal mirror.

The conservation equality says that the ideal lossless comparison branch
decomposes into the actual reflected system branch plus a Tomita-mirrored
commutant leak.  Model-specific Tomita/CPT identifications should be stated as
separate theorem hypotheses, not as generic proposition fields here.
-/
structure StinespringTomitaMirrorDilation
    {c : CertifiedModularReduction (E := InfoGeometry.Krein.DoubledSpace E)}
    (M : MetalMirrorChannel c) where
  /-- Tomita/CPT mirror routing system data into the commutant/environment lane. -/
  mirror : OperatorEnd E →L[ℝ] OperatorEnd E

  /-- Leaked/environment branch. -/
  leakFlow : OperatorEnd E →L[ℝ] OperatorEnd E

  /-- Conservation equality: `ideal = actual + mirrored leak`. -/
  conservation_eq :
    ∀ U : OperatorEnd E,
      M.idealFlow U = M.actualFlow U + mirror (leakFlow U)

namespace StinespringTomitaMirrorDilation

variable
    {c : CertifiedModularReduction (E := InfoGeometry.Krein.DoubledSpace E)}
    {M : MetalMirrorChannel c}
    (D : StinespringTomitaMirrorDilation M)

/-- The Stinespring-Tomita conservation equality. -/
theorem conservation
    (U : OperatorEnd E) :
    M.idealFlow U = M.actualFlow U + D.mirror (D.leakFlow U) :=
  D.conservation_eq U

end StinespringTomitaMirrorDilation

/-! ## 3. Macroscopic heat as Bregman shear -/

/--
Macroscopic heat loss of the metal mirror.

This is the Bregman divergence from the ideal lossless reflected state to the
actual dissipative reflected state:

`Heat(U) = D_Φ(ideal(U) || actual(U))`.

The direction matters. This is an oriented thermodynamic readout, not a
symmetric distance.
-/
@[rep_depth thermo]
def macroscopicHeatLoss
    {c : CertifiedModularReduction (E := InfoGeometry.Krein.DoubledSpace E)}
    (M : MetalMirrorChannel c)
    (ω : OperatorEnd E →L[ℝ] ℝ)
    (gradPhi : OperatorEnd E → OperatorEnd E →L[ℝ] ℝ)
    (U : RegularConePoint c) : ℝ :=
  operatorBregmanDivergence ω gradPhi (M.idealPoint U) (M.actualPoint U)

/--
Reverse Bregman work: the divergence from actual to ideal.

This is generally different from `macroscopicHeatLoss`.
-/
@[rep_depth thermo]
def recoveryWork
    {c : CertifiedModularReduction (E := InfoGeometry.Krein.DoubledSpace E)}
    (M : MetalMirrorChannel c)
    (ω : OperatorEnd E →L[ℝ] ℝ)
    (gradPhi : OperatorEnd E → OperatorEnd E →L[ℝ] ℝ)
    (U : RegularConePoint c) : ℝ :=
  operatorBregmanDivergence ω gradPhi (M.actualPoint U) (M.idealPoint U)

/-- Thermodynamic arrow/skew of the mirror channel. -/
@[rep_depth thermo]
def mirrorBregmanSkew
    {c : CertifiedModularReduction (E := InfoGeometry.Krein.DoubledSpace E)}
    (M : MetalMirrorChannel c)
    (ω : OperatorEnd E →L[ℝ] ℝ)
    (gradPhi : OperatorEnd E → OperatorEnd E →L[ℝ] ℝ)
    (U : RegularConePoint c) : ℝ :=
  macroscopicHeatLoss M ω gradPhi U - recoveryWork M ω gradPhi U

/--
Heat loss is nonnegative once the regular-cone Bregman convexity datum is
supplied.
-/
@[rep_depth thermo]
theorem macroscopicHeatLoss_nonneg
    {c : CertifiedModularReduction (E := InfoGeometry.Krein.DoubledSpace E)}
    {ω : OperatorEnd E →L[ℝ] ℝ}
    {gradPhi : OperatorEnd E → OperatorEnd E →L[ℝ] ℝ}
    (M : MetalMirrorChannel c)
    (C : OperatorBregmanConvexityDatum c ω gradPhi)
    (U : RegularConePoint c) :
    0 ≤ macroscopicHeatLoss M ω gradPhi U :=
  OperatorBregmanConvexityDatum.nonneg C (M.idealPoint U) (M.actualPoint U)

/--
If the actual and ideal reflected branches agree on `U`, the heat loss
vanishes.
-/
@[rep_depth thermo]
theorem macroscopicHeatLoss_zero_of_actual_eq_ideal
    {c : CertifiedModularReduction (E := InfoGeometry.Krein.DoubledSpace E)}
    (M : MetalMirrorChannel c)
    (ω : OperatorEnd E →L[ℝ] ℝ)
    (gradPhi : OperatorEnd E → OperatorEnd E →L[ℝ] ℝ)
    (U : RegularConePoint c)
    (hU : M.actualFlow U.op = M.idealFlow U.op) :
    macroscopicHeatLoss M ω gradPhi U = 0 := by
  dsimp [
    macroscopicHeatLoss,
    MetalMirrorChannel.actualPoint,
    MetalMirrorChannel.idealPoint,
    operatorBregmanDivergence
  ]
  rw [← hU]
  simp

/-! ## 4. Ricci flux bridge -/

/--
A metal mirror Ricci-flux bridge.

This datum does not assert that every metal mirror automatically realizes a
given TKK Ricci flux.  For each installed instance, the proof of the bridge is
exactly the `heat_eq_ricci_flux` field below; concrete geometry modules must
supply that equality theorem when constructing the instance.
-/
structure MetalMirrorRicciFluxBridge
    {c : CertifiedModularReduction (E := InfoGeometry.Krein.DoubledSpace E)}
    {ω : OperatorEnd E →L[ℝ] ℝ}
    {gradPhi : OperatorEnd E → OperatorEnd E →L[ℝ] ℝ}
    {F : ModularRegularConeFlow c}
    {D2 : SecondVariationAtZero}
    {J L Obs : Type*}
    [AddCommGroup J] [Module ℝ J]
    [AddCommGroup L] [Module ℝ L]
    [AddCommGroup Obs] [Module ℝ Obs]
    {T : TKKLieClosure J L}
    {R : RicciFluxReadout J L Obs T}
    (M : MetalMirrorChannel c)
    (B : BregmanRicciFluxBridge c ω gradPhi F D2 J L Obs T R) where
  /-- Left/source generator extracted from a regular cone input. -/
  sourceLeft : RegularConePoint c → J

  /-- Right/source generator extracted from a regular cone input. -/
  sourceRight : RegularConePoint c → J

  /-- Heat equals the scalar Ricci-flux readout for the assigned generators. -/
  heat_eq_ricci_flux :
    ∀ U : RegularConePoint c,
      macroscopicHeatLoss M ω gradPhi U =
        R.flux (sourceLeft U) (sourceRight U)

namespace MetalMirrorRicciFluxBridge

variable
    {c : CertifiedModularReduction (E := InfoGeometry.Krein.DoubledSpace E)}
    {ω : OperatorEnd E →L[ℝ] ℝ}
    {gradPhi : OperatorEnd E → OperatorEnd E →L[ℝ] ℝ}
    {F : ModularRegularConeFlow c}
    {D2 : SecondVariationAtZero}
    {J L Obs : Type*}
    [AddCommGroup J] [Module ℝ J]
    [AddCommGroup L] [Module ℝ L]
    [AddCommGroup Obs] [Module ℝ Obs]
    {T : TKKLieClosure J L}
    {R : RicciFluxReadout J L Obs T}
    {M : MetalMirrorChannel c}
    {B : BregmanRicciFluxBridge c ω gradPhi F D2 J L Obs T R}
    (X : MetalMirrorRicciFluxBridge M B)

/-- Re-export the heat/Ricci-flux bridge law. -/
theorem heat_eq_flux
    (U : RegularConePoint c) :
    macroscopicHeatLoss M ω gradPhi U =
      R.flux (X.sourceLeft U) (X.sourceRight U) :=
  X.heat_eq_ricci_flux U

end MetalMirrorRicciFluxBridge

end RegularCone

/-! ## 6. Backend-generic metal mirror witness layer -/

/-! ### Regular cone and Bregman backend -/

/-- A regular cone/domain on which the thermodynamic potential is valid. -/
abbrev RegularConeDatum (Op : Type*) := Set Op

/-- Compatibility accessor for the underlying regular cone/domain. -/
abbrev RegularConeDatum.cone (Ω : RegularConeDatum Op) : Set Op := Ω

/-- A point of a regular cone. -/
abbrev RegularConePoint
    {Op : Type*}
    (Ω : RegularConeDatum Op) :=
  {op : Op // op ∈ Ω.cone}

namespace RegularConePoint

variable {Op : Type*} {Ω : RegularConeDatum Op}

/-- Compatibility accessor for the underlying cone point. -/
abbrev op (U : RegularConePoint Ω) : Op := U.1

/-- Compatibility accessor for cone membership. -/
abbrev mem (U : RegularConePoint Ω) : U.op ∈ Ω.cone := U.2

/-- Coercion to the underlying operator/state. -/
instance : CoeOut (RegularConePoint Ω) Op where
  coe U := U.1

@[simp]
theorem coe_mk
    (x : Op)
    (hx : x ∈ Ω.cone) :
    ((⟨x, hx⟩ : RegularConePoint Ω) : Op) = x :=
  rfl

end RegularConePoint

/--
A Bregman divergence backend on a regular cone.

`div ideal actual` is the thermodynamic shear between the ideal lossless state
and the actual dissipative state.

The divergence may be total as a function, but its geometric guarantees are
only asserted on the regular cone.
-/
structure BregmanDivergenceDatum
    (Op : Type*)
    (Ω : RegularConeDatum Op) where
  div : Op → Op → ℝ

  nonneg_on_cone :
    ∀ {x y : Op},
      x ∈ Ω.cone →
      y ∈ Ω.cone →
        0 ≤ div x y

  self_eq_zero_on_cone :
    ∀ {x : Op},
      x ∈ Ω.cone →
        div x x = 0

/-! ### Metal mirror channel -/

/--
A metal mirror channel.

`actualFlow` is the dissipative observed channel.

`idealUnitary` is the lossless reference channel.

Both are required to preserve the chosen regular cone.
-/
structure MetalMirrorChannel
    (Op : Type*) [NormedAddCommGroup Op] [NormedSpace ℝ Op]
    (Ω : RegularConeDatum Op) where
  actualFlow : Op →L[ℝ] Op
  idealUnitary : Op →L[ℝ] Op

  actual_preserves_cone :
    ∀ U : Op,
      U ∈ Ω.cone →
        actualFlow U ∈ Ω.cone

  ideal_preserves_cone :
    ∀ U : Op,
      U ∈ Ω.cone →
        idealUnitary U ∈ Ω.cone

  /-- The observed reduced branch is contractive in the carrier norm. -/
  actual_norm_nonincreasing :
    ∀ U : Op, ‖actualFlow U‖ ≤ ‖U‖

  /-- The ideal reference branch preserves the carrier norm. -/
  ideal_norm_preserving :
    ∀ U : Op, ‖idealUnitary U‖ = ‖U‖

namespace MetalMirrorChannel

variable
    {Op : Type*} [NormedAddCommGroup Op] [NormedSpace ℝ Op]
    {Ω : RegularConeDatum Op}
    (M : MetalMirrorChannel Op Ω)

/-- Actual reflected state as a regular cone point. -/
def actualPoint
    (U : RegularConePoint Ω) :
    RegularConePoint Ω :=
  ⟨M.actualFlow U.op, M.actual_preserves_cone U.op U.mem⟩

/-- Ideal reflected state as a regular cone point. -/
def idealPoint
    (U : RegularConePoint Ω) :
    RegularConePoint Ω :=
  ⟨M.idealUnitary U.op, M.ideal_preserves_cone U.op U.mem⟩

/-- Native dissipative-branch predicate for the backend-generic channel. -/
def ActualDissipativeBranch : Prop :=
  ∀ U : Op, ‖M.actualFlow U‖ ≤ ‖U‖

/-- Native lossless-branch predicate for the backend-generic reference. -/
def IdealLosslessBranch : Prop :=
  ∀ U : Op, ‖M.idealUnitary U‖ = ‖U‖

/-- The actual branch is dissipative by its contraction law. -/
theorem actual_dissipative_branch :
    M.ActualDissipativeBranch :=
  M.actual_norm_nonincreasing

/-- The ideal branch is lossless by its norm-preservation law. -/
theorem ideal_lossless_branch :
    M.IdealLosslessBranch :=
  M.ideal_norm_preserving

end MetalMirrorChannel

/-! ### Stinespring/Tomita dilation -/

/--
Stinespring/Tomita dilation witness for the mirror.

The conservation law says that the ideal lossless channel decomposes into the
observed dissipative channel plus a mirrored environment/commutant component.
-/
structure StinespringMirrorDilation
    (Op : Type*) [NormedAddCommGroup Op] [NormedSpace ℝ Op]
    {Ω : RegularConeDatum Op}
    (M : MetalMirrorChannel Op Ω) where
  mirror : Op →L[ℝ] Op
  commutantFlow : Op →L[ℝ] Op

  conservation_eq :
    ∀ U : Op,
      M.idealUnitary U = M.actualFlow U + mirror (commutantFlow U)

namespace StinespringMirrorDilation

variable
    {Op : Type*} [NormedAddCommGroup Op] [NormedSpace ℝ Op]
    {Ω : RegularConeDatum Op}
    {M : MetalMirrorChannel Op Ω}

/-- The dissipative deficit is exactly the mirrored commutant/environment flow. -/
theorem ideal_sub_actual_eq_mirror_commutant
    (D : StinespringMirrorDilation Op M)
    (U : Op) :
    M.idealUnitary U - M.actualFlow U =
      D.mirror (D.commutantFlow U) := by
  have h := D.conservation_eq U
  rw [h]
  abel

end StinespringMirrorDilation

/-! ### Heat loss as Bregman shear -/

/-- Macroscopic heat loss as Bregman divergence:

`Heat(U) = DΦ(idealFlow U, actualFlow U)`.
-/
def macroscopicHeatLoss
    {Op : Type*} [NormedAddCommGroup Op] [NormedSpace ℝ Op]
    {Ω : RegularConeDatum Op}
    (B : BregmanDivergenceDatum Op Ω)
    (M : MetalMirrorChannel Op Ω)
    (U : RegularConePoint Ω) : ℝ :=
  B.div (M.idealPoint U).op (M.actualPoint U).op

/-- Reverse Bregman work: the divergence from actual to ideal. -/
def recoveryWork
    {Op : Type*} [NormedAddCommGroup Op] [NormedSpace ℝ Op]
    {Ω : RegularConeDatum Op}
    (B : BregmanDivergenceDatum Op Ω)
    (M : MetalMirrorChannel Op Ω)
    (U : RegularConePoint Ω) : ℝ :=
  B.div (M.actualPoint U).op (M.idealPoint U).op

/-- Thermodynamic arrow/skew of the mirror channel. -/
def mirrorBregmanSkew
    {Op : Type*} [NormedAddCommGroup Op] [NormedSpace ℝ Op]
    {Ω : RegularConeDatum Op}
    (B : BregmanDivergenceDatum Op Ω)
    (M : MetalMirrorChannel Op Ω)
    (U : RegularConePoint Ω) : ℝ :=
  macroscopicHeatLoss B M U - recoveryWork B M U

/-- Heat loss is nonnegative. -/
theorem macroscopicHeatLoss_nonneg
    {Op : Type*} [NormedAddCommGroup Op] [NormedSpace ℝ Op]
    {Ω : RegularConeDatum Op}
    (B : BregmanDivergenceDatum Op Ω)
    (M : MetalMirrorChannel Op Ω)
    (U : RegularConePoint Ω) :
    0 ≤ macroscopicHeatLoss B M U :=
  B.nonneg_on_cone
    (M.idealPoint U).mem
    (M.actualPoint U).mem

/-- If actual flow agrees with ideal flow at `U`, the Bregman heat loss vanishes. -/
theorem macroscopicHeatLoss_eq_zero_of_actual_eq_ideal
    {Op : Type*} [NormedAddCommGroup Op] [NormedSpace ℝ Op]
    {Ω : RegularConeDatum Op}
    (B : BregmanDivergenceDatum Op Ω)
    (M : MetalMirrorChannel Op Ω)
    (U : RegularConePoint Ω)
    (h : M.actualFlow U.op = M.idealUnitary U.op) :
    macroscopicHeatLoss B M U = 0 := by
  dsimp [macroscopicHeatLoss, MetalMirrorChannel.actualPoint,
    MetalMirrorChannel.idealPoint]
  rw [h]
  exact B.self_eq_zero_on_cone (M.ideal_preserves_cone U.op U.mem)

/-! ### Ricci-flux bridge -/

/--
Ricci/Bregman flux readout.

This is intentionally abstract. Concrete geometry modules can instantiate it
from a Hessian, curvature operator, Ricci tensor, or TKK flux bridge.
-/
abbrev RicciFluxReadout (Op : Type*) := Op → ℝ

namespace RicciFluxReadout

abbrev flux {Op : Type*} (R : RicciFluxReadout Op) : Op → ℝ := R

end RicciFluxReadout

/--
Bridge saying that the metal-mirror Bregman heat equals the Ricci flux readout.
-/
structure MetalMirrorHeatRicciFluxBridge
    (Op : Type*) [NormedAddCommGroup Op] [NormedSpace ℝ Op]
    {Ω : RegularConeDatum Op}
    (B : BregmanDivergenceDatum Op Ω)
    (M : MetalMirrorChannel Op Ω)
    (R : RicciFluxReadout Op) where
  heat_eq_flux :
    ∀ U : RegularConePoint Ω,
      macroscopicHeatLoss B M U = R.flux U.op

namespace MetalMirrorHeatRicciFluxBridge

variable
    {Op : Type*} [NormedAddCommGroup Op] [NormedSpace ℝ Op]
    {Ω : RegularConeDatum Op}
    {B : BregmanDivergenceDatum Op Ω}
    {M : MetalMirrorChannel Op Ω}
    {R : RicciFluxReadout Op}

/-- Heat equals Ricci flux once the bridge datum is supplied. -/
theorem heat_is_ricci_flux
    (W : MetalMirrorHeatRicciFluxBridge Op B M R)
    (U : RegularConePoint Ω) :
    macroscopicHeatLoss B M U = R.flux U.op :=
  W.heat_eq_flux U

end MetalMirrorHeatRicciFluxBridge

/-! ### Optical calibration readouts -/

/--
Optical readouts for a metal mirror.

Equations connecting thermodynamic shear to measured reflectivity, retardance,
ellipticity, or refractive index belong to concrete optical material theorems.
-/
structure MetalMirrorOpticalCalibration
    (Op : Type*) where
  reflectivity : Op → ℝ
  retardance : Op → ℝ
  ellipticity : Op → ℝ
  refractiveIndexReadout : Op → ℂ

/-! ### Admissibility package -/

/--
Thermodynamic readout package for a metal mirror.

This records the scalar heat flux as the Bregman heat loss of a concrete
channel/backend pair.
-/
structure MetalMirrorThermoReadout
    (Op : Type*) [NormedAddCommGroup Op] [NormedSpace ℝ Op] where
  Ω : RegularConeDatum Op
  bregman : BregmanDivergenceDatum Op Ω
  channel : MetalMirrorChannel Op Ω
  heatFlux : RegularConePoint Ω → ℝ
  heatFlux_eq :
    ∀ U : RegularConePoint Ω,
      heatFlux U = macroscopicHeatLoss bregman channel U

namespace MetalMirrorThermoReadout

variable
    {Op : Type*} [NormedAddCommGroup Op] [NormedSpace ℝ Op]
    (R : MetalMirrorThermoReadout Op)

/-- Heat flux is nonnegative. -/
theorem heatFlux_nonneg
    (U : RegularConePoint R.Ω) :
    0 ≤ R.heatFlux U := by
  rw [R.heatFlux_eq U]
  exact macroscopicHeatLoss_nonneg R.bregman R.channel U

end MetalMirrorThermoReadout

/--
Admissibility package for constructing a calibrated metal-mirror heat/flux
bridge.
-/
structure MetalMirrorRicciFluxAdmissible
    (Op : Type*) [NormedAddCommGroup Op] [NormedSpace ℝ Op] where
  readout : MetalMirrorThermoReadout Op
  ricciFlux : Op → ℝ

  heat_eq_ricciFlux :
    ∀ U : RegularConePoint readout.Ω,
      readout.heatFlux U = ricciFlux U.op

/-- A calibrated Ricci-flux bridge from admissible data. -/
theorem metalMirrorRicciFluxBridge_of_admissible
    {Op : Type*} [NormedAddCommGroup Op] [NormedSpace ℝ Op]
    (h : MetalMirrorRicciFluxAdmissible Op) :
    MetalMirrorHeatRicciFluxBridge
      Op h.readout.bregman h.readout.channel
        h.ricciFlux := by
  refine {
    heat_eq_flux := ?_
  }
  intro U
  change macroscopicHeatLoss h.readout.bregman h.readout.channel U =
    h.ricciFlux U.op
  rw [← h.heat_eq_ricciFlux U]
  exact (h.readout.heatFlux_eq U).symm

end InfoGeometry.Thermo.MetalMirror
