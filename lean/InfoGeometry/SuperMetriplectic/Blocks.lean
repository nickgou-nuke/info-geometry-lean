import InfoGeometry.SuperMetriplectic.Axioms
import InfoGeometry.Canonical.AssociativeSuperBracket

/-!
# Supergraded Metriplectic Block Packets

Block-level algebraic packets for the matrix language used in the
supergraded/TKK formulation.  The file keeps the claims conservative:
reciprocity, cocycle corrections, Weyl scaling, and Hestenes/chiral-cone cross
response are represented by proof-carrying structures rather than by new
analytic existence theorems.
-/

namespace InfoGeometry.SuperMetriplectic

open InfoGeometry.Canonical.AssociativeSuperBracket

/-- The three TKK lanes `g_-`, `g_0`, and `g_+`. -/
inductive TKKGrade where
  | minus
  | zero
  | plus
deriving DecidableEq, Repr

namespace TKKGrade

/-- Sign-reversing grade involution on the outer TKK lanes. -/
def dual : TKKGrade → TKKGrade
  | .minus => .plus
  | .zero => .zero
  | .plus => .minus

@[simp] theorem dual_dual (g : TKKGrade) : dual (dual g) = g := by
  cases g <;> rfl

end TKKGrade

/--
Scalar shadow of a `3 × 3` TKK Onsager block matrix.

The entries are real body-level response coefficients.  Graded signs and
nilpotent parts should be carried by richer downstream models; this scalar
packet records the observable reciprocal block data.
-/
structure TKKOnsagerMatrix where
  entry : TKKGrade → TKKGrade → ℝ
  reciprocal : ∀ i j, entry i j = entry j i

namespace TKKOnsagerMatrix

/-- Public matrix entry notation as a definition. -/
abbrev L (M : TKKOnsagerMatrix) (i j : TKKGrade) : ℝ :=
  M.entry i j

/-- Onsager reciprocity for any two TKK lanes. -/
theorem reciprocal_entry (M : TKKOnsagerMatrix) (i j : TKKGrade) :
    M.L i j = M.L j i :=
  M.reciprocal i j

/-- The mixed `g_+ / g_-` response block is reciprocal. -/
theorem plus_minus_reciprocal (M : TKKOnsagerMatrix) :
    M.L TKKGrade.plus TKKGrade.minus =
      M.L TKKGrade.minus TKKGrade.plus :=
  M.reciprocal _ _

end TKKOnsagerMatrix

/--
Cocycle-modified Hessian entry.

This is the scalar packet for the formula
`L_ab = Cov_ab + theta_ab`; it does not assert that `theta` satisfies the full
Chevalley-Eilenberg cocycle identity.
-/
structure CocycleModifiedHessianEntry where
  covariance : ℝ
  souriauCocycle : ℝ
  hessianEntry : ℝ
  hessian_eq_covariance_add_cocycle :
    hessianEntry = covariance + souriauCocycle

namespace CocycleModifiedHessianEntry

/-- Public cocycle-modified Hessian equation. -/
theorem hessian_eq (H : CocycleModifiedHessianEntry) :
    H.hessianEntry = H.covariance + H.souriauCocycle :=
  H.hessian_eq_covariance_add_cocycle

end CocycleModifiedHessianEntry

/--
Weyl scaling packet for a scalar Onsager block.

`factor` is the already-computed positive or signed Weyl scale in the chosen
model.  This layer only records covariance of the block coefficient under that
scale.
-/
structure WeylScaledOnsagerEntry where
  oldEntry : ℝ
  newEntry : ℝ
  factor : ℝ
  new_eq_factor_mul_old : newEntry = factor * oldEntry

namespace WeylScaledOnsagerEntry

/-- Public Weyl scaling equation for a scalar response entry. -/
theorem new_eq (W : WeylScaledOnsagerEntry) :
    W.newEntry = W.factor * W.oldEntry :=
  W.new_eq_factor_mul_old

end WeylScaledOnsagerEntry

/--
Hestenes/chiral-cone cross response packet.

`Pmu` represents one emergent translation/energy-momentum generator.  The
charge lane is not an external `U(1)` summand: `chargeGenerator` is carried as
the sum of a geometric Hestenes rotation and a real boost, and the packet
requires that this generator is closed in the chiral-cone algebra.

If the emergent translation commutes with this internal rot-boost charge, the
reversible Lie contribution to the cross Onsager coefficient is explicitly
zero, so the total cross response reduces to the thermodynamic covariance lane.
-/
structure HestenesChiralConeCrossResponse
    (A : Type*) [Ring A] [Algebra ℝ A] where
  Pmu : A
  hestenesRotation : A
  realBoost : A
  chargeGenerator : A
  beta : A
  moment : A
  covariance : ℝ
  lieContribution : ℝ
  totalOnsager : ℝ
  inChiralCone : A → Prop
  charge_eq_rotation_add_boost :
    chargeGenerator = hestenesRotation + realBoost
  charge_mem_chiralCone :
    inChiralCone chargeGenerator
  p_charge_commute : commutator Pmu chargeGenerator = 0
  lieContribution_eq_zero_of_commute :
    commutator Pmu chargeGenerator = 0 → lieContribution = 0
  total_eq_lie_plus_covariance :
    totalOnsager = lieContribution + covariance

namespace HestenesChiralConeCrossResponse

variable {A : Type*} [Ring A] [Algebra ℝ A]

/-- The charge lane is the Hestenes rotation combined with the real boost. -/
theorem charge_eq_rotBoost (R : HestenesChiralConeCrossResponse A) :
    R.chargeGenerator = R.hestenesRotation + R.realBoost :=
  R.charge_eq_rotation_add_boost

/-- The rot-boost charge generator is closed in the chiral-cone algebra. -/
theorem charge_closed_in_chiralCone (R : HestenesChiralConeCrossResponse A) :
    R.inChiralCone R.chargeGenerator :=
  R.charge_mem_chiralCone

/--
If translation and Hestenes rot-boost charge commute, the cross response is
purely thermodynamic/covariance-level in this packet.
-/
theorem totalOnsager_eq_covariance (R : HestenesChiralConeCrossResponse A) :
    R.totalOnsager = R.covariance := by
  rw [R.total_eq_lie_plus_covariance]
  rw [R.lieContribution_eq_zero_of_commute R.p_charge_commute]
  simp

end HestenesChiralConeCrossResponse

/--
Conformal `SO(4,2)`-style Onsager block packet.

This is the conservative scalar/body-level packet for the `P/K/D/M` sector:

* `Pmu` is an emergent translation lane;
* `Kmu` is the special-conformal lane;
* `D` is the Weyl/dilation lane;
* `Mmunu` is the Lorentz/spin lane paired with this `(μ,ν)` block.

The conformal bracket relation is carried as data in the convention
`[P,K] = 2ηD - 2M`.  The reversible contribution is therefore not inferred from
a concrete representation; it is tied to the supplied dilation and Lorentz
moment readouts by an explicit field.
-/
structure ConformalOnsagerBlock
    (A : Type*) [Ring A] [Algebra ℝ A] where
  Pmu : A
  Kmu : A
  D : A
  Mmunu : A
  covariancePK : ℝ
  souriauCocyclePK : ℝ
  reversiblePK : ℝ
  totalPK : ℝ
  dilationMoment : ℝ
  lorentzMoment : ℝ
  eta : ℝ
  weylWeightP : ℝ
  weylWeightK : ℝ
  bracket_P_K_eq :
    commutator Pmu Kmu = (2 : ℝ) • (eta • D - Mmunu)
  reversiblePK_eq_dilation_lorentz_moment :
    reversiblePK = (2 : ℝ) * (eta * dilationMoment - lorentzMoment)
  totalPK_eq_reversible_plus_covariance_plus_cocycle :
    totalPK = reversiblePK + covariancePK + souriauCocyclePK

namespace ConformalOnsagerBlock

variable {A : Type*} [Ring A] [Algebra ℝ A]

/-- Public conformal bracket equation `[P,K] = 2ηD - 2M`. -/
theorem bracket_eq (C : ConformalOnsagerBlock A) :
    commutator C.Pmu C.Kmu = (2 : ℝ) • (C.eta • C.D - C.Mmunu) :=
  C.bracket_P_K_eq

/--
The reversible `P/K` response is the dilation-plus-Lorentz moment readout
carried by the conformal bracket lane.
-/
theorem reversiblePK_eq (C : ConformalOnsagerBlock A) :
    C.reversiblePK = (2 : ℝ) * (C.eta * C.dilationMoment - C.lorentzMoment) :=
  C.reversiblePK_eq_dilation_lorentz_moment

/-- The full `P/K` Onsager block splits into reversible, covariance, and cocycle parts. -/
theorem totalPK_eq (C : ConformalOnsagerBlock A) :
    C.totalPK = C.reversiblePK + C.covariancePK + C.souriauCocyclePK :=
  C.totalPK_eq_reversible_plus_covariance_plus_cocycle

/--
Expanded conformal `P/K` block:
`L_PK = 2(η<D> - <M>) + Cov(P,K) + θ(P,K)`.
-/
theorem totalPK_eq_expanded (C : ConformalOnsagerBlock A) :
    C.totalPK =
      (2 : ℝ) * (C.eta * C.dilationMoment - C.lorentzMoment)
        + C.covariancePK + C.souriauCocyclePK := by
  rw [C.totalPK_eq, C.reversiblePK_eq]

/-- Weyl weights of the `P/K` block add at scalar body level. -/
def totalWeylWeightPK (C : ConformalOnsagerBlock A) : ℝ :=
  C.weylWeightP + C.weylWeightK

end ConformalOnsagerBlock

/--
Explicit conformal metriplectic split for the `P/K` Onsager block.

This separates the reversible bracket-driven response from the dissipative
Hessian response.  The dissipative lane is the covariance plus Souriau-cocycle
contribution; the total lane is the sum of reversible and dissipative parts.
-/
structure ConformalPKMetriplecticSplit where
  reversiblePK : ℝ
  covariancePK : ℝ
  souriauCocyclePK : ℝ
  dissipativePK : ℝ
  totalPK : ℝ
  dissipativePK_eq_covariance_plus_cocycle :
    dissipativePK = covariancePK + souriauCocyclePK
  totalPK_eq_reversible_plus_dissipative :
    totalPK = reversiblePK + dissipativePK

namespace ConformalPKMetriplecticSplit

/-- The dissipative `P/K` block is covariance plus the conformal anomaly cocycle. -/
theorem dissipativePK_eq (S : ConformalPKMetriplecticSplit) :
    S.dissipativePK = S.covariancePK + S.souriauCocyclePK :=
  S.dissipativePK_eq_covariance_plus_cocycle

/-- The total `P/K` block is reversible plus dissipative response. -/
theorem totalPK_eq (S : ConformalPKMetriplecticSplit) :
    S.totalPK = S.reversiblePK + S.dissipativePK :=
  S.totalPK_eq_reversible_plus_dissipative

/-- Expanded split: `L_PK = L_rev + Cov(P,K) + θ(P,K)`. -/
theorem totalPK_eq_reversible_plus_covariance_plus_cocycle
    (S : ConformalPKMetriplecticSplit) :
    S.totalPK = S.reversiblePK + S.covariancePK + S.souriauCocyclePK := by
  rw [S.totalPK_eq, S.dissipativePK_eq]
  ring

/-- If covariance and cocycle vanish, the dissipative `P/K` channel vanishes. -/
theorem dissipativePK_eq_zero_of_covariance_cocycle_zero
    (S : ConformalPKMetriplecticSplit)
    (hCov : S.covariancePK = 0)
    (hCocycle : S.souriauCocyclePK = 0) :
    S.dissipativePK = 0 := by
  rw [S.dissipativePK_eq, hCov, hCocycle]
  ring

end ConformalPKMetriplecticSplit

/--
Conformal anomaly/bulk-viscosity packet.

The packet records the conservative implication used by the hydrodynamic
reading: a vanishing conformal trace/anomaly disables the bulk-viscous scalar
channel, while a nonzero channel is kept as explicit data rather than derived.
-/
structure ConformalBulkViscosityPacket where
  traceStress : ℝ
  bulkViscosity : ℝ
  conformalAnomaly : ℝ
  trace_eq_anomaly : traceStress = conformalAnomaly
  bulkViscosity_eq_zero_of_trace_zero :
    traceStress = 0 → bulkViscosity = 0

namespace ConformalBulkViscosityPacket

/-- Exact conformal trace/anomaly readout carried by the packet. -/
theorem trace_eq (C : ConformalBulkViscosityPacket) :
    C.traceStress = C.conformalAnomaly :=
  C.trace_eq_anomaly

/-- If the conformal trace vanishes, the scalar bulk-viscosity channel vanishes. -/
theorem bulkViscosity_eq_zero_of_conformal_trace_zero
    (C : ConformalBulkViscosityPacket)
    (hTrace : C.traceStress = 0) :
    C.bulkViscosity = 0 :=
  C.bulkViscosity_eq_zero_of_trace_zero hTrace

/-- If the anomaly vanishes, the scalar bulk-viscosity channel vanishes. -/
theorem bulkViscosity_eq_zero_of_anomaly_zero
    (C : ConformalBulkViscosityPacket)
    (hAnomaly : C.conformalAnomaly = 0) :
    C.bulkViscosity = 0 := by
  apply C.bulkViscosity_eq_zero_of_trace_zero
  rw [C.trace_eq_anomaly, hAnomaly]

end ConformalBulkViscosityPacket

/--
Perfect-CFT gate for conformal dissipative blocks.

This packet records the intended formal statement without deriving analytic
vanishing from first principles: once the trace/anomaly vanishes, the supplied
model must prove that the dilation and conformal cross dissipative channels
vanish.
-/
structure PerfectCFTDissipationGate where
  traceStress : ℝ
  conformalAnomaly : ℝ
  LDD : ℝ
  LPD : ℝ
  LPKdiss : ℝ
  trace_eq_anomaly : traceStress = conformalAnomaly
  dissipative_blocks_vanish_of_trace_zero :
    traceStress = 0 → LDD = 0 ∧ LPD = 0 ∧ LPKdiss = 0

namespace PerfectCFTDissipationGate

/-- A zero conformal trace disables the `D/D`, `P/D`, and dissipative `P/K` blocks. -/
theorem blocks_vanish_of_trace_zero
    (G : PerfectCFTDissipationGate)
    (hTrace : G.traceStress = 0) :
    G.LDD = 0 ∧ G.LPD = 0 ∧ G.LPKdiss = 0 :=
  G.dissipative_blocks_vanish_of_trace_zero hTrace

/-- A zero conformal anomaly disables the same dissipative blocks. -/
theorem blocks_vanish_of_anomaly_zero
    (G : PerfectCFTDissipationGate)
    (hAnomaly : G.conformalAnomaly = 0) :
    G.LDD = 0 ∧ G.LPD = 0 ∧ G.LPKdiss = 0 := by
  apply G.blocks_vanish_of_trace_zero
  rw [G.trace_eq_anomaly, hAnomaly]

end PerfectCFTDissipationGate

end InfoGeometry.SuperMetriplectic
