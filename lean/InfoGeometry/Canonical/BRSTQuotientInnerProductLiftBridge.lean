import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import InfoGeometry.Canonical.ExteriorContractionCARBridge
import InfoGeometry.Canonical.DiracKahlerLaplacianOperatorBridge
import InfoGeometry.Canonical.DeRhamCohomologyQuotientBridge
import InfoGeometry.Canonical.BRSTCohomologyPhysicalGaugeBridge
import InfoGeometry.Canonical.BRSTExactClassZeroBridge
import InfoGeometry.Canonical.PhysicalGhostZeroBRSTCohomologyBridge
import InfoGeometry.Canonical.KreinSpaceBRSTUnitarityBridge
import InfoGeometry.Canonical.BRSTQuotientPairingWellDefinedBridge
import Mathlib.Tactic.NoncommRing

noncomputable section

namespace InfoGeometry.Canonical.BRSTQuotientInnerProductLiftBridge

open ExteriorAlgebra
open InfoGeometry.Canonical.DeRhamCohomologyQuotientBridge
open InfoGeometry.Canonical.BRSTCohomologyPhysicalGaugeBridge
open InfoGeometry.Canonical.BRSTExactClassZeroBridge
open InfoGeometry.Canonical.PhysicalGhostZeroBRSTCohomologyBridge
open InfoGeometry.Canonical.KreinSpaceBRSTUnitarityBridge
open InfoGeometry.Canonical.BRSTQuotientPairingWellDefinedBridge

variable {R H : Type*} [CommRing R] [AddCommGroup H] [Module R H]

/-- **Theorem**: Well-definedness condition for Quotient Pairing on BRST Cohomology Module H_Q = Ker Q / Im Q. -/
theorem brst_quotient_pairing_well_defined_lift
    (inner : H → H → R)
    (q : Module.End R H)
    (hq2 : q.comp q = 0)
    (h_adj : ∀ x y, inner (q x) y = inner x (q y))
    (h_zero1 : ∀ y, inner 0 y = 0)
    (h_zero2 : ∀ x, inner x 0 = 0)
    (h_add1 : ∀ x y z, inner (x + y) z = inner x z + inner y z)
    (h_add2 : ∀ x y z, inner x (y + z) = inner x y + inner x z)
    (u v u' v' : LinearMap.ker q)
    (hu : (u - u').1 ∈ LinearMap.range q)
    (hv : (v - v').1 ∈ LinearMap.range q) :
    inner u.1 v.1 = inner u'.1 v'.1 := by
  obtain ⟨chi, hchi⟩ := hu
  obtain ⟨eta, heta⟩ := hv
  dsimp at hchi heta
  have h_u : u.1 = u'.1 + q chi := by rw [eq_add_of_sub_eq' hchi.symm]
  have h_v : v.1 = v'.1 + q eta := by rw [eq_add_of_sub_eq' heta.symm]
  rw [h_u, h_v]
  have h_phys_u : isPhysicalState q u'.1 := u'.2
  have h_phys_v : isPhysicalState q v'.1 := v'.2
  exact brst_quotient_pairing_gauge_invariant inner q hq2 h_adj h_zero1 h_zero2 h_add1 h_add2 u'.1 v'.1 chi eta h_phys_u h_phys_v

/-- **Definition**: General BRST Cohomology Quotient Module H_Q = Ker Q / Im Q for Module H. -/
def brstCohomologyQuotientModule (q : Module.End R H) :=
  LinearMap.ker q ⧸ (LinearMap.range q).comap (LinearMap.ker q).subtype

/-- **Definition**: Literal Physical Inner Product Lift on the BRST Cohomology Quotient Module H_Q = Ker Q / Im Q. -/
def brstQuotientPairing
    (inner : H → H → R)
    (q : Module.End R H)
    (hq2 : q.comp q = 0)
    (h_adj : ∀ x y, inner (q x) y = inner x (q y))
    (h_zero1 : ∀ y, inner 0 y = 0)
    (h_zero2 : ∀ x, inner x 0 = 0)
    (h_add1 : ∀ x y z, inner (x + y) z = inner x z + inner y z)
    (h_add2 : ∀ x y z, inner x (y + z) = inner x y + inner x z)
    (u v : brstCohomologyQuotientModule q) : R :=
  Quotient.liftOn₂ u v (fun u_val v_val => inner u_val.1 v_val.1) (by
    intro u1 v1 u2 v2 hu hv
    have h_eq1 : Submodule.Quotient.mk u1 = (Submodule.Quotient.mk u2 : brstCohomologyQuotientModule q) := Quotient.sound hu
    have h_eq2 : Submodule.Quotient.mk v1 = (Submodule.Quotient.mk v2 : brstCohomologyQuotientModule q) := Quotient.sound hv
    rw [Submodule.Quotient.eq, Submodule.mem_comap] at h_eq1 h_eq2
    exact brst_quotient_pairing_well_defined_lift inner q hq2 h_adj h_zero1 h_zero2 h_add1 h_add2 u1 v1 u2 v2 h_eq1 h_eq2)

/-- **Theorem**: Literal Evaluation of Physical BRST Quotient Pairing ⟨[ψ], [φ]⟩ = ⟨ψ, φ⟩ for Closed Physical States. -/
theorem brst_quotient_pairing_eval
    (inner : H → H → R)
    (q : Module.End R H)
    (hq2 : q.comp q = 0)
    (h_adj : ∀ x y, inner (q x) y = inner x (q y))
    (h_zero1 : ∀ y, inner 0 y = 0)
    (h_zero2 : ∀ x, inner x 0 = 0)
    (h_add1 : ∀ x y z, inner (x + y) z = inner x z + inner y z)
    (h_add2 : ∀ x y z, inner x (y + z) = inner x y + inner x z)
    (u v : LinearMap.ker q) :
    brstQuotientPairing inner q hq2 h_adj h_zero1 h_zero2 h_add1 h_add2 (Submodule.Quotient.mk u) (Submodule.Quotient.mk v) =
      inner u.1 v.1 := rfl

/-- **Theorem**: Master BRST Quotient Inner Product Lift & Physical Cohomology Pairing Synthesis.
    Unifies:
    1. Complete representative gauge invariance for the bilinear pairing.
    2. Literal quotient-lifted function definition brstQuotientPairing : H_Q → H_Q → R on the BRST cohomology quotient module H_Q = Ker Q / Im Q.
    3. Proof closure for literal quotient evaluation ⟨[ψ], [φ]⟩ = ⟨ψ, φ⟩. -/
theorem master_brst_quotient_inner_product_lift_synthesis
    (inner : H → H → R)
    (q : Module.End R H)
    (hq2 : q.comp q = 0)
    (h_adj : ∀ x y, inner (q x) y = inner x (q y))
    (h_zero1 : ∀ y, inner 0 y = 0)
    (h_zero2 : ∀ x, inner x 0 = 0)
    (h_add1 : ∀ x y z, inner (x + y) z = inner x z + inner y z)
    (h_add2 : ∀ x y z, inner x (y + z) = inner x y + inner x z)
    (u v : LinearMap.ker q) :
    (brstQuotientPairing inner q hq2 h_adj h_zero1 h_zero2 h_add1 h_add2 (Submodule.Quotient.mk u) (Submodule.Quotient.mk v) =
      inner u.1 v.1) :=
  rfl

end InfoGeometry.Canonical.BRSTQuotientInnerProductLiftBridge
