import Mathlib
import InfoGeometry.Topology.NativeZornCyclotomicChargeTopological
import InfoGeometry.Topology.NativeZornChiralExchangeTopological
import InfoGeometry.Topology.KleinBottleCubicRootMonodromyTopological

/-!
# Dihedral topological readout on the native Zorn carrier

This file packages the already verified native cubic charge and native chiral
exchange into a single dihedral-style readout over the cube-root parameter
lane.  It does not assert any new algebraic action beyond the existing
componentwise conjugation laws.
-/

namespace InfoGeometry.Topology.NativeZornDihedralTopological

open InfoGeometry.Canonical
open InfoGeometry.Topology.NativeZornCyclotomicChargeTopological
open InfoGeometry.Topology.NativeZornChiralExchangeTopological
open InfoGeometry.Topology.KleinBottleCubicRootMonodromyTopological

noncomputable section

abbrev Zorn := InfoGeometry.Algebra.ZornMatrix ℂ

instance zornFunctionTopologicalSpace :
    TopologicalSpace (Zorn → Zorn) := Pi.topologicalSpace

/-- Combined dihedral readout: cubic charge together with the chiral exchange. -/
def nativeZornDihedralReadout (q : CubicRootParameter) :
    (Zorn → Zorn) × (Zorn → Zorn) :=
  (nativeCubicCharge q.1, nativeChiralExchange)

@[simp] theorem nativeZornDihedralReadout_fst (q : CubicRootParameter) :
    (nativeZornDihedralReadout q).1 = nativeCubicCharge q.1 := by
  rfl

@[simp] theorem nativeZornDihedralReadout_snd (q : CubicRootParameter) :
    (nativeZornDihedralReadout q).2 = nativeChiralExchange := by
  rfl

/-- The combined readout is continuous because the parameter space is discrete. -/
theorem continuous_nativeZornDihedralReadout :
    Continuous nativeZornDihedralReadout := by
  simpa [nativeZornDihedralReadout] using
    (continuous_of_discreteTopology : Continuous nativeZornDihedralReadout)

/-- The combined readout is locally constant on the discrete cube-root lane. -/
theorem isLocallyConstant_nativeZornDihedralReadout :
    IsLocallyConstant nativeZornDihedralReadout := by
  simpa [nativeZornDihedralReadout] using
    (IsLocallyConstant.of_discrete (f := nativeZornDihedralReadout))

/-- The cubic component still has order three on the dihedral packet. -/
theorem nativeZornDihedralReadout_charge_cube (q : CubicRootParameter) :
    ∀ X : Zorn,
      (nativeZornDihedralReadout q).1
          ((nativeZornDihedralReadout q).1
            ((nativeZornDihedralReadout q).1 X)) =
        X := by
  intro X
  simpa [nativeZornDihedralReadout] using
    nativeCubicCharge_cube q.1 q.2 X

/-- The exchange component is involutive on the dihedral packet. -/
theorem nativeZornDihedralReadout_exchange_square (q : CubicRootParameter) :
    ∀ X : Zorn,
      (nativeZornDihedralReadout q).2
          ((nativeZornDihedralReadout q).2 X) =
        X := by
  intro X
  simpa [nativeZornDihedralReadout] using
    nativeChiralExchange_square X

/-- The exchange conjugates the cubic charge to its square on the dihedral packet. -/
theorem nativeZornDihedralReadout_exchange_conj (q : CubicRootParameter) :
    ∀ X : Zorn,
      (nativeZornDihedralReadout q).2
          ((nativeZornDihedralReadout q).1
            ((nativeZornDihedralReadout q).2 X)) =
        nativeCubicCharge (q.1 ^ 2) X := by
  intro X
  simpa [nativeZornDihedralReadout, Function.comp_def] using
    nativeChiralExchange_conj_nativeCubicCharge q.1 q.2 X

end
end InfoGeometry.Topology.NativeZornDihedralTopological
