import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.NativeZornCyclotomicChargeTopological

/-!
# Chiral exchange on the native Zorn carrier

The exchange involution swaps the upper and lower native vector coordinates.
Together with the cubic charge it gives the concrete reflection relation of
the cyclotomic/dihedral readout, without asserting a group action on any
external completion.
-/

namespace InfoGeometry.Topology.NativeZornChiralExchangeTopological

open InfoGeometry.Algebra
open InfoGeometry.Algebra.ZornMatrix
open InfoGeometry.Topology.ChiralSolderingTopological
open InfoGeometry.Topology.NativeZornCyclotomicChargeTopological

noncomputable section

abbrev Zorn := InfoGeometry.Algebra.ZornMatrix ℂ

/-- Chiral exchange: retain the diagonal and swap upper/lower vectors. -/
def nativeChiralExchange (X : Zorn) : Zorn where
  a := X.a
  v := X.w
  w := X.v
  b := X.b

theorem continuous_nativeChiralExchange :
    Continuous (nativeChiralExchange : Zorn → Zorn) := by
  apply continuous_induced_rng.mpr
  change Continuous (fun X : Zorn =>
    ZornMatrix.coordEquiv (nativeChiralExchange X))
  simp only [ZornMatrix.coordEquiv]
  change Continuous (fun X : Zorn => (X.a, X.w, X.v, X.b))
  exact continuous_zorn_a.prodMk
    (continuous_zorn_w.prodMk (continuous_zorn_v.prodMk continuous_zorn_b))

theorem nativeChiralExchange_square (X : Zorn) :
    nativeChiralExchange (nativeChiralExchange X) = X := by
  rfl

theorem nativeChiralExchange_square_function :
    nativeChiralExchange ∘ nativeChiralExchange = id := by
  funext X
  exact nativeChiralExchange_square X

theorem nativeChiralExchange_conj_nativeCubicCharge
    (ω : ℂ) (hω : ω ^ 3 = 1) (X : Zorn) :
    nativeChiralExchange
        (nativeCubicCharge ω (nativeChiralExchange X)) =
      nativeCubicCharge (ω ^ 2) X := by
  ext
  · rfl
  · rename_i i
    simp [nativeChiralExchange, nativeCubicCharge, smul_eq_mul]
  · rename_i i
    change ω * X.w i = (ω ^ 2) ^ 2 * X.w i
    have hcoeff : (ω ^ 2) ^ 2 = ω := by
      calc
        (ω ^ 2) ^ 2 = ω ^ 3 * ω := by ring
        _ = ω := by rw [hω]; ring
    rw [hcoeff]
  · rfl

end
end InfoGeometry.Topology.NativeZornChiralExchangeTopological
