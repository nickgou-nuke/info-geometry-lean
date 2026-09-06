import InfoGeometry.Lie.CanonicalZornG2GellMannRootComparison
import InfoGeometry.Lie.SplitOctonionQuaternionCircularBasis

/-!
# Multiplicative Cartan flow in the Gell--Mann readout

The uniform hyperbolic flow is only a quadratic isometry.  The traceless
Cartan weights, by contrast, are already owned by `axialCartanFlow`; this file
only specializes that multiplicative flow to the Gell--Mann weight vector and
exposes its action on the circular root channels.
-/

noncomputable section

namespace InfoGeometry.Lie.CanonicalZornG2CartanAutomorphismReadout

open InfoGeometry.Canonical
open InfoGeometry.Canonical.ZornMatrix
open InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge
open InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge
open InfoGeometry.Lie.SplitOctonionAxialCartanFlow
open InfoGeometry.Lie.SplitOctonionGellMannCartan
open InfoGeometry.Lie.SplitOctonionQuaternionCircularBasis
open InfoGeometry.Lie.SplitOctonionQuaternionZornCoordinates
open InfoGeometry.Lie.CanonicalZornG2GellMannRootComparison

abbrev CZ := ZornMatrix ℝ

noncomputable def gellMannCartanFlow (K1 K2 t : ℝ) : CZ ≃ₗ[ℝ] CZ :=
  axialCartanFlow (gellMannCartan K1 K2).1 t

theorem gellMannCartanFlow_map_mul (K1 K2 t : ℝ) (X Y : CZ) :
    gellMannCartanFlow K1 K2 t (X * Y) =
      gellMannCartanFlow K1 K2 t X * gellMannCartanFlow K1 K2 t Y := by
  exact axialCartanFlow_map_mul
    (gellMannCartan K1 K2).1 (gellMannCartan K1 K2).2 t X Y

@[simp] theorem gellMannCartanFlow_one (K1 K2 t : ℝ) :
    gellMannCartanFlow K1 K2 t (1 : CZ) = 1 := by
  exact axialCartanFlow_one (gellMannCartan K1 K2).1 t

theorem gellMannCartanFlow_add (K1 K2 s t : ℝ) (X : CZ) :
    gellMannCartanFlow K1 K2 (s + t) X =
      gellMannCartanFlow K1 K2 s (gellMannCartanFlow K1 K2 t X) := by
  exact axialCartanFlow_add (gellMannCartan K1 K2).1 s t X

@[simp] theorem gellMannCartanFlow_rootPlus
    (K1 K2 t : ℝ) (i : Fin 3) :
    gellMannCartanFlow K1 K2 t
        (cartesianZornLinearEquiv (rootPlus i)) =
      Real.exp (t * (gellMannCartan K1 K2).1 i) •
        cartesianZornLinearEquiv (rootPlus i) := by
  rw [gellMannCartanFlow, cartesianZorn_rootPlus]
  exact axialCartanFlow_chiralUpperBasis _ _ _

@[simp] theorem gellMannCartanFlow_rootMinus
    (K1 K2 t : ℝ) (i : Fin 3) :
    gellMannCartanFlow K1 K2 t
        (cartesianZornLinearEquiv (rootMinus i)) =
      Real.exp (-(t * (gellMannCartan K1 K2).1 i)) •
        cartesianZornLinearEquiv (rootMinus i) := by
  rw [gellMannCartanFlow, cartesianZorn_rootMinus]
  exact axialCartanFlow_chiralLowerBasis _ _ _

theorem gellMannCartanFlow_inverse (K1 K2 t : ℝ) (X : CZ) :
    gellMannCartanFlow K1 K2 (-t)
      (gellMannCartanFlow K1 K2 t X) = X := by
  rw [gellMannCartanFlow, ← axialCartanFlow_neg_apply]
  exact (axialCartanFlow (gellMannCartan K1 K2).1 t).symm_apply_apply X

noncomputable def gellMannCartanCompositionAut (K1 K2 t : ℝ) :
    realZornCompositionAut :=
  axialCartanCompositionAut (gellMannCartan K1 K2).1
    (gellMannCartan K1 K2).2 t

@[simp] theorem gellMannCartanCompositionAut_apply
    (K1 K2 t : ℝ) (X : CZ) :
    ((gellMannCartanCompositionAut K1 K2 t : realZornCompositionAut) :
      CanonicalLinearAut) X = gellMannCartanFlow K1 K2 t X := rfl

theorem gellMannCartanCompositionAut_zero (K1 K2 : ℝ) :
    gellMannCartanCompositionAut K1 K2 0 = 1 := by
  exact axialCartanCompositionAut_zero
    (gellMannCartan K1 K2).1 (gellMannCartan K1 K2).2

theorem gellMannCartanCompositionAut_add
    (K1 K2 s t : ℝ) :
    gellMannCartanCompositionAut K1 K2 (s + t) =
      gellMannCartanCompositionAut K1 K2 s *
        gellMannCartanCompositionAut K1 K2 t := by
  exact axialCartanCompositionAut_add
    (gellMannCartan K1 K2).1 (gellMannCartan K1 K2).2 s t

theorem gellMannCartanCompositionAut_neg
    (K1 K2 t : ℝ) :
    gellMannCartanCompositionAut K1 K2 (-t) =
      (gellMannCartanCompositionAut K1 K2 t)⁻¹ := by
  exact axialCartanCompositionAut_neg
    (gellMannCartan K1 K2).1 (gellMannCartan K1 K2).2 t

theorem gellMannCartanCompositionAut_commute
    (K1 K2 L1 L2 s t : ℝ) :
    gellMannCartanCompositionAut K1 K2 s *
        gellMannCartanCompositionAut L1 L2 t =
      gellMannCartanCompositionAut L1 L2 t *
        gellMannCartanCompositionAut K1 K2 s := by
  exact axialCartanCompositionAut_commute
    (gellMannCartan K1 K2).1 (gellMannCartan L1 L2).1
    (gellMannCartan K1 K2).2 (gellMannCartan L1 L2).2 s t

end InfoGeometry.Lie.CanonicalZornG2CartanAutomorphismReadout
