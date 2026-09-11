import InfoGeometry.Lie.SplitOctonionDerivationWittBlockRealization
import InfoGeometry.Algebra.FiniteSpinAlgebra

noncomputable section

namespace InfoGeometry.Lie.SplitOctonionWittSkewEndomorphismSubalgebra

open InfoGeometry.Lie.SplitOctonionWittPairingTransportBridge
open InfoGeometry.Lie.SplitOctonionDerivationWittBlockRealization

abbrev Coord8 := SplitOctonionWittPairingTransportBridge.Coord8

def IsNeutralWittSkew (T : Module.End ℝ Coord8) : Prop :=
  ∀ x y,
    neutralEtaPairing (T x) y + neutralEtaPairing x (T y) = 0

theorem neutralEtaPairing_symm (x y : Coord8) :
    neutralEtaPairing x y = neutralEtaPairing y x := by
  dsimp [neutralEtaPairing]
  ring

theorem neutralWittSkew_bracket
    {X Y : Module.End ℝ Coord8}
    (hX : IsNeutralWittSkew X) (hY : IsNeutralWittSkew Y) :
    IsNeutralWittSkew ⁅X, Y⁆ := by
  intro x y
  rw [LieRing.of_associative_ring_bracket]
  change neutralEtaPairing (X (Y x) - Y (X x)) y +
    neutralEtaPairing x (X (Y y) - Y (X y)) = 0
  have hXY := hX (Y x) y
  have hYX := hY (X x) y
  have hX' := hX (Y y) x
  have hY' := hY (X y) x
  rw [neutralEtaPairing_symm (X (Y y)) x] at hX'
  rw [neutralEtaPairing_symm (Y (X y)) x] at hY'
  dsimp [neutralEtaPairing] at hXY hYX hX' hY' ⊢
  ring_nf at hXY hYX hX' hY' ⊢
  linarith

def neutralWittSkewLieSubalgebra :
    LieSubalgebra ℝ (Module.End ℝ Coord8) where
  carrier := {T | IsNeutralWittSkew T}
  zero_mem' := by
    intro x y
    dsimp [IsNeutralWittSkew, neutralEtaPairing]
    ring
  add_mem' := by
    intro X Y hX hY x y
    calc
      neutralEtaPairing ((X + Y) x) y + neutralEtaPairing x ((X + Y) y) =
          (neutralEtaPairing (X x) y + neutralEtaPairing x (X y)) +
            (neutralEtaPairing (Y x) y + neutralEtaPairing x (Y y)) := by
              simp [neutralEtaPairing, LinearMap.add_apply]
              ring
      _ = 0 := by rw [hX x y, hY x y, add_zero]
  smul_mem' := by
    intro r X hX x y
    calc
      neutralEtaPairing ((r • X) x) y + neutralEtaPairing x ((r • X) y) =
          r * (neutralEtaPairing (X x) y + neutralEtaPairing x (X y)) := by
            simp [neutralEtaPairing, LinearMap.smul_apply]
            ring
      _ = 0 := by rw [hX x y, mul_zero]
  lie_mem' := by
    intro X Y hX hY
    exact neutralWittSkew_bracket hX hY

theorem transportedDerivation_mem_neutralWittSkew
    (D : Derivation) :
    transportedDerivation D ∈ neutralWittSkewLieSubalgebra := by
  intro x y
  simpa [transportedDerivation] using
    (neutral_canonical_derivation_eta_skew D
      (neutralCanonicalToCoord.symm x) (neutralCanonicalToCoord.symm y))

theorem transportedDerivationLieSubalgebra_le_neutralWittSkew :
    transportedDerivationLieSubalgebra ≤ neutralWittSkewLieSubalgebra := by
  intro T hT
  rcases hT with ⟨D, rfl⟩
  exact transportedDerivation_mem_neutralWittSkew D

end InfoGeometry.Lie.SplitOctonionWittSkewEndomorphismSubalgebra
