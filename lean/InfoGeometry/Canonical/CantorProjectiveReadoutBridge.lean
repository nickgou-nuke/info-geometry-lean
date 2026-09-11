import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.CantorProjectiveLimit
import InfoGeometry.Canonical.FractalCantorCliffordFockBridge
import InfoGeometry.Canonical.CantorBoundaryFiniteReadout

/-!
# Projective-prefix readout bridge

This file connects the finite `Fin n → Bool` projective-limit projections with
the list-valued prefix readout used by the analytic boundary owner.  It proves
only the concrete finite/infinite compatibility statement.
-/

noncomputable section

open scoped BigOperators

namespace InfoGeometry.Canonical.CantorProjectiveReadoutBridge

open InfoGeometry.Canonical.UHFInductiveColimitBoundary
open InfoGeometry.Canonical.FractalCantorCliffordFockBridge
open InfoGeometry.Canonical.CantorProjectiveLimit.PrefixProjectiveLimit
open InfoGeometry.Canonical.CantorBoundaryFiniteReadout

def finitePrefixReadoutFn {n : ℕ} (b : BitWord n) : ℝ :=
  finitePrefixReadout (List.ofFn b)

theorem bitWordPrefix_list_eq (n : ℕ) (x : CantorBoundary) :
    List.ofFn (InfoGeometry.Canonical.UHFInductiveColimitBoundary.boundaryPrefix n x) =
      InfoGeometry.Canonical.FractalCantorCliffordFockBridge.boundaryPrefix n x := by
  induction n generalizing x with
  | zero =>
      simp [FractalCantorCliffordFockBridge.boundaryPrefix]
  | succ n ih =>
      simp only [UHFInductiveColimitBoundary.boundaryPrefix,
        List.ofFn_eq_map, List.finRange_succ,
        FractalCantorCliffordFockBridge.boundaryPrefix]
      rw [List.map_cons]
      congr 1
      simpa [List.ofFn_eq_map,
        UHFInductiveColimitBoundary.boundaryPrefix,
        FractalCantorCliffordFockBridge.boundaryTail] using ih
        (FractalCantorCliffordFockBridge.boundaryTail x)

theorem projective_readout_prefix_tail
    (p : InfoGeometry.Canonical.CantorProjectiveLimit.PrefixProjectiveLimit) (N : ℕ) :
    InfoGeometry.Canonical.CantorBoundaryReadoutBounds.realBinaryReadout
        (InfoGeometry.Canonical.CantorProjectiveLimit.PrefixProjectiveLimit.toCantor p) =
      finitePrefixReadoutFn (π N p) +
        (1 / 2 : ℝ) ^ N *
          InfoGeometry.Canonical.CantorBoundaryReadoutBounds.realBinaryReadout
            (boundaryIterateTail N
              (InfoGeometry.Canonical.CantorProjectiveLimit.PrefixProjectiveLimit.toCantor p)) := by
  have hdecomp := realBinaryReadout_prefix_tail_decomposition N
    (InfoGeometry.Canonical.CantorProjectiveLimit.PrefixProjectiveLimit.toCantor p)
  have hp := boundaryPrefix_toCantor_eq_word p N
  have hl := bitWordPrefix_list_eq N (toCantor p)
  rw [hp] at hl
  rw [← hl] at hdecomp
  exact hdecomp

end InfoGeometry.Canonical.CantorProjectiveReadoutBridge
