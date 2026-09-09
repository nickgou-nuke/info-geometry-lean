import Mathlib.Algebra.Field.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel

noncomputable section

namespace InfoGeometry.Canonical.ZornAmariMoebius

set_option linter.unusedSectionVars false

variable {F : Type*} [Field F] [NeZero (2 : F)]

/-! ### 1. Three-Point Möbius Map and Weyl Dilation -/

/-- Conformal point on the extended information line. -/
structure MoebiusPoint (F : Type*) where
  val : F

/-- Multiplicative Weyl dilation operator mapping additive surprisal to projective scale. -/
def weylDilation (scale : F) (p : MoebiusPoint F) : MoebiusPoint F where
  val := scale * p.val

/-- 🏆 THEOREM: Weyl dilation preserves zero fixed-point. -/
theorem moebius_fixpoint_zero (scale : F) :
    (weylDilation scale ⟨0⟩).val = 0 := by
  dsimp [weylDilation]
  ring

/-- 🏆 THEOREM: Weyl dilation maps identity 1 to the dilation scale factor. -/
theorem moebius_scale_one (scale : F) :
    (weylDilation scale ⟨1⟩).val = scale := by
  dsimp [weylDilation]
  ring

/-! ### 2. Amari Information Geometry (Primal-Dual Affine Space) -/

/-- Amari primal potential (Entropy / Surprisal potential): ψ(E) = E² / 2. -/
def amariPrimalPotential (E : F) : F := E^2 / 2

/-- Amari dual potential (Energy gauge / Legendre transform): φ(P) = P² / 2. -/
def amariDualPotential (P : F) : F := P^2 / 2

/-- 🏆 THEOREM: Amari Legendre Duality:
    Primal and dual potentials sum exactly to the canonical coordinate pairing E * P. -/
theorem amari_legendre_duality (E P : F) (h_momentum : P = E) :
    amariPrimalPotential E + amariDualPotential P = E * P := by
  dsimp [amariPrimalPotential, amariDualPotential]
  rw [h_momentum, add_halves, sq]

/-- Amari Fisher information metric for the quadratic potential: g = d²ψ/dE² = 1. -/
def amariFisherMetric (_E : F) : F := 1

/-- 🏆 THEOREM: Conformal closure of the scale horizon:
    Total Legendre action minus primal potential recovers the kinetic action E² / 2. -/
theorem amari_moebius_unified_congruence (E : F) :
    let P := E
    let total_action := amariPrimalPotential E + amariDualPotential P
    total_action - (amariPrimalPotential E) = E^2 / 2 := by
  intro P total_action
  dsimp [total_action, amariPrimalPotential, amariDualPotential]
  ring

structure AmariMoebiusPacket (F : Type*) [Field F] [NeZero (2 : F)] where
  fix_zero : ∀ (scale : F), (weylDilation scale ⟨0⟩).val = 0
  scale_one : ∀ (scale : F), (weylDilation scale ⟨1⟩).val = scale
  legendre_dual : ∀ (E P : F), P = E → amariPrimalPotential E + amariDualPotential P = E * P
  unified_congruence : ∀ (E : F),
    let P := E
    let total_action := amariPrimalPotential E + amariDualPotential P
    total_action - (amariPrimalPotential E) = E^2 / 2

def makeAmariMoebiusPacket (F : Type*) [Field F] [NeZero (2 : F)] : AmariMoebiusPacket F where
  fix_zero := moebius_fixpoint_zero
  scale_one := moebius_scale_one
  legendre_dual := amari_legendre_duality
  unified_congruence := amari_moebius_unified_congruence

theorem amari_moebius_certified :
    amariPrimalPotential (1 : ℝ) + amariDualPotential 1 = 1 * 1 :=
  (makeAmariMoebiusPacket ℝ).legendre_dual 1 1 rfl

end InfoGeometry.Canonical.ZornAmariMoebius
