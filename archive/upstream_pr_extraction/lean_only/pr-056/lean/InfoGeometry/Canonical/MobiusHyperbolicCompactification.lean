import Mathlib.Tactic

/-!
# InfoGeometry.Canonical.MobiusHyperbolicCompactification

Möbius inversion on the compactified positive chart (`ℝ≥0∞`), used as a finite
owner-side model for:

* boundary exchange `0 ↔ ∞`,
* involutive compactification symmetry,
* two-sheet swap identity `(x, x⁻¹) ↔ (x⁻¹, x)`.

This is the theorem-safe compactified-hyperbolic readout layer.
-/

namespace InfoGeometry.Canonical.MobiusHyperbolicCompactification

open scoped ENNReal

noncomputable section

/-- Compactified positive chart used for hyperbolic boundary readout. -/
abbrev HyperChart := ℝ≥0∞

/-- Chiral/source boundary pole. -/
def ePlus : HyperChart := 0

/-- Chiral/sink boundary pole (point at infinity). -/
def eMinus : HyperChart := ∞

/-- Möbius inversion on the compactified chart. -/
def mobiusInv (x : HyperChart) : HyperChart := x⁻¹

@[simp] theorem mobiusInv_ePlus : mobiusInv ePlus = eMinus := by
  simp [mobiusInv, ePlus, eMinus]

@[simp] theorem mobiusInv_eMinus : mobiusInv eMinus = ePlus := by
  simp [mobiusInv, ePlus, eMinus]

/-- Inversion is involutive on the compactified chart. -/
theorem mobiusInv_involutive : Function.Involutive mobiusInv := by
  intro x
  simp [mobiusInv]

/-- Boundary set (`{0,∞}`) used by the compactified chart. -/
def boundarySet : Set HyperChart := {ePlus, eMinus}

theorem mobiusInv_mem_boundary_iff (x : HyperChart) :
    mobiusInv x ∈ boundarySet ↔ x ∈ boundarySet := by
  constructor
  · intro hx
    rcases hx with hx | hx
    · right
      have : x = eMinus := by
        have h := congrArg mobiusInv hx
        simpa [mobiusInv_involutive x] using h
      simpa [this]
    · left
      have : x = ePlus := by
        have h := congrArg mobiusInv hx
        simpa [mobiusInv_involutive x] using h
      simpa [this]
  · intro hx
    rcases hx with hx | hx
    · right
      simpa [hx] using mobiusInv_ePlus
    · left
      rw [hx, mobiusInv_eMinus]

/-- Two-sheet compactified readout `(x, x⁻¹)`. -/
def twoSheet (x : HyperChart) : HyperChart × HyperChart := (x, mobiusInv x)

/-- Möbius inversion swaps the two sheets. -/
theorem twoSheet_mobius_swap (x : HyperChart) :
    twoSheet (mobiusInv x) = Prod.swap (twoSheet x) := by
  ext <;> simp [twoSheet, mobiusInv]

end
end InfoGeometry.Canonical.MobiusHyperbolicCompactification
