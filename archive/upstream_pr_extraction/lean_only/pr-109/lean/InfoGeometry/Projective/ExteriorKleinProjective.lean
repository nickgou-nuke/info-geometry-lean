import InfoGeometry.Projective.ExteriorPowerPluckerBridge
import Mathlib.LinearAlgebra.Projectivization.Basic

/-!
# Projectivized exterior Klein locus

The Klein equation and exterior decomposability descend to Mathlib's actual
projectivization of the literal exterior square.  This owner stops before any
identification with a Grassmannian.
-/

noncomputable section

open scoped LinearAlgebra.Projectivization

namespace InfoGeometry.Projective.ExteriorKleinProjective

open InfoGeometry.Canonical.FierzKleinFoundation
open InfoGeometry.Projective.ExteriorPowerPluckerBridge

abbrev ExteriorSquare := ⋀[ℝ]^2 Vec4

/-- The Klein null equation on projective exterior rays. -/
def IsKlein : ℙ ℝ ExteriorSquare → Prop :=
  Projectivization.lift
    (f := fun X : {X : ExteriorSquare // X ≠ 0} =>
      exteriorKleinForm X = 0)
    (hf := by
      intro X Y c hXY
      apply propext
      have hc : c ≠ 0 := by
        intro hc
        have : (X : ExteriorSquare) = 0 := by simpa [hc] using hXY
        exact X.2 this
      constructor
      · intro hX
        have hscaled : c ^ 2 * exteriorKleinForm (Y : ExteriorSquare) = 0 := by
          rw [← exteriorKleinForm_smul]
          simpa [hXY] using hX
        exact (mul_eq_zero.mp hscaled).resolve_left (pow_ne_zero 2 hc)
      · intro hY
        have : exteriorKleinForm (c • (Y : ExteriorSquare)) = 0 := by
          rw [exteriorKleinForm_smul, hY, mul_zero]
        simpa [hXY] using this)

/-- Exterior decomposability on projective rays. -/
def IsDecomposable : ℙ ℝ ExteriorSquare → Prop :=
  Projectivization.lift
    (f := fun X : {X : ExteriorSquare // X ≠ 0} =>
      ∃ u v : Vec4, (X : ExteriorSquare) =
        exteriorPower.ιMulti ℝ 2 ![u, v])
    (hf := by
      intro X Y c hXY
      apply propext
      have hc : c ≠ 0 := by
        intro hc
        have : (X : ExteriorSquare) = 0 := by simpa [hc] using hXY
        exact X.2 this
      change
        (∃ u v : Vec4, (X : ExteriorSquare) =
          exteriorPower.ιMulti ℝ 2 ![u, v]) ↔
        (∃ u v : Vec4, (Y : ExteriorSquare) =
          exteriorPower.ιMulti ℝ 2 ![u, v])
      rw [← exteriorKleinForm_eq_zero_iff_decomposable,
        ← exteriorKleinForm_eq_zero_iff_decomposable]
      constructor
      · intro hX
        have hscaled : c ^ 2 * exteriorKleinForm (Y : ExteriorSquare) = 0 := by
          rw [← exteriorKleinForm_smul]
          simpa [hXY] using hX
        exact (mul_eq_zero.mp hscaled).resolve_left (pow_ne_zero 2 hc)
      · intro hY
        have : exteriorKleinForm (c • (Y : ExteriorSquare)) = 0 := by
          rw [exteriorKleinForm_smul, hY, mul_zero]
        simpa [hXY] using this)

abbrev KleinLocus := {p : ℙ ℝ ExteriorSquare // IsKlein p}

@[simp] theorem isKlein_mk_iff (X : ExteriorSquare) (hX : X ≠ 0) :
    IsKlein (Projectivization.mk ℝ X hX) ↔ exteriorKleinForm X = 0 := by
  simp [IsKlein, Projectivization.lift_mk]

@[simp] theorem isDecomposable_mk_iff (X : ExteriorSquare) (hX : X ≠ 0) :
    IsDecomposable (Projectivization.mk ℝ X hX) ↔
      ∃ u v : Vec4, X = exteriorPower.ιMulti ℝ 2 ![u, v] := by
  simp [IsDecomposable, Projectivization.lift_mk]

/-- The projective Klein locus is exactly the projective decomposable locus. -/
theorem isKlein_iff_isDecomposable (p : ℙ ℝ ExteriorSquare) :
    IsKlein p ↔ IsDecomposable p := by
  refine Projectivization.ind (p := p) ?_
  intro X hX
  rw [isKlein_mk_iff, isDecomposable_mk_iff]
  exact exteriorKleinForm_eq_zero_iff_decomposable X

end InfoGeometry.Projective.ExteriorKleinProjective
