import InfoGeometry.Exceptional.CircularSplitOctonionContactLift
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Circular split-octonion mixed bracket into the contact zero grade

This owner does not define a second mixed bracket.  It reads the existing
`fiveGradedBracket` on one circular atom in contact grade `-1` and one circular
atom in contact grade `+1`.

For charges `X,Y`, the native bracket is exactly

  `mixedSymplecticBracket D X Y + omega_D(X,Y) H`

inside `g_0 = g_0^symp ⊕ R H`.  The circular basis therefore gives a finite
readback of both zero-grade components.  No identification of `g_0^symp` with
`e7` and no octonion-associator interpretation is asserted here.
-/

noncomputable section

namespace InfoGeometry.Exceptional.Freudenthal.CircularSplitOctonionZeroGradeBridge

open InfoGeometry.Exceptional.Freudenthal

variable {J : Type*} [AddCommGroup J] [Module ℝ J]
variable (D : CubicJordanDatum J)
variable (rootMapPlus rootMapMinus : Fin 3 → J)

/-- Native zero-grade symplectic operator associated to two circular atoms. -/
def circularZeroSymp (a b : CircularChargeAtom) : SymplecticTKKZero D :=
  mixedSymplecticBracket D
    (circularCharge rootMapPlus rootMapMinus a)
    (circularCharge rootMapPlus rootMapMinus b)

/-- Native scalar/H component associated to two circular atoms. -/
def circularZeroScale (a b : CircularChargeAtom) : ℝ :=
  FreudenthalCharge.symplecticForm D
    (circularCharge rootMapPlus rootMapMinus a)
    (circularCharge rootMapPlus rootMapMinus b)

/-- The existing `[-1,+1]` bracket, restricted to the circular basis. -/
def circularMixedBracket (a b : CircularChargeAtom) : FiveGradedCarrier D :=
  fiveGradedBracket D
    (toMinusOne D rootMapPlus rootMapMinus a)
    (toPlusOne D rootMapPlus rootMapMinus b)

/-- The symplectic component of the circular mixed bracket is literally the
native rank-two mixed bracket. -/
theorem circularMixedBracket_zero_symp (a b : CircularChargeAtom) :
    (circularMixedBracket D rootMapPlus rootMapMinus a b).zero_symp =
      circularZeroSymp D rootMapPlus rootMapMinus a b := by
  rw [circularMixedBracket, circular_mixed_bracket_readback]
  rfl

/-- The scale component of the circular mixed bracket is literally the
Freudenthal symplectic pairing. -/
theorem circularMixedBracket_zero_scale (a b : CircularChargeAtom) :
    (circularMixedBracket D rootMapPlus rootMapMinus a b).zero_scale =
      circularZeroScale D rootMapPlus rootMapMinus a b := by
  rw [circularMixedBracket, circular_mixed_bracket_readback]
  rfl

/-- Exact zero-grade decomposition of the circular mixed bracket.
The four nonzero contact lanes outside degree zero vanish identically. -/
theorem circularMixedBracket_eq_zeroGrade (a b : CircularChargeAtom) :
    circularMixedBracket D rootMapPlus rootMapMinus a b =
      injSympZero D (circularZeroSymp D rootMapPlus rootMapMinus a b) +
        genHscale D (circularZeroScale D rootMapPlus rootMapMinus a b) := by
  rw [circularMixedBracket, circular_mixed_bracket_readback]
  apply FiveGradedCarrier.ext <;>
    simp [circularZeroSymp, circularZeroScale, injSympZero, genHscale]

/-- Pole-pair mixed bracket: the `H` coefficient is `1`. -/
theorem pole_pair_zero_scale :
    (circularMixedBracket D rootMapPlus rootMapMinus uPlus uMinus).zero_scale = 1 := by
  rw [circularMixedBracket_zero_scale]
  dsimp [circularZeroScale, circularCharge]
  exact omega_poles D

/-- Pole-pair full zero-grade readback. -/
theorem pole_pair_mixedBracket :
    circularMixedBracket D rootMapPlus rootMapMinus uPlus uMinus =
      injSympZero D
        (mixedSymplecticBracket D embedPlusPole embedMinusPole) +
      genHscale D 1 := by
  rw [circularMixedBracket_eq_zeroGrade]
  dsimp [circularZeroSymp, circularZeroScale, circularCharge]
  rw [omega_poles]

/-- Root-pair `H` coefficient is exactly the Kronecker delta. -/
theorem root_pair_zero_scale
    (h_ortho : ∀ i j : Fin 3,
      D.traceBilin (rootMapPlus i) (rootMapMinus j) = if i = j then 1 else 0)
    (i j : Fin 3) :
    (circularMixedBracket D rootMapPlus rootMapMinus (.plusRoot i) (.minusRoot j)).zero_scale =
      if i = j then 1 else 0 := by
  rw [circularMixedBracket_zero_scale]
  dsimp [circularZeroScale, circularCharge]
  exact omega_roots D rootMapPlus rootMapMinus h_ortho i j

/-- Root-pair full zero-grade readback: the symplectic component is the native
rank-two operator and the scale component is `delta_ij H`. -/
theorem root_pair_mixedBracket
    (h_ortho : ∀ i j : Fin 3,
      D.traceBilin (rootMapPlus i) (rootMapMinus j) = if i = j then 1 else 0)
    (i j : Fin 3) :
    circularMixedBracket D rootMapPlus rootMapMinus (.plusRoot i) (.minusRoot j) =
      injSympZero D
        (mixedSymplecticBracket D
          (embedPlusRoot rootMapPlus i)
          (embedMinusRoot rootMapMinus j)) +
      genHscale D (if i = j then 1 else 0) := by
  rw [circularMixedBracket_eq_zeroGrade]
  simp [circularZeroSymp, circularZeroScale, circularCharge,
    omega_roots D rootMapPlus rootMapMinus h_ortho i j]

/-- Same-chirality root channels have zero `H` projection. -/
theorem plus_root_pair_zero_scale (i j : Fin 3) :
    (circularMixedBracket D rootMapPlus rootMapMinus (.plusRoot i) (.plusRoot j)).zero_scale = 0 := by
  rw [circularMixedBracket_zero_scale]
  simp [circularZeroScale, circularCharge, omega_roots_same_plus]

/-- Same-chirality lower-root channels have zero `H` projection. -/
theorem minus_root_pair_zero_scale (i j : Fin 3) :
    (circularMixedBracket D rootMapPlus rootMapMinus (.minusRoot i) (.minusRoot j)).zero_scale = 0 := by
  rw [circularMixedBracket_zero_scale]
  simp [circularZeroScale, circularCharge, omega_roots_same_minus]

/-- The zero-grade symplectic component has the already-proved rank-two action
on a positive circular root. -/
theorem root_pair_zero_symp_action_on_plus
    (h_ortho : ∀ i j : Fin 3,
      D.traceBilin (rootMapPlus i) (rootMapMinus j) = if i = j then 1 else 0)
    (i j k : Fin 3) :
    ((circularMixedBracket D rootMapPlus rootMapMinus (.plusRoot i) (.minusRoot j)).zero_symp :
      Module.End ℝ (FreudenthalCharge J))
        (embedPlusRoot rootMapPlus k) =
      - (if j = k then (1 : ℝ) else 0) • embedPlusRoot rootMapPlus i := by
  rw [circularMixedBracket_zero_symp]
  change symplecticRankTwo D
      (embedPlusRoot rootMapPlus i) (embedMinusRoot rootMapMinus j)
      (embedPlusRoot rootMapPlus k) = _
  exact rankTwo_roots_on_plus D rootMapPlus rootMapMinus h_ortho i j k

/-- The zero-grade symplectic component has the already-proved rank-two action
on a negative circular root. -/
theorem root_pair_zero_symp_action_on_minus
    (h_ortho : ∀ i j : Fin 3,
      D.traceBilin (rootMapPlus i) (rootMapMinus j) = if i = j then 1 else 0)
    (i j k : Fin 3) :
    ((circularMixedBracket D rootMapPlus rootMapMinus (.plusRoot i) (.minusRoot j)).zero_symp :
      Module.End ℝ (FreudenthalCharge J))
        (embedMinusRoot rootMapMinus k) =
      (if i = k then (1 : ℝ) else 0) • embedMinusRoot rootMapMinus j := by
  rw [circularMixedBracket_zero_symp]
  change symplecticRankTwo D
      (embedPlusRoot rootMapPlus i) (embedMinusRoot rootMapMinus j)
      (embedMinusRoot rootMapMinus k) = _
  exact rankTwo_roots_on_minus D rootMapPlus rootMapMinus h_ortho i j k

end InfoGeometry.Exceptional.Freudenthal.CircularSplitOctonionZeroGradeBridge
