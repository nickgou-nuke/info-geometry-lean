import Mathlib.Tactic
import InfoGeometry.Arithmetic.PrimonPhaseLift
import InfoGeometry.Twistor.Cl55MinkowskiCelestialSlice

/-!
# Finite primon phase descent to the native projective null boundary

The logarithmic phase is an affine two-coordinate object.  A projective-null
point is obtained only after imposing the finite normalization
`ChiralPhase.normSq z = 1`.  The normalized scalar and bivector coordinates
then form a point of the existing celestial two-sphere, whose native
`Q55`-null projectivization is supplied by
`Cl55MinkowskiCelestialSlice.celestialNullPoint`.

This file does not identify the full phase plane with a null cone and does not
introduce a new twistor carrier.
-/

noncomputable section

namespace InfoGeometry.Arithmetic.PrimonProjectiveNullDescent

open BigOperators
open InfoGeometry.Algebraic
open InfoGeometry.Arithmetic.PrimonPhaseLift
open InfoGeometry.Clifford.Clifford55
open InfoGeometry.Twistor
open InfoGeometry.Twistor.Cl55MinkowskiCelestialSlice

/-- The normalized celestial direction carried by a chiral phase. -/
def chiralPhaseCelestialDirection (z : ChiralPhase) (hz : z.normSq = 1) : CelestialSphere :=
  ⟨![z.scalar, z.bivector, 0], by
    convert hz using 1 <;> simp [Fin.sum_univ_succ, ChiralPhase.normSq]
  ⟩

theorem chiralPhaseCelestialDirection_injective :
    ∀ (z w : ChiralPhase) (hz : z.normSq = 1) (hw : w.normSq = 1),
      chiralPhaseCelestialDirection z hz = chiralPhaseCelestialDirection w hw → z = w := by
  intro z w hz hw h
  apply ChiralPhase.ext
  · exact congrArg (fun x : CelestialSphere => x.1 0) h
  · exact congrArg (fun x : CelestialSphere => x.1 1) h

/-- A unit chiral phase descends to the native `Q55` projective-null point. -/
def chiralPhaseNullPoint (z : ChiralPhase) (hz : z.normSq = 1) :
    TwistorSpace (K := ℝ) (V := V55) Q55 :=
  celestialNullPoint (chiralPhaseCelestialDirection z hz)

theorem chiralPhaseNullPoint_is_null
    (z : ChiralPhase) (hz : z.normSq = 1) :
    IsNull Q55 (chiralPhaseNullPoint z hz).1 :=
  (chiralPhaseNullPoint z hz).2

theorem chiralPhaseNullPoint_injective_on_unit :
    Function.Injective (fun z : {z : ChiralPhase // z.normSq = 1} =>
      chiralPhaseNullPoint z.1 z.2) := by
  intro z w h
  apply Subtype.ext
  apply chiralPhaseCelestialDirection_injective z.1 w.1 z.2 w.2
  apply celestialNullPoint_injective
  change celestialNullPoint (chiralPhaseCelestialDirection z.1 z.2) =
    celestialNullPoint (chiralPhaseCelestialDirection w.1 w.2) at h
  exact h

/-- The normalized prime logarithmic phase has a projective-null descent. -/
def primonLogGeneratorNullPoint
    (σ t : ℝ) (p : Nat.Primes) (n : ℤ)
    (h : (primonLogGenerator σ t p n).normSq = 1) :
    TwistorSpace (K := ℝ) (V := V55) Q55 :=
  chiralPhaseNullPoint (primonLogGenerator σ t p n) h

theorem primonLogGeneratorNullPoint_is_null
    (σ t : ℝ) (p : Nat.Primes) (n : ℤ)
    (h : (primonLogGenerator σ t p n).normSq = 1) :
    IsNull Q55 (primonLogGeneratorNullPoint σ t p n h).1 :=
  chiralPhaseNullPoint_is_null _ h

end InfoGeometry.Arithmetic.PrimonProjectiveNullDescent
