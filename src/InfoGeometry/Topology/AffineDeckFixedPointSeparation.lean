import InfoGeometry.External.Auto.KleinBottle
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Clifford.Pin55ReflectionGlide
import Mathlib.Tactic

noncomputable section

/-! The affine inversion with constant translation has a fixed point.  This
prevents confusing it with the already-owned free Klein glide. -/
namespace InfoGeometry.Topology.AffineDeckFixedPointSeparation

open InfoGeometry.External.Auto.KleinBottle

abbrev FiveSpace := InfoGeometry.Algebra.FiniteSpin.Vec5R

def affineInversion (c x : FiveSpace) : FiveSpace := c - x

theorem affineInversion_involutive (c x : FiveSpace) :
    affineInversion c (affineInversion c x) = x := by
  unfold affineInversion
  abel

theorem affineInversion_fixed_iff (c x : FiveSpace) :
    affineInversion c x = x ↔ x = (1 / 2 : ℝ) • c := by
  constructor
  · intro h
    ext i
    have hi := congrFun h i
    change c i - x i = x i at hi
    change x i = (1 / 2 : ℝ) * c i
    linarith
  · intro h
    subst x
    ext i
    change c i - (1 / 2 : ℝ) * c i = (1 / 2 : ℝ) * c i
    ring

def proposedDeck : FiveSpace → FiveSpace := affineInversion (fun _ => 1 / 2)

theorem proposedDeck_fixed : proposedDeck (fun _ => 1 / 4) = fun _ => 1 / 4 := by
  ext i
  norm_num [proposedDeck, affineInversion]

theorem proposedDeck_square (x : FiveSpace) : proposedDeck (proposedDeck x) = x :=
  affineInversion_involutive _ x

theorem proposedDeck_not_fixedPointFree : ¬ ∀ x, proposedDeck x ≠ x := by
  intro h
  exact h (fun _ => 1 / 4) proposedDeck_fixed

theorem proposed_linearPart_det :
    Matrix.det (Matrix.diagonal (fun _ : Fin 5 => (-1 : ℝ))) = -1 := by
  rw [Matrix.det_diagonal]
  norm_num

theorem existingKleinGlide_no_fixed (z : ℂ) : G z ≠ z := by
  intro h
  have hre := congrArg Complex.re h
  simp [G] at hre <;> linarith

def productGlide (x : ℂ × (Fin 3 → ℝ)) : ℂ × (Fin 3 → ℝ) :=
  (G x.1, x.2)

theorem productGlide_no_fixed (x : ℂ × (Fin 3 → ℝ)) : productGlide x ≠ x := by
  intro h
  exact existingKleinGlide_no_fixed x.1 (congrArg Prod.fst h)

end InfoGeometry.Topology.AffineDeckFixedPointSeparation
