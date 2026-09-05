import InfoGeometry.External.Auto.KleinBottle
import InfoGeometry.Clifford.Pin55ReflectionGlide
import Mathlib.Tactic

/-!
# Full affine inversion is not a free glide action

The supplied map `x ↦ -x + (1/2,...,1/2)` has a fixed point and squares to
identity. It must not be used as a free deck transformation of the proposed
Euclidean covering. Its determinant sign does not repair the fixed point.

The positive results below reuse the existing complex Klein glide and the
existing split-coordinate pair glide. They assert their actual pointwise
laws, not a quotient manifold, a Pin bundle, or a homology computation.
-/

namespace InfoGeometry.Topology.AffineDeckFixedPointSeparation

abbrev FiveSpace := Fin 5 → ℝ

/-- Affine inversion with an arbitrary translation vector. -/
def affineInversion (c x : FiveSpace) : FiveSpace := c - x

theorem affineInversion_involutive (c x : FiveSpace) :
    affineInversion c (affineInversion c x) = x := by
  unfold affineInversion
  abel

/-- Translating full inversion moves its fixed point; it does not remove it. -/
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

/-- The exact affine map from the attachment. -/
def proposedDeck : FiveSpace → FiveSpace := affineInversion (fun _ => 1 / 2)

theorem proposedDeck_fixed : proposedDeck (fun _ => 1 / 4) = fun _ => 1 / 4 := by
  ext i
  norm_num [proposedDeck, affineInversion]

theorem proposedDeck_square (x : FiveSpace) : proposedDeck (proposedDeck x) = x :=
  affineInversion_involutive _ x

/-- The fixed-point transformation is nontrivial. -/
theorem proposedDeck_ne_identity : proposedDeck ≠ id := by
  intro h
  have h0 := congrArg (fun f : FiveSpace → FiveSpace => f 0 0) h
  norm_num [proposedDeck, affineInversion] at h0

/-- Literal obstruction to the proposed free action. -/
theorem proposedDeck_not_fixedPointFree : ¬ ∀ x, proposedDeck x ≠ x := by
  intro h
  exact h (fun _ => 1 / 4) proposedDeck_fixed

/-- A negative determinant alone is insufficient to establish freeness. -/
theorem proposed_linearPart_det :
    Matrix.det (Matrix.diagonal (fun _ : Fin 5 => (-1 : ℝ))) = -1 := by
  rw [Matrix.det_diagonal]
  norm_num

/-- The existing Klein glide, unlike full inversion, has no fixed point. -/
theorem existingKleinGlide_no_fixed (z : ℂ) : KleinBottle.G z ≠ z := by
  intro h
  have hre := congrArg Complex.re h
  simp [KleinBottle.G] at hre <;> linarith

/-- A five-real-dimensional product extension of the existing Klein glide. -/
def productGlide (x : ℂ × (Fin 3 → ℝ)) : ℂ × (Fin 3 → ℝ) :=
  (KleinBottle.G x.1, x.2)

theorem productGlide_no_fixed (x : ℂ × (Fin 3 → ℝ)) : productGlide x ≠ x := by
  intro h
  exact existingKleinGlide_no_fixed x.1 (congrArg Prod.fst h)

theorem productGlide_square (x : ℂ × (Fin 3 → ℝ)) :
    productGlide (productGlide x) = (x.1 + 2, x.2) := by
  apply Prod.ext
  · exact KleinBottle.glide_reflection_sq x.1
  · rfl

/-- The separate pre-existing split pair glide is also fixed-point free.
It flips two coordinates and is not identified with the five-space inversion. -/
theorem existingSplitPairGlide_no_fixed
    (x : InfoGeometry.Clifford.Pin55ReflectionGlide.Split55) :
    InfoGeometry.Clifford.Pin55ReflectionGlide.glide x ≠ x := by
  intro h
  have hp := congrArg
    (fun y : InfoGeometry.Clifford.Pin55ReflectionGlide.Split55 => y.p 1) h
  norm_num [InfoGeometry.Clifford.Pin55ReflectionGlide.glide,
    InfoGeometry.Clifford.Pin55ReflectionGlide.translateP,
    InfoGeometry.Clifford.Pin55ReflectionGlide.pinReflection,
    InfoGeometry.Clifford.Pin55ReflectionGlide.addAtOne,
    InfoGeometry.Clifford.Pin55ReflectionGlide.flipFirst] at hp <;> linarith

end InfoGeometry.Topology.AffineDeckFixedPointSeparation
