import InfoGeometry.Projective.KleinQuadricPlucker
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic

/-!
# Exterior/Grassmannian twistor line bridge

This owner uses the native six-coordinate Pluecker carrier.  A pair of
homogeneous four-vectors determines a decomposable bivector (a Grassmannian
line), and the Klein relation is exposed as its boundary equation.  No new
Grassmannian or twistor structure is introduced.
-/

namespace InfoGeometry.Canonical.ExteriorGrassmannianTwistorBridge

open InfoGeometry.Projective.KleinQuadricPlucker
open InfoGeometry.Projective.KleinQuadricPlucker.Plucker6

abbrev Vec4 := InfoGeometry.Projective.KleinQuadricPlucker.Vec4 ℝ
abbrev Plucker6 := InfoGeometry.Projective.KleinQuadricPlucker.Plucker6 ℝ

open ExteriorAlgebra

def exteriorTwistorBivector {V : Type*} [AddCommGroup V] [Module ℝ V]
    (X Y : V) : ExteriorAlgebra ℝ V :=
  ι ℝ X * ι ℝ Y

theorem exteriorTwistorBivector_self_zero
    {V : Type*} [AddCommGroup V] [Module ℝ V] (X : V) :
    exteriorTwistorBivector X X = 0 := by
  exact ι_sq_zero X

theorem exteriorTwistorBivector_swap
    {V : Type*} [AddCommGroup V] [Module ℝ V] (X Y : V) :
    exteriorTwistorBivector Y X = -exteriorTwistorBivector X Y := by
  apply eq_neg_of_add_eq_zero_left
  simp [exteriorTwistorBivector, add_comm]

def twistorLine (X Y : Vec4) : Plucker6 :=
  pluckerLine X Y

def pluckerNeg (P : Plucker6) : Plucker6 where
  p01 := -P.p01
  p02 := -P.p02
  p03 := -P.p03
  p12 := -P.p12
  p13 := -P.p13
  p23 := -P.p23

def pluckerZero : Plucker6 where
  p01 := 0
  p02 := 0
  p03 := 0
  p12 := 0
  p13 := 0
  p23 := 0

theorem twistorLine_swap (X Y : Vec4) :
    twistorLine Y X = pluckerNeg (twistorLine X Y) := by
  rcases X with ⟨x0, x1, x2, x3⟩
  rcases Y with ⟨y0, y1, y2, y3⟩
  apply Plucker6.ext <;> simp [twistorLine, pluckerLine, pluckerNeg] <;> ring

theorem twistorLine_self (X : Vec4) :
    twistorLine X X = pluckerZero := by
  rcases X with ⟨x0, x1, x2, x3⟩
  apply Plucker6.ext <;> simp [twistorLine, pluckerLine, pluckerZero] <;> ring

theorem twistorLine_on_klein (X Y : Vec4) :
    kleinQ (twistorLine X Y) = 0 := by
  exact kleinQ_pluckerLine X Y

theorem twistorLine_scale_left (l : ℝ) (X Y : Vec4) :
    twistorLine (Vec4.scale l X) Y = scale l (twistorLine X Y) := by
  exact pluckerLine_scale_left l X Y

theorem twistorLine_scale_right (l : ℝ) (X Y : Vec4) :
    twistorLine X (Vec4.scale l Y) = scale l (twistorLine X Y) := by
  exact pluckerLine_scale_right l X Y

theorem twistorLine_projective_rescaling
    (u v : ℝ) (X Y : Vec4) :
    twistorLine (Vec4.scale u X) (Vec4.scale v Y) =
      scale (u * v) (twistorLine X Y) := by
  rw [twistorLine_scale_left, twistorLine_scale_right]
  rcases twistorLine X Y with ⟨p01, p02, p03, p12, p13, p23⟩
  apply Plucker6.ext <;> simp [scale] <;> ring

end InfoGeometry.Canonical.ExteriorGrassmannianTwistorBridge
