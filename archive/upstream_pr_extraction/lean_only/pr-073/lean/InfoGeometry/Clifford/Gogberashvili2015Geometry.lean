import InfoGeometry.Clifford.SplitOctonionicDiracCoordinates

/-!
# Geometrical Applications of Split Octonions (2015), equations (1), (8)--(10)

The paper's signal/world-line coordinates are placed in the existing native
`ZornCell ℝ` carrier.  The coordinate order is the one used by the repository's
coordinate owner: scalar, `j₁ j₂ j₃`, `I`, then `J₁ J₂ J₃`.
-/

namespace InfoGeometry.Clifford.Gogberashvili2015Geometry

open InfoGeometry.Clifford.SplitOctonionicDiracCoordinates
open InfoGeometry.Clifford.GogberashviliSplitOctonionBasis
open InfoGeometry.Algebra.Zorn.ConcreteComposition
open InfoGeometry.Algebra.Zorn.ConcreteComposition.ZornCell

structure Worldline where
  omega : ℝ
  lambda1 : ℝ
  lambda2 : ℝ
  lambda3 : ℝ
  x1 : ℝ
  x2 : ℝ
  x3 : ℝ
  c : ℝ
  t : ℝ

def coordinates (s : Worldline) : Coordinates :=
  { x0 := s.omega
    x1 := s.x1
    x2 := s.x2
    x3 := s.x3
    x4 := s.c * s.t
    x5 := s.lambda1
    x6 := s.lambda2
    x7 := s.lambda3 }

def signal (s : Worldline) : ZornCell ℝ :=
  element (coordinates s)

def normSquared (s : Worldline) : ℝ :=
  s.omega ^ 2 - s.lambda1 ^ 2 - s.lambda2 ^ 2 - s.lambda3 ^ 2 +
    s.x1 ^ 2 + s.x2 ^ 2 + s.x3 ^ 2 - (s.c * s.t) ^ 2

def spatialSquared (s : Worldline) : ℝ :=
  s.x1 ^ 2 + s.x2 ^ 2 + s.x3 ^ 2

def lambdaSquared (s : Worldline) : ℝ :=
  s.lambda1 ^ 2 + s.lambda2 ^ 2 + s.lambda3 ^ 2

def physicalEvent (s : Worldline) : Prop :=
  0 ≤ normSquared s

def timelikeVectorPart (s : Worldline) : Prop :=
  spatialSquared s < (s.c * s.t) ^ 2 + lambdaSquared s

theorem signal_mul_conjugate (s : Worldline) :
    signal s * element (conjugate (coordinates s)) =
      scalarElement (normSquared s) := by
  convert element_mul_conjugate (coordinates s) using 1 <;>
    simp [signal, normSquared, coordinates, quadratic, spatialSquared,
      lambdaSquared, mul_pow] <;> ring

theorem conjugate_signal_mul (s : Worldline) :
    element (conjugate (coordinates s)) * signal s =
      scalarElement (normSquared s) := by
  convert element_mul_conjugate (conjugate (coordinates s)) using 1 <;>
    simp [signal, conjugate, conjugate_involutive, normSquared, coordinates,
      quadratic, lambdaSquared, spatialSquared, mul_pow] <;> ring

theorem normSquared_expanded (s : Worldline) :
    normSquared s =
      s.omega ^ 2 - lambdaSquared s + spatialSquared s - (s.c * s.t) ^ 2 := by
  simp [normSquared, lambdaSquared, spatialSquared]
  ring

theorem physical_event_norm_nonnegative (s : Worldline)
    (h : physicalEvent s) : 0 ≤ normSquared s := h

theorem timelike_vector_part_expanded (s : Worldline) :
    timelikeVectorPart s ↔
      spatialSquared s < (s.c * s.t) ^ 2 + lambdaSquared s := by
  rfl

end InfoGeometry.Clifford.Gogberashvili2015Geometry
