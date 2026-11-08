import InfoGeometry.Canonical.AlbertPeirceChiralFrameEmbedding
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Canonical

open InfoGeometry.Algebra

/-! A coordinate quadratic bridge for the local matrix readout.
This file proves a determinant identity only; it does not identify this cone
with a physical mass shell without an additional metric-preserving map. -/

def splitQuadratic (x : RealSplitOct) : ℝ :=
  x.a * x.b - (x.x0 * x.y0 + x.x1 * x.y1 + x.x2 * x.y2)

abbrev KinematicCoordinates := InfoGeometry.Algebra.FiniteSpin.Vec4R

def channelCoordinates (M : Matrix (Fin 2) (Fin 2) ℝ) : KinematicCoordinates :=
  fun i => match i with
  | 0 => M 0 0
  | 1 => M 1 1
  | 2 => M 0 1
  | 3 => M 1 0

def channelQuadratic (p : KinematicCoordinates) : ℝ :=
  p 0 * p 1 - p 2 * p 3

theorem embedRealSplit_quadratic_transport (M : Matrix (Fin 2) (Fin 2) ℝ) :
    splitQuadratic (embedRealSplit M) = channelQuadratic (channelCoordinates M) := by
  simp [splitQuadratic, channelQuadratic, channelCoordinates, embedRealSplit]

def peirceNullCone : Set KinematicCoordinates :=
  {p | channelQuadratic p = 0}

theorem embedRealSplit_mem_peirceNullCone_iff (M : Matrix (Fin 2) (Fin 2) ℝ) :
    channelCoordinates M ∈ peirceNullCone ↔
      splitQuadratic (embedRealSplit M) = 0 := by
  rw [embedRealSplit_quadratic_transport]
  rfl

end InfoGeometry.Canonical
