import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Complex.Basic

namespace InfoGeometry.Algebra.G2

/--
Conditional `G₂(2)`-style twisting data over a matrix carrier.

The only theorem in this file is the tautological readback of the stored cubic
constraint; no classification or geometric interpretation is proved here.
-/
abbrev G2TwistedSystem (BlockType : Type) [DecidableEq BlockType] [Fintype BlockType] :=
  {omega_twist : Matrix BlockType BlockType ℂ // omega_twist ^ 3 = 1}

namespace G2TwistedSystem

/-- Named projection for the direct matrix carrier. -/
abbrev omega_twist {BlockType : Type} [DecidableEq BlockType] [Fintype BlockType]
    (sys : G2TwistedSystem BlockType) : Matrix BlockType BlockType ℂ :=
  sys.1

/-- Named projection for the defining cubic invariant. -/
abbrev h_cubic_center {BlockType : Type} [DecidableEq BlockType] [Fintype BlockType]
    (sys : G2TwistedSystem BlockType) : omega_twist sys ^ 3 = 1 :=
  sys.2

end G2TwistedSystem

/--
Readback theorem for the stored cubic constraint.
-/
theorem g2_twist_closure {BlockType : Type} [DecidableEq BlockType] [Fintype BlockType]
    (sys : G2TwistedSystem BlockType) :
    sys.omega_twist ^ 3 = 1 := by
  exact sys.h_cubic_center

end InfoGeometry.Algebra.G2
