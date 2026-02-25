import Architect
import InfoGeometry.Geometry.DualFlat

namespace InfoGeometry.Research.Cayley

open InfoGeometry.Geometry.DualFlat

@[blueprint "def:cayley-bridge"]
structure Bridge (U B : Type*) where
  toBounded   : U → B
  toUnbounded : B → U
  left_inv    : Function.LeftInverse toUnbounded toBounded
  right_inv   : Function.RightInverse toUnbounded toBounded

@[blueprint "def:compatible-dual-flat"]
structure CompatibleDualFlat
    {U B : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
    [NormedAddCommGroup B] [InnerProductSpace ℝ B] [CompleteSpace B]
    (C : Bridge U B) (SU : DualFlatStructure U) where
  SB : DualFlatStructure B
  D_transport : ∀ x y : U, divergence SB (C.toBounded x) (C.toBounded y) = divergence SU x y
  grad_transport : ∀ x : U, C.toBounded (nabla SU x) = nabla SB (C.toBounded x)

def identityBridge (E : Type*) : Bridge E E where
  toBounded x := x
  toUnbounded x := x
  left_inv _ := rfl
  right_inv _ := rfl

def identityCompatibleGeometry
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (S : DualFlatStructure E) : CompatibleDualFlat (identityBridge E) S where
  SB := S
  D_transport _ _ := rfl
  grad_transport _ := rfl

@[blueprint "thm:cayley-pythagorean-invariance"]
theorem cayley_pythagorean_invariance
    {U B : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
    [NormedAddCommGroup B] [InnerProductSpace ℝ B] [CompleteSpace B]
    (C : Bridge U B) (SU : DualFlatStructure U)
    (hC : CompatibleDualFlat C SU)
    (Prior Posterior Alt : U)
    (hproj : inner ℝ (nabla SU Prior - nabla SU Posterior) (Alt - Posterior) = 0) :
    divergence hC.SB (C.toBounded Alt) (C.toBounded Prior)
      = divergence hC.SB (C.toBounded Alt) (C.toBounded Posterior)
      + divergence hC.SB (C.toBounded Posterior) (C.toBounded Prior) := by
  have hU : divergence SU Alt Prior = divergence SU Alt Posterior + divergence SU Posterior Prior :=
    bregman_pythagorean SU Alt Posterior Prior hproj
  calc
    divergence hC.SB (C.toBounded Alt) (C.toBounded Prior)
        = divergence SU Alt Prior := by rw [hC.D_transport]
    _ = divergence SU Alt Posterior + divergence SU Posterior Prior := hU
    _ = divergence hC.SB (C.toBounded Alt) (C.toBounded Posterior)
        + divergence hC.SB (C.toBounded Posterior) (C.toBounded Prior) := by
          rw [hC.D_transport, hC.D_transport]

end InfoGeometry.Research.Cayley
