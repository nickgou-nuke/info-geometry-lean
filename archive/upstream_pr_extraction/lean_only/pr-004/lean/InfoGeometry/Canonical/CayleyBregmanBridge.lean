import Architect
import InfoGeometry.Geometry.DualFlat

namespace InfoGeometry.Canonical.Cayley

open InfoGeometry.Geometry.DualFlat

@[blueprint "def:cayley-bridge"]
structure Bridge (U B : Type*) where
  toBounded   : U → B
  toUnbounded : B → U
  left_inv    : Function.LeftInverse toUnbounded toBounded
  right_inv   : Function.RightInverse toUnbounded toBounded

/-- Canonical name for a Cayley transport equivalence. -/
abbrev CayleyBridge (U B : Type*) := Bridge U B

/-- Canonical naming alias for a Cayley transport equivalence. -/
abbrev CayleyEquivalence (U B : Type*) := CayleyBridge U B

@[blueprint "def:compatible-dual-flat"]
structure CompatibleDualFlat
    {U B : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
    [NormedAddCommGroup B] [InnerProductSpace ℝ B] [CompleteSpace B]
    (C : CayleyBridge U B) (SU : DualFlatStructure U) where
  SB : DualFlatStructure B
  D_transport : ∀ x y : U, divergence SB (C.toBounded x) (C.toBounded y) = divergence SU x y
  grad_transport : ∀ x : U, C.toBounded (nabla SU x) = nabla SB (C.toBounded x)

/-- Canonical name for dual-flat compatibility under Cayley transport. -/
abbrev CayleyCompatibleDualFlat
    {U B : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
    [NormedAddCommGroup B] [InnerProductSpace ℝ B] [CompleteSpace B]
    (C : CayleyBridge U B) (SU : DualFlatStructure U) :=
  CompatibleDualFlat C SU

/-- Canonical naming alias for dual-flat compatibility under Cayley transport. -/
abbrev CayleyDualFlatCompatibility
    {U B : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
    [NormedAddCommGroup B] [InnerProductSpace ℝ B] [CompleteSpace B]
    (C : CayleyBridge U B) (SU : DualFlatStructure U) :=
  CayleyCompatibleDualFlat C SU

def cayleyIdentityBridge (E : Type*) : CayleyBridge E E where
  toBounded x := x
  toUnbounded x := x
  left_inv _ := rfl
  right_inv _ := rfl

def cayleyIdentityCompatibleGeometry
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (S : DualFlatStructure E) : CayleyCompatibleDualFlat (cayleyIdentityBridge E) S where
  SB := S
  D_transport _ _ := rfl
  grad_transport _ := rfl

/-- Legacy compatibility alias for `cayleyIdentityBridge`. -/
abbrev identityBridge (E : Type*) : CayleyBridge E E := cayleyIdentityBridge E

attribute [deprecated cayleyIdentityBridge (since := "2026-02-26")] identityBridge

/-- Legacy compatibility alias for `cayleyIdentityCompatibleGeometry`. -/
abbrev identityCompatibleGeometry
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (S : DualFlatStructure E) : CayleyCompatibleDualFlat (cayleyIdentityBridge E) S :=
  cayleyIdentityCompatibleGeometry S

attribute [deprecated cayleyIdentityCompatibleGeometry (since := "2026-02-26")]
  identityCompatibleGeometry

@[blueprint "thm:cayley-pythagorean-invariance"]
theorem cayley_pythagorean_invariance
    {U B : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
    [NormedAddCommGroup B] [InnerProductSpace ℝ B] [CompleteSpace B]
    (C : CayleyBridge U B) (SU : DualFlatStructure U)
    (hC : CayleyCompatibleDualFlat C SU)
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

/-- Canonical camelCase alias for Cayley Pythagorean invariance. -/
theorem cayleyPythagoreanInvariance
    {U B : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
    [NormedAddCommGroup B] [InnerProductSpace ℝ B] [CompleteSpace B]
    (C : CayleyBridge U B) (SU : DualFlatStructure U)
    (hC : CayleyCompatibleDualFlat C SU)
    (prior posterior alt : U)
    (hproj : inner ℝ (nabla SU prior - nabla SU posterior) (alt - posterior) = 0) :
    divergence hC.SB (C.toBounded alt) (C.toBounded prior)
      = divergence hC.SB (C.toBounded alt) (C.toBounded posterior)
      + divergence hC.SB (C.toBounded posterior) (C.toBounded prior) := by
  simpa using
    cayley_pythagorean_invariance
      (C := C) (SU := SU) (hC := hC)
      (Prior := prior) (Posterior := posterior) (Alt := alt) hproj

attribute [deprecated cayleyPythagoreanInvariance (since := "2026-02-26")]
  cayley_pythagorean_invariance

end InfoGeometry.Canonical.Cayley
