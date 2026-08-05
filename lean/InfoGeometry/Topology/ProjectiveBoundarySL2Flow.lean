import Mathlib
import InfoGeometry.Topology.ProjectiveBoundarySL2Composition

namespace InfoGeometry.Topology

/-!
# One-parameter families of determinant-one boundary blocks

The algebraic flow laws are separated from continuity.  This prevents an
algebraic representation from being promoted to a topological flow without a
genuine continuity proof on the chosen quotient topology.
-/

def SL2BoundaryMatrix.identity
    {R : Type*} [CommRing R] : SL2BoundaryMatrix R where
  matrix := ![![1, 0], ![0, 1]]
  det_eq_one := by simp [det2]

theorem SL2BoundaryMatrix.identity_applyPair
    {R : Type*} [CommRing R] (p : UnimodularPair R) :
    SL2BoundaryMatrix.identity.applyPair p = p := by
  ext <;> simp [SL2BoundaryMatrix.identity, SL2BoundaryMatrix.applyPair]

theorem SL2BoundaryMatrix.identity_onBoundary
    {R : Type*} [CommRing R] (p : ProjectiveBoundary R) :
    SL2BoundaryMatrix.identity.onBoundary p = p := by
  refine Quotient.inductionOn p ?_
  intro q
  simpa [SL2BoundaryMatrix.onBoundary_mk] using
    congrArg projectiveBoundaryMk (SL2BoundaryMatrix.identity_applyPair q)

structure SL2BoundaryFlow (R : Type*) [CommRing R] where
  act : ℝ → SL2BoundaryMatrix R
  zero_law : act 0 = SL2BoundaryMatrix.identity
  add_law : ∀ s t : ℝ,
    act (s + t) = (act s).mul (act t)

def SL2BoundaryFlow.onBoundary
    {R : Type*} [CommRing R]
    (Φ : SL2BoundaryFlow R) (t : ℝ) :
    ProjectiveBoundary R → ProjectiveBoundary R :=
  (Φ.act t).onBoundary

theorem SL2BoundaryFlow.onBoundary_zero
    {R : Type*} [CommRing R]
    (Φ : SL2BoundaryFlow R) (p : ProjectiveBoundary R) :
    Φ.onBoundary 0 p = p := by
  rw [SL2BoundaryFlow.onBoundary, Φ.zero_law]
  exact SL2BoundaryMatrix.identity_onBoundary p

theorem SL2BoundaryFlow.onBoundary_add
    {R : Type*} [CommRing R]
    (Φ : SL2BoundaryFlow R) (s t : ℝ) (p : ProjectiveBoundary R) :
    Φ.onBoundary (s + t) p =
      Φ.onBoundary s (Φ.onBoundary t p) := by
  rw [SL2BoundaryFlow.onBoundary, Φ.add_law]
  exact SL2BoundaryMatrix.mul_onBoundary (Φ.act s) (Φ.act t) p

structure ContinuousSL2BoundaryFlow (R : Type*) [CommRing R]
    [TopologicalSpace (ProjectiveBoundary R)] where
  algebraic : SL2BoundaryFlow R
  continuous_action : Continuous
    (fun p : ℝ × ProjectiveBoundary R =>
      algebraic.onBoundary p.1 p.2)

end InfoGeometry.Topology
