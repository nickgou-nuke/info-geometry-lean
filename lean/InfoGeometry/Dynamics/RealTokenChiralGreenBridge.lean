import InfoGeometry.Dynamics.RealTokenChiralHodgeBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Green/resolvent contract for the chiral token Laplacian

The Hodge--Dirac square need not be invertible on the whole carrier.  A Green
operator is therefore recorded together with the projector onto its regular
sector.  The two-sided Green identities are the exact algebraic boundary of
the resolvent claim.
-/

namespace InfoGeometry.Dynamics

noncomputable section

variable {V : Type*} [Fintype V]

abbrev RealTokenGreenOperator :=
  RealTokenDoubledSpace (V := V) →ₗ[ℝ] RealTokenDoubledSpace (V := V)

structure RealTokenChiralGreenWitness
    (W : RealTokenChiralHodgeWitness (V := V)) where
  green : RealTokenGreenOperator (V := V)
  regularProjector : RealTokenGreenOperator (V := V)
  left_green : W.hodgeLaplacian.comp green = regularProjector
  right_green : green.comp W.hodgeLaplacian = regularProjector
  green_regular : green.comp regularProjector = green

theorem realTokenChiralGreen_left
    {W : RealTokenChiralHodgeWitness (V := V)}
    (G : RealTokenChiralGreenWitness W) :
    W.hodgeLaplacian.comp G.green = G.regularProjector :=
  G.left_green

theorem realTokenChiralGreen_right
    {W : RealTokenChiralHodgeWitness (V := V)}
    (G : RealTokenChiralGreenWitness W) :
    G.green.comp W.hodgeLaplacian = G.regularProjector :=
  G.right_green

theorem realTokenChiralGreen_two_sided_on_regular
    {W : RealTokenChiralHodgeWitness (V := V)}
    (G : RealTokenChiralGreenWitness W) :
    G.regularProjector.comp G.green = G.green := by
  calc
    G.regularProjector.comp G.green =
        (G.green.comp W.hodgeLaplacian).comp G.green := by
      rw [G.right_green]
    _ = G.green.comp (W.hodgeLaplacian.comp G.green) := by
      exact LinearMap.comp_assoc G.green W.hodgeLaplacian G.green
    _ = G.green.comp G.regularProjector := by
      rw [G.left_green]
    _ = G.green := G.green_regular

theorem realTokenChiralGreen_regularProjector_idempotent
    {W : RealTokenChiralHodgeWitness (V := V)}
    (G : RealTokenChiralGreenWitness W) :
    G.regularProjector.comp G.regularProjector = G.regularProjector := by
  calc
    G.regularProjector.comp G.regularProjector =
        (W.hodgeLaplacian.comp G.green).comp G.regularProjector := by
      rw [G.left_green]
    _ = W.hodgeLaplacian.comp (G.green.comp G.regularProjector) := by
      exact LinearMap.comp_assoc G.regularProjector G.green W.hodgeLaplacian
    _ = W.hodgeLaplacian.comp G.green := by
      rw [G.green_regular]
    _ = G.regularProjector := G.left_green

theorem realTokenChiralGreen_regularProjector_commutes_laplacian
    {W : RealTokenChiralHodgeWitness (V := V)}
    (G : RealTokenChiralGreenWitness W) :
    G.regularProjector.comp W.hodgeLaplacian =
      W.hodgeLaplacian.comp G.regularProjector := by
  apply LinearMap.ext
  intro x
  have hleft (y : RealTokenDoubledSpace (V := V)) :=
    congrArg (fun T : RealTokenGreenOperator (V := V) => T y) G.left_green
  have hright (y : RealTokenDoubledSpace (V := V)) :=
    congrArg (fun T : RealTokenGreenOperator (V := V) => T y) G.right_green
  change G.regularProjector (W.hodgeLaplacian x) =
    W.hodgeLaplacian (G.regularProjector x)
  calc
    G.regularProjector (W.hodgeLaplacian x) =
        G.green (W.hodgeLaplacian (W.hodgeLaplacian x)) :=
      (hright (W.hodgeLaplacian x)).symm
    _ = G.regularProjector (W.hodgeLaplacian x) := by
      simpa [LinearMap.comp_apply] using hright (W.hodgeLaplacian x)
    _ = W.hodgeLaplacian (G.green (W.hodgeLaplacian x)) :=
      (hleft (W.hodgeLaplacian x)).symm
    _ = W.hodgeLaplacian (G.regularProjector x) := by
      congr 1
      simpa [LinearMap.comp_apply] using hright x

theorem realTokenChiralGreen_regularProjector_range_le_laplacian_range
    {W : RealTokenChiralHodgeWitness (V := V)}
    (G : RealTokenChiralGreenWitness W) :
    LinearMap.range G.regularProjector ≤ LinearMap.range W.hodgeLaplacian := by
  intro y hy
  rcases hy with ⟨x, rfl⟩
  refine ⟨G.green x, ?_⟩
  simpa [LinearMap.comp_apply] using
    congrArg (fun T : RealTokenGreenOperator (V := V) => T x) G.left_green

end
end InfoGeometry.Dynamics
