import InfoGeometry.Algebra.ChiralOperatorSymbolProjection
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Mirror transport of a symbolic operator projection

The operator mirror is required to be multiplicative and to intertwine the
inclusion/readout pair.  Under those explicit hypotheses, both the visible
symbol projection and its hidden defect sector are transported equivariantly.
-/

namespace InfoGeometry.Algebra

variable {R Z E : Type*}
  [CommRing R]
  [AddCommGroup Z] [Module R Z]
  [Ring E] [Algebra R E]

structure SymbolProjectionMirrorData
    (ι : Z →ₗ[R] E) (σ : E →ₗ[R] Z) where
  mirrorOperator : E →ₗ[R] E
  mirrorSymbol : Z →ₗ[R] Z
  mirrorOperator_mul :
    ∀ X Y, mirrorOperator (X * Y) =
      mirrorOperator X * mirrorOperator Y
  mirror_inclusion :
    mirrorOperator.comp ι = ι.comp mirrorSymbol
  mirror_readout :
    mirrorSymbol.comp σ = σ.comp mirrorOperator

/-- Trivial identity instance of SymbolProjectionMirrorData. -/
def idSymbolProjectionMirrorData (ι : Z →ₗ[R] E) (σ : E →ₗ[R] Z) :
    SymbolProjectionMirrorData ι σ where
  mirrorOperator := LinearMap.id
  mirrorSymbol := LinearMap.id
  mirrorOperator_mul _ _ := rfl
  mirror_inclusion := by ext; rfl
  mirror_readout := by ext; rfl

theorem mirror_symbolProjection
    {ι : Z →ₗ[R] E} {σ : E →ₗ[R] Z}
    (D : SymbolProjectionMirrorData ι σ) (X : E) :
    D.mirrorOperator (symbolProjection ι σ X) =
      symbolProjection ι σ (D.mirrorOperator X) := by
  calc
    D.mirrorOperator (symbolProjection ι σ X) =
        D.mirrorOperator (ι (σ X)) := rfl
    _ = ι (D.mirrorSymbol (σ X)) := by
      simpa using congrArg (fun f => f (σ X)) D.mirror_inclusion
    _ = ι (σ (D.mirrorOperator X)) := by
      rw [show D.mirrorSymbol (σ X) = σ (D.mirrorOperator X) by
        simpa using congrArg (fun f => f X) D.mirror_readout]
    _ = symbolProjection ι σ (D.mirrorOperator X) := rfl

theorem mirror_symbolDefect
    {ι : Z →ₗ[R] E} {σ : E →ₗ[R] Z}
    (D : SymbolProjectionMirrorData ι σ) (X : E) :
    D.mirrorOperator (symbolDefect ι σ X) =
      symbolDefect ι σ (D.mirrorOperator X) := by
  simp only [symbolDefect, map_sub, mirror_symbolProjection]

theorem mirror_projectedOperatorMul
    {ι : Z →ₗ[R] E} {σ : E →ₗ[R] Z}
    (D : SymbolProjectionMirrorData ι σ) (x y : Z) :
    D.mirrorSymbol (projectedOperatorMul ι σ x y) =
      projectedOperatorMul ι σ (D.mirrorSymbol x)
        (D.mirrorSymbol y) := by
  calc
    D.mirrorSymbol (projectedOperatorMul ι σ x y) =
        D.mirrorSymbol (σ (ι x * ι y)) := rfl
    _ = σ (D.mirrorOperator (ι x * ι y)) := by
      simpa using congrArg (fun f => f (ι x * ι y)) D.mirror_readout
    _ = σ (D.mirrorOperator (ι x) * D.mirrorOperator (ι y)) := by
      rw [D.mirrorOperator_mul]
    _ = σ (ι (D.mirrorSymbol x) * ι (D.mirrorSymbol y)) := by
      rw [show D.mirrorOperator (ι x) = ι (D.mirrorSymbol x) by
        simpa using congrArg (fun f => f x) D.mirror_inclusion]
      rw [show D.mirrorOperator (ι y) = ι (D.mirrorSymbol y) by
        simpa using congrArg (fun f => f y) D.mirror_inclusion]
    _ = projectedOperatorMul ι σ (D.mirrorSymbol x)
        (D.mirrorSymbol y) := rfl

end InfoGeometry.Algebra
