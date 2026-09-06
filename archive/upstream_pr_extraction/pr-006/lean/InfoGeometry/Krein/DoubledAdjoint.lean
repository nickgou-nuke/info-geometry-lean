import InfoGeometry.Krein.DoubledSpace
import InfoGeometry.Krein.HilbertBridge
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# InfoGeometry.Krein.DoubledAdjoint

Canonical adjoint/Krein-adjoint operations on `DoubledSpace E`.
-/

namespace InfoGeometry.Krein

variable {E : Type _}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Endomorphism type on doubled space. -/
abbrev DoubledEnd (E : Type _) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] :=
  DoubledSpace E →L[ℝ] DoubledSpace E

/-- Canonical linear isometry from raw doubled coordinates to `WithLp` Hilbert doubled space. -/
noncomputable abbrev doubledToHilbert : DoubledSpace E ≃L[ℝ] HilbertDoubled E :=
  (WithLp.prodContinuousLinearEquiv (p := (2 : ENNReal)) (𝕜 := ℝ) (α := E) (β := E)).symm

/-- Hilbert adjoint on doubled-space endomorphisms, transported through `HilbertDoubled`. -/
noncomputable def doubledAdjoint (A : DoubledEnd E) : DoubledEnd E :=
  let e := doubledToHilbert (E := E)
  let Ah : HilbertDoubled E →L[ℝ] HilbertDoubled E :=
    (e : DoubledSpace E →L[ℝ] HilbertDoubled E).comp
      (A.comp ((e.symm : HilbertDoubled E →L[ℝ] DoubledSpace E)))
  (e.symm : HilbertDoubled E →L[ℝ] DoubledSpace E).comp
    ((ContinuousLinearMap.adjoint Ah).comp (e : DoubledSpace E →L[ℝ] HilbertDoubled E))

/-- Krein adjoint on doubled space, using `J = spectralEpsilon`: `A♯ = J ∘ A† ∘ J`. -/
noncomputable def doubledKreinAdjoint (A : DoubledEnd E) : DoubledEnd E :=
  (spectralEpsilon (E := E)).comp ((doubledAdjoint (E := E) A).comp (spectralEpsilon (E := E)))

@[simp] lemma doubledKreinAdjoint_apply (A : DoubledEnd E) (x : DoubledSpace E) :
    doubledKreinAdjoint (E := E) A x =
      (spectralEpsilon (E := E)) ((doubledAdjoint (E := E) A) ((spectralEpsilon (E := E)) x)) := rfl

end InfoGeometry.Krein
