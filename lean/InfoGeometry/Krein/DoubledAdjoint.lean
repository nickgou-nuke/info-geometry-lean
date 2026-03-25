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

/-- Canonical linear isometry between doubled and Hilbert wrappers. -/
noncomputable abbrev doubledToHilbert : DoubledSpace E ≃L[ℝ] HilbertDoubled E :=
  { toLinearEquiv :=
      { toFun := fun u => ⟨u⟩
        invFun := fun u => (u : DoubledSpace E)
        left_inv := by
          intro u
          rfl
        right_inv := by
          intro u
          apply HilbertDoubled.ext
          rfl
        map_add' := by
          intro u v
          rfl
        map_smul' := by
          intro a u
          rfl }
    continuous_toFun := by
      simpa using (continuous_uliftUp : Continuous (ULift.up : DoubledSpace E → HilbertDoubled E))
    continuous_invFun := by
      simpa using
        (continuous_uliftDown : Continuous (ULift.down : HilbertDoubled E → DoubledSpace E)) }

/-- Hilbert adjoint on doubled-space endomorphisms, transported through `HilbertDoubled`. -/
noncomputable def doubledAdjoint (A : DoubledEnd E) : DoubledEnd E :=
  ContinuousLinearMap.adjoint A

/-- Krein adjoint on doubled space, using `J = spectral_epsilon`: `A♯ = J ∘ A† ∘ J`. -/
noncomputable def doubledKreinAdjoint (A : DoubledEnd E) : DoubledEnd E :=
  (spectral_epsilon (E := E)).comp ((doubledAdjoint (E := E) A).comp (spectral_epsilon (E := E)))

@[simp] lemma doubledKreinAdjoint_apply (A : DoubledEnd E) (x : DoubledSpace E) :
    doubledKreinAdjoint (E := E) A x =
      (spectral_epsilon (E := E)) ((doubledAdjoint (E := E) A) ((spectral_epsilon (E := E)) x)) := rfl

end InfoGeometry.Krein
