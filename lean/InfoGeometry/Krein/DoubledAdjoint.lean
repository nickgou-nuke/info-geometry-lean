/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Krein.DoubledSpace
import InfoGeometry.Algebra.FiniteSpinAlgebra
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

@[simp] theorem doubledToHilbert_eq_ofDoubledContinuousLinearEquiv :
    doubledToHilbert (E := E) = HilbertDoubled.ofDoubledContinuousLinearEquiv (E := E) := rfl

@[simp] theorem doubledToHilbert_apply (u : DoubledSpace E) :
    doubledToHilbert (E := E) u = HilbertDoubled.ofDoubledContinuousLinearEquiv (E := E) u := rfl

/-- Hilbert adjoint on doubled-space endomorphisms, transported through `HilbertDoubled`. -/
noncomputable def doubledAdjoint (A : DoubledEnd E) : DoubledEnd E :=
  ContinuousLinearMap.adjoint A

/-- Krein adjoint on doubled space, using `J = spectral_epsilon`: `A♯ = J ∘ A† ∘ J`. -/
noncomputable def doubledKreinAdjoint (A : DoubledEnd E) : DoubledEnd E :=
  (spectral_epsilon (E := E)).comp ((doubledAdjoint (E := E) A).comp (spectral_epsilon (E := E)))

@[simp] lemma doubledKreinAdjoint_apply (A : DoubledEnd E) (x : DoubledSpace E) :
    doubledKreinAdjoint (E := E) A x =
      (spectral_epsilon (E := E)) ((doubledAdjoint (E := E) A) ((spectral_epsilon (E := E)) x)) := rfl

/-- The Hilbert adjoint fixes the real doubled-space sheet swap. -/
lemma doubledAdjoint_modular_j :
    doubledAdjoint (E := E) (modular_j (E := E)) = modular_j (E := E) := by
  symm
  refine (ContinuousLinearMap.eq_adjoint_iff
    (A := modular_j (E := E)) (B := modular_j (E := E))).2 ?_
  intro u v
  simp [modular_j, WithLp.prod_inner_apply, add_comm]

/-- On the canonical doubled carrier, the sheet swap is skew-adjoint for the
Krein metric defined by `spectral_epsilon`. -/
theorem modular_j_kreinSkewAdjoint :
    KreinSpace.IsKreinSkewAdjoint (H := DoubledSpace E) (modular_j (E := E)) := by
  change KreinSpace.kreinAdjoint (H := DoubledSpace E) (modular_j (E := E)) =
    -(modular_j (E := E))
  rw [KreinSpace.kreinAdjoint]
  have hε : KreinSpace.jCLM (H := DoubledSpace E) = spectral_epsilon (E := E) := by
    apply ContinuousLinearMap.ext
    intro u
    apply DoubledSpace.ext <;> rfl
  rw [hε, doubledAdjoint_modular_j]
  apply ContinuousLinearMap.ext
  intro u
  apply DoubledSpace.ext <;> simp [modular_j, spectral_epsilon]

/-- Conjugation of doubled operators by the modular sheet swap commutes with
the Krein adjoint.  The result is a statement about actual operators on the
real doubled carrier, not merely about the two spectral projectors. -/
theorem kreinAdjoint_modular_j_sandwich (A : DoubledEnd E) :
    KreinSpace.kreinAdjoint (H := DoubledSpace E)
        ((modular_j (E := E)).comp (A.comp (modular_j (E := E)))) =
      (modular_j (E := E)).comp
        ((KreinSpace.kreinAdjoint (H := DoubledSpace E) A).comp
          (modular_j (E := E))) := by
  exact KreinSpace.kreinAdjoint_sandwich_of_skewAdjoint
    (modular_j (E := E)) A modular_j_kreinSkewAdjoint

end InfoGeometry.Krein
