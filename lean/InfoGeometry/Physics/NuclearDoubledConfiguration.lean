/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Krein.DoubledSpace
import Mathlib.Analysis.Normed.Operator.Prod

/-!
# Paired configuration operators on the native real doubled carrier

The same real configuration map acts on both native doubled legs. This is a
configuration lift, separate from the sheet involutions. It intertwines the
existing sheet exchange, fundamental symmetry, and internal phase axis.
Self-adjoint configuration projectors therefore supply nondegenerate model
corners without identifying a Krein sheet with a Feshbach model space.
-/

noncomputable section

namespace InfoGeometry.Physics.NuclearDoubledConfiguration

open InfoGeometry.Krein
open scoped InnerProductSpace

variable {E F G : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
variable [NormedAddCommGroup G] [InnerProductSpace ℝ G] [CompleteSpace G]

/-- A real configuration map acting on both legs of the native doubled carrier. -/
def pairedLift (A : E →L[ℝ] F) : DoubledSpace E →L[ℝ] DoubledSpace F :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ F F).symm.toContinuousLinearMap.comp
    ((A.prodMap A).comp
      (WithLp.prodContinuousLinearEquiv 2 ℝ E E).toContinuousLinearMap)

@[simp] theorem pairedLift_apply (A : E →L[ℝ] F) (u : DoubledSpace E) :
    pairedLift A u = to_doubled (A (WithLp.fst u)) (A (WithLp.snd u)) := rfl

@[simp] theorem pairedLift_to_doubled (A : E →L[ℝ] F) (x ξ : E) :
    pairedLift A (to_doubled x ξ) = to_doubled (A x) (A ξ) := rfl

@[simp] theorem pairedLift_id :
    pairedLift (ContinuousLinearMap.id ℝ E) =
      ContinuousLinearMap.id ℝ (DoubledSpace E) := by
  apply ContinuousLinearMap.ext
  intro u
  apply DoubledSpace.ext <;> rfl

@[simp] theorem pairedLift_zero : pairedLift (0 : E →L[ℝ] F) = 0 := by
  apply ContinuousLinearMap.ext
  intro u
  apply DoubledSpace.ext <;> simp

@[simp] theorem pairedLift_add (A B : E →L[ℝ] F) :
    pairedLift (A + B) = pairedLift A + pairedLift B := by
  apply ContinuousLinearMap.ext
  intro u
  apply DoubledSpace.ext <;> simp [WithLp.add_fst, WithLp.add_snd]

@[simp] theorem pairedLift_sub (A B : E →L[ℝ] F) :
    pairedLift (A - B) = pairedLift A - pairedLift B := by
  apply ContinuousLinearMap.ext
  intro u
  apply DoubledSpace.ext <;> simp [WithLp.sub_fst, WithLp.sub_snd]

@[simp] theorem pairedLift_smul (c : ℝ) (A : E →L[ℝ] F) :
    pairedLift (c • A) = c • pairedLift A := by
  apply ContinuousLinearMap.ext
  intro u
  apply DoubledSpace.ext <;> simp [WithLp.smul_fst, WithLp.smul_snd]

@[simp] theorem pairedLift_comp (B : F →L[ℝ] G) (A : E →L[ℝ] F) :
    pairedLift (B.comp A) = (pairedLift B).comp (pairedLift A) := by
  apply ContinuousLinearMap.ext
  intro u
  apply DoubledSpace.ext <;> rfl

/-- The paired realization does not identify distinct configuration maps. -/
theorem pairedLift_injective :
    Function.Injective (pairedLift : (E →L[ℝ] F) →
      (DoubledSpace E →L[ℝ] DoubledSpace F)) := by
  intro A B h
  apply ContinuousLinearMap.ext
  intro x
  have hx := congrArg
    (fun T : DoubledSpace E →L[ℝ] DoubledSpace F =>
      WithLp.fst (T (to_doubled x 0))) h
  simpa using hx

/-- An injective configuration map stays injective after native doubling. -/
theorem pairedLift_injective_of (A : E →L[ℝ] F) (hA : Function.Injective A) :
    Function.Injective (pairedLift A) := by
  intro u v h
  apply DoubledSpace.ext
  · apply hA
    simpa using congrArg WithLp.fst h
  · apply hA
    simpa using congrArg WithLp.snd h

theorem pairedLift_comp_spectral_epsilon (A : E →L[ℝ] F) :
    (pairedLift A).comp (spectral_epsilon (E := E)) =
      (spectral_epsilon (E := F)).comp (pairedLift A) := by
  apply ContinuousLinearMap.ext
  intro u
  apply DoubledSpace.ext <;> simp

theorem pairedLift_comp_modular_j (A : E →L[ℝ] F) :
    (pairedLift A).comp (modular_j (E := E)) =
      (modular_j (E := F)).comp (pairedLift A) := by
  apply ContinuousLinearMap.ext
  intro u
  apply DoubledSpace.ext <;> simp

theorem pairedLift_comp_clockAxis (A : E →L[ℝ] F) :
    (pairedLift A).comp (clockAxis (E := E)) =
      (clockAxis (E := F)).comp (pairedLift A) := by
  apply ContinuousLinearMap.ext
  intro u
  apply DoubledSpace.ext <;> simp

/-- The auxiliary positive pairing and its adjoint respect the paired lift. -/
theorem pairedLift_inner (A : E →L[ℝ] F)
    (u : DoubledSpace E) (v : DoubledSpace F) :
    inner ℝ (pairedLift A u) v =
      inner ℝ u (pairedLift (ContinuousLinearMap.adjoint A) v) := by
  simp only [pairedLift_apply, WithLp.prod_inner_apply, WithLp.fst, WithLp.snd,
    ContinuousLinearMap.adjoint_inner_right]

@[simp] theorem pairedLift_adjoint (A : E →L[ℝ] F) :
    ContinuousLinearMap.adjoint (pairedLift A) =
      pairedLift (ContinuousLinearMap.adjoint A) := by
  apply ContinuousLinearMap.ext
  intro v
  apply ext_inner_left ℝ
  intro u
  rw [ContinuousLinearMap.adjoint_inner_right]
  exact pairedLift_inner A u v

/-- The same adjoint identity holds for the native signed pairings, including
maps between different real configuration spaces. -/
theorem pairedLift_krein_pairing (A : E →L[ℝ] F)
    (u : DoubledSpace E) (v : DoubledSpace F) :
    KreinSpace.kreinInner (pairedLift A u) v =
      KreinSpace.kreinInner u (pairedLift (ContinuousLinearMap.adjoint A) v) := by
  simp only [krein_inner_prod_l2, pairedLift_apply, WithLp.fst, WithLp.snd,
    ContinuousLinearMap.adjoint_inner_right]

@[simp] theorem pairedLift_kreinAdjoint (A : E →L[ℝ] E) :
    KreinSpace.kreinAdjoint (pairedLift A) =
      pairedLift (ContinuousLinearMap.adjoint A) := by
  rw [KreinSpace.kreinAdjoint, pairedLift_adjoint]
  have hε : KreinSpace.jCLM (H := DoubledSpace E) = spectral_epsilon (E := E) := by
    apply ContinuousLinearMap.ext
    intro u
    apply DoubledSpace.ext <;> rfl
  rw [hε]
  apply ContinuousLinearMap.ext
  intro u
  apply DoubledSpace.ext <;> simp

theorem pairedLift_kreinSelfAdjoint (A : E →L[ℝ] E)
    (hA : ContinuousLinearMap.adjoint A = A) :
    KreinSpace.IsKreinSelfAdjoint (pairedLift A) := by
  change KreinSpace.kreinAdjoint (pairedLift A) = pairedLift A
  rw [pairedLift_kreinAdjoint, hA]

theorem pairedLift_idempotent (p : E →L[ℝ] E) (hp : p.comp p = p) :
    (pairedLift p).comp (pairedLift p) = pairedLift p := by
  rw [← pairedLift_comp, hp]

section ModelCorner

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable [CompleteSpace V] [KreinSpace V]

/-- The fixed-point model corner of a Krein-self-adjoint idempotent is
nondegenerate. No positivity of the restricted signed form is asserted. -/
theorem modelCorner_nondegenerate (P : V →L[ℝ] V)
    (hPP : P.comp P = P) (hP : KreinSpace.kreinAdjoint P = P)
    (u : V) (hu : P u = u)
    (hzero : ∀ v : V, P v = v → KreinSpace.kreinInner u v = 0) : u = 0 := by
  let J : V ≃ₗᵢ[ℝ] V := KreinSpace.J
  have hmodel : P (P (J u)) = P (J u) :=
    congrArg (fun T : V →L[ℝ] V => T (J u)) hPP
  have hpair : KreinSpace.kreinInner u (J u) = 0 := by
    calc
      KreinSpace.kreinInner u (J u) =
          KreinSpace.kreinInner (P u) (J u) := by rw [hu]
      _ = KreinSpace.kreinInner u (P (J u)) := by
        rw [KreinSpace.kreinInner_kreinAdjoint, hP]
      _ = 0 := hzero _ hmodel
  have hJu : J u = 0 := by
    change inner ℝ (J u) (J u) = 0 at hpair
    exact (inner_self_eq_zero).mp hpair
  have h := congrArg J hJu
  simpa [J, KreinSpace.J_invol] using h

end ModelCorner

/-- A self-adjoint configuration projection produces a nondegenerate native
doubled model corner, while retaining both Krein legs. -/
theorem pairedLift_modelCorner_nondegenerate (p : E →L[ℝ] E)
    (hpp : p.comp p = p) (hp : ContinuousLinearMap.adjoint p = p)
    (u : DoubledSpace E) (hu : pairedLift p u = u)
    (hzero : ∀ v : DoubledSpace E,
      pairedLift p v = v → KreinSpace.kreinInner u v = 0) : u = 0 :=
  modelCorner_nondegenerate (pairedLift p) (pairedLift_idempotent p hpp)
    (pairedLift_kreinSelfAdjoint p hp) u hu hzero

end InfoGeometry.Physics.NuclearDoubledConfiguration
