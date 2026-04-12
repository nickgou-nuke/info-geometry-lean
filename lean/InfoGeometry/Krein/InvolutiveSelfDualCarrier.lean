import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.LinearAlgebra.Dual.Defs
import InfoGeometry.Cartan.Involution

/-!
# Involutive Self-Dual Carrier

This module consolidates the doubled/Krein operator substrate.

Placement discipline:
- The semantic root remains the projective-ray/state layer.
- This file is the algebraic root of the downstream doubled operator lane.

**🚨 SEMANTIC WARNING:**
The ambient `InnerProductSpace ℝ H` and its associated norm/topology are treated
exclusively as **auxiliary analytic scaffolding** (required for completeness
and continuity statements). The **primary owned datum** of the Spire is the
`kreinPairing`. All physical and informational symmetries are defined relative
to the pairing, not the Hilbert inner product.

An involutive self-dual carrier is a real Hilbert space equipped with:
- a symmetric bilinear pairing (`kreinPairing`),
- an involutive grading (`J`, `ε`) that preserves the pairing.

The nondegeneracy of the pairing is required at the substrate level,
grounding all downstream Fenchel/Legendre conjugacy statements.
-/

namespace InfoGeometry.Krein

/--
Generic pairing-to-dual mapping.
Converts a bilinear form into a linear map from the space to its dual.
Defined before the structure to ensure owner-level coherence.
-/
def pairingFlat
    {H : Type*} [AddCommGroup H] [Module ℝ H]
    (B : LinearMap.BilinForm ℝ H) :
    H →ₗ[ℝ] Module.Dual ℝ H :=
{ toFun := fun u =>
    { toFun := fun v => B u v
      map_add' := by
        intro v w
        exact (B u).map_add v w
      map_smul' := by
        intro c v
        exact (B u).map_smul c v }
  map_add' := by
    intro u v
    ext w
    change B (u + v) w = B u w + B v w
    exact congrArg (fun f : H →ₗ[ℝ] ℝ => f w) (B.map_add u v)
  map_smul' := by
    intro c u
    ext w
    change B (c • u) w = c • B u w
    exact congrArg (fun f : H →ₗ[ℝ] ℝ => f w) (B.map_smul c u) }

/-- Nondegeneracy predicate for the carrier pairing based on the flat map. -/
def IsNondegeneratePairing
    {H : Type*} [AddCommGroup H] [Module ℝ H]
    (B : LinearMap.BilinForm ℝ H) : Prop :=
  Function.Injective (pairingFlat B)

section CoreRelations

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Core split-`Cl(1,1)` identity for `K := Jε`: `K² = -Id`. -/
theorem K_sq_of_relations
    (J ε : H →L[ℝ] H)
    (hJ : J.comp J = ContinuousLinearMap.id ℝ H)
    (hε : ε.comp ε = ContinuousLinearMap.id ℝ H)
    (hAnti : J.comp ε = -(ε.comp J)) :
    (J.comp ε).comp (J.comp ε) = -(ContinuousLinearMap.id ℝ H) := by
  ext x
  have hAnti' (y : H) : J (ε y) = -ε (J y) := by
    simpa [ContinuousLinearMap.comp_apply] using congrArg (fun f : H →L[ℝ] H => f y) hAnti
  have hJJ (y : H) : J (J y) = y := by
    simpa [ContinuousLinearMap.comp_apply] using congrArg (fun f : H →L[ℝ] H => f y) hJ
  have hEE (y : H) : ε (ε y) = y := by
    simpa [ContinuousLinearMap.comp_apply] using congrArg (fun f : H →L[ℝ] H => f y) hε
  calc
    ((J.comp ε).comp (J.comp ε)) x = J (ε (J (ε x))) := by rfl
    _ = -ε (J (J (ε x))) := by simpa using hAnti' (J (ε x))
    _ = -ε (ε x) := by rw [hJJ (ε x)]
    _ = -x := by rw [hEE x]
    _ = (-(ContinuousLinearMap.id ℝ H)) x := by rfl

/-- Core split-`Cl(1,1)` identity for `K := Jε`: `JK = ε`. -/
theorem J_comp_K_of_relations
    (J ε : H →L[ℝ] H)
    (hJ : J.comp J = ContinuousLinearMap.id ℝ H) :
    J.comp (J.comp ε) = ε := by
  ext x
  calc
    (J.comp (J.comp ε)) x = J (J (ε x)) := by rfl
    _ = ε x := by
          simpa [ContinuousLinearMap.comp_apply] using congrArg (fun f : H →L[ℝ] H => f (ε x)) hJ
    _ = ε x := rfl

/-- Core split-`Cl(1,1)` identity for `K := Jε`: `KJ = -ε`. -/
theorem K_comp_J_of_relations
    (J ε : H →L[ℝ] H)
    (hJ : J.comp J = ContinuousLinearMap.id ℝ H)
    (hAnti : J.comp ε = -(ε.comp J)) :
    (J.comp ε).comp J = -ε := by
  ext x
  have hAnti' (y : H) : J (ε y) = -ε (J y) := by
    simpa [ContinuousLinearMap.comp_apply] using congrArg (fun f : H →L[ℝ] H => f y) hAnti
  have hJJ (y : H) : J (J y) = y := by
    simpa [ContinuousLinearMap.comp_apply] using congrArg (fun f : H →L[ℝ] H => f y) hJ
  calc
    ((J.comp ε).comp J) x = J (ε (J x)) := by rfl
    _ = -ε (J (J x)) := by simpa using hAnti' (J x)
    _ = -ε x := by rw [hJJ x]
    _ = (-ε) x := by rfl

/-- Core split-`Cl(1,1)` identity for `K := Jε`: `Kε = J`. -/
theorem K_comp_ε_of_relations
    (J ε : H →L[ℝ] H)
    (hε : ε.comp ε = ContinuousLinearMap.id ℝ H) :
    (J.comp ε).comp ε = J := by
  ext x
  have hEE (y : H) : ε (ε y) = y := by
    simpa [ContinuousLinearMap.comp_apply] using congrArg (fun f : H →L[ℝ] H => f y) hε
  calc
    ((J.comp ε).comp ε) x = J (ε (ε x)) := by rfl
    _ = J x := by rw [hEE x]
    _ = J x := rfl

/-- Core split-`Cl(1,1)` identity for `K := Jε`: `εK = -J`. -/
theorem ε_comp_K_of_relations
    (J ε : H →L[ℝ] H)
    (hε : ε.comp ε = ContinuousLinearMap.id ℝ H)
    (hAnti : J.comp ε = -(ε.comp J)) :
    ε.comp (J.comp ε) = -J := by
  ext x
  have hAnti' (y : H) : J (ε y) = -ε (J y) := by
    simpa [ContinuousLinearMap.comp_apply] using congrArg (fun f : H →L[ℝ] H => f y) hAnti
  have hEE (y : H) : ε (ε y) = y := by
    simpa [ContinuousLinearMap.comp_apply] using congrArg (fun f : H →L[ℝ] H => f y) hε
  calc
    (ε.comp (J.comp ε)) x = ε (J (ε x)) := by rfl
    _ = ε (-ε (J x)) := by
          simpa using congrArg (fun v : H => ε v) (hAnti' x)
    _ = -ε (ε (J x)) := by simp
    _ = -J x := by rw [hEE (J x)]
    _ = (-J) x := by rfl

end CoreRelations

/--
The root substrate of the Spire.
An involutive self-dual carrier owns the distinction and conjugacy laws.
-/
structure InvolutiveSelfDualCarrier where
  H : Type*
  [instNormedAddCommGroup : NormedAddCommGroup H]
  [instInnerProductSpace : InnerProductSpace ℝ H]
  [instCompleteSpace : CompleteSpace H]

  kreinPairing : LinearMap.BilinForm ℝ H

  J : H →L[ℝ] H
  ε : H →L[ℝ] H

  J_sq : J.comp J = ContinuousLinearMap.id ℝ H
  ε_sq : ε.comp ε = ContinuousLinearMap.id ℝ H
  J_ε_anticomm : J.comp ε = -(ε.comp J)

  pairing_symm :
    ∀ u v, kreinPairing u v = kreinPairing v u

  pairing_J_invariant :
    ∀ u v, kreinPairing (J u) (J v) = kreinPairing u v
  pairing_ε_invariant :
    ∀ u v, kreinPairing (ε u) (ε v) = kreinPairing u v

  pairing_nondegenerate :
    IsNondegeneratePairing kreinPairing

attribute [instance] InvolutiveSelfDualCarrier.instNormedAddCommGroup
attribute [instance] InvolutiveSelfDualCarrier.instInnerProductSpace
attribute [instance] InvolutiveSelfDualCarrier.instCompleteSpace

namespace InvolutiveSelfDualCarrier

variable (X : InvolutiveSelfDualCarrier)

/-- The induced linear map from the carrier to its dual (the 'flat' map). -/
def flat : X.H →ₗ[ℝ] Module.Dual ℝ X.H :=
  pairingFlat X.kreinPairing

/-- The internal phase axis (Complexifier). K = Jε. -/
noncomputable def K : X.H →L[ℝ] X.H := X.J.comp X.ε

/-- The positive chiral spectral projector. P₊ = (1 + ε) / 2. -/
noncomputable def Pplus : X.H →L[ℝ] X.H :=
  (⅟ (2 : ℝ)) • (ContinuousLinearMap.id ℝ X.H + X.ε)

/-- The negative chiral spectral projector. P₋ = (1 - ε) / 2. -/
noncomputable def Pminus : X.H →L[ℝ] X.H :=
  (⅟ (2 : ℝ)) • (ContinuousLinearMap.id ℝ X.H - X.ε)

section Algebra

@[simp] theorem K_sq : X.K.comp X.K = -(ContinuousLinearMap.id ℝ X.H) := by
  ext x
  have hAnti (y : X.H) : X.J (X.ε y) = -X.ε (X.J y) := by
    simpa [ContinuousLinearMap.comp_apply]
      using congrArg (fun f : X.H →L[ℝ] X.H => f y) X.J_ε_anticomm
  have hJJ (y : X.H) : X.J (X.J y) = y := by
    simpa [ContinuousLinearMap.comp_apply]
      using congrArg (fun f : X.H →L[ℝ] X.H => f y) X.J_sq
  have hEE (y : X.H) : X.ε (X.ε y) = y := by
    simpa [ContinuousLinearMap.comp_apply]
      using congrArg (fun f : X.H →L[ℝ] X.H => f y) X.ε_sq
  calc
    (X.K.comp X.K) x = X.J (X.ε (X.J (X.ε x))) := by rfl
    _ = -X.ε (X.J (X.J (X.ε x))) := by simpa using hAnti (X.J (X.ε x))
    _ = -X.ε (X.ε x) := by rw [hJJ (X.ε x)]
    _ = -x := by rw [hEE x]
    _ = (-(ContinuousLinearMap.id ℝ X.H)) x := by rfl

@[simp] theorem J_comp_K : X.J.comp X.K = X.ε := by
  ext x
  calc
    (X.J.comp X.K) x = X.J (X.J (X.ε x)) := by rfl
    _ = X.ε x := by
          simpa [ContinuousLinearMap.comp_apply]
            using congrArg (fun f : X.H →L[ℝ] X.H => f (X.ε x)) X.J_sq
    _ = X.ε x := rfl

@[simp] theorem K_comp_J : X.K.comp X.J = -(X.ε) := by
  ext x
  have hAnti (y : X.H) : X.J (X.ε y) = -X.ε (X.J y) := by
    simpa [ContinuousLinearMap.comp_apply]
      using congrArg (fun f : X.H →L[ℝ] X.H => f y) X.J_ε_anticomm
  have hJJ (y : X.H) : X.J (X.J y) = y := by
    simpa [ContinuousLinearMap.comp_apply]
      using congrArg (fun f : X.H →L[ℝ] X.H => f y) X.J_sq
  calc
    (X.K.comp X.J) x = X.J (X.ε (X.J x)) := by rfl
    _ = -X.ε (X.J (X.J x)) := by simpa using hAnti (X.J x)
    _ = -X.ε x := by rw [hJJ x]
    _ = (-(X.ε)) x := rfl

@[simp] theorem K_comp_ε : X.K.comp X.ε = X.J := by
  ext x
  have hEE : X.ε (X.ε x) = x := by
    simpa [ContinuousLinearMap.comp_apply]
      using congrArg (fun f : X.H →L[ℝ] X.H => f x) X.ε_sq
  calc
    (X.K.comp X.ε) x = X.J (X.ε (X.ε x)) := by rfl
    _ = X.J x := by rw [hEE]
    _ = X.J x := rfl

@[simp] theorem ε_comp_K : X.ε.comp X.K = -(X.J) := by
  ext x
  have hAnti (y : X.H) : X.J (X.ε y) = -X.ε (X.J y) := by
    simpa [ContinuousLinearMap.comp_apply]
      using congrArg (fun f : X.H →L[ℝ] X.H => f y) X.J_ε_anticomm
  have hEE (y : X.H) : X.ε (X.ε y) = y := by
    simpa [ContinuousLinearMap.comp_apply]
      using congrArg (fun f : X.H →L[ℝ] X.H => f y) X.ε_sq
  calc
    (X.ε.comp X.K) x = X.ε (X.J (X.ε x)) := by rfl
    _ = X.ε (-X.ε (X.J x)) := by
          simpa using congrArg (fun v : X.H => X.ε v) (hAnti x)
    _ = -X.ε (X.ε (X.J x)) := by simp
    _ = -X.J x := by rw [hEE (X.J x)]
    _ = (-(X.J)) x := rfl

private theorem ε_is_cartan (X : InvolutiveSelfDualCarrier) :
    InfoGeometry.Cartan.IsCartanInvolution (𝕜 := ℝ) (E := X.H) X.ε.toLinearMap := by
  dsimp [InfoGeometry.Cartan.IsCartanInvolution]
  ext x
  simpa [Module.End.mul_eq_comp, ContinuousLinearMap.comp_apply]
    using congrArg (fun f : X.H →L[ℝ] X.H => f x) X.ε_sq

@[simp] theorem Pplus_idempotent : X.Pplus.comp X.Pplus = X.Pplus := by
  apply ContinuousLinearMap.ext
  intro x
  have h := LinearMap.congr_fun
    (InfoGeometry.Cartan.Pplus_idempotent (θ := X.ε.toLinearMap) (ε_is_cartan X)) x
  simpa [Pplus, InfoGeometry.Cartan.Pplus, ContinuousLinearMap.comp_apply] using h

@[simp] theorem Pminus_idempotent : X.Pminus.comp X.Pminus = X.Pminus := by
  apply ContinuousLinearMap.ext
  intro x
  have h := LinearMap.congr_fun
    (InfoGeometry.Cartan.Pminus_idempotent (θ := X.ε.toLinearMap) (ε_is_cartan X)) x
  simpa [Pminus, InfoGeometry.Cartan.Pminus, ContinuousLinearMap.comp_apply,
    smul_sub, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using h

@[simp] theorem Pplus_add_Pminus : X.Pplus + X.Pminus = ContinuousLinearMap.id ℝ X.H := by
  apply ContinuousLinearMap.ext
  intro x
  have h := LinearMap.congr_fun (InfoGeometry.Cartan.Pplus_add_Pminus_eq_id (θ := X.ε.toLinearMap)) x
  simpa [Pplus, Pminus, InfoGeometry.Cartan.Pplus, InfoGeometry.Cartan.Pminus] using h

@[simp] theorem Pplus_comp_Pminus : X.Pplus.comp X.Pminus = 0 := by
  have h :=
    congrArg (fun T : X.H →L[ℝ] X.H => T.comp X.Pminus) (X.Pplus_add_Pminus)
  have h' : X.Pplus.comp X.Pminus + X.Pminus = 0 + X.Pminus := by
    simpa [ContinuousLinearMap.add_comp, Pminus_idempotent (X := X), add_comm, add_left_comm,
      add_assoc] using h
  exact add_right_cancel h'

@[simp] theorem Pminus_comp_Pplus : X.Pminus.comp X.Pplus = 0 := by
  have h :=
    congrArg (fun T : X.H →L[ℝ] X.H => T.comp X.Pplus) (X.Pplus_add_Pminus)
  have h' : X.Pplus + X.Pminus.comp X.Pplus = X.Pplus + 0 := by
    simpa [ContinuousLinearMap.add_comp, Pplus_idempotent (X := X), add_comm, add_left_comm,
      add_assoc] using h
  exact add_left_cancel h'

end Algebra

end InvolutiveSelfDualCarrier

end InfoGeometry.Krein
