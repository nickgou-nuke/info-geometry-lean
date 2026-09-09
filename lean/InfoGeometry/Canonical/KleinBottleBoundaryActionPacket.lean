import Mathlib.Data.Matrix.Basic
import InfoGeometry.Canonical.CptBoundaryMobius

/-!
# InfoGeometry.Canonical.KleinBottleBoundaryActionPacket

Finite `Z₂` / glide-reflection packet for the Klein-bottle boundary lane.

This file stays in the closed finite owner lane:

- the sheet action is the two-point swap on `Fin 2`;
- the boundary action is conjugation by the existing `CPT_local` involution;
- the zero/infinity boundary projectors are exchanged by that action.

It does **not** prove a global Klein-bottle manifold theorem, orientifold
consistency in string theory, or any Katz-Sarnak / RH statement.

#### BUCKET 1: CLOSED FINITE THEOREMS
- `sheetSwap_involutive`
- `glideReflection_involutive`
- `glideReflection_zero_to_infinity`
- `glideReflection_infinity_to_zero`
- `canonicalPacket_boundaryAction_involutive`

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES
None.

#### BUCKET 3: OPEN CLOSURE DEBT
Global topological realization, infinite-colimit transport, and physical
orientifold/string interpretations remain outside this file.
-/

namespace InfoGeometry.Canonical.KleinBottleBoundaryActionPacket

open Matrix
open CptBoundaryMobius

/-- Finite boundary packet: one `Z₂` sheet action plus one matrix boundary action. -/
structure BoundaryActionPacket where
  sheetAction : Equiv.Perm (Fin 2)
  parityOperator : Matrix (Fin 2) (Fin 2) ℤ
  boundaryAction : Matrix (Fin 2) (Fin 2) ℤ → Matrix (Fin 2) (Fin 2) ℤ

/-- The two-sheet Klein-bottle boundary flip. -/
def sheetSwap : Equiv.Perm (Fin 2) := Equiv.swap 0 1

@[simp] theorem sheetSwap_apply_zero : sheetSwap 0 = 1 := rfl
@[simp] theorem sheetSwap_apply_one : sheetSwap 1 = 0 := rfl

@[simp] theorem sheetSwap_involutive (i : Fin 2) : sheetSwap (sheetSwap i) = i := by
  fin_cases i <;> rfl

/-- Boundary glide reflection induced by the finite CPT involution. -/
def glideReflection (M : Matrix (Fin 2) (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ :=
  CPT_local * M * CPT_local

@[simp] theorem glideReflection_involutive (M : Matrix (Fin 2) (Fin 2) ℤ) :
    glideReflection (glideReflection M) = M := by
  unfold glideReflection
  calc
    CPT_local * (CPT_local * M * CPT_local) * CPT_local
        = (CPT_local * (CPT_local * M)) * (CPT_local * CPT_local) := by
            simp [Matrix.mul_assoc]
    _ = CPT_local * (CPT_local * M) := by
          rw [CptInvolution.is_involution CPT_local_is_involution, Matrix.mul_one]
    _ = (CPT_local * CPT_local) * M := by
          rw [← Matrix.mul_assoc]
    _ = M := by
          rw [CptInvolution.is_involution CPT_local_is_involution, Matrix.one_mul]

@[simp] theorem glideReflection_zero_to_infinity :
    glideReflection P_zero = L_spectator := by
  simpa [glideReflection] using moebius_zero_infinity_duality

@[simp] theorem glideReflection_infinity_to_zero :
    glideReflection L_spectator = P_zero := by
  simpa [glideReflection_zero_to_infinity] using
    (glideReflection_involutive P_zero)

/-- Canonical finite packet for the Klein-bottle boundary lane. -/
def canonicalPacket : BoundaryActionPacket where
  sheetAction := sheetSwap
  parityOperator := CPT_local
  boundaryAction := glideReflection

@[simp] theorem canonicalPacket_boundaryAction_zero :
    canonicalPacket.boundaryAction P_zero = L_spectator :=
  glideReflection_zero_to_infinity

@[simp] theorem canonicalPacket_boundaryAction_infinity :
    canonicalPacket.boundaryAction L_spectator = P_zero :=
  glideReflection_infinity_to_zero

@[simp] theorem canonicalPacket_boundaryAction_involutive
    (M : Matrix (Fin 2) (Fin 2) ℤ) :
    canonicalPacket.boundaryAction (canonicalPacket.boundaryAction M) = M :=
  glideReflection_involutive M

end InfoGeometry.Canonical.KleinBottleBoundaryActionPacket
