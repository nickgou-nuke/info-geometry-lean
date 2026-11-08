/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.NCG.CuntzColimitKMSTiltGNS
import InfoGeometry.NCG.CuntzColimitShiftKMSGNSBridge
import InfoGeometry.Core.SquareZeroSandwich
import InfoGeometry.Algebra.CuntzTensorQuotient

/-!
# Cuntz Metriplectic Evolution — Reuse of Existing Infrastructure

Archetype extracted from Kitaev / Naaijkens / Nachtergaele transcripts:
gapped Hamiltonians, superselection sectors, modular flow, KMS states.

This module does NOT redefine dissipator, generator, or KMS state. It reuses:
- `InfoGeometry.NCG.cuntzShift` — the shift endomorphism Φ(X) = Σ S_i X S_i*
- `InfoGeometry.NCG.CuntzColimit.KMSState` — shift-invariant KMS state
- `InfoGeometry.Core.SquareZeroSandwich.symmDissipator` — double-commutator dissipator
- `InfoGeometry.Core.SquareZeroSandwich.symmGenerator` — generator (derivation + dissipator)

Real-linear Hestenes–Kreit formulation. No complex numbers, no complex
Tomita–Takesaki theory, no anti-linear modular conjugation.
-/

open InfoGeometry.NCG
open InfoGeometry.NCG.CuntzColimit
open InfoGeometry.Core.SquareZeroSandwich
open InfoGeometry.Algebra.CuntzTensorQuotient

noncomputable section

namespace InfoGeometry.Algebra.CuntzMetriplectic

/-! ## Metriplectic Generator on Cuntz Algebra

The metriplectic generator combines:
- Poisson (commutator) part: [H, X] = H * X − X * H
- Metric (dissipative) part: deviation of cuntzShift from identity

Both parts reuse existing definitions: `cuntzShift` from `NCG` for
the dissipative core, and the plain commutator for the Poisson part.
-/

def cuntzMetriplecticGenerator {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Type*} [Ring A] [StarRing A]
    (S : ι → A) (H : A) (X : A) : A :=
  (H * X - X * H) + (cuntzShift S X - X)

/-! ## KMS State as Fixed Point

Reuses `KMSState.shift_invariant` from `NCG.CuntzColimit` to prove that a
shift-invariant KMS state is annihilated by the metriplectic generator when
the commutator part vanishes in the state.

This expresses thermal equilibrium: the state does not change under the
metriplectic dynamics.
-/

theorem kmsStateFixedPoint {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Type*} [Ring A] [StarRing A]
    (S : ι → A)
    {φ : A →ₗ[ℤ] A} (hKMS : KMSState S φ)
    (H : A) (hComm : ∀ (X : A), φ (H * X - X * H) = 0)
    (X : A) :
    φ (cuntzMetriplecticGenerator S H X) = 0 := by
  calc
    φ (cuntzMetriplecticGenerator S H X)
        = φ ((H * X - X * H) + (cuntzShift S X - X)) := by
      dsimp [cuntzMetriplecticGenerator]
    _ = φ (H * X - X * H) + φ (cuntzShift S X - X) := by
      rw [φ.map_add]
    _ = 0 + φ (cuntzShift S X - X) := by
      rw [hComm X]
    _ = 0 + 0 := by
      have h₁ : φ (cuntzShift S X - X) = 0 := by
        have h₂ : φ (cuntzShift S X) = φ X := hKMS.shift_invariant X
        have h₃ : φ (cuntzShift S X - X) = φ (cuntzShift S X) - φ X := by
          rw [φ.map_sub]
        rw [h₃, h₂]
        ; simp [sub_self]
      rw [h₁]
    _ = 0 := by
      (simp [add_zero])
