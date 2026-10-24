/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.FiveStreamMasterIntertwiner
import InfoGeometry.Canonical.PeirceRotorChordal

/-! Algebraic displacement and compression for the existing five-stream rotor.
No metric, positivity, or adjoint unitarity is inferred from these identities. -/
namespace InfoGeometry.Canonical.FiveStreamRotorChordal
open DeBruijnRotorAlternationCycle
variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]

theorem movingPolePlus_displacement_square {d B : A} (h : IsDualSeedPair d B)
    (c s : R) (hc : c*c+s*s=1) :
    (movingPolePlus c s d B - polePlus d B) *
      (movingPolePlus c s d B - polePlus d B) = (s*s) • carrierSupport d B :=
  PeirceRotorChordal.movingPlus_displacement_square h.d_sq h.B_sq h.dBd h.BdB c s hc

theorem movingPolePlus_sandwich {d B : A} (h : IsDualSeedPair d B) (c s : R) :
    polePlus d B * movingPolePlus c s d B * polePlus d B = (c*c) • polePlus d B :=
  PeirceRotorChordal.plus_movingPlus_sandwich h.d_sq h.B_sq h.dBd h.BdB c s

theorem movingPolePlus_commutator_square {d B : A} (h : IsDualSeedPair d B) (c s : R) :
    lieBracket (polePlus d B) (movingPolePlus c s d B) *
      lieBracket (polePlus d B) (movingPolePlus c s d B) =
      -((c*s)*(c*s)) • carrierSupport d B :=
  PeirceRotorChordal.plus_movingPlus_commutator_square h.d_sq h.B_sq h.dBd h.BdB c s

end InfoGeometry.Canonical.FiveStreamRotorChordal
