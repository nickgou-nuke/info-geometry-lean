/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.HestenesPauliEvenClifford
import InfoGeometry.Canonical.BipolarCartanCl3PhaseBridge

/-!
# Real transport of the even spacetime Clifford volume

The existing even Clifford--Pauli equivalence and interleaved realification
give an injective real algebra representation on four real coordinates. The
intrinsic spacetime volume acts as the existing real Pauli phase axis. Its
centrality is proved for every element of the even Clifford algebra, and its
left action is intertwined with the real phase action without a commuting
restriction on the other even elements.

This is a finite representation theorem. It does not construct a Hilbert
completion, a spin connection, or a wavepacket transform.
-/

noncomputable section

namespace InfoGeometry.Canonical.HestenesCartanPhaseTransport

open InfoGeometry.Canonical.HestenesPauliEvenClifford
open InfoGeometry.Canonical.Cl11JordanComplexRealificationBridge
open InfoGeometry.Canonical.BipolarCartanCl3PhaseBridge
open InfoGeometry.Clifford.GullDoranPseudoscalarBridge

/-- Interleaved realification, bundled with its real linear and algebra laws. -/
def interleavedRealifyAlgHom : M2C →ₐ[ℝ] Matrix4R :=
  AlgHom.ofLinearMap
    { toFun := interleavedRealify
      map_add' A B := by
        simp only [interleavedRealify, realify_add, mul_add, add_mul]
      map_smul' r A := by
        have hr : realify (r • A) = r • realify A := by
          rw [RCLike.real_smul_eq_coe_smul (K := ℂ) r A]
          exact realify_real_smul r A
        simp only [interleavedRealify, hr, mul_smul_comm, smul_mul_assoc, RingHom.id_apply] }
    interleavedRealify_one interleavedRealify_mul

/-- The faithful real representation of the native even spacetime algebra. -/
def evenRealification : ClPlus14 →ₐ[ℝ] Matrix4R :=
  interleavedRealifyAlgHom.comp clPlusToPauli

@[simp] theorem evenRealification_apply (a : ClPlus14) :
    evenRealification a = interleavedRealify (clPlusToPauli a) := rfl

theorem interleavedRealify_injective : Function.Injective interleavedRealify := by
  intro A B h
  apply realify_injective
  have h' := congrArg
    (fun M : Matrix4R => realificationOrderSwap * M * realificationOrderSwap) h
  have undo (M : Matrix4R) :
      realificationOrderSwap * (realificationOrderSwap * M * realificationOrderSwap) *
        realificationOrderSwap = M := by
    calc
      _ = (realificationOrderSwap * realificationOrderSwap) * M *
          (realificationOrderSwap * realificationOrderSwap) := by noncomm_ring
      _ = M := by simp only [realificationOrderSwap_sq, one_mul, mul_one]
  simpa only [interleavedRealify, undo] using h'

theorem evenRealification_injective : Function.Injective evenRealification :=
  interleavedRealify_injective.comp clPlusToPauli_injective

/-- The native spacetime volume is the real square-minus-one phase axis. -/
@[simp] theorem evenRealification_pseudoscalar :
    evenRealification spacetimePseudoscalar = realPhaseAxis := by
  rw [evenRealification_apply, clPlusToPauli_pseudoscalar,
    interleavedRealify_complexPhase]

/-- Centrality holds throughout the even spacetime algebra. -/
theorem spacetimePseudoscalar_commutes (a : ClPlus14) :
    Commute spacetimePseudoscalar a := by
  apply clPlusToPauli_injective
  simp only [map_mul, clPlusToPauli_pseudoscalar, smul_mul_assoc,
    mul_smul_comm, one_mul, mul_one]

@[simp] theorem spacetimePseudoscalar_sq :
    spacetimePseudoscalar * spacetimePseudoscalar = -1 := by
  apply evenRealification_injective
  simp only [map_mul, map_neg, map_one, evenRealification_pseudoscalar]
  exact realPhaseAxis_sq

/-- Realification intertwines the intrinsic volume action on every even element. -/
theorem evenRealification_pseudoscalar_mul (a : ClPlus14) :
    evenRealification (spacetimePseudoscalar * a) =
      realPhaseAxis * evenRealification a := by
  rw [map_mul, evenRealification_pseudoscalar]

/-- The real phase axis commutes with the entire represented even algebra. -/
theorem realPhaseAxis_commutes_evenRealification (a : ClPlus14) :
    Commute realPhaseAxis (evenRealification a) := by
  change _ * _ = _ * _
  simpa only [map_mul, evenRealification_pseudoscalar] using
    congrArg evenRealification (spacetimePseudoscalar_commutes a).eq

/-- The established Cartan conversion uses the represented native volume. -/
theorem interleavedKcirc_eq_even_volume_mul_boost :
    interleavedKcirc =
      evenRealification spacetimePseudoscalar * interleavedKboost := by
  rw [evenRealification_pseudoscalar]
  exact interleavedKcirc_eq_realPhaseAxis_mul_interleavedKboost

end InfoGeometry.Canonical.HestenesCartanPhaseTransport
