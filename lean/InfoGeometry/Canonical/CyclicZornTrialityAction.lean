/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.GaloisZornTrialityBridge
import InfoGeometry.Canonical.CanonicalZornProjectiveTKKBridge
import Mathlib.Data.ZMod.Aut

/-! A faithful cyclic action on the existing nonassociative Zorn carrier. -/

noncomputable section

namespace InfoGeometry.Canonical.GaloisZornTrialityBridge

def cyclicTrialityPerm (χ : ZMod 3) : Equiv.Perm ZornCore.Zorn where
  toFun X := galoisActionOnTriality X χ
  invFun X := galoisActionOnTriality X (-χ)
  left_inv X := by
    change galoisActionOnTriality (galoisActionOnTriality X χ) (-χ) = X
    rw [← galoisActionOnTriality_homomorphism, neg_add_cancel]
    rfl
  right_inv X := by
    change galoisActionOnTriality (galoisActionOnTriality X (-χ)) χ = X
    rw [← galoisActionOnTriality_homomorphism, add_neg_cancel]
    rfl

def cyclicTrialityHom : Multiplicative (ZMod 3) →* Equiv.Perm ZornCore.Zorn where
  toFun χ := cyclicTrialityPerm χ.toAdd
  map_one' := by apply Equiv.ext; intro X; rfl
  map_mul' χ ψ := by
    apply Equiv.ext
    intro X
    exact galoisActionOnTriality_homomorphism X χ.toAdd ψ.toAdd

theorem cyclicTriality_seed_injective :
    Function.Injective (fun χ : ZMod 3 =>
      galoisActionOnTriality (ZornCore.U ZornCore.e1) χ) := by
  intro χ ψ h
  have h0 := congrArg (fun X : ZornCore.Zorn => X.u 0) h
  have h1 := congrArg (fun X : ZornCore.Zorn => X.u 1) h
  fin_cases χ <;> fin_cases ψ <;>
    simp_all [galoisActionOnTriality, ZornCore.triality, ZornCore.rotate3,
      ZornCore.U, ZornCore.e1] <;> rfl

theorem cyclicTrialityHom_injective : Function.Injective cyclicTrialityHom := by
  intro χ ψ h
  have he := congrArg (fun e : Equiv.Perm ZornCore.Zorn => e (ZornCore.U ZornCore.e1)) h
  exact cyclicTriality_seed_injective he

theorem cyclicTrialityHom_preserves_det (χ : Multiplicative (ZMod 3)) (X : ZornCore.Zorn) :
    ZornCore.det (cyclicTrialityHom χ X) = ZornCore.det X :=
  galoisActionOnTriality_preserves_det X χ.toAdd

theorem core_triality_mul (X Y : ZornCore.Zorn) :
    ZornCore.triality (X * Y) = ZornCore.triality X * ZornCore.triality Y := by
  apply CanonicalZornProjectiveTKKBridge.coreToCanonical_injective
  simp only [CanonicalZornProjectiveTKKBridge.coreToCanonical_triality,
    CanonicalZornProjectiveTKKBridge.coreToCanonical_mul,
    CanonicalZornProjectiveTKKBridge.canonicalTriality_mul]

theorem cyclicTrialityHom_preserves_mul (χ : Multiplicative (ZMod 3)) (X Y : ZornCore.Zorn) :
    cyclicTrialityHom χ (X * Y) = cyclicTrialityHom χ X * cyclicTrialityHom χ Y := by
  change galoisActionOnTriality (X * Y) χ.toAdd =
    galoisActionOnTriality X χ.toAdd * galoisActionOnTriality Y χ.toAdd
  generalize χ.toAdd = a
  fin_cases a <;> simp [galoisActionOnTriality, core_triality_mul]

end InfoGeometry.Canonical.GaloisZornTrialityBridge
