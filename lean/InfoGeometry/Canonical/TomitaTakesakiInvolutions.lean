import Mathlib.Tactic
import Mathlib.LinearAlgebra.CliffordAlgebra.Conjugation
import InfoGeometry.Clifford.SplitQ44
import InfoGeometry.Clifford.Cl44Witt
import InfoGeometry.Canonical.TopologicalKMSFlow
import InfoGeometry.Canonical.CoordinateFreeConnectionChannels

/-!
# Tomita-Takesaki Involutions

This file constructs the real Clifford involutions used by the modular mirror
and proves their order-reversing action on the `Cl(4,4)` operator algebra.
-/

namespace InfoGeometry.Canonical.TomitaTakesakiInvolutions

open InfoGeometry.Clifford
open InfoGeometry.Clifford.Cl44Witt
open InfoGeometry.Canonical.TopologicalKMSFlow
open CliffordAlgebra

def GammaNFun (x : Fin 8 → ℝ) : Fin 8 → ℝ
  | 0 => x 0
  | 1 => x 1
  | 2 => x 2
  | 3 => x 3
  | 4 => -x 4
  | 5 => -x 5
  | 6 => -x 6
  | 7 => -x 7

lemma GammaNFun_add (x y : Fin 8 → ℝ) : GammaNFun (x + y) = GammaNFun x + GammaNFun y := by
  ext j; fin_cases j <;> simp [GammaNFun, Pi.add_apply] <;> ring

lemma GammaNFun_smul (c : ℝ) (x : Fin 8 → ℝ) : GammaNFun (c • x) = c • GammaNFun x := by
  ext j; fin_cases j <;> simp [GammaNFun, Pi.smul_apply]

theorem GammaNFun_preserves_Q (x : Fin 8 → ℝ) : splitQ44 (GammaNFun x) = splitQ44 x := by
  simp [splitQ44_apply, GammaNFun]

noncomputable def GammaNIsometry : QuadraticMap.IsometryEquiv splitQ44 splitQ44 where
  toFun := GammaNFun
  invFun := GammaNFun
  map_add' := GammaNFun_add
  map_smul' := GammaNFun_smul
  left_inv x := by ext j; fin_cases j <;> simp [GammaNFun]
  right_inv x := by ext j; fin_cases j <;> simp [GammaNFun]
  map_app' x := GammaNFun_preserves_Q x

/-- Charge Conjugation (Gamma_N) as an algebra automorphism. -/
noncomputable def GammaN : Cl44 ≃ₐ[ℝ] Cl44 :=
  CliffordAlgebra.equivOfIsometry GammaNIsometry

def GammaChiFun (x : Fin 8 → ℝ) : Fin 8 → ℝ
  | 0 => x 1
  | 1 => x 0
  | 2 => x 3
  | 3 => x 2
  | 4 => x 5
  | 5 => x 4
  | 6 => x 7
  | 7 => x 6

lemma GammaChiFun_add (x y : Fin 8 → ℝ) : GammaChiFun (x + y) = GammaChiFun x + GammaChiFun y := by
  ext j; fin_cases j <;> simp [GammaChiFun, Pi.add_apply]

lemma GammaChiFun_smul (c : ℝ) (x : Fin 8 → ℝ) : GammaChiFun (c • x) = c • GammaChiFun x := by
  ext j; fin_cases j <;> simp [GammaChiFun, Pi.smul_apply]

theorem GammaChiFun_preserves_Q (x : Fin 8 → ℝ) : splitQ44 (GammaChiFun x) = splitQ44 x := by
  simp [splitQ44_apply, GammaChiFun]
  ring

noncomputable def GammaChiIsometry : QuadraticMap.IsometryEquiv splitQ44 splitQ44 where
  toFun := GammaChiFun
  invFun := GammaChiFun
  map_add' := GammaChiFun_add
  map_smul' := GammaChiFun_smul
  left_inv x := by ext j; fin_cases j <;> simp [GammaChiFun]
  right_inv x := by ext j; fin_cases j <;> simp [GammaChiFun]
  map_app' x := GammaChiFun_preserves_Q x

/-- Chiral Conjugation (Gamma_chi) as an algebra automorphism. -/
noncomputable def GammaChi : Cl44 ≃ₐ[ℝ] Cl44 :=
  CliffordAlgebra.equivOfIsometry GammaChiIsometry

/-- Time Reversal (Gamma_R) as the canonical anti-automorphism. -/
noncomputable def GammaR : Cl44 →ₗ[ℝ] Cl44 :=
  reverse

/-- The Tomita-Takesaki modular mirror on the real Clifford carrier.

`J_Tomita` is real-linear and anti-multiplicative.  Any complex
anti-linearity must be supplied separately by a chosen real phase-axis
structure; it is not silently asserted by this definition. -/
noncomputable def J_Tomita : Cl44 →ₗ[ℝ] Cl44 :=
  GammaR.comp GammaN.toLinearMap

/-! `J_Tomita` is real-linear and reverses operator order.  This is the
    algebraic content used below; no scalar complex conjugation is introduced. -/
theorem J_Tomita_reverse_mul (x y : Cl44) :
    J_Tomita (x * y) = J_Tomita y * J_Tomita x := by
  change reverse (GammaN (x * y)) =
    reverse (GammaN y) * reverse (GammaN x)
  rw [map_mul, reverse.map_mul]

theorem J_Tomita_thermalAnticommutator (x y : Cl44) :
    J_Tomita (x * y + y * x) =
      J_Tomita x * J_Tomita y + J_Tomita y * J_Tomita x := by
  calc
    J_Tomita (x * y + y * x) =
        J_Tomita (x * y) + J_Tomita (y * x) := by
          exact map_add _ _ _
    _ = J_Tomita y * J_Tomita x + J_Tomita x * J_Tomita y := by
          rw [J_Tomita_reverse_mul, J_Tomita_reverse_mul]
    _ = J_Tomita x * J_Tomita y + J_Tomita y * J_Tomita x := by
          exact add_comm _ _

theorem J_Tomita_quadraticCommutator (x y : Cl44) :
    J_Tomita (x * y - y * x) =
      -(J_Tomita x * J_Tomita y - J_Tomita y * J_Tomita x) := by
  calc
    J_Tomita (x * y - y * x) =
        J_Tomita (x * y) - J_Tomita (y * x) := by
          exact map_sub _ _ _
    _ = J_Tomita y * J_Tomita x - J_Tomita x * J_Tomita y := by
          rw [J_Tomita_reverse_mul, J_Tomita_reverse_mul]
    _ = -(J_Tomita x * J_Tomita y - J_Tomita y * J_Tomita x) := by
          noncomm_ring

theorem J_Tomita_twoSlotCurvature
    (dXY dYX AX AY : Cl44) :
    J_Tomita
        (InfoGeometry.Canonical.CoordinateFreeConnectionChannels.twoSlotCurvature
          dXY dYX AX AY) =
      InfoGeometry.Canonical.CoordinateFreeConnectionChannels.twoSlotCurvature
        (J_Tomita dXY) (J_Tomita dYX) (J_Tomita AY) (J_Tomita AX) := by
  unfold InfoGeometry.Canonical.CoordinateFreeConnectionChannels.twoSlotCurvature
    InfoGeometry.Canonical.CoordinateFreeConnectionChannels.commutator
  simp only [map_add, map_sub, J_Tomita_reverse_mul]

variable (E μ : Fin 4 → ℝ)

/-- J on the generators behaves exactly to reverse the modular flow. -/
theorem J_Tomita_reverses_flow (t : ℝ) (x : Fin 8 → ℝ) :
    J_Tomita (modularFlow E μ t (J_Tomita (ι splitQ44 x))) =
    modularFlow E μ (-t) (ι splitQ44 x) := by
  -- Since ι x is a vector, GammaN maps it to ι (GammaNFun x), and reverse preserves it.
  have h1 : ∀ v, J_Tomita (ι splitQ44 v) = ι splitQ44 (GammaNFun v) := by
    intro v
    change reverse (GammaN (ι splitQ44 v)) = ι splitQ44 (GammaNFun v)
    have hh : GammaN (ι splitQ44 v) = ι splitQ44 (GammaNFun v) := by
      change CliffordAlgebra.map GammaNIsometry.toIsometry (ι splitQ44 v) = ι splitQ44 (GammaNFun v)
      rw [CliffordAlgebra.map_apply_ι]
      rfl
    rw [hh]
    exact reverse_ι _
  rw [h1 x]
  -- Now modularFlow maps this to ι (boostFun t (GammaNFun x))
  have h2 : modularFlow E μ t (ι splitQ44 (GammaNFun x)) = ι splitQ44 (boostFun E μ t (GammaNFun x)) := by
    change CliffordAlgebra.map (boostIsometryEquiv E μ t).toIsometry (ι splitQ44 (GammaNFun x)) = _
    rw [CliffordAlgebra.map_apply_ι]
    rfl
  rw [h2]
  -- And J_Tomita on this is ι (GammaNFun (boostFun t (GammaNFun x)))
  rw [h1]
  have h3 : modularFlow E μ (-t) (ι splitQ44 x) = ι splitQ44 (boostFun E μ (-t) x) := by
    change CliffordAlgebra.map (boostIsometryEquiv E μ (-t)).toIsometry (ι splitQ44 x) = _
    rw [CliffordAlgebra.map_apply_ι]
    rfl
  rw [h3]
  -- So we just need to show that GammaNFun ∘ boostFun t ∘ GammaNFun = boostFun (-t)
  congr 1
  ext j
  fin_cases j <;> simp [GammaNFun, boostFun, Real.cosh_neg, Real.sinh_neg] <;> ring

/-! The generator calculation extends to the whole Clifford algebra by the
    additive/multiplicative induction principle.  The multiplicative case is
    deliberately written with the reversed order supplied by `J_Tomita`. -/
theorem J_Tomita_reverses_flow_all (t : ℝ) (z : Cl44) :
    J_Tomita (modularFlow E μ t (J_Tomita z)) =
      modularFlow E μ (-t) z := by
  induction z using CliffordAlgebra.induction with
  | algebraMap r =>
      simp [J_Tomita, GammaN, GammaR, modularFlow]
  | ι x =>
      exact J_Tomita_reverses_flow E μ t x
  | mul x y hx hy =>
      calc
        J_Tomita (modularFlow E μ t (J_Tomita (x * y))) =
            J_Tomita (modularFlow E μ t (J_Tomita y * J_Tomita x)) := by
              rw [J_Tomita_reverse_mul]
        _ = J_Tomita (modularFlow E μ t (J_Tomita y) *
              modularFlow E μ t (J_Tomita x)) := by
              congr 1
              exact (modularFlow E μ t).map_mul _ _
        _ = J_Tomita (modularFlow E μ t (J_Tomita x)) *
              J_Tomita (modularFlow E μ t (J_Tomita y)) := by
              rw [J_Tomita_reverse_mul]
        _ = modularFlow E μ (-t) x * modularFlow E μ (-t) y := by
              rw [hx, hy]
        _ = modularFlow E μ (-t) (x * y) := by
              exact ((modularFlow E μ (-t)).map_mul _ _).symm
  | add x y hx hy =>
      calc
        J_Tomita (modularFlow E μ t (J_Tomita (x + y))) =
            J_Tomita (modularFlow E μ t (J_Tomita x + J_Tomita y)) := by
              rw [map_add, map_add]
        _ = J_Tomita (modularFlow E μ t (J_Tomita x) +
              modularFlow E μ t (J_Tomita y)) := by
              congr 1
              exact (modularFlow E μ t).map_add _ _
        _ = J_Tomita (modularFlow E μ t (J_Tomita x)) +
              J_Tomita (modularFlow E μ t (J_Tomita y)) := by
              rw [map_add]
        _ = modularFlow E μ (-t) x + modularFlow E μ (-t) y := by
              rw [hx, hy]
        _ = modularFlow E μ (-t) (x + y) := by
              exact ((modularFlow E μ (-t)).map_add _ _).symm

/-- The Clifford reversion commutes with the charge-conjugation automorphism. -/
theorem reverse_commutes_GammaN (z : Cl44) :
    reverse (GammaN z) = GammaN (reverse z) := by
  induction z using CliffordAlgebra.induction with
  | algebraMap r => simp [GammaN]
  | ι x => simp [GammaN]
  | mul x y hx hy =>
      simp only [map_mul, reverse.map_mul, hx, hy]
  | add x y hx hy =>
      simp only [map_add, reverse.map_add, hx, hy]

theorem GammaN_involutive (z : Cl44) :
    GammaN (GammaN z) = z := by
  induction z using CliffordAlgebra.induction with
  | algebraMap r => simp [GammaN]
  | ι x =>
      have h1 : ∀ v, GammaN (ι splitQ44 v) = ι splitQ44 (GammaNFun v) := by
        intro v
        change CliffordAlgebra.map GammaNIsometry.toIsometry (ι splitQ44 v) = _
        rw [CliffordAlgebra.map_apply_ι]
        rfl
      rw [h1, h1]
      congr 1
      ext j
      fin_cases j <;> simp [GammaNFun]
  | mul x y hx hy =>
      simp only [map_mul, hx, hy]
  | add x y hx hy =>
      simp only [map_add, hx, hy]

/- The Tomita map is therefore an involution on the whole Clifford carrier. -/
theorem J_Tomita_involutive (z : Cl44) :
    J_Tomita (J_Tomita z) = z := by
  change reverse (GammaN (reverse (GammaN z))) = z
  rw [reverse_commutes_GammaN]
  simp only [reverse_reverse]
  exact GammaN_involutive z

end InfoGeometry.Canonical.TomitaTakesakiInvolutions
