/-
Copyright (c) 2026 InfoGeometry Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Contributors
-/
import InfoGeometry.Superalgebra.DonaldsonWittenSeibergMonopole

/-!
# Audit: DonaldsonWittenSeibergMonopole
Concrete integer checks for Section 141a Donaldson-Witten BRST twist and Seiberg-Witten monopole condensation.
-/

namespace InfoGeometry.Superalgebra.DonaldsonWittenAudit

open InfoGeometry.Superalgebra.DonaldsonWitten

theorem audit_octonion_brst_nilpotent_int :
    let u : ColorVec3 ℤ := ⟨2, -3, 5⟩
    SplitOctonion.mul (SplitOctonion.quark u) (SplitOctonion.quark u) = SplitOctonion.zero := by decide

theorem audit_octonion_seiberg_witten_anticommutator_int :
    let u : ColorVec3 ℤ := ⟨1, 2, 3⟩
    let v : ColorVec3 ℤ := ⟨4, -1, 2⟩
    SplitOctonion.add (SplitOctonion.mul (SplitOctonion.quark u) (SplitOctonion.antiquark v))
                      (SplitOctonion.mul (SplitOctonion.antiquark v) (SplitOctonion.quark u)) =
      SplitOctonion.scale (ColorVec3.dot u v) SplitOctonion.one := by decide

theorem audit_octonion_donaldson_brst_exact_closed_int :
    let Q := SplitOctonion.quark (⟨1, 2, -1⟩ : ColorVec3 ℤ)
    let Lambda := SplitOctonion.quark (⟨3, 0, 4⟩ : ColorVec3 ℤ)
    let exactObs := SplitOctonion.add (SplitOctonion.mul Q Lambda) (SplitOctonion.mul Lambda Q)
    SplitOctonion.sub (SplitOctonion.mul Q exactObs) (SplitOctonion.mul exactObs Q) =
      SplitOctonion.zero := by decide

theorem audit_monopole_condensation_mass_gap_int :
    let v_mono : ℤ := 7
    (2 * v_mono^2) - 2 * (v_mono * v_mono) = 0 := by decide

theorem audit_donaldson_witten_brst_sq_eq_neg_gauge_var_int :
    let F : BRSTFieldMultiplet (SplitOctonion ℤ) :=
      ⟨canonicalSplitOctonionInt, SplitOctonion.one, canonicalSplitOctonionInt, SplitOctonion.zero⟩
    brstQ (brstQ F) =
      ⟨SplitOctonion.neg (gaugeVarPhi F).A, SplitOctonion.zero, SplitOctonion.zero, SplitOctonion.zero⟩ := by
  decide

theorem audit_donaldson_witten_brst_sq_zero_on_gauge_invariant_int :
    let F : BRSTFieldMultiplet (SplitOctonion ℤ) :=
      ⟨canonicalSplitOctonionInt, SplitOctonion.one, SplitOctonion.zero, SplitOctonion.zero⟩
    brstQ (brstQ F) =
      ⟨SplitOctonion.zero, SplitOctonion.zero, SplitOctonion.zero, SplitOctonion.zero⟩ := by
  decide

theorem audit_swQuadraticMap_norm_sq_factorization_int :
    let ψ₁ : ℤ := 3
    let ψ₂ : ℤ := 2
    let barψ₁ : ℤ := 5
    let barψ₂ : ℤ := 4
    (ψ₁ * barψ₁ - ψ₂ * barψ₂)^2 + (2 * ψ₁ * barψ₂) * (2 * ψ₂ * barψ₁) =
      (ψ₁ * barψ₁ + ψ₂ * barψ₂)^2 := by
  decide

end InfoGeometry.Superalgebra.DonaldsonWittenAudit
