/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Core.PeirceDensityIntertwining
import InfoGeometry.Core.JordanMultiplicationClosure

/-!
# Algebraic synthesis of the supplied five-pillar statement

The conclusion composes native MP/Hodge support laws, supported cyclotomic
identities, an ambient Weyl unit, trace intertwining, and associative Jordan
multiplication. No exceptional-Lie classification or analytic KMS theorem is
asserted. The last identity uses the corrected order `[s,t]`.
-/

namespace InfoGeometry.Canonical.PeirceWeylSynthesis

open InfoGeometry.Singular.MoorePenrose
open InfoGeometry.Core.DiracSuperalgebra
open InfoGeometry.Core.PeirceWeylUnits
open InfoGeometry.Core.PeirceDensityIntertwining
open InfoGeometry.Core.JordanMultiplicationClosure

variable {R A : Type*} [CommRing R] [Ring A] [StarRing A] [Algebra R A]

/-- A checked carrier-level synthesis, conditional on the actual MP witness
and a specified tracial linear functional. -/
theorem peirce_weyl_trace_synthesis {d b : A}
    (h : IsMoorePenroseInverse d b) (hd : d * d = 0)
    (τ : A →ₗ[R] R) (hτ : ∀ x y : A, τ (x * y) = τ (y * x))
    (u v : R) (s t x : A) :
    SquareZeroChiralHodge d b ∧
    star (harmonicSupport d b) = harmonicSupport d b ∧
    thirdRoot d b * thirdRoot d b + thirdRoot d b + activeSupport d b = 0 ∧
    thirdRoot d b ^ 3 = activeSupport d b ∧
    sixthRoot d b ^ 6 = activeSupport d b ∧
    (1 + d) * (1 - b) * (1 + d) = (weylUnit h hd : A) ∧
    (weylUnit h hd : A) * d * ↑((weylUnit h hd)⁻¹) = -b ∧
    (u * u) * weightedTrace τ (density d b (u * u) (v * v)) (d * x) =
      (v * v) * weightedTrace τ (density d b (u * u) (v * v)) (x * d) ∧
    (jordanLeft (R := R) s * jordanLeft (R := R) t -
      jordanLeft (R := R) t * jordanLeft (R := R) s : Module.End R A) x =
      (s * t - t * s) * x - x * (s * t - t * s) := by
  exact ⟨h.squareZero_chiralHodge_decomposition hd, harmonicSupport_star h,
    thirdRoot_polynomial h hd, thirdRoot_cube h hd, (sixthRoot_laws h hd).2.2,
    unipotent_triple hd h.aba_eq_a, (weyl_conjugation h hd).2.2.1,
    (density_trace_boundary h hd τ hτ (u * u) (v * v) x).1,
    commutator_apply s t x⟩

end InfoGeometry.Canonical.PeirceWeylSynthesis
