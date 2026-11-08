/-
Copyright (c) 2026 nickgou-nuke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: nickgou-nuke contributors
-/
import InfoGeometry.Physics.MarsdenWeinsteinHasimotoVortex

/-!
# Audit Module: MarsdenWeinsteinHasimotoVortexAudit

Automated kernel verification of Section 5.95:
Marsden–Weinstein Symplectic Reduction, Vortex Filament Local Induction Approximation (LIA),
and the Hasimoto Transformation.
-/

namespace InfoGeometry.Physics.HasimotoVortexAudit

set_option linter.unusedVariables false

open Matrix Complex
open scoped ComplexConjugate
open InfoGeometry.Physics.HasimotoVortex

-- 1. Signature and Type Verification

#check (crossFrame_scaled_normal :
  ∀ (t n b : Fin 3 → ℝ), t ⨯₃ n = b → ∀ (kappa : ℝ),
    t ⨯₃ (kappa • n) = kappa • b)

#check (cross_expansion_identity :
  ∀ (t n b : Fin 3 → ℝ), t ⨯₃ n = b → t ⨯₃ b = -n → t ⨯₃ t = 0 →
    ∀ (kappa kappa_prime tau : ℝ),
      t ⨯₃ crossExpansionVector t n b kappa kappa_prime tau =
        crossExpansionResult n b kappa_prime kappa tau)

#check (normSq_exp_ofReal_mul_I :
  ∀ (x : ℝ), normSq (exp (x * I)) = 1)

#check (hasimoto_normSq :
  ∀ (kappa theta : ℝ),
    normSq (hasimotoWave kappa theta) = kappa ^ 2)

#check (hasDerivAt_hasimotoPath :
  ∀ (kappa theta : ℝ → ℝ) (s kappa' theta' : ℝ),
    HasDerivAt kappa kappa' s → HasDerivAt theta theta' s →
      HasDerivAt (hasimotoPath kappa theta)
        ((kappa' : ℂ) * exp ((theta s : ℂ) * I) +
          (kappa s : ℂ) * (exp ((theta s : ℂ) * I) * ((theta' : ℂ) * I))) s)

#check (hasDerivAt_hasimotoPath_eq_jet :
  ∀ (kappa theta : ℝ → ℝ) (s kappa' tau : ℝ),
    HasDerivAt kappa kappa' s → HasDerivAt theta tau s →
      HasDerivAt (hasimotoPath kappa theta)
        (hasimotoDeriv (kappa s) kappa' tau (theta s)) s)

#check (hasimotoPath_conj_mul_deriv :
  ∀ (kappa theta : ℝ → ℝ) (s kappa' tau : ℝ),
    HasDerivAt kappa kappa' s → HasDerivAt theta tau s →
      conj (hasimotoPath kappa theta s) * deriv (hasimotoPath kappa theta) s =
        ((kappa s * kappa' : ℝ) : ℂ) + I * ((kappa s ^ 2 * tau : ℝ) : ℂ))

#check (conj_exp_ofReal_mul_I :
  ∀ (x : ℝ), conj (exp (x * I)) = exp (- (x * I)))

#check (hasimoto_conj_mul_deriv :
  ∀ (kappa kappa_prime tau theta : ℝ),
    conj (hasimotoWave kappa theta) * hasimotoDeriv kappa kappa_prime tau theta =
      ((kappa * kappa_prime : ℝ) : ℂ) + I * ((kappa ^ 2 * tau : ℝ) : ℂ))

#check (hasimoto_helicity_density :
  ∀ (kappa kappa_prime tau theta : ℝ),
    (conj (hasimotoWave kappa theta) * hasimotoDeriv kappa kappa_prime tau theta).im =
      kappa ^ 2 * tau)

#check (hasimoto_jet_real_part :
  ∀ (kappa kappa_prime tau theta : ℝ),
    (conj (hasimotoWave kappa theta) * hasimotoDeriv kappa kappa_prime tau theta).re =
      kappa * kappa_prime)

#check (filamentLength_nonneg :
  ∀ {k : ℕ} (w : Fin k → ℝ) (kappa : Fin k → ℝ) (hw : ∀ i, 0 ≤ w i),
    0 ≤ filamentLength w kappa)

#check (filamentHelicity_zero_of_planar :
  ∀ {k : ℕ} (w : Fin k → ℝ) (kappa : Fin k → ℝ) (tau : Fin k → ℝ) (h_planar : ∀ i, tau i = 0),
    filamentHelicity w kappa tau = 0)

#check (crossTripleProduct_skew :
  ∀ (t u v : Fin 3 → ℝ),
    crossTripleProduct t v u = - crossTripleProduct t u v)

#check (crossTripleProduct_self :
  ∀ (t u : Fin 3 → ℝ),
    crossTripleProduct t u u = 0)

#check (crossTripleProduct_first_cross_zero :
  ∀ (t w : Fin 3 → ℝ),
    crossTripleProduct t t w = 0)

-- 2. Axiom Footprint Verification
#print axioms crossFrame_scaled_normal
#print axioms cross_expansion_identity
#print axioms normSq_exp_ofReal_mul_I
#print axioms hasimoto_normSq
#print axioms hasDerivAt_hasimotoPath
#print axioms hasDerivAt_hasimotoPath_eq_jet
#print axioms hasimotoPath_conj_mul_deriv
#print axioms conj_exp_ofReal_mul_I
#print axioms hasimoto_conj_mul_deriv
#print axioms hasimoto_helicity_density
#print axioms hasimoto_jet_real_part
#print axioms filamentLength_nonneg
#print axioms filamentHelicity_zero_of_planar
#print axioms crossTripleProduct_skew
#print axioms crossTripleProduct_self
#print axioms crossTripleProduct_first_cross_zero
end InfoGeometry.Physics.HasimotoVortexAudit
