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

#check (lia_tangent_cross_prime :
  ∀ (F : FrenetTriad) (kappa : ℝ),
    F.t ⨯₃ (kappa • F.n) = kappa • F.b)

#check (lia_heisenberg_cross_equivalence :
  ∀ (F : FrenetTriad) (kappa kappa_prime tau : ℝ),
    F.t ⨯₃ tangentSecondDeriv F kappa kappa_prime tau =
      liaTangentTimeDeriv F kappa_prime kappa tau)

#check (normSq_exp_ofReal_mul_I :
  ∀ (x : ℝ), normSq (exp (x * I)) = 1)

#check (hasimoto_normSq :
  ∀ (kappa theta : ℝ),
    normSq (hasimotoWave kappa theta) = kappa ^ 2)

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

#check (hasimoto_soliton_density_deriv :
  ∀ (kappa kappa_prime tau theta : ℝ),
    (conj (hasimotoWave kappa theta) * hasimotoDeriv kappa kappa_prime tau theta).re =
      kappa * kappa_prime)

#check (filamentLength_nonneg :
  ∀ {k : ℕ} (w : Fin k → ℝ) (kappa : Fin k → ℝ) (hw : ∀ i, 0 ≤ w i),
    0 ≤ filamentLength w kappa)

#check (filamentHelicity_zero_of_planar :
  ∀ {k : ℕ} (w : Fin k → ℝ) (kappa : Fin k → ℝ) (tau : Fin k → ℝ) (h_planar : ∀ i, tau i = 0),
    filamentHelicity w kappa tau = 0)

#check (su2SymplecticForm_skew :
  ∀ (t u v : Fin 3 → ℝ),
    su2SymplecticForm t v u = - su2SymplecticForm t u v)

#check (su2SymplecticForm_self :
  ∀ (t u : Fin 3 → ℝ),
    su2SymplecticForm t u u = 0)

#check (su2SymplecticForm_radial_zero :
  ∀ (t w : Fin 3 → ℝ),
    su2SymplecticForm t t w = 0)

#check (vortexRingDrift_pos :
  ∀ {R : ℝ} (hR : 0 < R), 0 < vortexRingDrift R)

#check (vortexRingDispersion_pos :
  ∀ {R : ℝ} (hR : 0 < R), 0 < vortexRingDispersion R)

#check (marsden_weinstein_hasimoto_vortex_synthesis :
  ∀ (F : FrenetTriad) (kappa kappa_prime tau theta : ℝ)
    {k : ℕ} (w : Fin k → ℝ) (hw : ∀ i, 0 ≤ w i)
    (k_curv : Fin k → ℝ) (tau_planar : Fin k → ℝ) (h_planar : ∀ i, tau_planar i = 0)
    (u v : Fin 3 → ℝ)
    {R : ℝ} (hR : 0 < R),
    (F.t ⨯₃ (kappa • F.n) = kappa • F.b) ∧
    (F.t ⨯₃ tangentSecondDeriv F kappa kappa_prime tau = liaTangentTimeDeriv F kappa_prime kappa tau) ∧
    (normSq (hasimotoWave kappa theta) = kappa ^ 2) ∧
    ((conj (hasimotoWave kappa theta) * hasimotoDeriv kappa kappa_prime tau theta).im = kappa ^ 2 * tau) ∧
    ((conj (hasimotoWave kappa theta) * hasimotoDeriv kappa kappa_prime tau theta).re = kappa * kappa_prime) ∧
    (0 ≤ filamentLength w k_curv) ∧
    (filamentHelicity w k_curv tau_planar = 0) ∧
    (su2SymplecticForm F.t v u = - su2SymplecticForm F.t u v) ∧
    (su2SymplecticForm F.t F.t u = 0) ∧
    (0 < vortexRingDrift R) ∧
    (0 < vortexRingDispersion R))

#check (makeCertifiedMarsdenWeinsteinHasimotoSynthesis :
  CertifiedMarsdenWeinsteinHasimotoSynthesis)

-- 2. Axiom Footprint Verification
#print axioms lia_tangent_cross_prime
#print axioms lia_heisenberg_cross_equivalence
#print axioms normSq_exp_ofReal_mul_I
#print axioms hasimoto_normSq
#print axioms conj_exp_ofReal_mul_I
#print axioms hasimoto_conj_mul_deriv
#print axioms hasimoto_helicity_density
#print axioms hasimoto_soliton_density_deriv
#print axioms filamentLength_nonneg
#print axioms filamentHelicity_zero_of_planar
#print axioms su2SymplecticForm_skew
#print axioms su2SymplecticForm_self
#print axioms su2SymplecticForm_radial_zero
#print axioms vortexRingDrift_pos
#print axioms vortexRingDispersion_pos
#print axioms marsden_weinstein_hasimoto_vortex_synthesis
#print axioms makeCertifiedMarsdenWeinsteinHasimotoSynthesis

end InfoGeometry.Physics.HasimotoVortexAudit
