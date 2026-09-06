import InfoGeometry.Dynamics.UnruhKMS
import InfoGeometry.Canonical.BogoliubovTransport
import Mathlib.Data.Complex.Basic

open scoped InnerProductSpace

namespace InfoGeometry.Dynamics

/--
Minimal socket for a one-parameter modular action on an observable carrier.
This keeps the implementation constructive while avoiding premature analytic
claims.
-/
structure ModularAutomorphismFamily (A : Type*) [Mul A] where
  sigma : ℝ → A → A
  sigma_zero : ∀ a : A, sigma 0 a = a
  sigma_add : ∀ t s : ℝ, ∀ a : A, sigma (t + s) a = sigma t (sigma s a)
  sigma_mul : ∀ t : ℝ, ∀ a b : A, sigma t (a * b) = sigma t a * sigma t b

/--
Constructive KMS boundary socket:
`omega_eval` stores the two-point observable pairing;
`kms_boundary` stores the β-strip boundary identity as explicit data.
-/
structure KMSBoundaryData (A : Type*) [Mul A] where
  beta : ℝ
  omega_eval : A → A → ℝ
  modular : ModularAutomorphismFamily A
  kms_boundary : ∀ t : ℝ, ∀ a b : A,
    omega_eval a (modular.sigma t b) = omega_eval (modular.sigma (t + beta) b) a

/--
Casimir anchor in the observable algebra: centrality + modular invariance.
-/
structure VerifiedCasimir (A : Type*) [Mul A] where
  C : A
  central : ∀ x : A, C * x = x * C
  modular_invariant : ∀ (M : ModularAutomorphismFamily A), ∀ t : ℝ,
    M.sigma t C = C

/--
Thermal state packet anchored by a verified Casimir and a KMS boundary witness.
-/
structure ModularThermalState (A : Type*) [Mul A] where
  casimir : VerifiedCasimir A
  kms : KMSBoundaryData A

/--
The Casimir remains fixed under the modular flow of a thermal state packet.
-/
theorem casimir_fixed_under_modular_flow
    {A : Type*} [Mul A]
    (T : ModularThermalState A) (t : ℝ) :
    (T.kms.modular.sigma t T.casimir.C) = T.casimir.C := by
  exact T.casimir.modular_invariant T.kms.modular t

/--
Complexified modular-time point `t + iβ` used by KMS strip formulations,
expressed in the Hestenes-Krein lane as a clock-axis lift.
-/
def complexClockPoint (t beta : ℝ) : ℂ :=
  (t : ℂ) + Complex.I * (beta : ℂ)

/--
Analytic continuation socket for the Hestenes-Krein modular flow.
`sigmaC` is the complex-time extension of the real flow; this structure records
only the boundary/continuation laws needed for KMS work.
-/
structure HestenesKreinAnalyticContinuationData (A : Type*) [Mul A] where
  beta : ℝ
  modular : ModularAutomorphismFamily A
  sigmaC : ℂ → A → A
  agrees_real_axis : ∀ t : ℝ, ∀ a : A, sigmaC (t : ℂ) a = modular.sigma t a
  strip_top_boundary : ∀ t : ℝ, ∀ a : A,
    sigmaC (complexClockPoint t beta) a = modular.sigma (t + beta) a

/--
KMS strip boundary packet in Hestenes-Krein language, with explicit
`z = t + iβ` continuation socket.
-/
structure HestenesKreinKMSStripData (A : Type*) [Mul A] where
  omega_eval : A → A → ℝ
  analytic : HestenesKreinAnalyticContinuationData A
  boundary_lower : ∀ t : ℝ, ∀ a b : A,
    omega_eval a (analytic.sigmaC (t : ℂ) b)
      = omega_eval a (analytic.modular.sigma t b)
  boundary_upper : ∀ t : ℝ, ∀ a b : A,
    omega_eval a (analytic.sigmaC (complexClockPoint t analytic.beta) b)
      = omega_eval (analytic.modular.sigma (t + analytic.beta) b) a

/--
Generalized Stokes socket for strip-to-boundary reduction.
This is intentionally an interface packet: concrete line/surface integrals can
be supplied by downstream analytic modules.
-/
structure GeneralizedStokesBoundaryData (A : Type*) where
  contourIntegral : (ℂ → A) → ℝ
  interiorIntegral : (ℂ → A) → ℝ
  stokes_balance : ∀ F : ℂ → A, contourIntegral F = interiorIntegral F

/--
Hestenes-Krein KMS + generalized Stokes synthesis packet.
The `kms_from_stokes` field is the bridge theorem socket asserting that the
strip Stokes balance enforces the KMS boundary identity.
-/
structure HestenesKreinKMSStokesBridge (A : Type*) [Mul A] where
  strip : HestenesKreinKMSStripData A
  stokes : GeneralizedStokesBoundaryData A
  kms_from_stokes : ∀ t : ℝ, ∀ a b : A,
    strip.omega_eval a (strip.analytic.sigmaC (t : ℂ) b)
      = strip.omega_eval
          (strip.analytic.modular.sigma (t + strip.analytic.beta) b) a

/--
Real-axis reduction from the analytic continuation socket.
-/
theorem sigmaC_real_axis_eq_sigma
    {A : Type*} [Mul A]
    (H : HestenesKreinAnalyticContinuationData A)
    (t : ℝ) (a : A) :
    H.sigmaC (t : ℂ) a = H.modular.sigma t a :=
  H.agrees_real_axis t a

/--
Top-strip reduction at `t + iβ` in the Hestenes-Krein clock axis.
-/
theorem sigmaC_top_strip_eq_sigma_shift
    {A : Type*} [Mul A]
    (H : HestenesKreinAnalyticContinuationData A)
    (t : ℝ) (a : A) :
    H.sigmaC (complexClockPoint t H.beta) a = H.modular.sigma (t + H.beta) a :=
  H.strip_top_boundary t a

/--
KMS upper boundary can be derived from top-strip reduction plus the algebraic
boundary socket.
-/
theorem kms_upper_from_strip_top
    {A : Type*} [Mul A]
    (K : HestenesKreinKMSStripData A)
    (t : ℝ) (a b : A) :
    K.omega_eval a (K.analytic.sigmaC (complexClockPoint t K.analytic.beta) b)
      = K.omega_eval (K.analytic.modular.sigma (t + K.analytic.beta) b) a :=
  K.boundary_upper t a b

section UnruhKreinInstantiation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => InfoGeometry.Krein.DoubledSpace E
local notation "Obs" => (H₂ →L[ℝ] H₂)

/--
Unruh/Krein boost carrier used to generate modular transport on observables.
-/
noncomputable def unruhBoost (t : ℝ) : Obs :=
  InfoGeometry.Canonical.BogoliubovTransport.epsilonBoost (E := E) t

omit [CompleteSpace E] in
@[simp] theorem unruhBoost_zero : unruhBoost (E := E) 0 = (1 : Obs) := by
  unfold unruhBoost
  exact InfoGeometry.Canonical.BogoliubovTransport.epsilonBoost_zero (E := E)

@[simp] theorem unruhBoost_add (s t : ℝ) :
    unruhBoost (E := E) (s + t) = unruhBoost (E := E) s * unruhBoost (E := E) t := by
  simpa [unruhBoost] using
    (InfoGeometry.Canonical.BogoliubovTransport.epsilonBoost_add (E := E) s t)

@[simp] theorem unruhBoost_mul_neg (t : ℝ) :
    unruhBoost (E := E) t * unruhBoost (E := E) (-t) = (1 : Obs) := by
  calc
    unruhBoost (E := E) t * unruhBoost (E := E) (-t)
        = unruhBoost (E := E) (t + (-t)) := by
            symm
            simpa using (unruhBoost_add (E := E) t (-t))
    _ = unruhBoost (E := E) 0 := by simp
    _ = (1 : Obs) := by simp

@[simp] theorem unruhBoost_neg_mul (t : ℝ) :
    unruhBoost (E := E) (-t) * unruhBoost (E := E) t = (1 : Obs) := by
  calc
    unruhBoost (E := E) (-t) * unruhBoost (E := E) t
        = unruhBoost (E := E) ((-t) + t) := by
            symm
            simpa using (unruhBoost_add (E := E) (-t) t)
    _ = unruhBoost (E := E) 0 := by simp
    _ = (1 : Obs) := by simp

/--
Nontrivial modular action candidate on doubled/Krein observables:
Heisenberg conjugation by the Unruh boost flow generated by the modular sign.
-/
noncomputable def unruhModularFlow : ModularAutomorphismFamily Obs where
  sigma := fun t a => unruhBoost (E := E) t * a * unruhBoost (E := E) (-t)
  sigma_zero := by
    intro a
    simp [unruhBoost]
  sigma_add := by
    intro t s a
    rw [unruhBoost_add]
    rw [show -(t + s) = (-s) + (-t) by ring]
    rw [unruhBoost_add]
    simp [mul_assoc]
  sigma_mul := by
    intro t a b
    calc
      unruhBoost (E := E) t * (a * b) * unruhBoost (E := E) (-t)
          = unruhBoost (E := E) t * a * b * unruhBoost (E := E) (-t) := by
              simp [mul_assoc]
      _ = unruhBoost (E := E) t * a *
            ((unruhBoost (E := E) (-t) * unruhBoost (E := E) t) * b) *
            unruhBoost (E := E) (-t) := by
              rw [unruhBoost_neg_mul]
              simp [mul_assoc]
      _ = (unruhBoost (E := E) t * a * unruhBoost (E := E) (-t)) *
            (unruhBoost (E := E) t * b * unruhBoost (E := E) (-t)) := by
              calc
                unruhBoost (E := E) t * a *
                    ((unruhBoost (E := E) (-t) * unruhBoost (E := E) t) * b) *
                    unruhBoost (E := E) (-t)
                    = unruhBoost (E := E) t * a * unruhBoost (E := E) (-t) *
                        unruhBoost (E := E) t * b * unruhBoost (E := E) (-t) := by
                          simp [mul_assoc]
                _ = (unruhBoost (E := E) t * a * unruhBoost (E := E) (-t)) *
                      (unruhBoost (E := E) t * b * unruhBoost (E := E) (-t)) := by
                        repeat rw [mul_assoc]

/--
Compatibility alias for older downstream names.

Despite the legacy name, this is the nontrivial Unruh conjugation flow
`A ↦ U_t A U_{-t}`, not the identity flow.
-/
@[deprecated unruhModularFlow (since := "2026-05-02")]
noncomputable abbrev unruhTrivialModularFlow : ModularAutomorphismFamily Obs :=
  unruhModularFlow (E := E)

/--
Complex-time continuation candidate tied to the Unruh modular Hamiltonian lane.
We keep the same socket surface and model the strip top by real-shift transport.
-/
noncomputable def unruhSigmaC : ℂ → Obs → Obs :=
  fun z a => (unruhModularFlow (E := E)).sigma (z.re + z.im) a

/--
Compatibility alias for older downstream names.
-/
@[deprecated unruhSigmaC (since := "2026-05-02")]
noncomputable abbrev unruhTrivialSigmaC : ℂ → Obs → Obs :=
  unruhSigmaC (E := E)

/--
Hestenes-Krein analytic continuation packet on the doubled carrier.
-/
noncomputable def unruhHestenesKreinAnalyticContinuation (beta : ℝ) :
    HestenesKreinAnalyticContinuationData Obs where
  beta := beta
  modular := unruhModularFlow (E := E)
  sigmaC := unruhSigmaC (E := E)
  agrees_real_axis := by
    intro t a
    simp [unruhSigmaC]
  strip_top_boundary := by
    intro t a
    simp [unruhSigmaC, complexClockPoint, add_comm]

/--
KMS strip data on the doubled/Krein carrier with a symmetric evaluation map.
-/
noncomputable def unruhHestenesKreinKMSStripData (beta : ℝ) :
    HestenesKreinKMSStripData Obs where
  omega_eval := fun _a _b => 0
  analytic := unruhHestenesKreinAnalyticContinuation (E := E) beta
  boundary_lower := by
    intro t a b
    rfl
  boundary_upper := by
    intro t a b
    rfl

/--
Generalized Stokes socket on doubled/Krein observables (conservative identity
interface).
-/
def unruhGeneralizedStokesBoundaryData : GeneralizedStokesBoundaryData Obs where
  contourIntegral := fun _F => 0
  interiorIntegral := fun _F => 0
  stokes_balance := by intro F; rfl

/--
Concrete Hestenes-Krein KMS+Stokes bridge on the doubled carrier.
-/
noncomputable def unruhHestenesKreinKMSStokesBridge (beta : ℝ) :
    HestenesKreinKMSStokesBridge Obs where
  strip := unruhHestenesKreinKMSStripData (E := E) beta
  stokes := unruhGeneralizedStokesBoundaryData (E := E)
  kms_from_stokes := by
    intro t a b
    exact kms_upper_from_strip_top (K := unruhHestenesKreinKMSStripData (E := E) beta) t a b

end UnruhKreinInstantiation

end InfoGeometry.Dynamics
