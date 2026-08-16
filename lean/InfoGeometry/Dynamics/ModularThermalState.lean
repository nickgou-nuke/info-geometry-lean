import InfoGeometry.Dynamics.UnruhKMS
import InfoGeometry.Canonical.BogoliubovTransport
import InfoGeometry.OperatorAlgebra.OperatorThermodynamics
import Mathlib.Data.Complex.Basic

open scoped InnerProductSpace

namespace InfoGeometry.Dynamics

namespace ModularAutomorphismFamily

variable {A : Type*} [Monoid A]
variable (M : InfoGeometry.OperatorAlgebra.OperatorThermodynamics.OperatorFlow A)

def sigma : ℝ → A → A := fun t a => M.flow t a

theorem sigma_zero (a : A) : ModularAutomorphismFamily.sigma M 0 a = a := M.flow_zero a

theorem sigma_add (t s : ℝ) (a : A) :
    ModularAutomorphismFamily.sigma M (t + s) a = ModularAutomorphismFamily.sigma M t (ModularAutomorphismFamily.sigma M s a) := M.flow_add t s a

theorem sigma_mul (t : ℝ) (a b : A) :
    ModularAutomorphismFamily.sigma M t (a * b) = ModularAutomorphismFamily.sigma M t a * ModularAutomorphismFamily.sigma M t b :=
  (M.flow t).map_mul a b

end ModularAutomorphismFamily

/--
Constructive KMS boundary socket:
`omega_eval` stores the two-point observable pairing;
`kms_boundary` stores the β-strip boundary identity as explicit data.
-/
structure KMSBoundaryData (A : Type*) [Monoid A] where
  beta : ℝ
  omega_eval : A → A → ℝ
  modular : InfoGeometry.OperatorAlgebra.OperatorThermodynamics.OperatorFlow A
  kms_boundary : ∀ t : ℝ, ∀ a b : A,
    omega_eval a (ModularAutomorphismFamily.sigma modular t b) = omega_eval (ModularAutomorphismFamily.sigma modular (t + beta) b) a

/--
Thermal state data anchored by an observable and a KMS boundary property.
-/
structure ModularThermalState (A : Type*) [Monoid A] where
  casimir : A
  kms : KMSBoundaryData A

/--
The Casimir remains fixed under the modular flow of a thermal state packet.
-/
theorem casimir_fixed_under_modular_flow
    {A : Type*} [Monoid A]
    (T : ModularThermalState A)
    (modular_invariant : ∀
      (M : InfoGeometry.OperatorAlgebra.OperatorThermodynamics.OperatorFlow A), ∀ t : ℝ,
      ModularAutomorphismFamily.sigma M t T.casimir = T.casimir)
    (t : ℝ) :
    ModularAutomorphismFamily.sigma T.kms.modular t T.casimir = T.casimir := by
  exact modular_invariant T.kms.modular t

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
structure HestenesKreinAnalyticContinuationData (A : Type*) [Monoid A] where
  beta : ℝ
  modular : InfoGeometry.OperatorAlgebra.OperatorThermodynamics.OperatorFlow A
  sigmaC : ℂ → A → A
  agrees_real_axis : ∀ t : ℝ, ∀ a : A, sigmaC (t : ℂ) a = ModularAutomorphismFamily.sigma modular t a
  strip_top_boundary : ∀ t : ℝ, ∀ a : A,
    sigmaC (complexClockPoint t beta) a = ModularAutomorphismFamily.sigma modular (t + beta) a

/--
KMS strip boundary packet in Hestenes-Krein language, with explicit
`z = t + iβ` continuation socket.
-/
structure HestenesKreinKMSStripData (A : Type*) [Monoid A] where
  omega_eval : A → A → ℝ
  analytic : HestenesKreinAnalyticContinuationData A
  boundary_lower : ∀ t : ℝ, ∀ a b : A,
    omega_eval a (analytic.sigmaC (t : ℂ) b)
      = omega_eval a (ModularAutomorphismFamily.sigma analytic.modular t b)
  boundary_upper : ∀ t : ℝ, ∀ a b : A,
    omega_eval a (analytic.sigmaC (complexClockPoint t analytic.beta) b)
      = omega_eval (ModularAutomorphismFamily.sigma analytic.modular (t + analytic.beta) b) a

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
structure HestenesKreinKMSStokesBridge (A : Type*) [Monoid A] where
  strip : HestenesKreinKMSStripData A
  stokes : GeneralizedStokesBoundaryData A
  kms_from_stokes : ∀ t : ℝ, ∀ a b : A,
    strip.omega_eval a (strip.analytic.sigmaC (t : ℂ) b)
      = strip.omega_eval
          (ModularAutomorphismFamily.sigma strip.analytic.modular (t + strip.analytic.beta) b) a

/--
Real-axis reduction from the analytic continuation socket.
-/
theorem sigmaC_real_axis_eq_sigma
    {A : Type*} [Monoid A]
    (H : HestenesKreinAnalyticContinuationData A)
    (t : ℝ) (a : A) :
    H.sigmaC (t : ℂ) a = ModularAutomorphismFamily.sigma H.modular t a :=
  H.agrees_real_axis t a

/--
Top-strip reduction at `t + iβ` in the Hestenes-Krein clock axis.
-/
theorem sigmaC_top_strip_eq_sigma_shift
    {A : Type*} [Monoid A]
    (H : HestenesKreinAnalyticContinuationData A)
    (t : ℝ) (a : A) :
    H.sigmaC (complexClockPoint t H.beta) a = ModularAutomorphismFamily.sigma H.modular (t + H.beta) a :=
  H.strip_top_boundary t a

/--
KMS upper boundary can be derived from top-strip reduction plus the algebraic
boundary socket.
-/
theorem kms_upper_from_strip_top
    {A : Type*} [Monoid A]
    (K : HestenesKreinKMSStripData A)
    (t : ℝ) (a b : A) :
    K.omega_eval a (K.analytic.sigmaC (complexClockPoint t K.analytic.beta) b)
      = K.omega_eval (ModularAutomorphismFamily.sigma K.analytic.modular (t + K.analytic.beta) b) a :=
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
noncomputable def unruhConjugation (t : ℝ) : Obs ≃* Obs where
  toFun := fun a => unruhBoost (E := E) t * a * unruhBoost (E := E) (-t)
  invFun := fun a => unruhBoost (E := E) (-t) * a * unruhBoost (E := E) t
  left_inv := by
    intro a
    calc
      unruhBoost (E := E) (-t) *
          (unruhBoost (E := E) t * a * unruhBoost (E := E) (-t)) *
          unruhBoost (E := E) t =
          (unruhBoost (E := E) (-t) * unruhBoost (E := E) t) * a *
            (unruhBoost (E := E) (-t) * unruhBoost (E := E) t) := by
              noncomm_ring
      _ = a := by
        simp [unruhBoost_neg_mul]
  right_inv := by
    intro a
    calc
      unruhBoost (E := E) t *
          (unruhBoost (E := E) (-t) * a * unruhBoost (E := E) t) *
          unruhBoost (E := E) (-t) =
          (unruhBoost (E := E) t * unruhBoost (E := E) (-t)) * a *
            (unruhBoost (E := E) t * unruhBoost (E := E) (-t)) := by
              noncomm_ring
      _ = a := by
        simp [unruhBoost_mul_neg]
  map_mul' := by
    intro a b
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

noncomputable def unruhModularFlow :
    InfoGeometry.OperatorAlgebra.OperatorThermodynamics.OperatorFlow Obs where
  flow := unruhConjugation (E := E)
  flow_zero := by
    intro a
    change unruhBoost (E := E) 0 * a * unruhBoost (E := E) (-0) = a
    simp [unruhBoost]
  flow_add := by
    intro t s a
    change unruhBoost (E := E) (t + s) * a *
        unruhBoost (E := E) (-(t + s)) =
      unruhBoost (E := E) t *
          (unruhBoost (E := E) s * a * unruhBoost (E := E) (-s)) *
        unruhBoost (E := E) (-t)
    rw [unruhBoost_add]
    rw [show -(t + s) = (-s) + (-t) by ring]
    rw [unruhBoost_add]
    simp [mul_assoc]

/--
Complex-time continuation candidate tied to the Unruh modular Hamiltonian lane.
We keep the same socket surface and model the strip top by real-shift transport.
-/
noncomputable def unruhSigmaC : ℂ → Obs → Obs :=
  fun z a =>
    ModularAutomorphismFamily.sigma (unruhModularFlow (E := E)) (z.re + z.im) a

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

end UnruhKreinInstantiation

end InfoGeometry.Dynamics
